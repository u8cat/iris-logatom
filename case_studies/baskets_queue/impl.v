From iris.heap_lang Require Export notation.

(** * The Baskets Queue (Hoffman, Shalev, Shavit, OPODIS 2007).

    A lock-free FIFO queue built on a singly-linked list with [head]
    and [tail] pointers. The list is logically partitioned into
    "baskets" of nodes whose enqueue operations overlapped in time.

    Within a single basket the physical order of nodes is unrelated to
    the FIFO order; the FIFO order is decided only later, by the
    sequence of dequeues. Concretely, the linearisation point of each
    enqueue inside a basket is determined by the moment its
    corresponding dequeue logically removes it. This is the
    future-dependent linearisation point that makes the algorithm
    interesting to verify.

    ** The basket mechanism.
    When several enqueues race on the [next] field of the current tail,
    exactly one CAS succeeds. The losers do *not* retry against the new
    tail; they retry against the *same* [next] field, splicing
    themselves *in front of* the winning node. The list ends up
    pointing through the basket (in some unspecified order) to the
    "leader" (the original CAS winner). The leader becomes the new
    tail, and the next basket is formed off the leader's [next] field.

    ** Pointer-marking dequeues.
    A dequeue logically removes a node by setting a mark bit on the
    [next] pointer of that node's *predecessor*. The successful CAS
    that flips the mark bit is the linearisation point of the dequeue,
    and it is also what fixes the linearisation point of the matching
    enqueue inside its basket.

    ** Tagged-pointer encoding.
    HeapLang's [CmpXchg] requires its comparison values to be unboxed.
    We encode a marked pointer (the original C [<ptr, deleted>] pair)
    using sums of unboxed literals:

        [InjLV  v]  =  unmarked, with [v ∈ {#(), #l}]
        [InjRV  v]  =  marked,   with [v ∈ {#(), #l}]

    where [#()] denotes [null] and [#l] denotes a heap location. Both
    forms are unboxed, so they are valid CAS operands.

    ** Simplifications relative to the paper.
    We omit, as none of these affect linearisability or the
    future-dependent LP argument:
      - the ABA tag scheme (Iris reasons about logical resources, not
        memory addresses);
      - the [free_chain] memory reclamation and the [MAX_HOPS] cap.
        We assume a GC'd setting, so the head pointer is advanced past
        each successfully dequeued node via a best-effort CAS, but we
        do not track per-node liveness for explicit reclamation;
      - the multi-hop tail-lagging skip in the empty branch of
        dequeue;
      - the exponential backoff between CAS retries.
*)

(** ** Node layout.
    Each node is a 2-cell block allocated with [AllocN #2]:
      - offset 0: [value] (immutable after init)
      - offset 1: [next ] field, a tagged pointer in the encoding above.
*)
Local Notation valuef n := n%E (only parsing).
Local Notation nextf  n := (n +ₗ #1)%E (only parsing).

(** [new_node v] allocates a node with value [v] and an unmarked null
    [next] pointer. *)
Definition new_node : val := λ: "v",
  let: "n" := AllocN #2 #() in
  valuef "n" <- "v";;
  nextf  "n" <- InjL #() ;;
  "n".

(** [new_queue ()] allocates the dummy node and the [head]/[tail]
    references, returning the pair [(head, tail)]. *)
Definition new_queue : val := λ: <>,
  let: "dummy" := new_node #() in
  let: "head"  := ref "dummy" in
  let: "tail"  := ref "dummy" in
  ("head", "tail").

(** *** Basket-insertion helper.
    [enq_basket tail1 nd] attempts to splice [nd] into the basket
    hanging off [tail1]'s [next] field, by repeatedly:
      (1) re-reading [tail1.next];
      (2) setting [nd.next] to that value;
      (3) CAS-ing [tail1.next] from that value to (an unmarked
          pointer to) [nd].

    The retry loop is the *essential* mechanism that turns failed CAS
    contenders into a basket of unordered enqueues. Each successful
    CAS pushes [nd] onto the head of the basket; subsequent failures
    insert further nodes ahead of it. The basket therefore grows in
    LIFO order, but its FIFO order will be set later by the dequeues.

    Returns [#true] if [nd] was inserted, or [#false] if [tail1] is
    no longer a valid basket entry point (its [next] became marked,
    indicating that the basket leader has been dequeued). The caller
    treats [#false] as a signal to restart the enqueue. *)
Definition enq_basket : val := rec: "loop" "tail1" "nd" :=
  let: "next2" := !(nextf "tail1") in
  match: "next2" with
    InjL "p" =>
      if: "p" = #() then
        (* The basket has dissolved; restart. *) #false
      else
        nextf "nd" <- "next2" ;;
        if: CAS (nextf "tail1") "next2" (InjL "nd") then #true
        else "loop" "tail1" "nd"
  | InjR <> =>
      (* [tail1]'s next is marked: [tail1]'s successor (the basket's
         current leader) has been dequeued. Abort. *) #false
  end.

(** [enqueue q v] inserts [v] at the tail of [q]. Mirrors lines
    E01-E22 of Fig. 5 (less the simplifications listed at the top of
    this file). *)
Definition enqueue : val := λ: "q" "v",
  let: "head" := Fst "q" in
  let: "tail" := Snd "q" in
  let: "nd"   := new_node "v" in
  (rec: "outer" <> :=
    let: "tail1" := !"tail" in
    let: "next"  := !(nextf "tail1") in
    if: !"tail" = "tail1" then
      match: "next" with
        InjL "p" =>
          if: "p" = #() then
            (* [tail1.next] is unmarked null: try a direct CAS,
               attempting to *create a fresh basket* with [nd] as its
               leader. *)
            nextf "nd" <- InjL #() ;;
            if: CAS (nextf "tail1") (InjL #()) (InjL "nd") then
              (* Direct insert succeeded: best-effort tail advance. *)
              CAS "tail" "tail1" "nd" ;; #()
            else
              (* CAS failed: another enqueue won the race and became
                 the leader of a new basket off [tail1]. We try to
                 *join that basket* via [enq_basket]; if the basket has
                 already dissolved we restart. *)
              if: enq_basket "tail1" "nd" then #()
              else "outer" #()
        else
          (* [tail1.next] is non-null and unmarked: [tail] is lagging.
             Help advance it past the leader, then retry. *)
          CAS "tail" "tail1" "p" ;; "outer" #()
      | InjR <> =>
          (* [tail1.next] is marked: the leader was dequeued. Refresh
             [tail] and retry. *) "outer" #()
      end
    else "outer" #()) #().

(** [dequeue q] removes the oldest live node and returns its value as
    [SOME _], or [NONE] if the queue is empty.

    Dispatch is driven by [head1.next] alone:
      - [InjL #()]  (unmarked-null): the chain ends at [head1] with no
        successor.  By the chain shape, this can only hold when
        [head1] is the live tail with [del_pref = length - 1], so the
        queue is empty.  We return [NONE] without further checks; the
        atomic load of [head1.next] is the linearisation point.
      - [InjL #p] with [p ≠ #()] (unmarked-pointer): [p] is a live
        successor; attempt a mark-CAS at [head1.next] to dequeue [p].
        The CAS itself acts as the consistency check — if [head] has
        advanced past [head1] (so [head1] is in the marked prefix and
        [head1.next] is now marked), the CAS fails.  On success we
        also best-effort advance [head] past the dequeued node.
      - [InjR _]   (marked next-pointer): [head1] is in the marked prefix; walk
        forward through additional marked next-pointers until we hit
        an unmarked successor (live node) or unmarked-null (empty).

    Note: we omit the head=tail comparison and the helper
    [CAS "tail" "tail1" "p"] from the original Hoffman-Shalev-Shavit
    pseudocode.  The head=tail check was a redundant consistency
    check — the next-field encoding already discriminates the empty
    case unambiguously.  The tail-lagging help is a progress
    optimisation, irrelevant to linearisability. *)
Definition dequeue : val := λ: "q",
  let: "head" := Fst "q" in
  (rec: "outer" <> :=
    let: "head1" := !"head" in
    let: "next"  := !(nextf "head1") in
    (rec: "walk" "iter" "next" :=
      match: "next" with
        InjL "p" =>
          if: "p" = #() then NONE
          else
            let: "v" := !(valuef "p") in
            if: CAS (nextf "iter") "next" (InjR "p") then
              (* Best-effort head advance past the dequeued node;
                 in a GC'd setting the old prefix becomes unreachable
                 and is reclaimed by the collector. *)
              CAS "head" "head1" "p" ;;
              SOME "v"
            else
              "outer" #()
      | InjR "p" =>
          if: "p" = #() then "outer" #()
          else
            let: "next2" := !(nextf "p") in
            "walk" "p" "next2"
      end) "head1" "next") #().

(** ** Unified dispatcher (matches the [op] convention used elsewhere
    in this development for adversarial-client lemmas). [SOME d]
    requests an enqueue of [d], returning [#()]; [NONE] requests a
    dequeue, returning [SOMEV v] / [NONEV] in line with
    [bag_like.queue_model]'s [request_response]. *)
Definition op : val := λ: "q" "req",
  match: "req" with
    SOME "d" => enqueue "q" "d"
  | NONE     => dequeue "q"
  end.
