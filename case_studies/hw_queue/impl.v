From iris.heap_lang Require Export notation par arith diverge.

(* The Herlihy-Wing queue implementation is copied from
https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/logatom/herlihy_wing_queue/hwq.v *)

(** * Some array-related notations ******************************************)

Notation "new_array: sz" :=
  (AllocN sz%E NONEV) (at level 80) : expr_scope.

Notation "e1 <[[ e2 ]]>" :=
  (BinOp OffsetOp e1%E e2%E) (at level 8) : expr_scope.

(** * Implementation of the queue operations ********************************)

(** new_queue(sz){
      let ar := new_array sz None in
      let back := ref 0 in
      {sz, ar, back}
    } *)
Definition new_queue : val :=
  λ: "sz",
    let: "ar" := new_array: "sz" in
    let: "back" := ref #0 in (* First free cell. *)
    ("sz", "ar", "back").

(** enqueue(q : queue, x : item){
      let i : int := FAA(q.back, 1) in
      if(i < q.size){
        q.items[i] := x
      } else {
        while true;
      }
    } *)
Definition enqueue : val :=
  λ: "q" "x",
    let: "q_size" := Fst (Fst "q") in
    let: "q_ar"   := Snd (Fst "q") in
    let: "q_back" := Snd "q" in
    (* Get the next free index. *)
    let: "i" := FAA "q_back" #1 in
    (* Check not full, and actually insert. *)
    if: "i" < "q_size" then "q_ar"<[["i"]]> <- SOME "x"
    else diverge #().

(** dequeue(q : queue){
      let range = min(!q.back, q.size) in
      let rec dequeue_aux(i) =
        if i = 0 {
          dequeue(q)
        } else {
          let j = range - i in
          let x = ! q.ar[j] in
          if x == null {
            dequeue_aux(i-1)
          } else {
            if CAS q.ar[j] x null {
              v
            } else {
              dequeue_aux(i-1)
            }
          }
        }
      in
      dequeue_aux(range)
    } *)
Definition dequeue_aux : val :=
  rec: "loop" "dequeue" "q" "range" "i" :=
    if: "i" = #0 then "dequeue" "q" else
      let: "q_ar" := Snd (Fst "q") in
      let: "j"    := "range" - "i" in
      let: "x"    := ! "q_ar"<[["j"]]> in
      match: "x" with
        NONE     => "loop" "dequeue" "q" "range" ("i" - #1)
      | SOME "v" =>
        let: "c" := CmpXchg ("q_ar"<[["j"]]>) "x" NONE in
        if: Snd "c" then "v" else "loop" "dequeue" "q" "range" ("i" - #1)
      end.
Definition dequeue : val :=
  rec: "dequeue" "q" :=
    let: "q_size" := Fst (Fst "q") in
    let: "q_back" := Snd "q" in
    let: "range"  := minimum !"q_back" "q_size" in
    dequeue_aux "dequeue" "q" "range" "range".

Definition ops : list val := [enqueue; (λ: "q" <>, SOME (dequeue "q"))%V].

