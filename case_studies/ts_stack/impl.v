(* impl.v *)

From iris.heap_lang Require Import primitive_laws notation.
From iris.heap_lang.lib Require Import array.
From iris_logatom.heap_lang.lib Require Import thread_id.

(* A model of the pause function used by delay optimisation. This function could
  be an arbitrary pure function. *)
Local Definition delay : val := λ: <>,
  Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;
  Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;
  Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;
  Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip;;Skip.

(********************************************)
(* TS_cas presented in Listing 3 *)
Definition new_timestamper : val := λ: <>, ref #1.

Definition get_timestamp : val := λ: "counter",
  let: "timestamp" := !"counter" in
  delay #();;
  let: "timestamp2" := !"counter" in
  if: "timestamp" ≠ "timestamp2" then
    ("timestamp", "timestamp2" - #1)
  else if: CAS "counter" "timestamp" ("timestamp" + #1) then
    ("timestamp", "timestamp")
  else
    ("timestamp", !"counter" - #1).

Definition timestamp_top : val := (#-1,#-1).
Definition timestamp_bot : val := (#0,#0).

Definition timestamp_lt : val := λ: "ts0" "ts1",
  if: (Fst "ts1" = #(-1)) && (Fst "ts0" ≠ #(-1)) then #true
  else Snd "ts0" < Fst "ts1".
(********************************************)

(********************************************)
(* structure Node {
  element: val;       #0
  timestamp: int*int; #1
  next: loc;          #2
  taken: bool;        #3
} *)

Local Notation element n := n (only parsing).
Local Notation timestamp n := (n+ₗ#1)%E (only parsing).
Local Notation next n := (n+ₗ#2)%E (only parsing).
Local Notation taken n := (n+ₗ#3)%E (only parsing).

Definition new_node : val := λ: "element" "taken",
  let: "n" := AllocN #4 #() in
  element "n" <- "element";;
  timestamp "n" <- timestamp_top;;
  next "n" <- "n";;
  taken "n" <- "taken";;
  "n".
(********************************************)

(********************************************)
(* SP pool presented in Listing 2, but without ID field. *)
Definition new_sppool : val := λ: <>,
  let: "sentinel" := new_node #() #true in
  "sentinel".

Definition unlink_loop_aux : val := rec: "loop" "next" :=
  if: (!(next "next") ≠ "next") && !(taken "next") then
    "loop" !(next "next")
  else
    "next".

Definition sppool_insert : val := λ: "top" "element",
  let: "newNode" := new_node "element" #false in
  next "newNode" <- !"top";;
  "top" <- "newNode";;
  let: "next" := !(next "newNode") in
  next "newNode" <- unlink_loop_aux "next";;
  "newNode".

Definition sppool_get_youngest : val := λ: "top",
  let: "oldTop" := !"top" in
  (rec: "loop" "result" :=
    if: ~ !(taken "result") then
      (SOME "result", "oldTop")
    else if: !(next "result") = "result" then
      (NONE, "oldTop")
    else
      "loop" !(next "result")) "oldTop".

Definition sppool_remove : val := λ: "top" "oldTop" "node",
  if: CAS (taken "node") #false #true then
    CAS "top" "oldTop" "node";;
    (if: "oldTop" ≠ "node" then
      next "oldTop" <- "node"
    else Skip);;
    let: "next" := !(next "node") in
    next "node" <- unlink_loop_aux "next";;
    SOME !(element "node")
  else
    NONE.
(********************************************)

(********************************************)
(* TSStack presented in Listing 1 *)
Definition new_tsstack : val := λ: "maxThreads",
  (array_init "maxThreads" new_sppool, new_timestamper #(), new_threadpool "maxThreads", "maxThreads").

Definition tsstack_push : val := λ: "stack" "element",
  let: "spPools" := Fst (Fst (Fst "stack")) in
  let: "timestamper" := Snd (Fst (Fst "stack")) in
  let: "threadIDer" := Snd (Fst "stack") in
  (********)
  let: "threadID" := claim_tid "threadIDer" in
  let: "pool" := "spPools" +ₗ "threadID" in
  let: "node" := sppool_insert "pool" "element" in
  let: "timestamp" := get_timestamp "timestamper" in
  timestamp "node" <- "timestamp";;
  release_tid "threadIDer" "threadID".

Local Notation EMPTY := NONE (only parsing).
Local Notation NONEMPTY x := (SOME x) (only parsing).

Local Definition wrap_nonempty_result : val := λ: "x",
  match: "x" with
    SOME "x" => SOME (NONEMPTY "x")
  | NONE => NONE
  end.

Definition tsstack_tryRem : val := λ: "stack" "startTime",
  let: "spPools" := Fst (Fst (Fst "stack")) in
  let: "timestamper" := Snd (Fst (Fst "stack")) in
  let: "maxThreads" := Snd "stack" in
  (********)
  let: "empty" := AllocN "maxThreads" #(Loc 0) in
  (* BEGIN for-loop on line 35 *)
  (rec: "loop" "ID" "youngest" "timestamp" "pool" "top" :=
    if: "ID" ≠ "maxThreads" then
      let: "current" := "spPools" +ₗ "ID" in
      let: "tmp" := sppool_get_youngest "current" in
      let: "node" := Fst "tmp" in
      let: "poolTop" := Snd "tmp" in
      match: "node" with
        NONE => "empty" +ₗ "ID" <- "poolTop";;
        "loop" ("ID" + #1) "youngest" "timestamp" "pool" "top"
      | SOME "node" =>
          let: "nodeTimestamp" := !(timestamp "node") in
          if: timestamp_lt "startTime" "nodeTimestamp" then
            wrap_nonempty_result (sppool_remove "current" "poolTop" "node")
          else if: timestamp_lt "timestamp" "nodeTimestamp" then
            "loop" ("ID" + #1) (SOME "node") "nodeTimestamp" "current" "poolTop"
          else
            "loop" ("ID" + #1) "youngest" "timestamp" "pool" "top"
      end
    else (* END for-loop on line 35 *)
      (* HeapLang has no reserved null location, so "no youngest node" is NONE *)
      match: "youngest" with
        NONE =>
        (rec: "loop" "ID" := (* BEGIN for-loop on line 57 *)
          if: "ID" ≠ "maxThreads" then
            let: "current" := "spPools" +ₗ "ID" in
            if: !"current" ≠ !("empty" +ₗ "ID") then
              NONE
            else
              "loop" ("ID" + #1)
          else (* END for-loop on line 57 *)
            SOME EMPTY
        ) #0
      | SOME "youngest" =>
        wrap_nonempty_result (sppool_remove "pool" "top" "youngest")
      end)
    (*ID=*)#0 (*youngest=*)NONE (*timestamp=*)timestamp_bot (*pool=*)#(Loc 0) (*top=*)#(Loc 0).

Definition tsstack_pop : val := λ: "stack",
  let: "spPools" := Fst (Fst (Fst "stack")) in
  let: "timestamper" := Snd (Fst (Fst "stack")) in
  (********)
  let:"startTime" := get_timestamp "timestamper" in
  (rec: "loop" <> :=
    match: tsstack_tryRem "stack" "startTime" with
      SOME "element" => "element"
    | NONE => "loop" #()
    end) #().

Definition ops : list val := [tsstack_push; (λ: "s" <>, tsstack_pop "s")%V].
