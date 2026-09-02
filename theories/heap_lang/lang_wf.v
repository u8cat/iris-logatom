(* Definitions for syntactic less-than for [expr] and [val],
and well-foundness theorems about them. *)

From stdpp Require Import countable well_founded.
From iris.heap_lang Require Import lang.
From iris.prelude Require Import options.

Section strong_induction.

Context {T: Type}.
Notation gen_tree := (gen_tree T).

Inductive gen_le (t: gen_tree): gen_tree → Prop :=
  | gen_le_t: gen_le t t
  | gen_le_node n l r s: gen_le t s → gen_le t (GenNode n (l++s::r)).

Definition gen_lt t s := ∃ n l r, gen_le (GenNode n (l++t::r)) s.

Lemma gen_lt_wf: well_founded gen_lt.
Proof.
  set (f:=fix f (t: gen_tree) :=
    match t with
    | GenLeaf _ => 0
    | GenNode n ts => S (list_sum (map f ts))
    end
  ).
  apply well_founded_lt_compat with (f:=f) => x y H.
  destruct H as (n0 & l0 & r0 & H).
  induction H as [ | n l r s H IH]; simpl.
  all: rewrite map_app; simpl.
  all: rewrite list_sum_app; simpl.
  all: lia.
Qed.

End strong_induction.

Fixpoint expr2gentree (e: expr) :=
  match e with
  | Val v => GenNode 0 [val2gentree v]
  | Var x => GenLeaf (inl (inl x))
  | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); expr2gentree e]
  | App e1 e2 => GenNode 2 [expr2gentree e1; expr2gentree e2]
  | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); expr2gentree e]
  | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr op))); expr2gentree e1; expr2gentree e2]
  | If e0 e1 e2 => GenNode 5 [expr2gentree e0; expr2gentree e1; expr2gentree e2]
  | Pair e1 e2 => GenNode 6 [expr2gentree e1; expr2gentree e2]
  | Fst e => GenNode 7 [expr2gentree e]
  | Snd e => GenNode 8 [expr2gentree e]
  | InjL e => GenNode 9 [expr2gentree e]
  | InjR e => GenNode 10 [expr2gentree e]
  | Case e0 e1 e2 => GenNode 11 [expr2gentree e0; expr2gentree e1; expr2gentree e2]
  | AllocN e1 e2 => GenNode 13 [expr2gentree e1; expr2gentree e2]
  | Free e => GenNode 14 [expr2gentree e]
  | Load e => GenNode 15 [expr2gentree e]
  | Store e1 e2 => GenNode 16 [expr2gentree e1; expr2gentree e2]
  | CmpXchg e0 e1 e2 => GenNode 17 [expr2gentree e0; expr2gentree e1; expr2gentree e2]
  | Xchg e0 e1 => GenNode 18 [expr2gentree e0; expr2gentree e1]
  | FAA e1 e2 => GenNode 19 [expr2gentree e1; expr2gentree e2]
  | Fork e => GenNode 20 [expr2gentree e]
  | NewProph => GenNode 21 []
  | Resolve e0 e1 e2 => GenNode 22 [expr2gentree e0; expr2gentree e1; expr2gentree e2]
  end
with val2gentree (v: val) :=
  match v with
  | LitV l => GenLeaf (inr (inl l))
  | RecV f x e =>
    GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); expr2gentree e]
  | PairV v1 v2 => GenNode 1 [val2gentree v1; val2gentree v2]
  | InjLV v => GenNode 2 [val2gentree v]
  | InjRV v => GenNode 3 [val2gentree v]
  end.

Definition expr_lt e1 e2 := gen_lt (expr2gentree e1) (expr2gentree e2).
Definition val_lt v1 v2 := gen_lt (val2gentree v1) (val2gentree v2).

Lemma expr_lt_wf: well_founded expr_lt.
Proof. eapply wf_projected; eauto using gen_lt_wf. Qed.
Lemma val_lt_wf: well_founded val_lt.
Proof. eapply wf_projected; eauto using gen_lt_wf. Qed.

Local Ltac left_half n l :=
  lazymatch n with
  | 0 =>
    let t := type of l in
    constr:([]:t)
  | S ?n' =>
    match l with
    | ?x :: ?xs =>
        let xs' := left_half n' xs in
        constr:(x::xs')
    end
  end.

Local Ltac right_half n l :=
  lazymatch n with
  | 0 => l
  | S ?n' =>
    match l with
    | _::?xs => right_half n' xs
    end
  end.

Ltac gen_le_constructor n :=
  match goal with
  |  |- gen_le _ (GenNode _ ?l) =>
    let lh := left_half n l in
    let rh := right_half n l in
    change l with (lh++rh); (eapply gen_le_t || eapply gen_le_node)
  end.

Create HintDb _gen_wf.
Global Hint Extern 1 => gen_le_constructor 0: _gen_wf.
Global Hint Extern 1 => gen_le_constructor 1: _gen_wf.
Global Hint Extern 1 => gen_le_constructor 2: _gen_wf.
Global Hint Extern 1 => gen_le_constructor 3: _gen_wf.
Global Hint Extern 1 => gen_le_constructor 4: _gen_wf.
Global Hint Extern 1 => gen_le_constructor 5: _gen_wf.

Ltac solve_gen_lt := rewrite /gen_lt; do 3 eexists; auto with _gen_wf.
Ltac solve_expr_lt := rewrite /expr_lt /=; solve_gen_lt.
Ltac solve_val_lt := rewrite /val_lt /=; solve_gen_lt.

Create HintDb solve_lt.
Global Hint Extern 0 => solve_expr_lt: solve_lt.
Global Hint Extern 0 => solve_val_lt: solve_lt.
Global Hint Extern 0 => solve_gen_lt: solve_lt.

