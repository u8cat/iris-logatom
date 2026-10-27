(* sym_lang.v: symbolic heap_lang, whose locations and prophecy ids may be
   symbolic variables. *)
(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From stdpp Require Import ssreflect list numbers list_numbers.
From iris.program_logic Require Import language ectx_language ectxi_language.
From iris.heap_lang Require Import lang.
From iris_logatom.pure_logic Require Import lang_step_decidable.
From iris_logatom.heap_lang.decide Require Export constraint.

(** Symbolic heap_lang has the syntax and evaluation contexts of heap_lang,
except that a location or a prophecy id is a [term]: a symbolic variable plus
an offset, or a constant. Allocating a location or a prophecy id introduces a
fresh variable instead of choosing a fresh name, and records that the new name
is fresh. A step whose outcome depends on the names (comparing locations,
finding a location in the heap) branches, and each branch records its
condition. The conditions form the path condition of the state. *)

(** * Syntax *)
Inductive slit :=
  | SLitInt (n : Z) | SLitBool (b : bool) | SLitUnit | SLitPoison
  | SLitLoc (l : term) | SLitProphecy (p : term).

Inductive sexpr :=
  | SVal (v : sval)
  | SVar (x : string)
  | SRec (f x : binder) (e : sexpr)
  | SApp (e1 e2 : sexpr)
  | SUnOp (op : un_op) (e : sexpr)
  | SBinOp (op : bin_op) (e1 e2 : sexpr)
  | SIf (e0 e1 e2 : sexpr)
  | SPair (e1 e2 : sexpr)
  | SFst (e : sexpr)
  | SSnd (e : sexpr)
  | SInjL (e : sexpr)
  | SInjR (e : sexpr)
  | SCase (e0 e1 e2 : sexpr)
  | SAllocN (e1 e2 : sexpr)
  | SFree (e : sexpr)
  | SLoad (e : sexpr)
  | SStore (e1 e2 : sexpr)
  | SCmpXchg (e0 e1 e2 : sexpr)
  | SXchg (e0 e1 : sexpr)
  | SFAA (e1 e2 : sexpr)
  | SFork (e : sexpr)
  | SNewProph
  | SResolve (e0 e1 e2 : sexpr)
with sval :=
  | SLitV (l : slit)
  | SRecV (f x : binder) (e : sexpr)
  | SPairV (v1 v2 : sval)
  | SInjLV (v : sval)
  | SInjRV (v : sval).

Scheme sexpr_mut_ind := Induction for sexpr Sort Prop
with sval_mut_ind := Induction for sval Sort Prop.
Combined Scheme sexpr_sval_mut_ind from sexpr_mut_ind, sval_mut_ind.

Definition sto_val (e : sexpr) : option sval :=
  match e with SVal v => Some v | _ => None end.

Inductive sectx_item :=
  | SAppLCtx (v2 : sval)
  | SAppRCtx (e1 : sexpr)
  | SUnOpCtx (op : un_op)
  | SBinOpLCtx (op : bin_op) (v2 : sval)
  | SBinOpRCtx (op : bin_op) (e1 : sexpr)
  | SIfCtx (e1 e2 : sexpr)
  | SPairLCtx (v2 : sval)
  | SPairRCtx (e1 : sexpr)
  | SFstCtx
  | SSndCtx
  | SInjLCtx
  | SInjRCtx
  | SCaseCtx (e1 : sexpr) (e2 : sexpr)
  | SAllocNLCtx (v2 : sval)
  | SAllocNRCtx (e1 : sexpr)
  | SFreeCtx
  | SLoadCtx
  | SStoreLCtx (v2 : sval)
  | SStoreRCtx (e1 : sexpr)
  | SXchgLCtx (v2 : sval)
  | SXchgRCtx (e1 : sexpr)
  | SCmpXchgLCtx (v1 : sval) (v2 : sval)
  | SCmpXchgMCtx (e0 : sexpr) (v2 : sval)
  | SCmpXchgRCtx (e0 : sexpr) (e1 : sexpr)
  | SFaaLCtx (v2 : sval)
  | SFaaRCtx (e1 : sexpr)
  | SResolveLCtx (ctx : sectx_item) (v1 : sval) (v2 : sval)
  | SResolveMCtx (e0 : sexpr) (v2 : sval)
  | SResolveRCtx (e0 : sexpr) (e1 : sexpr).

Fixpoint sfill_item (Ki : sectx_item) (e : sexpr) : sexpr :=
  match Ki with
  | SAppLCtx v2 => SApp e (SVal v2)
  | SAppRCtx e1 => SApp e1 e
  | SUnOpCtx op => SUnOp op e
  | SBinOpLCtx op v2 => SBinOp op e (SVal v2)
  | SBinOpRCtx op e1 => SBinOp op e1 e
  | SIfCtx e1 e2 => SIf e e1 e2
  | SPairLCtx v2 => SPair e (SVal v2)
  | SPairRCtx e1 => SPair e1 e
  | SFstCtx => SFst e
  | SSndCtx => SSnd e
  | SInjLCtx => SInjL e
  | SInjRCtx => SInjR e
  | SCaseCtx e1 e2 => SCase e e1 e2
  | SAllocNLCtx v2 => SAllocN e (SVal v2)
  | SAllocNRCtx e1 => SAllocN e1 e
  | SFreeCtx => SFree e
  | SLoadCtx => SLoad e
  | SStoreLCtx v2 => SStore e (SVal v2)
  | SStoreRCtx e1 => SStore e1 e
  | SXchgLCtx v2 => SXchg e (SVal v2)
  | SXchgRCtx e1 => SXchg e1 e
  | SCmpXchgLCtx v1 v2 => SCmpXchg e (SVal v1) (SVal v2)
  | SCmpXchgMCtx e0 v2 => SCmpXchg e0 e (SVal v2)
  | SCmpXchgRCtx e0 e1 => SCmpXchg e0 e1 e
  | SFaaLCtx v2 => SFAA e (SVal v2)
  | SFaaRCtx e1 => SFAA e1 e
  | SResolveLCtx K v1 v2 => SResolve (sfill_item K e) (SVal v1) (SVal v2)
  | SResolveMCtx ex v2 => SResolve ex e (SVal v2)
  | SResolveRCtx ex e1 => SResolve ex e1 e
  end.

Fixpoint ssubst (x : string) (v : sval) (e : sexpr) : sexpr :=
  match e with
  | SVal _ => e
  | SVar y => if decide (x = y) then SVal v else SVar y
  | SRec f y e =>
     SRec f y (if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then ssubst x v e else e)
  | SApp e1 e2 => SApp (ssubst x v e1) (ssubst x v e2)
  | SUnOp op e => SUnOp op (ssubst x v e)
  | SBinOp op e1 e2 => SBinOp op (ssubst x v e1) (ssubst x v e2)
  | SIf e0 e1 e2 => SIf (ssubst x v e0) (ssubst x v e1) (ssubst x v e2)
  | SPair e1 e2 => SPair (ssubst x v e1) (ssubst x v e2)
  | SFst e => SFst (ssubst x v e)
  | SSnd e => SSnd (ssubst x v e)
  | SInjL e => SInjL (ssubst x v e)
  | SInjR e => SInjR (ssubst x v e)
  | SCase e0 e1 e2 => SCase (ssubst x v e0) (ssubst x v e1) (ssubst x v e2)
  | SAllocN e1 e2 => SAllocN (ssubst x v e1) (ssubst x v e2)
  | SFree e => SFree (ssubst x v e)
  | SLoad e => SLoad (ssubst x v e)
  | SXchg e1 e2 => SXchg (ssubst x v e1) (ssubst x v e2)
  | SStore e1 e2 => SStore (ssubst x v e1) (ssubst x v e2)
  | SCmpXchg e0 e1 e2 => SCmpXchg (ssubst x v e0) (ssubst x v e1) (ssubst x v e2)
  | SFAA e1 e2 => SFAA (ssubst x v e1) (ssubst x v e2)
  | SFork e => SFork (ssubst x v e)
  | SNewProph => SNewProph
  | SResolve ex e1 e2 => SResolve (ssubst x v ex) (ssubst x v e1) (ssubst x v e2)
  end.

Definition ssubst' (mx : binder) (v : sval) : sexpr → sexpr :=
  match mx with BNamed x => ssubst x v | BAnon => id end.

(** * Structural equality modulo names *)

(** [sexpr_match e1 e2 = Some cs] if [e1] and [e2] have the same structure,
and their names coincide iff [cs] holds; [None] if their structures differ. *)
Definition match_and (o1 o2 : option (list atom)) : option (list atom) :=
  cs1 ← o1; cs2 ← o2; Some (cs1 ++ cs2).

Definition slit_match (l1 l2 : slit) : option (list atom) :=
  match l1, l2 with
  | SLitInt n1, SLitInt n2 => if decide (n1 = n2) then Some [] else None
  | SLitBool b1, SLitBool b2 => if decide (b1 = b2) then Some [] else None
  | SLitUnit, SLitUnit => Some []
  | SLitPoison, SLitPoison => Some []
  | SLitLoc t1, SLitLoc t2 => Some [Atom CEq t1 t2]
  | SLitProphecy t1, SLitProphecy t2 => Some [Atom CEq t1 t2]
  | _, _ => None
  end.

Fixpoint sexpr_match (e1 e2 : sexpr) {struct e1} : option (list atom) :=
  match e1, e2 with
  | SVal v1, SVal v2 => sval_match v1 v2
  | SVar x1, SVar x2 => if decide (x1 = x2) then Some [] else None
  | SRec f1 x1 e1, SRec f2 x2 e2 =>
    if decide (f1 = f2 ∧ x1 = x2) then sexpr_match e1 e2 else None
  | SApp e11 e12, SApp e21 e22 => match_and (sexpr_match e11 e21) (sexpr_match e12 e22)
  | SUnOp op1 e1, SUnOp op2 e2 => if decide (op1 = op2) then sexpr_match e1 e2 else None
  | SBinOp op1 e11 e12, SBinOp op2 e21 e22 =>
    if decide (op1 = op2) then match_and (sexpr_match e11 e21) (sexpr_match e12 e22) else None
  | SIf e10 e11 e12, SIf e20 e21 e22 =>
    match_and (sexpr_match e10 e20) (match_and (sexpr_match e11 e21) (sexpr_match e12 e22))
  | SPair e11 e12, SPair e21 e22 => match_and (sexpr_match e11 e21) (sexpr_match e12 e22)
  | SFst e1, SFst e2 => sexpr_match e1 e2
  | SSnd e1, SSnd e2 => sexpr_match e1 e2
  | SInjL e1, SInjL e2 => sexpr_match e1 e2
  | SInjR e1, SInjR e2 => sexpr_match e1 e2
  | SCase e10 e11 e12, SCase e20 e21 e22 =>
    match_and (sexpr_match e10 e20) (match_and (sexpr_match e11 e21) (sexpr_match e12 e22))
  | SAllocN e11 e12, SAllocN e21 e22 => match_and (sexpr_match e11 e21) (sexpr_match e12 e22)
  | SFree e1, SFree e2 => sexpr_match e1 e2
  | SLoad e1, SLoad e2 => sexpr_match e1 e2
  | SStore e11 e12, SStore e21 e22 => match_and (sexpr_match e11 e21) (sexpr_match e12 e22)
  | SCmpXchg e10 e11 e12, SCmpXchg e20 e21 e22 =>
    match_and (sexpr_match e10 e20) (match_and (sexpr_match e11 e21) (sexpr_match e12 e22))
  | SXchg e11 e12, SXchg e21 e22 => match_and (sexpr_match e11 e21) (sexpr_match e12 e22)
  | SFAA e11 e12, SFAA e21 e22 => match_and (sexpr_match e11 e21) (sexpr_match e12 e22)
  | SFork e1, SFork e2 => sexpr_match e1 e2
  | SNewProph, SNewProph => Some []
  | SResolve e10 e11 e12, SResolve e20 e21 e22 =>
    match_and (sexpr_match e10 e20) (match_and (sexpr_match e11 e21) (sexpr_match e12 e22))
  | _, _ => None
  end
with sval_match (v1 v2 : sval) {struct v1} : option (list atom) :=
  match v1, v2 with
  | SLitV l1, SLitV l2 => slit_match l1 l2
  | SRecV f1 x1 e1, SRecV f2 x2 e2 =>
    if decide (f1 = f2 ∧ x1 = x2) then sexpr_match e1 e2 else None
  | SPairV v11 v12, SPairV v21 v22 => match_and (sval_match v11 v21) (sval_match v12 v22)
  | SInjLV v1, SInjLV v2 => sval_match v1 v2
  | SInjRV v1, SInjRV v2 => sval_match v1 v2
  | _, _ => None
  end.

(** The outcomes of comparing two values, with their conditions *)
Definition sval_eq_branches (v1 v2 : sval) : list (bool * list atom) :=
  match sval_match v1 v2 with
  | None => [(false, [])]
  | Some cs => (true, cs) :: ((λ α, (false, [atom_neg α])) <$> cs)
  end.

Definition slit_is_unboxed (l : slit) : bool :=
  match l with SLitProphecy _ | SLitPoison => false | _ => true end.
Definition sval_is_unboxed (v : sval) : bool :=
  match v with
  | SLitV l => slit_is_unboxed l
  | SInjLV (SLitV l) => slit_is_unboxed l
  | SInjRV (SLitV l) => slit_is_unboxed l
  | _ => false
  end.
Definition svals_compare_safe (v1 v2 : sval) : bool := sval_is_unboxed v1 || sval_is_unboxed v2.

(** * Operators *)
Definition sun_op_eval (op : un_op) (v : sval) : option sval :=
  match op, v with
  | NegOp, SLitV (SLitBool b) => Some (SLitV (SLitBool (negb b)))
  | NegOp, SLitV (SLitInt n) => Some (SLitV (SLitInt (Z.lnot n)))
  | MinusUnOp, SLitV (SLitInt n) => Some (SLitV (SLitInt (- n)))
  | _, _ => None
  end.

(** Operators on integers and booleans only produce integers and booleans *)
Definition slit_of_int_bool (l : base_lit) : option slit :=
  match l with LitInt n => Some (SLitInt n) | LitBool b => Some (SLitBool b) | _ => None end.

Definition term_add (t : term) (off : Z) : term := Term (term_var t) (term_off t + off).

Definition sbin_op_eval_loc (op : bin_op) (l1 : term) (v2 : slit) : list (slit * list atom) :=
  match op, v2 with
  | OffsetOp, SLitInt off => [(SLitLoc (term_add l1 off), [])]
  | LeOp, SLitLoc l2 => [(SLitBool true, [Atom CLe l1 l2]); (SLitBool false, [Atom CLt l2 l1])]
  | LtOp, SLitLoc l2 => [(SLitBool true, [Atom CLt l1 l2]); (SLitBool false, [Atom CLe l2 l1])]
  | _, _ => []
  end.

Definition sbin_op_eval (op : bin_op) (v1 v2 : sval) : list (sval * list atom) :=
  if decide (op = EqOp) then
    if svals_compare_safe v1 v2 then
      (λ bcs, (SLitV (SLitBool bcs.1), bcs.2)) <$> sval_eq_branches v1 v2
    else []
  else
    match v1, v2 with
    | SLitV (SLitInt n1), SLitV (SLitInt n2) =>
      match bin_op_eval_int op n1 n2 ≫= slit_of_int_bool with
      | Some l => [(SLitV l, [])] | None => [] end
    | SLitV (SLitBool b1), SLitV (SLitBool b2) =>
      match bin_op_eval_bool op b1 b2 ≫= slit_of_int_bool with
      | Some l => [(SLitV l, [])] | None => [] end
    | SLitV (SLitLoc l1), SLitV l2 => (λ lcs, (SLitV lcs.1, lcs.2)) <$> sbin_op_eval_loc op l1 l2
    | _, _ => []
    end.

(** * States *)

(** The heap is a list of updates, the most recent first: the cell of a
location is given by its first entry. The path condition is a list of atoms.
[snext] is the next fresh variable. *)
Record sstate := SState {
  sheap : list (term * option sval);
  sused : list term;
  scons : list atom;
  snext : nat;
}.

Definition sstate_add_atoms (cs : list atom) (σ : sstate) : sstate :=
  SState (sheap σ) (sused σ) (cs ++ scons σ) (snext σ).
Definition sstate_upd_heap (l : term) (c : option sval) (σ : sstate) : sstate :=
  SState ((l, c) :: sheap σ) (sused σ) (scons σ) (snext σ).

(** The possible cells of [l], with their conditions: [l] is the [i]-th entry
and none of the previous ones *)
Fixpoint sheap_lookup (l : term) (h : list (term * option sval)) : list (option sval * list atom) :=
  match h with
  | [] => []
  | (k, c) :: h =>
    (c, [Atom CEq l k]) :: ((λ ccs, (ccs.1, Atom CNe l k :: ccs.2)) <$> sheap_lookup l h)
  end.

(** The possible values stored at [l] *)
Definition sstate_lookup (l : term) (σ : sstate) : list (sval * list atom) :=
  omap (λ ccs : option sval * list atom, (λ v, (v, ccs.2)) <$> ccs.1) (sheap_lookup l (sheap σ)).

(** Allocate [n] cells at the fresh variable *)
Definition sstate_alloc (n : Z) (v : sval) (σ : sstate) : sstate :=
  let x := snext σ in
  SState (((λ i, (Term (Some x) i, Some v)) <$> seqZ 0 n) ++ sheap σ)
    (sused σ)
    ((i ← seqZ 0 n; (λ kc, Atom CNe (Term (Some x) i) kc.1) <$> sheap σ) ++ scons σ)
    (S x).

(** A fresh prophecy id at the fresh variable *)
Definition sstate_new_proph (σ : sstate) : sstate :=
  let x := snext σ in
  SState (sheap σ) (Term (Some x) 0 :: sused σ)
    (((λ p, Atom CNe (Term (Some x) 0) p) <$> sused σ) ++ scons σ) (S x).

(** * Steps *)

(** The arguments are inspected in evaluation order (right to left), so that a
non-value argument in an evaluation position immediately yields no step. *)
Fixpoint sbase_step (e : sexpr) (σ : sstate) : list (sexpr * sstate * list sexpr) :=
  match e with
  | SRec f x e => [(SVal (SRecV f x e), σ, [])]
  | SPair e1 e2 =>
    match e2, e1 with
    | SVal v2, SVal v1 => [(SVal (SPairV v1 v2), σ, [])]
    | _, _ => []
    end
  | SInjL e => match e with SVal v => [(SVal (SInjLV v), σ, [])] | _ => [] end
  | SInjR e => match e with SVal v => [(SVal (SInjRV v), σ, [])] | _ => [] end
  | SApp e1 e2 =>
    match e2, e1 with
    | SVal v2, SVal (SRecV f x e1) => [(ssubst' x v2 (ssubst' f (SRecV f x e1) e1), σ, [])]
    | _, _ => []
    end
  | SUnOp op e =>
    match e with
    | SVal v => match sun_op_eval op v with Some v' => [(SVal v', σ, [])] | None => [] end
    | _ => []
    end
  | SBinOp op e1 e2 =>
    match e2, e1 with
    | SVal v2, SVal v1 =>
      (λ vcs, (SVal vcs.1, sstate_add_atoms vcs.2 σ, [])) <$> sbin_op_eval op v1 v2
    | _, _ => []
    end
  | SIf e0 e1 e2 =>
    match e0 with
    | SVal (SLitV (SLitBool true)) => [(e1, σ, [])]
    | SVal (SLitV (SLitBool false)) => [(e2, σ, [])]
    | _ => []
    end
  | SFst e => match e with SVal (SPairV v1 v2) => [(SVal v1, σ, [])] | _ => [] end
  | SSnd e => match e with SVal (SPairV v1 v2) => [(SVal v2, σ, [])] | _ => [] end
  | SCase e0 e1 e2 =>
    match e0 with
    | SVal (SInjLV v) => [(SApp e1 (SVal v), σ, [])]
    | SVal (SInjRV v) => [(SApp e2 (SVal v), σ, [])]
    | _ => []
    end
  | SAllocN e1 e2 =>
    match e2, e1 with
    | SVal v, SVal (SLitV (SLitInt n)) =>
      if decide (0 < n)%Z then
        [(SVal (SLitV (SLitLoc (Term (Some (snext σ)) 0))), sstate_alloc n v σ, [])]
      else []
    | _, _ => []
    end
  | SFree e =>
    match e with
    | SVal (SLitV (SLitLoc l)) =>
      (λ vcs, (SVal (SLitV SLitUnit), sstate_add_atoms vcs.2 (sstate_upd_heap l None σ), []))
        <$> sstate_lookup l σ
    | _ => []
    end
  | SLoad e =>
    match e with
    | SVal (SLitV (SLitLoc l)) =>
      (λ vcs, (SVal vcs.1, sstate_add_atoms vcs.2 σ, [])) <$> sstate_lookup l σ
    | _ => []
    end
  | SStore e1 e2 =>
    match e2, e1 with
    | SVal w, SVal (SLitV (SLitLoc l)) =>
      (λ vcs, (SVal (SLitV SLitUnit), sstate_add_atoms vcs.2 (sstate_upd_heap l (Some w) σ), []))
        <$> sstate_lookup l σ
    | _, _ => []
    end
  | SXchg e1 e2 =>
    match e2, e1 with
    | SVal v2, SVal (SLitV (SLitLoc l)) =>
      (λ vcs, (SVal vcs.1, sstate_add_atoms vcs.2 (sstate_upd_heap l (Some v2) σ), []))
        <$> sstate_lookup l σ
    | _, _ => []
    end
  | SCmpXchg e0 e1 e2 =>
    match e2, e1, e0 with
    | SVal v2, SVal v1, SVal (SLitV (SLitLoc l)) =>
      vcs ← sstate_lookup l σ;
      if svals_compare_safe vcs.1 v1 then
        (λ bcs, (SVal (SPairV vcs.1 (SLitV (SLitBool bcs.1))),
          sstate_add_atoms (bcs.2 ++ vcs.2)
            (if bcs.1 then sstate_upd_heap l (Some v2) σ else σ), []))
          <$> sval_eq_branches vcs.1 v1
      else []
    | _, _, _ => []
    end
  | SFAA e1 e2 =>
    match e2, e1 with
    | SVal v2, SVal (SLitV (SLitLoc l)) =>
      match v2 with
      | SLitV (SLitInt i2) =>
        vcs ← sstate_lookup l σ;
        match vcs.1 with
        | SLitV (SLitInt i1) =>
          [(SVal (SLitV (SLitInt i1)),
            sstate_add_atoms vcs.2 (sstate_upd_heap l (Some (SLitV (SLitInt (i1 + i2)))) σ), [])]
        | _ => []
        end
      | _ => []
      end
    | _, _ => []
    end
  | SFork e => [(SVal (SLitV SLitUnit), σ, [e])]
  | SNewProph =>
    [(SVal (SLitV (SLitProphecy (Term (Some (snext σ)) 0))), sstate_new_proph σ, [])]
  | SResolve e0 e1 e2 =>
    match e2, e1 with
    | SVal w, SVal (SLitV (SLitProphecy p)) =>
      res ← sbase_step e0 σ;
      match res with
      | (SVal v, σ', efs) =>
        (λ q, (SVal v, sstate_add_atoms [Atom CEq p q] σ', efs)) <$> sused σ
      | _ => []
      end
    | _, _ => []
    end
  | _ => []
  end.

Definition sbase_step_rel (e : sexpr) (σ : sstate) (κ : list unit)
    (e' : sexpr) (σ' : sstate) (efs : list sexpr) : Prop :=
  κ = [] ∧ (e', σ', efs) ∈ sbase_step e σ.

(** * The language *)
Lemma sto_of_val v : sto_val (SVal v) = Some v.
Proof. done. Qed.

Lemma sof_to_val e v : sto_val e = Some v → SVal v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Lemma sval_base_stuck e1 σ1 κ e2 σ2 efs :
  sbase_step_rel e1 σ1 κ e2 σ2 efs → sto_val e1 = None.
Proof. destruct e1; [|done..]. intros [_ Hin]. by apply elem_of_nil in Hin. Qed.

Lemma sfill_item_val Ki e : is_Some (sto_val (sfill_item Ki e)) → is_Some (sto_val e).
Proof. intros [v Hv]. destruct Ki; discriminate Hv. Qed.

Global Instance sfill_item_inj Ki : Inj (=) (=) (sfill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma sfill_item_no_val_inj Ki1 Ki2 e1 e2 :
  sto_val e1 = None → sto_val e2 = None →
  sfill_item Ki1 e1 = sfill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  revert Ki1. induction Ki2; intros Ki1; induction Ki1; naive_solver eauto with f_equal.
Qed.

Lemma sbase_step_resolve_inv e0 e1 e2 σ x :
  x ∈ sbase_step (SResolve e0 e1 e2) σ → ∃ y, y ∈ sbase_step e0 σ.
Proof.
  intros Hin. simpl in Hin. repeat case_match; try by apply elem_of_nil in Hin.
  apply list_elem_of_bind in Hin as (y & _ & Hy). by exists y.
Qed.

Lemma sbase_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  sbase_step_rel (sfill_item Ki e) σ1 κ e2 σ2 efs → is_Some (sto_val e).
Proof.
  intros [_ Hin]. revert e2 σ2 efs Hin.
  induction Ki; intros e2' σ2' efs' Hin;
    lazymatch type of Hin with
    | _ ∈ sbase_step (sfill_item (SResolveLCtx _ _ _) _) _ =>
      (* the inner expression of [Resolve] takes a base step *)
      apply sbase_step_resolve_inv in Hin as ([[e' σ'] efs] & Hin); by eauto
    | _ =>
      destruct e; try (eexists; reflexivity); simpl in Hin; by apply elem_of_nil in Hin
    end.
Qed.

Lemma sym_heap_lang_mixin : EctxiLanguageMixin SVal sto_val sfill_item sbase_step_rel.
Proof.
  split; apply _ || eauto using sto_of_val, sof_to_val, sval_base_stuck,
    sfill_item_val, sfill_item_no_val_inj, sbase_ctx_step_val.
Qed.

Canonical Structure sym_heap_ectxi_lang := EctxiLanguage sym_heap_lang_mixin.
Canonical Structure sym_heap_ectx_lang := EctxLanguageOfEctxi sym_heap_ectxi_lang.
Canonical Structure sym_heap_lang := LanguageOfEctx sym_heap_ectx_lang.

(** * Finitely many steps *)
Fixpoint sexpr_size (e : sexpr) : nat :=
  match e with
  | SVal _ | SVar _ | SNewProph => 1
  | SRec _ _ e | SUnOp _ e | SFst e | SSnd e | SInjL e | SInjR e | SFree e | SLoad e
  | SFork e => S (sexpr_size e)
  | SApp e1 e2 | SBinOp _ e1 e2 | SPair e1 e2 | SAllocN e1 e2 | SStore e1 e2
  | SXchg e1 e2 | SFAA e1 e2 => S (sexpr_size e1 + sexpr_size e2)
  | SIf e0 e1 e2 | SCase e0 e1 e2 | SCmpXchg e0 e1 e2 | SResolve e0 e1 e2 =>
    S (sexpr_size e0 + sexpr_size e1 + sexpr_size e2)
  end.

Lemma sexpr_size_fill_item Ki e : sexpr_size e < sexpr_size (sfill_item Ki e).
Proof. induction Ki; simpl; lia. Qed.

(** All ways to write [e] as [sfill_item Ki e'] *)
Fixpoint sitems (e : sexpr) : list (sectx_item * sexpr) :=
  match e with
  | SApp e1 e2 =>
    (SAppRCtx e1, e2) :: (if sto_val e2 is Some v2 then [(SAppLCtx v2, e1)] else [])
  | SUnOp op e => [(SUnOpCtx op, e)]
  | SBinOp op e1 e2 =>
    (SBinOpRCtx op e1, e2) :: (if sto_val e2 is Some v2 then [(SBinOpLCtx op v2, e1)] else [])
  | SIf e0 e1 e2 => [(SIfCtx e1 e2, e0)]
  | SPair e1 e2 =>
    (SPairRCtx e1, e2) :: (if sto_val e2 is Some v2 then [(SPairLCtx v2, e1)] else [])
  | SFst e => [(SFstCtx, e)]
  | SSnd e => [(SSndCtx, e)]
  | SInjL e => [(SInjLCtx, e)]
  | SInjR e => [(SInjRCtx, e)]
  | SCase e0 e1 e2 => [(SCaseCtx e1 e2, e0)]
  | SAllocN e1 e2 =>
    (SAllocNRCtx e1, e2) :: (if sto_val e2 is Some v2 then [(SAllocNLCtx v2, e1)] else [])
  | SFree e => [(SFreeCtx, e)]
  | SLoad e => [(SLoadCtx, e)]
  | SStore e1 e2 =>
    (SStoreRCtx e1, e2) :: (if sto_val e2 is Some v2 then [(SStoreLCtx v2, e1)] else [])
  | SXchg e1 e2 =>
    (SXchgRCtx e1, e2) :: (if sto_val e2 is Some v2 then [(SXchgLCtx v2, e1)] else [])
  | SCmpXchg e0 e1 e2 =>
    (SCmpXchgRCtx e0 e1, e2) ::
    match sto_val e2 with
    | Some v2 =>
      (SCmpXchgMCtx e0 v2, e1) ::
      (if sto_val e1 is Some v1 then [(SCmpXchgLCtx v1 v2, e0)] else [])
    | None => []
    end
  | SFAA e1 e2 =>
    (SFaaRCtx e1, e2) :: (if sto_val e2 is Some v2 then [(SFaaLCtx v2, e1)] else [])
  | SResolve e0 e1 e2 =>
    (SResolveRCtx e0 e1, e2) ::
    match sto_val e2 with
    | Some v2 =>
      (SResolveMCtx e0 v2, e1) ::
      match sto_val e1 with
      | Some v1 => (λ Kie, (SResolveLCtx Kie.1 v1 v2, Kie.2)) <$> sitems e0
      | None => []
      end
    | None => []
    end
  | _ => []
  end.

Lemma sitems_sound e Ki e' : (Ki, e') ∈ sitems e → e = sfill_item Ki e'.
Proof.
  revert Ki e'. induction e; intros Ki e' Hin; simpl in Hin; repeat case_match;
    repeat match goal with
    | H : _ ∈ [] |- _ => by apply elem_of_nil in H
    | H : _ ∈ _ :: _ |- _ => apply elem_of_cons in H as [H|H]
    | H : (_, _) = (_, _) |- _ => injection H as -> ->
    | H : (_, _) ∈ (λ _, _) <$> _ |- _ =>
      apply list_elem_of_fmap in H as ([Ki0 e0'] & [= -> ->] & H)
    end;
    simpl; f_equal; first [by symmetry; apply sof_to_val | by eauto].
Qed.

Lemma sitems_complete Ki e' : (Ki, e') ∈ sitems (sfill_item Ki e').
Proof.
  induction Ki; simpl; rewrite ?elem_of_cons; auto.
  do 2 right. apply list_elem_of_fmap. eexists (_, _). split; [reflexivity|done].
Qed.

Local Lemma sfill_snoc (K : list sectx_item) Ki e :
  @ectx_language.fill sym_heap_ectx_lang (K ++ [Ki]) e =
  sfill_item Ki (@ectx_language.fill sym_heap_ectx_lang K e).
Proof. exact (fill_app (Λ:=sym_heap_ectxi_lang) K [Ki] e). Qed.

Local Lemma prim_step_cases e σ κ e2 σ2 efs :
  @language.prim_step sym_heap_lang e σ κ e2 σ2 efs ↔
    sbase_step_rel e σ κ e2 σ2 efs ∨
    ∃ Ki e' e2', (Ki, e') ∈ sitems e ∧ e2 = sfill_item Ki e2' ∧
      @language.prim_step sym_heap_lang e' σ κ e2' σ2 efs.
Proof.
  split.
  - intros [K e1' e2' -> -> Hbase].
    destruct K as [|Ki K _] using rev_ind; first by left.
    right. rewrite !sfill_snoc.
    exists Ki, (fill K e1'), (fill K e2'). split_and!.
    + apply sitems_complete.
    + done.
    + by econstructor.
  - intros [Hbase|(Ki & e' & e2' & Hin & -> & Hstep)].
    + by apply base_prim_step.
    + apply sitems_sound in Hin as ->. by apply (fill_step (K:=sfill_item Ki)).
Qed.

Global Instance sym_heap_lang_bounded : BoundedLanguage sym_heap_lang.
Proof.
  constructor. intros e σ.
  remember (sexpr_size e) as n eqn:Hn. revert e Hn.
  induction n as [n IH] using lt_wf_ind. intros e ->.
  assert (∀ its : list (sectx_item * sexpr), (∀ x, x ∈ its → x ∈ sitems e) →
    ∃ L : list (list unit * sexpr * sstate * list sexpr), ∀ κ e2 σ2 efs,
      (∃ Ki e' e2', (Ki, e') ∈ its ∧ e2 = sfill_item Ki e2' ∧
        @language.prim_step sym_heap_lang e' σ κ e2' σ2 efs) ↔
      (κ, e2, σ2, efs) ∈ L) as Hctx.
  { intros its. induction its as [|[Ki e'] its IHits]; intros Hits.
    { exists []. intros κ e2 σ2 efs. split.
      - intros (Ki & e' & e2' & Hin & _). by apply elem_of_nil in Hin.
      - intros Hin. by apply elem_of_nil in Hin. }
    destruct IHits as [L HL].
    { intros x Hx. apply Hits, elem_of_cons. by right. }
    assert (e = sfill_item Ki e') as He.
    { apply sitems_sound, Hits, elem_of_cons. by left. }
    destruct (IH (sexpr_size e') ltac:(subst e; apply sexpr_size_fill_item) e' eq_refl)
      as [L' HL'].
    exists (((λ x, (x.1.1.1, sfill_item Ki x.1.1.2, x.1.2, x.2)) <$> L') ++ L).
    intros κ e2 σ2 efs. rewrite elem_of_app -HL. split.
    - intros (Ki0 & e0 & e2' & [[= <- <-]|Hin]%elem_of_cons & -> & Hstep).
      + left. apply list_elem_of_fmap. exists (κ, e2', σ2, efs). split; first done.
        by apply HL'.
      + right. eauto 10.
    - intros [([[[κ' e2'] σ2'] efs'] & [= -> -> -> ->] & Hin)%list_elem_of_fmap|Hrest].
      + exists Ki, e', e2'. split_and!; [by apply elem_of_cons; left|done|by apply HL'].
      + destruct Hrest as (Ki0 & e0 & e2' & Hin & -> & Hstep).
        exists Ki0, e0, e2'. split_and!; [by apply elem_of_cons; right|done|done]. }
  destruct (Hctx (sitems e) (λ x Hx, Hx)) as [L HL].
  exists (((λ x, ([], x.1.1, x.1.2, x.2)) <$> sbase_step e σ) ++ L).
  intros κ e2 σ2 efs. rewrite prim_step_cases elem_of_app -HL. split.
  - intros [[-> Hbase]|Hctx']; last by right.
    left. apply list_elem_of_fmap. by exists (e2, σ2, efs).
  - intros [([[e2' σ2'] efs'] & [= -> -> -> ->] & Hin)%list_elem_of_fmap|Hctx'];
      last by right.
    left. by split.
Qed.
