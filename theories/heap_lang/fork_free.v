(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From iris_logatom.pure_logic Require Import adequacy.
From iris.heap_lang Require Import lang notation.
From iris.prelude Require Import options.

(** [fork_free e] holds when evaluating the expression [e] can never spawn a thread,
  as [Fork] is the only construct that adds to the thread pool. It is decided by a pico
  type system, where a value of unknown origin, e.g., read from the heap, is never
  called. A type consists of a level, which says with which arguments a value can be
  called, and a flag that says whether the value is load-free:
  - [FfTrusted]: values that are safe to call with any argument;
  - [FfCallable]: values that are safe to call with a [FfTrusted] argument;
  - [FfUntrusted]: arbitrary values, which are never called on account of their level;
  - load-free values never read the heap ([Load], [Xchg], [CmpXchg]) nor fork, also in
    the bodies of their closures. They are safe to call with a load-free argument, and
    the result is load-free. *)

(** * Types *)

Inductive ff_lvl := FfTrusted | FfCallable | FfUntrusted.

Global Instance ff_lvl_eq_dec : EqDecision ff_lvl.
Proof. solve_decision. Defined.

Definition ff_lvl_rank (l : ff_lvl) : nat :=
  match l with FfTrusted => 0 | FfCallable => 1 | FfUntrusted => 2 end.

Record ff_ty := FfTy { ff_ty_lvl : ff_lvl; ff_ty_load_free : bool }.

Global Instance ff_ty_eq_dec : EqDecision ff_ty.
Proof. solve_decision. Defined.

Global Instance ff_ty_sqsubseteq : SqSubsetEq ff_ty := λ τ1 τ2,
  ff_lvl_rank (ff_ty_lvl τ1) ≤ ff_lvl_rank (ff_ty_lvl τ2)
  ∧ (ff_ty_load_free τ2 = true → ff_ty_load_free τ1 = true).

(* The type of literals *)
Definition ff_ty_bot : ff_ty := FfTy FfTrusted true.

(* The type of values of unknown origin *)
Definition ff_ty_top : ff_ty := FfTy FfUntrusted false.

Definition ff_ty_join (τ1 τ2 : ff_ty) : ff_ty :=
  FfTy (if decide (ff_lvl_rank (ff_ty_lvl τ1) ≤ ff_lvl_rank (ff_ty_lvl τ2))
        then ff_ty_lvl τ2 else ff_ty_lvl τ1)
    (ff_ty_load_free τ1 && ff_ty_load_free τ2).

(* The type of a component of a pair or an injection of type [τ] *)
Definition ff_ty_data (τ : ff_ty) : ff_ty :=
  FfTy (if ff_ty_lvl τ is FfTrusted then FfTrusted else FfUntrusted) (ff_ty_load_free τ).

Definition ff_ty_pair (τ1 τ2 : ff_ty) : ff_ty :=
  FfTy (if (ff_ty_lvl τ1, ff_ty_lvl τ2) is (FfTrusted, FfTrusted) then FfTrusted
        else FfUntrusted)
    (ff_ty_load_free τ1 && ff_ty_load_free τ2).

(* A function of type [τf] can be called with an argument of type [τa] *)
Definition ff_callable (τf τa : ff_ty) : bool :=
  match ff_ty_lvl τf with
  | FfTrusted => true
  | FfCallable => if ff_ty_lvl τa is FfTrusted then true else false
  | FfUntrusted => false
  end || ff_ty_load_free τf && ff_ty_load_free τa.

(* The type of the result of a call *)
Definition ff_ty_app (τf τa : ff_ty) : ff_ty :=
  FfTy FfUntrusted (ff_ty_load_free τf && ff_ty_load_free τa).

(** * Load-freedom *)

(** A free variable is stuck, so it can have any type: we give it the least type. *)
Definition ff_lookup (Γ : gmap string ff_ty) (x : string) : ff_ty :=
  default ff_ty_bot (Γ !! x).

(** [ff_load_free Γ e] holds when [e] does not read the heap nor fork, also in the
  bodies of closures, and its free variables are load-free in [Γ]. *)
Fixpoint ff_load_free (Γ : gmap string ff_ty) (e : expr) : bool :=
  match e with
  | Val v => ff_val_load_free v
  | Var x => ff_ty_load_free (ff_lookup Γ x)
  | Rec f x e => ff_load_free (binder_insert f ff_ty_bot (binder_insert x ff_ty_bot Γ)) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Free e => ff_load_free Γ e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 | FAA e1 e2 =>
    ff_load_free Γ e1 && ff_load_free Γ e2
  | If e0 e1 e2 | Case e0 e1 e2 | Resolve e0 e1 e2 =>
    ff_load_free Γ e0 && ff_load_free Γ e1 && ff_load_free Γ e2
  | Load _ | Xchg _ _ | CmpXchg _ _ _ | Fork _ => false
  | NewProph => true
  end
with ff_val_load_free (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV f x e => ff_load_free (binder_insert f ff_ty_bot (binder_insert x ff_ty_bot ∅)) e
  | PairV v1 v2 => ff_val_load_free v1 && ff_val_load_free v2
  | InjLV v | InjRV v => ff_val_load_free v
  end.

(** The syntactic check of the previous version of this file: [e] contains no [Load],
  [Xchg], [CmpXchg], [Fork], also in the bodies of closures. *)
Definition fork_read_free (e : expr) : bool := ff_load_free ∅ e.

(** * Typing *)

(** [ff_type Γ e] is the least type of [e] in the typing context [Γ], and [None] if [e]
  is not typable. A function is trusted if its body is typable when its argument is
  untrusted; otherwise it is callable if its body is typable when its argument is
  trusted. A call is typable if the level of the function allows it or both the
  function and the argument are load-free. [Fork] is not typable, so a typable
  expression never spawns a thread. [Resolve e0 e1 e2] has the type of [e0], as it
  reduces to the result of a base step of [e0]. *)
Fixpoint ff_type (Γ : gmap string ff_ty) (e : expr) : option ff_ty :=
  match e with
  | Val v => Some (ff_val_type v)
  | Var x => Some (ff_lookup Γ x)
  | Rec f x e' =>
    Some (FfTy
      (if ff_type (binder_insert f (FfTy FfTrusted false) (binder_insert x ff_ty_top Γ)) e'
       is Some _ then FfTrusted
       else if ff_type (binder_insert f (FfTy FfCallable false)
         (binder_insert x (FfTy FfTrusted false) Γ)) e'
       is Some _ then FfCallable else FfUntrusted)
      (ff_load_free Γ (Rec f x e')))
  | App e1 e2 =>
    τ1 ← ff_type Γ e1; τ2 ← ff_type Γ e2;
    guard (ff_callable τ1 τ2 = true);; Some (ff_ty_app τ1 τ2)
  | UnOp _ e => ff_type Γ e;; Some ff_ty_bot
  | BinOp _ e1 e2 => ff_type Γ e1;; ff_type Γ e2;; Some ff_ty_bot
  | If e0 e1 e2 =>
    ff_type Γ e0;; τ1 ← ff_type Γ e1; τ2 ← ff_type Γ e2; Some (ff_ty_join τ1 τ2)
  | Pair e1 e2 => τ1 ← ff_type Γ e1; τ2 ← ff_type Γ e2; Some (ff_ty_pair τ1 τ2)
  | Fst e | Snd e | InjL e | InjR e => τ ← ff_type Γ e; Some (ff_ty_data τ)
  | Case e0 e1 e2 =>
    τ0 ← ff_type Γ e0; τ1 ← ff_type Γ e1; τ2 ← ff_type Γ e2;
    guard (ff_callable τ1 (ff_ty_data τ0) = true);;
    guard (ff_callable τ2 (ff_ty_data τ0) = true);;
    Some (ff_ty_join (ff_ty_app τ1 (ff_ty_data τ0)) (ff_ty_app τ2 (ff_ty_data τ0)))
  | AllocN e1 e2 | Store e1 e2 | FAA e1 e2 => ff_type Γ e1;; ff_type Γ e2;; Some ff_ty_bot
  | Free e => ff_type Γ e;; Some ff_ty_bot
  | Load e => ff_type Γ e;; Some ff_ty_top
  | Xchg e1 e2 => ff_type Γ e1;; ff_type Γ e2;; Some ff_ty_top
  | CmpXchg e0 e1 e2 => ff_type Γ e0;; ff_type Γ e1;; ff_type Γ e2;; Some ff_ty_top
  | Fork _ => None
  | NewProph => Some ff_ty_bot
  | Resolve e0 e1 e2 => τ0 ← ff_type Γ e0; ff_type Γ e1;; ff_type Γ e2;; Some τ0
  end
with ff_val_type (v : val) : ff_ty :=
  match v with
  | LitV _ => ff_ty_bot
  | RecV f x e =>
    FfTy
      (if ff_type (binder_insert f (FfTy FfTrusted false) (binder_insert x ff_ty_top ∅)) e
       is Some _ then FfTrusted
       else if ff_type (binder_insert f (FfTy FfCallable false)
         (binder_insert x (FfTy FfTrusted false) ∅)) e
       is Some _ then FfCallable else FfUntrusted)
      (ff_val_load_free (RecV f x e))
  | PairV v1 v2 => ff_ty_pair (ff_val_type v1) (ff_val_type v2)
  | InjLV v | InjRV v => ff_ty_data (ff_val_type v)
  end.

(** [fork_free e] holds when the expression [e] is typable. *)
Definition fork_free (e : expr) : bool :=
  if ff_type ∅ e is Some _ then true else false.

(** * Properties of the types *)

Lemma ff_ty_le_intro l1 b1 l2 b2 :
  ff_lvl_rank l1 ≤ ff_lvl_rank l2 → (b2 = true → b1 = true) → FfTy l1 b1 ⊑ FfTy l2 b2.
Proof. by split. Qed.

Local Ltac ff_ty_solve :=
  repeat match goal with τ : ff_ty |- _ => destruct τ as [[] []] end;
  unfold sqsubseteq, ff_ty_sqsubseteq, ff_ty_join, ff_ty_data, ff_ty_pair, ff_ty_app,
    ff_callable in *;
  simpl in *; repeat case_decide; naive_solver lia.

Lemma ff_ty_le_refl (τ : ff_ty) : τ ⊑ τ.
Proof. by split. Qed.

Lemma ff_ty_le_trans (τ1 τ2 τ3 : ff_ty) : τ1 ⊑ τ2 → τ2 ⊑ τ3 → τ1 ⊑ τ3.
Proof. intros [Hl12 Hb12] [Hl23 Hb23]. split; [lia|naive_solver]. Qed.

Lemma ff_ty_le_top (τ : ff_ty) : τ ⊑ ff_ty_top.
Proof. split; [destruct τ as [[] ?]; simpl; lia|done]. Qed.

Lemma ff_ty_le_load_free (τ1 τ2 : ff_ty) :
  τ1 ⊑ τ2 → ff_ty_load_free τ2 = true → ff_ty_load_free τ1 = true.
Proof. by intros [_ Hb]. Qed.

Lemma ff_ty_join_l (τ1 τ2 : ff_ty) : τ1 ⊑ ff_ty_join τ1 τ2.
Proof. ff_ty_solve. Qed.

Lemma ff_ty_join_r (τ1 τ2 : ff_ty) : τ2 ⊑ ff_ty_join τ1 τ2.
Proof. ff_ty_solve. Qed.

Lemma ff_ty_join_mono (τ1 τ1' τ2 τ2' : ff_ty) :
  τ1' ⊑ τ1 → τ2' ⊑ τ2 → ff_ty_join τ1' τ2' ⊑ ff_ty_join τ1 τ2.
Proof.
  intros [Hl1 Hb1] [Hl2 Hb2]. rewrite /ff_ty_join. split; simpl.
  - repeat case_decide; lia.
  - rewrite !andb_true_iff. naive_solver.
Qed.

Lemma ff_ty_data_mono (τ τ' : ff_ty) : τ' ⊑ τ → ff_ty_data τ' ⊑ ff_ty_data τ.
Proof. ff_ty_solve. Qed.

Lemma ff_ty_le_data_data (τ : ff_ty) : τ ⊑ ff_ty_data (ff_ty_data τ).
Proof. ff_ty_solve. Qed.

Lemma ff_ty_pair_mono (τ1 τ1' τ2 τ2' : ff_ty) :
  τ1' ⊑ τ1 → τ2' ⊑ τ2 → ff_ty_pair τ1' τ2' ⊑ ff_ty_pair τ1 τ2.
Proof.
  intros [Hl1 Hb1] [Hl2 Hb2]. rewrite /ff_ty_pair. split; simpl.
  - destruct (ff_ty_lvl τ1), (ff_ty_lvl τ1'), (ff_ty_lvl τ2), (ff_ty_lvl τ2');
      simpl in *; lia.
  - rewrite !andb_true_iff. naive_solver.
Qed.

Lemma ff_ty_pair_data_l (τ1 τ2 : ff_ty) : τ1 ⊑ ff_ty_data (ff_ty_pair τ1 τ2).
Proof. ff_ty_solve. Qed.

Lemma ff_ty_pair_data_r (τ1 τ2 : ff_ty) : τ2 ⊑ ff_ty_data (ff_ty_pair τ1 τ2).
Proof. ff_ty_solve. Qed.

Lemma ff_ty_app_mono (τf τf' τa τa' : ff_ty) :
  τf' ⊑ τf → τa' ⊑ τa → ff_ty_app τf' τa' ⊑ ff_ty_app τf τa.
Proof.
  intros [_ Hbf] [_ Hba]. rewrite /ff_ty_app. split; simpl; first done.
  rewrite !andb_true_iff. naive_solver.
Qed.

Lemma ff_callable_mono (τf τf' τa τa' : ff_ty) :
  ff_callable τf τa = true → τf' ⊑ τf → τa' ⊑ τa → ff_callable τf' τa' = true.
Proof.
  rewrite /ff_callable !orb_true_iff !andb_true_iff.
  intros [Hcall|Hcall] [Hlf Hbf] [Hla Hba]; [left|right; naive_solver].
  destruct (ff_ty_lvl τf), (ff_ty_lvl τf'), (ff_ty_lvl τa), (ff_ty_lvl τa');
    simpl in *; done || lia.
Qed.

Lemma ff_callable_load_free (τf τa : ff_ty) :
  ff_ty_load_free τf = true → ff_ty_load_free τa = true → ff_callable τf τa = true.
Proof. intros Hf Ha. by rewrite /ff_callable Hf Ha orb_true_r. Qed.

(** * Load-free expressions are typable *)

Lemma ff_val_type_load_free v : ff_ty_load_free (ff_val_type v) = ff_val_load_free v.
Proof.
  induction v as [l|f x e|v1 IH1 v2 IH2|v IH|v IH];
    rewrite /= /ff_ty_pair /ff_ty_data /= ?IH ?IH1 ?IH2 //.
Qed.

(* Use the induction hypotheses on the load-freedom of the subexpressions *)
Local Ltac ff_load_free_IH :=
  repeat match goal with
  | IH : ∀ Γ, ff_load_free Γ ?e = true → _, H : ff_load_free ?G ?e = true |- _ =>
      let τ := fresh "τ" in let Hτ := fresh "Hτ" in let Hlf := fresh "Hlf" in
      destruct (IH _ H) as (τ & Hτ & Hlf); clear H; rewrite Hτ /=
  end.

Lemma ff_load_free_type (Γ : gmap string ff_ty) e :
  ff_load_free Γ e = true → ∃ τ, ff_type Γ e = Some τ ∧ ff_ty_load_free τ = true.
Proof.
  revert Γ.
  induction e as [v|y|f x e IH|e1 IH1 e2 IH2|op e IH|op e1 IH1 e2 IH2|e0 IH0 e1 IH1 e2 IH2
    |e1 IH1 e2 IH2|e IH|e IH|e IH|e IH|e0 IH0 e1 IH1 e2 IH2
    |e1 IH1 e2 IH2|e IH|e IH|e1 IH1 e2 IH2|e0 IH0 e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
    |e IH| |e0 IH0 e1 IH1 e2 IH2];
    intros Γ Hlf; simpl in Hlf; try done.
  { (* Val *) eexists. split; first done. by rewrite ff_val_type_load_free. }
  { (* Var *) by eexists. }
  { (* Rec *) by eexists. }
  all: rewrite ?andb_true_iff in Hlf; destruct_and?; simpl.
  all: ff_load_free_IH.
  all: rewrite ?option_guard_True; try (by apply ff_callable_load_free).
  all: eexists; split; first done.
  all: rewrite /= /ff_ty_join /ff_ty_app /ff_ty_pair /ff_ty_data /=.
  all: by repeat match goal with H : ff_ty_load_free _ = true |- _ => rewrite H end.
Qed.

Lemma fork_read_free_fork_free e : fork_read_free e = true → fork_free e = true.
Proof.
  intros Hlf. destruct (ff_load_free_type ∅ e Hlf) as (τ & Hτ & _).
  by rewrite /fork_free Hτ.
Qed.

(** * Substitution *)

Local Lemma binder_insert_insert_commute {A} f x y (τf τx τy : A) (Γ : gmap string A) :
  BNamed y ≠ f → BNamed y ≠ x →
  binder_insert f τf (binder_insert x τx (<[y:=τy]> Γ))
  = <[y:=τy]> (binder_insert f τf (binder_insert x τx Γ)).
Proof.
  intros Hf Hx. apply map_eq. intros z.
  destruct f as [|f], x as [|x]; simpl; rewrite !lookup_insert;
    repeat case_decide; simplify_eq; naive_solver.
Qed.

Local Lemma binder_insert_insert_shadow {A} f x y (τf τx τy : A) (Γ : gmap string A) :
  ¬ (BNamed y ≠ f ∧ BNamed y ≠ x) →
  binder_insert f τf (binder_insert x τx (<[y:=τy]> Γ))
  = binder_insert f τf (binder_insert x τx Γ).
Proof.
  intros Hshadow. apply map_eq. intros z.
  destruct f as [|f], x as [|x]; simpl; rewrite !lookup_insert;
    repeat case_decide; simplify_eq; naive_solver.
Qed.

Lemma ff_load_free_subst e (Γ : gmap string ff_ty) x v (τx : ff_ty) :
  ff_load_free (<[x:=τx]> Γ) e = true →
  (ff_ty_load_free τx = true → ff_val_load_free v = true) →
  ff_load_free Γ (subst x v e) = true.
Proof.
  intros Hlf Hv. revert Γ Hlf.
  induction e as [w|y|f y e IH|e1 IH1 e2 IH2|op e IH|op e1 IH1 e2 IH2|e0 IH0 e1 IH1 e2 IH2
    |e1 IH1 e2 IH2|e IH|e IH|e IH|e IH|e0 IH0 e1 IH1 e2 IH2
    |e1 IH1 e2 IH2|e IH|e IH|e1 IH1 e2 IH2|e0 IH0 e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
    |e IH| |e0 IH0 e1 IH1 e2 IH2];
    intros Γ Hlf; simpl in Hlf |- *; try done.
  { (* Var *)
    rewrite /ff_lookup lookup_insert in Hlf. rewrite /ff_lookup.
    case_decide; simplify_eq/=; auto. }
  { (* Rec *)
    case_decide as Hfresh.
    - destruct Hfresh as [Hf Hy].
      rewrite binder_insert_insert_commute // in Hlf. by apply IH.
    - by rewrite binder_insert_insert_shadow in Hlf. }
  all: rewrite ?andb_true_iff in Hlf |- *; naive_solver.
Qed.

Lemma ff_load_free_subst' e (Γ : gmap string ff_ty) b v (τb : ff_ty) :
  ff_load_free (binder_insert b τb Γ) e = true →
  (ff_ty_load_free τb = true → ff_val_load_free v = true) →
  ff_load_free Γ (subst' b v e) = true.
Proof. destruct b; simpl; [done|apply ff_load_free_subst]. Qed.

(* The level of a function is monotone in the typability of its body *)
Local Lemma ff_rec_lvl_mono (oT oC oT' oC' : option ff_ty) :
  (is_Some oT → is_Some oT') → (is_Some oC → is_Some oC') →
  ff_lvl_rank (if oT' is Some _ then FfTrusted else if oC' is Some _ then FfCallable
    else FfUntrusted)
  ≤ ff_lvl_rank (if oT is Some _ then FfTrusted else if oC is Some _ then FfCallable
    else FfUntrusted).
Proof.
  intros HT HC.
  destruct oT, oC, oT', oC'; simpl; try lia.
  all: exfalso;
    first [by destruct (HT ltac:(by eexists))|by destruct (HC ltac:(by eexists))].
Qed.

(* Use the induction hypotheses on the typing of the subexpressions *)
Local Ltac ff_subst_IH :=
  repeat match goal with
  | IH : ∀ Γ τ, ff_type (<[?x:=?τx]> Γ) ?e = Some τ → _,
    H : ff_type (<[?x:=?τx]> ?G) ?e = Some _ |- _ =>
      let τ' := fresh "τ" in let Hτ' := fresh "Hτ" in let Hle' := fresh "Hle" in
      destruct (IH _ _ H) as (τ' & Hτ' & Hle'); clear H; rewrite Hτ' /=
  end.

Lemma ff_type_subst e (Γ : gmap string ff_ty) x v (τx τ : ff_ty) :
  ff_type (<[x:=τx]> Γ) e = Some τ → ff_val_type v ⊑ τx →
  ∃ τ', ff_type Γ (subst x v e) = Some τ' ∧ τ' ⊑ τ.
Proof.
  intros Hty Hv. revert Γ τ Hty.
  induction e as [w|y|f y e IH|e1 IH1 e2 IH2|op e IH|op e1 IH1 e2 IH2|e0 IH0 e1 IH1 e2 IH2
    |e1 IH1 e2 IH2|e IH|e IH|e IH|e IH|e0 IH0 e1 IH1 e2 IH2
    |e1 IH1 e2 IH2|e IH|e IH|e1 IH1 e2 IH2|e0 IH0 e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
    |e IH| |e0 IH0 e1 IH1 e2 IH2];
    intros Γ τ Hty; simpl in Hty; simpl.
  { (* Val *) simplify_eq. eexists. split; [done|apply ff_ty_le_refl]. }
  { (* Var *)
    rewrite /ff_lookup lookup_insert in Hty. rewrite /ff_lookup.
    case_decide as Hxy; simplify_eq/=.
    - eexists. split; [done|exact Hv].
    - eexists. split; [done|apply ff_ty_le_refl]. }
  { (* Rec *)
    injection Hty as <-. eexists. split; first done.
    apply ff_ty_le_intro.
    - case_decide as Hfresh.
      + destruct Hfresh as [Hf Hy]. apply ff_rec_lvl_mono; intros [τb Hb];
          rewrite binder_insert_insert_commute // in Hb;
          destruct (IH _ _ Hb) as (τb' & Hb' & _); by eexists.
      + by rewrite !binder_insert_insert_shadow.
    - intros Hlf. apply (ff_load_free_subst (Rec f y e) Γ x v τx); first done.
      intros Hτx. rewrite -(ff_val_type_load_free v). by eapply ff_ty_le_load_free. }
  all: simplify_option_eq.
  all: ff_subst_IH.
  all: rewrite ?option_guard_True /=.
  all: try (eexists; split; [done|]).
  all: eauto 10 using ff_ty_le_refl, ff_ty_join_mono, ff_ty_pair_mono, ff_ty_data_mono,
    ff_ty_app_mono, ff_callable_mono.
Qed.

Lemma ff_type_subst' e (Γ : gmap string ff_ty) b v (τb τ : ff_ty) :
  ff_type (binder_insert b τb Γ) e = Some τ → ff_val_type v ⊑ τb →
  ∃ τ', ff_type Γ (subst' b v e) = Some τ' ∧ τ' ⊑ τ.
Proof.
  destruct b as [|x]; simpl.
  - intros Hty _. eexists. split; [exact Hty|apply ff_ty_le_refl].
  - apply ff_type_subst.
Qed.

(** * Preservation under reduction *)

Lemma un_op_eval_ff_val_type op v v' :
  un_op_eval op v = Some v' → ff_val_type v' = ff_ty_bot.
Proof.
  rewrite /un_op_eval.
  destruct op, v as [l| | | |]; try destruct l; simpl; intros Hop; simplify_eq; done.
Qed.

Lemma bin_op_eval_ff_val_type op v1 v2 v' :
  bin_op_eval op v1 v2 = Some v' → ff_val_type v' = ff_ty_bot.
Proof.
  intros Hop.
  assert (∃ l, v' = LitV l) as [l ->]; [|done].
  rewrite /bin_op_eval /bin_op_eval_int /bin_op_eval_bool /bin_op_eval_loc in Hop.
  repeat case_match; simpl in Hop; simplify_eq; by eexists.
Qed.

(* The body of a function that can be called with an argument, as the level of the
  function allows it *)
Lemma ff_type_beta_lvl f x e v :
  ff_lvl_rank (ff_ty_lvl (ff_val_type (RecV f x e))) ≤ 1 →
  (ff_ty_lvl (ff_val_type (RecV f x e)) = FfCallable →
    ff_ty_lvl (ff_val_type v) = FfTrusted) →
  ∃ τ, ff_type ∅ (subst' x v (subst' f (RecV f x e) e)) = Some τ.
Proof.
  intros Hlvl Hcall.
  assert (∃ τf τx, ff_type (binder_insert f τf (binder_insert x τx ∅)) e ≠ None
    ∧ ff_val_type (RecV f x e) ⊑ τf ∧ ff_val_type v ⊑ τx) as (τf & τx & Hbody & Hf & Hx).
  { revert Hlvl Hcall. simpl.
    destruct (ff_type (binder_insert f (FfTy FfTrusted false)
      (binder_insert x ff_ty_top ∅)) e) as [τb|] eqn:Hb; simpl; intros Hlvl Hcall.
    - exists (FfTy FfTrusted false), ff_ty_top. rewrite Hb.
      split_and!; [done|by apply ff_ty_le_intro|apply ff_ty_le_top].
    - destruct (ff_type (binder_insert f (FfTy FfCallable false)
        (binder_insert x (FfTy FfTrusted false) ∅)) e) as [τc|] eqn:Hc; simpl in *; last lia.
      exists (FfTy FfCallable false), (FfTy FfTrusted false). rewrite Hc.
      split_and!; [done|by apply ff_ty_le_intro|].
      destruct (ff_val_type v) as [lv bv]. simpl in Hcall.
      apply ff_ty_le_intro; last done. by rewrite Hcall. }
  destruct (ff_type (binder_insert f τf (binder_insert x τx ∅)) e) as [τb|] eqn:Hb;
    last done.
  destruct (ff_type_subst' _ _ _ _ _ _ Hb Hf) as (τb' & Hb' & _).
  destruct (ff_type_subst' _ _ _ _ _ _ Hb' Hx) as (τb'' & Hb'' & _).
  by eexists.
Qed.

(* The branch of a [Case] can be called with the payload *)
Local Ltac ff_case_guard :=
  match goal with
  | Hn : ¬ ff_callable ?τf ?τa = true,
    Hc : ff_callable ?τf (ff_ty_data (ff_ty_data ?τa)) = true |- _ =>
      apply Hn, (ff_callable_mono _ _ _ _ Hc); [apply ff_ty_le_refl|apply ff_ty_le_data_data]
  end.

(** A typable expression takes a base step without forking to a typable expression of a
  smaller type. By induction on the step, as [ResolveS] is recursive. *)
Lemma ff_type_base_step e1 σ1 κ e2 σ2 efs (τ : ff_ty) :
  ff_type ∅ e1 = Some τ → base_step e1 σ1 κ e2 σ2 efs →
  efs = [] ∧ ∃ τ2, ff_type ∅ e2 = Some τ2 ∧ τ2 ⊑ τ.
Proof.
  intros Hty Hstep. revert τ Hty.
  induction Hstep as [f x e σ|v1 v2 σ|v σ|v σ|f x e v2 e' σ He'|op v v' σ Hop|op v1 v2 v' σ Hop
    |e e' σ|e e' σ|v1 v2 σ|v1 v2 σ|v e e' σ|v e e' σ|n v σ l Hn Hfresh|l v σ Hl|l v σ Hl
    |l v w σ Hl|l v1 v2 σ Hl|l v1 v2 vl σ b Hl Hsafe Hb|l i1 i2 σ Hl|e σ|σ p Hp
    |p v e σ w σ' κs ts Hstep IH Hp]; intros τ Hty; simpl in Hty; last 1 first.
  { (* ResolveS *)
    assert (He : ff_type ∅ e = Some τ) by (destruct (ff_type ∅ e); by simplify_eq/=).
    destruct (IH _ He) as (-> & τ2 & Hτ2 & Hle).
    split; first done. by exists τ2. }
  all: try done.
  all: split; [done|].
  { (* RecS *) simplify_eq. eexists. split; [done|apply ff_ty_le_refl]. }
  { (* PairS *) simplify_eq. eexists. split; [done|apply ff_ty_le_refl]. }
  { (* InjLS *) simplify_eq. eexists. split; [done|apply ff_ty_le_refl]. }
  { (* InjRS *) simplify_eq. eexists. split; [done|apply ff_ty_le_refl]. }
  { (* BetaS *)
    subst e'. simplify_option_eq. rename select (ff_callable _ _ = true) into Hcall.
    change (ff_callable (ff_val_type (RecV f x e)) (ff_val_type v2) = true) in Hcall.
    change (∃ τ2, ff_type ∅ (subst' x v2 (subst' f (RecV f x e) e)) = Some τ2
      ∧ τ2 ⊑ ff_ty_app (ff_val_type (RecV f x e)) (ff_val_type v2)).
    rewrite /ff_ty_app.
    destruct (ff_ty_load_free (ff_val_type (RecV f x e)) && ff_ty_load_free (ff_val_type v2))
      eqn:Hlf.
    - (* A call of a load-free function with a load-free argument *)
      apply andb_true_iff in Hlf as [Hlf_f Hlf_2].
      rewrite !ff_val_type_load_free in Hlf_f Hlf_2.
      assert (Hbody : ff_load_free ∅ (subst' x v2 (subst' f (RecV f x e) e)) = true).
      { apply (ff_load_free_subst' _ _ _ _ ff_ty_bot); last done.
        by apply (ff_load_free_subst' _ _ _ _ ff_ty_bot). }
      destruct (ff_load_free_type _ _ Hbody) as (τ' & Hτ' & Hlf').
      exists τ'. split; first done.
      apply ff_ty_le_intro; [destruct τ' as [[] ?]; simpl; lia|done].
    - (* A call allowed by the level of the function *)
      rewrite /ff_callable Hlf orb_false_r in Hcall.
      destruct (ff_type_beta_lvl f x e v2) as [τ' Hτ'].
      { destruct (ff_ty_lvl (ff_val_type (RecV f x e))); simpl; first [lia|done]. }
      { intros Hl. rewrite Hl in Hcall. by destruct (ff_ty_lvl (ff_val_type v2)). }
      exists τ'. split; first done. apply ff_ty_le_top. }
  { (* UnOpS *)
    simplify_option_eq. eexists. split; first done.
    rewrite (un_op_eval_ff_val_type _ _ _ Hop). apply ff_ty_le_refl. }
  { (* BinOpS *)
    simplify_option_eq. eexists. split; first done.
    rewrite (bin_op_eval_ff_val_type _ _ _ _ Hop). apply ff_ty_le_refl. }
  { (* IfTrueS *) simplify_option_eq. eexists. split; [done|apply ff_ty_join_l]. }
  { (* IfFalseS *) simplify_option_eq. eexists. split; [done|apply ff_ty_join_r]. }
  { (* FstS *) simplify_option_eq. eexists. split; [done|apply ff_ty_pair_data_l]. }
  { (* SndS *) simplify_option_eq. eexists. split; [done|apply ff_ty_pair_data_r]. }
  { (* CaseLS *)
    simplify_option_eq.
    - eexists. split; first done.
      eapply ff_ty_le_trans; last apply ff_ty_join_l.
      apply ff_ty_app_mono; [apply ff_ty_le_refl|apply ff_ty_le_data_data].
    - exfalso. ff_case_guard. }
  { (* CaseRS *)
    simplify_option_eq.
    - eexists. split; first done.
      eapply ff_ty_le_trans; last apply ff_ty_join_r.
      apply ff_ty_app_mono; [apply ff_ty_le_refl|apply ff_ty_le_data_data].
    - exfalso. ff_case_guard. }
  (* Heap operations and [NewProphS] *)
  all: simplify_option_eq.
  all: eexists; split; [done|].
  all: solve [apply ff_ty_le_refl|apply ff_ty_le_top].
Qed.

(** Evaluation contexts can be filled with an expression of a smaller type. *)
Lemma ff_type_fill_item Ki e (τ : ff_ty) :
  ff_type ∅ (fill_item Ki e) = Some τ →
  ∃ τe, ff_type ∅ e = Some τe ∧
    ∀ e' τe', ff_type ∅ e' = Some τe' → τe' ⊑ τe →
      ∃ τ', ff_type ∅ (fill_item Ki e') = Some τ' ∧ τ' ⊑ τ.
Proof.
  revert τ.
  induction Ki as [| | | | | | | | | | | | | | | | | | | | | | | | | |Ki IH v1 v2| |];
    intros τ Hty; simpl in Hty; last 3 first.
  { (* [ResolveLCtx]: the hole is in the expression of [Resolve] that takes a base step *)
    assert (HKi : ff_type ∅ (fill_item Ki e) = Some τ)
      by (destruct (ff_type ∅ (fill_item Ki e)); by simplify_eq/=).
    destruct (IH _ HKi) as (τe & He & Hrepl). exists τe. split; first done.
    intros e' τe' He' Hle. destruct (Hrepl _ _ He' Hle) as (τ' & Hτ' & Hle').
    simpl. rewrite Hτ' /=. by exists τ'. }
  all: simplify_option_eq.
  all: eexists; split; first done.
  all: intros e' τe' Hty' Hle; simpl; rewrite Hty' /=.
  all: repeat match goal with H : ff_type ∅ _ = Some _ |- _ => rewrite H /=; clear H end.
  all: rewrite ?option_guard_True /=.
  all: try (eexists; split; [done|]).
  all: eauto 10 using ff_ty_le_refl, ff_ty_join_mono, ff_ty_pair_mono, ff_ty_data_mono,
    ff_ty_app_mono, ff_callable_mono.
Qed.

Lemma ff_type_fill K e (τ : ff_ty) :
  ff_type ∅ (fill K e) = Some τ →
  ∃ τe, ff_type ∅ e = Some τe ∧
    ∀ e' τe', ff_type ∅ e' = Some τe' → τe' ⊑ τe →
      ∃ τ', ff_type ∅ (fill K e') = Some τ' ∧ τ' ⊑ τ.
Proof.
  revert e τ. induction K as [|Ki K IH] using rev_ind; intros e τ Hty.
  - exists τ. split; first done. intros e' τe' Hty' Hle. by exists τe'.
  - rewrite fill_app /= in Hty.
    destruct (ff_type_fill_item _ _ _ Hty) as (τK & HK & Hrepl).
    destruct (IH _ _ HK) as (τe & He & HreplK).
    exists τe. split; first done. intros e' τe' He' Hle.
    destruct (HreplK _ _ He' Hle) as (τK' & HK' & HleK).
    rewrite fill_app /=. by apply (Hrepl _ τK').
Qed.

Lemma ff_type_prim_step e1 σ1 κ e2 σ2 efs (τ : ff_ty) :
  ff_type ∅ e1 = Some τ → prim_step e1 σ1 κ e2 σ2 efs →
  efs = [] ∧ ∃ τ2, ff_type ∅ e2 = Some τ2 ∧ τ2 ⊑ τ.
Proof.
  intros Hty [K e1' e2' -> -> Hbase].
  destruct (ff_type_fill _ _ _ Hty) as (τe & He & Hrepl).
  destruct (ff_type_base_step _ _ _ _ _ _ _ He Hbase) as (-> & τe' & He' & Hle).
  split; first done. by apply (Hrepl _ τe').
Qed.

Lemma fork_free_prim_step e σ κ e' σ' efs :
  prim_step e σ κ e' σ' efs →
  fork_free e = true →
  fork_free e' = true ∧ efs = [].
Proof.
  rewrite /fork_free. intros Hprim Hff.
  destruct (ff_type ∅ e) as [τ|] eqn:Hτ; last done.
  destruct (ff_type_prim_step _ _ _ _ _ _ _ Hτ Hprim) as (-> & τ' & Hτ' & _).
  by rewrite Hτ'.
Qed.

(** * Lifting to configurations and [rtc erased_step]. *)

Lemma erased_step_singleton_fork_free e σ t2 σ2 :
  fork_free e = true →
  erased_step ([e], σ) (t2, σ2) →
  ∃ e', t2 = [e'] ∧ fork_free e' = true.
Proof.
  intros Hff [κ Hstep].
  destruct Hstep as [e1 σ1 e2 σ2' efs t1 ttl Heq1 Heq2 Hprim].
  destruct t1 as [|x t1]; simplify_eq/=.
  - destruct (fork_free_prim_step _ _ _ _ _ _ Hprim Hff) as [Hff' ->].
    by eexists.
  - destruct t1; discriminate.
Qed.

Lemma rtc_erased_step_fork_free (ρ1 ρ2 : cfg heap_ectx_lang) :
  rtc erased_step ρ1 ρ2 →
  (∃ e, ρ1.1 = [e] ∧ fork_free e = true) →
  (∃ e', ρ2.1 = [e'] ∧ fork_free e' = true).
Proof.
  induction 1 as [|ρ ρ' ρ'' Hstep Hrtc IH]; auto.
  intros (e & Hpool & Hff_e).
  destruct ρ as [t σ]. simpl in Hpool. subst t.
  destruct ρ' as [t' σ'].
  destruct (erased_step_singleton_fork_free _ _ _ _ Hff_e Hstep) as (e'' & -> & Hff'').
  apply IH. simpl. by eexists.
Qed.

Lemma rtc_erased_step_singleton_fork_free e σ t2 σ2 :
  fork_free e = true →
  rtc erased_step ([e], σ) (t2, σ2) →
  ∃ e', t2 = [e'] ∧ fork_free e' = true.
Proof.
  intros Hff Hrtc.
  apply (rtc_erased_step_fork_free ([e], σ) (t2, σ2) Hrtc).
  simpl. by eexists.
Qed.

Lemma fork_free_sequential e :
  fork_free e = true → ∀ σ, sequential e σ.
Proof.
  intros Hff σ t2 σ2 Hrtc.
  destruct (rtc_erased_step_singleton_fork_free _ _ _ _ Hff Hrtc)
    as (e' & -> & _).
  reflexivity.
Qed.
