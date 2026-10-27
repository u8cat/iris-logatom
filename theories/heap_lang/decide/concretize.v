(* concretize.v: the relation between symbolic heap_lang and heap_lang. *)
(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From stdpp Require Import ssreflect list numbers list_numbers gmap.
From iris_logatom.heap_lang.decide Require Export sym_lang.
From iris.heap_lang Require Import lang.

(** * Names *)

(** Prophecy ids are concretized through a bijection between [Z] and
[positive], so that all symbolic names are valued in [Z]. *)
Definition proph_of_Z (z : Z) : proph_id :=
  match z with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Definition Z_of_proph (p : proph_id) : Z :=
  match p with xH => Z0 | xO p => Zpos p | xI p => Zneg p end.

Lemma proph_of_Z_of_proph p : proph_of_Z (Z_of_proph p) = p.
Proof. by destruct p. Qed.
Lemma Z_of_proph_of_Z z : Z_of_proph (proph_of_Z z) = z.
Proof. by destruct z. Qed.

(** * Concretization under a valuation *)
Section concretize.
  Context (ν : valuation).

  Definition ac_loc (t : term) : loc := {| loc_car := term_eval ν t |}.
  Definition ac_proph (t : term) : proph_id := proph_of_Z (term_eval ν t).

  Definition ac_lit (l : slit) : base_lit :=
    match l with
    | SLitInt n => LitInt n
    | SLitBool b => LitBool b
    | SLitUnit => LitUnit
    | SLitPoison => LitPoison
    | SLitLoc t => LitLoc (ac_loc t)
    | SLitProphecy t => LitProphecy (ac_proph t)
    end.

  Fixpoint ac_expr (e : sexpr) : expr :=
    match e with
    | SVal v => Val (ac_val v)
    | SVar x => Var x
    | SRec f x e => Rec f x (ac_expr e)
    | SApp e1 e2 => App (ac_expr e1) (ac_expr e2)
    | SUnOp op e => UnOp op (ac_expr e)
    | SBinOp op e1 e2 => BinOp op (ac_expr e1) (ac_expr e2)
    | SIf e0 e1 e2 => If (ac_expr e0) (ac_expr e1) (ac_expr e2)
    | SPair e1 e2 => Pair (ac_expr e1) (ac_expr e2)
    | SFst e => Fst (ac_expr e)
    | SSnd e => Snd (ac_expr e)
    | SInjL e => InjL (ac_expr e)
    | SInjR e => InjR (ac_expr e)
    | SCase e0 e1 e2 => Case (ac_expr e0) (ac_expr e1) (ac_expr e2)
    | SAllocN e1 e2 => AllocN (ac_expr e1) (ac_expr e2)
    | SFree e => Free (ac_expr e)
    | SLoad e => Load (ac_expr e)
    | SStore e1 e2 => Store (ac_expr e1) (ac_expr e2)
    | SCmpXchg e0 e1 e2 => CmpXchg (ac_expr e0) (ac_expr e1) (ac_expr e2)
    | SXchg e1 e2 => Xchg (ac_expr e1) (ac_expr e2)
    | SFAA e1 e2 => FAA (ac_expr e1) (ac_expr e2)
    | SFork e => Fork (ac_expr e)
    | SNewProph => NewProph
    | SResolve e0 e1 e2 => Resolve (ac_expr e0) (ac_expr e1) (ac_expr e2)
    end
  with ac_val (v : sval) : val :=
    match v with
    | SLitV l => LitV (ac_lit l)
    | SRecV f x e => RecV f x (ac_expr e)
    | SPairV v1 v2 => PairV (ac_val v1) (ac_val v2)
    | SInjLV v => InjLV (ac_val v)
    | SInjRV v => InjRV (ac_val v)
    end.

  Fixpoint ac_item (Ki : sectx_item) : ectx_item :=
    match Ki with
    | SAppLCtx v2 => AppLCtx (ac_val v2)
    | SAppRCtx e1 => AppRCtx (ac_expr e1)
    | SUnOpCtx op => UnOpCtx op
    | SBinOpLCtx op v2 => BinOpLCtx op (ac_val v2)
    | SBinOpRCtx op e1 => BinOpRCtx op (ac_expr e1)
    | SIfCtx e1 e2 => IfCtx (ac_expr e1) (ac_expr e2)
    | SPairLCtx v2 => PairLCtx (ac_val v2)
    | SPairRCtx e1 => PairRCtx (ac_expr e1)
    | SFstCtx => FstCtx
    | SSndCtx => SndCtx
    | SInjLCtx => InjLCtx
    | SInjRCtx => InjRCtx
    | SCaseCtx e1 e2 => CaseCtx (ac_expr e1) (ac_expr e2)
    | SAllocNLCtx v2 => AllocNLCtx (ac_val v2)
    | SAllocNRCtx e1 => AllocNRCtx (ac_expr e1)
    | SFreeCtx => FreeCtx
    | SLoadCtx => LoadCtx
    | SStoreLCtx v2 => StoreLCtx (ac_val v2)
    | SStoreRCtx e1 => StoreRCtx (ac_expr e1)
    | SXchgLCtx v2 => XchgLCtx (ac_val v2)
    | SXchgRCtx e1 => XchgRCtx (ac_expr e1)
    | SCmpXchgLCtx v1 v2 => CmpXchgLCtx (ac_val v1) (ac_val v2)
    | SCmpXchgMCtx e0 v2 => CmpXchgMCtx (ac_expr e0) (ac_val v2)
    | SCmpXchgRCtx e0 e1 => CmpXchgRCtx (ac_expr e0) (ac_expr e1)
    | SFaaLCtx v2 => FaaLCtx (ac_val v2)
    | SFaaRCtx e1 => FaaRCtx (ac_expr e1)
    | SResolveLCtx K v1 v2 => ResolveLCtx (ac_item K) (ac_val v1) (ac_val v2)
    | SResolveMCtx e0 v2 => ResolveMCtx (ac_expr e0) (ac_val v2)
    | SResolveRCtx e0 e1 => ResolveRCtx (ac_expr e0) (ac_expr e1)
    end.

  Definition ac_cell (c : option sval) : option val := ac_val <$> c.

  Definition ac_heap (h : list (term * option sval)) : gmap loc (option val) :=
    list_to_map ((λ kc, (ac_loc kc.1, ac_cell kc.2)) <$> h).

  Definition ac_state (σ : sstate) : state :=
    {| heap := ac_heap (sheap σ); used_proph_id := list_to_set (ac_proph <$> sused σ) |}.
End concretize.

(** * Abstraction: the symbolic objects without variables *)
Definition ca_lit (l : base_lit) : slit :=
  match l with
  | LitInt n => SLitInt n
  | LitBool b => SLitBool b
  | LitUnit => SLitUnit
  | LitPoison => SLitPoison
  | LitLoc l => SLitLoc (Term None (loc_car l))
  | LitProphecy p => SLitProphecy (Term None (Z_of_proph p))
  end.

Fixpoint ca_expr (e : expr) : sexpr :=
  match e with
  | Val v => SVal (ca_val v)
  | Var x => SVar x
  | Rec f x e => SRec f x (ca_expr e)
  | App e1 e2 => SApp (ca_expr e1) (ca_expr e2)
  | UnOp op e => SUnOp op (ca_expr e)
  | BinOp op e1 e2 => SBinOp op (ca_expr e1) (ca_expr e2)
  | If e0 e1 e2 => SIf (ca_expr e0) (ca_expr e1) (ca_expr e2)
  | Pair e1 e2 => SPair (ca_expr e1) (ca_expr e2)
  | Fst e => SFst (ca_expr e)
  | Snd e => SSnd (ca_expr e)
  | InjL e => SInjL (ca_expr e)
  | InjR e => SInjR (ca_expr e)
  | Case e0 e1 e2 => SCase (ca_expr e0) (ca_expr e1) (ca_expr e2)
  | AllocN e1 e2 => SAllocN (ca_expr e1) (ca_expr e2)
  | Free e => SFree (ca_expr e)
  | Load e => SLoad (ca_expr e)
  | Store e1 e2 => SStore (ca_expr e1) (ca_expr e2)
  | CmpXchg e0 e1 e2 => SCmpXchg (ca_expr e0) (ca_expr e1) (ca_expr e2)
  | Xchg e1 e2 => SXchg (ca_expr e1) (ca_expr e2)
  | FAA e1 e2 => SFAA (ca_expr e1) (ca_expr e2)
  | Fork e => SFork (ca_expr e)
  | NewProph => SNewProph
  | Resolve e0 e1 e2 => SResolve (ca_expr e0) (ca_expr e1) (ca_expr e2)
  end
with ca_val (v : val) : sval :=
  match v with
  | LitV l => SLitV (ca_lit l)
  | RecV f x e => SRecV f x (ca_expr e)
  | PairV v1 v2 => SPairV (ca_val v1) (ca_val v2)
  | InjLV v => SInjLV (ca_val v)
  | InjRV v => SInjRV (ca_val v)
  end.

Definition ca_state (σ : state) : sstate :=
  SState
    ((λ kc : loc * option val, (Term None (loc_car kc.1), ca_val <$> kc.2))
      <$> map_to_list (heap σ))
    ((λ p, Term None (Z_of_proph p)) <$> elements (used_proph_id σ)) [] 0.

Scheme expr_mut_ind := Induction for expr Sort Prop
with val_mut_ind := Induction for val Sort Prop.
Combined Scheme expr_val_mut_ind from expr_mut_ind, val_mut_ind.

(** ** Concretization of abstractions *)
Lemma ac_ca_lit ν l : ac_lit ν (ca_lit l) = l.
Proof.
  destruct l as [| | | |[z]|p];
    rewrite /= /ac_loc /ac_proph /term_eval /term_base /= ?proph_of_Z_of_proph //.
Qed.

Lemma ac_ca ν : (∀ e, ac_expr ν (ca_expr e) = e) ∧ (∀ v, ac_val ν (ca_val v) = v).
Proof. apply expr_val_mut_ind; intros; simpl; f_equal; auto using ac_ca_lit. Qed.

Lemma ac_ca_expr ν e : ac_expr ν (ca_expr e) = e.
Proof. apply ac_ca. Qed.
Lemma ac_ca_val ν v : ac_val ν (ca_val v) = v.
Proof. apply ac_ca. Qed.

Lemma ac_ca_state ν σ : ac_state ν (ca_state σ) = σ.
Proof.
  destruct σ as [h used]. rewrite /ac_state /ca_state /ac_heap /=. f_equal.
  - rewrite -list_fmap_compose -{2}(list_to_map_to_list h). f_equal.
    rewrite -{2}(list_fmap_id (map_to_list h)). apply list_fmap_ext.
    intros i [[z] c] _. rewrite /= /ac_loc /ac_cell /term_eval /term_base /=. f_equal.
    destruct c; by rewrite /= ?ac_ca_val.
  - rewrite -list_fmap_compose -{2}(list_to_set_elements_L used). f_equal.
    rewrite -{2}(list_fmap_id (elements used)). apply list_fmap_ext.
    intros i p _. by rewrite /= /ac_proph /term_eval /term_base /= proph_of_Z_of_proph.
Qed.

(** ** Concretization commutes with the language constructs *)
Lemma ac_expr_to_val ν e : to_val (ac_expr ν e) = ac_val ν <$> sto_val e.
Proof. by destruct e. Qed.

Lemma ac_subst ν x v e : ac_expr ν (ssubst x v e) = subst x (ac_val ν v) (ac_expr ν e).
Proof. induction e; simpl; try case_decide; f_equal; auto. Qed.

Lemma ac_subst' ν mx v e : ac_expr ν (ssubst' mx v e) = subst' mx (ac_val ν v) (ac_expr ν e).
Proof. destruct mx; simpl; [done|apply ac_subst]. Qed.

Lemma ac_fill_item ν Ki e :
  ac_expr ν (sfill_item Ki e) = fill_item (ac_item ν Ki) (ac_expr ν e).
Proof. induction Ki; simpl; f_equal; auto. Qed.

Lemma ac_val_is_unboxed ν v : val_is_unboxed (ac_val ν v) ↔ sval_is_unboxed v = true.
Proof.
  destruct v as [l| | |v|v]; simpl; [by destruct l|done|done|..].
  all: destruct v as [l| | | |]; [by destruct l|done..].
Qed.

Lemma ac_vals_compare_safe ν v1 v2 :
  vals_compare_safe (ac_val ν v1) (ac_val ν v2) ↔ svals_compare_safe v1 v2 = true.
Proof. rewrite /vals_compare_safe /svals_compare_safe orb_true_iff !ac_val_is_unboxed //. Qed.

(** ** Structural equality modulo names *)
Definition match_spec ν (P : Prop) (o : option (list atom)) : Prop :=
  match o with None => ¬ P | Some cs => P ↔ atoms_hold ν cs end.

Local Lemma match_spec_iff ν P Q o : (P ↔ Q) → match_spec ν P o → match_spec ν Q o.
Proof. destruct o; simpl; tauto. Qed.

Local Lemma match_and_spec ν P1 P2 o1 o2 :
  match_spec ν P1 o1 → match_spec ν P2 o2 → match_spec ν (P1 ∧ P2) (match_and o1 o2).
Proof. destruct o1, o2; rewrite /= ?atoms_hold_app; tauto. Qed.

Local Lemma atoms_hold_eq ν t1 t2 :
  atoms_hold ν [Atom CEq t1 t2] ↔ term_eval ν t1 = term_eval ν t2.
Proof. rewrite /atoms_hold Forall_singleton //. Qed.

Lemma slit_match_spec ν l1 l2 : match_spec ν (ac_lit ν l1 = ac_lit ν l2) (slit_match l1 l2).
Proof.
  destruct l1, l2; rewrite /=; try case_decide; subst;
    rewrite /= ?atoms_hold_eq /ac_loc /ac_proph; try by intros [=].
  all: try (split; [by constructor|done]).
  - split; [by intros [=]|by intros ->].
  - split; [intros [= Heq]|by intros ->].
    apply (f_equal Z_of_proph) in Heq. by rewrite !Z_of_proph_of_Z in Heq.
Qed.

Lemma sexpr_sval_match_spec ν :
  (∀ e1 e2, match_spec ν (ac_expr ν e1 = ac_expr ν e2) (sexpr_match e1 e2)) ∧
  (∀ v1 v2, match_spec ν (ac_val ν v1 = ac_val ν v2) (sval_match v1 v2)).
Proof.
  apply sexpr_sval_mut_ind; intros;
    lazymatch goal with
    | |- match_spec _ _ (sexpr_match _ ?e2) => destruct e2
    | |- match_spec _ _ (sval_match _ ?v2) => destruct v2
    end;
    cbn [sexpr_match sval_match ac_expr ac_val];
    repeat case_decide; destruct_and?; subst;
    lazymatch goal with
    | |- match_spec _ _ None =>
      intros Heq; first [discriminate Heq|injection Heq; naive_solver]
    | |- match_spec _ _ (Some []) => split; [by constructor|done]
    | |- match_spec _ _ (slit_match _ _) =>
      eapply match_spec_iff; last apply slit_match_spec; split; [by intros ->|by intros [=]]
    | |- _ =>
      eapply match_spec_iff; last (repeat apply match_and_spec; eauto);
      split; [intros; destruct_and?; congruence|intros Heq; injection Heq; naive_solver]
    end.
Qed.

Lemma sval_match_spec ν v1 v2 :
  match_spec ν (ac_val ν v1 = ac_val ν v2) (sval_match v1 v2).
Proof. apply sexpr_sval_match_spec. Qed.

Lemma sval_eq_branches_sound ν v1 v2 b cs :
  (b, cs) ∈ sval_eq_branches v1 v2 → atoms_hold ν cs →
  bool_decide (ac_val ν v1 = ac_val ν v2) = b.
Proof.
  pose proof (sval_match_spec ν v1 v2) as Hspec.
  rewrite /sval_eq_branches. destruct (sval_match v1 v2) as [cs'|]; simpl in Hspec.
  - intros [[= -> ->]|(α & [= -> ->] & Hα)%list_elem_of_fmap]%elem_of_cons Hcs.
    + by apply bool_decide_eq_true, Hspec.
    + apply bool_decide_eq_false. rewrite Hspec. intros Hcs'.
      apply Forall_singleton, atom_neg_holds in Hcs. apply Hcs.
      by eapply Forall_forall.
  - intros [= -> ->]%list_elem_of_singleton _. by apply bool_decide_eq_false.
Qed.

Lemma sval_eq_branches_complete ν v1 v2 :
  ∃ cs, (bool_decide (ac_val ν v1 = ac_val ν v2), cs) ∈ sval_eq_branches v1 v2 ∧
    atoms_hold ν cs.
Proof.
  pose proof (sval_match_spec ν v1 v2) as Hspec.
  rewrite /sval_eq_branches. destruct (sval_match v1 v2) as [cs|]; simpl in Hspec.
  - case_bool_decide as Heq.
    + exists cs. split; [by apply elem_of_cons; left|by apply Hspec].
    + rewrite Hspec in Heq.
      apply not_Forall_Exists, Exists_exists in Heq as (α & Hα & Hnot); last apply _.
      exists [atom_neg α]. split.
      * apply elem_of_cons. right. apply list_elem_of_fmap. by exists α.
      * by apply Forall_singleton, atom_neg_holds.
  - rewrite bool_decide_eq_false_2 //. exists []. split; [by apply elem_of_cons; left|constructor].
Qed.

(** * Path conditions *)
Definition ssat (ν : valuation) (σ : sstate) : Prop := atoms_hold ν (scons σ).

(** An atom that never holds *)
Definition false_atom : atom := Atom CLt (Term None 0) (Term None 0).

Lemma false_atom_not_holds ν : ¬ atom_holds ν false_atom.
Proof. rewrite /atom_holds /=. lia. Qed.

Definition sunify (σ : sstate) (va : sval) (v : val) : sstate :=
  sstate_add_atoms (default [false_atom] (sval_match va (ca_val v))) σ.

Lemma ssat_ca_state ν σ : ssat ν (ca_state σ).
Proof. constructor. Qed.

Lemma ssat_decide σ : (∃ ν, ssat ν σ) ∨ ¬ (∃ ν, ssat ν σ).
Proof. apply atoms_hold_decide. Qed.

Lemma sunify_sat ν σ va v : ssat ν (sunify σ va v) ↔ ssat ν σ ∧ ac_val ν va = v.
Proof.
  pose proof (sval_match_spec ν va (ca_val v)) as Hspec. rewrite ac_ca_val in Hspec.
  rewrite /ssat /sunify /= atoms_hold_app.
  destruct (sval_match va (ca_val v)) as [cs|]; simpl in Hspec |- *.
  - rewrite Hspec. tauto.
  - rewrite /atoms_hold Forall_singleton. pose proof (false_atom_not_holds ν). tauto.
Qed.

Lemma sunify_ac_state ν σ va v : ac_state ν (sunify σ va v) = ac_state ν σ.
Proof. done. Qed.

(** * Well-formedness: all variables are below [snext] *)
Definition term_wf (n : nat) (t : term) : Prop :=
  match term_var t with Some x => (x < n)%nat | None => True end.
Definition atom_wf (n : nat) (α : atom) : Prop := term_wf n (atom_lhs α) ∧ term_wf n (atom_rhs α).
Definition slit_wf (n : nat) (l : slit) : Prop :=
  match l with SLitLoc t | SLitProphecy t => term_wf n t | _ => True end.

Fixpoint sexpr_wf (n : nat) (e : sexpr) : Prop :=
  match e with
  | SVal v => sval_wf n v
  | SVar _ | SNewProph => True
  | SRec _ _ e | SUnOp _ e | SFst e | SSnd e | SInjL e | SInjR e | SFree e | SLoad e
  | SFork e => sexpr_wf n e
  | SApp e1 e2 | SBinOp _ e1 e2 | SPair e1 e2 | SAllocN e1 e2 | SStore e1 e2
  | SXchg e1 e2 | SFAA e1 e2 => sexpr_wf n e1 ∧ sexpr_wf n e2
  | SIf e0 e1 e2 | SCase e0 e1 e2 | SCmpXchg e0 e1 e2 | SResolve e0 e1 e2 =>
    sexpr_wf n e0 ∧ sexpr_wf n e1 ∧ sexpr_wf n e2
  end
with sval_wf (n : nat) (v : sval) : Prop :=
  match v with
  | SLitV l => slit_wf n l
  | SRecV _ _ e => sexpr_wf n e
  | SPairV v1 v2 => sval_wf n v1 ∧ sval_wf n v2
  | SInjLV v | SInjRV v => sval_wf n v
  end.

Definition cell_wf (n : nat) (c : option sval) : Prop :=
  match c with Some v => sval_wf n v | None => True end.

Definition sstate_wf (σ : sstate) : Prop :=
  Forall (λ kc, term_wf (snext σ) kc.1 ∧ cell_wf (snext σ) kc.2) (sheap σ) ∧
  Forall (term_wf (snext σ)) (sused σ) ∧
  Forall (atom_wf (snext σ)) (scons σ).

Definition sexpr_wf_in (σ : sstate) (e : sexpr) : Prop := sexpr_wf (snext σ) e.

Lemma ca_wf n : (∀ e, sexpr_wf n (ca_expr e)) ∧ (∀ v, sval_wf n (ca_val v)).
Proof.
  apply expr_val_mut_ind; intros; simpl; auto.
  match goal with |- slit_wf _ (ca_lit ?l) => by destruct l end.
Qed.

Lemma sstate_wf_ca_state σ : sstate_wf (ca_state σ).
Proof.
  rewrite /sstate_wf /=. split_and!.
  - apply Forall_fmap, Forall_forall. intros [l c] _. split; first done.
    destruct c; [apply ca_wf|done].
  - apply Forall_fmap, Forall_forall. done.
  - done.
Qed.

Lemma sexpr_wf_in_ca σa e : sexpr_wf_in σa (ca_expr e).
Proof. apply ca_wf. Qed.

Lemma sexpr_sval_match_wf n :
  (∀ e1 e2 cs, sexpr_wf n e1 → sexpr_wf n e2 → sexpr_match e1 e2 = Some cs →
    Forall (atom_wf n) cs) ∧
  (∀ v1 v2 cs, sval_wf n v1 → sval_wf n v2 → sval_match v1 v2 = Some cs →
    Forall (atom_wf n) cs).
Proof.
  apply sexpr_sval_mut_ind; intros;
    lazymatch goal with
    | H : sexpr_match _ ?e2 = Some _ |- _ => rename H into Hmatch; destruct e2
    | H : sval_match _ ?v2 = Some _ |- _ => rename H into Hmatch; destruct v2
    end;
    cbn [sexpr_match sval_match sexpr_wf sval_wf] in *;
    repeat case_decide; destruct_and?; subst; try discriminate Hmatch.
  all: repeat match goal with
    | H : match_and ?o1 ?o2 = Some _ |- _ =>
      destruct o1 eqn:?, o2 eqn:?; simpl in H; [injection H as <-|discriminate H..];
      apply Forall_app; split
    end; eauto.
  all: try (injection Hmatch as <-; constructor).
  (* literals *)
  all: lazymatch goal with
    | H : slit_match ?l1 ?l2 = Some _ |- _ =>
      destruct l1, l2; simpl in *; try case_decide; simplify_eq/=;
        first [by constructor|apply Forall_singleton; by split]
    end.
Qed.

Lemma sstate_wf_sunify σ va v :
  sstate_wf σ → sexpr_wf_in σ (SVal va) → sstate_wf (sunify σ va v).
Proof.
  intros (Hh & Hu & Hc) Hva. rewrite /sstate_wf /sunify /=. split_and!; [done|done|].
  apply Forall_app. split; last done.
  destruct (sval_match va (ca_val v)) as [cs|] eqn:Hmatch; simpl.
  - eapply sexpr_sval_match_wf; [exact Hva|apply ca_wf|exact Hmatch].
  - apply Forall_singleton. by split.
Qed.

Lemma sexpr_wf_in_sunify σ va v e : sexpr_wf_in σ e → sexpr_wf_in (sunify σ va v) e.
Proof. done. Qed.

(** ** Concretization only depends on the variables below the bound *)
Lemma term_eval_agree ν ν' n t :
  (∀ x, (x < n)%nat → ν x = ν' x) → term_wf n t → term_eval ν t = term_eval ν' t.
Proof.
  intros Hagree. destruct t as [[x|] o]; rewrite /term_wf /term_eval /term_base /=; last done.
  intros Hx. by rewrite Hagree.
Qed.

Lemma ac_agree ν ν' n :
  (∀ x, (x < n)%nat → ν x = ν' x) →
  (∀ e, sexpr_wf n e → ac_expr ν e = ac_expr ν' e) ∧
  (∀ v, sval_wf n v → ac_val ν v = ac_val ν' v).
Proof.
  intros Hagree. apply sexpr_sval_mut_ind; intros; simpl in *; destruct_and?; f_equal; auto.
  match goal with |- ac_lit _ ?l = _ => destruct l end; simpl in *; try done.
  - rewrite /ac_loc. f_equal. f_equal. by eapply term_eval_agree.
  - rewrite /ac_proph. do 2 f_equal. by eapply term_eval_agree.
Qed.
