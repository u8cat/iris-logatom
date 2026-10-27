(* gadv_step.v: deciding bounded executions of a most adversarial client of a
   symbolically executable language. *)
(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From stdpp Require Import gmap.
From iris.program_logic Require Import language.
From iris_logatom.lib Require Import labeled_relations.
From iris_logatom.pure_logic Require Import lang_step_decidable.

(** * Most adversarial clients of a generic language *)

(** A configuration of a most adversarial client: the pending operations, the
threads forked by operations, and the state. *)
Record gconfig (Λ : language) := GConfig {
  gc_pending : list (positive * option (expr Λ));
  gc_children : list (expr Λ);
  gc_state : state Λ;
}.
Global Arguments GConfig {_} _ _ _.
Global Arguments gc_pending {_} _.
Global Arguments gc_children {_} _.
Global Arguments gc_state {_} _.

Inductive glabel (Λ : language) :=
  | GCall (n : nat) (v : val Λ)
  | GRet (v : val Λ).
Global Arguments GCall {_} _ _.
Global Arguments GRet {_} _.

Section gadv_step.
  Context {Λ : language} (call : nat → val Λ → expr Λ) (vr : nat → val Λ → Prop).

  (** [adv_step] of [linear.v] for a generic language *)
  Inductive gadv_step : relationL (gconfig Λ) (positive * glabel Λ) :=
    | gadv_step_call n v τ π efs σ :
      τ ∉ π.*1 → vr n v →
      gadv_step (GConfig π efs σ) (GConfig (π ++ [(τ, Some (call n v))]) efs σ) [(τ, GCall n v)]
    | gadv_step_intermediate τ π₁ π₂ efs e e' σ σ' κ ef :
      prim_step e σ κ e' σ' ef →
      gadv_step (GConfig (π₁ ++ (τ, Some e) :: π₂) efs σ)
        (GConfig (π₁ ++ (τ, Some e') :: π₂) (efs ++ ef) σ') []
    | gadv_step_child π efs1 efs2 e e' σ σ' κ ef :
      prim_step e σ κ e' σ' ef →
      gadv_step (GConfig π (efs1 ++ e :: efs2) σ) (GConfig π (efs1 ++ e' :: efs2 ++ ef) σ') []
    | gadv_step_return τ π₁ π₂ efs v σ :
      gadv_step (GConfig (π₁ ++ (τ, Some (of_val v)) :: π₂) efs σ)
        (GConfig (π₁ ++ (τ, None) :: π₂) efs σ) [(τ, GRet v)].
End gadv_step.

(** * Decidability helpers *)
Local Lemma dec_iff (P Q : Prop) : (P ↔ Q) → P ∨ ¬ P → Q ∨ ¬ Q.
Proof. tauto. Qed.

Local Lemma dec_or (P Q : Prop) : P ∨ ¬ P → Q ∨ ¬ Q → (P ∨ Q) ∨ ¬ (P ∨ Q).
Proof. tauto. Qed.

Local Lemma dec_exists_list {A} (l : list A) (P : A → Prop) :
  (∀ x, x ∈ l → P x ∨ ¬ P x) → (∃ x, x ∈ l ∧ P x) ∨ ¬ (∃ x, x ∈ l ∧ P x).
Proof.
  induction l as [|y l IH]; intros Hdec.
  { right. intros (x & Hx & _). by apply elem_of_nil in Hx. }
  destruct (Hdec y) as [Hy|Hy]; first by apply elem_of_cons; left.
  { left. exists y. split; [by apply elem_of_cons; left|done]. }
  destruct IH as [(x & Hx & HPx)|Hnone].
  { intros x Hx. apply Hdec. apply elem_of_cons. by right. }
  - left. exists x. split; [by apply elem_of_cons; right|done].
  - right. intros (x & [->|Hx]%elem_of_cons & HPx); first done.
    apply Hnone. eauto.
Qed.

Local Lemma dec_exists_split {A} (l : list A) (P : list A → A → list A → Prop) :
  (∀ l1 x l2, l = l1 ++ x :: l2 → P l1 x l2 ∨ ¬ P l1 x l2) →
  (∃ l1 x l2, l = l1 ++ x :: l2 ∧ P l1 x l2) ∨ ¬ (∃ l1 x l2, l = l1 ++ x :: l2 ∧ P l1 x l2).
Proof.
  revert P. induction l as [|y l IH]; intros P Hdec.
  { right. intros ([|??] & x & l2 & Heq & _); discriminate Heq. }
  destruct (Hdec [] y l) as [Hy|Hy]; first done.
  { left. by exists [], y, l. }
  destruct (IH (λ l1 x l2, P (y :: l1) x l2)) as [(l1 & x & l2 & -> & HP)|Hnone].
  { intros l1 x l2 ->. by apply Hdec. }
  - left. by exists (y :: l1), x, l2.
  - right. intros ([|y' l1] & x & l2 & Heq & HP).
    + injection Heq as -> ->. done.
    + injection Heq as -> ->. apply Hnone. eauto.
Qed.

Local Lemma bstepsL_0_inv {A B} (R : relationL A B) x z l :
  bstepsL R 0 x z l → x = z ∧ l = [].
Proof. inversion 1. done. Qed.

Local Lemma bstepsL_S_inv {A B} (R : relationL A B) n x z l :
  bstepsL R (Datatypes.S n) x z l ↔
    (x = z ∧ l = []) ∨ ∃ y l1 l2, R x y l1 ∧ bstepsL R n y z l2 ∧ l = l1 ++ l2.
Proof.
  split.
  - inversion 1; eauto 10.
  - intros [[-> ->]|(y & l1 & l2 & HR & Hsteps & ->)].
    + apply bstepsL_refl.
    + by eapply bstepsL_l.
Qed.

(** * Symbolic execution of a most adversarial client *)
Section sadv_step.
  Context {Λc Λa : language} `{!LanguageAbsInterp Λc Λa}.
  Context (call : nat → val Λc → expr Λc) (vr : nat → val Λc → Prop).
  Implicit Types (a : assignment Λc Λa) (C : gconfig Λa) (c : gconfig Λc).

  (** The adversary runs on symbolic configurations, but emits concrete
  labels: a call injects the (variable-free) abstraction of the concrete
  call, and a return of an abstract value adds the condition that it
  concretizes to the returned concrete value. *)
  Inductive sadv_step : relationL (gconfig Λa) (positive * glabel Λc) :=
    | sadv_step_call n v τ π efs σ :
      τ ∉ π.*1 → vr n v →
      sadv_step (GConfig π efs σ)
        (GConfig (π ++ [(τ, Some (ca_e (call n v)))]) efs σ) [(τ, GCall n v)]
    | sadv_step_intermediate τ π₁ π₂ efs e e' σ σ' κ ef :
      prim_step e σ κ e' σ' ef →
      sadv_step (GConfig (π₁ ++ (τ, Some e) :: π₂) efs σ)
        (GConfig (π₁ ++ (τ, Some e') :: π₂) (efs ++ ef) σ') []
    | sadv_step_child π efs1 efs2 e e' σ σ' κ ef :
      prim_step e σ κ e' σ' ef →
      sadv_step (GConfig π (efs1 ++ e :: efs2) σ) (GConfig π (efs1 ++ e' :: efs2 ++ ef) σ') []
    | sadv_step_return τ π₁ π₂ efs va v σ :
      sadv_step (GConfig (π₁ ++ (τ, Some (of_val va)) :: π₂) efs σ)
        (GConfig (π₁ ++ (τ, None) :: π₂) efs (unify σ va v)) [(τ, GRet v)].

  (** A symbolic execution emitting [ts] whose path condition is satisfiable *)
  Definition sadv_emit k C ts :=
    ∃ C', bstepsL sadv_step k C C' ts ∧ ∃ a, sat a (gc_state C').

  Definition ac_pending a (p : positive * option (expr Λa)) : positive * option (expr Λc) :=
    (p.1, ac_e a <$> p.2).
  Definition ac_config a C : gconfig Λc :=
    GConfig (ac_pending a <$> gc_pending C) (ac_e a <$> gc_children C) (ac_s a (gc_state C)).
  Definition ca_config c : gconfig Λa :=
    GConfig ((λ p : positive * option (expr Λc), (p.1, ca_e <$> p.2)) <$> gc_pending c)
      (ca_e <$> gc_children c) (ca_s (gc_state c)).

  Definition wf_pending σ (π : list (positive * option (expr Λa))) :=
    Forall (λ p, ∀ e, p.2 = Some e → wf_expr σ e) π.
  Definition wf_config C :=
    wf_state (gc_state C) ∧ wf_pending (gc_state C) (gc_pending C)
    ∧ Forall (wf_expr (gc_state C)) (gc_children C).

  (** ** Basic facts *)
  Lemma ac_e_of_val a va : ac_e a (of_val va) = of_val (ac_v a va).
  Proof. symmetry. apply of_to_val. by rewrite ac_to_val to_of_val. Qed.

  Lemma ac_e_of_val_inv a e v :
    ac_e a e = of_val v → ∃ va, e = of_val va ∧ ac_v a va = v.
  Proof.
    intros Hv. assert (to_val (ac_e a e) = Some v) as Hto by rewrite Hv to_of_val //.
    rewrite ac_to_val in Hto.
    destruct (to_val e) as [va|] eqn:He; last discriminate Hto.
    injection Hto as <-. exists va. split; last done.
    symmetry. by apply of_to_val.
  Qed.

  Lemma ac_pending_fst a π : (ac_pending a <$> π).*1 = π.*1.
  Proof. induction π as [|p π IH]; first done. by rewrite !fmap_cons IH. Qed.

  Lemma ac_pending_agree a a' σ π :
    wf_pending σ π → (∀ e, wf_expr σ e → ac_e a' e = ac_e a e) →
    ac_pending a' <$> π = ac_pending a <$> π.
  Proof.
    intros Hwf Hagree. induction Hwf as [|[τ [e|]] π He Hwf IH]; first done.
    - rewrite !fmap_cons IH /ac_pending /= Hagree //. by apply He.
    - by rewrite !fmap_cons IH.
  Qed.

  Lemma ac_children_agree a a' σ efs :
    Forall (wf_expr σ) efs → (∀ e, wf_expr σ e → ac_e a' e = ac_e a e) →
    ac_e a' <$> efs = ac_e a <$> efs.
  Proof.
    intros Hwf Hagree. induction Hwf as [|e efs He Hwf IH]; first done.
    by rewrite !fmap_cons IH Hagree.
  Qed.

  Lemma wf_pending_mono σ σ' π :
    (∀ e, wf_expr σ e → wf_expr σ' e) → wf_pending σ π → wf_pending σ' π.
  Proof.
    intros Hmono Hwf. eapply Forall_impl; first exact Hwf.
    intros p Hp e He. by apply Hmono, Hp.
  Qed.

  Lemma ac_config_ca_config a c : ac_config a (ca_config c) = c.
  Proof.
    destruct c as [π efs σ].
    rewrite /ac_config /ca_config /= ac_ca_s -!list_fmap_compose.
    f_equal.
    - rewrite -{2}(list_fmap_id π). apply list_fmap_ext. intros i [τ [e|]] _; last done.
      by rewrite /ac_pending /= ac_ca_e.
    - rewrite -{2}(list_fmap_id efs). apply list_fmap_ext. intros i e _.
      by rewrite /= ac_ca_e.
  Qed.

  Lemma wf_config_ca_config c : wf_config (ca_config c).
  Proof.
    destruct c as [π efs σ]. split_and!; simpl.
    - apply wf_state_ca_s.
    - apply Forall_fmap, Forall_forall. intros [τ [e|]] _ e' [= <-]. apply wf_expr_ca_e.
    - apply Forall_fmap, Forall_forall. intros e _. apply wf_expr_ca_e.
  Qed.

  (** ** Soundness *)
  Lemma sadv_step_sound a C C' l :
    sadv_step C C' l → sat a (gc_state C') →
    gadv_step call vr (ac_config a C) (ac_config a C') l ∧ sat a (gc_state C).
  Proof.
    intros Hstep Hsat.
    destruct Hstep as [n v τ π efs σ Hfresh Hvr
      |τ π₁ π₂ efs e e' σ σ' κ ef Hprim
      |π efs1 efs2 e e' σ σ' κ ef Hprim
      |τ π₁ π₂ efs va v σ];
      rewrite /ac_config /=; simpl in Hsat.
    - split; last done.
      rewrite fmap_app /= /ac_pending /= ac_ca_e.
      apply gadv_step_call; last done.
      rewrite -/(ac_pending a) ac_pending_fst //.
    - destruct (prim_step_ac a _ _ _ _ _ _ Hprim Hsat) as [κc Hprimc].
      split; last by eapply prim_step_sat.
      rewrite !fmap_app !fmap_cons /=.
      by eapply gadv_step_intermediate.
    - destruct (prim_step_ac a _ _ _ _ _ _ Hprim Hsat) as [κc Hprimc].
      split; last by eapply prim_step_sat.
      rewrite !fmap_app !fmap_cons !fmap_app /=.
      by eapply gadv_step_child.
    - apply unify_sat in Hsat as [Hsat <-].
      split; last done.
      rewrite unify_ac_s !fmap_app !fmap_cons /ac_pending /= ac_e_of_val.
      apply gadv_step_return.
  Qed.

  Lemma sadv_steps_sound a k C C' ts :
    bstepsL sadv_step k C C' ts → sat a (gc_state C') →
    bstepsL (gadv_step call vr) k (ac_config a C) (ac_config a C') ts ∧ sat a (gc_state C).
  Proof.
    induction 1 as [k C|k C C1 C' l ts Hstep Hsteps IH]; intros Hsat.
    { split; [apply bstepsL_refl|done]. }
    destruct (IH Hsat) as [Hsteps' Hsat1].
    destruct (sadv_step_sound a _ _ _ Hstep Hsat1) as [Hstep' Hsat0].
    split; last done. by eapply bstepsL_l.
  Qed.

  (** ** Completeness *)
  Lemma gadv_step_complete c c' l :
    gadv_step call vr c c' l →
    ∀ a C, c = ac_config a C → sat a (gc_state C) → wf_config C →
    ∃ C' a', sadv_step C C' l ∧ c' = ac_config a' C' ∧ sat a' (gc_state C') ∧ wf_config C'.
  Proof.
    intros Hstep a [πa efsa σa] Heq Hsat (Hwfσ & Hwfπ & Hwfefs).
    rewrite /ac_config /= in Heq. simpl in Hsat, Hwfσ, Hwfπ, Hwfefs.
    destruct Hstep as [n v τ π efs σ Hfresh Hvr
      |τ π₁ π₂ efs e e' σ σ' κ ef Hprim
      |π efs1 efs2 e e' σ σ' κ ef Hprim
      |τ π₁ π₂ efs v σ];
      injection Heq as Hπ Hefs Hσ.
    - (* call *)
      subst π efs σ.
      exists (GConfig (πa ++ [(τ, Some (ca_e (call n v)))]) efsa σa), a.
      split_and!.
      + apply sadv_step_call; last done. by rewrite ac_pending_fst in Hfresh.
      + rewrite /ac_config /= fmap_app /= /ac_pending /= ac_ca_e //.
      + done.
      + split_and!; simpl; [done| |done].
        apply Forall_app. split; first done.
        apply Forall_singleton. intros e [= <-]. apply wf_expr_ca_e.
    - (* intermediate step of a pending operation *)
      subst efs σ. symmetry in Hπ.
      apply fmap_app_inv in Hπ as (π₁a & πrest & -> & Hrest & ->).
      symmetry in Hrest. apply fmap_cons_inv in Hrest as ([τa [ea|]] & π₂a & Hp & -> & ->);
        rewrite /ac_pending /= in Hp; injection Hp as -> Hea; [subst e|discriminate Hea].
      rewrite /wf_pending Forall_app Forall_cons in Hwfπ.
      destruct Hwfπ as (Hwfπ₁ & Hwfea & Hwfπ₂).
      assert (wf_expr σa ea) as Hwfea' by by apply Hwfea.
      destruct (prim_step_ca _ _ _ _ _ _ _ Hsat Hwfσ Hwfea' Hprim)
        as (κa & ea' & σa' & efsa' & a' & Hprima & Hsat' & -> & -> & -> & Hagree).
      destruct (prim_step_wf _ _ _ _ _ _ Hprima Hwfσ Hwfea')
        as (Hwfσ' & Hwfea'' & Hwfefsa' & Hmono).
      exists (GConfig (π₁a ++ (τa, Some ea') :: π₂a) (efsa ++ efsa') σa'), a'.
      split_and!.
      + by eapply sadv_step_intermediate.
      + rewrite /ac_config /= fmap_app fmap_cons fmap_app.
        rewrite (ac_pending_agree a a' σa π₁a) // (ac_pending_agree a a' σa π₂a) //.
        rewrite (ac_children_agree a a' σa efsa) //.
      + done.
      + split_and!; simpl; first done.
        * rewrite /wf_pending Forall_app Forall_cons.
          split_and!; [by eapply wf_pending_mono| |by eapply wf_pending_mono].
          intros e0 [= <-]. done.
        * apply Forall_app. split; last done.
          eapply Forall_impl; first exact Hwfefs. done.
    - (* step of a forked thread *)
      subst π σ. symmetry in Hefs.
      apply fmap_app_inv in Hefs as (efs1a & efsrest & -> & Hrest & ->).
      symmetry in Hrest. apply fmap_cons_inv in Hrest as (ea & efs2a & -> & -> & ->).
      rewrite Forall_app Forall_cons in Hwfefs.
      destruct Hwfefs as (Hwfefs1 & Hwfea & Hwfefs2).
      destruct (prim_step_ca _ _ _ _ _ _ _ Hsat Hwfσ Hwfea Hprim)
        as (κa & ea' & σa' & efsa' & a' & Hprima & Hsat' & -> & -> & -> & Hagree).
      destruct (prim_step_wf _ _ _ _ _ _ Hprima Hwfσ Hwfea)
        as (Hwfσ' & Hwfea' & Hwfefsa' & Hmono).
      exists (GConfig πa (efs1a ++ ea' :: efs2a ++ efsa') σa'), a'.
      split_and!.
      + by eapply sadv_step_child.
      + rewrite /ac_config /= fmap_app fmap_cons fmap_app.
        rewrite (ac_pending_agree a a' σa πa) //.
        rewrite (ac_children_agree a a' σa efs1a) // (ac_children_agree a a' σa efs2a) //.
      + done.
      + split_and!; simpl; [done|by eapply wf_pending_mono|].
        rewrite Forall_app Forall_cons Forall_app.
        split_and!; [| | |done].
        * eapply Forall_impl; first exact Hwfefs1. done.
        * done.
        * eapply Forall_impl; first exact Hwfefs2. done.
    - (* return *)
      subst efs σ. symmetry in Hπ.
      apply fmap_app_inv in Hπ as (π₁a & πrest & -> & Hrest & ->).
      symmetry in Hrest. apply fmap_cons_inv in Hrest as ([τa [ea|]] & π₂a & Hp & -> & ->);
        rewrite /ac_pending /= in Hp; injection Hp as -> Hea; last done.
      symmetry in Hea. apply ac_e_of_val_inv in Hea as (va & -> & <-).
      rewrite /wf_pending Forall_app Forall_cons in Hwfπ.
      destruct Hwfπ as (Hwfπ₁ & Hwfva & Hwfπ₂).
      assert (wf_expr σa (of_val va)) as Hwfva' by by apply Hwfva.
      exists (GConfig (π₁a ++ (τa, None) :: π₂a) efsa (unify σa va (ac_v a va))), a.
      split_and!.
      + apply sadv_step_return.
      + rewrite /ac_config /= unify_ac_s fmap_app fmap_cons //.
      + by apply unify_sat.
      + split_and!; simpl.
        * by apply wf_state_unify.
        * rewrite /wf_pending Forall_app Forall_cons.
          split_and!; [|done|];
            (eapply wf_pending_mono; last done); intros e; apply wf_expr_unify.
        * eapply Forall_impl; first exact Hwfefs. intros e. apply wf_expr_unify.
  Qed.

  Lemma gadv_steps_complete k c c' ts :
    bstepsL (gadv_step call vr) k c c' ts →
    ∀ a C, c = ac_config a C → sat a (gc_state C) → wf_config C → sadv_emit k C ts.
  Proof.
    induction 1 as [k c|k c c1 c' l ts Hstep Hsteps IH]; intros a C -> Hsat Hwf.
    { exists C. split; [apply bstepsL_refl|by exists a]. }
    destruct (gadv_step_complete _ _ _ Hstep a C eq_refl Hsat Hwf)
      as (C1 & a' & Hstep' & -> & Hsat' & Hwf').
    destruct (IH a' C1 eq_refl Hsat' Hwf') as (C' & Hsteps' & Hsat'').
    exists C'. split; last done. by eapply bstepsL_l.
  Qed.
End sadv_step.

(** ** Decidability of symbolic executions *)
Section sadv_decide.
  Context {Λc Λa : language} `{!BoundedLanguage Λa, !LanguageAbsInterp Λc Λa}.
  Context (call : nat → val Λc → expr Λc) (vr : nat → val Λc → Prop).
  Context (vr_decide : ∀ n v, vr n v ∨ ¬ vr n v).

  (** The symbolic steps emitting a prefix of [ts], by case *)
  Local Lemma sadv_step_cases (Q : gconfig Λa → list (positive * glabel Λc) → Prop) π efs σ ts :
    (∃ C1 l ts1, sadv_step call vr (GConfig π efs σ) C1 l ∧ ts = l ++ ts1 ∧ Q C1 ts1) ↔
    ((∃ τ n v ts1, ts = (τ, GCall n v) :: ts1 ∧ τ ∉ π.*1 ∧ vr n v ∧
        Q (GConfig (π ++ [(τ, Some (ca_e (call n v)))]) efs σ) ts1)
    ∨ (∃ π₁ p π₂, π = π₁ ++ p :: π₂ ∧ ∃ e, p.2 = Some e ∧
        ∃ κ e' σ' ef, prim_step e σ κ e' σ' ef ∧
          Q (GConfig (π₁ ++ (p.1, Some e') :: π₂) (efs ++ ef) σ') ts)
    ∨ (∃ efs1 e efs2, efs = efs1 ++ e :: efs2 ∧
        ∃ κ e' σ' ef, prim_step e σ κ e' σ' ef ∧
          Q (GConfig π (efs1 ++ e' :: efs2 ++ ef) σ') ts)
    ∨ (∃ τ v ts1, ts = (τ, GRet v) :: ts1 ∧ ∃ π₁ p π₂, π = π₁ ++ p :: π₂ ∧ p.1 = τ ∧
        ∃ va, p.2 = Some (of_val va) ∧
          Q (GConfig (π₁ ++ (τ, None) :: π₂) efs (unify σ va v)) ts1)).
  Proof.
    split.
    - intros (C1 & l & ts1 & Hstep & -> & HQ).
      remember (GConfig π efs σ) as C eqn:HC.
      destruct Hstep as [n v τ π' efs' σ' Hfresh Hvr
        |τ π₁ π₂ efs' e e' σ' σ'' κ ef Hprim
        |π' efs1 efs2 e e' σ' σ'' κ ef Hprim
        |τ π₁ π₂ efs' va v σ'];
        injection HC as <- <- <-.
      + left. by exists τ, n, v, ts1.
      + right; left. exists π₁, (τ, Some e), π₂. split; first done.
        exists e. split; first done. by exists κ, e', σ'', ef.
      + right; right; left. exists efs1, e, efs2. split; first done.
        by exists κ, e', σ'', ef.
      + right; right; right. exists τ, v, ts1. split; first done.
        exists π₁, (τ, Some (of_val va)), π₂. split_and!; [done|done|].
        by exists va.
    - intros [Hcall|[Hinter|[Hchild|Hret]]].
      + destruct Hcall as (τ & n & v & ts1 & -> & Hfresh & Hvr & HQ).
        eexists _, [_], ts1. split_and!; [|done|done].
        by apply sadv_step_call.
      + destruct Hinter as (π₁ & [τ oe] & π₂ & -> & e & Hoe & κ & e' & σ' & ef & Hprim & HQ).
        simpl in Hoe, HQ. subst oe.
        eexists _, [], ts. split_and!; [|done|done].
        by eapply sadv_step_intermediate.
      + destruct Hchild as (efs1 & e & efs2 & -> & κ & e' & σ' & ef & Hprim & HQ).
        eexists _, [], ts. split_and!; [|done|done].
        by eapply sadv_step_child.
      + destruct Hret as (τ & v & ts1 & -> & π₁ & [τ' oe] & π₂ & -> & Hτ & va & Hoe & HQ).
        simpl in Hτ, Hoe. subst τ' oe.
        eexists _, [_], ts1. split_and!; [|done|done].
        apply sadv_step_return.
  Qed.

  (** Some step of a thread from [e] continues to a configuration satisfying [Q] *)
  Local Lemma dec_prim_step e σ (Q : expr Λa → state Λa → list (expr Λa) → Prop) :
    (∀ e' σ' ef, Q e' σ' ef ∨ ¬ Q e' σ' ef) →
    (∃ κ e' σ' ef, prim_step e σ κ e' σ' ef ∧ Q e' σ' ef) ∨
    ¬ (∃ κ e' σ' ef, prim_step e σ κ e' σ' ef ∧ Q e' σ' ef).
  Proof.
    intros HQ. destruct (prim_step_bounded e σ) as [L HL].
    eapply dec_iff; last first.
    { apply (dec_exists_list L (λ x, Q x.1.1.2 x.1.2 x.2)). intros x _. apply HQ. }
    split.
    - intros ([[[κ e'] σ'] ef] & Hx & HQx). exists κ, e', σ', ef. by rewrite HL.
    - intros (κ & e' & σ' & ef & Hprim & HQx). exists (κ, e', σ', ef). by rewrite -HL.
  Qed.

  Lemma sadv_emit_decide k C ts :
    sadv_emit call vr k C ts ∨ ¬ sadv_emit call vr k C ts.
  Proof.
    revert C ts. induction k as [|k IH]; intros [π efs σ] ts.
    { eapply (dec_iff (ts = [] ∧ ∃ a, sat a σ)).
      - split.
        + intros [-> Hsat]. exists (GConfig π efs σ). split; [apply bstepsL_refl|done].
        + intros (C' & [<- ->]%bstepsL_0_inv & Hsat). done.
      - destruct ts; [destruct (sat_decide σ)|]; naive_solver. }
    eapply (dec_iff ((ts = [] ∧ ∃ a, sat a σ) ∨
      ∃ C1 l ts1, sadv_step call vr (GConfig π efs σ) C1 l ∧ ts = l ++ ts1 ∧
        sadv_emit call vr k C1 ts1)).
    { split.
      - intros [[-> Hsat]|(C1 & l & ts1 & Hstep & -> & C' & Hsteps & Hsat)].
        + exists (GConfig π efs σ). split; [apply bstepsL_refl|done].
        + exists C'. split; last done. by eapply bstepsL_l.
      - intros (C' & [[<- ->]|(C1 & l & ts1 & Hstep & Hsteps & ->)]%bstepsL_S_inv & Hsat).
        + by left.
        + right. exists C1, l, ts1. split_and!; [done|done|]. by exists C'. }
    apply dec_or.
    { destruct ts; [destruct (sat_decide σ)|]; naive_solver. }
    eapply dec_iff; first (symmetry; apply sadv_step_cases).
    apply dec_or; [|apply dec_or; [|apply dec_or]].
    - (* call *)
      destruct ts as [|[τ [n v|v]] ts1].
      1,3: right; intros (τ' & n' & v' & ts1' & Heq & _); discriminate Heq.
      destruct (decide (τ ∈ π.*1)) as [Hin|Hfresh].
      { right. intros (τ' & n' & v' & ts1' & [= <- <- <- <-] & Hfresh & _). done. }
      destruct (vr_decide n v) as [Hvr|Hvr].
      2: { right. intros (τ' & n' & v' & ts1' & [= <- <- <- <-] & _ & Hvr' & _). done. }
      destruct (IH (GConfig (π ++ [(τ, Some (ca_e (call n v)))]) efs σ) ts1) as [HQ|HQ].
      + left. by exists τ, n, v, ts1.
      + right. intros (τ' & n' & v' & ts1' & [= <- <- <- <-] & _ & _ & HQ'). done.
    - (* intermediate step of a pending operation *)
      apply dec_exists_split. intros π₁ [τ [e|]] π₂ _; simpl.
      2: { right. intros (e & Hoe & _). discriminate Hoe. }
      eapply (dec_iff (∃ κ e' σ' ef, prim_step e σ κ e' σ' ef ∧
        sadv_emit call vr k (GConfig (π₁ ++ (τ, Some e') :: π₂) (efs ++ ef) σ') ts)).
      { split.
        - intros HQ. by exists e.
        - intros (e0 & [= <-] & HQ). done. }
      apply dec_prim_step. intros e' σ' ef. apply IH.
    - (* step of a forked thread *)
      apply dec_exists_split. intros efs1 e efs2 _.
      apply dec_prim_step. intros e' σ' ef. apply IH.
    - (* return *)
      destruct ts as [|[τ [n v|v]] ts1].
      1,2: right; intros (τ' & v' & ts1' & Heq & _); discriminate Heq.
      eapply (dec_iff (∃ π₁ p π₂, π = π₁ ++ p :: π₂ ∧ p.1 = τ ∧
        ∃ va, p.2 = Some (of_val va) ∧
          sadv_emit call vr k (GConfig (π₁ ++ (τ, None) :: π₂) efs (unify σ va v)) ts1)).
      { split.
        - intros HQ. by exists τ, v, ts1.
        - intros (τ' & v' & ts1' & [= <- <- <-] & HQ). done. }
      apply dec_exists_split. intros π₁ [τ' [e|]] π₂ _; simpl.
      2: { right. intros (_ & va & Hoe & _). discriminate Hoe. }
      destruct (decide (τ' = τ)) as [->|Hne].
      2: { right. intros (Hτ & _). done. }
      destruct (to_val e) as [va|] eqn:He.
      + apply of_to_val in He as <-.
        eapply (dec_iff (sadv_emit call vr k
          (GConfig (π₁ ++ (τ, None) :: π₂) efs (unify σ va v)) ts1)).
        { split.
          - intros HQ. split; first done. by exists va.
          - intros (_ & va' & [= Hva%(inj of_val)] & HQ). by subst va'. }
        apply IH.
      + right. intros (_ & va & [= ->] & _). by rewrite to_of_val in He.
  Qed.
End sadv_decide.

(** * Decidability of bounded executions of a most adversarial client *)
Theorem gadv_emit_decide `{!LanguageSymbolicExecutable Λ}
    (call : nat → val Λ → expr Λ) (vr : nat → val Λ → Prop) :
  (∀ n v, vr n v ∨ ¬ vr n v) →
  ∀ k c ts,
    (∃ c', bstepsL (gadv_step call vr) k c c' ts) ∨
    ¬ (∃ c', bstepsL (gadv_step call vr) k c c' ts).
Proof.
  intros vr_decide k c ts.
  destruct (sadv_emit_decide call vr vr_decide k (ca_config c) ts)
    as [(C' & Hsteps & a & Hsat)|Hnot].
  - left. exists (ac_config a C').
    rewrite -(ac_config_ca_config a c).
    by apply (sadv_steps_sound call vr a k _ _ ts Hsteps Hsat).
  - right. intros (c' & Hsteps).
    destruct (sat_ca_s (gc_state c)) as [a Hsat].
    apply Hnot. eapply gadv_steps_complete; first exact Hsteps.
    + symmetry. apply (ac_config_ca_config a c).
    + exact Hsat.
    + apply wf_config_ca_config.
Qed.
