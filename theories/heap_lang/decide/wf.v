(* wf.v: symbolic heap_lang steps preserve well-formedness. *)
(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From stdpp Require Import ssreflect list numbers list_numbers gmap.
From iris.program_logic Require Import language.
From iris_logatom.heap_lang.decide Require Export concretize.
From iris.heap_lang Require Import lang.

(** * Monotonicity *)
Lemma term_wf_mono n m t : (n ≤ m)%nat → term_wf n t → term_wf m t.
Proof. intros Hnm. destruct t as [[x|] o]; rewrite /term_wf /=; [lia|done]. Qed.

Lemma atom_wf_mono n m α : (n ≤ m)%nat → atom_wf n α → atom_wf m α.
Proof. intros Hnm [??]. split; by eapply term_wf_mono. Qed.

Lemma wf_mono n m :
  (n ≤ m)%nat → (∀ e, sexpr_wf n e → sexpr_wf m e) ∧ (∀ v, sval_wf n v → sval_wf m v).
Proof.
  intros Hnm. apply sexpr_sval_mut_ind; intros; simpl in *; destruct_and?; eauto 10.
  match goal with |- slit_wf _ ?l => destruct l end; simpl in *; eauto using term_wf_mono.
Qed.

Lemma sexpr_wf_mono n m e : (n ≤ m)%nat → sexpr_wf n e → sexpr_wf m e.
Proof. intros. by eapply wf_mono. Qed.
Lemma sval_wf_mono n m v : (n ≤ m)%nat → sval_wf n v → sval_wf m v.
Proof. intros. by eapply wf_mono. Qed.
Lemma cell_wf_mono n m c : (n ≤ m)%nat → cell_wf n c → cell_wf m c.
Proof. destruct c; simpl; eauto using sval_wf_mono. Qed.

(** * Language constructs *)
Lemma ssubst_wf n x v e : sval_wf n v → sexpr_wf n e → sexpr_wf n (ssubst x v e).
Proof.
  intros Hv. induction e; simpl; intros; destruct_and?; repeat case_decide; simpl; naive_solver.
Qed.

Lemma ssubst'_wf n mx v e : sval_wf n v → sexpr_wf n e → sexpr_wf n (ssubst' mx v e).
Proof. destruct mx; simpl; [done|apply ssubst_wf]. Qed.

Lemma atom_neg_wf n α : atom_wf n α → atom_wf n (atom_neg α).
Proof. destruct α as [[] t1 t2]; rewrite /atom_wf /=; naive_solver. Qed.

Lemma sun_op_eval_wf n op v v' : sun_op_eval op v = Some v' → sval_wf n v'.
Proof. destruct op, v as [l| | | |]; try done; destruct l; simpl; by intros [= <-]. Qed.

Lemma sval_eq_branches_wf n v1 v2 b cs :
  (b, cs) ∈ sval_eq_branches v1 v2 → sval_wf n v1 → sval_wf n v2 → Forall (atom_wf n) cs.
Proof.
  rewrite /sval_eq_branches. intros Hin Hwf1 Hwf2.
  destruct (sval_match v1 v2) as [cs'|] eqn:Hmatch.
  - pose proof (proj2 (sexpr_sval_match_wf n) v1 v2 cs' Hwf1 Hwf2 Hmatch) as Hcs'.
    apply elem_of_cons in Hin as [[= -> ->]|(α & [= -> ->] & Hα)%list_elem_of_fmap]; first done.
    apply Forall_singleton, atom_neg_wf. by eapply Forall_forall.
  - apply list_elem_of_singleton in Hin. by injection Hin as -> ->.
Qed.

Lemma sbin_op_eval_wf n op v1 v2 v cs :
  (v, cs) ∈ sbin_op_eval op v1 v2 → sval_wf n v1 → sval_wf n v2 →
  sval_wf n v ∧ Forall (atom_wf n) cs.
Proof.
  rewrite /sbin_op_eval. intros Hin Hwf1 Hwf2. case_decide.
  - destruct (svals_compare_safe v1 v2); last by apply elem_of_nil in Hin.
    apply list_elem_of_fmap in Hin as ([b cs'] & [= -> ->] & Hin).
    split; first done. by eapply sval_eq_branches_wf.
  - destruct v1 as [l1| | | |]; try (by apply elem_of_nil in Hin).
    destruct l1; try (by apply elem_of_nil in Hin).
    all: destruct v2 as [l2| | | |]; try (by apply elem_of_nil in Hin).
    all: destruct l2; simpl in Hin; try (by apply elem_of_nil in Hin).
    (* integers and booleans *)
    all: try (case_match eqn:Hl; [|by apply elem_of_nil in Hin];
      apply list_elem_of_singleton in Hin; injection Hin as -> ->;
      split; [|constructor];
      apply bind_Some in Hl as (bl & _ & Hbl); destruct bl; by simplify_eq/=).
    (* locations *)
    all: apply list_elem_of_fmap in Hin as ([lr cs'] & [= -> ->] & Hin).
    all: destruct op; simpl in Hin; try (by apply elem_of_nil in Hin).
    all: repeat (apply elem_of_cons in Hin as [Hin|Hin]); try (by apply elem_of_nil in Hin).
    all: injection Hin as -> ->; simpl in *; split; try done.
    all: try (apply Forall_singleton; by split).
Qed.

(** * States *)
Local Ltac wf_mono_tac :=
  first [eapply term_wf_mono|eapply sval_wf_mono|eapply cell_wf_mono|eapply atom_wf_mono];
  [|eassumption]; lia.

Lemma sstate_wf_add_atoms cs σ :
  sstate_wf σ → Forall (atom_wf (snext σ)) cs → sstate_wf (sstate_add_atoms cs σ).
Proof. intros (Hh & Hu & Hc) Hcs. split_and!; [done|done|]. by apply Forall_app. Qed.

Lemma sstate_wf_upd_heap l c σ :
  sstate_wf σ → term_wf (snext σ) l → cell_wf (snext σ) c → sstate_wf (sstate_upd_heap l c σ).
Proof. intros (Hh & Hu & Hc) Hl Hcell. split_and!; [by constructor|done|done]. Qed.

Lemma sstate_wf_alloc n v σ :
  sstate_wf σ → sval_wf (snext σ) v → sstate_wf (sstate_alloc n v σ).
Proof.
  intros (Hh & Hu & Hc) Hv. rewrite /sstate_wf /=. split_and!.
  - apply Forall_app. split.
    + apply Forall_fmap, Forall_forall. intros i _. split; [rewrite /term_wf /=; lia|].
      simpl. wf_mono_tac.
    + eapply Forall_impl; first exact Hh. intros [k c] [Hk Hcell]. simpl in *.
      split; [wf_mono_tac|wf_mono_tac].
  - eapply Forall_impl; first exact Hu. intros p Hp. wf_mono_tac.
  - apply Forall_app. split.
    + apply Forall_forall. intros α (i & Hα & _)%list_elem_of_bind.
      apply list_elem_of_fmap in Hα as ([k c] & -> & Hkc).
      pose proof (proj1 (Forall_forall _ _) Hh _ Hkc) as [Hk _].
      split; simpl; [rewrite /term_wf /=; lia|wf_mono_tac].
    + eapply Forall_impl; first exact Hc. intros α Hα. wf_mono_tac.
Qed.

Lemma sstate_wf_new_proph σ : sstate_wf σ → sstate_wf (sstate_new_proph σ).
Proof.
  intros (Hh & Hu & Hc). rewrite /sstate_wf /=. split_and!.
  - eapply Forall_impl; first exact Hh. intros [k c] [Hk Hcell]. simpl in *.
    split; [wf_mono_tac|wf_mono_tac].
  - constructor; [rewrite /term_wf /=; lia|].
    eapply Forall_impl; first exact Hu. intros p Hp. wf_mono_tac.
  - apply Forall_app. split.
    + apply Forall_fmap, Forall_forall. intros p Hp.
      pose proof (proj1 (Forall_forall _ _) Hu _ Hp) as Hwfp.
      split; simpl; [rewrite /term_wf /=; lia|wf_mono_tac].
    + eapply Forall_impl; first exact Hc. intros α Hα. wf_mono_tac.
Qed.

Lemma sheap_lookup_wf n l h c cs :
  (c, cs) ∈ sheap_lookup l h → Forall (λ kc, term_wf n kc.1 ∧ cell_wf n kc.2) h →
  term_wf n l → cell_wf n c ∧ Forall (atom_wf n) cs.
Proof.
  revert c cs. induction h as [|[k c'] h IH]; intros c cs; simpl.
  { by intros ?%elem_of_nil. }
  intros [[= -> ->]|([c0 cs0] & [= -> ->] & Hin)%list_elem_of_fmap]%elem_of_cons Hh Hl;
    apply Forall_cons in Hh as [[Hk Hcell] Hh].
  - split; first done. apply Forall_singleton. by split.
  - destruct (IH _ _ Hin Hh Hl) as [Hc Hcs]. split; first done.
    constructor; [by split|done].
Qed.

Lemma sstate_lookup_wf l σ v cs :
  (v, cs) ∈ sstate_lookup l σ → sstate_wf σ → term_wf (snext σ) l →
  sval_wf (snext σ) v ∧ Forall (atom_wf (snext σ)) cs.
Proof.
  rewrite /sstate_lookup list_elem_of_omap. intros ([[v'|] cs'] & Hin & Heq) (Hh & _) Hl;
    simplify_eq/=.
  by destruct (sheap_lookup_wf _ _ _ _ _ Hin Hh Hl).
Qed.

(** * Base steps *)
Definition base_wf_concl σ e' σ' efs : Prop :=
  sstate_wf σ' ∧ sexpr_wf (snext σ') e' ∧ Forall (sexpr_wf (snext σ')) efs ∧
  (snext σ ≤ snext σ')%nat.

Local Lemma resolve_wf t σ e' σ' efs q :
  sstate_wf σ → term_wf (snext σ) t → q ∈ sused σ →
  base_wf_concl σ e' σ' efs →
  base_wf_concl σ e' (sstate_add_atoms [Atom CEq t q] σ') efs.
Proof.
  intros Hwfσ Ht Hq (Hwfσ' & He' & Hefs & Hle). split_and!; [|done|done|done].
  apply sstate_wf_add_atoms; first done.
  destruct Hwfσ as (_ & Hu & _). pose proof (proj1 (Forall_forall _ _) Hu _ Hq) as Hwfq.
  apply Forall_singleton. split; simpl; wf_mono_tac.
Qed.

Lemma sbase_step_wf e σ e' σ' efs :
  (e', σ', efs) ∈ sbase_step e σ → sstate_wf σ → sexpr_wf (snext σ) e →
  base_wf_concl σ e' σ' efs.
Proof.
  revert e' σ' efs. induction e; intros e' σ' efs Hin Hwfσ Hwfe;
    cbn [sbase_step] in Hin; repeat case_match; subst; simpl in Hwfe; destruct_and?;
    try (by apply elem_of_nil in Hin).
  all: rewrite /base_wf_concl.
  all: lazymatch goal with
  | H : (_, _, _) ∈ (λ _, _) <$> sbin_op_eval _ _ _ |- _ =>
    apply list_elem_of_fmap in H as ([vr cr] & [= -> -> ->] & Hvcs);
    destruct (sbin_op_eval_wf _ _ _ _ _ _ Hvcs ltac:(done) ltac:(done)) as [Hvr Hcr];
    split_and!; [by apply sstate_wf_add_atoms|done|done|done]
  | H : (_, _, _) ∈ (λ _, _) <$> sstate_lookup _ _ |- _ =>
    apply list_elem_of_fmap in H as ([vr cr] & [= -> -> ->] & Hvcs);
    destruct (sstate_lookup_wf _ _ _ _ Hvcs ltac:(done) ltac:(done)) as [Hvr Hcr];
    split_and!; [|done|done|done];
    apply sstate_wf_add_atoms; [|done];
    first [done|by apply sstate_wf_upd_heap]
  | H : (_, _, _) ∈ sstate_lookup _ _ ≫= _ |- _ =>
    apply list_elem_of_bind in H as ([vr cr] & H & Hvcs);
    destruct (sstate_lookup_wf _ _ _ _ Hvcs ltac:(done) ltac:(done)) as [Hvr Hcr];
    simpl in H;
    (* [CmpXchg] or [FAA] *)
    repeat case_match; try (by apply elem_of_nil in H);
    first
      [ apply list_elem_of_fmap in H as ([b cb] & [= -> -> ->] & Hbcs);
        pose proof (sval_eq_branches_wf _ _ _ _ _ Hbcs Hvr ltac:(done)) as Hcb;
        destruct b; (split_and!; [|simpl; split; done|done|done]);
        (apply sstate_wf_add_atoms; [|by apply Forall_app]);
        first [done|by apply sstate_wf_upd_heap]
      | apply list_elem_of_singleton in H; injection H as -> -> ->;
        split_and!; [|done|done|done];
        apply sstate_wf_add_atoms; [|done]; by apply sstate_wf_upd_heap ]
  | H : (_, _, _) ∈ sbase_step _ _ ≫= _ |- _ =>
    (* [Resolve] *)
    apply list_elem_of_bind in H as ([[e0 σ0] efs0] & H & Hin0);
    destruct e0; simpl in H; try (by apply elem_of_nil in H);
    apply list_elem_of_fmap in H as (q & [= -> -> ->] & Hq);
    eapply resolve_wf; [done|done|done|by eauto]
  | H : (_, _, _) ∈ [_] |- _ =>
    apply list_elem_of_singleton in H; injection H as -> -> ->;
    first
      [ (* allocation *)
        split_and!; [by apply sstate_wf_alloc|rewrite /= /term_wf /=; lia|done|simpl; lia]
      | (* new prophecy *)
        split_and!; [by apply sstate_wf_new_proph|rewrite /= /term_wf /=; lia|done|simpl; lia]
      | split_and!; [done| |simpl; eauto|done];
        simpl; eauto using ssubst'_wf, sun_op_eval_wf ]
  end.
Qed.

(** * Steps *)
Lemma sexpr_wf_fill_item n Ki e : sexpr_wf n (sfill_item Ki e) → sexpr_wf n e.
Proof. induction Ki; simpl; naive_solver. Qed.

Lemma sexpr_wf_fill_item_mono n m Ki e e' :
  (n ≤ m)%nat → sexpr_wf n (sfill_item Ki e) → sexpr_wf m e' → sexpr_wf m (sfill_item Ki e').
Proof.
  intros Hnm. induction Ki; simpl; intros; destruct_and?; split_and?;
    eauto using sexpr_wf_mono, sval_wf_mono.
Qed.

Lemma sexpr_wf_fill_inv n K e :
  sexpr_wf n (@ectx_language.fill sym_heap_ectx_lang K e) → sexpr_wf n e.
Proof.
  induction K as [|Ki K IH] in e |- *; first done. intros Hwf.
  change (@ectx_language.fill sym_heap_ectx_lang (Ki :: K) e) with
    (@ectx_language.fill sym_heap_ectx_lang K (sfill_item Ki e)) in Hwf.
  apply IH in Hwf. by eapply sexpr_wf_fill_item.
Qed.

Lemma sexpr_wf_fill_mono n m K e e' :
  (n ≤ m)%nat →
  sexpr_wf n (@ectx_language.fill sym_heap_ectx_lang K e) → sexpr_wf m e' →
  sexpr_wf m (@ectx_language.fill sym_heap_ectx_lang K e').
Proof.
  intros Hnm. induction K as [|Ki K IH] in e, e' |- *; intros Hwf Hwf'; first done.
  change (@ectx_language.fill sym_heap_ectx_lang (Ki :: K) e) with
    (@ectx_language.fill sym_heap_ectx_lang K (sfill_item Ki e)) in Hwf.
  change (@ectx_language.fill sym_heap_ectx_lang (Ki :: K) e') with
    (@ectx_language.fill sym_heap_ectx_lang K (sfill_item Ki e')).
  apply (IH (sfill_item Ki e)); first done.
  eapply sexpr_wf_fill_item_mono; [done| |done]. by eapply sexpr_wf_fill_inv.
Qed.

Theorem sprim_step_wf e σ κ e' σ' efs :
  prim_step e σ κ e' σ' efs → sstate_wf σ → sexpr_wf (snext σ) e →
  sstate_wf σ' ∧ sexpr_wf (snext σ') e' ∧ Forall (sexpr_wf (snext σ')) efs ∧
    ∀ e0, sexpr_wf (snext σ) e0 → sexpr_wf (snext σ') e0.
Proof.
  intros [K e1 e2 -> -> [_ Hbase]] Hwfσ Hwfe.
  destruct (sbase_step_wf _ _ _ _ _ Hbase Hwfσ (sexpr_wf_fill_inv _ _ _ Hwfe))
    as (Hwfσ' & He2 & Hefs & Hle).
  split_and!; [done| |done|].
  - by eapply sexpr_wf_fill_mono.
  - intros e0 He0. by eapply sexpr_wf_mono.
Qed.
