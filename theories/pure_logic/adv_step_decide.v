From iris_logatom.pure_logic Require Import linear lang_step_decidable gadv_step.
From iris_logatom.heap_lang.decide Require Import instance.
From iris.heap_lang Require Import lang notation.

(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

(** * The most adversarial client of heap_lang *)
Section logatom.
  Context `{M : model}.
  Context (init : expr) (ops : list val) (valid_obj : val → state → Prop).

  Definition adv_steps_emit obj config steps_left (ts : list (positive*trace)) :=
    ∃ config', bstepsL (adv_step ops obj valid_requests) steps_left config config' ts.

  Local Definition to_gconfig (config : configuration) : gconfig heap_lang :=
    GConfig config.(config_pendingOp) config.(config_childThread) config.(config_state).
  Local Definition of_gconfig (C : gconfig heap_lang) : configuration :=
    Config (gc_pending C) (gc_children C) (gc_state C).

  Local Definition trace_of_glabel (t : positive * glabel heap_lang) : positive * trace :=
    match t with
    | (τ, GCall n v) => (τ, Call n v)
    | (τ, GRet v) => (τ, Ret v)
    end.
  (** [Lin] is never emitted; it is mapped to an arbitrary label *)
  Local Definition glabel_of_trace (t : positive * trace) : positive * glabel heap_lang :=
    match t with
    | (τ, Call n v) => (τ, GCall n v)
    | (τ, Lin _ _ v) => (τ, GRet v)
    | (τ, Ret v) => (τ, GRet v)
    end.

  Local Definition heap_lang_call (obj : val) (n : nat) (v : val) : expr := (ops!!!n : val) obj v.
  Local Definition heap_lang_vr (n : nat) (v : val) : Prop :=
    default default_vr (valid_requests!!n) v.

  Local Lemma adv_steps_gadv_steps obj k config config' ts :
    bstepsL (adv_step ops obj valid_requests) k config config' ts →
    Forall (λ t, ¬ is_lin t.2) ts ∧
    bstepsL (gadv_step (heap_lang_call obj) heap_lang_vr) k
      (to_gconfig config) (to_gconfig config') (glabel_of_trace <$> ts).
  Proof.
    induction 1 as [k config|k config config1 config' l ts Hstep Hsteps IH].
    { split; [done|apply bstepsL_refl]. }
    destruct IH as [Hnolin Hsteps'].
    rewrite Forall_app fmap_app.
    destruct Hstep as [n v τ π efs σ Hfresh Hvr
      |τ π₁ π₂ efs e e' σ σ' κ ef Hprim
      |π efs1 efs2 e e' σ σ' κ ef Hprim
      |τ π₁ π₂ efs v σ].
    - split_and!; [apply Forall_singleton; by intros []|done|].
      eapply bstepsL_l; last exact Hsteps'.
      by apply (gadv_step_call (heap_lang_call obj) heap_lang_vr n v τ π efs σ).
    - split_and!; [done|done|].
      eapply bstepsL_l; last exact Hsteps'.
      by eapply gadv_step_intermediate.
    - split_and!; [done|done|].
      eapply bstepsL_l; last exact Hsteps'.
      by eapply gadv_step_child.
    - split_and!; [apply Forall_singleton; by intros []|done|].
      eapply bstepsL_l; last exact Hsteps'.
      apply (gadv_step_return _ _ τ π₁ π₂ efs v σ).
  Qed.

  Local Lemma gadv_steps_adv_steps obj k C C' gts :
    bstepsL (gadv_step (heap_lang_call obj) heap_lang_vr) k C C' gts →
    bstepsL (adv_step ops obj valid_requests) k
      (of_gconfig C) (of_gconfig C') (trace_of_glabel <$> gts).
  Proof.
    induction 1 as [k C|k C C1 C' l gts Hstep Hsteps IH]; first apply bstepsL_refl.
    rewrite fmap_app.
    eapply bstepsL_l; last exact IH.
    destruct Hstep as [n v τ π efs σ Hfresh Hvr
      |τ π₁ π₂ efs e e' σ σ' κ ef Hprim
      |π efs1 efs2 e e' σ σ' κ ef Hprim
      |τ π₁ π₂ efs v σ].
    - by apply adv_step_call.
    - by eapply adv_step_intermediate.
    - by eapply adv_step_child.
    - apply adv_step_return.
  Qed.

  Lemma adv_steps_emit_decide `{!ModelDecidable M} obj config steps_left ts :
    (adv_steps_emit obj config steps_left ts) ∨ ¬(adv_steps_emit obj config steps_left ts).
  Proof.
    destruct (decide (Forall (λ t, ¬ is_lin t.2) ts)) as [Hnolin|Hlin].
    - destruct (gadv_emit_decide (heap_lang_call obj) heap_lang_vr
        model_valid_request_decide steps_left (to_gconfig config) (glabel_of_trace <$> ts))
        as [(C' & Hsteps)|Hnot].
      + left. exists (of_gconfig C').
        apply gadv_steps_adv_steps in Hsteps.
        replace (trace_of_glabel <$> (glabel_of_trace <$> ts)) with ts in Hsteps.
        { by destruct config. }
        rewrite -list_fmap_compose -{1}(list_fmap_id ts).
        apply list_fmap_ext. intros i [τ [n v|n v v'|v]] Hi; [done| |done].
        exfalso. apply (Forall_lookup_1 _ _ _ _ Hnolin Hi). exact I.
      + right. intros (config' & Hsteps).
        apply Hnot. exists (to_gconfig config').
        by apply adv_steps_gadv_steps in Hsteps as [_ Hsteps].
    - right. intros (config' & Hsteps).
      by apply adv_steps_gadv_steps in Hsteps as [Hnolin _].
  Qed.
End logatom.
