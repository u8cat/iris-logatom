(* atomic_sound.v *)

From iris_logatom.lib Require Import list namespace.
From iris_logatom.pure_logic Require Import encodable.
From iris.proofmode Require Import base ltac_tactics.
From iris.base_logic Require Import invariants ghost_map.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc.

Inductive tag_state :=
  | AfterCall: nat → val → tag_state
  | AfterLin: nat → val → val → tag_state
  | AfterRet.

Class logicatomicityG Σ := {
  #[local] logatom_meta :: inG Σ (agreeR (prodO gnameO gnameO));
  #[local] logatom_state :: ghost_mapG Σ positive tag_state;
}.

Definition logicatomicityΣ := #[
  GFunctor (agreeRF (prodO gnameO gnameO));
  ghost_mapΣ positive tag_state].
Global Instance subG_logicatomicityG Σ : subG logicatomicityΣ Σ → logicatomicityG Σ.
Proof. solve_inG. Qed.

(* LLM-generated local lemma *)
(* A tag absent from a trace contributes no events to the per-tag filter. *)
Local Lemma fresh_tag_filter_eq_nil (τ : positive) (ts : list (positive*trace)) :
  τ ∉ events_of_trace ts →
  filter (λ x : positive*trace, x.1 = τ) ts = [].
Proof.
  intros Hfresh. apply filter_False_nil, Forall_forall.
  intros [τ' t] Hin Heq. simpl in Heq. subst τ'.
  apply Hfresh, elem_of_list_to_set, list_elem_of_fmap.
  by exists (τ, t).
Qed.

(* LLM-generated local lemma *)
(* In a per_tag_linearized trace, every tag that appears at all appears with a
   Call event, which survives the [filter (not∘is_lin∘snd)] projection. *)
Local Lemma tag_in_filter_not_lin (τ : positive) (ts : list (positive*trace)) :
  per_tag_linearized ts →
  τ ∈ events_of_trace ts →
  τ ∈ (filter (not ∘ is_lin ∘ snd) ts).*1.
Proof.
  intros Hper_tag Hin.
  destruct (Hper_tag τ) as (n & v & v' & [k Hk]).
  destruct (filter (λ x, x.1 = τ) ts) as [|hd rest] eqn:Hfilter.
  - exfalso. apply elem_of_list_to_set in Hin.
    apply list_elem_of_fmap in Hin as ([τ' t] & Heq & Hin).
    simpl in Heq. subst τ'.
    assert ((τ, t) ∈ filter (λ x : positive*trace, x.1 = τ) ts) as Hcontra.
    { apply list_elem_of_filter. split; done. }
    rewrite Hfilter in Hcontra. by apply not_elem_of_nil in Hcontra.
  - rewrite -app_comm_cons in Hk. injection Hk as Hhd _. subst hd.
    assert (Hcall : (τ, Call n v) ∈ ts).
    { eapply (list_elem_of_filter_1 (λ x : positive*trace, x.1 = τ)).
      rewrite Hfilter. rewrite elem_of_cons. by left. }
    apply list_elem_of_fmap. exists (τ, Call n v). split; first done.
    apply list_elem_of_filter. split; last exact Hcall.
    by intros HF.
Qed.

Section def.
  Context `{M : model} `{!logicatomicityG Σ, !traceG Σ}
    (N : namespace)
    (is_P : heapGS Σ → gname → val → iProp Σ)
    (P_state : heapGS Σ → gname → S → iProp Σ)
    `{!∀ H γ v, Persistent (is_P H γ v)}.

  Definition logatom_sound_inv_content `{!heapGS Σ} γ tracer : iProp Σ :=
    ∃ γi γm s ts' (ST : gmap positive tag_state), ⌜dom ST = events_of_trace ts' ⌝
      ∗ own γ (to_agree (γi,γm)) ∗ P_state _ γi s ∗ ghost_map_auth γm 1 ST
      ∗ trace_is tracer (filter (not∘is_lin∘snd) ts')
      ∗ ⌜call_valid (filter (not∘is_lin∘snd) ts')⌝
      ∗ ⌜rtcL model_step s_init s (filter (is_lin∘snd) ts')⌝
      ∗ ⌜per_tag_linearized ts'⌝
      ∗ [∗ map] τ↦st ∈ ST, ⌜ match st with
        | AfterCall n v => filter (λ x, x.1 = τ) ts' = [(τ, Call n v)]
        | AfterLin n v v' => filter (λ x, x.1 = τ) ts' = [(τ, Call n v); (τ, Lin n v v')]
        | AfterRet => True
        end⌝.

  Definition logatom_sound_inv `{!heapGS Σ} tracer γ v : iProp Σ :=
    ∃ γi γm, own γ (to_agree (γi,γm)) ∗ is_P _ γi v ∗
      inv (fresh_namespace2 N traceN) (logatom_sound_inv_content γ tracer).

  Definition logatom_repr : mgc_repr Σ := {|
    I_lang := trace_linearizable;
    mgc_inv := @logatom_sound_inv |}.
End def.

Section spec.
  Context `{M : model} `{!logicatomicityG Σ, !traceG Σ}
    (init : expr) (ops : list val)
    (N : namespace)
    (is_P : heapGS Σ → gname → val → iProp Σ)
    (P_state : heapGS Σ → gname → S → iProp Σ)
    (Hdisj : N ## traceN)
    `{!∀ H γ v, Persistent (is_P H γ v)}
    `{!∀ H γ s, Timeless (P_state H γ s)}.

  Hypothesis init_spec :
    ∀ `(!heapGS Σ),
    {{{ True }}} init {{{ γ r, RET r; is_P _ γ r ∗ P_state _ γ s_init }}}.

  Hypothesis op_spec :
    ∀ `(!heapGS Σ) n γ (x y: val), default default_vr (valid_requests!!n) y → is_P _ γ x ⊢
      <<{ ∀∀ s, P_state _ γ s }>>
        (ops!!!n : val) x y @ ↑N
      <<{ ∃∃ s' y', P_state _ γ s' ∗ ⌜default default_rr (request_responses!!n) s y s' y'⌝ | RET y' }>>.

  Lemma mgc_init_spec `{!heapGS Σ} : init_spec_type (logatom_repr N is_P P_state) NotStuck init.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_fupd.
    wp_apply (init_spec with "[//]") as (γi obj) "[His_P HP_state]".
    iMod ghost_map_alloc_empty as (γm) "HM●".
    iMod (own_alloc (to_agree (γi, γm))) as (γ) "#Hmeta"; first done.
    iApply "HΦ". iIntros "!>" (tracer) "Htrace_is". simpl.
    iExists γi, γm. iFrame "Hmeta His_P".
    iApply inv_alloc. iNext.
    iExists γi, γm, s_init, [], ∅.
    rewrite !filter_nil. iFrame "#∗".
    iPureIntro. split_and!.
    - reflexivity.
    - rewrite /call_valid Forall_nil //.
    - apply rtcL_refl.
    - apply per_tag_linearized_nil.
    - apply map_Forall_empty.
  Qed.

  Lemma call_ret_wrapper_spec `{!heapGS Σ} : call_ret_wrapper_spec_type (logatom_repr N is_P P_state) NotStuck valid_requests ops.
  Proof.
    destruct (fresh_namespace2_disjoint _ _ Hdisj) as [Hdisj1 Hdisj2].
    iIntros (n γ tracer obj req Hvr Φ) "[#Htrace_inv #Hmgc_inv] HΦ".
    iDestruct "Hmgc_inv" as (γi γm) "(Hmeta & His_P & Inv)".

    (* Call *)
    wp_lam. wp_pures.
    awp_apply (trace_fresh_spec with "Htrace_inv");
      first exact (decode_encode_val (Call n req)).
    iInv "Inv" as (γi' γm' s ts' ST) ">(%Hdom & #Hmeta' & HP_state & HM● & Htrace_is & %Hcall_valid & %Hmsteps & %Hper_tag_lin & %Hst)".
    iCombine "Hmeta Hmeta'" gives %Heq%to_agree_op_inv_L.
    injection Heq as <- <-. iClear "Hmeta'".
    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iFrame "Htrace_is". iSplit.
    { iPureIntro. intros τ Hfresh.
      split; last (exists (ts'++[(τ,Call n req)]); split_and!).
      - rewrite /call_valid Forall_app Forall_singleton //.
      - rewrite filter_app filter_cons_True; last by auto.
        done.
      - intros τ₀. destruct (decide (τ=τ₀)) as [<- | Hne].
        + exists n, req, inhabitant.
          rewrite filter_app filter_False_nil.
          * rewrite left_id_L filter_cons_True // filter_nil.
            eexists. done.
          * apply Forall_forall.
            intros [τ' t] Hτ'_in Heq. apply Hfresh.
            simpl in Heq. subst τ'.
            apply tag_in_filter_not_lin; first done.
            apply elem_of_list_to_set, list_elem_of_fmap.
            exists (τ, t). split; done.
        + destruct (Hper_tag_lin τ₀) as (n₀ & v₀ & v₀' & Hfilter).
          exists n₀, v₀, v₀'.
          rewrite filter_app filter_cons_False // filter_nil right_id_L.
          done.
      - exists s.
        rewrite filter_app filter_cons_False; last auto.
        rewrite filter_nil right_id_L. assumption. }
    iSplit.
    { iIntros "[Htrace_is _]". iMod "Hclose" as "_".
      iModIntro. iFrame "HΦ".
      iNext. iFrame "Hmeta HP_state HM● Htrace_is".
      auto. }
    iIntros (τ) "[Htrace_is %Hfresh]". iMod "Hclose" as "_".
    assert (Hτ_notin_ST : ST !! τ = None).
    { apply not_elem_of_dom. rewrite Hdom.
      intros Hin. apply Hfresh. by apply tag_in_filter_not_lin. }
    iMod (ghost_map_insert τ (AfterCall n req) with "HM●") as "[HM● HM◯]"; first done.
    iModIntro. iSplitR "HΦ HM◯".
    { iNext. iFrame "Hmeta HM● HP_state".
      iExists (ts'++[(τ,Call n req)]).
      iSplit.
      { iPureIntro. rewrite dom_insert_L Hdom /events_of_trace fmap_app list_to_set_app_L /=.
        set_solver. }
      iSplitL "Htrace_is".
      { rewrite filter_app filter_cons_True; last auto.
        rewrite filter_nil //. }
      iPureIntro. split_and!.
      - rewrite filter_app /call_valid Forall_app.
        split; first exact Hcall_valid.
        rewrite filter_cons_True; last by intros HF.
        rewrite filter_nil Forall_singleton //.
      - rewrite filter_app filter_cons_False; last by intros HF.
        rewrite filter_nil app_nil_r. exact Hmsteps.
      - intros τ₀. destruct (decide (τ = τ₀)) as [<- | Hne].
        + exists n, req, inhabitant.
          rewrite filter_app (fresh_tag_filter_eq_nil τ ts').
          * rewrite left_id_L filter_cons_True // filter_nil.
            by eexists.
          * intros Hin. apply Hfresh. by apply tag_in_filter_not_lin.
        + destruct (Hper_tag_lin τ₀) as (n₀ & v₀ & v₀' & Hfilter).
          exists n₀, v₀, v₀'.
          rewrite filter_app filter_cons_False // filter_nil right_id_L. done.
      - intros τ' st Hlookup'.
        destruct (decide (τ = τ')) as [<- | Hne].
        + rewrite lookup_insert_eq in Hlookup'. injection Hlookup' as <-.
          simpl. rewrite filter_app.
          rewrite (fresh_tag_filter_eq_nil τ ts');
            last (intros Hin; apply Hfresh; by apply tag_in_filter_not_lin).
          rewrite filter_cons_True // filter_nil //.
        + rewrite lookup_insert_ne in Hlookup'; last done.
          specialize (Hst τ' st Hlookup').
          destruct st; simpl in Hst |- *.
          * rewrite filter_app filter_cons_False; last done.
            rewrite filter_nil. by rewrite app_nil_r.
          * rewrite filter_app filter_cons_False; last done.
            rewrite filter_nil. by rewrite app_nil_r.
          * done. }
    clear s ts' ST Hdom Hcall_valid Hmsteps Hper_tag_lin Hst Hfresh Hτ_notin_ST.

    (* Lin *)
    wp_pures.
    awp_apply (op_spec with "His_P"); first done.
    iInv "Inv" as (γi' γm' s ts' ST) ">(%Hdom & #Hmeta' & HP_state & HM● & Htrace_is & %Hcall_valid & %Hmsteps & %Hper_tag_lin & %Hst)".
    iCombine "Hmeta Hmeta'" gives %Heq%to_agree_op_inv_L.
    injection Heq as <- <-. iClear "Hmeta'".
    iCombine "HM● HM◯" gives %Hlookup.
    iAaccIntro with "HP_state"; first auto 7 with iFrame.
    iIntros (s' res) "[HP_state %Hrr]".
    iMod (ghost_map_update (AfterLin n req res) with "HM● HM◯") as "[HM● HM◯]".
    iModIntro. iSplitR "HΦ HM◯".
    { iNext. iFrame "Hmeta HM● HP_state".
      iExists (ts'++[(τ,Lin n req res)]).
      iSplit.
      { iPureIntro. rewrite dom_insert_L Hdom.
        apply elem_of_dom_2 in Hlookup. rewrite Hdom in Hlookup.
        rewrite /events_of_trace fmap_app list_to_set_app_L /=.
        set_solver. }
      iSplitL "Htrace_is".
      { rewrite filter_app filter_cons_False; last by simpl; intros [].
        by rewrite filter_nil app_nil_r. }
      iPureIntro. split_and!.
      - rewrite filter_app filter_cons_False; last by simpl; intros [].
        rewrite filter_nil app_nil_r. exact Hcall_valid.
      - rewrite filter_app filter_cons_True; last by simpl.
        rewrite filter_nil.
        eapply rtcL_r; [|constructor]; [exact Hmsteps|exact Hvr|exact Hrr].
      - intros τ₀. destruct (decide (τ = τ₀)) as [<- | Hne].
        + exists n, req, res.
          specialize (Hst τ (AfterCall n req) Hlookup). simpl in Hst.
          rewrite filter_app Hst filter_cons_True // filter_nil.
          by eexists [_].
        + destruct (Hper_tag_lin τ₀) as (n₀ & v₀ & v₀' & Hfilter).
          exists n₀, v₀, v₀'.
          rewrite filter_app filter_cons_False // filter_nil app_nil_r. done.
      - intros τ' st Hlookup'.
        destruct (decide (τ = τ')) as [<- | Hne].
        + rewrite lookup_insert_eq in Hlookup'. injection Hlookup' as <-.
          simpl. specialize (Hst τ (AfterCall n req) Hlookup). simpl in Hst.
          rewrite filter_app Hst filter_cons_True // filter_nil //.
        + rewrite lookup_insert_ne in Hlookup'; last done.
          specialize (Hst τ' st Hlookup').
          destruct st; simpl in Hst |- *.
          * rewrite filter_app filter_cons_False; last done.
            rewrite filter_nil. by rewrite app_nil_r.
          * rewrite filter_app filter_cons_False; last done.
            rewrite filter_nil. by rewrite app_nil_r.
          * done. }
    clear s s' ts' ST Hdom Hcall_valid Hmsteps Hper_tag_lin Hst Hrr Hlookup.

    (* Ret *)
    wp_pures.
    awp_apply (trace_emit_spec with "Htrace_inv"); first reflexivity.
    iInv "Inv" as (γi' γm' s ts' ST) ">(%Hdom & #Hmeta' & HP_state & HM● & Htrace_is & %Hcall_valid & %Hmsteps & %Hper_tag_lin & %Hst)".
    iCombine "Hmeta Hmeta'" gives %Heq%to_agree_op_inv_L.
    injection Heq as <- <-. iClear "Hmeta'".
    iCombine "HM● HM◯" gives %Hlookup.
    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iFrame "Htrace_is". iSplit.
    { iPureIntro.
      split; last (exists (ts'++[(τ,Ret res)]); split_and!).
      - rewrite /call_valid Forall_app Forall_singleton //.
      - rewrite filter_app filter_cons_True; last by auto.
        done.
      - intros τ₀. destruct (decide (τ = τ₀)) as [<- | Hne].
        + exists n, req, res.
          specialize (Hst τ (AfterLin n req res) Hlookup). simpl in Hst.
          rewrite filter_app Hst.
          rewrite filter_cons_True; last done.
          rewrite filter_nil.
          by exists [].
        + destruct (Hper_tag_lin τ₀) as (n₀ & v₀ & v₀' & Hfilter).
          exists n₀, v₀, v₀'.
          rewrite filter_app filter_cons_False // filter_nil app_nil_r. done.
      - exists s.
        rewrite filter_app filter_cons_False; last auto.
        rewrite filter_nil app_nil_r. assumption. }
    iSplit.
    { iIntros "[Htrace_is _]". iMod "Hclose" as "_".
      iModIntro. iFrame "HM◯ HΦ".
      iNext. iFrame "Hmeta HP_state HM● Htrace_is".
      auto. }
    iIntros "Htrace_is". iMod "Hclose" as "_".
    iMod (ghost_map_update AfterRet with "HM● HM◯") as "[HM● HM◯]".
    iModIntro. iSplitR "HΦ HM◯".
    { iNext. iFrame "Hmeta HM● HP_state".
      iExists (ts'++[(τ,Ret res)]).
      iSplit.
      { iPureIntro. rewrite dom_insert_L.
        apply elem_of_dom_2 in Hlookup. rewrite Hdom in Hlookup.
        rewrite /events_of_trace fmap_app list_to_set_app_L /=.
        set_solver. }
      iSplitL "Htrace_is".
      { rewrite filter_app filter_cons_True; last auto.
        rewrite filter_nil //. }
      iPureIntro. split_and!.
      - rewrite filter_app /call_valid Forall_app.
        split; first exact Hcall_valid.
        rewrite filter_cons_True; last by auto.
        rewrite filter_nil Forall_singleton //.
      - rewrite filter_app filter_cons_False; last by auto.
        rewrite filter_nil app_nil_r. exact Hmsteps.
      - intros τ₀. destruct (decide (τ = τ₀)) as [<- | Hne].
        + exists n, req, res.
          specialize (Hst τ (AfterLin n req res) Hlookup). simpl in Hst.
          rewrite filter_app Hst.
          rewrite filter_cons_True; last done.
          rewrite filter_nil.
          by exists [].
        + destruct (Hper_tag_lin τ₀) as (n₀ & v₀ & v₀' & Hfilter).
          exists n₀, v₀, v₀'.
          rewrite filter_app filter_cons_False // filter_nil app_nil_r. done.
      - intros τ' st Hlookup'.
        destruct (decide (τ = τ')) as [<- | Hne].
        + rewrite lookup_insert_eq in Hlookup'. injection Hlookup' as <-. done.
        + rewrite lookup_insert_ne in Hlookup'; last done.
          specialize (Hst τ' st Hlookup').
          destruct st; simpl in Hst |- *.
          * rewrite filter_app filter_cons_False; last done.
            rewrite filter_nil. by rewrite app_nil_r.
          * rewrite filter_app filter_cons_False; last done.
            rewrite filter_nil. by rewrite app_nil_r.
          * done. }

    wp_pures. iModIntro. by iApply "HΦ".
  Qed.
End spec.

Section logatom.
  Context `{!heapGpreS Σ, M : model, !logicatomicityG Σ, traceG Σ}.
  Context (init : expr) (ops : list val).

  Theorem logatom_sound N
    (is_P : heapGS Σ → gname → val → iProp Σ) (P_state : heapGS Σ → gname → S → iProp Σ)
    `{!∀ H γ v, Persistent (is_P H γ v)} `{!∀ H γ s, Timeless (P_state H γ s)}:
    N ## traceN →
    (∀ `(!heapGS Σ), {{{ True }}} init {{{ γ r, RET r; is_P _ γ r ∗ P_state _ γ s_init }}}) →
    (∀ `(!heapGS Σ) n γ (x y: val), default default_vr (valid_requests!!n) y → is_P _ γ x ⊢
      <<{ ∀∀ s, P_state _ γ s }>>
        (ops!!!n : val) x y @ ↑N
      <<{ ∃∃ s' y', P_state _ γ s' ∗ ⌜default default_rr (request_responses!!n) s y s' y'⌝ | RET y' }>>) →
    library_initializable_linearizable init ops.
  Proof.
    intros Hdisj init_spec op_spec.
    split.
    - intros σ. apply (heap_adequacy Σ NotStuck _ σ (λ _, True)).
      iIntros (?) "_". iApply init_spec; auto.
    - intros obj σ₀ t σ config' ts Herased_steps Hadv_steps.
      eapply (bdgjst_free (logatom_repr N is_P P_state)).
      + intros ?. eapply mgc_init_spec; by eauto.
      + intros ?. eapply call_ret_wrapper_spec; by eauto.
      + apply trace_linearizable_nil.
      + exact Herased_steps.
      + exact Hadv_steps.
  Qed.
End logatom.
