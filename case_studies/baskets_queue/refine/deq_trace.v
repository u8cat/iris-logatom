(* refine_deq_trace.v: helper lemma for the trace_emit RET-DEQ step
  shared between LIN-DEQ1 and LIN-DEQ2 branches of [op_spec_deq_cont].

  The body opens the inv at the [trace_emit], identifies the dequeue
  τ's recorded return value via the persistent dq_map fragment,
  fires [absq_step_ret_deq] (advancing cp[τ] from R2 to R3), and
  re-establishes [bq_sim] for the post-RET state.

  Extracted to its own file so the trace_emit work compiles once
  and the LIN-DEQ1 head-CAS-success and head-CAS-fail branches can
  both dispatch via [iApply], avoiding ~150 lines of duplicated
  code per branch. *)

From iris.algebra Require Import auth excl gmap agree mono_list.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.baskets_queue Require Import impl refine.defs.

Section bq_skeleton_deq_trace.
  Context `{!traceG Σ, !bqG Σ}.

  Local Notation valid_value := bq_valid_value.
  Local Notation Nbq := Nbq.
  Local Notation bq_inv_body := bq_inv_body.

  Lemma op_spec_deq_trace_emit
    `{!heapGS Σ} (γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w : gname)
    (l head tail : loc)
    (τ : positive) (rng_init : nat) (v_dq : val) (Φ : val → iProp Σ) :
    inv Nbq (bq_inv_body γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w head tail l) -∗
    trace_inv l (I_lang_bq) -∗
    own γ (◯ {[τ := Excl {| op_info_kind := OpDeq [] rng_init;
                            op_info_node := None;
                            op_info_linked := true |}]}) -∗
    own γ_dq (◯ {[τ := to_agree v_dq]}) -∗
    (∀ v : val, True -∗ Φ v) -∗
    WP (trace_emit #l #(Z.pos τ) (InjRV v_dq) ;; v_dq) {{ v, Φ v }}.
  Proof.
    iIntros "#Hinv #Htrace_inv Hfrag #Hdq_τ_frag HΦ".
    wp_pures.
    wp_bind (trace_emit _ _ _)%E.
    awp_apply (trace_emit_spec l τ (Ret v_dq) (InjRV v_dq) I_lang_bq
                 with "Htrace_inv"); first done.
    iInv Nbq as (nodes_t del_pref_t head_val_t tail_val_t dummy_loc_t
                 ts_t s_t ls_t op_map_t node_map_t dq_map_t no_O_set_t witness_map_t)
      "(>Hhead_t & >Htail_t & Hchain_t & >Htrace_t & >Hauth_op_t
        & >Hauth_nm_t & Hfrag_nm_t & >Hauth_dq_t & Hfrag_dq_t & >Hauth_del_t
        & >Hauth_calls_t & >Hauth_no_O_t & >Hauth_ls_t & >Hauth_w_t & Hfrag_w_t & >%Hsteps_t
        & >%Hts_eq_t & >%Hsim_t & >%Hdummy_t & >%Hnvi_t & >%Hdqi_t
        & >%Hno_O_inv_t & >%Hcoi_t & >%Hwit_t)".
    iDestruct (own_valid_2 with "Hauth_op_t Hfrag") as %Hτ_both_t.
    apply auth_both_valid_discrete in Hτ_both_t as [Hτ_incl_t Hτ_valid_t].
    apply singleton_included_exclusive_l in Hτ_incl_t; [|apply _|done].
    rewrite lookup_fmap in Hτ_incl_t.
    apply leibniz_equiv in Hτ_incl_t.
    apply fmap_Some_1 in Hτ_incl_t as (info_τ_t & Hτ_in_op_t & Hinfo_τ_t).
    destruct info_τ_t; injection Hinfo_τ_t as <- <- <-.
    pose proof Hsim_t as (_ & _ & Hcp_in_ts_t & _ & _ & _ & Hdeq_clause_t & _).
    destruct (Hdeq_clause_t _ _ _ _ _ Hτ_in_op_t) as (_ & _ & Hcp_τ_R2_post).
    specialize (Hcp_τ_R2_post eq_refl) as (Hcp_τ_R2 & v_rv & Hrv_τ_v).
    (* Use [Hdq_τ_frag] to identify [v_rv = v_dq]. *)
    iDestruct (own_valid_2 with "Hauth_dq_t Hdq_τ_frag") as %Hdq_both_t.
    apply auth_both_valid_discrete in Hdq_both_t as [Hdq_incl_t _].
    apply singleton_included_l in Hdq_incl_t as (q & Hq_lookup & Hq_incl).
    rewrite /to_dqmap lookup_fmap in Hq_lookup.
    apply fmap_Some_equiv in Hq_lookup as (v_stored & Hdq_τ & Hq_eq).
    rewrite Hq_eq in Hq_incl.
    rewrite Some_included in Hq_incl.
    assert (v_stored = v_dq) as Hv_eq.
    { destruct Hq_incl as [Heq|Hin].
      - symmetry. by apply (inj to_agree), leibniz_equiv in Heq.
      - symmetry. rewrite to_agree_included in Hin. by apply leibniz_equiv. }
    rewrite Hv_eq in Hdq_τ.
    pose proof (Hdqi_t _ _ Hdq_τ) as Hrv_τ_v_dq.
    assert (v_rv = v_dq) as ->
      by (rewrite Hrv_τ_v in Hrv_τ_v_dq; injection Hrv_τ_v_dq; done).
    destruct s_t as [O_t lt_t ℓ_t rv_t cp_t]; simpl in Hcp_τ_R2, Hrv_τ_v.
    iAssert (trace_is l ts_t ∗
             ⌜I_lang_bq (ts_t ++ [(τ, Ret v_dq)])⌝)%I
      with "[$Htrace_t]" as "Halpha".
    { iPureIntro.
      exists (AbsQState O_t lt_t ℓ_t rv_t (<[τ := R3]> cp_t)),
             (ls_t ++ [(τ, ARetDeq v_dq)]).
      split.
      - eapply rtcL_r; [exact Hsteps_t|].
        by apply absq_step_ret_deq.
      - rewrite Hts_eq_t /trace_of_absq_labels map_app /= filter_app.
        rewrite filter_cons_True; [done|]. by compute. }
    iAaccIntro with "Halpha".
    { iIntros "[Htrace_t _]". iModIntro.
      iFrame "Hfrag HΦ".
      iNext. iExists nodes_t, del_pref_t, head_val_t, tail_val_t, dummy_loc_t, ts_t,
        {| absq_O := O_t; absq_lt := lt_t; absq_l := ℓ_t;
           absq_rv := rv_t; absq_cp := cp_t |}, ls_t,
        op_map_t, node_map_t, dq_map_t, no_O_set_t, witness_map_t.
      iFrame. iPureIntro.
      split; [exact Hsteps_t|].
      split; [exact Hts_eq_t|].
      split; [exact Hsim_t|].
      split; [exact Hdummy_t|].
      split; [exact Hnvi_t|].
      split; [exact Hdqi_t|].
      split; [exact Hno_O_inv_t|].
      split; [exact Hcoi_t|]. exact Hwit_t. }
    iIntros "Htrace_t".
    iMod (own_update_2 _ _ _ (● to_opmap (delete τ op_map_t))
            with "Hauth_op_t Hfrag") as "Hauth_op_t".
    { apply auth_update_dealloc.
      rewrite /to_opmap fmap_delete.
      apply: delete_singleton_local_update. }
    iMod (own_update _ _
            (●ML (ls_t ++ [(τ, ARetDeq v_dq)] : list (leibnizO (positive * absq_action))))
            with "Hauth_ls_t") as "Hauth_ls_t".
    { apply mono_list_update. by apply prefix_app_r. }
    iModIntro.
    iSplitL "Hhead_t Htail_t Hchain_t Htrace_t Hauth_op_t Hauth_nm_t Hfrag_nm_t Hauth_dq_t Hfrag_dq_t Hauth_del_t Hauth_calls_t Hauth_no_O_t Hauth_ls_t Hauth_w_t Hfrag_w_t".
    { iNext.
      iExists nodes_t, del_pref_t, head_val_t, tail_val_t, dummy_loc_t,
        (ts_t ++ [(τ, Ret v_dq)]),
        {| absq_O := O_t; absq_lt := lt_t; absq_l := ℓ_t; absq_rv := rv_t;
           absq_cp := <[τ := R3]> cp_t |},
        (ls_t ++ [(τ, ARetDeq v_dq)]), (delete τ op_map_t),
        node_map_t, dq_map_t, no_O_set_t, witness_map_t.
      iFrame "Hhead_t Htail_t Hchain_t Htrace_t Hauth_op_t Hauth_nm_t Hfrag_nm_t
              Hauth_dq_t Hfrag_dq_t Hauth_del_t Hauth_ls_t Hauth_no_O_t Hauth_w_t Hfrag_w_t".
      rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R2)).
      iFrame "Hauth_calls_t".
      iPureIntro. split_and!.
      - eapply rtcL_r; [exact Hsteps_t|].
        by apply absq_step_ret_deq.
      - rewrite Hts_eq_t /trace_of_absq_labels map_app /= filter_app.
        rewrite filter_cons_True; [done|]. by compute.
      - (* bq_sim *)
        destruct Hsim_t as (Hlen_t & Hdel_t & _ & Hdomsub_t & Hnm_dom_t & Henq_clause_t
                            & _ & Hinj_t & Hcorr_t & Hlt_pos_t & _Htbd_t & Hcomp_link_t
                            & Htail_in_t & Hhead_in_t & Hnm_chain_t & Hsome_at_pos_t).
        split_and!; simpl.
        + exact Hlen_t.
        + exact Hdel_t.
        + rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R2)) fmap_app /= list_to_set_app_L.
          clear -Hcp_in_ts_t. set_solver.
        + rewrite dom_insert_L dom_delete_L.
          assert (τ ∈ dom cp_t) as Hτ_in_cp_t
            by (apply elem_of_dom; by eexists).
          clear -Hdomsub_t Hτ_in_cp_t. set_solver.
        + exact Hnm_dom_t.
        + (* clause 6: per-enqueue *)
          intros τ' d' node' linked' Hop'.
          assert (τ' ≠ τ) as Hne.
          { intros ->. rewrite lookup_delete_eq in Hop'. discriminate. }
          rewrite lookup_delete_ne in Hop'; last done.
          destruct (Henq_clause_t _ _ _ _ Hop') as (Hcp & Hℓ & Hpre & Hpost).
          split_and!.
          { rewrite lookup_insert_ne; [exact Hcp|done]. }
          { exact Hℓ. }
          { exact Hpre. }
          { exact Hpost. }
        + (* clause 7: per-dequeue *)
          intros τ' obs' rng' node' linked' Hop'.
          assert (τ' ≠ τ) as Hne.
          { intros ->. rewrite lookup_delete_eq in Hop'. discriminate. }
          rewrite lookup_delete_ne in Hop'; last done.
          destruct (Hdeq_clause_t _ _ _ _ _ Hop') as (Hnone & Hpre & Hpost).
          split_and!.
          { exact Hnone. }
          { intros Hb. rewrite lookup_insert_ne; [|done]. by apply Hpre. }
          { intros Hb. destruct (Hpost Hb) as (Hcp_R2' & v_rv' & Hrv_v').
            rewrite lookup_insert_ne; [|done]. split; first done.
            by exists v_rv'. }
        + exact Hinj_t.
        + exact Hcorr_t.
        + exact Hlt_pos_t.
        + done.
        + exact Hcomp_link_t.
        + exact Htail_in_t.
        + exact Hhead_in_t.
        + exact Hnm_chain_t.
        + exact Hsome_at_pos_t.
      - exact Hdummy_t.
      - exact Hnvi_t.
      - exact Hdqi_t.
      - apply Hno_O_inv_t.
      - apply Hno_O_inv_t.
      - (* chain_op_inv *)
        intros i loc τ' v Hpos Hlk info Hop_lk.
        pose proof (Hcoi_t _ _ _ _ Hpos Hlk) as Hlinked.
        destruct (decide (τ' = τ)) as [->|Hne].
        + rewrite lookup_delete_eq in Hop_lk. discriminate.
        + rewrite lookup_delete_ne in Hop_lk; [|done].
          exact (Hlinked _ Hop_lk).
      - (* chain_witness_inv *)
        destruct Hwit_t as [Hwit_dom Hwit_per].
        split.
        { simpl. clear -Hwit_dom. set_solver. }
        intros τ' tail_loc' snap Hwit_lookup.
        exact (Hwit_per τ' tail_loc' snap Hwit_lookup). }
    wp_pures.
    iApply ("HΦ" $! v_dq with "[//]").
  Qed.

End bq_skeleton_deq_trace.
