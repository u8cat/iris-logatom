(* refine_enq_trace.v: helper lemma for the trace_emit RET-ENQ step
  of [op_spec_enq_cont] in [refine_enq_cont.v].

  The body is the bulk of phase 8: open the inv at the [trace_emit],
  case-split on whether [τ ∈ absq_O] to fire RET-ENQ1 or RET-ENQ2,
  perform the [γ_op] delete and [γ_ls] append, re-establish [bq_sim]
  for the post-RET state, and conclude with [HΦ] applied to [#()].

  Extracted to its own file so that the trace_emit work compiles
  once and both the phase-7-success and phase-7-failure branches of
  the main lemma can dispatch via [iApply], keeping each per-file
  build under the project's 1-minute target. *)

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

Section bq_skeleton_enq_trace.
  Context `{!traceG Σ, !bqG Σ}.

  Local Notation valid_value := bq_valid_value.
  Local Notation Nbq := Nbq.
  Local Notation bq_inv_body := bq_inv_body.

  Lemma op_spec_enq_trace_emit
    `{!heapGS Σ} (γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w : gname)
    (l head tail nd : loc)
    (τ : positive) (d : val) (Φ : val → iProp Σ) :
    inv Nbq (bq_inv_body γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w head tail l) -∗
    trace_inv l (I_lang_bq) -∗
    own γ (◯ {[τ := Excl {| op_info_kind := OpEnq d;
                            op_info_node := Some nd;
                            op_info_linked := true |}]}) -∗
    (∀ v : val, True -∗ Φ v) -∗
    WP (trace_emit #l #(Z.pos τ) (InjRV #()) ;; #()) {{ v, Φ v }}.
  Proof.
    iIntros "#Hinv #Htrace_inv Hfrag HΦ".
    wp_pures.
    wp_bind (trace_emit _ _ _)%E.
    awp_apply (trace_emit_spec l τ (Ret #()) (InjRV #()) I_lang_bq
                 with "Htrace_inv"); first done.
    iInv Nbq as (nodes_8 del_pref_8 head_val_8 tail_val_8 dummy_loc_8
                 ts_8 s_8 ls_8 op_map_8 node_map_8 dq_map_8 no_O_set_8 witness_map_8)
      "(>Hhead8 & >Htail8 & >Hchain8 & >Htrace8 & >Hauth_op8
        & >Hauth_nm8 & Hfrag_nm8 & >Hauth_dq8 & Hfrag_dq8 & >Hauth_del8
        & >Hauth_calls8 & >Hauth_no_O8 & >Hauth_ls8 & >Hauth_w8 & Hfrag_w8 & >%Hsteps8
        & >%Hts_eq8 & >%Hsim8 & >%Hdummy8 & >%Hnvi8 & >%Hdqi8
        & >%Hno_O_inv8 & >%Hcoi8 & >%Hwit8)".
    iDestruct (own_valid_2 with "Hauth_op8 Hfrag") as %Hτ_both8.
    apply auth_both_valid_discrete in Hτ_both8 as [Hτ_incl8 Hτ_valid8].
    apply singleton_included_exclusive_l in Hτ_incl8; [|apply _|done].
    rewrite lookup_fmap in Hτ_incl8.
    apply leibniz_equiv in Hτ_incl8.
    apply fmap_Some_1 in Hτ_incl8 as (info_τ8 & Hτ_in_op8 & Hinfo_τ8).
    destruct info_τ8; injection Hinfo_τ8 as <- <- <-.
    pose proof Hsim8 as (Hlen8 & Hdel8 & Hcp_in_ts8 & Hdomsub8 & Hnm_dom8
                         & Henq_clause8 & Hdeq_clause8 & Hinj8 & Hcorr8
                         & Hlt_pos8 & _Htbd8 & Hcomp_link8 & Htail_in8
                         & Hhead_in8 & Hnm_chain8 & Hsome_at_pos8).
    destruct (Henq_clause8 _ _ _ _ Hτ_in_op8)
      as (Hcp_τ_A1_8 & Hℓ_τ_PEND_8 & _ & Hpost_8).
    destruct (Hpost_8 eq_refl)
      as (l_τ_8 & i_τ_8 & Hnode_eq_8 & Hi_τ_pos_8 & Hi_τ_lookup_8
           & Hnm_τ_8 & _).
    injection Hnode_eq_8 as ?. subst l_τ_8.
    destruct s_8 as [O_8 lt_8 ℓ_8 rv_8 cp_8].
    simpl in Hcp_τ_A1_8, Hℓ_τ_PEND_8.
    iAssert (trace_is l ts_8 ∗
             ⌜I_lang_bq (ts_8 ++ [(τ, Ret #())])⌝)%I
      with "[$Htrace8]" as "Halpha".
    { iPureIntro.
      destruct (decide (τ ∈ O_8)) as [Hτ_in_O | Hτ_not_in_O].
      - eexists _, (ls_8 ++ [(τ, ARetEnq)]).
        split.
        + eapply rtcL_r; [exact Hsteps8|].
          apply absq_step_ret_enq1 with (d := d); done.
        + rewrite Hts_eq8 /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute.
      - eexists _, (ls_8 ++ [(τ, ARetEnq)]).
        split.
        + eapply rtcL_r; [exact Hsteps8|].
          apply absq_step_ret_enq2; done.
        + rewrite Hts_eq8 /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute. }
    iAaccIntro with "Halpha".
    { iIntros "[Htrace8 _]".
      iModIntro. rewrite bi.sep_assoc. iSplitR "HΦ"; last eauto.
      iSplitR "Hfrag"; last by eauto.
      iNext. iExists nodes_8, del_pref_8, head_val_8, tail_val_8,
        dummy_loc_8, ts_8,
        {| absq_O := O_8; absq_lt := lt_8; absq_l := ℓ_8;
           absq_rv := rv_8; absq_cp := cp_8 |}, ls_8,
        op_map_8, node_map_8, dq_map_8, no_O_set_8, witness_map_8.
      iFrame. iPureIntro.
      split; [exact Hsteps8|].
      split; [exact Hts_eq8|].
      split; [exact Hsim8|].
      split; [exact Hdummy8|].
      split; [exact Hnvi8|].
      split; [exact Hdqi8|].
      split; [exact Hno_O_inv8|].
      split; [exact Hcoi8|]. exact Hwit8. }
    iIntros "Htrace8".
    iMod (own_update_2 _ _ _ (● to_opmap (delete τ op_map_8))
            with "Hauth_op8 Hfrag") as "Hauth_op8".
    { apply auth_update_dealloc.
      rewrite /to_opmap fmap_delete.
      apply: delete_singleton_local_update. }
    iMod (own_update _ _
            (●ML (ls_8 ++ [(τ, ARetEnq)]
                    : list (leibnizO (positive * absq_action))))
            with "Hauth_ls8") as "Hauth_ls8".
    { apply mono_list_update. by apply prefix_app_r. }
    iModIntro.
    destruct (decide (τ ∈ O_8)) as [Hτ_in_O | Hτ_not_in_O].
    - (* RET-ENQ1 close *)
      iSplitL "Hhead8 Htail8 Hchain8 Htrace8 Hauth_op8 Hauth_nm8
               Hfrag_nm8 Hauth_dq8 Hfrag_dq8 Hauth_del8 Hauth_calls8
               Hauth_no_O8 Hauth_ls8 Hauth_w8 Hfrag_w8".
      { iNext.
        iExists nodes_8, del_pref_8, head_val_8, tail_val_8, dummy_loc_8,
          (ts_8 ++ [(τ, Ret #())]),
          {| absq_O := O_8; absq_lt := lt_8;
             absq_l := <[τ := (d, COMP)]> ℓ_8;
             absq_rv := rv_8; absq_cp := <[τ := A2]> cp_8 |},
          (ls_8 ++ [(τ, ARetEnq)]), (delete τ op_map_8),
          node_map_8, dq_map_8, no_O_set_8, witness_map_8.
        rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_A1_8)).
        iFrame.
        iPureIntro. split_and!.
        - eapply rtcL_r; [exact Hsteps8|].
          apply absq_step_ret_enq1 with (d := d); done.
        - rewrite Hts_eq8 /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute.
        - (* bq_sim — 16 clauses *)
          split_and!; simpl.
          + exact Hlen8.
          + exact Hdel8.
          + (* clause 3: dom cp ⊆ ts.*1 *)
            rewrite ?dom_insert_L fmap_app /= list_to_set_app_L.
            apply union_least.
            * etrans; [|apply union_subseteq_r].
              intros x ->%elem_of_singleton.
              rewrite /=. apply elem_of_union_l, elem_of_singleton.
              reflexivity.
            * etrans; [exact Hcp_in_ts8|]. apply union_subseteq_l.
          + (* clause 4: dom op_map ⊆ dom cp *)
            rewrite dom_delete_L ?dom_insert_L.
            intros x [Hx _]%elem_of_difference.
            apply elem_of_union_r, Hdomsub8, Hx.
          + exact Hnm_dom8.
          + (* clause 6: per-enqueue *)
            intros τ' d' node' linked' Hop'.
            assert (τ' ≠ τ) as Hne.
            { intros ->. by rewrite lookup_delete_eq in Hop'. }
            rewrite lookup_delete_ne in Hop'; [|done].
            destruct (Henq_clause8 _ _ _ _ Hop')
              as (Hcp' & Hℓ' & Hpre' & Hpost').
            split_and!.
            * rewrite lookup_insert_ne; [exact Hcp' | done].
            * rewrite lookup_insert_ne; [exact Hℓ' | done].
            * exact Hpre'.
            * intros Hlinked.
              destruct (Hpost' Hlinked)
                as (l_old & i_old & Hnode_eq' & Hi_pos' & Hi_lookup'
                     & Hnm_old & Hin_iff').
              exists l_old, i_old. split_and!; auto.
          + (* clause 7: per-dequeue *)
            intros τ' obs' rng' node' linked' Hop'.
            assert (τ' ≠ τ) as Hne.
            { intros ->. by rewrite lookup_delete_eq in Hop'. }
            rewrite lookup_delete_ne in Hop'; [|done].
            destruct (Hdeq_clause8 _ _ _ _ _ Hop')
              as (Hnone & Hpre' & Hpost').
            split_and!.
            * exact Hnone.
            * intros Hb. rewrite lookup_insert_ne; [|done].
              by apply Hpre'.
            * intros Hb. destruct (Hpost' Hb) as (Hcp' & v & Hrv).
              split.
              ** rewrite lookup_insert_ne; [exact Hcp' | done].
              ** by exists v.
          + exact Hinj8.
          + (* clause 9: chain ↔ absq_l *)
            intros i lk τ' v Hi_pos Hi_lookup.
            destruct (Hcorr8 _ _ _ _ Hi_pos Hi_lookup)
              as (Hnm_l & (f & Hℓ_τ') & Hin_iff).
            split; [exact Hnm_l|].
            split; [|exact Hin_iff].
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite Hℓ_τ_PEND_8 in Hℓ_τ'.
              injection Hℓ_τ' as <- _.
              exists COMP. by rewrite lookup_insert_eq.
            * exists f. rewrite lookup_insert_ne; [exact Hℓ_τ' | done].
          + exact Hlt_pos8.
          + done.
          + (* clause 12: COMP enqueues are linked *)
            intros τ' d' Hℓ_τ'.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hℓ_τ'.
              injection Hℓ_τ' as <-.
              exists i_τ_8, nd. split; [exact Hi_τ_pos_8|exact Hi_τ_lookup_8].
            * rewrite lookup_insert_ne in Hℓ_τ'; [|done].
              apply (Hcomp_link8 _ _ Hℓ_τ').
          + exact Htail_in8.
          + exact Hhead_in8.
          + exact Hnm_chain8.
          + exact Hsome_at_pos8.
        - exact Hdummy8.
        - (* node_val_inv *)
          destruct Hnvi8 as [Hnvi_fwd Hnvi_inj].
          split.
          + intros lk τ' d' Hlk.
            destruct (Hnvi_fwd _ _ _ Hlk) as (f' & Hℓ_τ').
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite Hℓ_τ_PEND_8 in Hℓ_τ'.
              injection Hℓ_τ' as <- _.
              exists COMP. by rewrite lookup_insert_eq.
            * exists f'. rewrite lookup_insert_ne; [exact Hℓ_τ' | done].
          + exact Hnvi_inj.
        - exact Hdqi8.
        - destruct Hno_O_inv8 as [HnoO_sub _]. exact HnoO_sub.
        - destruct Hno_O_inv8 as [_ HnoO_disj]. exact HnoO_disj.
        - (* chain_op_inv *)
          intros i lk τ' v Hpos Hlk info Hop_lk.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_delete_eq in Hop_lk. discriminate.
          + rewrite lookup_delete_ne in Hop_lk; [|done].
            exact (Hcoi8 _ _ _ _ Hpos Hlk _ Hop_lk).
        - (* chain_witness_inv: cp unchanged at RET-ENQ1 (only flag transitions),
             chain unchanged, witness_map unchanged.  lt unchanged. *)
          destruct Hwit8 as [Hwit_dom Hwit_per].
          split.
          { simpl. clear -Hwit_dom. set_solver. }
          intros τ' snap Hwit_lookup.
          exact (Hwit_per τ' snap Hwit_lookup). }
      wp_pures. by iApply ("HΦ" $! #() with "[//]").
    - (* RET-ENQ2 close *)
      iSplitL "Hhead8 Htail8 Hchain8 Htrace8 Hauth_op8 Hauth_nm8
               Hfrag_nm8 Hauth_dq8 Hfrag_dq8 Hauth_del8 Hauth_calls8
               Hauth_no_O8 Hauth_ls8 Hauth_w8 Hfrag_w8".
      { iNext.
        iExists nodes_8, del_pref_8, head_val_8, tail_val_8, dummy_loc_8,
          (ts_8 ++ [(τ, Ret #())]),
          {| absq_O := O_8; absq_lt := lt_8;
             absq_l := ℓ_8;
             absq_rv := rv_8; absq_cp := <[τ := A2]> cp_8 |},
          (ls_8 ++ [(τ, ARetEnq)]), (delete τ op_map_8),
          node_map_8, dq_map_8, no_O_set_8, witness_map_8.
        rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_A1_8)).
        iFrame.
        iPureIntro. split_and!.
        - eapply rtcL_r; [exact Hsteps8|].
          apply absq_step_ret_enq2; done.
        - rewrite Hts_eq8 /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute.
        - split_and!; simpl.
          + exact Hlen8.
          + exact Hdel8.
          + rewrite ?dom_insert_L fmap_app /= list_to_set_app_L.
            apply union_least.
            * etrans; [|apply union_subseteq_r].
              intros x ->%elem_of_singleton.
              rewrite /=. apply elem_of_union_l, elem_of_singleton.
              reflexivity.
            * etrans; [exact Hcp_in_ts8|]. apply union_subseteq_l.
          + rewrite dom_delete_L ?dom_insert_L.
            intros x [Hx _]%elem_of_difference.
            apply elem_of_union_r, Hdomsub8, Hx.
          + exact Hnm_dom8.
          + intros τ' d' node' linked' Hop'.
            assert (τ' ≠ τ) as Hne.
            { intros ->. by rewrite lookup_delete_eq in Hop'. }
            rewrite lookup_delete_ne in Hop'; [|done].
            destruct (Henq_clause8 _ _ _ _ Hop')
              as (Hcp' & Hℓ' & Hpre' & Hpost').
            split_and!.
            * rewrite lookup_insert_ne; [exact Hcp' | done].
            * exact Hℓ'.
            * exact Hpre'.
            * exact Hpost'.
          + intros τ' obs' rng' node' linked' Hop'.
            assert (τ' ≠ τ) as Hne.
            { intros ->. by rewrite lookup_delete_eq in Hop'. }
            rewrite lookup_delete_ne in Hop'; [|done].
            destruct (Hdeq_clause8 _ _ _ _ _ Hop')
              as (Hnone & Hpre' & Hpost').
            split_and!.
            * exact Hnone.
            * intros Hb. rewrite lookup_insert_ne; [|done].
              by apply Hpre'.
            * intros Hb. destruct (Hpost' Hb) as (Hcp' & v & Hrv).
              split.
              ** rewrite lookup_insert_ne; [exact Hcp' | done].
              ** by exists v.
          + exact Hinj8.
          + exact Hcorr8.
          + exact Hlt_pos8.
          + done.
          + exact Hcomp_link8.
          + exact Htail_in8.
          + exact Hhead_in8.
          + exact Hnm_chain8.
          + exact Hsome_at_pos8.
        - exact Hdummy8.
        - exact Hnvi8.
        - exact Hdqi8.
        - destruct Hno_O_inv8 as [HnoO_sub _]. exact HnoO_sub.
        - destruct Hno_O_inv8 as [_ HnoO_disj]. exact HnoO_disj.
        - (* chain_op_inv: same as RET-ENQ1 close *)
          intros i lk τ' v Hpos Hlk info Hop_lk.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_delete_eq in Hop_lk. discriminate.
          + rewrite lookup_delete_ne in Hop_lk; [|done].
            exact (Hcoi8 _ _ _ _ Hpos Hlk _ Hop_lk).
        - (* chain_witness_inv: same as RET-ENQ1 close *)
          destruct Hwit8 as [Hwit_dom Hwit_per].
          split.
          { simpl. clear -Hwit_dom. set_solver. }
          intros τ' snap Hwit_lookup.
          exact (Hwit_per τ' snap Hwit_lookup). }
      wp_pures. by iApply ("HΦ" $! #() with "[//]").
  Qed.

End bq_skeleton_enq_trace.
