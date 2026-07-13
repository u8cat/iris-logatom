(* refine_op_spec.v: proof of [op_spec] for the Baskets Queue —
  the [call_ret_wrapper]-level Hoare triple that
  [bdgjst_free] consumes.

  ** Structure.
  The [op] dispatcher uses [SOMEV d] for an enqueue request and
  [NONEV] for a dequeue request.  This wrapper:
    1. opens the [Nbq] invariant and runs [trace_fresh] to allocate a
       fresh trace identifier [τ], simultaneously committing either
       an [absq_step_call_enq] or an [absq_step_call_deq] step in the
       AbsQ witness;
    2. allocates a fresh [op_map] entry for [τ] and gives the calling
       thread an [Excl]-typed fragment;
    3. closes the invariant and dispatches to
       [op_spec_enq_cont] / [op_spec_deq_cont]. *)

From iris.algebra Require Import auth excl gmap gset agree mono_list.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.baskets_queue Require Import impl refine.defs
                                                refine.enq_cont refine.deq_cont.

Section bq_skeleton_op_spec.
  Context `{!traceG Σ, !bqG Σ}.

  Local Notation valid_value := bq_valid_value.
  Local Notation Nbq := Nbq.
  Local Notation bq_inv_body := bq_inv_body.
  Local Notation is_bq := is_bq.
  Local Notation bq_repr := bq_repr.

  Lemma op_spec :
    ∀ `(!heapGS Σ), call_ret_wrapper_spec_type
      bq_repr NotStuck (queue_model MayEmpty valid_value).(valid_request) op.
  Proof.
    iIntros (Hheap γ l obj req Hvalid Φ) "[#Htrace_inv #Hq] HΦ".
    iDestruct "Hq" as (head tail γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w) "[%Heq #Hinv]". subst obj.
    rewrite /call_ret_wrapper. wp_pures.
    wp_bind (trace_fresh _ _).
    awp_apply (trace_fresh_spec _ (Call req) (InjLV req) I_lang_bq
                with "Htrace_inv").
    { done. }
    iInv Nbq as (nodes del_pref head_val tail_val dummy_loc ts s ls op_map node_map dq_map no_O_set witness_map)
      "(>Hhead & >Htail & Hchain & >Htrace & >Hauth_op & >Hauth_nm & Hfrag_nm
        & >Hauth_dq & Hfrag_dq & >Hauth_del & >Hauth_calls & >Hauth_no_O & >Hauth_ls & >Hauth_w & Hfrag_w
        & >%Hsteps & >%Hts_eq & >%Hsim & >%Hdummy & >%Hnvi & >%Hdqi & >%Hno_O & >%Hcoi & >%Hwit)".
    destruct s as [O_s lt_s l_s rv_s cp_s].
    iAssert (trace_is l ts ∗
      ⌜∀ τ, τ ∉ ts.*1 →
            I_lang_bq (ts ++ [(τ, Call req)])⌝)%I
      with "[$Htrace]" as "Halpha".
    { iPureIntro. intros τ Hτ_fresh.
      assert (τ ∉ dom cp_s) as Hτ_notin_cp.
      { destruct Hsim as (_ & _ & Hcp_in_ts & _). simpl in *. set_solver. }
      destruct Hvalid as [(d & Hd_valid & ->) | ->].
      - eexists _, (ls ++ [(τ, ACallEnq d)]).
        split.
        + eapply lts_steps_app; [exact Hsteps|].
          eapply lts_steps_cons; [|apply lts_steps_nil].
          apply absq_step_call_enq; done.
        + rewrite Hts_eq /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute.
      - eexists _, (ls ++ [(τ, ACallDeq)]).
        split.
        + eapply lts_steps_app; [exact Hsteps|].
          eapply lts_steps_cons; [|apply lts_steps_nil].
          apply absq_step_call_deq; done.
        + rewrite Hts_eq /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute. }
    iAaccIntro with "Halpha".
    { iIntros "[Htrace _]". iModIntro.
      iSplitL "Hhead Htail Hchain Htrace Hauth_op Hauth_nm Hfrag_nm Hauth_dq Hfrag_dq Hauth_del Hauth_calls Hauth_no_O Hauth_ls Hauth_w Hfrag_w"; last done.
      iNext. iExists nodes, del_pref, head_val, tail_val, dummy_loc, ts, _, ls, op_map, node_map, dq_map, no_O_set, witness_map.
      by iFrame. }
    iIntros (τ) "[Htrace %Hτ_fresh]".
    assert (τ ∉ dom cp_s) as Hτ_notin_cp.
    { destruct Hsim as (_ & _ & Hcp_in_ts & _). simpl in *. set_solver. }
    assert (op_map !! τ = None) as Hτ_notin_opmap.
    { destruct Hsim as (_ & _ & _ & Hdomsub & _). simpl in *.
      apply not_elem_of_dom. set_solver. }
    assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s)) as Hwf_s.
    { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
    destruct Hvalid as [(d & Hd_valid & Hreq_eq) | Hreq_eq]; subst req.
    - (* Enqueue case: CALL-ENQ commit. *)
      set (new_info := {| op_info_kind := OpEnq d;
                          op_info_node := None;
                          op_info_linked := false |}).
      iMod (own_update _ _
              (● to_opmap (<[τ := new_info]> op_map)
               ⋅ ◯ {[τ := Excl new_info]}) with "Hauth_op") as "[Hauth_op Hfrag_op]".
      { apply (auth_update_alloc _ (to_opmap (<[τ := new_info]> op_map))
                 ({[τ := Excl new_info]})).
        rewrite /to_opmap fmap_insert.
        apply: alloc_singleton_local_update; [|done].
        rewrite lookup_fmap Hτ_notin_opmap //. }
      iMod (own_update _ _
              (● ({[τ]} ∪ dom cp_s : gsetUR positive) : authR (gsetUR positive))
              with "Hauth_calls") as "Hauth_calls".
      { apply auth_update_auth with (b' := ({[τ]} ∪ dom cp_s : gsetUR positive)).
        apply gset_local_update. set_solver. }
      iMod (own_update _ _ (●ML (ls ++ [(τ, ACallEnq d)] : list (leibnizO (positive * absq_action))))
              with "Hauth_ls") as "Hauth_ls".
      { apply mono_list_update. by apply prefix_app_r. }
      iModIntro.
      iSplitL "Hhead Htail Hchain Htrace Hauth_op Hauth_nm Hfrag_nm Hauth_dq Hfrag_dq Hauth_del Hauth_calls Hauth_no_O Hauth_ls Hauth_w Hfrag_w".
      { iNext.
        iExists nodes, del_pref, head_val, tail_val, dummy_loc,
          (ts ++ [(τ, Call (encode_request (Push d)))]),
          {| absq_O := O_s ∪ {[τ]};
             absq_lt := lt_s ∪ set_map (λ k', (k', τ)) (absq_COMP O_s l_s);
             absq_l := <[τ := (d, PEND)]> l_s;
             absq_rv := rv_s;
             absq_cp := <[τ := A1]> cp_s |},
          (ls ++ [(τ, ACallEnq d)]),
          (<[τ := new_info]> op_map), node_map, dq_map, no_O_set, witness_map.
        iFrame "Hhead Htail Hchain Htrace Hauth_op Hauth_nm Hfrag_nm Hauth_dq Hfrag_dq Hauth_del Hauth_no_O Hauth_ls Hauth_w Hfrag_w".
        simpl. rewrite dom_insert_L. iFrame "Hauth_calls".
        iPureIntro. split_and!.
        - eapply lts_steps_app; [exact Hsteps|].
          eapply lts_steps_cons; [|apply lts_steps_nil].
          apply absq_step_call_enq; done.
        - rewrite Hts_eq /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute.
        - destruct Hsim as
            (Hlen & Hdel & Hcp_in_ts & Hdomsub & Hnm_dom & Henq_clause
             & Hdeq_clause & Hinj & Hcorr & Hlt_pos & _Htbd & Hcomp_link
             & Htail_in & Hhead_in & Hnm_chain & Hsome_at_pos).
          split_and!; simpl in *.
          + exact Hlen.
          + exact Hdel.
          + rewrite dom_insert_L fmap_app /= list_to_set_app_L.
            clear -Hcp_in_ts. set_solver.
          + rewrite !dom_insert_L. clear -Hdomsub. set_solver.
          + (* Clause 5: node_map domain (chain only; node_map unchanged). *)
            exact Hnm_dom.
          + (* Clause 6: per-enqueue. *)
            intros τ' d' node' linked' Hop'.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hop'.
              injection Hop' as <- <- <-.
              split_and!.
              { by rewrite lookup_insert_eq. }
              { by rewrite lookup_insert_eq. }
              { intros _. clear. set_solver. }
              { intros [=]. }
            * rewrite lookup_insert_ne in Hop'; last done.
              destruct (Henq_clause _ _ _ _ Hop') as (Hcp & Hℓ & Hpre & Hpost).
              split_and!.
              { rewrite lookup_insert_ne //. }
              { rewrite lookup_insert_ne //. }
              { intros Hb. specialize (Hpre Hb). clear -Hpre. set_solver. }
              { intros Hb. destruct (Hpost Hb) as (l_e & i & Hnode_eq & Hi & Hnodes & Hnm & Hin_iff).
                exists l_e, i. split_and!; auto.
                rewrite -Hin_iff. clear -Hne. set_solver. }
          + (* Clause 7: per-dequeue. *)
            intros τ' obs rng node' linked' Hop'.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hop'. discriminate. }
            rewrite lookup_insert_ne in Hop'; last done.
            destruct (Hdeq_clause _ _ _ _ _ Hop') as (Hnone & Hpre & Hpost).
            split_and!.
            { exact Hnone. }
            { intros Hb. rewrite lookup_insert_ne; [|done]. by apply Hpre. }
            { intros Hb. destruct (Hpost Hb) as (Hcp & v & Hrv).
              rewrite lookup_insert_ne; [|done]. split; [exact Hcp|]. by exists v. }
          + (* Clause 8: injectivity (nodes unchanged). *)
            exact Hinj.
          + (* Clause 9: node-list correspondence. *)
            intros i l' τ' v' Hi Hnodes.
            destruct (Hcorr _ _ _ _ Hi Hnodes) as (Hnm & (f' & Hℓ_τ') & Hin_iff).
            assert (τ' ≠ τ) as Hne.
            { intros ->. apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s). apply elem_of_dom. by exists (v', f'). }
            split_and!.
            { exact Hnm. }
            { exists f'. by rewrite lookup_insert_ne. }
            { rewrite -Hin_iff. clear -Hne. set_solver. }
          + (* Clause 10: lt respects list order. *)
            intros k k_e Hlt_new.
            apply elem_of_union in Hlt_new as [Hold | Hnew].
            * destruct (Hlt_pos _ _ Hold) as (p_k & l_k & d_k & Hp_k & Hnodes_k & Hupper).
              by exists p_k, l_k, d_k.
            * apply elem_of_map in Hnew as [y [Heq Hcomp]].
              injection Heq as -> ->.
              apply elem_of_filter in Hcomp as [Hcomp_k Hk_in_O].
              destruct Hcomp_k as (d_k & Hℓ_k).
              destruct (Hcomp_link _ _ Hℓ_k) as (p_k & l_k & Hp_k & Hnodes_k).
              exists p_k, l_k, d_k. split_and!; auto.
              intros p_ke l_ke d_ke Hp_ke Hnodes_ke.
              exfalso. apply Hτ_notin_cp.
              destruct (Hcorr _ _ _ _ Hp_ke Hnodes_ke) as (_ & (f' & Hℓ_τ) & _).
              apply (absq_wf_dom _ _ Hwf_s). apply elem_of_dom. by exists (d_ke, f').
          + done.
          + (* Clause 12: COMP linked. *)
            intros τ' d' Hℓ.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hℓ. discriminate. }
            rewrite lookup_insert_ne in Hℓ; last done.
            exact (Hcomp_link _ _ Hℓ).
          + (* Clause 13: tail in chain (unchanged). *) exact Htail_in.
          + (* Clause 14: head in marked prefix (unchanged). *) exact Hhead_in.
          + (* Clause 15: chain → node_map (unchanged). *) exact Hnm_chain.
          + (* Clause 16: non-dummy positions have Some τ (unchanged). *) exact Hsome_at_pos.
        - (* dummy at chain[0] (unchanged). *) exact Hdummy.
        - (* node_val_inv preserved (op_map and node_map unchanged; absq_l grows). *)
          destruct Hnvi as (Hnvi1 & Hnvi2).
          split.
          + intros l' τ' d' Hnm.
            destruct (Hnvi1 _ _ _ Hnm) as (f' & Hℓ').
            assert (τ' ≠ τ) as Hne.
            { intros ->. apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s). apply elem_of_dom. by exists (d', f'). }
            exists f'. by rewrite lookup_insert_ne.
          + exact Hnvi2.
        - (* dq_inv preserved (rv_s unchanged). *)
          exact Hdqi.
        - (* no_O_set ⊆ dom cp (CALL-ENQ grows dom cp). *)
          destruct Hno_O as [Hsub _]. simpl in Hsub.
          simpl. clear -Hsub. set_solver.
        - (* no_O_set ## absq_O (CALL-ENQ adds τ ∉ dom cp ⊇ no_O_set to absq_O). *)
          simpl. assert (τ ∉ no_O_set) as Hτ_notin_no_O.
          { destruct Hno_O as [Hsub _]. simpl in Hsub. set_solver. }
          destruct Hno_O as [_ Hdisj]. simpl in Hdisj.
          clear -Hτ_notin_no_O Hdisj. set_solver.
        - (* chain_op_inv: τ is fresh, so no chain pos has τ tag.  For
             τ' ≠ τ at chain pos, lookup_insert_ne preserves. *)
          intros i loc τ' v Hpos Hlk info Hop_lk.
          destruct (decide (τ' = τ)) as [->|Hne].
          + exfalso.
            destruct Hsim as (_ & _ & _ & _ & _ & _ & _ & _ & Hcorr_s & _).
            destruct (Hcorr_s _ _ _ _ Hpos Hlk) as (_ & (f & Hℓ_τ) & _).
            apply Hτ_notin_cp.
            apply (absq_wf_dom _ _ Hwf_s). apply elem_of_dom. by exists (v, f).
          + rewrite lookup_insert_ne in Hop_lk; [|done].
            exact (Hcoi _ _ _ _ Hpos Hlk _ Hop_lk).
        - (* chain_witness_inv: CALL-ENQ for fresh τ.  τ ∉ dom cp_old, so
             τ ∉ dom witness_map (by old inv).  New edges (k, τ) added in
             lt don't affect any τ' ∈ dom witness_map (since τ' ≠ τ). *)
          destruct Hwit as [Hwit_dom Hwit_per].
          split.
          { simpl. intros [τ_w tail_loc_w] Hk.
            specialize (Hwit_dom (τ_w, tail_loc_w) Hk).
            simpl in *. rewrite dom_insert_L. set_solver. }
          intros τ' tail_loc snap Hwit_lookup.
          assert (τ' ≠ τ) as Hne.
          { intros ->.  apply Hτ_notin_cp.
            specialize (Hwit_dom (τ, tail_loc)).
            simpl in Hwit_dom. apply Hwit_dom.
            apply elem_of_dom. by eexists. }
          destruct (Hwit_per τ' tail_loc snap Hwit_lookup)
            as (Hsub & Hlen & Hsucc & Hsnap_end & Hlt_in).
          split_and!; [exact Hsub|exact Hlen|exact Hsucc|exact Hsnap_end|].
          intros k Hkin.
          apply Hlt_in.
          (* Hkin: (k, τ') ∈ new lt = old lt ∪ {(k_c, τ) : k_c ∈ COMP}.
             Since τ' ≠ τ, (k, τ') ∈ new lt iff (k, τ') ∈ old lt. *)
          simpl in Hkin. apply elem_of_union in Hkin as [Hold|Hnew]; first done.
          exfalso. rewrite elem_of_map in Hnew. destruct Hnew as [k_c [Heq _]].
          injection Heq as _ ?. done. }
      iApply (op_spec_enq_cont γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w l head tail τ d Φ
                Hd_valid Hd_valid with "Hinv Htrace_inv Hfrag_op HΦ").
    - (* Dequeue case: CALL-DEQ commit. *)
      set (rng_init := length nodes).
      set (new_info := {| op_info_kind := OpDeq [] rng_init;
                          op_info_node := None;
                          op_info_linked := false |}).
      iMod (own_update _ _
              (● to_opmap (<[τ := new_info]> op_map)
               ⋅ ◯ {[τ := Excl new_info]}) with "Hauth_op") as "[Hauth_op Hfrag_op]".
      { apply (auth_update_alloc _ (to_opmap (<[τ := new_info]> op_map))
                 ({[τ := Excl new_info]})).
        rewrite /to_opmap fmap_insert.
        apply: alloc_singleton_local_update; [|done].
        rewrite lookup_fmap Hτ_notin_opmap //. }
      iMod (own_update _ _
              (● ({[τ]} ∪ dom cp_s : gsetUR positive) : authR (gsetUR positive))
              with "Hauth_calls") as "Hauth_calls".
      { apply auth_update_auth with (b' := ({[τ]} ∪ dom cp_s : gsetUR positive)).
        apply gset_local_update. set_solver. }
      iMod (own_update _ _ (●ML (ls ++ [(τ, ACallDeq)] : list (leibnizO (positive * absq_action))))
              with "Hauth_ls") as "Hauth_ls".
      { apply mono_list_update. by apply prefix_app_r. }
      iModIntro.
      iSplitL "Hhead Htail Hchain Htrace Hauth_op Hauth_nm Hfrag_nm Hauth_dq Hfrag_dq Hauth_del Hauth_calls Hauth_no_O Hauth_ls Hauth_w Hfrag_w".
      { iNext.
        iExists nodes, del_pref, head_val, tail_val, dummy_loc,
          (ts ++ [(τ, Call (encode_request Pop))]),
          {| absq_O := O_s; absq_lt := lt_s; absq_l := l_s; absq_rv := rv_s;
             absq_cp := <[τ := R1]> cp_s |},
          (ls ++ [(τ, ACallDeq)]),
          (<[τ := new_info]> op_map), node_map, dq_map, no_O_set, witness_map.
        iFrame "Hhead Htail Hchain Htrace Hauth_op Hauth_nm Hfrag_nm Hauth_dq Hfrag_dq Hauth_del Hauth_no_O Hauth_ls Hauth_w Hfrag_w".
        simpl. rewrite dom_insert_L. iFrame "Hauth_calls".
        iPureIntro. split_and!.
        - eapply lts_steps_app; [exact Hsteps|].
          eapply lts_steps_cons; [|apply lts_steps_nil].
          apply absq_step_call_deq; done.
        - rewrite Hts_eq /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute.
        - destruct Hsim as
            (Hlen & Hdel & Hcp_in_ts & Hdomsub & Hnm_dom & Henq_clause
             & Hdeq_clause & Hinj & Hcorr & Hlt_pos & _Htbd & Hcomp_link
             & Htail_in & Hhead_in & Hnm_chain & Hsome_at_pos).
          split_and!; simpl in *.
          + exact Hlen.
          + exact Hdel.
          + rewrite dom_insert_L fmap_app /= list_to_set_app_L.
            clear -Hcp_in_ts. set_solver.
          + rewrite !dom_insert_L. clear -Hdomsub. set_solver.
          + (* Clause 5: node_map domain (chain only; node_map unchanged). *)
            exact Hnm_dom.
          + (* Clause 6: per-enqueue (CALL-DEQ: only cp grows by τ ↦ R1). *)
            intros τ' d' node' linked' Hop'.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hop'. discriminate. }
            rewrite lookup_insert_ne in Hop'; last done.
            destruct (Henq_clause _ _ _ _ Hop') as (Hcp & Hℓ & Hpre & Hpost).
            split_and!.
            { rewrite lookup_insert_ne; [exact Hcp|done]. }
            { exact Hℓ. }
            { exact Hpre. }
            { exact Hpost. }
          + (* Clause 7: per-dequeue. *)
            intros τ' obs rng node' linked' Hop'.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hop'.
              injection Hop' as <- <- <- <-.
              split_and!.
              { reflexivity. }
              { intros _. by rewrite lookup_insert_eq. }
              { intros [=]. }
            * rewrite lookup_insert_ne in Hop'; last done.
              destruct (Hdeq_clause _ _ _ _ _ Hop') as (Hnone & Hpre & Hpost).
              split_and!.
              { exact Hnone. }
              { intros Hb. rewrite lookup_insert_ne; [|done]. by apply Hpre. }
              { intros Hb. destruct (Hpost Hb) as (Hcp & v & Hrv).
                rewrite lookup_insert_ne; [|done]. split; [exact Hcp|]. by exists v. }
          + exact Hinj.
          + (* Clause 9: node-list correspondence (only cp changes; nothing else). *)
            exact Hcorr.
          + exact Hlt_pos.
          + done.
          + exact Hcomp_link.
          + exact Htail_in.
          + exact Hhead_in.
          + exact Hnm_chain.
          + exact Hsome_at_pos.
        - exact Hdummy.
        - exact Hnvi.
        - exact Hdqi.
        - (* no_O_set ⊆ dom cp (CALL-DEQ grows dom cp). *)
          destruct Hno_O as [Hsub _]. simpl in Hsub.
          simpl. clear -Hsub. set_solver.
        - (* no_O_set ## absq_O (CALL-DEQ doesn't change absq_O). *)
          destruct Hno_O as [_ Hdisj]. simpl in Hdisj.
          simpl. exact Hdisj.
        - (* chain_op_inv: τ is fresh, so no chain pos has τ tag.  For
             τ' ≠ τ at chain pos, lookup_insert_ne preserves. *)
          intros i loc τ' v Hpos Hlk info Hop_lk.
          destruct (decide (τ' = τ)) as [->|Hne].
          + exfalso.
            destruct Hsim as (_ & _ & _ & _ & _ & _ & _ & _ & Hcorr_s & _).
            destruct (Hcorr_s _ _ _ _ Hpos Hlk) as (_ & (f & Hℓ_τ) & _).
            apply Hτ_notin_cp.
            apply (absq_wf_dom _ _ Hwf_s). apply elem_of_dom. by exists (v, f).
          + rewrite lookup_insert_ne in Hop_lk; [|done].
            exact (Hcoi _ _ _ _ Hpos Hlk _ Hop_lk).
        - (* chain_witness_inv: CALL-DEQ doesn't change lt, chain unchanged.
             cp gains τ; existing witnesses' invariants preserved (τ' ≠ τ
             since τ ∉ dom cp_old). *)
          destruct Hwit as [Hwit_dom Hwit_per].
          split.
          { simpl. intros [τ_w tail_loc_w] Hk.
            specialize (Hwit_dom (τ_w, tail_loc_w) Hk).
            simpl in *. rewrite dom_insert_L. set_solver. }
          intros τ' tail_loc snap Hwit_lookup.
          exact (Hwit_per τ' tail_loc snap Hwit_lookup). }
      iApply (op_spec_deq_cont γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w l head tail τ rng_init Φ
                with "Hinv Htrace_inv Hfrag_op HΦ").
  Qed.

End bq_skeleton_op_spec.
