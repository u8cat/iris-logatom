(* The dequeue: the scans of the array, the CAS that commits a match, and the return. *)
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Import bag queue.
From iris_logatom.pure_logic Require Import encodable linear.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gset agree mono_list mono_nat.
From iris.base_logic Require Import invariants ghost_map.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy lang notation tactics unwrap.
From iris_logatom.heap_lang Require Import mgc fork_free.

From case_studies.hw_queue Require Import impl.
From case_studies.hw_queue.aspect Require Import defs.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !hwqG Σ}.

  (**********************************************************)
  (* Begin LLM-generated code. *)
  (* tool: Claude Code 2.1.111
     model: Claude Opus 4.7 with 1M context (claude-opus-4-7)
     parameters:
        effort = max
        context window = 1000000
        max output tokens = 128000 *)

  (** A [scan_witness γ_slot γ_match j'] is a persistent witness recording
      the state of cell [j'] at some past trace [ts_scan]. It is one of:
      (a) CASed-at-scan: τ' was in [m_scan.*1] for some [m_scan] (forwardable
          to the current [m] by mono_list snapshot).
      (b) NotStored-at-scan: τ' hadn't returned from its push by [ts_scan]
          (recorded as [(τ', Ret #()) ∉ ts_scan]).
      Used in [pop_wrapper_spec]'s inner Löb to discharge the
      [order_correct_unmatched_snoc_match] premise at CAS commit. *)

  (* per_tag_wellformed_bag: each τ has at most one Push-Call event in the trace,
   so any two such events agree on the pushed value. *)
  Lemma per_tag_wellformed_bag_call_push_unique valid_value ts τ v v' :
    per_tag_wellformed_bag NeverEmpty valid_value ts →
    (τ, Call Push v) ∈ ts →
    (τ, Call Push v') ∈ ts →
    v = v'.
  Proof.
    intros Hwf Hin Hin'.
    assert (Hin_filt : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts).
    { apply list_elem_of_filter. done. }
    assert (Hin_filt' : (τ, Call Push v') ∈ filter (λ x, x.1 = τ) ts).
    { apply list_elem_of_filter. done. }
    destruct (Hwf τ) as [(w & _ & Hpfx)|(r & _ & Hpfx)].
    - eapply elem_of_prefix in Hin_filt; last exact Hpfx.
      eapply elem_of_prefix in Hin_filt'; last exact Hpfx.
      apply elem_of_cons in Hin_filt as [Heq|Hin_cons].
      + apply elem_of_cons in Hin_filt' as [Heq'|Hin_cons'].
        * injection Heq as Heq. injection Heq' as Heq'.
          by simplify_eq.
        * apply elem_of_cons in Hin_cons' as [Habs|Hnil]; [discriminate|by apply elem_of_nil in Hnil].
      + apply elem_of_cons in Hin_cons as [Habs|Hnil]; [discriminate|by apply elem_of_nil in Hnil].
    - exfalso.
      eapply elem_of_prefix in Hin_filt; last exact Hpfx.
      apply elem_of_cons in Hin_filt as [Habs|Hin_cons].
      + discriminate.
      + apply elem_of_cons in Hin_cons as [Habs|Hnil]; [discriminate|by apply elem_of_nil in Hnil].
  Qed.

  Lemma pre_of_trace_ret_in_pre_cell
        valid_value ts e1 ts_pre τ v :
    per_tag_wellformed_bag NeverEmpty valid_value ts →
    ts_pre ++ [(τ, Call Push v)] `prefix_of` ts →
    pre_of_trace ts e1 τ →
    e1 ∈ push_of_trace ts →
    (e1, Ret #()) ∈ ts_pre.
  Proof.
    intros Hwf Hpfx_cell Hpre Hpush.
    rewrite /pre_of_trace in Hpre.
    destruct (ret_of_tag ts e1) as [[i_ret t_ret]|] eqn:Hret_e1;
      simpl in Hpre; cycle 1; first done.
    destruct (call_of_tag ts τ) as [[i_call t_call]|] eqn:Hcall_τ;
      simpl in Hpre; cycle 1; first done.
    rewrite /ret_of_tag in Hret_e1. rewrite /call_of_tag in Hcall_τ.
    apply list_find_Some in Hret_e1 as (Hi_ret_lk & [Heq_e1 His_ret] & _).
    apply list_find_Some in Hcall_τ as (Hi_call_lk & [Heq_τ His_call] & _).
    destruct t_ret as [τ' t_ret]. simpl in Heq_e1. subst τ'.
    destruct t_call as [τ' t_call]. simpl in Heq_τ. subst τ'.
    destruct t_ret as [|? ? ?|v_ret]; [done|done|].
    destruct t_call as [n_call v_call|?|?]; [|done|done].
    (* Step 2: τ's Call value is uniquely [encode (Push v)] and its position is
       the unique [length ts_pre]. *)
    assert (Hin_call_τ : (τ, Call n_call v_call) ∈ ts)
      by (eapply list_elem_of_lookup_2; exact Hi_call_lk).
    assert (Hin_call_jn : (τ, Call Push v) ∈ ts).
    { destruct Hpfx_cell as [k Hk]. rewrite Hk.
      apply elem_of_app. left. apply elem_of_app. right.
      apply list_elem_of_singleton. reflexivity. }
    assert (Hpos_call_τ : ts !! length ts_pre =
                          Some (τ, Call Push v)).
    { destruct Hpfx_cell as [k Hk]. rewrite Hk -app_assoc lookup_app_r;
        last lia. by rewrite Nat.sub_diag. }
    assert (Hcall_eq : Call n_call v_call = Call Push v).
    { destruct (Hwf τ) as [(w & _ & Hpfx_filt)|(r & _ & Hpfx_filt)]; cycle 1.
      - exfalso.
        assert (Hin_filt : (τ, Call Push v) ∈
                            filter (λ x, x.1 = τ) ts)
          by (apply list_elem_of_filter; done).
        eapply elem_of_prefix in Hin_filt; last exact Hpfx_filt.
        apply elem_of_cons in Hin_filt as [Heq|Hin]; first by discriminate.
        apply elem_of_cons in Hin as [?|Habs]; [discriminate|by apply elem_of_nil in Habs].
      - assert (Hin_filt_jn : (τ, Call Push v) ∈
                               filter (λ x, x.1 = τ) ts)
          by (apply list_elem_of_filter; done).
        assert (Hin_filt_call : (τ, Call n_call v_call) ∈ filter (λ x, x.1 = τ) ts)
          by (apply list_elem_of_filter; done).
        eapply elem_of_prefix in Hin_filt_jn; last exact Hpfx_filt.
        eapply elem_of_prefix in Hin_filt_call; last exact Hpfx_filt.
        apply elem_of_cons in Hin_filt_jn as [Heq_jn|Hin_jn'].
        + apply elem_of_cons in Hin_filt_call as [Heq_call|Hin_call'].
          * by simplify_eq.
          * apply elem_of_cons in Hin_call' as [?|Hnil];
              [discriminate|by apply elem_of_nil in Hnil].
        + apply elem_of_cons in Hin_jn' as [?|Hnil];
            [discriminate|by apply elem_of_nil in Hnil]. }
    injection Hcall_eq as -> ->.
    assert (Hi_call_eq : i_call = length ts_pre).
    { eapply per_tag_wellformed_bag_call_push_pos_unique;
        [exact Hwf|exact Hi_call_lk|exact Hpos_call_τ]. }
    (* Step 3: localize (e1, Ret v_ret) into [ts_pre], then force v_ret = #(). *)
    rewrite Hi_call_eq in Hpre.
    assert (Hi_ret_in_pre : ts_pre !! i_ret = Some (e1, Ret v_ret)).
    { destruct Hpfx_cell as [k Hk]. rewrite Hk -app_assoc in Hi_ret_lk.
      rewrite lookup_app_l in Hi_ret_lk; [exact Hi_ret_lk|lia]. }
    rewrite /push_of_trace in Hpush.
    apply list_elem_of_fmap in Hpush as [[τ' t'] [Heq_τ Hin_e1_call]].
    simpl in Heq_τ. subst τ'.
    apply list_elem_of_filter in Hin_e1_call as [Hcall_e1 Hin_e1_call'].
    simpl in Hcall_e1. destruct Hcall_e1 as [v_e1 Hv_e1]. subst t'.
    assert (Hret_e1_eq : v_ret = #()).
    { assert (Hin_filt : (e1, Ret v_ret) ∈ filter (λ x, x.1 = e1) ts).
      { apply list_elem_of_filter. split; first reflexivity.
        eapply list_elem_of_lookup_2. exact Hi_ret_lk. }
      destruct (Hwf e1) as [(w & _ & Hpfx_filt)|(r & _ & Hpfx_filt)].
      - eapply elem_of_prefix in Hin_filt; last exact Hpfx_filt.
        apply elem_of_cons in Hin_filt as [Heq|Hin_filt]; first by discriminate.
        apply elem_of_cons in Hin_filt as [Heq|Habs]; cycle 1.
        + by apply elem_of_nil in Habs.
        + injection Heq as Heq. exact Heq.
      - exfalso.
        assert (Hin_call_e1 : (e1, Call Push v_e1) ∈
                               filter (λ x, x.1 = e1) ts)
          by (apply list_elem_of_filter; done).
        eapply elem_of_prefix in Hin_call_e1; last exact Hpfx_filt.
        apply elem_of_cons in Hin_call_e1 as [Heq|Hin_call]; first by discriminate.
        apply elem_of_cons in Hin_call as [Heq|Habs];
          [discriminate|by apply elem_of_nil in Habs]. }
    subst v_ret. by eapply list_elem_of_lookup_2.
  Qed.

  Definition scan_witness ts_outer (tracer : loc) γ_slot γ_match (j' : nat) : iProp Σ :=
    ∃ ts_scan τ',
      hist tracer ts_scan ∗
      ⌜ts_outer `prefix_of` ts_scan⌝ ∗
      j' ↪[γ_slot]□ τ' ∗
      ((∃ m_scan, own γ_match (◯ML m_scan) ∗ ⌜τ' ∈ m_scan.*1⌝)
       ∨ ⌜(τ', Ret #()) ∉ ts_scan⌝).

  Lemma pop_wrapper_spec γ tracer (q : val) :
    {{{ trace_inv tracer I_hwq ∗ is_hwq_trace γ q tracer }}}
      call_ret_wrapper tracer Pop (λ: "q" <>, SOME (dequeue "q"))%V q #()
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "[#Itrace #Ihwp] HΦ".
    wp_lam. wp_pures.

    (* ====== Phase 1: trace_fresh emit (τ_pop, Call Pop #()). ====== *)
    awp_apply (trace_fresh_spec with "Itrace"); first exact (decode_encode_val (Call Pop #())).
    iInv "Ihwp" as (sz l_ar l_back ar back ts m γ_back γ_ar γ_op γ_tkn γ_match γ_slot M_ar M_op M_tkn M_slot)
      ">(-> & Hvalid_trace & Hpstate & Hgstate & %Hdom & %Hpush_stored_inv & Hallocated & H)".
    iDestruct "Hpstate" as "(Htrace & Har & Hback)".
    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    iFrame "Htrace". iSplit.
    { iDestruct "Hvalid_trace" as "[%Hper_tag_wf %HI_queue_pre]". iPureIntro.
      intros τ Hfresh.
      destruct HI_queue_pre as (Hvm & Hps & Hocm & Hocu).
      split; last (exists m; rewrite /I_queue_pre; split_and!).
      - by apply per_tag_wellformed_bag_snoc_call_pop.
      - by apply valid_match_snoc_call_pop.
      - by apply per_tag_pop_empty_sound_snoc_call_pop.
      - by apply order_correct_matched_snoc_call_pop.
      - by apply order_correct_unmatched_snoc_call_pop. }
    iSplit.
    { iIntros "[Hpstate _]". iMod "Hclose". iModIntro.
      iSplitR "HΦ"; last done.
      iNext. iExists sz, l_ar, l_back, ar. iFrame. done. }
    iIntros (τ_pop) "[Htrace %Hfresh]". iMod "Hclose" as "_".
    iDestruct "H" as "(Hunallocated & Hm_nodup & Hop & #Hreturned)".
    iDestruct "Hgstate" as "(#Hmeta & Hback● & Har● & Hop● & Htkn● & Hmatch● & Hslot●)".
    iDestruct (alloc_hist with "Htrace") as "[Htrace #Hhist_pop]".
    iEval (rewrite mono_nat_auth_lb_op) in "Hback●".
    iDestruct "Hback●" as "[Hback● #Hback◯]".
    iMod (ghost_map_insert τ_pop PopCalled with "Hop●") as "[Hop● Hop◯]".
    { apply not_elem_of_dom. destruct Hdom as (_ & _ & -> & _ & _).
      rewrite /events_of_trace. clear -Hfresh. set_solver. }
    iMod (ghost_map_insert τ_pop 0 with "Htkn●") as "[Htkn● Htkn_pop◯]".
    { apply not_elem_of_dom.
      destruct Hdom as (Hd_tkn & _ & Hd_op & _ & _).
      rewrite Hd_tkn Hd_op /events_of_trace.
      intros Hin. apply Hfresh.
      apply (elem_of_list_to_set (C := gset positive)) in Hin. exact Hin. }
    iModIntro. iSplitR "HΦ Hop◯ Htkn_pop◯".
    { iNext.
      iExists sz, l_ar, l_back, ar.
      iFrame "Hmeta Har Hback Htrace Hunallocated Hback● Har● Htkn● Hop● Hmatch● Hm_nodup Hslot●".
      iSplit; first done.
      iSplit.
      { iDestruct "Hvalid_trace" as "[%Hper_tag_wf %HI_queue_pre]". iPureIntro.
        destruct HI_queue_pre as (Hvm & Hps & Hocm & Hocu).
        rewrite /I_queue_pre. split_and!.
        - by eapply per_tag_wellformed_bag_snoc_call_pop.
        - by apply valid_match_snoc_call_pop.
        - by apply per_tag_pop_empty_sound_snoc_call_pop.
        - by apply order_correct_matched_snoc_call_pop.
        - by apply order_correct_unmatched_snoc_call_pop. }
      iSplit.
      { iPureIntro.
        destruct Hdom as (Hd_tkn & Hd_ar & Hd_op & Hd_len & Hd_slot).
        split_and!.
        - rewrite !dom_insert_L. clear -Hd_tkn. set_solver.
        - exact Hd_ar.
        - rewrite /events_of_trace fmap_app list_to_set_snoc_L.
          rewrite dom_insert_L Hd_op. clear. set_solver.
        - exact Hd_len.
        - exact Hd_slot. }
      iSplit.
      { (* Hpush_stored_inv: τ_pop is a fresh tag, M_op[τ_pop] := PopCalled (not stored). *)
        iPureIntro.
        intros τ' s_op' i' Hop_lookup_τ' Hstored Htkn_lookup_τ'.
        rewrite lookup_insert_Some in Hop_lookup_τ'.
        rewrite lookup_insert_Some in Htkn_lookup_τ'.
        destruct Hop_lookup_τ' as [[<- <-]|[Hτ_neq Hop_lookup_τ']].
        - destruct Hstored; discriminate.
        - destruct Htkn_lookup_τ' as [[<- _]|[_ Htkn_lookup_τ']]; first done.
          eapply Hpush_stored_inv; eauto. }
      iSplitL "Hallocated".
      { iApply (big_sepL_impl with "Hallocated").
        iIntros "!#" (i a Hlk) "Hcell".
        iDestruct "Hcell" as (ts_prefix τ₀ v₀ ɛ₀) "(#Hcall & %Hub₀ & $ & #Hslot_τ₀ & Hcell_state)".
        iFrame "Hcall Hslot_τ₀". iExists ɛ₀.
        iSplit; first done.
        destruct (M_ar !!! i).
        - iDestruct "Hcell_state" as "[[% %Hno_ret] $]".
          iPureIntro. split; first done.
          intros HFalse. contradict Hno_ret.
          rewrite elem_of_app list_elem_of_singleton in HFalse.
          destruct HFalse as [? | HFalse]; first done.
          exfalso. discriminate HFalse.
        - iExact "Hcell_state".
        - iExact "Hcell_state". }
      iSplitL "Hop".
      { destruct Hdom as (_ & _ & Hd_op & _ & _).
        rewrite /events_of_trace in Hd_op.
        pose proof (Hfresh' := Hfresh).
        rewrite -(not_elem_of_list_to_set (C:=gset positive)) -Hd_op in Hfresh'.
        iApply big_sepM_insert; first by apply not_elem_of_dom.
        iSplitR.
        - iPureIntro. simpl.
          rewrite filter_app filter_False_nil.
          + rewrite left_id_L filter_cons_True //.
          + apply Forall_forall.
            intros [τ' t] Hin%(list_elem_of_fmap_2 fst) <-. done.
        - iApply (big_sepM_impl with "Hop").
          iIntros "!#" (τ' s_op Hlookup) "%Htrace_inv !%".
          rewrite /trace_per_tag_inv.
          assert (τ_pop ≠ τ').
          { intros <-. apply elem_of_dom_2 in Hlookup. done. }
          rewrite filter_app filter_cons_False; last (simpl; congruence).
          rewrite filter_nil right_id_L.
          exact Htrace_inv. }
      iEval (rewrite filter_app filter_cons_False //).
      iEval (rewrite filter_nil right_id_L).
      iExact "Hreturned". }

    (* ====== Phase 2: wp_pures into [SOMEV (dequeue q)]. ====== *)
    wp_pures.
    wp_bind (dequeue _).

    (* ====== Phase 3: outer Löb on [dequeue q]. ====== *)
    iLöb as "IH_outer".
    wp_lam. wp_pures.

    (* Read l_back to get a snapshot of the current back counter. *)
    wp_bind (! _)%E.
    iInv "Ihwp" as (sz3 l_ar3 l_back3 ar3 back3 ts3 m3 γ_back3 γ_ar3 γ_op3 γ_tkn3 γ_match3 γ_slot3 M_ar3 M_op3 M_tkn3 M_slot3)
      ">(%Hq_eq3 & Hvalid_trace3 & Hpstate3 & Hgstate3 & %Hdom3 & %Hpush_stored_inv3 & Hallocated3 & %Hunallocated3 & Hm_nodup3 & Hop3 & #Hreturned3)".
    injection Hq_eq3 as Hsz_eq <- <-. apply Nat2Z.inj in Hsz_eq. subst sz3.
    iDestruct "Hpstate3" as "(Htrace3 & Har3 & Hback3)".
    iDestruct "Hgstate3" as "(#Hmeta3 & Hback●3 & Har●3 & Hop●3 & Htkn●3 & Hmatch●3 & Hslot●3)".
    iDestruct (own_valid_2 with "Hmeta Hmeta3") as %Hagree3%to_agree_op_inv_L.
    injection Hagree3 as <- <- <- <- <- <-. iClear "Hmeta3".
    wp_load.
    iEval (rewrite mono_nat_auth_lb_op) in "Hback●3".
    iDestruct "Hback●3" as "[Hback●3 #Hback_curr◯]".
    (* Snapshot the trace at outer-back-read. We use this hist witness later
       to bound the cell-at-j_n's [Call] event prefix at scan time. *)
    iDestruct (alloc_hist with "Htrace3") as "[Htrace3 #Hhist_outer]".
    (* Extract per-cell persistent witnesses bounded by [ts3]. *)
    iDestruct (big_sepL_allocated_ar_inv_allocated_ar_inv' with "Htrace3 Hallocated3")
      as "[Htrace3 Hallocated3']".
    iAssert ([∗ list] j↦a ∈ take back3 ar3,
                ∃ ts_pre_j τ_j v_j,
                  hist tracer (ts_pre_j ++ [(τ_j, Call Push v_j)]) ∗
                  ⌜ts_pre_j ++ [(τ_j, Call Push v_j)] `prefix_of` ts3⌝ ∗
                  j ↪[γ_slot]□ τ_j)%I as "#Hcalls_at_outer".
    { iApply (big_sepL_impl with "Hallocated3'").
      iIntros "!#" (j a Hlk).
      iDestruct 1 as (ts_pre_j τ_j v_j ɛ_j) "(%Hpfx_j & #Hist_j & _ & _ & #Hslot_j & _)".
      iExists ts_pre_j, τ_j, v_j. iFrame "Hist_j Hslot_j". iPureIntro. exact Hpfx_j. }
    iDestruct (big_sepL_allocated_ar_inv'_allocated_ar_inv with "Hallocated3'") as "Hallocated3".
    iModIntro. iSplitR "HΦ Hop◯ Htkn_pop◯".
    { iNext. iExists sz, l_ar, l_back, ar3, back3, ts3, m3.
      iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
      iExists M_ar3, M_op3, M_tkn3, M_slot3.
      iFrame "Hmeta Hvalid_trace3 Htrace3 Har3 Hback3 Hback●3 Har●3 Hop●3 Htkn●3 Hmatch●3 Hslot●3".
      iFrame "Hallocated3 Hm_nodup3 Hop3 Hreturned3".
      iSplit; first done.
      iSplit.
      { iPureIntro. exact Hdom3. }
      iSplit; first by iPureIntro.
      iPureIntro. exact Hunallocated3. }

    wp_pures.
    wp_apply minimum_spec.
    wp_pures.

    (* Generalize: introduce [range_z] (fixed) with bounds [0 ≤ range_z ≤ sz]. *)
    remember (Z.of_nat back3 `min` Z.of_nat sz)%Z as range_z eqn:Hrange_z.
    assert (Hrange_le_sz : (range_z ≤ Z.of_nat sz)%Z).
    { subst range_z. apply Z.le_min_r. }
    assert (Hrange_le_back3 : (range_z ≤ Z.of_nat back3)%Z).
    { subst range_z. apply Z.le_min_l. }
    assert (Hrange_pos : (0 ≤ range_z)%Z).
    { subst range_z. apply Z.min_glb; apply Nat2Z.is_nonneg. }
    clear Hrange_z.

    (* ====== Phase 4: inner Löb on [dequeue_aux dequeue q range_z i].
       Threaded preconditions:
       - [0 ≤ i_iter ≤ range_z] for in-array indexing.
       - A persistent scan-witness list for slots [0..range_z - i_iter)],
         used at CAS commit to discharge [order_correct_unmatched_snoc_match]. *)
    iAssert (∀ (i_iter : Z),
              ⌜(0 ≤ i_iter ≤ range_z)%Z⌝ -∗
              ([∗ list] j' ∈ seq 0 (Z.to_nat (range_z - i_iter)),
                 scan_witness ts3 tracer γ_slot γ_match j') -∗
              (∀ v : val, True -∗ Φ v) -∗
              τ_pop ↪[γ_op] PopCalled -∗
              τ_pop ↪[γ_tkn]{#1} 0 -∗
              WP (dequeue_aux dequeue (#sz, #l_ar, #l_back)%V #range_z #i_iter)%E
                {{ (v_ret : val),
                   WP (let: "res" := InjR v_ret in
                       trace_emit #tracer #(Z.pos τ_pop) (InjR "res") ;; "res")%E
                   {{ (v' : val), Φ v' }} }})%I
      as "Hloop"; last first.
    { iApply ("Hloop" $! range_z with "[%] [] HΦ Hop◯ Htkn_pop◯"); [lia|].
      rewrite Z.sub_diag /=. done. }
    iIntros (i_iter).
    iLöb as "IH_inner" forall (i_iter).
    iIntros (Hi_bounds) "#Hscan HΦ Hop◯ Htkn_pop◯".

    wp_lam. wp_pures.

    (* Phase 4(a): if [range_z = 0], tail-call into [dequeue]. Use [IH_outer]. *)
    case_bool_decide as Hi_zero.
    { (* range_z = 0 case — tail-call dequeue. *)
      wp_pures. iApply ("IH_outer" with "HΦ Hop◯ Htkn_pop◯"). }

    (* Phase 4(b)-(d): i_iter > 0 case. *)
    wp_pures.

    (* ====== Phase 4(b): Load q.ar[j] where j = range_z - i_iter. ====== *)
    wp_bind (! _)%E.
    iInv "Ihwp" as (sz4 l_ar4 l_back4 ar4 back4 ts4 m4 γ_back4 γ_ar4 γ_op4 γ_tkn4 γ_match4 γ_slot4 M_ar4 M_op4 M_tkn4 M_slot4)
      ">(%Hq_eq4 & Hvalid_trace4 & Hpstate4 & Hgstate4 & %Hdom4 & %Hpush_stored_inv4 & Hallocated4 & %Hunallocated4 & Hm_nodup4 & Hop4 & #Hreturned4)".
    injection Hq_eq4 as Hsz_eq <- <-. apply Nat2Z.inj in Hsz_eq. subst sz4.
    iDestruct "Hpstate4" as "(Htrace4 & Har4 & Hback4)".
    iDestruct "Hgstate4" as "(#Hmeta4 & Hback●4 & Har●4 & Hop●4 & Htkn●4 & Hmatch●4 & Hslot●4)".
    iDestruct (own_valid_2 with "Hmeta Hmeta4") as %Hagree4%to_agree_op_inv_L.
    injection Hagree4 as <- <- <- <- <- <-. iClear "Hmeta4".

    (* Set up the slot index [j_n : nat]. Bounds derived from threaded
       [Hi_bounds] (0 ≤ i_iter ≤ range_z), [Hi_zero] (i_iter ≠ 0), [Hrange_le_sz]
       (range_z ≤ Z.of_nat sz), and the inv's [length ar4 = sz]. *)
    destruct Hdom4 as (Hd_tkn4 & Hd_ar4 & Hd_op4 & Hd_len4 & Hd_slot4).
    assert (Hi_pos : (0 < i_iter)%Z).
    { destruct (Z.eq_dec i_iter 0) as [->|]; [exfalso; apply Hi_zero; reflexivity|lia]. }
    assert (Hbounds : (0 ≤ range_z - i_iter < Z.of_nat (length ar4))%Z).
    { rewrite Hd_len4. lia. }
    set (j_n := Z.to_nat (range_z - i_iter)).
    assert (Hj_n_lt : j_n < length ar4) by (subst j_n; lia).
    assert (Hj_n_eq : Z.of_nat j_n = (range_z - i_iter)%Z) by (subst j_n; lia).
    apply lookup_lt_is_Some in Hj_n_lt as [a_j Ha_j].

    (* Load via wp_apply (wp_load_offset _ _ _ _ j_n ar4 a_j with "Har4")
       after [replace (range_z - i_iter)%Z with (Z.of_nat j_n) by exact Hj_n_eq]. *)
    rewrite -Hj_n_eq.
    wp_apply (wp_load_offset _ _ _ _ j_n ar4 a_j with "Har4") as "Har4";
      first exact Ha_j.

    (* Snapshot a persistent scan witness for slot j_n: either
       (a) cell at j_n was CASed at scan ⇒ τ_cell ∈ m_at_scan.*1
           (so by mono_list snapshot, ⊆ m_curr.*1), or
       (b) cell was NotStored at scan ⇒ a hist tracer ts_at_scan
           witnessing the push tag hadn't returned by scan time. *)
    (* Derive [j_n < back4] via [Hback_curr◯] vs [Hback●4]. *)
    iDestruct (own_valid_2 with "Hback●4 Hback_curr◯") as %Hback4_lb%mono_nat_both_valid.
    assert (Hj_n_lt_back4 : j_n < back4).
    { subst j_n. lia. }
    assert (Hj_n_take : take back4 ar4 !! j_n = Some a_j).
    { rewrite lookup_take_lt; [exact Ha_j|exact Hj_n_lt_back4]. }
    iDestruct (big_sepL_lookup_acc _ _ j_n a_j Hj_n_take with "Hallocated4")
      as "[Hcell_jn Hclose_cell_jn]".
    iDestruct "Hcell_jn" as (ts_pre_jn τ_jn v_jn ε_jn)
      "(#Hcall_jn & %Hub_jn & #Hpre_jn & #Hslot_jn & Hcell_state_jn)".
    (* Snapshot trace and match list at scan time; [ts3] (outer-back-read) is a
       prefix of [ts4] (current scan). *)
    iDestruct (alloc_hist with "Htrace4") as "[Htrace4 #Hhist_ts4]".
    iDestruct (hist_trace_is_prefix with "Htrace4 Hhist_outer") as %Hpfx_outer4.
    iEval (rewrite mono_list_auth_lb_op) in "Hmatch●4".
    iDestruct "Hmatch●4" as "[Hmatch●4 #Hm4_snap]".
    iAssert (∃ τ_cell : positive, j_n ↪[γ_slot]□ τ_cell)%I as "#Hscan_jn".
    { iExists τ_jn. iFrame "Hslot_jn". }
    (* Combined extraction: derive [Hshape] (a_j is NONEV or SOMEV v_jn) AND a
       conditional scan_witness for slot j_n (valid when a_j = NONEV: cell must
       be NotStored or CASed, since StoredNotCAS forces a_j = SOMEV). The
       reconstructed cell content is the same as before the destructure. *)
    iAssert (⌜a_j = NONEV ∨ a_j = InjRV v_jn⌝ ∗
             (⌜a_j = NONEV⌝ -∗ scan_witness ts3 tracer γ_slot γ_match j_n) ∗
             match M_ar4 !!! j_n with
             | NotStored => ⌜a_j = NONEV ∧ (τ_jn, Ret #()) ∉ ts4⌝ ∗ τ_jn ↪[γ_tkn]{#2/3+ε_jn} j_n
             | StoredNotCAS => j_n ↪[γ_ar] StoredNotCAS ∗ ⌜a_j = SOMEV v_jn⌝ ∗ τ_jn ↪[γ_tkn]{#2/3+ε_jn} j_n
             | CASed => j_n ↪[γ_ar] CASed ∗ ⌜a_j = NONEV ∧ τ_jn ∈ m4.*1⌝
             end)%I with "[Hcell_state_jn]"
      as "(%Hshape & #Hscan_jn_cond & Hcell_state_jn)".
    { destruct (M_ar4 !!! j_n) eqn:Hsj_n.
      - (* NotStored *)
        iDestruct "Hcell_state_jn" as "[[%Heq %Hno_ret] Htkn_jn]".
        iSplit; first by iPureIntro; left.
        iSplit.
        { iIntros (_). rewrite /scan_witness.
          iExists ts4, τ_jn. iFrame "Hhist_ts4 Hslot_jn".
          iSplit; first by iPureIntro.
          iRight. by iPureIntro. }
        iSplit; first (iPureIntro; split; done).
        iExact "Htkn_jn".
      - (* StoredNotCAS *)
        iDestruct "Hcell_state_jn" as "[Har_cell [%Heq Htkn_jn]]".
        iSplit; first by iPureIntro; right.
        iSplit.
        { iIntros (Ha_j_NONEV). rewrite Heq in Ha_j_NONEV. discriminate. }
        iFrame "Har_cell". iSplit; first by iPureIntro. iExact "Htkn_jn".
      - (* CASed *)
        iDestruct "Hcell_state_jn" as "[Har_cell %Hpure]".
        destruct Hpure as [Heq Hin].
        iSplit; first by iPureIntro; left.
        iSplit.
        { iIntros (_). rewrite /scan_witness.
          iExists ts4, τ_jn. iFrame "Hhist_ts4 Hslot_jn".
          iSplit; first by iPureIntro.
          iLeft. iExists m4. iFrame "Hm4_snap". by iPureIntro. }
        iFrame "Har_cell". iPureIntro. split; done. }
    iDestruct ("Hclose_cell_jn" with "[Hcell_state_jn]") as "Hallocated4".
    { iExists ts_pre_jn, τ_jn, v_jn, ε_jn.
      iFrame "Hcall_jn Hpre_jn Hslot_jn Hcell_state_jn".
      done. }

    (* Close inv unchanged. *)
    iModIntro. iSplitR "HΦ Hop◯ Htkn_pop◯".
    { iNext. iExists sz, l_ar, l_back, ar4, back4, ts4, m4.
      iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
      iExists M_ar4, M_op4, M_tkn4, M_slot4.
      iFrame "Hmeta Hvalid_trace4 Htrace4 Har4 Hback4".
      iFrame "Hback●4 Har●4 Hop●4 Htkn●4 Hmatch●4 Hslot●4".
      iFrame "Hallocated4 Hm_nodup4 Hop4 Hreturned4".
      iSplit; first done.
      iSplit.
      { iPureIntro. split_and!; [exact Hd_tkn4|exact Hd_ar4|exact Hd_op4|exact Hd_len4|exact Hd_slot4]. }
      iSplit; first by iPureIntro.
      iPureIntro. exact Hunallocated4. }

    wp_pures.

    (* Match on a_j: NONEV (skip) or SOMEV v (try CAS). *)
    destruct (decide (a_j = NONEV)) as [Ha_j_NONEV | Ha_j_some].
    { (* ====== Phase 4(b): NONE-arm — recurse with i_iter - 1. ====== *)
      iAssert (scan_witness ts3 tracer γ_slot γ_match j_n)%I as "#Hscan_jn_full".
      { iApply "Hscan_jn_cond". by iPureIntro. }
      rewrite Ha_j_NONEV. wp_pures.
      iApply ("IH_inner" $! (i_iter - 1)%Z with "[%] [Hscan] HΦ Hop◯ Htkn_pop◯");
        first lia.
      (* Extend Hscan with the new witness for slot j_n. *)
      assert (Hseq_eq : Z.to_nat (range_z - (i_iter - 1))
                      = Z.to_nat (range_z - i_iter) + 1) by lia.
      rewrite Hseq_eq seq_app big_sepL_app big_sepL_singleton.
      replace (0 + Z.to_nat (range_z - i_iter))%nat with j_n by (subst j_n; lia).
      iFrame "Hscan Hscan_jn_full". }

    (* SOMEV-arm: a_j ≠ NONEV. From [Hshape] (a_j = NONEV or a_j = InjRV v_jn),
       a_j must be InjRV v_jn. *)
    assert (a_j_inner_eq : a_j = InjRV v_jn).
    { destruct Hshape as [Heq|Heq]; [exfalso; by apply Ha_j_some|exact Heq]. }
    rewrite a_j_inner_eq.
    set (a_j_inner := v_jn).
    wp_pures.

    (* ====== Phase 4(c)/(d): CAS at l_ar +ₗ j_n: SOMEV a_j_inner ↔ NONEV. ====== *)
    wp_bind (CmpXchg _ _ _).
    iInv "Ihwp" as (sz5 l_ar5 l_back5 ar5 back5 ts5 m5 γ_back5 γ_ar5 γ_op5 γ_tkn5 γ_match5 γ_slot5 M_ar5 M_op5 M_tkn5 M_slot5)
      ">(%Hq_eq5 & Hvalid_trace5 & Hpstate5 & Hgstate5 & %Hdom5 & %Hpush_stored_inv5 & Hallocated5 & %Hunallocated5 & Hm_nodup5 & Hop5 & #Hreturned5)".
    injection Hq_eq5 as Hsz_eq <- <-. apply Nat2Z.inj in Hsz_eq. subst sz5.
    iDestruct "Hpstate5" as "(Htrace5 & Har5 & Hback5)".
    iDestruct "Hgstate5" as "(#Hmeta5 & Hback●5 & Har●5 & Hop●5 & Htkn●5 & Hmatch●5 & Hslot●5)".
    iDestruct (own_valid_2 with "Hmeta Hmeta5") as %Hagree5%to_agree_op_inv_L.
    injection Hagree5 as <- <- <- <- <- <-. iClear "Hmeta5".

    (* j_n < length ar5: from inv [length ar5 = sz] + threaded bounds. *)
    destruct Hdom5 as (Hd_tkn5 & Hd_ar5 & Hd_op5 & Hd_len5 & Hd_slot5).
    assert (Hj_n_lt5 : j_n < length ar5).
    { rewrite Hd_len5. subst j_n. lia. }
    apply lookup_lt_is_Some in Hj_n_lt5 as [a_j5 Ha_j5].

    destruct (decide (a_j5 = InjRV a_j_inner)) as [Ha_j5_eq | Ha_j5_neq].
    { (* ====== Phase 4(c): CAS success — state was StoredNotCAS, transition
         to CASed. Commit the match (snoc_match) and run Phase 5
         (trace_emit Ret). ====== *)
      replace (range_z - i_iter)%Z with (Z.of_nat j_n) by exact Hj_n_eq.
      wp_apply (wp_cmpxchg_suc_offset _ _ _ j_n with "Har5") as "Har5".
      { rewrite Ha_j5_eq in Ha_j5. exact Ha_j5. }
      { reflexivity. }
      { (* vals_compare_safe a_j5 (InjRV a_j_inner): from Hub_jn (val_is_unboxed
           (SOMEV v_jn)) and a_j_inner = v_jn. *)
        left. exact Hub_jn. }

      (* Decompose Hallocated5 at j_n. Cell at j_n is in StoredNotCAS arm
         (NotStored has a = NONEV, but a_j5 = SOMEV; CASed has a = NONEV too). *)
      iDestruct (own_valid_2 with "Hback●5 Hback_curr◯") as %Hback5_lb%mono_nat_both_valid.
      assert (Hj_n_lt_back5 : j_n < back5) by (subst j_n; lia).
      assert (Hj_n_take5 : take back5 ar5 !! j_n = Some a_j5).
      { rewrite lookup_take_lt; [exact Ha_j5|exact Hj_n_lt_back5]. }
      pose proof (take_drop_middle _ _ _ Hj_n_take5) as Hsplit5.
      assert (Hlen_inner5 : length (take j_n (take back5 ar5)) = j_n).
      { rewrite take_take (Nat.min_l j_n back5); [|lia]. rewrite length_take_le; lia. }
      iEval (rewrite -Hsplit5 big_sepL_app big_sepL_cons Hlen_inner5 Nat.add_0_r) in "Hallocated5".
      iDestruct "Hallocated5" as "(Hpre5 & Hcell5 & Hpost5)".
      iDestruct "Hcell5" as (ts_pre_cell τ_cell v_cell ε_cell)
        "(#Hcall_cell5 & %Hub_cell5 & #Hpre_cell5 & #Hslot_cell5 & Hcell_state5)".
      iDestruct (ghost_map_elem_agree with "Hslot_cell5 Hslot_jn") as %->.
      iDestruct "Hvalid_trace5" as %Hvtr5.
      destruct Hvtr5 as [Hwf5 HI5].
      destruct (M_ar5 !!! j_n) eqn:Hsj_n5; cycle 1.
      - (* StoredNotCAS — the only consistent case. *)
        iDestruct "Hcell_state5" as "(Har_cell & %Heq_a & Htkn_cell)".
        assert (Hv_cell_eq : v_cell = v_jn).
        { rewrite Heq_a in Ha_j5_eq. injection Ha_j5_eq as Heq. exact Heq. }
        subst v_cell.
        (* Split tokens for m_nodup contribution. (Doesn't depend on γ_match update.) *)
        iDestruct (ghost_map_elem_fractional with "Htkn_cell") as "[Htkn_jn_2t Htkn_jn_eps]".
        iEval (rewrite -aspect_dfrac_2third_1third) in "Htkn_pop◯".
        iDestruct (ghost_map_elem_fractional with "Htkn_pop◯") as "[Htkn_pop_2t Htkn_pop_1t]".
        (* Discharge I_queue_pre_snoc_match's order_correct_unmatched premise.
           For each preceding push e1 ≺ τ_jn, e1 ∈ m5.*1. *)
        iDestruct (hist_trace_is_prefix with "Htrace5 Hcall_jn") as %Hpfx_jn.
        assert (Hin_jn_ts5 : (τ_jn, Call Push v_jn) ∈ ts5).
        { destruct Hpfx_jn as [k Hk]. rewrite Hk. apply elem_of_app. left.
          apply elem_of_app. right. apply list_elem_of_singleton. reflexivity. }
        iDestruct (ghost_map_lookup with "Hop●5 Hop◯") as %Hop_lookup_pop.
        iDestruct (big_sepM_lookup _ _ τ_pop PopCalled with "Hop5") as %Htrace_pop;
          [exact Hop_lookup_pop|].
        simpl in Htrace_pop.
        assert (Hpop_no_ret : (τ_pop, Ret #()) ∉ ts5).
        { intros Hin. assert (Hin_filt : (τ_pop, Ret #()) ∈ filter (λ x, x.1 = τ_pop) ts5).
          { apply list_elem_of_filter. split; [reflexivity|exact Hin]. }
          rewrite Htrace_pop in Hin_filt. clear -Hin_filt. set_solver. }
        assert (Hpop_no_ret_filter : τ_pop ∉ (filter (is_ret ∘ snd) ts5).*1).
        { intros Hin. apply list_elem_of_fmap in Hin as [[τ' t] [Heq Hin']]. simpl in Heq. subst τ'.
          apply list_elem_of_filter in Hin' as [Hret Hin'].
          simpl in Hret. unfold is_ret in Hret. destruct t as [| | v_ret]; [done|done|].
          assert (Hin_filt : (τ_pop, Ret v_ret) ∈ filter (λ x, x.1 = τ_pop) ts5).
          { apply list_elem_of_filter. done. }
          rewrite Htrace_pop in Hin_filt. clear -Hin_filt. set_solver. }
        assert (Hin_pop_ts5 : (τ_pop, Call Pop #()) ∈ ts5).
        { assert (Hin_filt : (τ_pop, Call Pop #()) ∈ filter (λ x, x.1 = τ_pop) ts5).
          { rewrite Htrace_pop. clear. set_solver. }
          apply list_elem_of_filter in Hin_filt as [_ Hin]. exact Hin. }
        (* τ_jn ∉ m5.*1: cell at j_n was StoredNotCAS, so τ_jn was not yet matched.
           m_nodup gives unique τ for each m entry; if τ_jn ∈ m5.*1, there'd be a
           cell at some slot for τ_jn that's CASed. But our cell at j_n is
           StoredNotCAS. Slot uniqueness (M_slot bijective with M_tkn): τ_jn maps
           to j_n. So the only cell for τ_jn is at j_n. Hence τ_jn ∉ m5.*1. *)
        iDestruct (m_nodup_no_dup_push with "Hm_nodup5 Htkn_jn_2t") as %Hτ_jn_no_match.
        iDestruct (m_nodup_no_dup_pop with "Hm_nodup5 Htkn_pop_2t") as %Hτ_pop_no_match.
        (* Discharge order_correct_unmatched_snoc_match's premise via Hscan.
           For each preceding push e1 ≺ τ_jn:
           - e1's slot j' = M_tkn[e1] is < j_n via FAA monotonicity (from Hreturned5).
           - We have a [scan_witness] for j' in Hscan (j' < j_n = Z.to_nat (range_z - i_iter)).
           - The witness gives either CASed-at-scan (⇒ e1 ∈ m_scan ⊆ m5) or
             NotStored-at-scan (which contradicts e1 ≺ τ_jn since e1 returned before
             our pop's Phase 1 Call, hence before any of our scans). *)
        (* Establish [ts3 ⊆ ts5] for use in the discharge. *)
        iDestruct (hist_trace_is_prefix with "Htrace5 Hhist_outer") as %Hpfx_outer5.
        iAssert (⌜∀ e1, pre_of_trace ts5 e1 τ_jn → e1 ∈ push_of_trace ts5 → e1 ∈ m5.*1⌝)%I
          as %Hdischarge.
        { iIntros (e1 Hpre Hpush).
          (* Steps 1-2: from pre_of_trace + per_tag_wellformed_bag, derive
             [(e1, Ret #()) ∈ ts_pre_cell]; from [e1 ∈ push_of_trace], extract
             a Push value [v_e1] for [e1]'s Call event. *)
          iDestruct (hist_trace_is_prefix with "Htrace5 Hcall_cell5") as %Hpfx_cell.
          pose proof (pre_of_trace_ret_in_pre_cell _ _ _ _ _ _ Hwf5 Hpfx_cell Hpre Hpush)
            as Hin_pre_cell.
          rewrite /push_of_trace in Hpush.
          apply list_elem_of_fmap in Hpush as [[τ' t'] [Heq_τ Hin_e1_call]].
          simpl in Heq_τ. subst τ'.
          apply list_elem_of_filter in Hin_e1_call as [Hcall_e1 Hin_e1_call'].
          simpl in Hcall_e1. destruct Hcall_e1 as [v_e1 Hv_e1]. subst t'.
          (* Step 3: e1 ∈ (filter is_ret_push ts_pre_cell).*1. *)
          assert (He1_in_filt_pre : e1 ∈ (filter (is_ret_push ∘ snd) ts_pre_cell).*1).
          { apply list_elem_of_fmap. exists (e1, Ret #()). simpl. split; first reflexivity.
            apply list_elem_of_filter. split; first reflexivity. exact Hin_pre_cell. }
          (* Step 4: from Hpre_cell5, get j' < j_n with e1 ↪[γ_tkn]□ j'. *)
          iDestruct (big_sepL_elem_of with "Hpre_cell5") as "[%j' [#He1_tkn %Hj'_lt]]";
            first exact He1_in_filt_pre.
          (* Step 5: M_tkn5[e1] = j'. *)
          iDestruct (ghost_map_lookup with "Htkn●5 He1_tkn") as %He1_tkn_lookup.
          (* Step 6: From Hop5 + (e1, Ret #()) ∈ ts5 + (e1, Call Push) ∈ ts5,
             M_op5[e1] = PushReturned (the only state with both Call and Ret in trace). *)
          assert (Hin_pre_cell_ts5 : (e1, Ret #()) ∈ ts5).
          { destruct Hpfx_cell as [k Hk]. rewrite Hk. apply elem_of_app. left. apply elem_of_app. left. exact Hin_pre_cell. }
          assert (He1_in_dom : e1 ∈ dom M_op5).
          { rewrite Hd_op5 /events_of_trace.
            apply elem_of_list_to_set, list_elem_of_fmap.
            exists (e1, Ret #()). split; [reflexivity|exact Hin_pre_cell_ts5]. }
          apply elem_of_dom in He1_in_dom as [s_op_e1 Hop_e1_lookup].
          iDestruct (big_sepM_lookup _ _ e1 s_op_e1 with "Hop5") as %Htrace_e1;
            first exact Hop_e1_lookup.
          simpl in Htrace_e1.
          (* Trace shape for e1 includes both Call (Push v_e1) and Ret #(); among
             the operation states only PushReturned has both events. *)
          assert (Hcall_e1_in : (e1, Call Push v_e1) ∈
                                 filter (λ x, x.1 = e1) ts5)
            by (apply list_elem_of_filter; done).
          assert (Hret_e1_in : (e1, Ret #()) ∈ filter (λ x, x.1 = e1) ts5)
            by (apply list_elem_of_filter; done).
          assert (Hop_e1_eq : s_op_e1 = PushReturned).
          { destruct s_op_e1; auto; exfalso.
            - destruct Htrace_e1 as [v1 Heq1]. rewrite Heq1 in Hret_e1_in.
              clear -Hret_e1_in. set_solver.
            - destruct Htrace_e1 as [v2 Heq2]. rewrite Heq2 in Hret_e1_in.
              clear -Hret_e1_in. set_solver.
            - rewrite Htrace_e1 in Hcall_e1_in. clear -Hcall_e1_in. set_solver.
            - destruct Htrace_e1 as [v3 Heq3]. rewrite Heq3 in Hcall_e1_in.
              clear -Hcall_e1_in. set_solver. }
          subst s_op_e1.
          (* Step 7: by Hpush_stored_inv5, M_slot5[j'] = e1. *)
          assert (Hslot_e1 : M_slot5 !! j' = Some e1).
          { destruct (Hpush_stored_inv5 e1 PushReturned j' Hop_e1_lookup) as [_ Hslot_lk];
              [right; reflexivity|exact He1_tkn_lookup|exact Hslot_lk]. }
          (* Step 8: lookup scan_witness for j' (j' < j_n = Z.to_nat (range_z - i_iter)). *)
          assert (Hj'_in_seq : j' ∈ seq 0 (Z.to_nat (range_z - i_iter))).
          { apply elem_of_seq. subst j_n. lia. }
          iDestruct (big_sepL_elem_of with "Hscan") as "Hsw_j'"; first exact Hj'_in_seq.
          iDestruct "Hsw_j'" as (ts_scan τ_at_j') "(#Hist_scan & %Hpfx_outer_scan & #Hslot_at_j' & Hsw_arm)".
          (* Identify τ_at_j' = e1 via the auth: M_slot5[j'] = e1 (Hslot_e1) and
             j' ↪[γ_slot]□ τ_at_j' agree. *)
          iDestruct (ghost_map_lookup with "Hslot●5 Hslot_at_j'") as %Hslot_at_j_eq.
          rewrite Hslot_at_j_eq in Hslot_e1.
          injection Hslot_e1 as ->.
          iDestruct "Hsw_arm" as "[Hleft|%Hright]".
          - (* Left arm: e1 ∈ m_scan ⊆ OLD m5 (= current m5, before update). *)
            iDestruct "Hleft" as (m_scan) "[#Hm_scan_snap %He1_in_m_scan]".
            iDestruct (own_valid_2 with "Hmatch●5 Hm_scan_snap") as %[_ Hpfx_m]%mono_list_both_dfrac_valid_L.
            iPureIntro.
            destruct Hpfx_m as [k_m Hk_m]. rewrite Hk_m fmap_app.
            apply elem_of_app. left. exact He1_in_m_scan.
          - (* Right arm: (e1, Ret #()) ∉ ts_scan. We derive contradiction via:
               (e1, Ret #()) ∈ ts_pre_cell ⊆ ts3 ⊆ ts_scan.
               Step a: from #Hcalls_at_outer's j_n entry, we get
                 [hist tracer (ts_pre_outer_jn ++ [Call Push jn'])] ⊆ ts3.
               Step b: per_tag_wellformed gives ts_pre_cell = ts_pre_outer_jn.
               Step c: ts3 ⊆ ts_scan (from scan_witness). *)
            (* Look up the j_n-th entry of [Hcalls_at_outer] (j_n < back3). *)
            assert (Hj_n_lt_back3 : j_n < back3) by lia.
            assert (Hj_n_lt_len3 : j_n < length ar3)
              by (destruct Hdom3 as (_ & _ & _ & Hd_len3 & _); lia).
            destruct (lookup_lt_is_Some_2 ar3 j_n Hj_n_lt_len3) as [a3 Ha3].
            iDestruct (big_sepL_lookup _ _ j_n a3 with "Hcalls_at_outer") as
              (ts_pre_outer τ_outer v_outer) "(#Hcall_outer & %Hpfx_outer_jn & #Hslot_outer)";
              first by rewrite lookup_take_lt.
            iDestruct (ghost_map_elem_agree with "Hslot_outer Hslot_cell5") as %<-.
            iDestruct (hist_trace_is_prefix with "Htrace5 Hcall_outer") as %Hpfx_outer_in_ts5.
            (* per_tag_wellformed_bag uniqueness: ts_pre_outer = ts_pre_cell. *)
            destruct (per_tag_wellformed_bag_call_push_unique_prefix
                        _ _ _ _ _ _ _ Hwf5 Hpfx_cell Hpfx_outer_in_ts5) as [-> _].
            (* Chain: (e1, Ret #()) ∈ ts_pre_cell ⊆ ts3 ⊆ ts_scan, contradiction. *)
            iPureIntro. exfalso. apply Hright.
            destruct Hpfx_outer_scan as [k1 ->]. apply elem_of_app. left.
            destruct Hpfx_outer_jn as [k0 ->]. apply elem_of_app. left.
            apply elem_of_app. left. exact Hin_pre_cell. }
        (* Now perform the deferred ghost updates: M_ar[j_n] := CASed and
           m := m ++ [(τ_jn, τ_pop)]. *)
        iMod (ghost_map_update CASed with "Har●5 Har_cell") as "[Har●5 Har_cell_new]".
        iMod (own_update _ _ (●ML (m5 ++ [(τ_jn, τ_pop)])) with "Hmatch●5") as "Hmatch●5".
        { apply mono_list_update. by apply prefix_app_r. }
        (* Snapshot post-CAS m for use at Phase 5 (Ret-emit). *)
        iEval (rewrite mono_list_auth_lb_op) in "Hmatch●5".
        iDestruct "Hmatch●5" as "[Hmatch●5 #Hm5_snap]".
        assert (HI5_new : I_queue_pre ts5 (m5 ++ [(τ_jn, τ_pop)])).
        { eapply I_queue_pre_snoc_match; eauto. }
        (* Re-pack cell at j_n in the CASed arm. *)
        iAssert (allocated_ar_inv tracer γ_ar γ_tkn γ_slot ts5
                   (m5 ++ [(τ_jn, τ_pop)]) j_n NONEV CASed)%I
          with "[Har_cell_new]" as "Hcell_new".
        { iExists ts_pre_cell, τ_jn, v_jn, ε_cell.
          iFrame "Hcall_cell5 Hpre_cell5 Hslot_cell5".
          iSplit; first done.
          iFrame "Har_cell_new".
          iPureIntro. split; first done.
          rewrite fmap_app /=. apply elem_of_app. right. by apply list_elem_of_singleton. }
        (* Close inv. *)
        iModIntro. iSplitR "HΦ Hop◯ Htkn_pop_1t".
        { iNext.
          iExists sz, l_ar, l_back, (<[j_n := NONEV]> ar5), back5, ts5, (m5 ++ [(τ_jn, τ_pop)]).
          iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
          iExists (<[j_n := CASed]> M_ar5), M_op5, M_tkn5, M_slot5.
          iFrame "Hmeta Htrace5 Har5 Hback5".
          iFrame "Hback●5 Har●5 Hop●5 Htkn●5 Hmatch●5 Hslot●5".
          iFrame "Hop5 Hreturned5".
          iSplit; first done.
          iSplit.
          { iPureIntro. split; [exact Hwf5|exact HI5_new]. }
          iSplit.
          { iPureIntro. split_and!.
            - exact Hd_tkn5.
            - rewrite dom_insert_L Hd_ar5.
              assert (Hin_jn : j_n ∈ (list_to_set (seq 0 back5) : gset nat)).
              { rewrite elem_of_list_to_set elem_of_seq. lia. }
              clear -Hin_jn. set_solver.
            - exact Hd_op5.
            - rewrite length_insert. exact Hd_len5.
            - exact Hd_slot5. }
          iSplit.
          { iPureIntro.
            intros τ' s_op' i' Hop_lookup_τ' Hstored Htkn_lookup_τ'.
            destruct (decide (i' = j_n)) as [->|Hi_neq].
            - assert (Hold : (M_ar5 !! j_n = Some StoredNotCAS ∨ M_ar5 !! j_n = Some CASed)
                           ∧ M_slot5 !! j_n = Some τ').
              { eapply Hpush_stored_inv5; eauto. }
              destruct Hold as [_ Hslot_old].
              split; [right; by rewrite lookup_insert_eq|exact Hslot_old].
            - rewrite lookup_insert_ne; last done.
              eapply Hpush_stored_inv5; eauto. }
          iSplitR "Htkn_jn_2t Htkn_pop_2t Hm_nodup5".
          { (* big_sepL of cells with new ar, M_ar, m. *)
            rewrite (take_insert_lt _ back5 j_n); last lia.
            rewrite (insert_take_drop _ j_n NONEV);
              last by rewrite length_take; lia.
            rewrite big_sepL_app big_sepL_cons.
            rewrite Hlen_inner5 Nat.add_0_r.
            iSplitL "Hpre5".
            { iApply (big_sepL_impl with "Hpre5").
              iIntros "!#" (i x Hlk_x) "Hcell".
              assert (Hi_lt : i < j_n).
              { apply lookup_lt_Some in Hlk_x. rewrite Hlen_inner5 in Hlk_x. lia. }
              rewrite lookup_total_insert_ne; last lia.
              iApply allocated_ar_inv_mono_m. iExact "Hcell". }
            iSplitL "Hcell_new".
            { rewrite lookup_total_insert_eq. iExact "Hcell_new". }
            iApply (big_sepL_impl with "Hpost5").
            iIntros "!#" (i x Hlk_x) "Hcell".
            rewrite lookup_total_insert_ne; last lia.
            iApply allocated_ar_inv_mono_m. iExact "Hcell". }
          iSplit.
          { iPureIntro. rewrite drop_insert_lt; [exact Hunallocated5|lia]. }
          (* m_nodup: append (τ_jn, τ_pop). *)
          rewrite big_sepL_snoc. iFrame "Hm_nodup5".
          iSplitL "Htkn_jn_2t".
          - iExists j_n. iExact "Htkn_jn_2t".
          - iExists 0. iExact "Htkn_pop_2t". }

        (* ====== Phase 5: trace_emit Ret (NonEmpty v_jn). ====== *)
        wp_pures.
        awp_apply (trace_emit_spec _ _ (Ret (encode_response (NonEmpty v_jn)))
                   with "Itrace"); first reflexivity.
        iInv "Ihwp" as (sz6 l_ar6 l_back6 ar6 back6 ts6 m6 γ_back6 γ_ar6 γ_op6 γ_tkn6 γ_match6 γ_slot6 M_ar6 M_op6 M_tkn6 M_slot6)
          ">(%Hq_eq6 & Hvalid_trace6 & Hpstate6 & Hgstate6 & %Hdom6 & %Hpush_stored_inv6 & Hallocated6 & %Hunallocated6 & Hm_nodup6 & Hop6 & #Hreturned6)".
        injection Hq_eq6 as Hsz_eq <- <-. apply Nat2Z.inj in Hsz_eq. subst sz6.
        iDestruct "Hpstate6" as "(Htrace6 & Har6 & Hback6)".
        iDestruct "Hgstate6" as "(#Hmeta6 & Hback●6 & Har●6 & Hop●6 & Htkn●6 & Hmatch●6 & Hslot●6)".
        iDestruct (own_valid_2 with "Hmeta Hmeta6") as %Hagree6%to_agree_op_inv_L.
        injection Hagree6 as <- <- <- <- <- <-. iClear "Hmeta6".
        rewrite /atomic_acc /=.
        iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose6".
        iDestruct (ghost_map_lookup with "Hop●6 Hop◯") as %Hop6_lookup.
        iDestruct (big_sepM_lookup _ _ τ_pop PopCalled with "Hop6") as %Htrace6_pop;
          [exact Hop6_lookup|].
        simpl in Htrace6_pop.
        assert (Hpop_in_filter6 : (τ_pop, Call Pop #()) ∈ filter (λ x, x.1 = τ_pop) ts6).
        { rewrite Htrace6_pop. clear. set_solver. }
        apply list_elem_of_filter in Hpop_in_filter6 as [_ Hpop_in_ts6].
        iAssert (⌜(τ_jn, τ_pop) ∈ m6⌝)%I as %Hmatch_in_m6.
        { iCombine "Hmatch●6 Hm5_snap" gives %[_ Hpfx]%mono_list_both_dfrac_valid_L.
          iPureIntro.
          destruct Hpfx as [tail Htail]. rewrite Htail.
          apply elem_of_app. left.
          apply elem_of_app. right. apply list_elem_of_singleton. reflexivity. }
        iDestruct (hist_trace_is_prefix with "Htrace6 Hcall_jn") as %Hpfx6_jn.
        assert (Hin_jn_ts6 : (τ_jn, Call Push v_jn) ∈ ts6).
        { destruct Hpfx6_jn as [k Hk]. rewrite Hk. apply elem_of_app. left.
          apply elem_of_app. right. apply list_elem_of_singleton. reflexivity. }
        iDestruct "Hvalid_trace6" as %[Hwf6 HI6].
        iFrame "Htrace6". iSplit.
        { iPureIntro. split.
          - apply (per_tag_wellformed_bag_snoc_ret_pop _ _ _ _ (NonEmpty v_jn)); [done|done|done].
          - exists m6.
            eapply I_queue_pre_snoc_ret_pop_val; eassumption. }
        iSplit.
        { (* abort branch *)
          iIntros "[Htrace6 _]". iMod "Hclose6" as "_". iModIntro.
          iSplitR "HΦ Hop◯ Htkn_pop_1t".
          - iNext.
            iExists sz, l_ar, l_back, ar6, back6, ts6, m6.
            iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
            iExists M_ar6, M_op6, M_tkn6, M_slot6.
            iFrame "Hmeta Htrace6 Har6 Hback6".
            iFrame "Hback●6 Har●6 Hop●6 Htkn●6 Hmatch●6 Hslot●6".
            iFrame "Hallocated6 Hm_nodup6 Hop6 Hreturned6".
            iSplit; first done.
            iSplit; first (iPureIntro; split; [exact Hwf6|exact HI6]).
            iSplit; first by iPureIntro.
            iSplit; first by iPureIntro.
            iPureIntro. exact Hunallocated6.
          - iFrame. }
        iIntros "Htrace6". iMod "Hclose6" as "_".
        iMod (ghost_map_update PopReturned with "Hop●6 Hop◯") as "[Hop●6 Hop◯]".
        iModIntro. iSplitR "HΦ".
        { iNext.
          iExists sz, l_ar, l_back, ar6, back6,
                  (ts6 ++ [(τ_pop, Ret (encode_response (NonEmpty v_jn)))]), m6.
          iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
          iExists M_ar6, (<[τ_pop := PopReturned]> M_op6), M_tkn6, M_slot6.
          iFrame "Hmeta Htrace6 Har6 Hback6".
          iFrame "Hback●6 Har●6 Hop●6 Htkn●6 Hmatch●6 Hslot●6".
          iFrame "Hm_nodup6".
          iSplit; first done.
          iSplit.
          { iPureIntro. split.
            - eapply per_tag_wellformed_bag_snoc_ret_pop; eauto.
            - eapply I_queue_pre_snoc_ret_pop_val; eassumption. }
          iSplit.
          { iPureIntro. destruct Hdom6 as (Hd_tkn6 & Hd_ar6 & Hd_op6 & Hd_len6 & Hd_slot6).
            apply elem_of_dom_2 in Hop6_lookup as Hop6_in.
            split_and!.
            - rewrite dom_insert_L Hd_tkn6. clear -Hop6_in. set_solver.
            - exact Hd_ar6.
            - rewrite dom_insert_L /events_of_trace fmap_app list_to_set_app_L.
              rewrite Hd_op6. clear -Hop6_in. set_solver.
            - exact Hd_len6.
            - exact Hd_slot6. }
          iSplit.
          { iPureIntro.
            intros τ' s_op' i' Hop_lookup_τ' Hstored Htkn_lookup_τ'.
            destruct (decide (τ' = τ_pop)) as [->|Hτ_neq].
            - rewrite lookup_insert_eq in Hop_lookup_τ'.
              injection Hop_lookup_τ' as <-. destruct Hstored; discriminate.
            - rewrite lookup_insert_ne in Hop_lookup_τ'; last done.
              eapply Hpush_stored_inv6; eauto. }
          iSplitL "Hallocated6".
          { (* Cells unchanged but ts grows. NotStored arm has [(τ, Ret #()) ∉ ts]. *)
            iApply (big_sepL_impl with "Hallocated6").
            iIntros "!#" (i a Hlk_a) "Hcell".
            iDestruct "Hcell" as (ts_p τ' v' ε') "(#H1 & %Hub' & #Hpre' & #Hsl' & Hst)".
            iExists ts_p, τ', v', ε'. iFrame "H1 Hpre' Hsl'".
            iSplit; first done.
            destruct (M_ar6 !!! i).
            - iDestruct "Hst" as "[[%Heq %Hno_ret] $]".
              iPureIntro. split; first done.
              intros Hin. apply elem_of_app in Hin as [Hin|Hin].
              + exact (Hno_ret Hin).
              + apply list_elem_of_singleton in Hin. injection Hin as Heq_τ Heq_t.
                discriminate.
            - iExact "Hst".
            - iExact "Hst". }
          iSplit.
          { iPureIntro. exact Hunallocated6. }
          iSplitL "Hop6".
          { rewrite (big_sepM_delete _ _ τ_pop PopCalled); [|exact Hop6_lookup].
            iDestruct "Hop6" as "[_ Hop6_rest]".
            rewrite (big_sepM_delete _ (<[τ_pop := PopReturned]> M_op6) τ_pop PopReturned);
              [|by rewrite lookup_insert_eq].
            iSplitR.
            - iPureIntro. simpl. exists v_jn.
              rewrite filter_app Htrace6_pop filter_cons_True //=.
            - rewrite delete_insert_eq.
              iApply (big_sepM_impl with "Hop6_rest").
              iIntros "!#" (τ' s_op' Hlk') "%Htrace_τ' !%".
              rewrite /trace_per_tag_inv in Htrace_τ' |- *.
              assert (τ_pop ≠ τ').
              { intros <-. rewrite lookup_delete_eq in Hlk'. discriminate. }
              rewrite filter_app filter_cons_False; last (simpl; congruence).
              rewrite filter_nil right_id_L.
              exact Htrace_τ'. }
          iEval (rewrite filter_app filter_cons_False //=).
          iEval (rewrite filter_nil right_id_L).
          iExact "Hreturned6". }
        wp_pures. by iApply "HΦ".
      - (* CASed: cell has [a = NONEV], but a_j5 = SOMEV. Contradiction. *)
        iDestruct "Hcell_state5" as "[_ %Hpure]".
        destruct Hpure as [Heq_a _]. rewrite Heq_a in Ha_j5_eq. discriminate.
      - (* NotStored: cell has [a = NONEV], but a_j5 = SOMEV. Contradiction. *)
        iDestruct "Hcell_state5" as "[[%Heq_a _] _]". rewrite Heq_a in Ha_j5_eq. discriminate. }
    { (* ====== Phase 4(d): CAS failure — recurse with i_iter - 1. ====== *)
      replace (range_z - i_iter)%Z with (Z.of_nat j_n) by exact Hj_n_eq.
      wp_apply (wp_cmpxchg_fail_offset _ _ _ _ j_n with "Har5") as "Har5".
      { exact Ha_j5. }
      { exact Ha_j5_neq. }
      { (* vals_compare_safe a_j5 (InjRV a_j_inner): from Hub_jn. *)
        right. exact Hub_jn. }
      (* Reconstruct a scan_witness for j_n from the post-CAS cell state.
         Since [a_j5 ≠ SOMEV v_jn] (Ha_j5_neq) and the cell's StoredNotCAS arm
         would force [a_j5 = SOMEV v_jn5 = SOMEV v_jn] (per_tag_wellformed_bag
         uniqueness), the cell at j_n is NotStored or CASed at this point. *)
      iDestruct (own_valid_2 with "Hback●5 Hback_curr◯") as %Hback5_lb%mono_nat_both_valid.
      assert (Hj_n_lt_back5 : j_n < back5) by (subst j_n; lia).
      assert (Hj_n_take5 : take back5 ar5 !! j_n = Some a_j5).
      { rewrite lookup_take_lt; [exact Ha_j5|exact Hj_n_lt_back5]. }
      iDestruct (alloc_hist with "Htrace5") as "[Htrace5 #Hhist_ts5]".
      (* ts3 ⊆ ts5 since outer-back-read precedes the CAS-fail step. *)
      iDestruct (hist_trace_is_prefix with "Htrace5 Hhist_outer") as %Hpfx_outer5.
      iEval (rewrite mono_list_auth_lb_op) in "Hmatch●5".
      iDestruct "Hmatch●5" as "[Hmatch●5 #Hm5_snap]".
      iDestruct (big_sepL_lookup_acc _ _ j_n a_j5 Hj_n_take5 with "Hallocated5")
        as "[Hcell_jn5 Hclose_cell_jn5]".
      iDestruct "Hcell_jn5" as (ts_pre5 τ_jn5 v_jn5 ε_jn5)
        "(#Hcall_jn5 & %Hub_jn5 & #Hpre_jn5 & #Hslot_jn5 & Hcell_state_jn5)".
      iDestruct (ghost_map_elem_agree with "Hslot_jn5 Hslot_jn") as %->.
      iDestruct "Hvalid_trace5" as %Hvtr5.
      destruct Hvtr5 as [Hwf5 HI5].
      (* From Hcall_jn (LOAD-time hist) and Hcall_jn5 (CAS-fail-time hist),
         both witness Push Calls for τ_jn in ts5; per_tag_wellformed_bag forces
         their values to coincide. *)
      iDestruct (hist_trace_is_prefix with "Htrace5 Hcall_jn") as %Hpfx_jn.
      iDestruct (hist_trace_is_prefix with "Htrace5 Hcall_jn5") as %Hpfx_jn5.
      assert (Hin_jn : (τ_jn, Call Push v_jn) ∈ ts5).
      { destruct Hpfx_jn as [k Hk]. rewrite Hk. apply elem_of_app. left.
        apply elem_of_app. right. apply list_elem_of_singleton. reflexivity. }
      assert (Hin_jn5 : (τ_jn, Call Push v_jn5) ∈ ts5).
      { destruct Hpfx_jn5 as [k Hk]. rewrite Hk. apply elem_of_app. left.
        apply elem_of_app. right. apply list_elem_of_singleton. reflexivity. }
      assert (Hv_eq : v_jn5 = v_jn).
      { symmetry. eapply per_tag_wellformed_bag_call_push_unique; eauto. }
      iAssert (scan_witness ts3 tracer γ_slot γ_match j_n)%I as "#Hscan_jn_full".
      { rewrite /scan_witness.
        iExists ts5, τ_jn. iFrame "Hhist_ts5 Hslot_jn".
        iSplit; first by iPureIntro.
        destruct (M_ar5 !!! j_n) eqn:Hsj_n5.
        - (* NotStored: a_j5 = NONEV; cell has [(τ_jn, Ret #()) ∉ ts5]. Use Right. *)
          iDestruct "Hcell_state_jn5" as "[[_ %Hno_ret] _]".
          iRight. by iPureIntro.
        - (* StoredNotCAS: cell has [a_j5 = SOMEV v_jn5] = [SOMEV v_jn]
             contradicting Ha_j5_neq. *)
          iDestruct "Hcell_state_jn5" as "[_ [%Heq _]]".
          exfalso. apply Ha_j5_neq. rewrite Heq Hv_eq. reflexivity.
        - (* CASed: cell has [τ_jn ∈ m5.*1]. Use Left. *)
          iDestruct "Hcell_state_jn5" as "[_ %Hpure]".
          destruct Hpure as [_ Hin].
          iLeft. iExists m5. iFrame "Hm5_snap". by iPureIntro. }
      iDestruct ("Hclose_cell_jn5" with "[Hcell_state_jn5]") as "Hallocated5".
      { iExists ts_pre5, τ_jn, v_jn5, ε_jn5.
        iFrame "Hcall_jn5 Hpre_jn5 Hslot_jn5 Hcell_state_jn5". done. }
      iModIntro. iSplitR "HΦ Hop◯ Htkn_pop◯".
      { iNext.
        iExists sz, l_ar, l_back, ar5, back5, ts5, m5.
        iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
        iExists M_ar5, M_op5, M_tkn5, M_slot5.
        iFrame "Hmeta Htrace5 Har5 Hback5".
        iFrame "Hback●5 Har●5 Hop●5 Htkn●5 Hmatch●5 Hslot●5".
        iFrame "Hallocated5 Hm_nodup5 Hop5 Hreturned5".
        iSplit; first done.
        iSplit; first by iPureIntro.
        iSplit.
        { iPureIntro. split_and!; [exact Hd_tkn5|exact Hd_ar5|exact Hd_op5|exact Hd_len5|exact Hd_slot5]. }
        iSplit; first by iPureIntro.
        iPureIntro. exact Hunallocated5. }
      wp_pures.
      iApply ("IH_inner" $! (i_iter - 1)%Z with "[%] [Hscan] HΦ Hop◯ Htkn_pop◯");
        first lia.
      assert (Hseq_eq : Z.to_nat (range_z - (i_iter - 1))
                      = Z.to_nat (range_z - i_iter) + 1) by lia.
      rewrite Hseq_eq seq_app big_sepL_app big_sepL_singleton.
      replace (0 + Z.to_nat (range_z - i_iter))%nat with j_n by (subst j_n; lia).
      iFrame "Hscan Hscan_jn_full". }
  Qed.
  (* End LLM-generated code. *)
  (**********************************************************)
End proof.
