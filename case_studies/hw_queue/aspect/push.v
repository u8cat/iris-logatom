(* The enqueue: the slot reservation (FAA on back), the store, and the return. *)
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

  Lemma push_wrapper_spec γ tracer (q v_push : val) :
    val_is_unboxed (SOMEV v_push) →
    {{{ trace_inv tracer I_hwq ∗ is_hwq_trace γ q tracer }}}
      call_ret_wrapper tracer Push enqueue q v_push
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Hunboxed Φ) "[#Itrace #Ihwp] HΦ".
    wp_lam. wp_pures.

    (* Call *)
    awp_apply (trace_fresh_spec with "Itrace"); first exact (decode_encode_val (Call Push v_push)).
    iInv "Ihwp" as (sz l_ar l_back ar back ts m γ_back γ_ar γ_op γ_tkn γ_match γ_slot M_ar M_op M_tkn M_slot)
      ">(-> & Hvalid_trace & Hpstate & Hgstate & %Hdom & %Hpush_stored_inv & Hallocated & H)".
    iDestruct "Hpstate" as "(Htrace & Har & Hback)".
    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    iFrame "Htrace". iSplit.
    { iDestruct "Hvalid_trace" as "[%Hper_tag_wf %HI_queue_pre]". iPureIntro.
      intros τ Hfresh.
      destruct HI_queue_pre as (Hvalid_match & Hpop_empty_sound & Hocm & Hocum).
      split; last (exists m; rewrite /I_queue_pre; split_and!).
      - by apply per_tag_wellformed_bag_snoc_call_push.
      - by apply valid_match_snoc_call_push.
      - by apply per_tag_pop_empty_sound_snoc_call_push.
      - by apply order_correct_matched_snoc_call_push.
      - by apply order_correct_unmatched_snoc_call_push. }
    iSplit.
    { iIntros "[Hpstate _]". iMod "Hclose". iModIntro.
      iSplitR "HΦ"; last done.
      iNext. iExists sz, l_ar, l_back, ar. iFrame. done. }
    iIntros (τ) "[Htrace %Hfresh]". iMod "Hclose" as "_".
    iDestruct "H" as "(Hunallocated & Hm_nodup & Hop & #Hreturned)".
    iDestruct "Hgstate" as "(#Hmeta & Hback● & Har● & Hop● & Htkn● & Hmatch●)".
    iDestruct (alloc_hist with "Htrace") as "[Htrace #Hhist]".
    iEval (rewrite mono_nat_auth_lb_op) in "Hback●".
    iDestruct "Hback●" as "[Hback● #Hback◯]".
    (* This is an invariant in [allocated_ar_inv]. It has to be proved here. *)
    iAssert (own γ_back (●MN back) ∗ [∗ list] τ' ∈ (filter (is_ret_push∘snd) ts).*1, ∃ j, τ'↪[γ_tkn]□ j ∗ ⌜j<back⌝)%I
      with "[Hback●]" as "[Hback● #Hplaced_after_pre_push]".
    { remember ((filter (is_ret_push ∘ snd) ts).*1) as l eqn:Htmp. clear Htmp.
      iInduction l as [|τ' l] "IH".
      - iFrame "Hback●". iApply big_sepL_nil. done.
      - rewrite !big_sepL_cons.
        iDestruct "Hreturned" as "[(%j & %k & $ & Hk◯ & %) Hreturned]".
        iDestruct (own_valid_2 with "Hback● Hk◯") as %Hle%mono_nat_both_valid.
        iDestruct ("IH" with "Hreturned Hback●") as "[$ $]".
        iPureIntro. lia. }
    iMod (ghost_map_insert τ PushCalled with "Hop●") as "[Hop● Hop◯]".
    { apply not_elem_of_dom.
      destruct Hdom as (_ & _ & -> & _ & _).
      rewrite /events_of_trace.
      clear -Hfresh. set_solver. }
    (* Pre-allocate τ↦0 in M_tkn so that the FAA step can [ghost_map_update]
       to the FAA-returned index. The placeholder index 0 is irrelevant. *)
    iMod (ghost_map_insert τ 0 with "Htkn●") as "[Htkn● Htkn◯]".
    { apply not_elem_of_dom.
      destruct Hdom as (Hdom_tkn & _ & Hdom_op & _ & _).
      rewrite Hdom_tkn Hdom_op /events_of_trace.
      intros Hin. apply Hfresh.
      apply (elem_of_list_to_set (C := gset positive)) in Hin. exact Hin. }
    iModIntro. iSplitR "HΦ Hop◯ Htkn◯".
    { iNext.
      iExists sz, l_ar, l_back, ar.
      iFrame "Hmeta Har Hback Htrace Hunallocated Hback● Har● Htkn● Hop● Hmatch● Hm_nodup".
      iSplit; first done.
      iSplit.
      { (* Hvalid_trace *)
        iDestruct "Hvalid_trace" as "[%Hper_tag_wf %HI_queue_pre]". iPureIntro.
        destruct HI_queue_pre as (Hvalid_match & Hpop_empty_sound & Hocm & Hocum).
        rewrite /I_queue_pre. split_and!.
        - by eapply per_tag_wellformed_bag_snoc_call_push.
        - by apply valid_match_snoc_call_push.
        - by apply per_tag_pop_empty_sound_snoc_call_push.
        - by apply order_correct_matched_snoc_call_push.
        - by apply order_correct_unmatched_snoc_call_push. }
      iSplit.
      { (* Hdom *)
        iPureIntro.
        destruct Hdom as (Hdom_tkn_op & Hdom_ar & Hdom_op & Hdom_len & Hdom_slot).
        split_and!.
        - rewrite !dom_insert_L. clear -Hdom_tkn_op. set_solver.
        - done.
        - rewrite /events_of_trace fmap_app list_to_set_snoc_L.
          rewrite dom_insert_L Hdom_op. clear. set_solver.
        - exact Hdom_len.
        - exact Hdom_slot. }
      iSplit.
      { (* Hpush_stored_inv: τ freshly inserted as PushCalled (not stored). *)
        iPureIntro.
        intros τ' s_op' i' Hop_lookup_τ' Hstored Htkn_lookup_τ'.
        rewrite lookup_insert_Some in Hop_lookup_τ'.
        rewrite lookup_insert_Some in Htkn_lookup_τ'.
        destruct Hop_lookup_τ' as [[<- <-]|[Hτ_neq Hop_lookup_τ']].
        - destruct Hstored; discriminate.
        - destruct Htkn_lookup_τ' as [[<- _]|[_ Htkn_lookup_τ']]; first done.
          eapply Hpush_stored_inv; eauto. }
      iSplitL "Hallocated".
      { (* Hallocated: cell-preserve impl under snoc Call. *)
        iApply (big_sepL_impl with "Hallocated").
        iIntros "!#" (i a Hlookup) "Hinv".
        iDestruct "Hinv" as (ts_prefix τ₀ v₀ ɛ₀) "(#Hcall & %Hub₀ & $ & #Hslot_τ₀ & Hinv)".
        iFrame "Hcall Hslot_τ₀".
        iExists ɛ₀. iSplitR; first done.
        destruct (M_ar !!! i).
        - (* NotStored: preserve [(τ, Ret #()) ∉ ts]. *)
          iDestruct "Hinv" as "[[% %Hnotin] $]".
          iPureIntro. split; first done.
          intros HFalse. contradict Hnotin.
          rewrite elem_of_app list_elem_of_singleton in HFalse.
          destruct HFalse as [? | HFalse]; first done.
          exfalso. discriminate HFalse.
        - (* StoredNotCAS: cell content unchanged (γ_ar fragment + a = SOMEV + token). *)
          iExact "Hinv".
        - (* CASed: cell content unchanged. *)
          iExact "Hinv". }
      iSplitL "Hop".
      { (* Hop *)
        destruct Hdom as (_ & _ & Hdom & _ & _).
        rewrite /events_of_trace in Hdom.
        pose proof (Hfresh' := Hfresh).
        rewrite -(not_elem_of_list_to_set (C:=gset positive)) -Hdom in Hfresh'.
        iApply big_sepM_insert; first by apply not_elem_of_dom.
        iSplitR.
        - iPureIntro.
          simpl. exists v_push.
          rewrite filter_app filter_False_nil.
          + rewrite left_id_L filter_cons_True //.
          + apply Forall_forall.
            intros [τ' t] Hin%(list_elem_of_fmap_2 fst) <-.
            done.
        - iApply (big_sepM_impl with "Hop").
          iIntros "!#" (τ' s_op Hlookup) "%Htrace_inv !%".
          rewrite /trace_per_tag_inv.
          remember (filter (λ x, x.1 = τ') (ts++[(τ,Call Push v_push)])) as ts_τ' eqn:Heq.
          assert (τ ≠ τ').
          { intros <-. apply elem_of_dom_2 in Hlookup. done. }
          rewrite filter_app filter_cons_False // filter_nil right_id_L in Heq.
          rewrite Heq. apply Htrace_inv.  }
      { (* Hreturned *)
        iEval (rewrite filter_app filter_cons_False // filter_nil right_id_L).
        iExact "Hreturned". }}

      wp_pures. wp_lam. wp_pures.

    (* ====== Phase A: FAA on l_back to allocate a new slot. ====== *)
    wp_bind (FAA _ _).
    iInv "Ihwp" as (sz' l_ar' l_back' ar' back' ts' m' γ_back' γ_ar' γ_op' γ_tkn' γ_match' γ_slot' M_ar' M_op' M_tkn' M_slot')
      ">(%Hq_eq & Hvalid_trace & Hpstate & Hgstate & %Hdom' & %Hpush_stored_inv' & Hallocated & %Hunallocated & Hm_nodup & Hop & #Hreturned')".
    injection Hq_eq as Hsz_eq <- <-. apply Nat2Z.inj in Hsz_eq. subst sz'.
    iDestruct "Hpstate" as "(Htrace & Har & Hback)".
    iDestruct "Hgstate" as "(#Hmeta' & Hback● & Har● & Hop● & Htkn● & Hmatch● & Hslot●)".
    iDestruct (own_valid_2 with "Hmeta Hmeta'") as %Hagree%to_agree_op_inv_L.
    injection Hagree as <- <- <- <- <- <-. iClear "Hmeta'".
    wp_faa.
    (* Derive [back0 ≤ back'] from [Hback◯] (snapshot at trace_fresh time)
       against the current [Hback●]. Used to discharge [j < back'] in the new
       cell's [Hplaced_after_pre_push]-derived list. *)
    iDestruct (own_valid_2 with "Hback● Hback◯") as %Hb0_le%mono_nat_both_valid.
    iMod (ghost_map_update back' with "Htkn● Htkn◯") as "[Htkn● Htkn◯]".
    iMod (ghost_map_insert back' NotStored with "Har●") as "[Har● Har_back◯]".
    { apply not_elem_of_dom. destruct Hdom' as (_ & Hdom_ar & _ & _ & _).
      rewrite Hdom_ar elem_of_list_to_set elem_of_seq. lia. }
    iMod (own_update _ _ (●MN (Datatypes.S back')) with "Hback●") as "Hback●".
    { apply mono_nat_update. lia. }
    iEval (rewrite mono_nat_auth_lb_op) in "Hback●".
    iDestruct "Hback●" as "[Hback● #Hi◯]".
    iEval (rewrite -aspect_dfrac_3quarter_1quarter) in "Htkn◯".
    iDestruct "Htkn◯" as "[Htkn3◯ Htkn1◯]".
    iEval (rewrite Z.add_1_r -Nat2Z.inj_succ) in "Hback".
    (* Derive [M_op' !! τ = Some PushCalled] via [ghost_map_lookup] on Hop◯,
       and lift to [τ ∈ dom M_op'] for the dom proof and to
       [trace_per_tag_inv ts' τ PushCalled] for the cell's [(τ,Ret #()) ∉ ts']. *)
    iDestruct (ghost_map_lookup with "Hop● Hop◯") as %Hop_lookup.
    pose proof (Hop_in := Hop_lookup). apply elem_of_dom_2 in Hop_in.
    iDestruct (big_sepM_lookup _ _ τ PushCalled with "Hop") as %Htrace_τ;
      [exact Hop_lookup|].
    simpl in Htrace_τ. destruct Htrace_τ as [v_filt Hfilt].
    assert (Hτ_no_ret : (τ, Ret #()) ∉ ts').
    { intros Hin. assert (Hin_filt : (τ, Ret #()) ∈ filter (λ x, x.1 = τ) ts').
      { apply list_elem_of_filter. split; [reflexivity|exact Hin]. }
      rewrite Hfilt in Hin_filt. clear -Hin_filt. set_solver. }
    destruct Hdom' as (Hdom_tkn & Hdom_ar & Hdom_op & Hdom_len & Hdom_slot).
    (* Insert [back' ↦ τ] into [M_slot] and persist the fragment for Phase C. *)
    iMod (ghost_map_insert back' τ with "Hslot●") as "[Hslot● Hslot_τ◯]".
    { apply not_elem_of_dom. rewrite Hdom_slot elem_of_list_to_set elem_of_seq. lia. }
    iMod (ghost_map_elem_persist with "Hslot_τ◯") as "#Hslot_τ□".
    iModIntro. iSplitR "HΦ Hop◯ Htkn1◯ Hi◯ Har_back◯".
    { iNext.
      iExists sz, l_ar, l_back, ar', (Datatypes.S back'), ts', m'.
      iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
      iExists (<[back' := NotStored]> M_ar'), M_op', (<[τ := back']> M_tkn'),
              (<[back' := τ]> M_slot').
      iFrame "Hmeta Hvalid_trace Hback Htrace Hback● Hop● Hmatch● Hslot●".
      iFrame "Har Har● Htkn● Hm_nodup Hop Hreturned'".
      iSplit; first done.
      iSplit.
      { iPureIntro. split_and!.
        - rewrite !dom_insert_L Hdom_tkn.
          clear -Hop_in. set_solver.
        - rewrite dom_insert_L Hdom_ar seq_S /=.
          rewrite list_to_set_app_L /=. clear. set_solver.
        - exact Hdom_op.
        - exact Hdom_len.
        - rewrite dom_insert_L Hdom_slot seq_S /=.
          rewrite list_to_set_app_L /=. clear. set_solver. }
      iSplit.
      { (* Hpush_stored_inv: M_op' unchanged, M_tkn' updated [τ ↦ back'],
           M_ar' updated [back' ↦ NotStored], M_slot' updated [back' ↦ τ].
           For τ' = τ: M_op'[τ] = PushCalled (not stored), antecedent fails.
           For τ' ≠ τ: M_tkn lookup unchanged. From old Hpush_stored_inv',
           M_ar' !! i' ∈ {Some StoredNotCAS, Some CASed} ∧ M_slot' !! i' = Some τ',
           hence i' ≠ back' (since back' ∉ dom M_ar'); inserts at back' don't affect. *)
        iPureIntro.
        intros τ' s_op' i' Hop_lookup_τ' Hstored Htkn_lookup_τ'.
        destruct (decide (τ' = τ)) as [<-|Hτ_neq].
        - rewrite Hop_lookup in Hop_lookup_τ'.
          injection Hop_lookup_τ' as <-.
          destruct Hstored; discriminate.
        - rewrite lookup_insert_ne in Htkn_lookup_τ'; last done.
          assert (Hold : (M_ar' !! i' = Some StoredNotCAS ∨ M_ar' !! i' = Some CASed)
                       ∧ M_slot' !! i' = Some τ').
          { eapply Hpush_stored_inv'; eauto. }
          destruct Hold as [Hold_ar Hold_slot].
          assert (Hi_neq : i' ≠ back').
          { intros ->. assert (back' ∉ dom M_ar') as Hno_dom.
            { rewrite Hdom_ar elem_of_list_to_set elem_of_seq. lia. }
            apply not_elem_of_dom in Hno_dom.
            destruct Hold_ar as [Heq|Heq]; rewrite Hno_dom in Heq; discriminate. }
          split.
          + rewrite lookup_insert_ne; [exact Hold_ar|by intros <-].
          + rewrite lookup_insert_ne; [exact Hold_slot|by intros <-]. }
      iSplitL "Hallocated Htkn3◯".
      { destruct (decide (back' < length ar')) as [Hbk_in|Hbk_oob]; last first.
        { (* OOB: take (S back') ar' = take back' ar' = ar'; cells unchanged.
             Htkn3◯ is orphan but discarded by affine logic. *)
          assert (Htake_eq : take (Datatypes.S back') ar' = take back' ar').
          { rewrite (take_ge ar' back'); [|lia]. rewrite take_ge //. lia. }
          rewrite Htake_eq.
          iApply (big_sepL_impl with "Hallocated").
          iIntros "!#" (i a Hlk_a) "Hcell".
          assert (Hi_lt_bk : i < back').
          { apply lookup_lt_Some in Hlk_a. rewrite length_take in Hlk_a. lia. }
          rewrite lookup_total_insert_ne; last lia.
          iExact "Hcell". }
        assert (Hbk_NONEV : ar' !! back' = Some NONEV).
        { destruct (drop back' ar') as [|x rest] eqn:Hdrop.
          - exfalso. apply (f_equal length) in Hdrop.
            rewrite length_drop in Hdrop. simpl in Hdrop. lia.
          - rewrite Forall_cons in Hunallocated. destruct Hunallocated as [-> _].
            assert (drop back' ar' !! 0 = ar' !! back') as <-.
            { rewrite lookup_drop Nat.add_0_r. reflexivity. }
            rewrite Hdrop /=. reflexivity. }
        rewrite (take_S_r _ _ NONEV) //.
        rewrite big_sepL_app big_sepL_singleton.
        iSplitL "Hallocated".
        - (* Old big_sepL: M_ar !!! i unchanged for i < back'. *)
          iApply (big_sepL_impl with "Hallocated").
          iIntros "!#" (i x Hlk_take) "Hcell".
          assert (Hi_lt : i < back').
          { apply lookup_lt_Some in Hlk_take.
            rewrite length_take in Hlk_take. lia. }
          rewrite lookup_total_insert_ne; last lia.
          iExact "Hcell".
        - (* New cell at back'. *)
          rewrite length_take_le; last lia.
          rewrite Nat.add_0_r lookup_total_insert_eq.
          iExists ts, τ, v_push, _.
          iSplit; first iApply "Hhist".
          iSplit; first by iPureIntro.
          iSplit.
          { iApply (big_sepL_impl with "Hplaced_after_pre_push").
            iIntros "!#" (k τ' Hlk) "(%j & H1 & %Hj)".
            iExists j. iFrame "H1". iPureIntro. lia. }
          iSplit; first iExact "Hslot_τ□".
          iSplit; last first.
          { iEval (rewrite -aspect_dfrac_3quarter_eq) in "Htkn3◯".
            iExact "Htkn3◯". }
          iPureIntro. split; [reflexivity|exact Hτ_no_ret]. }
      (* Forall NONEV (drop (S back') ar'): drop is monotone in n. *)
      iPureIntro.
      replace (Datatypes.S back') with (back' + 1) by lia.
      rewrite -(drop_drop ar' 1 back'). by apply (Forall_drop). }
    (* ====== Phase B: bounds check (back' < sz). ====== *)
    wp_pures.
    case_bool_decide as Hbk_lt; wp_pures; last first.
    { (* back' >= sz: diverge *)
      wp_apply wp_diverge. }
    (* back' < sz, so back' < length ar' = Z.to_nat sz. *)
    (* ====== Phase C: store SOMEV v_push at l_ar +ₗ back'. ====== *)
    wp_bind (_ <- _)%E.
    iInv "Ihwp" as (sz3 l_ar3 l_back3 ar3 back3 ts3 m3 γ_back3 γ_ar3 γ_op3 γ_tkn3 γ_match3 γ_slot3 M_ar3 M_op3 M_tkn3 M_slot3)
      ">(%Hq_eq3 & Hvalid_trace3 & Hpstate3 & Hgstate3 & %Hdom3 & %Hpush_stored_inv3 & Hallocated3 & %Hunallocated3 & Hm_nodup3 & Hop3 & #Hreturned3)".
    injection Hq_eq3 as Hsz_eq <- <-. apply Nat2Z.inj in Hsz_eq. subst sz3.
    iDestruct "Hpstate3" as "(Htrace3 & Har3 & Hback3)".
    iDestruct "Hgstate3" as "(#Hmeta3 & Hback●3 & Har●3 & Hop●3 & Htkn●3 & Hmatch●3 & Hslot●3)".
    iDestruct (own_valid_2 with "Hmeta Hmeta3") as %Hagree3%to_agree_op_inv_L.
    injection Hagree3 as <- <- <- <- <- <-. iClear "Hmeta3".
    (* Derive [back' < length ar3] from [Hbk_lt] and [Hdom3.length]; and [back' < back3]
       from [Hi◯] vs [Hback●3]. *)
    destruct Hdom3 as (Hdom_tkn3 & Hdom_ar3 & Hdom_op3 & Hdom_len3 & Hdom_slot3).
    assert (Hbk_in_ar : back' < length ar3).
    { rewrite Hdom_len3. lia. }
    iDestruct (own_valid_2 with "Hback●3 Hi◯") as %Hback3_lb%mono_nat_both_valid.
    assert (Hbk_lt_back3 : back' < back3) by lia.
    apply lookup_lt_is_Some in Hbk_in_ar as [a Hbk_eq].
    (* Manually decompose [take back3 ar3] at back' via take_drop_middle. *)
    assert (Hbk_take : take back3 ar3 !! back' = Some a).
    { rewrite lookup_take_lt; last lia. exact Hbk_eq. }
    pose proof (take_drop_middle _ _ _ Hbk_take) as Hsplit.
    assert (Hlen_inner : length (take back' (take back3 ar3)) = back').
    { rewrite take_take (Nat.min_l back' back3); [|lia].
      rewrite length_take_le; lia. }
    iEval (rewrite -Hsplit big_sepL_app big_sepL_cons Hlen_inner Nat.add_0_r) in "Hallocated3".
    iDestruct "Hallocated3" as "(Hpre & Hcell & Hpost)".
    iDestruct "Hcell" as (ts_pre τ_cell v_cell ε_cell) "(#Hcall_cell & %Hub_cell & #Hpre_cell & #Hslot_τ_cell□ & Hcell_state)".
    (* Identify [τ_cell = τ] via the persistent slot witness. *)
    iDestruct (ghost_map_elem_agree with "Hslot_τ_cell□ Hslot_τ□") as %->.
    (* State discrimination on [M_ar3 !!! back']. From [Har_back◯ : back' ↪[γ_ar] NotStored],
       agreement with the auth gives [M_ar3 !! back' = Some NotStored], hence
       [M_ar3 !!! back' = NotStored]. *)
    iDestruct (ghost_map_lookup with "Har●3 Har_back◯") as %Har_lookup.
    assert (Hstate : M_ar3 !!! back' = NotStored).
    { rewrite lookup_total_alt Har_lookup //. }
    rewrite Hstate.
    iDestruct "Hcell_state" as "[[%Ha %Hno_ret_cell] Htkn_cell◯]".
    subst a.
    (* Perform the array store. *)
    wp_apply (wp_store_offset _ _ _ back' _ (SOMEV v_push) with "Har3") as "Har3".
    { rewrite Hbk_eq. eauto. }
    iMod (ghost_map_update StoredNotCAS with "Har●3 Har_back◯") as "[Har●3 Har_back◯]".
    (* Updating M_op[τ] := PushStored refines Phase D's state-determination via
       Hpush_stored_inv. *)
    iDestruct (ghost_map_lookup with "Hop●3 Hop◯") as %Hop3_lookup.
    iMod (ghost_map_update PushStored with "Hop●3 Hop◯") as "[Hop●3 Hop◯]".
    iDestruct (ghost_map_lookup with "Htkn●3 Htkn1◯") as %Htkn3_lookup.
    (* Re-pack cell into StoredNotCAS arm: hand off [Har_back◯] (now StoredNotCAS)
       to the cell, where pop extracts it at CAS commit. *)
    iAssert (allocated_ar_inv tracer γ_ar γ_tkn γ_slot ts3 m3 back' (SOMEV v_push) StoredNotCAS)%I
      with "[Htkn_cell◯ Har_back◯]" as "Hcell_new".
    { iExists ts, τ, v_push, ε_cell.
      iSplit; first iApply "Hhist".
      iSplit; first by iPureIntro.
      iSplit.
      { iApply (big_sepL_impl with "Hplaced_after_pre_push").
        iIntros "!#" (k τ' Hlk) "(%j & H1 & %Hj)".
        iExists j. iFrame "H1". iPureIntro. lia. }
      iFrame "Hslot_τ□".
      iFrame "Har_back◯".
      iSplit; [iPureIntro; reflexivity|iExact "Htkn_cell◯"]. }
    iDestruct (ghost_map_lookup with "Hslot●3 Hslot_τ□") as %Hslot_lookup_τ.
    (* Close the inv with updated M_ar/M_op and the new array. *)
    iModIntro. iSplitR "HΦ Hop◯ Htkn1◯ Hi◯".
    { iNext.
      iExists sz, l_ar, l_back, (<[back' := SOMEV v_push]> ar3), back3, ts3, m3.
      iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
      iExists (<[back' := StoredNotCAS]> M_ar3), (<[τ := PushStored]> M_op3),
              M_tkn3, M_slot3.
      iFrame "Hmeta Hback3 Htrace3 Hback●3 Hop●3 Hmatch●3 Hslot●3".
      iFrame "Har3 Har●3 Htkn●3 Hm_nodup3 Hreturned3".
      iSplit; first done.
      iSplit.
      { iDestruct "Hvalid_trace3" as "[%Hwf3 %HI3]".
        iPureIntro. exact (conj Hwf3 HI3). }
      iSplit.
      { iPureIntro. split_and!; [|  |  | |exact Hdom_slot3].
        - rewrite dom_insert_L. apply elem_of_dom_2 in Hop3_lookup as Hop3_in.
          rewrite Hdom_tkn3. clear -Hop3_in. set_solver.
        - rewrite dom_insert_L Hdom_ar3.
          assert (Hbk_in_seq : (back' : nat) ∈ (list_to_set (seq 0 back3) : gset nat)).
          { rewrite elem_of_list_to_set elem_of_seq. lia. }
          clear -Hbk_in_seq. set_solver.
        - rewrite dom_insert_L. apply elem_of_dom_2 in Hop3_lookup as Hop3_in.
          rewrite Hdom_op3 in Hop3_in. rewrite Hdom_op3.
          clear -Hop3_in. set_solver.
        - rewrite length_insert. exact Hdom_len3. }
      iSplit.
      { (* Hpush_stored_inv: τ now PushStored at back'; M_ar[back'] = StoredNotCAS;
           M_slot[back'] = τ (from Phase A). ✓ *)
        iPureIntro.
        intros τ' s_op' i' Hop_lookup_τ' Hstored Htkn_lookup_τ'.
        (* Need M_slot3[back'] = Some τ. Derive from old Hpush_stored_inv3 using
           e.g., the existing fact that M_slot tracks Phase-A insertions. We
           recover it by pulling from Hslot_τ□ which is persistent. *)
        destruct (decide (τ' = τ)) as [<-|Hτ_neq].
        - rewrite Htkn3_lookup in Htkn_lookup_τ'.
          injection Htkn_lookup_τ' as <-.
          split; first by left; rewrite lookup_insert_eq.
          exact Hslot_lookup_τ.
        - rewrite lookup_insert_ne in Hop_lookup_τ'; last done.
          destruct (decide (i' = back')) as [->|Hi_neq].
          + assert (Hold : (M_ar3 !! back' = Some StoredNotCAS ∨ M_ar3 !! back' = Some CASed)
                         ∧ M_slot3 !! back' = Some τ').
            { eapply Hpush_stored_inv3; eauto. }
            destruct Hold as [Hold_ar Hold_slot].
            split; [left; by rewrite lookup_insert_eq|exact Hold_slot].
          + rewrite lookup_insert_ne; last done.
            eapply Hpush_stored_inv3; eauto. }
      iSplitL "Hpre Hcell_new Hpost".
      { (* Build the new big_sepL via take_insert_lt and the same decomposition. *)
        rewrite (take_insert_lt _ back3 back'); last lia.
        rewrite (insert_take_drop _ back' (SOMEV v_push));
          last by rewrite length_take; lia.
        rewrite big_sepL_app big_sepL_cons.
        rewrite Hlen_inner Nat.add_0_r.
        iSplitL "Hpre".
        { iApply (big_sepL_impl with "Hpre").
          iIntros "!#" (i x Hlk_x) "Hcell".
          assert (Hi_lt : i < back').
          { apply lookup_lt_Some in Hlk_x. rewrite Hlen_inner in Hlk_x. lia. }
          rewrite lookup_total_insert_ne; last lia. iExact "Hcell". }
        iSplitL "Hcell_new".
        { rewrite lookup_total_insert_eq. iExact "Hcell_new". }
        iApply (big_sepL_impl with "Hpost").
        iIntros "!#" (i x Hlk_x) "Hcell".
        rewrite lookup_total_insert_ne; last lia. iExact "Hcell". }
      iSplit.
      { iPureIntro. rewrite drop_insert_lt; [exact Hunallocated3|lia]. }
      (* Hop big_sepM: M_op[τ] := PushStored. Trace shape unchanged for τ
         (PushStored has same trace shape as PushCalled). *)
      rewrite (big_sepM_delete _ M_op3 τ PushCalled); [|exact Hop3_lookup].
      iDestruct "Hop3" as "[%Hτ_inv Hop3_rest]".
      rewrite (big_sepM_delete _ (<[τ := PushStored]> M_op3) τ PushStored);
        [|by rewrite lookup_insert_eq].
      iSplit.
      { iPureIntro. simpl. simpl in Hτ_inv. exact Hτ_inv. }
      rewrite delete_insert_eq. iApply "Hop3_rest". }
    (* ====== Phase D: emit Ret #() event. ====== *)
    wp_pures.
    awp_apply (trace_emit_spec _ _ (Ret #()) with "Itrace"); first reflexivity.
    iInv "Ihwp" as (sz4 l_ar4 l_back4 ar4 back4 ts4 m4 γ_back4 γ_ar4 γ_op4 γ_tkn4 γ_match4 γ_slot4 M_ar4 M_op4 M_tkn4 M_slot4)
      ">(%Hq_eq4 & Hvalid_trace4 & Hpstate4 & Hgstate4 & %Hdom4 & %Hpush_stored_inv4 & Hallocated4 & %Hunallocated4 & Hm_nodup4 & Hop4 & #Hreturned4)".
    injection Hq_eq4 as Hsz_eq <- <-. apply Nat2Z.inj in Hsz_eq. subst sz4.
    iDestruct "Hpstate4" as "(Htrace4 & Har4 & Hback4)".
    iDestruct "Hgstate4" as "(#Hmeta4 & Hback●4 & Har●4 & Hop●4 & Htkn●4 & Hmatch●4 & Hslot●4)".
    iDestruct (own_valid_2 with "Hmeta Hmeta4") as %Hagree4%to_agree_op_inv_L.
    injection Hagree4 as <- <- <- <- <- <-. iClear "Hmeta4".
    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose4".
    iDestruct (ghost_map_lookup with "Hop●4 Hop◯") as %Hop4_lookup.
    iDestruct (ghost_map_lookup with "Htkn●4 Htkn1◯") as %Htkn4_lookup.
    (* From Hpush_stored_inv4 + M_op4[τ] = PushStored + M_tkn4[τ] = back':
       M_ar4 !! back' ∈ {Some StoredNotCAS, Some CASed}, so M_ar4 !!! back' ≠ NotStored. *)
    assert (Hbk_state4 : M_ar4 !! back' = Some StoredNotCAS ∨ M_ar4 !! back' = Some CASed).
    { eapply Hpush_stored_inv4; [exact Hop4_lookup|left; reflexivity|exact Htkn4_lookup]. }
    assert (Hbk_state4_neq : M_ar4 !!! back' ≠ NotStored).
    { rewrite lookup_total_alt. destruct Hbk_state4 as [-> | ->]; done. }
    iDestruct (big_sepM_lookup _ _ τ PushStored with "Hop4") as %Htrace4_τ;
      [exact Hop4_lookup|].
    destruct Htrace4_τ as [v_filt4 Hfilt4].
    iDestruct (hist_trace_is_prefix with "Htrace4 Hhist") as %Hpfx_us4.
    assert (Hus_in_ts4 : (τ, Call Push v_push) ∈ ts4).
    { destruct Hpfx_us4 as [k Hk]. rewrite Hk. apply elem_of_app. left.
      apply elem_of_app. right. apply list_elem_of_singleton. reflexivity. }
    assert (Hv_filt4_eq : v_filt4 = v_push).
    { assert (Hus_in_filt4 : (τ, Call Push v_push) ∈ filter (λ x, x.1 = τ) ts4).
      { apply list_elem_of_filter. split; [reflexivity|exact Hus_in_ts4]. }
      rewrite Hfilt4 in Hus_in_filt4.
      apply list_elem_of_singleton in Hus_in_filt4. by simplify_eq. }
    subst v_filt4.
    iFrame "Htrace4". iSplit.
    { iDestruct "Hvalid_trace4" as "[%Hwf4 %HI4]". iPureIntro.
      destruct HI4 as (Hvm & Hps & Hocm & Hocu).
      split; last (exists m4; rewrite /I_queue_pre; split_and!).
      - by eapply per_tag_wellformed_bag_snoc_ret_push.
      - by eapply valid_match_snoc_ret_push.
      - by eapply per_tag_pop_empty_sound_snoc_ret_push.
      - by eapply order_correct_matched_snoc_ret_push.
      - by eapply order_correct_unmatched_snoc_ret_push. }
    iSplit.
    { iIntros "[Htrace4 _]". iMod "Hclose4" as "_". iModIntro.
      iSplitR "HΦ Hop◯ Htkn1◯".
      - iNext.
        iExists sz, l_ar, l_back, ar4, back4, ts4, m4.
        iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
        iExists M_ar4, M_op4, M_tkn4, M_slot4.
        iFrame "Hmeta Htrace4 Har4 Hback4".
        iFrame "Hback●4 Har●4 Hop●4 Htkn●4 Hmatch●4 Hslot●4".
        iFrame "Hallocated4 Hm_nodup4 Hop4 Hreturned4 Hvalid_trace4".
        iSplit; first done.
        iSplit.
        { iPureIntro. destruct Hdom4 as (?&?&?&?&?). split_and!; done. }
        iSplit; first by iPureIntro.
        iPureIntro. exact Hunallocated4.
      - iFrame. }
    iIntros "Htrace4". iMod "Hclose4" as "_".
    iMod (ghost_map_update PushReturned with "Hop●4 Hop◯") as "[Hop●4 Hop◯]".
    iMod (ghost_map_elem_persist with "Htkn1◯") as "#Htkn□".
    iModIntro. iSplitR "HΦ".
    { iNext.
      iExists sz, l_ar, l_back, ar4, back4, (ts4 ++ [(τ, Ret #())]), m4.
      iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot.
      iExists M_ar4, (<[τ := PushReturned]> M_op4), M_tkn4, M_slot4.
      iFrame "Hmeta Hback4 Htrace4 Hback●4 Hop●4 Hmatch●4 Hslot●4".
      iFrame "Har4 Har●4 Htkn●4 Hm_nodup4".
      iSplit; first done.
      iSplit.
      { iDestruct "Hvalid_trace4" as "[%Hwf4 %HI4]". iPureIntro.
        destruct HI4 as (Hvm & Hps & Hocm & Hocu).
        rewrite /I_queue_pre. split_and!.
        - by eapply per_tag_wellformed_bag_snoc_ret_push.
        - by eapply valid_match_snoc_ret_push.
        - by eapply per_tag_pop_empty_sound_snoc_ret_push.
        - by eapply order_correct_matched_snoc_ret_push.
        - by eapply order_correct_unmatched_snoc_ret_push. }
      iSplit.
      { iPureIntro. destruct Hdom4 as (Hd_tkn4 & Hd_ar4 & Hd_op4 & Hd_len4 & Hd_slot4).
        apply elem_of_dom_2 in Hop4_lookup as Hop4_in.
        split_and!.
        - rewrite dom_insert_L Hd_tkn4. clear -Hop4_in. set_solver.
        - exact Hd_ar4.
        - rewrite dom_insert_L /events_of_trace fmap_app list_to_set_app_L.
          rewrite Hd_op4. clear -Hop4_in. set_solver.
        - exact Hd_len4.
        - exact Hd_slot4. }
      iSplit.
      { (* Hpush_stored_inv: M_op[τ] := PushReturned, both PushStored and PushReturned
           are stored states; M_ar/M_tkn unchanged. *)
        iPureIntro.
        intros τ' s_op' i' Hop_lookup_τ' Hstored Htkn_lookup_τ'.
        destruct (decide (τ' = τ)) as [Heq_τ|Hτ_neq].
        - subst τ'.
          rewrite lookup_insert_eq in Hop_lookup_τ'. injection Hop_lookup_τ' as <-.
          rewrite Htkn4_lookup in Htkn_lookup_τ'. injection Htkn_lookup_τ' as <-.
          eapply Hpush_stored_inv4; [exact Hop4_lookup|left; reflexivity|exact Htkn4_lookup].
        - rewrite lookup_insert_ne in Hop_lookup_τ'; last done.
          eapply Hpush_stored_inv4; eauto. }
      iSplitL "Hallocated4".
      { iApply (big_sepL_impl with "Hallocated4").
        iIntros "!#" (i a Hlk_a) "Hcell".
        iDestruct "Hcell" as (ts_pre' τ_cell' v_cell' ε_cell')
          "(#Hcall_cell' & %Hub_cell' & #Hpre_cell' & #Hslot_cell' & Hcell_state')".
        iExists ts_pre', τ_cell', v_cell', ε_cell'.
        iFrame "Hcall_cell' Hpre_cell' Hslot_cell'".
        iSplit; first done.
        destruct (M_ar4 !!! i) eqn:Hsi; [|iExact "Hcell_state'"|iExact "Hcell_state'"].
        iDestruct "Hcell_state'" as "[%Ha_pure Htkn_cell'◯]".
        destruct Ha_pure as [Ha Hno_ret].
        assert (Hi_neq_bk : i ≠ back').
        { intros ->. by apply Hbk_state4_neq. }
        destruct (decide (τ_cell' = τ)) as [Heq|Hτ_neq].
        - subst τ_cell'.
          iDestruct (ghost_map_elem_agree with "Htkn_cell'◯ Htkn□") as %Heq_i.
          exfalso. exact (Hi_neq_bk Heq_i).
        - iFrame "Htkn_cell'◯".
          iPureIntro. split; [exact Ha|].
          intros Hin. apply elem_of_app in Hin as [Hin|Hin].
          + exact (Hno_ret Hin).
          + apply list_elem_of_singleton in Hin.
            by simplify_eq. }
      iSplit.
      { iPureIntro. exact Hunallocated4. }
      iSplitL "Hop4".
      { rewrite (big_sepM_delete _ _ τ PushStored); [|exact Hop4_lookup].
        iDestruct "Hop4" as "[_ Hop4_rest]".
        rewrite (big_sepM_delete _ (<[τ := PushReturned]> M_op4) τ PushReturned);
          [|by rewrite lookup_insert_eq].
        iSplitR.
        - iPureIntro. simpl. exists v_push.
          rewrite filter_app Hfilt4 filter_cons_True //=.
        - rewrite delete_insert_eq.
          iApply (big_sepM_impl with "Hop4_rest").
          iIntros "!#" (τ' s_op' Hlk') "%Htrace_τ' !%".
          rewrite lookup_delete_Some in Hlk'. destruct Hlk' as [Hτ_neq _].
          rewrite /trace_per_tag_inv in Htrace_τ' |- *.
          rewrite filter_app filter_cons_False; last (simpl; congruence).
          rewrite filter_nil app_nil_r. exact Htrace_τ'. }
      rewrite filter_app filter_cons_True; last done.
      rewrite filter_nil fmap_app /=.
      rewrite big_sepL_app big_sepL_singleton.
      iFrame "Hreturned4".
      iExists back', (Datatypes.S back'). iFrame "Htkn□ Hi◯".
      iPureIntro. lia. }
    wp_pures. by iApply "HΦ".
  Qed.
  (* End LLM-generated code. *)
  (**********************************************************)
End proof.
