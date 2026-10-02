(* The push: insertion into the pool of its thread (the point), timestamping, and the return. *)

From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Import bag stack.
From iris_logatom.pure_logic Require Import encodable linear.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import agree mono_list mono_nat.
From iris.base_logic Require Import invariants ghost_map ghost_var.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy lang notation tactics unwrap proofmode.
From iris.heap_lang.lib Require Import array.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import thread_id.
From case_studies.ts_stack Require Import impl.
From case_studies.ts_stack.aspect Require Import pure defs resources steps timestamp unlink.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  Lemma new_node_spec (v : val) (b : bool) :
    {{{ True }}}
      new_node v #b
    {{{ (x : loc), RET #x; x ↦ v ∗ (x +ₗ 1) ↦ timestamp_val None ∗ (x +ₗ 2) ↦ #x ∗ (x +ₗ 3) ↦ #b }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_pures.
    wp_apply (wp_allocN with "[//]") as (x) "[Hx _]"; first done.
    iEval (rewrite /= array_cons array_cons array_cons array_singleton) in "Hx".
    iDestruct "Hx" as "(H0 & H1 & H2 & H3)".
    iEval (rewrite !Loc.add_assoc /=) in "H2 H3".
    wp_pures. wp_store. wp_store. wp_store. wp_store.
    iModIntro. iApply "HΦ". iFrame.
  Qed.

  Lemma push_wrapper_spec γ tracer (q v : val) :
    {{{ trace_inv tracer I_ts ∗ is_ts tracer γ q }}}
      call_ret_wrapper tracer Push tsstack_push q v
    {{{ w, RET w; True }}}.
  Proof.
    iIntros (Φ) "[#Itrace #His] HΦ".
    iDestruct "His" as (γs pools ctr tpl n sents) "([-> [%Hn %Hlen]] & #Hγ & #Htp & #Hinv)".
    wp_lam. wp_pures.
    (* the call *)
    awp_apply (trace_fresh_spec with "Itrace"); first exact (decode_encode_val (Call Push v)).
    iInv "Hinv" as (σ) "(>[%HI %Hsent] & >Htr & >Hrest)".
    rewrite /atomic_acc /=. iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    iFrame "Htr". iSplit.
    { iPureIntro. intros τ Hfresh. exact (tss_inv_I_ts n _ (tss_inv_call_push n σ τ v HI Hfresh)). }
    iSplit.
    { iIntros "[Htr _]". iMod "Hclose" as "_". iModIntro. iSplitR "HΦ"; last done.
      iNext. iExists σ. by iFrame. }
    iIntros (τ) "[Htr %Hfresh]". iMod "Hclose" as "_".
    iMod (rest_call _ _ _ σ τ (Call Push v) PushCalled with "Hrest") as "(Hrest & Hτ & #HτK)";
      [done|apply HI|apply HI|].
    iDestruct (alloc_hist with "Htr") as "[Htr #Hhist]".
    iModIntro. iSplitR "HΦ Hτ".
    { iNext. iExists (ev_call σ τ (Call Push v) PushCalled). iFrame. iPureIntro.
      split; [by apply tss_inv_call_push|done]. }
    wp_pures. wp_lam. wp_pures.
    (* claim a thread ID: become the owner of its pool *)
    wp_apply (claim_tid_spec with "Htp") as (j) "Htid".
    iDestruct (is_threadpool_tid_bounded with "Htp Htid") as %Hj.
    iApply fupd_wp.
    iInv "Hinv" as (σ1) "(>[%HI1 %Hsent1] & >Htr & >Hrest)" "Hclose".
    iMod (owner_acquire with "Htid Hrest") as "(Hrest & Hmine & #Hview1 & #Hlast1)"; [done|done|].
    iMod ("Hclose" with "[Htr Hrest]") as "_".
    { iNext. iExists (ev_busy σ1 j true). iFrame. iPureIntro. split; [|done].
      apply tss_inv_busy; [done|done|done]. }
    iModIntro. rewrite Hsent1.
    set (k := length (pool_list σ1 j)).
    assert (Hk1 : 1 ≤ k).
    { rewrite /k /pool_list /pool_list_l. destruct (ti_len _ _ HI1) as (Hls1 & _).
      destruct (lookup_lt_is_Some_2 (s_sent σ1) j) as [s1 ->]; [lia|]. simpl. lia. }
    wp_pures.
    (* sppool_insert: a fresh node *)
    wp_lam. wp_pures.
    wp_apply (new_node_spec v false) as (x) "(Hx0 & Hx1 & Hx2 & Hx3)"; first done.
    wp_pures.
    (* read the top *)
    wp_bind (! _)%E.
    iInv "Hinv" as (σr) "(>[%HIr %Hsentr] & >Htr & >Hrest)" "Hclose".
    iDestruct (owner_agree with "Hmine Hrest") as %[Hbr Hkr]; [done|done|].
    iDestruct (rest_view_get with "Hrest") as "[Hrest #Hviewr]".
    destruct (ti_len _ _ HIr) as (_ & Hltr & _).
    destruct (lookup_lt_is_Some_2 (s_top σr) j) as [t Ht]; first lia.
    iDestruct "Hrest" as "(Hm & Hp & Hc & Hctr & HTS & HTSf & HK & HKf & Hos & Htops & Hrest)".
    iDestruct (big_sepL_lookup_acc with "Htops") as "[Htop Htops]"; first done.
    wp_load.
    iDestruct ("Htops" with "Htop") as "Htops".
    iMod ("Hclose" with "[Htr Hm Hp Hc Hctr HTS HTSf HK HKf Hos Htops Hrest]") as "_".
    { iNext. iExists σr. iFrame. done. }
    iModIntro.
    destruct (read_top n σr j t HIr Hj Ht) as (it & Hit & Habove).
    wp_store.
    (* publish: the point of the push *)
    wp_bind (_ <- _)%E.
    iInv "Hinv" as (σp) "(>[%HIp %Hsentp] & >Htr & >Hrest)" "Hclose".
    iDestruct (owner_agree with "Hmine Hrest") as %[Hbp Hkp]; [done|done|].
    iDestruct (fresh_node with "Hx2 Hrest") as %Hxfresh.
    iDestruct (rest_view_valid with "Hrest Hviewr") as %[Hprp Hmrp].
    iDestruct (rest_view_valid with "Hrest Hview1") as %[Hp1p Hm1p].
    iDestruct (rest_os_lookup with "Hrest Hτ") as %Hosp.
    iDestruct (hist_trace_is_prefix with "Htr Hhist") as %Hhp.
    assert (Hcall : (τ, Call Push v) ∈ s_ts σp).
    { eapply elem_of_prefix; [|exact Hhp]. rewrite elem_of_app list_elem_of_singleton. by right. }
    assert (Hpl : pool_list σp j = pool_list σr j).
    { apply (pool_list_frozen σp (s_sent σr) (s_pts σr) j); [congruence|done|].
      change (pool_list_l (s_sent σr) (s_pts σr) j) with (pool_list σr j). lia. }
    assert (Hpl1 : pool_list σp j = pool_list σ1 j).
    { apply (pool_list_frozen σp (s_sent σ1) (s_pts σ1) j); [congruence|done|].
      change (pool_list_l (s_sent σ1) (s_pts σ1) j) with (pool_list σ1 j). lia. }
    iAssert (⌜∀ z τz, last (pool_list σp j) = Some z → tag_of σp z = Some τz → is_Some (s_TS σp !! τz)⌝)%I
      as %Hlastp.
    { iIntros (z τz Hz Hτz).
      assert (Hz1 : last (pool_list_l sents (s_pts σ1) j) = Some z).
      { rewrite -Hsent1 -/(pool_list σ1 j) -Hpl1. done. }
      assert (Hτz1 : tag_of_l (s_pts σ1) z = Some τz).
      { apply (tag_of_old n σ1 σp j); [done|done|congruence|done| |done].
        apply last_Some_elem_of. by rewrite -Hpl1. }
      iDestruct ("Hlast1" $! z τz with "[]") as (tz) "Htz"; first (iPureIntro; done).
      iDestruct (rest_TS_lookup with "Hrest Htz") as %?. by eauto. }
    iDestruct (rest_publish with "Hrest Hτ Hmine") as (t') "[Htop Hpub]"; [done|done|done|done|].
    wp_store.
    iMod ("Hpub" with "Htop Hx0 Hx1 Hx2 Hx3") as "(Hrest & Hτ & Hmine & #HpP & #HcP)".
    destruct (publish_facts n σp τ x j t HIp Hj Hosp Hxfresh) as (HnodeP & HPTP & HtagP & HplP).
    iMod ("Hclose" with "[Htr Hrest]") as "_".
    { iNext. iExists (ev_publish σp τ x j t). iFrame. iPureIntro. split; [|done].
      apply (tss_inv_publish n σp τ x j t it); try done.
      - by rewrite Hpl.
      - intros i z Hi Hz. rewrite Hpl in Hz. destruct (Habove i z Hi Hz) as [Hzt _].
        eapply (taken_snapshot σp); [exact Hprp|exact Hmrp|].
        rewrite /taken /takenb Hsentr in Hzt. by rewrite Hsentp. }
    iModIntro.
    set (pP := s_pts σp ++ [(τ, s_c σp, Some (x, j))]).
    assert (HplP' : pool_list_l sents pP j = pool_list σp j ++ [x]).
    { rewrite -Hsentp. exact HplP. }
    assert (HxP : pool_list_l sents pP j !! k = Some x).
    { rewrite HplP'. apply list_lookup_middle. lia. }
    assert (HlenP : length (pool_list_l sents pP j) = 1 + k).
    { rewrite HplP' length_app /=. lia. }
    (* the pool of j as seen from later states *)
    assert (Hlater : ∀ σ', s_sent σ' = sents → pP `prefix_of` s_pts σ' → length (pool_list σ' j) = 1 + k →
              pool_list σ' j = pool_list_l sents pP j).
    { intros σ' Hs' Hp' Hl'. apply pool_list_frozen; [done|done|lia]. }
    wp_pures.
    (* read the next field of the new node *)
    wp_bind (! _)%E.
    iInv "Hinv" as (σn) "(>[%HIn %Hsentn] & >Htr & >Hrest)" "Hclose".
    iDestruct (owner_agree with "Hmine Hrest") as %[Hbn Hkn]; [done|done|].
    iDestruct (rest_pts_valid with "Hrest HpP") as %HpPn.
    pose proof (Hlater σn Hsentn HpPn Hkn) as Hpln.
    assert (Hxn : pool_list σn j !! k = Some x) by (by rewrite Hpln).
    iDestruct (rest_view_get with "Hrest") as "[Hrest #Hviewn]".
    iDestruct (rest_node_acc _ _ _ σn x with "Hrest") as (y) "(%Hy & Hnx & Hback)".
    { eapply (pool_list_in_dom n); [done|]. by eapply list_elem_of_lookup_2. }
    iDestruct "Hnx" as "(Hn2 & Hn3 & Hn1)".
    wp_load.
    iMod ("Hclose" with "[Htr Hn2 Hn3 Hn1 Hback]") as "_".
    { iNext. iExists σn. iFrame "Htr". iSplit; [done|]. iApply "Hback". iFrame. }
    iModIntro.
    destruct (read_next n σn j k x HIn Hj Hxn) as [[? _]|[_ (k' & y' & Hk' & Hy' & Hyy' & _ & Hbetw)]]; [lia|].
    rewrite Hy in Hyy'. injection Hyy' as <-.
    (* unlink the taken nodes below the new node *)
    wp_pures.
    wp_apply (unlink_loop_spec γs n pools ctr sents tracer j (s_pts σn) (s_m σn) k' y k with "[$Hinv $Hviewn]")
      as (r ir pS' mS') "[#Hview' (%Hr & %Hir & %Htb')]".
    { iPureIntro. split_and!; [done|by rewrite -Hsentn|done|]. split.
      - rewrite -Hsentn -/(pool_list σn j). lia.
      - intros i z Hi Hz. rewrite -Hsentn in Hz |- *. exact (Hbetw i z Hi Hz). }
    wp_pures.
    wp_bind (_ <- _)%E.
    iInv "Hinv" as (σw) "(>[%HIw %Hsentw] & >Htr & >Hrest)" "Hclose".
    iDestruct (owner_agree with "Hmine Hrest") as %[Hbw Hkw]; [done|done|].
    iDestruct (rest_pts_valid with "Hrest HpP") as %HpPw.
    iDestruct (rest_view_valid with "Hrest Hview'") as %[HpSw HmSw].
    pose proof (Hlater σw Hsentw HpPw Hkw) as Hplw.
    assert (Hxw : pool_list σw j !! k = Some x) by (by rewrite Hplw).
    iDestruct (rest_next _ _ _ σw x r with "Hrest") as (y0) "[Hn2 Hback]".
    { eapply (pool_list_in_dom n); [done|]. by eapply list_elem_of_lookup_2. }
    wp_store.
    iMod ("Hclose" with "[Htr Hn2 Hback]") as "_".
    { iNext. iExists (ev_next σw x r). iFrame "Htr". iSplitR; [|by iApply "Hback"].
      iPureIntro. split; [|done].
      destruct Htb' as [Hlen' Hall'].
      assert (Hsnap : pool_list_l sents pS' j `prefix_of` pool_list σw j) by (by apply pool_list_snap).
      apply (tss_inv_next n σw j k x ir r); [done|done|done|lia|lia| |].
      - by eapply prefix_lookup_Some.
      - intros i' z Hi' Hz.
        destruct (lookup_lt_is_Some_2 (pool_list_l sents pS' j) i') as [z' Hz']; [lia|].
        rewrite (prefix_lookup_Some _ _ _ _ Hz' Hsnap) in Hz. injection Hz as <-.
        eapply (taken_snapshot σw); [exact HpSw|exact HmSw|]. rewrite Hsentw. by apply (Hall' i'). }
    iModIntro. wp_pures.
    (* the timestamp *)
    wp_apply (get_timestamp_spec with "[$Hinv $HcP]") as (t1 t2) "[%Ht12 #Hct]".
    wp_pures.
    wp_bind (_ <- _)%E.
    iInv "Hinv" as (σs) "(>[%HIs %Hsents] & >Htr & >Hrest)" "Hclose".
    iDestruct (owner_agree with "Hmine Hrest") as %[Hbs Hks]; [done|done|].
    iDestruct (rest_pts_valid with "Hrest HpP") as %HpPs.
    iDestruct (rest_c_valid with "Hrest Hct") as %Hcs.
    iDestruct (rest_os_lookup with "Hrest Hτ") as %Hoss.
    pose proof (Hlater σs Hsents HpPs Hks) as Hpls.
    pose proof (node_of_l_prefix _ _ _ _ HpPs HnodeP) as Hnodes.
    pose proof (PT_l_prefix _ _ _ _ HpPs HPTP) as HPTs.
    assert (Hlasts : last (pool_list σs j) = Some x) by (rewrite Hpls HplP'; apply last_snoc).
    destruct (ti_os _ _ HIs τ _ Hoss) as (_ & _ & HTSs).
    iDestruct (rest_stamp γs pools ctr σs n τ x j (t1, t2) with "Hrest Hτ") as (v0) "[Hn1 Hst]"; [done|done|done|].
    wp_store.
    iMod ("Hst" with "Hn1") as "(Hrest & Hτ & #Hτt)".
    iMod ("Hclose" with "[Htr Hrest]") as "_".
    { iNext. iExists (ev_stamp σs τ (t1, t2)). iFrame. iPureIntro. split; [|done].
      apply (tss_inv_stamp n σs τ (t1, t2) x j (s_c σp)); simpl; try done; lia. }
    iModIntro. wp_pures.
    (* release the thread ID: the newest node of the pool is timestamped *)
    iApply fupd_wp.
    iInv "Hinv" as (σq) "(>[%HIq %Hsentq] & >Htr & >Hrest)" "Hclose".
    iDestruct (owner_agree with "Hmine Hrest") as %[Hbq Hkq]; [done|done|].
    iDestruct (rest_pts_valid with "Hrest HpP") as %HpPq.
    iDestruct (rest_TS_lookup with "Hrest Hτt") as %HTSq.
    pose proof (Hlater σq Hsentq HpPq Hkq) as Hplq.
    pose proof (tag_of_l_prefix _ _ _ _ HpPq HtagP) as Htagq.
    iMod (owner_release with "Hmine Hrest") as "[Hrest Htid]"; [done|done|].
    iMod ("Hclose" with "[Htr Hrest]") as "_".
    { iNext. iExists (ev_busy σq j false). iFrame. iPureIntro. split; [|done].
      apply (tss_inv_busy n σq j false HIq Hj). intros _ z τz Hz Hτz.
      rewrite Hplq HplP' last_snoc in Hz. injection Hz as <-.
      rewrite /tag_of Htagq in Hτz. injection Hτz as <-. by eexists. }
    iModIntro.
    wp_apply (release_tid_spec with "[$Htp $Htid]") as "_".
    (* the return *)
    wp_pures.
    awp_apply (trace_emit_spec _ _ (Ret #()) with "Itrace"); first reflexivity.
    iInv "Hinv" as (σf) "(>[%HIf %Hsentf] & >Htr & >Hrest)".
    rewrite /atomic_acc /=. iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    iDestruct (rest_os_lookup with "Hrest Hτ") as %Hosf.
    iFrame "Htr". iSplit.
    { iPureIntro. exact (tss_inv_I_ts n _ (tss_inv_ret_push n σf τ HIf Hosf)). }
    iSplit.
    { iIntros "[Htr _]". iMod "Hclose" as "_". iModIntro. iSplitR "HΦ Hτ"; last by iFrame.
      iNext. iExists σf. by iFrame. }
    iIntros "Htr". iMod "Hclose" as "_".
    iMod (rest_ret _ _ _ _ _ #() _ PushReturned with "Hrest Hτ") as "[Hrest _]".
    iModIntro. iSplitR "HΦ".
    { iNext. iExists (ev_ret σf τ #() PushReturned). iFrame. iPureIntro.
      split; [by apply tss_inv_ret_push|done]. }
    wp_pures. by iApply "HΦ".
  Qed.
End proof.
