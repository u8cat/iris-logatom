(* The pop: its start (the point), its start time, and the retries of tryRem. *)

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
From case_studies.ts_stack.aspect Require Import pure defs resources steps timestamp tryrem.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  Lemma pop_wrapper_spec γ tracer (q : val) :
    {{{ trace_inv tracer I_ts ∗ is_ts tracer γ q }}}
      call_ret_wrapper tracer Pop (λ: "s" <>, tsstack_pop "s")%V q #()
    {{{ w, RET w; True }}}.
  Proof.
    iIntros (Φ) "[#Itrace #His] HΦ".
    iDestruct "His" as (γs pools ctr tpl n sents) "([-> [%Hn %Hlen]] & #Hγ & #Htp & #Hinv)".
    wp_lam. wp_pures.
    (* the call *)
    awp_apply (trace_fresh_spec with "Itrace"); first exact (decode_encode_val (Call Pop #())).
    iInv "Hinv" as (σ) "(>[%HI %Hsent] & >Htr & >Hrest)".
    rewrite /atomic_acc /=. iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    iFrame "Htr". iSplit.
    { iPureIntro. intros τ Hfresh. exact (tss_inv_I_ts n _ (tss_inv_call_pop n σ τ HI Hfresh)). }
    iSplit.
    { iIntros "[Htr _]". iMod "Hclose" as "_". iModIntro. iSplitR "HΦ"; last done.
      iNext. iExists σ. by iFrame. }
    iIntros (p) "[Htr %Hfresh]". iMod "Hclose" as "_".
    iMod (rest_call _ _ _ σ p (Call Pop #()) PopCalled with "Hrest") as "(Hrest & Hp & #HpK)";
      [done|apply HI|apply HI|].
    iDestruct (alloc_hist with "Htr") as "[Htr #Hhist]".
    iModIntro. iSplitR "HΦ Hp".
    { iNext. iExists (ev_call σ p (Call Pop #()) PopCalled). iFrame. iPureIntro.
      split; [by apply tss_inv_call_pop|done]. }
    wp_pures.
    (* the point of the pop: its start *)
    iApply fupd_wp.
    iInv "Hinv" as (σ1) "(>[%HI1 %Hsent1] & >Htr & >Hrest)" "Hclose".
    iDestruct (rest_os_lookup with "Hrest Hp") as %Hos1.
    iDestruct (rest_K_lookup with "Hrest HpK") as %HK1.
    iMod (rest_point with "Hrest Hp") as "(Hrest & Hp & #HpP & #Hc1)".
    iMod ("Hclose" with "[Htr Hrest]") as "_".
    { iNext. iExists (ev_point σ1 p). iFrame. iPureIntro. split; [by apply tss_inv_point|done]. }
    iModIntro.
    pose proof (ti_K _ _ HI1 p _ HK1) as Hkc.
    wp_lam. wp_pures.
    wp_apply (get_timestamp_spec with "[$Hinv $Hc1]") as (s1 s2) "[%Hs12 _]".
    wp_let. wp_pure (Rec _ _ _).
    iLöb as "IH".
    wp_rec.
    wp_apply (tryRem_spec γs n pools ctr sents tracer tpl p _ (s_c σ) s1 s2 _ with "[$Hinv $Hp $HpP $HpK $Hhist]")
      as (w) "Hw".
    { iPureIntro. split_and!; [lia|done| |lia|lia|].
      - rewrite fmap_app elem_of_app. right. by left.
      - rewrite elem_of_app list_elem_of_singleton. by right. }
    iDestruct "Hw" as "[[-> Hp]|[(%b & %v & %mC & %tsC & (-> & %Hbp & %Hbv) & Hp & #HmC & #HhC)|(-> & Hp & #Hempty)]]".
    - (* retry *)
      wp_pure (Case _ _ _). wp_pure (Rec _ _ _). wp_pure (App _ _).
      iApply ("IH" with "HΦ Hp").
    - (* a value *)
      wp_pures.
      awp_apply (trace_emit_spec _ _ (Ret (SOMEV v)) with "Itrace"); first reflexivity.
      iInv "Hinv" as (σf) "(>[%HIf %Hsentf] & >Htr & >Hrest)".
      rewrite /atomic_acc /=. iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
      iDestruct (rest_os_lookup with "Hrest Hp") as %Hosf.
      iDestruct (rest_m_valid with "Hrest HmC") as %HmCf.
      iDestruct (hist_trace_is_prefix with "Htr HhC") as %HtsCf.
      assert (Hbpf : (b, p) ∈ s_m σf) by (by eapply elem_of_prefix).
      assert (Hbvf : (b, Call Push v) ∈ s_ts σf) by (by eapply elem_of_prefix).
      pose proof (tss_inv_ret_pop_val n σf p b v HIf Hosf Hbpf Hbvf) as HIf'.
      iFrame "Htr". iSplit; [iPureIntro; exact (tss_inv_I_ts n _ HIf')|].
      iSplit.
      { iIntros "[Htr _]". iMod "Hclose" as "_". iModIntro. iSplitR "HΦ Hp"; last by iFrame.
        iNext. iExists σf. by iFrame. }
      iIntros "Htr". iMod "Hclose" as "_".
      iMod (rest_ret _ _ _ _ _ (SOMEV v) _ PopReturned with "Hrest Hp") as "[Hrest _]".
      iModIntro. iSplitR "HΦ".
      { iNext. iExists (ev_ret σf p (SOMEV v) PopReturned). iFrame. iPureIntro. split; [exact HIf'|done]. }
      wp_pures. by iApply "HΦ".
    - (* empty *)
      wp_pures.
      iDestruct "Hempty" as (tsT mT pT) "(#HhT & #HmT & #HpT & %HwT & #Hcs)".
      destruct HwT as (HpT' & Hret & Hm2 & Hpool).
      awp_apply (trace_emit_spec _ _ (Ret NONEV) with "Itrace"); first reflexivity.
      iInv "Hinv" as (σf) "(>[%HIf %Hsentf] & >Htr & >Hrest)".
      rewrite /atomic_acc /=. iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
      iDestruct (rest_os_lookup with "Hrest Hp") as %Hosf.
      iDestruct (rest_m_valid with "Hrest HmT") as %HmTf.
      iDestruct (rest_pts_valid with "Hrest HpT") as %HpTf.
      iDestruct (hist_trace_is_prefix with "Htr HhT") as %HtsTf.
      iAssert (⌜∀ j x, x ∈ pnodes pT j → takenb_l (s_sent σf) (s_pts σf) mT x = true⌝)%I as %Htk.
      { iIntros (j x Hx). destruct (decide (j < n)) as [Hj|Hj].
        - iDestruct (big_sepL_lookup _ _ j j with "Hcs") as (pj) "[Hpj %Hcj]".
          { apply lookup_seq. split; [done|lia]. }
          iDestruct (rest_pts_valid with "Hrest Hpj") as %Hpjf.
          iPureIntro. destruct Hcj as [_ Hcj].
          eapply takenb_l_mono; [exact Hpjf|done|]. rewrite Hsentf. by apply Hcj.
        - iPureIntro. exfalso. apply elem_of_pnodes in Hx as (τ & c & Hin).
          specialize (Hpool _ _ _ _ Hin). lia. }
      destruct (empty_witness n σf tsT mT pT HIf HtsTf HmTf HpTf Hret Hm2 Htk) as [Hcov1 Hcov2].
      apply list_elem_of_lookup in HpT' as [icall Hicall].
      pose proof (prefix_lookup_Some _ _ _ _ Hicall HtsTf) as Hicallf.
      assert (Hle : icall ≤ length tsT ≤ length (s_ts σf)).
      { split; [apply lookup_lt_Some in Hicall; lia|by apply prefix_length]. }
      pose proof (tss_inv_ret_pop_empty n σf p icall (length tsT) HIf Hosf Hicallf Hle Hcov1 Hcov2) as HIf'.
      iFrame "Htr". iSplit; [iPureIntro; exact (tss_inv_I_ts n _ HIf')|].
      iSplit.
      { iIntros "[Htr _]". iMod "Hclose" as "_". iModIntro. iSplitR "HΦ Hp"; last by iFrame.
        iNext. iExists σf. by iFrame. }
      iIntros "Htr". iMod "Hclose" as "_".
      iMod (rest_ret _ _ _ _ _ NONEV _ PopReturned with "Hrest Hp") as "[Hrest _]".
      iModIntro. iSplitR "HΦ".
      { iNext. iExists (ev_ret σf p NONEV PopReturned). iFrame. iPureIntro. split; [exact HIf'|done]. }
      wp_pures. by iApply "HΦ".
  Qed.
End proof.
