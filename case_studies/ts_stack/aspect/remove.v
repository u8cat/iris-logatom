(* The removal of a node from an SP pool; its taken-CAS is the commit of the pop. *)

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
From case_studies.ts_stack.aspect Require Import pure defs resources unlink.


Section proof.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  (* removing node x (position k of pool j, found by a walk that read the top A) *)
  Lemma sppool_remove_spec γs n pools ctr sents tracer p (j : nat) (A x : loc) k :
    {{{ inv tsN (ts_inv γs n pools ctr sents tracer) ∗ ⌜j < n⌝ ∗ p ↪[γ_os γs] PopStarted ∗
        walk_wit γs sents p j A (Some (x, k)) ∗ lifo_wit γs n pools ctr sents tracer x p }}}
      sppool_remove #(pools +ₗ j) #A #x
    {{{ w, RET w; (⌜w = NONEV⌝ ∗ p ↪[γ_os γs] PopStarted) ∨
        (∃ b v (mC : list (positive * positive)) tsC, ⌜w = SOMEV v ∧ (b, p) ∈ mC ∧ (b, Call Push v) ∈ tsC⌝ ∗
          p ↪[γ_os γs] PopCommitted ∗ own (γ_m γs) (◯ML (mC : list (leibnizO (positive * positive)))) ∗
          hist tracer tsC) }}}.
  Proof.
    iIntros (Φ) "(#Hinv & %Hj & Hp & #Hwalk & #Hlifo) HΦ".
    iDestruct "Hwalk" as (pS pT mT) "(#HpS & #HvT & %HppS & %Hwr)".
    destruct Hwr as (HpST & ia & HA & Hx & [Hk1 Hkia] & Habove).
    set (L0 := pool_list_l sents pS j) in *.
    assert (HL0T : L0 `prefix_of` pool_list_l sents pT j) by (by apply pool_list_l_prefix).
    wp_lam. wp_pures.
    (* the taken-CAS: the commit *)
    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as (σc) "(>[%HIc %Hsentc] & >Htr & >Hrest)" "Hclose".
    iDestruct (rest_pts_valid with "Hrest HpS") as %HpSc.
    iDestruct (rest_view_valid with "Hrest HvT") as %[HpTc HmTc].
    iDestruct (rest_view_get with "Hrest") as "[Hrest #Hvc]".
    assert (Hxc : pool_list σc j !! k = Some x).
    { eapply prefix_lookup_Some; [exact Hx|]. by apply pool_list_snap. }
    destruct (pool_node_tag n σc j k x HIc Hk1 Hxc) as (b & Htagc & Hnodec & Hpushc).
    iDestruct (rest_os_lookup with "Hrest Hp") as %Hosc.
    iDestruct (rest_elem _ _ _ σc n x b with "Hrest") as (v) "[#Hxv %Hbv]"; [done|done|].
    iDestruct (alloc_hist with "Htr") as "[Htr #Hhc]".
    iDestruct ("Hlifo" $! σc b with "[%] Htr Hrest") as %Hlifo; first done.
    iDestruct (rest_commit _ _ _ σc n b p x j with "Hrest") as "[H3 Hcommit]"; [done|done|].
    destruct (takenb σc x) eqn:Htk.
    { (* already taken: fail *)
      wp_cmpxchg_fail. iDestruct "Hcommit" as "[Hback _]".
      iMod ("Hclose" with "[Htr H3 Hback]") as "_".
      { iNext. iExists σc. iFrame "Htr". iSplit; [done|]. by iApply "Hback". }
      iModIntro. wp_pures. iModIntro. iApply "HΦ". iLeft. by iFrame. }
    wp_cmpxchg_suc. iDestruct "Hcommit" as "[_ Hcommit]".
    iMod ("Hcommit" with "H3 Hp") as "(Hrest & Hp & #HmC)".
    assert (Hbm : b ∉ (s_m σc).*1).
    { intros Hin. rewrite /takenb /takenb_l in Htk. change (tag_of_l (s_pts σc) x) with (tag_of σc x) in Htk.
      rewrite Htagc in Htk. apply orb_false_iff in Htk as [_ Htk]. by apply bool_decide_eq_false in Htk. }
    iMod ("Hclose" with "[Htr Hrest]") as "_".
    { iNext. iExists (ev_commit σc b p). iFrame. iPureIntro. split; [|done].
      exact (tss_inv_commit n σc b p x j HIc Hosc Hnodec Hbm Hlifo). }
    iModIntro. wp_pures.
    (* move the top down to the removed node *)
    wp_bind (CmpXchg _ _ _).
    iApply (wp_wand _ _ _ (λ v, ⌜∃ w1 w2 : val, v = (w1, w2)%V⌝)%I with "[]").
    { iInv "Hinv" as (σt) "(>[%HIt %Hsentt] & >Htr & >Hrest)" "Hclose".
      iDestruct (rest_pts_valid with "Hrest HpS") as %HpSt.
      iDestruct (rest_view_valid with "Hrest HvT") as %[HpTt HmTt].
      iDestruct (rest_view_valid with "Hrest Hvc") as %[Hpct _].
      iDestruct (rest_m_valid with "Hrest HmC") as %HmCt.
      destruct (ti_len _ _ HIt) as (_ & Hltt & _).
      destruct (lookup_lt_is_Some_2 (s_top σt) j) as [t Ht]; first lia.
      iDestruct (rest_top_acc with "Hrest") as "[Htop Hback]"; first done.
      destruct (decide (t = A)) as [->|Hne].
      - wp_cmpxchg_suc. iDestruct "Hback" as "[_ Hback]". iSpecialize ("Hback" $! x with "Htop").
        iMod ("Hclose" with "[Htr Hback]") as "_"; last by eauto.
        iNext. iExists (ev_top σt j x). iFrame. iPureIntro. split; [|done].
        assert (HL : L0 `prefix_of` pool_list σt j) by (by apply pool_list_snap).
        apply (tss_inv_top n σt j x k HIt Hj); first exact (prefix_lookup_Some _ _ _ _ Hx HL).
        apply (top_cas_ok n σt j A x ia k L0 pT mT b HIt Hj Ht HL HA Hx Hkia HpTt HmTt).
        + intros i z Hi Hz. rewrite Hsentt. by apply (Habove i).
        + exact (tag_of_l_prefix _ _ _ _ Hpct Htagc).
        + intros Hin. apply Hbm. destruct HmTc as [l ->]. rewrite fmap_app elem_of_app. by left.
        + destruct HmCt as [l ->]. rewrite !fmap_app !elem_of_app. left. right. by left.
      - wp_cmpxchg_fail.
        iDestruct "Hback" as "[Hback _]".
        iMod ("Hclose" with "[Htr Htop Hback]") as "_"; last by eauto.
        iNext. iExists σt. iFrame "Htr". iSplit; [done|]. by iApply "Hback". }
    iIntros (?) "(%w1 & %w2 & ->)". wp_pures.
    (* the old top points to the removed node *)
    wp_bind (If _ _ _).
    iApply (wp_wand _ _ _ (λ _, True)%I with "[]").
    { destruct (decide (A = x)) as [->|Hne].
      - rewrite bool_decide_eq_true_2 //. wp_pures. done.
      - rewrite bool_decide_eq_false_2; last by intros [= ?]. wp_pures.
        assert (Hk : k < ia).
        { destruct (decide (k = ia)) as [->|?]; [|lia]. rewrite HA in Hx. by injection Hx. }
        wp_apply (next_store_spec γs n pools ctr sents tracer j pS pT mT ia A k x with "[$Hinv $HpS $HvT]");
          [|done].
        iPureIntro. split_and!; [done|done|exact (prefix_lookup_Some _ _ _ _ Hx HL0T)|done|]. split.
        + pose proof (prefix_length _ _ HL0T). apply lookup_lt_Some in HA. lia.
        + intros i z Hi Hz. apply (Habove i); [lia|].
          destruct (lookup_lt_is_Some_2 L0 i) as [z' Hz']; [apply lookup_lt_Some in HA; lia|].
          by rewrite (prefix_lookup_Some _ _ _ _ Hz' HL0T) in Hz; injection Hz as ->. }
    iIntros (?) "_". wp_pures.
    (* unlink the taken nodes below the removed node *)
    wp_bind (! _)%E.
    iInv "Hinv" as (σn) "(>[%HIn %Hsentn] & >Htr & >Hrest)" "Hclose".
    iDestruct (rest_pts_valid with "Hrest HpS") as %HpSn.
    assert (Hxn : pool_list σn j !! k = Some x).
    { eapply prefix_lookup_Some; [exact Hx|]. by apply pool_list_snap. }
    iDestruct (rest_view_get with "Hrest") as "[Hrest #Hviewn]".
    iDestruct (rest_node_acc _ _ _ σn x with "Hrest") as (y) "(%Hy & (Hn2 & Hn3 & Hn1) & Hback)".
    { eapply (pool_list_in_dom n); [done|]. by eapply list_elem_of_lookup_2. }
    wp_load.
    iMod ("Hclose" with "[Htr Hn2 Hn3 Hn1 Hback]") as "_".
    { iNext. iExists σn. iFrame "Htr". iSplit; [done|]. iApply "Hback". iFrame. }
    iModIntro.
    destruct (read_next n σn j k x HIn Hj Hxn) as [[? _]|[_ (k' & y' & Hk' & Hy' & Hyy' & _ & Hbetw)]]; [lia|].
    rewrite Hy in Hyy'. injection Hyy' as <-.
    wp_pures.
    wp_apply (unlink_loop_spec γs n pools ctr sents tracer j (s_pts σn) (s_m σn) k' y k with "[$Hinv $Hviewn]")
      as (r ir pS' mS') "[#Hview' (%Hr & %Hir & %Htb')]".
    { iPureIntro. split_and!; [done|by rewrite -Hsentn|done|]. split.
      - rewrite -Hsentn -/(pool_list σn j). apply lookup_lt_Some in Hxn. lia.
      - intros i z Hi Hz. rewrite -Hsentn in Hz |- *. exact (Hbetw i z Hi Hz). }
    wp_pures.
    wp_apply (next_store_spec γs n pools ctr sents tracer j pS pS' mS' k x ir r with "[$Hinv $HpS $Hview']").
    { iPureIntro. split_and!; [done|done|done|lia|done]. }
    iIntros "_". wp_pures. wp_load. wp_pures. iModIntro.
    iApply "HΦ". iRight. iExists b, v, (s_m σc ++ [(b, p)]), (s_ts σc). iFrame "Hp HmC Hhc".
    iPureIntro. split_and!; [done| |done]. rewrite elem_of_app list_elem_of_singleton. by right.
  Qed.
End proof.
