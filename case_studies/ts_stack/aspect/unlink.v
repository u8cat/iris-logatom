(* Unlinking the taken nodes below a node of an SP pool, and storing a next pointer. *)

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
From case_studies.ts_stack.aspect Require Import pure defs resources.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  Lemma unlink_loop_spec γs n pools ctr sents tracer j (pS : list pt_entry) mS iy (y : loc) ix :
    {{{ inv tsN (ts_inv γs n pools ctr sents tracer) ∗ view γs pS mS ∗
        ⌜j < n ∧ pool_list_l sents pS j !! iy = Some y ∧ iy < ix ∧ taken_between sents pS mS j iy ix⌝ }}}
      unlink_loop_aux #y
    {{{ (r : loc) (ir : nat) pS' mS', RET #r; view γs pS' mS' ∗
        ⌜pool_list_l sents pS' j !! ir = Some r ∧ ir ≤ iy ∧ taken_between sents pS' mS' j ir ix⌝ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hview & %Hj & %Hy & %Hiy & %Htb) HΦ".
    iLöb as "IH" forall (pS mS iy y Hy Hiy Htb) "Hview".
    iDestruct "Hview" as "#Hview".
    wp_rec. wp_pures.
    (* read next *)
    wp_bind (! _)%E.
    iInv "Hinv" as (σ) "(>[%HI %Hsent] & Htr & >Hm● & >Hp● & Hrest)" "Hclose".
    iDestruct (view_valid with "Hp● Hm● Hview") as %[HpS HmS].
    pose proof (prefix_lookup_Some _ _ _ _ Hy (pool_list_snap σ sents pS j Hsent HpS)) as Hyσ.
    iDestruct "Hrest" as "(Hc● & Hctr & HTS & HTSf & HK & HKf & Hos & Htops & Hnodes & Hrest)".
    iDestruct (node_access σ y with "Hnodes") as (y1) "(>%Hy1 & (Hn2 & Hn3 & Hn1) & Hback)".
    { eapply pool_list_in_dom; [done|by eapply list_elem_of_lookup_2]. }
    wp_load.
    iDestruct (view_get with "Hp● Hm●") as "(Hp● & Hm● & #Hview1)".
    iMod ("Hclose" with "[-HΦ]") as "_".
    { iNext. iExists σ. iFrame. iSplit; [done|]. iApply "Hback". iFrame. }
    iModIntro.
    pose proof (read_next n σ j iy y HI Hj Hyσ) as Hrn. rewrite Hy1 in Hrn.
    destruct (decide (y1 = y)) as [->|Hne].
    - (* the sentinel: stop *)
      wp_pures. rewrite bool_decide_eq_true_2 //. wp_pures.
      iModIntro. iApply ("HΦ" $! y iy pS mS). by iFrame "Hview".
    - destruct Hrn as [[_ Hself]|[Hiy0 (k & y' & Hk & Hy' & Hyy' & Hy'y & Hbetw)]].
      { injection Hself as ->. done. }
      wp_pures. rewrite bool_decide_eq_false_2; [|by intros [= ?]]. wp_pures.
      (* read taken *)
      wp_bind (! _)%E.
      iInv "Hinv" as (σ') "(>[%HI' %Hsent'] & Htr & >Hm● & >Hp● & Hrest)" "Hclose".
      iDestruct (view_valid with "Hp● Hm● Hview1") as %[HpS1 HmS1].
      iDestruct "Hrest" as "(Hc● & Hctr & HTS & HTSf & HK & HKf & Hos & Htops & Hnodes & Hrest)".
      pose proof (prefix_lookup_Some _ _ _ _ Hyσ (pool_list_mono σ σ' j (eq_trans Hsent (eq_sym Hsent')) HpS1)) as Hyσ'.
      iDestruct (node_access σ' y with "Hnodes") as (y2) "(>%Hy2 & (Hn2 & Hn3 & Hn1) & Hback)".
      { eapply pool_list_in_dom; [done|by eapply list_elem_of_lookup_2]. }
      wp_load.
      iDestruct (view_get with "Hp● Hm●") as "(Hp● & Hm● & #Hview2)".
      iMod ("Hclose" with "[-HΦ]") as "_".
      { iNext. iExists σ'. iFrame. iSplit; [done|]. iApply "Hback". iFrame. }
      iModIntro.
      destruct (takenb σ' y) eqn:Htk.
      + (* taken: move on *)
        wp_pures.
        wp_bind (! _)%E.
        iInv "Hinv" as (σ'') "(>[%HI'' %Hsent''] & Htr & >Hm● & >Hp● & Hrest)" "Hclose".
        iDestruct (view_valid with "Hp● Hm● Hview2") as %[HpS2 HmS2].
        iDestruct "Hrest" as "(Hc● & Hctr & HTS & HTSf & HK & HKf & Hos & Htops & Hnodes & Hrest)".
        pose proof (prefix_lookup_Some _ _ _ _ Hyσ' (pool_list_mono σ' σ'' j (eq_trans Hsent' (eq_sym Hsent'')) HpS2)) as Hyσ''.
        iDestruct (node_access σ'' y with "Hnodes") as (y3) "(>%Hy3 & (Hn2 & Hn3 & Hn1) & Hback)".
        { eapply pool_list_in_dom; [done|by eapply list_elem_of_lookup_2]. }
        wp_load.
        iDestruct (view_get with "Hp● Hm●") as "(Hp● & Hm● & #Hview3)".
        iMod ("Hclose" with "[-HΦ]") as "_".
        { iNext. iExists σ''. iFrame. iSplit; [done|]. iApply "Hback". iFrame. }
        iModIntro.
        pose proof (read_next n σ'' j iy y HI'' Hj Hyσ'') as Hrn'. rewrite Hy3 in Hrn'.
        destruct Hrn' as [[? _]|[_ (k3 & y4 & Hk3 & Hy4 & Hyy4 & _ & Hbetw3)]]; [lia|].
        injection Hyy4 as ->.
        assert (Hlen'' : ix ≤ length (pool_list σ'' j)).
        { destruct Htb as [Hlen _]. pose proof (prefix_length _ _ (pool_list_snap σ'' sents pS j Hsent''
            (transitivity HpS (transitivity HpS1 HpS2)))). lia. }
        iApply ("IH" $! (s_pts σ'') (s_m σ'') k3 y4 with "[%] [%] [%] [HΦ] Hview3").
        4:{ iNext. iIntros (r ir pS' mS') "[Hv (%Hr & %Hir & %Htb')]". iApply "HΦ". iFrame "Hv".
            iPureIntro. split_and!; [done|lia|done]. }
        * rewrite -Hsent''. done.
        * lia.
        * split; [rewrite -Hsent''; done|]. intros i z Hi Hz.
          destruct (decide (i < iy)) as [Hlt|Hge].
          { rewrite -Hsent''. apply (Hbetw3 i); [lia|]. rewrite /pool_list Hsent''. done. }
          destruct (decide (i = iy)) as [->|Hne'].
          { assert (z = y) as -> by (rewrite -Hsent'' in Hz; rewrite /pool_list in Hyσ''; congruence).
            rewrite -Hsent'. eapply takenb_l_mono; [exact HpS2|exact HmS2|exact Htk]. }
          assert (Htb'' : taken_between sents (s_pts σ'') (s_m σ'') j iy ix).
          { apply (taken_between_mono sents pS (s_pts σ'') mS (s_m σ'')); [| |done].
            - by etrans; [|etrans].
            - by etrans; [|etrans]. }
          destruct Htb'' as [_ Hall]. apply (Hall i z); [lia|done].
      + wp_pures. iModIntro. iApply ("HΦ" $! y iy pS mS). by iFrame "Hview".
  Qed.

  (* storing a next pointer that only skips taken nodes *)
  Lemma next_store_spec γs n pools ctr sents tracer (j : nat) (pX pT : list pt_entry) mT ix (x : loc) iy (y : loc) :
    {{{ inv tsN (ts_inv γs n pools ctr sents tracer) ∗ own (γ_pts γs) (◯ML (pX : list (leibnizO pt_entry))) ∗
        view γs pT mT ∗
        ⌜j < n ∧ pool_list_l sents pX j !! ix = Some x ∧ pool_list_l sents pT j !! iy = Some y ∧ iy < ix ∧
          taken_between sents pT mT j iy ix⌝ }}}
      #(x +ₗ 2) <- #y
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #HpX & #HvT & %Hj & %Hx & %Hy & %Hlt & %Htb) HΦ".
    destruct Htb as [Hlen Hbetw].
    iInv "Hinv" as (σ) "(>[%HI %Hsent] & >Htr & >Hrest)" "Hclose".
    iDestruct (rest_pts_valid with "Hrest HpX") as %HpX.
    iDestruct (rest_view_valid with "Hrest HvT") as %[HpT HmT].
    assert (HLX : pool_list_l sents pX j `prefix_of` pool_list σ j) by (by apply pool_list_snap).
    assert (HLT : pool_list_l sents pT j `prefix_of` pool_list σ j) by (by apply pool_list_snap).
    pose proof (prefix_lookup_Some _ _ _ _ Hx HLX) as Hxσ.
    pose proof (prefix_lookup_Some _ _ _ _ Hy HLT) as Hyσ.
    iDestruct (rest_next _ _ _ σ x y with "Hrest") as (y0) "[Hn2 Hback]".
    { eapply (pool_list_in_dom n); [done|]. by eapply list_elem_of_lookup_2. }
    wp_store.
    iMod ("Hclose" with "[Htr Hn2 Hback]") as "_".
    { iNext. iExists (ev_next σ x y). iFrame "Htr". iSplitR; [|by iApply "Hback"].
      iPureIntro. split; [|done].
      apply (tss_inv_next n σ j ix x iy y HI Hj Hxσ ltac:(lia) Hlt Hyσ).
      intros i' z Hi' Hz.
      destruct (lookup_lt_is_Some_2 (pool_list_l sents pT j) i') as [z' Hz']; [lia|].
      rewrite (prefix_lookup_Some _ _ _ _ Hz' HLT) in Hz. injection Hz as <-.
      eapply (taken_snapshot σ); [exact HpT|exact HmT|]. rewrite Hsent. by apply (Hbetw i'). }
    iModIntro. by iApply "HΦ".
  Qed.
End proof.
