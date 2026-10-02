(* The walk of a pop down an SP pool, from the top to the first node that is not taken. *)

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

  Lemma get_youngest_spec γs n pools ctr sents tracer (j : nat) p (pP : list pt_entry) :
    {{{ inv tsN (ts_inv γs n pools ctr sents tracer) ∗ ⌜j < n⌝ ∗
        own (γ_pts γs) (◯ML (pP : list (leibnizO pt_entry))) ∗ ⌜p ∈ (λ e : pt_entry, e.1.1) <$> pP⌝ }}}
      sppool_get_youngest #(pools +ₗ j)
    {{{ (ro : option (loc * nat)) (A : loc),
        RET (opt_node ro, #A)%V;
        walk_wit γs sents p j A ro }}}.
  Proof.
    iIntros (Φ) "(#Hinv & %Hj & #HpP & %HppP) HΦ".
    wp_lam.
    (* read the top *)
    wp_bind (! _)%E.
    iInv "Hinv" as (σ0) "(>[%HI0 %Hsent0] & >Htr & >Hrest)" "Hclose".
    iDestruct (rest_pts_valid with "Hrest HpP") as %HpP0.
    iDestruct (rest_view_get with "Hrest") as "[Hrest #Hview0]".
    destruct (ti_len _ _ HI0) as (Hls & Hlt & _).
    destruct (lookup_lt_is_Some_2 (s_top σ0) j) as [A HA]; first lia.
    iDestruct (rest_top_acc with "Hrest") as "[Htop [Hback _]]"; first done.
    wp_load.
    iMod ("Hclose" with "[Htr Htop Hback]") as "_".
    { iNext. iExists σ0. iFrame "Htr". iSplit; [done|]. by iApply "Hback". }
    iModIntro.
    destruct (read_top n σ0 j A HI0 Hj HA) as (ia & Hia & Habove).
    set (pS := s_pts σ0).
    assert (HL0 : pool_list σ0 j = pool_list_l sents pS j) by (by rewrite /pool_list Hsent0).
    destruct (lookup_lt_is_Some_2 sents j) as [s Hs]; first (rewrite -Hsent0; lia).
    assert (HL00 : pool_list_l sents pS j !! 0 = Some s) by (by rewrite /pool_list_l Hs).
    assert (HppS : p ∈ (λ e : pt_entry, e.1.1) <$> pS) by (by eapply tags_prefix).
    iAssert (own (γ_pts γs) (◯ML (pS : list (leibnizO pt_entry))))%I as "#HpS0".
    { by iDestruct "Hview0" as "[$ _]". }
    wp_let. wp_pure (Rec _ _ _).
    lazymatch goal with |- context [wp _ _ (App (Val ?f) _) _] => set (F := f) end.
    iAssert (∀ (z : loc) (iz : nat) (pT : list pt_entry) mT,
      view γs pT mT -∗
      ⌜pS `prefix_of` pT ∧ pool_list_l sents pS j !! iz = Some z ∧ iz ≤ ia ∧
        ∀ i z', iz < i → pool_list_l sents pS j !! i = Some z' → takenb_l sents pT mT z' = true⌝ -∗
      (∀ ro A0, walk_wit γs sents p j A0 ro -∗ Φ (opt_node ro, #A0)%V) -∗
      WP F #z {{ v, Φ v }})%I as "Hloop".
    { iIntros (z iz pT mT) "Hview %Hinvar HΦ".
      iLöb as "IH" forall (z iz pT mT Hinvar) "Hview". iDestruct "Hview" as "#Hview".
      destruct Hinvar as (HpST & Hz & Hiz & HaboveT).
      rewrite {2}/F. wp_rec. wp_pures.
      (* read taken *)
      wp_bind (! _)%E.
      iInv "Hinv" as (σ1) "(>[%HI1 %Hsent1] & >Htr & >Hrest)" "Hclose".
      iDestruct (rest_pts_valid with "Hrest HpS0") as %HpS1.
      iDestruct (rest_view_valid with "Hrest Hview") as %[HpT1 HmT1].
      assert (HL1 : pool_list_l sents pS j `prefix_of` pool_list σ1 j) by (by apply pool_list_snap).
      pose proof (prefix_lookup_Some _ _ _ _ Hz HL1) as Hz1.
      iDestruct (rest_view_get with "Hrest") as "[Hrest #Hview1]".
      iDestruct (rest_node_acc _ _ _ σ1 z with "Hrest") as (y1) "(%Hy1 & (Hn2 & Hn3 & Hn1) & Hback)".
      { eapply (pool_list_in_dom n); [done|]. by eapply list_elem_of_lookup_2. }
      wp_load.
      iMod ("Hclose" with "[Htr Hn2 Hn3 Hn1 Hback]") as "_".
      { iNext. iExists σ1. iFrame "Htr". iSplit; [done|]. iApply "Hback". iFrame. }
      iModIntro.
      destruct (takenb σ1 z) eqn:Htk1; last first.
      { (* not taken: the result *)
        wp_pures. iModIntro. iApply ("HΦ" $! (Some (z, iz)) A).
        iExists pS, pT, mT. iFrame "HpS0 Hview". iPureIntro. split; [done|].
        split; [done|]. exists ia. split; [by rewrite -HL0|]. split_and!; [done| |done|done].
        destruct iz as [|iz]; [|lia]. exfalso. rewrite HL00 in Hz. injection Hz as <-.
        rewrite (sent_taken σ1 s) in Htk1; [done|]. rewrite Hsent1. by eapply list_elem_of_lookup_2. }
      wp_pures.
      (* taken: read next *)
      wp_bind (! _)%E.
      iInv "Hinv" as (σ2) "(>[%HI2 %Hsent2] & >Htr & >Hrest)" "Hclose".
      iDestruct (rest_pts_valid with "Hrest HpS0") as %HpS2.
      assert (Hz2 : pool_list σ2 j !! iz = Some z).
      { eapply prefix_lookup_Some; [exact Hz|]. by apply pool_list_snap. }
      iDestruct (rest_node_acc _ _ _ σ2 z with "Hrest") as (y2) "(%Hy2 & (Hn2 & Hn3 & Hn1) & Hback)".
      { eapply (pool_list_in_dom n); [done|]. by eapply list_elem_of_lookup_2. }
      wp_load.
      iMod ("Hclose" with "[Htr Hn2 Hn3 Hn1 Hback]") as "_".
      { iNext. iExists σ2. iFrame "Htr". iSplit; [done|]. iApply "Hback". iFrame. }
      iModIntro.
      destruct (read_next n σ2 j iz z HI2 Hj Hz2) as [[-> Hself]|[Hiz0 (k2 & y2' & Hk2 & _ & Hyy2 & Hne2 & _)]].
      { (* the sentinel: every node is taken *)
        rewrite Hy2 in Hself. injection Hself as ->.
        wp_pures. rewrite bool_decide_eq_true_2 //. wp_pures. iModIntro.
        iApply ("HΦ" $! None A). iExists pS, (s_pts σ1), (s_m σ1). iFrame "HpS0 Hview1".
        iPureIntro. split; [done|]. split; [done|]. exists ia. split; [by rewrite -HL0|].
        intros z' Hz'. apply list_elem_of_lookup in Hz' as [i Hi].
        destruct i as [|i].
        - rewrite HL00 in Hi. injection Hi as <-. rewrite /takenb_l bool_decide_eq_true_2 //.
          by eapply list_elem_of_lookup_2.
        - eapply takenb_l_mono; [exact HpT1|exact HmT1|]. apply (HaboveT (1 + i)); [lia|done]. }
      rewrite Hy2 in Hyy2. injection Hyy2 as <-.
      wp_pures. rewrite bool_decide_eq_false_2; last by intros [= ?]. wp_pures.
      (* read next again and go on *)
      wp_bind (! _)%E.
      iInv "Hinv" as (σ3) "(>[%HI3 %Hsent3] & >Htr & >Hrest)" "Hclose".
      iDestruct (rest_pts_valid with "Hrest HpS0") as %HpS3.
      iDestruct (rest_view_valid with "Hrest Hview1") as %[HpT13 HmT13].
      assert (HL3 : pool_list_l sents pS j `prefix_of` pool_list σ3 j) by (by apply pool_list_snap).
      pose proof (prefix_lookup_Some _ _ _ _ Hz HL3) as Hz3.
      iDestruct (rest_view_get with "Hrest") as "[Hrest #Hview3]".
      iDestruct (rest_node_acc _ _ _ σ3 z with "Hrest") as (y3) "(%Hy3 & (Hn2 & Hn3 & Hn1) & Hback)".
      { eapply (pool_list_in_dom n); [done|]. by eapply list_elem_of_lookup_2. }
      wp_load.
      iMod ("Hclose" with "[Htr Hn2 Hn3 Hn1 Hback]") as "_".
      { iNext. iExists σ3. iFrame "Htr". iSplit; [done|]. iApply "Hback". iFrame. }
      iModIntro.
      destruct (read_next n σ3 j iz z HI3 Hj Hz3) as [[? _]|[_ (k3 & y3' & Hk3 & Hy3' & Hyy3 & _ & Hbetw3)]];
        [lia|].
      rewrite Hy3 in Hyy3. injection Hyy3 as <-.
      assert (HlenL : iz < length (pool_list_l sents pS j)) by (by eapply lookup_lt_Some).
      destruct (lookup_lt_is_Some_2 (pool_list_l sents pS j) k3) as [y3'' Hy3'']; first lia.
      rewrite (prefix_lookup_Some _ _ _ _ Hy3'' HL3) in Hy3'. injection Hy3' as ->.
      iApply ("IH" $! y3 k3 (s_pts σ3) (s_m σ3) with "[%] HΦ Hview3").
      split_and!; [done|done|lia|]. intros i z' Hi Hz'.
      destruct (decide (i < iz)) as [Hlt'|Hge].
      { rewrite -Hsent3. apply (Hbetw3 i z'); [lia|]. by eapply prefix_lookup_Some. }
      destruct (decide (i = iz)) as [->|Hne'].
      { rewrite Hz in Hz'. injection Hz' as <-. rewrite /takenb Hsent1 in Htk1.
        eapply takenb_l_mono; [exact HpT13|exact HmT13|exact Htk1]. }
      eapply (takenb_l_mono _ pT _ mT); [by etrans|by etrans|].
      apply (HaboveT i); [lia|done]. }
    iApply ("Hloop" $! A ia (s_pts σ0) (s_m σ0) with "Hview0 [%] HΦ").
    split_and!; [done|by rewrite -HL0|done|].
    intros i z' Hi Hz'. rewrite -HL0 in Hz'. destruct (Habove i z' Hi Hz') as [Ht _].
    rewrite /taken /takenb Hsent0 in Ht. exact Ht.
  Qed.
End proof.
