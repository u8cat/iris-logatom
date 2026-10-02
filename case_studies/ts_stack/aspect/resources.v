(* The resources of the invariant: snapshots, lookups, and the accessors used by the SP-pool
   operations, including the commit of a pop. *)

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
From case_studies.ts_stack.aspect Require Import pure defs.


Section proof.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  Lemma view_valid γs σ pS mS :
    own (γ_pts γs) (●ML (s_pts σ : list (leibnizO pt_entry))) -∗
    own (γ_m γs) (●ML (s_m σ : list (leibnizO (positive * positive)))) -∗
    view γs pS mS -∗ ⌜pS `prefix_of` s_pts σ ∧ mS `prefix_of` s_m σ⌝.
  Proof.
    iIntros "Hp Hm [HpS HmS]".
    iDestruct (own_valid_2 with "Hp HpS") as %?%mono_list_both_valid_L.
    iDestruct (own_valid_2 with "Hm HmS") as %?%mono_list_both_valid_L.
    done.
  Qed.

  Lemma view_get γs σ :
    own (γ_pts γs) (●ML (s_pts σ : list (leibnizO pt_entry))) -∗
    own (γ_m γs) (●ML (s_m σ : list (leibnizO (positive * positive)))) -∗
    own (γ_pts γs) (●ML (s_pts σ : list (leibnizO pt_entry))) ∗
    own (γ_m γs) (●ML (s_m σ : list (leibnizO (positive * positive)))) ∗ view γs (s_pts σ) (s_m σ).
  Proof.
    iIntros "Hp Hm". iEval (rewrite mono_list_auth_lb_op) in "Hp". iEval (rewrite mono_list_auth_lb_op) in "Hm".
    iDestruct "Hp" as "[$ $]". iDestruct "Hm" as "[$ $]".
  Qed.

  Lemma node_access σ x :
    x ∈ dom (s_next σ) →
    ([∗ map] z ↦ y ∈ s_next σ, node_res σ z y) ⊢
    ∃ y, ⌜s_next σ !! x = Some y⌝ ∗ node_res σ x y ∗
      (node_res σ x y -∗ [∗ map] z ↦ y ∈ s_next σ, node_res σ z y).
  Proof.
    iIntros (Hx) "Hn". apply elem_of_dom in Hx as [y Hy].
    iDestruct (big_sepM_lookup_acc with "Hn") as "[Hy Hback]"; first done.
    iExists y. by iFrame.
  Qed.

  Lemma rest_pts_valid γs pools ctr σ pS :
    ts_rest γs pools ctr σ -∗ own (γ_pts γs) (◯ML (pS : list (leibnizO pt_entry))) -∗
    ⌜pS `prefix_of` s_pts σ⌝.
  Proof. iIntros "(_ & Hp & _) HpS". by iDestruct (own_valid_2 with "Hp HpS") as %?%mono_list_both_valid_L. Qed.

  Lemma rest_view_valid γs pools ctr σ pS mS :
    ts_rest γs pools ctr σ -∗ view γs pS mS -∗ ⌜pS `prefix_of` s_pts σ ∧ mS `prefix_of` s_m σ⌝.
  Proof. iIntros "(Hm & Hp & _) Hv". iApply (view_valid with "Hp Hm Hv"). Qed.

  Lemma rest_view_get γs pools ctr σ :
    ts_rest γs pools ctr σ -∗ ts_rest γs pools ctr σ ∗ view γs (s_pts σ) (s_m σ).
  Proof. iIntros "(Hm & Hp & Hrest)". iDestruct (view_get with "Hp Hm") as "(Hp & Hm & Hv)". iFrame. Qed.

  Lemma rest_c_valid γs pools ctr σ k :
    ts_rest γs pools ctr σ -∗ own (γ_c γs) (◯MN k) -∗ ⌜k ≤ s_c σ⌝.
  Proof. iIntros "(_ & _ & Hc & _) Hk". by iDestruct (own_valid_2 with "Hc Hk") as %?%mono_nat_both_valid. Qed.

  Lemma rest_TS_lookup γs pools ctr σ τ t :
    ts_rest γs pools ctr σ -∗ τ ↪[γ_TS γs]□ t -∗ ⌜s_TS σ !! τ = Some t⌝.
  Proof. iIntros "(_ & _ & _ & _ & HTS & _) Hτ". iApply (ghost_map_lookup with "HTS Hτ"). Qed.

  Lemma rest_K_lookup γs pools ctr σ τ k :
    ts_rest γs pools ctr σ -∗ τ ↪[γ_K γs]□ k -∗ ⌜s_K σ !! τ = Some k⌝.
  Proof. iIntros "(_ & _ & _ & _ & _ & _ & HK & _) Hτ". iApply (ghost_map_lookup with "HK Hτ"). Qed.

  Lemma rest_os_lookup γs pools ctr σ τ s :
    ts_rest γs pools ctr σ -∗ τ ↪[γ_os γs] s -∗ ⌜s_os σ !! τ = Some s⌝.
  Proof. iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & Hos & _) Hτ". iApply (ghost_map_lookup with "Hos Hτ"). Qed.

  Lemma rest_node_acc γs pools ctr σ x :
    x ∈ dom (s_next σ) →
    ts_rest γs pools ctr σ -∗ ∃ y : loc, ⌜s_next σ !! x = Some y⌝ ∗ node_res σ x y ∗
      (node_res σ x y -∗ ts_rest γs pools ctr σ).
  Proof.
    iIntros (Hx) "(Hm & Hp & Hc & Hctr & HTS & HTSf & HK & HKf & Hos & Htops & Hnodes & Hrest)".
    apply elem_of_dom in Hx as [y Hy].
    iDestruct (big_sepM_lookup_acc with "Hnodes") as "[Hy Hback]"; first done.
    iExists y. iFrame "Hy". iSplit; [done|]. iIntros "Hy". iFrame. by iApply "Hback".
  Qed.

  Lemma rest_next γs pools ctr σ x (r : loc) :
    x ∈ dom (s_next σ) →
    ts_rest γs pools ctr σ -∗ ∃ y : loc, (x +ₗ 2) ↦ #y ∗
      ((x +ₗ 2) ↦ #r -∗ ts_rest γs pools ctr (ev_next σ x r)).
  Proof.
    iIntros (Hx) "(Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners)".
    apply elem_of_dom in Hx as [y Hy].
    iDestruct (big_sepM_insert_acc with "Hnodes") as "[(H2 & H3 & H1) Hback]"; first done.
    iExists y. iFrame "H2". iIntros "H2".
    iSpecialize ("Hback" $! r with "[$H2 $H3 $H1]").
    rewrite /ts_rest /=. iFrame "∗ #".
  Qed.

  Lemma rest_m_valid γs pools ctr σ mS :
    ts_rest γs pools ctr σ -∗ own (γ_m γs) (◯ML (mS : list (leibnizO (positive * positive)))) -∗
    ⌜mS `prefix_of` s_m σ⌝.
  Proof. iIntros "(Hm & _) HmS". by iDestruct (own_valid_2 with "Hm HmS") as %?%mono_list_both_valid_L. Qed.

  Lemma rest_top_acc γs pools ctr σ (j : nat) (t : loc) :
    s_top σ !! j = Some t →
    ts_rest γs pools ctr σ -∗ (pools +ₗ j) ↦ #t ∗
      (((pools +ₗ j) ↦ #t -∗ ts_rest γs pools ctr σ) ∧
       (∀ t' : loc, (pools +ₗ j) ↦ #t' -∗ ts_rest γs pools ctr (ev_top σ j t'))).
  Proof.
    iIntros (Ht) "(Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners)".
    iDestruct (big_sepL_insert_acc with "Htops") as "[Htop Htops]"; first done.
    iFrame "Htop". iSplit.
    - iIntros "Htop". iSpecialize ("Htops" with "Htop"). rewrite list_insert_id //. iFrame "∗ #".
    - iIntros (t') "Htop". iSpecialize ("Htops" with "Htop"). rewrite /ts_rest /=. iFrame "∗ #".
  Qed.

  Lemma rest_elem γs pools ctr σ n x b :
    tss_inv n σ → tag_of σ x = Some b →
    ts_rest γs pools ctr σ -∗ ∃ v, x ↦□ v ∗ ⌜(b, Call Push v) ∈ s_ts σ⌝.
  Proof.
    iIntros (HI Htag) "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Helems & _)".
    destruct (tag_of_Some σ x b Htag) as (i & c & j & Hi).
    iDestruct (big_sepL_lookup with "Helems") as "He"; first done.
    rewrite /elem_res /=. iDestruct "He" as (v) "[Hx %Hv]". iExists v. by iFrame.
  Qed.

  (* reading the timestamp field of the node of push b *)
  Lemma rest_ts_read γs pools ctr σ x b :
    tag_of σ x = Some b → x ∈ dom (s_next σ) →
    ts_rest γs pools ctr σ -∗ ∃ w, (x +ₗ 1) ↦ w ∗ ((x +ₗ 1) ↦ w -∗ ts_rest γs pools ctr σ) ∗
      ((⌜w = timestamp_val None ∧ s_TS σ !! b = None⌝) ∨
       (∃ t, ⌜w = timestamp_val (Some t) ∧ s_TS σ !! b = Some t⌝ ∗ b ↪[γ_TS γs]□ t)).
  Proof.
    iIntros (Htag Hx) "(Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners)".
    apply elem_of_dom in Hx as [y Hy].
    iDestruct (big_sepM_lookup_acc with "Hnodes") as "[(H2 & H3 & H1) Hback]"; first done.
    iExists (tsfield σ x). iFrame "H1". iSplitL.
    { iIntros "H1". iFrame "∗ #". iApply "Hback". iFrame. }
    rewrite /tsfield. change (tag_of_l (s_pts σ) x) with (tag_of σ x). rewrite Htag /=.
    destruct (s_TS σ !! b) as [t|] eqn:Ht.
    - iRight. iExists t. iSplit; [done|]. by iApply (big_sepM_lookup with "HTSf").
    - iLeft. done.
  Qed.

  (* the commit of a pop: the taken-CAS on the node x of push b *)
  Lemma rest_commit γs pools ctr σ n b p x j :
    tss_inv n σ → node_of σ b = Some (x, j) →
    ts_rest γs pools ctr σ -∗
    (x +ₗ 3) ↦ #(takenb σ x) ∗
      (((x +ₗ 3) ↦ #(takenb σ x) -∗ ts_rest γs pools ctr σ) ∧
       ((x +ₗ 3) ↦ #true -∗ p ↪[γ_os γs] PopStarted ==∗
          ts_rest γs pools ctr (ev_commit σ b p) ∗ p ↪[γ_os γs] PopCommitted ∗
          own (γ_m γs) (◯ML (s_m σ ++ [(b, p)] : list (leibnizO (positive * positive)))))).
  Proof.
    iIntros (HI Hnode) "(Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners)".
    pose proof (node_of_tag n σ b x j HI Hnode) as Htag.
    pose proof (node_of_dom n σ b x j HI Hnode) as Hx. apply elem_of_dom in Hx as [y Hy].
    iDestruct (big_sepM_delete with "Hnodes") as "[(H2 & H3 & H1) Hnodes]"; first done.
    iFrame "H3". iSplit.
    - iIntros "H3". iFrame "∗ #". iApply (big_sepM_delete with "[$Hnodes H1 H2 H3]"); first done. iFrame.
    - iIntros "H3 Hτ".
      iMod (own_update with "Hm") as "Hm".
      { apply (mono_list_update (s_m σ ++ [(b, p)] : list (leibnizO (positive * positive)))).
        by apply prefix_app_r. }
      iEval (rewrite mono_list_auth_lb_op) in "Hm". iDestruct "Hm" as "[Hm #HmS]".
      iMod (ghost_map_update PopCommitted with "Hos Hτ") as "[Hos Hτ]".
      iModIntro. iFrame "Hτ HmS". rewrite /ts_rest.
      iFrame "Hm Hp Hc Hctr HTS HTSf HK HKf Hos Htops Helems Howners".
      change (s_next (ev_commit σ b p)) with (s_next σ).
      rewrite (big_sepM_delete _ (s_next σ) x y) //. iSplitL "H1 H2 H3".
      { rewrite /node_res (takenb_commit_new σ b p x Htag). iFrame. }
      iApply (big_sepM_mono with "Hnodes"). intros z yz Hz. rewrite /node_res takenb_commit //.
      intros Hzb. apply lookup_delete_Some in Hz as [Hzx _]. apply Hzx. symmetry. by eapply (tag_node n).
  Qed.
End proof.
