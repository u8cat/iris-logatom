(* The resources of the invariant under the other atomic steps: calls and returns, the
   ownership of a pool, the insertion and timestamping of a push, and the start of a pop. *)

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

  Lemma tss_inv_I_ts n σ : tss_inv n σ → I_ts (s_ts σ).
  Proof. intros HI. split; [apply HI|]. exists (s_m σ), (pts_tags σ). apply HI. Qed.

  (* moving the resources of the invariant to an updated state *)
  Lemma nodes_transfer σ σ' (N : gmap loc loc) :
    (∀ x, x ∈ dom N → takenb σ' x = takenb σ x ∧ tsfield σ' x = tsfield σ x) →
    ([∗ map] x ↦ y ∈ N, node_res σ x y) ⊢ [∗ map] x ↦ y ∈ N, node_res σ' x y.
  Proof.
    intros Heq. apply big_sepM_mono. intros x y Hx. rewrite /node_res.
    destruct (Heq x) as [-> ->]; [by apply elem_of_dom_2 with y|done].
  Qed.

  Lemma elems_transfer σ σ' :
    s_ts σ `prefix_of` s_ts σ' →
    ([∗ list] e ∈ s_pts σ, elem_res σ e) ⊢ [∗ list] e ∈ s_pts σ, elem_res σ' e.
  Proof.
    intros Hp. apply big_sepL_mono. intros i [[τ c] [[x j]|]] _; rewrite /elem_res /=; [|done].
    iDestruct 1 as (v) "[Hx %Hin]". iExists v. iFrame. iPureIntro. by eapply elem_of_prefix.
  Qed.

  Lemma owners_transfer γs σ σ' (bs : list bool) :
    (∀ j, length (pool_list σ' j) = length (pool_list σ j)) →
    ([∗ list] j ↦ b ∈ bs, owner_res γs j b (length (pool_list σ j))) ⊢
    [∗ list] j ↦ b ∈ bs, owner_res γs j b (length (pool_list σ' j)).
  Proof. intros Heq. apply big_sepL_mono. intros j b _. by rewrite Heq. Qed.

  Lemma rest_call γs pools ctr σ τ (t : trace) (s : op_state) :
    τ ∉ (s_ts σ).*1 → dom (s_K σ) = events_of_trace (s_ts σ) → dom (s_os σ) = events_of_trace (s_ts σ) →
    ts_rest γs pools ctr σ ==∗
    ts_rest γs pools ctr (ev_call σ τ t s) ∗ τ ↪[γ_os γs] s ∗ τ ↪[γ_K γs]□ (s_c σ).
  Proof.
    iIntros (Hfresh HKd Hosd) "(Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners)".
    assert (Hnin : τ ∉ events_of_trace (s_ts σ)) by (by rewrite /events_of_trace elem_of_list_to_set).
    iMod (ghost_map_insert τ (s_c σ) with "HK") as "[HK Hτk]"; first by apply not_elem_of_dom; rewrite HKd.
    iMod (ghost_map_elem_persist with "Hτk") as "#Hτk".
    iMod (ghost_map_insert τ s with "Hos") as "[Hos Hτs]"; first by apply not_elem_of_dom; rewrite Hosd.
    iModIntro. rewrite /ts_rest /=. iFrame "∗ #".
    iSplitL "".
    { rewrite big_sepM_insert; [by iFrame "#"|]. by apply not_elem_of_dom; rewrite HKd. }
    iApply (elems_transfer with "Helems"). simpl. by apply prefix_app_r.
  Qed.

  (* taking over pool j with its thread ID *)
  Lemma owner_acquire γs pools ctr σ n j :
    tss_inv n σ → j < n →
    own_tid (γ_tid γs) j -∗ ts_rest γs pools ctr σ ==∗
    ts_rest γs pools ctr (ev_busy σ j true) ∗
    ghost_var (γ_O γs !!! j) (1/2) (true, length (pool_list σ j)) ∗
    view γs (s_pts σ) (s_m σ) ∗ last_stamped γs (s_sent σ) (s_pts σ) j.
  Proof.
    iIntros (HI Hj) "Htid (Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners)".
    destruct (ti_len _ _ HI) as (Hls & Hlt & Hlb).
    destruct (lookup_lt_is_Some_2 (s_busy σ) j) as [b Hb]; first lia.
    destruct (lookup_lt_is_Some_2 (s_sent σ) j) as [s Hs]; first lia.
    destruct (lookup_lt_is_Some_2 (s_top σ) j) as [t Ht]; first lia.
    iDestruct (big_sepL_insert_acc with "Howners") as "[[Hhalf Hother] Hback]"; first done.
    destruct b.
    { iDestruct (own_tid_exclusive with "Htid Hother") as %?. done. }
    iMod (ghost_var_update_halves (true, length (pool_list σ j)) with "Hhalf Hother") as "[Hhalf Hmine]".
    iDestruct ("Hback" $! true with "[$Hhalf $Htid]") as "Howners".
    iEval (rewrite mono_list_auth_lb_op) in "Hp". iDestruct "Hp" as "[Hp #HpS]".
    iEval (rewrite mono_list_auth_lb_op) in "Hm". iDestruct "Hm" as "[Hm #HmS]".
    pose proof (po_owner _ _ _ _ _ _ _ _ _ (ti_pool _ _ HI j s t false Hs Ht Hb)) as Howner.
    iModIntro. iFrame "Hmine HpS HmS". rewrite /ts_rest /=. iFrame "∗ #".
    iIntros (x τx [Hx Hτx]).
    destruct (Howner x τx eq_refl Hx Hτx) as [tx Htx].
    iExists tx. by iApply (big_sepM_lookup with "HTSf").
  Qed.

  Lemma owner_agree γs pools ctr σ n j k :
    tss_inv n σ → j < n →
    ghost_var (γ_O γs !!! j) (1/2) (true, k) -∗ ts_rest γs pools ctr σ -∗
    ⌜s_busy σ !! j = Some true ∧ length (pool_list σ j) = k⌝.
  Proof.
    iIntros (HI Hj) "Hmine (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Howners)".
    destruct (ti_len _ _ HI) as (_ & _ & Hlb).
    destruct (lookup_lt_is_Some_2 (s_busy σ) j) as [b Hb]; first lia.
    iDestruct (big_sepL_lookup with "Howners") as "[Hhalf _]"; first done.
    by iDestruct (ghost_var_agree with "Hmine Hhalf") as %[= <- ->].
  Qed.

  (* giving back pool j and its thread ID *)
  Lemma owner_release γs pools ctr σ n j k :
    tss_inv n σ → j < n →
    ghost_var (γ_O γs !!! j) (1/2) (true, k) -∗ ts_rest γs pools ctr σ ==∗
    ts_rest γs pools ctr (ev_busy σ j false) ∗ own_tid (γ_tid γs) j.
  Proof.
    iIntros (HI Hj) "Hmine (Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners)".
    destruct (ti_len _ _ HI) as (Hls & Hlt & Hlb).
    destruct (lookup_lt_is_Some_2 (s_busy σ) j) as [b Hb]; first lia.
    iDestruct (big_sepL_insert_acc with "Howners") as "[[Hhalf Htid] Hback]"; first done.
    iDestruct (ghost_var_agree with "Hmine Hhalf") as %[= <- Hk].
    iMod (ghost_var_update_halves (false, k) with "Hmine Hhalf") as "[Hmine Hhalf]".
    iDestruct ("Hback" $! false with "[Hmine Hhalf]") as "Howners".
    { rewrite /owner_res -Hk. iFrame. }
    iModIntro. iFrame "Htid". rewrite /ts_rest /=. iFrame "∗ #".
  Qed.

  Lemma fresh_node γs pools ctr σ x v :
    (x +ₗ 2) ↦ v -∗ ts_rest γs pools ctr σ -∗ ⌜x ∉ dom (s_next σ)⌝.
  Proof.
    iIntros "Hx (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnodes & _)" (Hin).
    apply elem_of_dom in Hin as [y Hy].
    iDestruct (big_sepM_lookup with "Hnodes") as "[Hx' _]"; first done.
    by iDestruct (pointsto_valid_2 with "Hx Hx'") as %[? _].
  Qed.

  (* the point of a push: its node becomes the top of its pool *)
  Lemma rest_publish γs pools ctr σ n τ (x : loc) j (y : loc) v k :
    tss_inv n σ → j < n → x ∉ dom (s_next σ) → (τ, Call Push v) ∈ s_ts σ →
    ts_rest γs pools ctr σ -∗ τ ↪[γ_os γs] PushCalled -∗ ghost_var (γ_O γs !!! j) (1/2) (true, k) -∗
    ∃ t : loc, (pools +ₗ j) ↦ #t ∗
    ((pools +ₗ j) ↦ #x -∗ x ↦ v -∗ (x +ₗ 1) ↦ timestamp_val None -∗ (x +ₗ 2) ↦ #y -∗ (x +ₗ 3) ↦ #false ==∗
     ts_rest γs pools ctr (ev_publish σ τ x j y) ∗ τ ↪[γ_os γs] PushInserted ∗
     ghost_var (γ_O γs !!! j) (1/2) (true, 1 + k) ∗
     own (γ_pts γs) (◯ML (s_pts σ ++ [(τ, s_c σ, Some (x, j))] : list (leibnizO pt_entry))) ∗
     own (γ_c γs) (◯MN (s_c σ))).
  Proof.
    iIntros (HI Hj Hx Hcall) "(Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners) Hτ Hmine".
    destruct (ti_len _ _ HI) as (Hls & Hlt & Hlb).
    destruct (lookup_lt_is_Some_2 (s_top σ) j) as [t Ht]; first lia.
    destruct (lookup_lt_is_Some_2 (s_sent σ) j) as [s Hs]; first lia.
    destruct (lookup_lt_is_Some_2 (s_busy σ) j) as [b Hb]; first lia.
    iDestruct (ghost_map_lookup with "Hos Hτ") as %Hτos.
    destruct (ti_os _ _ HI τ _ Hτos) as (_ & Hτpts & HτTS).
    assert (Hτm : τ ∉ (s_m σ).*1) by (intros ?; apply Hτpts; by apply (m1_pts n)).
    iDestruct (big_sepL_insert_acc with "Htops") as "[Htop Htops]"; first done.
    iExists t. iFrame "Htop". iIntros "Htop Hx0 Hx1 Hx2 Hx3".
    iSpecialize ("Htops" with "Htop").
    iMod (own_update with "Hp") as "Hp".
    { apply (mono_list_update (s_pts σ ++ [(τ, s_c σ, Some (x, j))] : list (leibnizO pt_entry))).
      by apply prefix_app_r. }
    iEval (rewrite mono_list_auth_lb_op) in "Hp". iDestruct "Hp" as "[Hp #HpS]".
    iEval (rewrite mono_nat_auth_lb_op) in "Hc". iDestruct "Hc" as "[Hc #HcS]".
    iMod (ghost_map_update PushInserted with "Hos Hτ") as "[Hos Hτ]".
    iMod (pointsto_persist with "Hx0") as "#Hx0".
    iDestruct (big_sepL_lookup_acc_impl with "Howners") as "[[Hhalf Htid] Hback]"; first done.
    iDestruct (ghost_var_agree with "Hmine Hhalf") as %[= <- Hk].
    iMod (ghost_var_update_halves (true, 1 + k) with "Hmine Hhalf") as "[Hmine Hhalf]".
    iModIntro. iFrame "Hmine HpS HcS Hτ".
    rewrite /ts_rest. iFrame "Hm Hp Hc Hctr HTS HTSf HK HKf Hos Htops".
    iSplitL "Hnodes Hx1 Hx2 Hx3".
    { change (s_next (ev_publish σ τ x j y)) with (<[x := y]> (s_next σ)).
      rewrite big_sepM_insert; [|by apply not_elem_of_dom].
      iSplitL "Hx1 Hx2 Hx3".
      { rewrite /node_res (takenb_publish_new n) // (tsfield_publish_new n) //. iFrame. }
      iApply (nodes_transfer with "Hnodes"). intros z Hz. assert (z ≠ x) by (intros ->; done).
      split; [by apply takenb_publish|by apply tsfield_publish]. }
    iSplitL "Helems".
    { change (s_pts (ev_publish σ τ x j y)) with (s_pts σ ++ [(τ, s_c σ, Some (x, j))]).
      rewrite big_sepL_snoc. iSplitL "Helems"; [by iApply (elems_transfer with "Helems")|].
      rewrite /elem_res /=. iExists v. iFrame "Hx0". done. }
    change (s_busy (ev_publish σ τ x j y)) with (s_busy σ).
    iApply ("Hback" $! (λ j' b', owner_res γs j' b' (length (pool_list (ev_publish σ τ x j y) j')))
             with "[] [Hhalf Htid]").
    - iIntros "!>" (j' b' Hb' Hj') "Hj'".
      rewrite /pool_list /= pool_list_l_snoc_other; [done|simpl; congruence].
    - rewrite /owner_res /pool_list /= (pool_list_l_snoc _ _ _ _ s Hs) /= decide_True // length_app /=.
      rewrite -/(pool_list σ j) -Hk Nat.add_comm. iFrame.
  Qed.

  (* storing the timestamp of a push *)
  Lemma rest_stamp γs pools ctr σ n τ (x : loc) j t :
    tss_inv n σ → node_of σ τ = Some (x, j) → s_TS σ !! τ = None →
    ts_rest γs pools ctr σ -∗ τ ↪[γ_os γs] PushInserted -∗
    ∃ v0, (x +ₗ 1) ↦ v0 ∗ ((x +ₗ 1) ↦ timestamp_val (Some t) ==∗
      ts_rest γs pools ctr (ev_stamp σ τ t) ∗ τ ↪[γ_os γs] PushStamped ∗ τ ↪[γ_TS γs]□ t).
  Proof.
    iIntros (HI Hnode HTSτ) "(Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners) Hτ".
    pose proof (node_of_tag n σ τ x j HI Hnode) as Htag.
    pose proof (node_of_dom n σ τ x j HI Hnode) as Hx. apply elem_of_dom in Hx as [y Hy].
    iDestruct (big_sepM_delete with "Hnodes") as "[(H2 & H3 & H1) Hnodes]"; first done.
    iExists _. iFrame "H1". iIntros "H1".
    iMod (ghost_map_insert τ t with "HTS") as "[HTS Hτt]"; first done.
    iMod (ghost_map_elem_persist with "Hτt") as "#Hτt".
    iMod (ghost_map_update PushStamped with "Hos Hτ") as "[Hos Hτ]".
    iModIntro. iFrame "Hτ Hτt". rewrite /ts_rest. iFrame "Hm Hp Hc Hctr HTS HK HKf Hos Htops Helems Howners".
    iSplitR.
    { change (s_TS (ev_stamp σ τ t)) with (<[τ := t]> (s_TS σ)). rewrite big_sepM_insert; [by iFrame "#"|done]. }
    change (s_next (ev_stamp σ τ t)) with (s_next σ).
    rewrite (big_sepM_delete _ (s_next σ) x y) //. iSplitL "H1 H2 H3".
    { rewrite /node_res tsfield_stamp_new //. iFrame. }
    iApply (big_sepM_mono with "Hnodes"). intros z yz Hz. rewrite /node_res tsfield_stamp //.
    intros Hzτ. apply lookup_delete_Some in Hz as [Hzx _]. apply Hzx. symmetry. by eapply (tag_node n).
  Qed.

  Lemma rest_ret γs pools ctr σ τ r (s s' : op_state) :
    ts_rest γs pools ctr σ -∗ τ ↪[γ_os γs] s ==∗ ts_rest γs pools ctr (ev_ret σ τ r s') ∗ τ ↪[γ_os γs] s'.
  Proof.
    iIntros "(Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners) Hτ".
    iMod (ghost_map_update s' with "Hos Hτ") as "[Hos Hτ]".
    iModIntro. iFrame "Hτ". rewrite /ts_rest /=. iFrame "∗ #".
    iApply (elems_transfer with "Helems"). simpl. by apply prefix_app_r.
  Qed.

  Lemma rest_point γs pools ctr σ p :
    ts_rest γs pools ctr σ -∗ p ↪[γ_os γs] PopCalled ==∗
    ts_rest γs pools ctr (ev_point σ p) ∗ p ↪[γ_os γs] PopStarted ∗
    own (γ_pts γs) (◯ML (s_pts σ ++ [(p, s_c σ, None)] : list (leibnizO pt_entry))) ∗
    own (γ_c γs) (◯MN (s_c σ)).
  Proof.
    iIntros "(Hm & Hp & Hc & Hctr & HTS & #HTSf & HK & #HKf & Hos & Htops & Hnodes & Helems & Howners) Hτ".
    iMod (own_update with "Hp") as "Hp".
    { apply (mono_list_update (s_pts σ ++ [(p, s_c σ, None)] : list (leibnizO pt_entry))). by apply prefix_app_r. }
    iEval (rewrite mono_list_auth_lb_op) in "Hp". iDestruct "Hp" as "[Hp #HpS]".
    iEval (rewrite mono_nat_auth_lb_op) in "Hc". iDestruct "Hc" as "[Hc #HcS]".
    iMod (ghost_map_update PopStarted with "Hos Hτ") as "[Hos Hτ]".
    iModIntro. iFrame "Hτ HpS HcS". rewrite /ts_rest.
    iFrame "Hm Hp Hc Hctr HTS HTSf HK HKf Hos Htops".
    iSplitL "Hnodes".
    { iApply (nodes_transfer with "Hnodes"). intros z _.
      rewrite /takenb /tsfield /tag_of /= takenb_l_snoc_ne // tag_of_l_snoc_ne //. }
    iSplitL "Helems".
    { change (s_pts (ev_point σ p)) with (s_pts σ ++ [(p, s_c σ, None)]).
      rewrite big_sepL_snoc. iSplitL; [by iApply (elems_transfer with "Helems")|]. done. }
    iApply (owners_transfer with "Howners"). intros j.
    rewrite /pool_list /= pool_list_l_snoc_other //.
  Qed.
End proof.
