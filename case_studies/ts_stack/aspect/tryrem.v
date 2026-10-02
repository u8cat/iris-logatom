(* tryRem: the scan of all pools for the youngest candidate, the eliminations, and the
   emptiness check. *)

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
From case_studies.ts_stack.aspect Require Import pure defs resources timestamp youngest remove check.

(* the first loop of tsstack_tryRem, after the substitution of its free variables *)
Definition scan_loop (pools empty : loc) (n s1 s2 : nat) : val :=
  rec: "loop" "ID" "youngest" "timestamp" "pool" "top" :=
    if: "ID" ≠ #n then
      let: "current" := #pools +ₗ "ID" in
      let: "tmp" := sppool_get_youngest "current" in
      let: "node" := Fst "tmp" in
      let: "poolTop" := Snd "tmp" in
      match: "node" with
        NONE => #empty +ₗ "ID" <- "poolTop";;
        "loop" ("ID" + #1) "youngest" "timestamp" "pool" "top"
      | SOME "node" =>
          let: "nodeTimestamp" := ! ("node" +ₗ #1) in
          if: timestamp_lt (#s1, #s2)%V "nodeTimestamp" then
            impl.wrap_nonempty_result (sppool_remove "current" "poolTop" "node")
          else if: timestamp_lt "timestamp" "nodeTimestamp" then
            "loop" ("ID" + #1) (SOME "node") "nodeTimestamp" "current" "poolTop"
          else
            "loop" ("ID" + #1) "youngest" "timestamp" "pool" "top"
      end
    else
      match: "youngest" with
        NONE =>
        (rec: "loop" "ID" :=
          if: "ID" ≠ #n then
            let: "current" := #pools +ₗ "ID" in
            if: ! "current" ≠ ! (#empty +ₗ "ID") then NONE else "loop" ("ID" + #1)
          else SOME NONE) #0
      | SOME "youngest" =>
        impl.wrap_nonempty_result (sppool_remove "pool" "top" "youngest")
      end.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  Lemma pool_wit_scan_ok γs pools ctr σ n sents p j w :
    tss_inv n σ → s_sent σ = sents →
    ts_rest γs pools ctr σ -∗ pool_wit γs sents p j w -∗
    ⌜scan_ok σ p j (match w.2 with Some (_, k, t) => Some (k, t) | None => None end)⌝.
  Proof.
    iIntros (HI Hsent) "Hrest Hw". destruct w as [A [[[x k] t]|]]; simpl.
    - iDestruct "Hw" as "[Hw Hst]".
      iDestruct "Hw" as (pS pT mT) "(HpS & HvT & %HppS & %Hwr)".
      iDestruct "Hst" as (pX τ) "(HpX & %Hτ & Hτt)".
      iDestruct (rest_pts_valid with "Hrest HpS") as %HpS.
      iDestruct (rest_pts_valid with "Hrest HpX") as %HpX.
      iDestruct (rest_view_valid with "Hrest HvT") as %[HpT HmT].
      iDestruct (rest_TS_lookup with "Hrest Hτt") as %HTS.
      iPureIntro. destruct Hwr as (_ & ia & HA & Hx & _ & Habove).
      rewrite /pool_list_l in HA Hx Habove.
      destruct (sents !! j) as [s|] eqn:Hs; [|by rewrite lookup_nil in HA].
      exists pS, s. split_and!; [done|done|by rewrite Hsent|].
      exists x, τ. split_and!; [done|exact (tag_of_l_prefix _ _ _ _ HpX Hτ)|done|].
      intros i z Hi Hz. eapply (taken_snapshot σ); [exact HpT|exact HmT|]. rewrite Hsent. exact (Habove i z Hi Hz).
    - iDestruct "Hw" as (pS pT mT) "(HpS & HvT & %HppS & %Hwr)".
      iDestruct (rest_pts_valid with "Hrest HpS") as %HpS.
      iDestruct (rest_view_valid with "Hrest HvT") as %[HpT HmT].
      iPureIntro. destruct Hwr as (_ & ia & HA & Hall).
      rewrite /pool_list_l in HA Hall.
      destruct (sents !! j) as [s|] eqn:Hs; [|by rewrite lookup_nil in HA].
      exists pS, s. split_and!; [done|done|by rewrite Hsent|].
      intros x Hx. eapply (taken_snapshot σ); [exact HpT|exact HmT|]. rewrite Hsent. by apply Hall.
  Qed.

  Lemma pool_wits_scan_ok γs pools ctr σ n sents p (ws : list wentry) :
    tss_inv n σ → s_sent σ = sents →
    ts_rest γs pools ctr σ -∗ ([∗ list] j ↦ w ∈ ws, pool_wit γs sents p j w) -∗
    ⌜∀ j, j < length ws → scan_ok σ p j (res_of ws j)⌝.
  Proof.
    iIntros (HI Hsent) "Hrest #Hws". iIntros (j Hj).
    destruct (lookup_lt_is_Some_2 ws j Hj) as [w Hw].
    iDestruct (big_sepL_lookup with "Hws") as "Hw"; first done.
    iDestruct (pool_wit_scan_ok with "Hrest Hw") as %Hok; [done|done|].
    iPureIntro. rewrite /res_of Hw. destruct w as [A [[[x k] t]|]]; exact Hok.
  Qed.

  (* the youngest candidate of a complete scan *)
  Lemma lifo_normal γs n pools ctr sents tracer p (ws : list wentry) (y A : loc) jy ky tb :
    length ws = n → ws !! jy = Some (A, Some (y, ky, tb)) →
    (∀ j A' x k t, ws !! j = Some (A', Some (x, k, t)) → ¬ tb.2 < t.1) →
    ([∗ list] j ↦ w ∈ ws, pool_wit γs sents p j w) -∗ lifo_wit γs n pools ctr sents tracer y p.
  Proof.
    iIntros (Hlen Hjy Hyoung) "#Hws". iIntros "!>" (σ b [HI [Hsent Htag]]) "Htr Hrest".
    iDestruct (pool_wits_scan_ok with "Hrest Hws") as %Hscan; [done|done|].
    iDestruct (big_sepL_lookup with "Hws") as "Hw"; first exact Hjy.
    iEval (rewrite /pool_wit) in "Hw". iDestruct "Hw" as "[_ Hst]".
    iDestruct "Hst" as (pX τ) "(HpX & %Hτ & Hτt)".
    iDestruct (rest_pts_valid with "Hrest HpX") as %HpX.
    iDestruct (rest_TS_lookup with "Hrest Hτt") as %HTS.
    pose proof (tag_of_l_prefix _ _ _ _ HpX Hτ) as Hτ'.
    rewrite /tag_of in Htag. rewrite Htag in Hτ'. injection Hτ' as <-.
    iPureIntro. intros _ c _ Hts Hc Hcp.
    assert (Hscan' : ∀ j, j < n → scan_ok σ p j (res_of ws j)) by (intros j Hj; apply Hscan; lia).
    assert (Hyoung' : ∀ j k t, j < n → res_of ws j = Some (k, t) → ¬ tb.2 < t.1).
    { intros j k t Hj Hr. rewrite /res_of in Hr.
      destruct (ws !! j) as [[A' [[[x k'] t']|]]|] eqn:Hw; try done.
      injection Hr as <- <-. by eapply Hyoung. }
    exact (commit_lifo n σ p b tb (res_of ws) HI Hscan' HTS Hyoung' (tag_push n σ y b HI Htag) c Hts Hc Hcp).
  Qed.

  (* a candidate without a timestamp: its push overlaps the pop *)
  Lemma lifo_unstamped γs n pools ctr sents tracer p σr (x : loc) b :
    tss_inv n σr → tag_of σr x = Some b → (p, Call Pop #()) ∈ s_ts σr → s_TS σr !! b = None →
    hist tracer (s_ts σr) -∗ own (γ_pts γs) (◯ML (s_pts σr : list (leibnizO pt_entry))) -∗
    lifo_wit γs n pools ctr sents tracer x p.
  Proof.
    iIntros (HIr Htagr Hp HTS) "#Hh #Hpr". iIntros "!>" (σ b' [HI [Hsent Htag]]) "Htr Hrest".
    iDestruct (hist_trace_is_prefix with "Htr Hh") as %Hpre.
    iDestruct (rest_pts_valid with "Hrest Hpr") as %Hpts.
    pose proof (tag_of_l_prefix _ _ _ _ Hpts Htagr) as Htag'.
    rewrite /tag_of in Htag. rewrite Htag in Htag'. injection Htag' as ->.
    iPureIntro. intros Hpre'. exfalso.
    exact (elim_unstamped n σr σ b p HIr Hpre Hp (tag_push n σr x b HIr Htagr) HTS Hpre').
  Qed.

  (* a candidate with a timestamp later than the start time of the pop *)
  Lemma lifo_stamped γs n pools ctr sents tracer p σr (x : loc) b t kp s1 s2 :
    tag_of σr x = Some b → kp ≤ s1 → s1 ≤ s2 → s2 < t.1 →
    own (γ_pts γs) (◯ML (s_pts σr : list (leibnizO pt_entry))) -∗ b ↪[γ_TS γs]□ t -∗ p ↪[γ_K γs]□ kp -∗
    lifo_wit γs n pools ctr sents tracer x p.
  Proof.
    iIntros (Htagr Hk Hs Hlt) "#Hpr #Hbt #Hpk". iIntros "!>" (σ b' [HI [Hsent Htag]]) "Htr Hrest".
    iDestruct (rest_pts_valid with "Hrest Hpr") as %Hpts.
    iDestruct (rest_TS_lookup with "Hrest Hbt") as %HTS.
    iDestruct (rest_K_lookup with "Hrest Hpk") as %HK.
    pose proof (tag_of_l_prefix _ _ _ _ Hpts Htagr) as Htag'.
    rewrite /tag_of in Htag. rewrite Htag in Htag'. injection Htag' as ->.
    iPureIntro. intros Hpre. exfalso.
    exact (elim_stamped n σ b p t kp s1 s2 HI (tag_push n σ x b HI Htag) HTS HK Hk Hs Hlt Hpre).
  Qed.

  Lemma scan_loop_spec γs n pools ctr sents tracer p (pP : list pt_entry) kp (s1 s2 : nat) tsP
      (empty : loc) (i : nat) (ws : list wentry) (es : list val) (yv cv pv tv : val) :
    0 < n → length sents = n → p ∈ (λ e : pt_entry, e.1.1) <$> pP → kp ≤ s1 ≤ s2 →
    (p, Call Pop #()) ∈ tsP →
    i ≤ n ∧ length ws = i ∧ length es = n ∧ youngest_ok pools ws yv cv pv tv ∧
      (∀ j (A : loc), ws !! j = Some (A, None) → es !! j = Some #A) →
    {{{ inv tsN (ts_inv γs n pools ctr sents tracer) ∗ own (γ_pts γs) (◯ML (pP : list (leibnizO pt_entry))) ∗
        p ↪[γ_K γs]□ kp ∗ hist tracer tsP ∗ empty ↦∗ es ∗ p ↪[γ_os γs] PopStarted ∗
        [∗ list] j ↦ w ∈ ws, pool_wit γs sents p j w }}}
      scan_loop pools empty n s1 s2 #i yv cv pv tv
    {{{ w, RET w; tryRem_post γs tracer sents n p w }}}.
  Proof.
    iIntros (Hn Hlen HppP Hks HpP' Hinv Φ) "(#Hinv & #HpP & #Hpk & #HhP & Hes & Hp & #Hws) HΦ".
    iLöb as "IH" forall (i ws es yv cv pv tv Hinv) "Hws".
    destruct Hinv as (Hi & Hwsl & Hesl & Hyoung & Hes0).
    wp_rec. wp_pures.
    destruct (decide (i = n)) as [->|Hin].
    { (* the scan is over *)
      rewrite bool_decide_eq_true_2 //. wp_pure (If _ _ _).
      destruct Hyoung as [(-> & -> & Hnone)|(y & jy & A & ky & tb & -> & -> & -> & -> & Hjy & Hmax)].
      - (* no candidate: check that the pools did not change *)
        wp_pure (Case _ _ _). wp_pure (Rec _ _ _). wp_pure (App _ _). wp_pure (Rec _ _ _).
        (* the end of the scan *)
        iApply fupd_wp.
        iInv "Hinv" as (σT) "(>[%HIT %HsentT] & >Htr & >Hrest)" "Hclose".
        iDestruct (alloc_hist with "Htr") as "[Htr #HhT]".
        iDestruct (hist_trace_is_prefix with "Htr HhP") as %HtsPT.
        iDestruct (rest_view_get with "Hrest") as "[Hrest #HvT]".
        iAssert (⌜∀ j (A : loc), ws !! j = Some (A, None) → ∃ pS pTw mTw, pS `prefix_of` s_pts σT ∧
                   pTw `prefix_of` s_pts σT ∧ mTw `prefix_of` s_m σT ∧ walk_res sents pS pTw mTw j A None⌝)%I
          as %HET.
        { iIntros (j A Hw). iDestruct (big_sepL_lookup with "Hws") as "Hw"; first exact Hw.
          iEval (rewrite /pool_wit) in "Hw".
          iDestruct "Hw" as (pS pTw mTw) "(HpS & HvTw & _ & %Hwr)".
          iDestruct (rest_pts_valid with "Hrest HpS") as %?.
          iDestruct (rest_view_valid with "Hrest HvTw") as %[? ?].
          iPureIntro. by exists pS, pTw, mTw. }
        iMod ("Hclose" with "[Htr Hrest]") as "_".
        { iNext. iExists σT. iFrame "Htr Hrest". done. }
        iModIntro.
        set (tsT := s_ts σT). set (mT := s_m σT). set (pT := s_pts σT).
        assert (HwT : (p, Call Pop #()) ∈ tsT ∧
          (∀ τ1 r v, (τ1, Ret r) ∈ tsT → (τ1, Call Push v) ∈ tsT → ∃ c x j, (τ1, c, Some (x, j)) ∈ pT) ∧
          (∀ τ2, τ2 ∈ mT.*2 → (τ2, Call Pop #()) ∈ tsT) ∧
          (∀ τ c x j, (τ, c, Some (x, j)) ∈ pT → j < n)).
        { split_and!.
          - by eapply elem_of_prefix.
          - intros τ1 r v Hr Hc. exact (returned_push_pt n σT τ1 r v HIT Hr Hc).
          - intros τ2 ([b' τ2'] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst τ2'.
            exact (valid_match_call_pop _ _ _ _ (isv_valid _ _ _ (ti_stack _ _ HIT)) Hin).
          - intros τ c x j Hin. exact (ti_pts_pool _ _ HIT τ c x j Hin). }
        assert (Hall : ∀ j, j < n → ∃ A : loc, es !! j = Some #A ∧ ∃ pS pTw mTw, pS `prefix_of` pT ∧
                  pTw `prefix_of` pT ∧ mTw `prefix_of` mT ∧ walk_res sents pS pTw mTw j A None).
        { intros j Hj. destruct (lookup_lt_is_Some_2 ws j) as [[A ro] Hwj]; first lia.
          assert (ro = None) as -> by exact (Hnone j (A, ro) Hwj).
          exists A. split; [exact (Hes0 j A Hwj)|exact (HET j A Hwj)]. }
        iApply (check_loop_spec γs n pools ctr sents tracer p empty es tsT mT pT 0 Hlen Hall HwT
                  ltac:(lia) with "[$Hinv $HhT $HvT $Hes $Hp] HΦ").
        by rewrite big_sepL_nil.
      - (* remove the youngest candidate *)
        wp_pure (Case _ _ _). wp_pure (Rec _ _ _). wp_pure (App _ _).
        iDestruct (big_sepL_lookup with "Hws") as "Hw"; first exact Hjy.
        iEval (rewrite /pool_wit) in "Hw". iDestruct "Hw" as "[Hwalk _]".
        iPoseProof (lifo_normal γs n pools ctr sents tracer p ws y A jy ky tb with "Hws") as "Hlifo";
          [done|done|done|].
        assert (Hjyn : jy < n) by (rewrite -Hwsl; by eapply lookup_lt_Some).
        wp_apply (sppool_remove_spec γs n pools ctr sents tracer p jy A y ky with "[$Hinv $Hp $Hwalk $Hlifo]")
          as (w) "Hw'"; first done.
        wp_lam. iDestruct "Hw'" as "[[-> Hp]|(%b' & %v & %mC & %tsC & (-> & %Hbp & %Hbv) & Hp & HmC & Hh)]".
        + wp_pures. iModIntro. iApply "HΦ". iLeft. by iFrame.
        + wp_pures. iModIntro. iApply "HΦ". iRight. iLeft. iExists b', v, mC, tsC. by iFrame. }
    (* the scan of pool i *)
    rewrite bool_decide_eq_false_2; last (intros [= ?]; lia). wp_pures.
    wp_apply (get_youngest_spec γs n pools ctr sents tracer i p pP with "[$Hinv $HpP]") as (ro A) "#Hwalk".
    { iPureIntro. split; [lia|done]. }
    destruct ro as [[x k]|]; rewrite /opt_node; wp_pures; last first.
    { (* pool i is empty *)
      wp_apply (wp_store_offset with "Hes") as "Hes"; first (apply lookup_lt_is_Some_2; lia).
      wp_seq. wp_pure (BinOp _ _ _).
      replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1)) by lia.
      iApply ("IH" $! (i + 1) (ws ++ [(A, None)]) (<[i := #A]> es) yv cv pv tv with "[%] Hes Hp HΦ").
      - split_and!; [lia|rewrite length_app /=; lia|by rewrite length_insert|by apply youngest_ok_none|].
        intros j A' [Hw|[Hlen' Hw]]%lookup_app_Some.
        + rewrite list_lookup_insert_ne; [by apply Hes0|]. apply lookup_lt_Some in Hw.
          rewrite Hwsl in Hw. lia.
        + apply list_lookup_singleton_Some in Hw as [Hj0 Heq]. injection Heq as ->.
          rewrite Hwsl in Hj0 Hlen'. replace j with i by lia. rewrite list_lookup_insert_eq //. lia.
      - rewrite big_sepL_snoc Hwsl. by iFrame "Hws Hwalk". }
    (* a candidate: read its timestamp *)
    wp_bind (! _)%E.
    iPoseProof "Hwalk" as (pS pT mT) "(#HpS & #HvT & %HppS & %Hwr)".
    destruct Hwr as (_ & ia & HA & Hx & [Hk1 Hkia] & _).
    iInv "Hinv" as (σr) "(>[%HIr %Hsentr] & >Htr & >Hrest)" "Hclose".
    iDestruct (rest_pts_valid with "Hrest HpS") as %HpSr.
    assert (Hxr : pool_list σr i !! k = Some x).
    { eapply prefix_lookup_Some; [exact Hx|]. by apply pool_list_snap. }
    destruct (pool_node_tag n σr i k x HIr Hk1 Hxr) as (b & Htagr & Hnoder & Hpushr).
    iDestruct (rest_view_get with "Hrest") as "[Hrest #Hvr]".
    iAssert (own (γ_pts γs) (◯ML (s_pts σr : list (leibnizO pt_entry))))%I as "#Hpr".
    { by iDestruct "Hvr" as "[$ _]". }
    iDestruct (alloc_hist with "Htr") as "[Htr #Hhr]".
    iDestruct (hist_trace_is_prefix with "Htr HhP") as %HtsPr.
    iDestruct (rest_ts_read _ _ _ σr x b with "Hrest") as (w) "(Hn1 & Hback & Hcase)"; [done| |].
    { eapply (pool_list_in_dom n); [done|]. by eapply list_elem_of_lookup_2. }
    wp_load.
    iMod ("Hclose" with "[Htr Hn1 Hback]") as "_".
    { iNext. iExists σr. iFrame "Htr". iSplit; [done|]. by iApply "Hback". }
    iModIntro. wp_pures.
    assert (HpPr : (p, Call Pop #()) ∈ s_ts σr) by (by eapply elem_of_prefix).
    iDestruct "Hcase" as "[[-> %HTSr]|(%t & [-> %HTSr] & #Hbt)]".
    { (* no timestamp yet: the push overlaps the pop, eliminate *)
      wp_apply (timestamp_lt_top_spec s1 s2 with "[//]") as "_". wp_pures.
      iPoseProof (lifo_unstamped γs n pools ctr sents tracer p σr x b HIr Htagr HpPr HTSr with "Hhr Hpr")
        as "Hlifo".
      wp_apply (sppool_remove_spec γs n pools ctr sents tracer p i A x k with "[$Hinv $Hp $Hwalk $Hlifo]")
        as (w') "Hw'"; first (iPureIntro; lia).
      wp_lam. iDestruct "Hw'" as "[[-> Hp]|(%b' & %v & %mC & %tsC & (-> & %Hbp & %Hbv) & Hp & HmC & Hh)]".
      - wp_pures. iModIntro. iApply "HΦ". iLeft. by iFrame.
      - wp_pures. iModIntro. iApply "HΦ". iRight. iLeft. iExists b', v, mC, tsC. by iFrame. }
    destruct t as [t1 t2].
    wp_apply (timestamp_lt_spec s1 s2 t1 t2 with "[//]") as "_".
    destruct (decide (s2 < t1)) as [Hlt|Hge].
    { (* younger than the start of the pop: eliminate *)
      rewrite bool_decide_eq_true_2 //. wp_pures.
      iPoseProof (lifo_stamped γs n pools ctr sents tracer p σr x b (t1, t2) kp s1 s2 Htagr
                    with "Hpr Hbt Hpk") as "Hlifo"; [lia|lia|simpl; lia|].
      wp_apply (sppool_remove_spec γs n pools ctr sents tracer p i A x k with "[$Hinv $Hp $Hwalk $Hlifo]")
        as (w') "Hw'"; first (iPureIntro; lia).
      wp_lam. iDestruct "Hw'" as "[[-> Hp]|(%b' & %v & %mC & %tsC & (-> & %Hbp & %Hbv) & Hp & HmC & Hh)]".
      - wp_pures. iModIntro. iApply "HΦ". iLeft. by iFrame.
      - wp_pures. iModIntro. iApply "HΦ". iRight. iLeft. iExists b', v, mC, tsC. by iFrame. }
    rewrite bool_decide_eq_false_2 //. wp_pures.
    (* compare with the youngest candidate so far *)
    destruct (ti_TS _ _ HIr b (t1, t2) HTSr) as (_ & _ & _ & Ht12 & _). simpl in Ht12.
    pose proof (TS_pos n σr b (t1, t2) HIr HTSr) as Ht1. simpl in Ht1.
    iAssert (pool_wit γs sents p i (A, Some (x, k, (t1, t2))))%I as "#Hwi".
    { rewrite /pool_wit. iFrame "Hwalk". iExists (s_pts σr), b. by iFrame "Hpr Hbt". }
    destruct Hyoung as [(-> & -> & Hnone)|(y & jy & Ay & ky & tb & -> & -> & -> & -> & Hjy & Hmax)].
    - wp_apply (timestamp_lt_spec 0 0 t1 t2 with "[//]") as "_".
      rewrite bool_decide_eq_true_2; last lia.
      wp_pure (If _ _ _). wp_pure (InjR _). wp_pure (BinOp _ _ _).
      replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1)) by lia.
      iApply ("IH" $! (i + 1) (ws ++ [(A, Some (x, k, (t1, t2)))]) es with "[%] Hes Hp HΦ").
      + split_and!; [lia|rewrite length_app /=; lia|done| |].
        * rewrite -Hwsl. apply youngest_ok_new; [done|]. intros j A' x' k' t' Hw.
          by specialize (Hnone _ _ Hw).
        * intros j A' [Hw|[_ Hw]]%lookup_app_Some; [by apply Hes0|].
          apply list_lookup_singleton_Some in Hw as [_ ?]. by simplify_eq.
      + rewrite big_sepL_snoc Hwsl. by iFrame "Hws Hwi".
    - wp_apply (timestamp_lt_spec tb.1 tb.2 t1 t2 with "[//]") as "_".
      destruct (decide (tb.2 < t1)) as [Hyt|Hyt].
      + rewrite bool_decide_eq_true_2 //.
        wp_pure (If _ _ _). wp_pure (InjR _). wp_pure (BinOp _ _ _).
        replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1)) by lia.
        iApply ("IH" $! (i + 1) (ws ++ [(A, Some (x, k, (t1, t2)))]) es with "[%] Hes Hp HΦ").
        * split_and!; [lia|rewrite length_app /=; lia|done| |].
          -- rewrite -Hwsl. apply youngest_ok_new; [done|]. intros j A' x' k' t' Hw.
             specialize (Hmax _ _ _ _ _ Hw). simpl. lia.
          -- intros j A' [Hw|[_ Hw]]%lookup_app_Some; [by apply Hes0|].
             apply list_lookup_singleton_Some in Hw as [_ ?]. by simplify_eq.
        * rewrite big_sepL_snoc Hwsl. by iFrame "Hws Hwi".
      + rewrite bool_decide_eq_false_2 //.
        wp_pure (If _ _ _). wp_pure (BinOp _ _ _).
        replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1)) by lia.
        iApply ("IH" $! (i + 1) (ws ++ [(A, Some (x, k, (t1, t2)))]) es with "[%] Hes Hp HΦ").
        * split_and!; [lia|rewrite length_app /=; lia|done| |].
          -- apply (youngest_ok_keep pools ws A x k (t1, t2) y jy Ay ky tb); [done|done|simpl; lia].
          -- intros j A' [Hw|[_ Hw]]%lookup_app_Some; [by apply Hes0|].
             apply list_lookup_singleton_Some in Hw as [_ ?]. by simplify_eq.
        * rewrite big_sepL_snoc Hwsl. by iFrame "Hws Hwi".
  Qed.

  Lemma tryRem_spec γs n pools ctr sents tracer (tpl : val) p (pP : list pt_entry) kp (s1 s2 : nat) tsP :
    {{{ inv tsN (ts_inv γs n pools ctr sents tracer) ∗ ⌜0 < n ∧ length sents = n⌝ ∗
        p ↪[γ_os γs] PopStarted ∗ own (γ_pts γs) (◯ML (pP : list (leibnizO pt_entry))) ∗
        ⌜p ∈ (λ e : pt_entry, e.1.1) <$> pP⌝ ∗ p ↪[γ_K γs]□ kp ∗ ⌜kp ≤ s1 ≤ s2⌝ ∗
        hist tracer tsP ∗ ⌜(p, Call Pop #()) ∈ tsP⌝ }}}
      tsstack_tryRem (#pools, #ctr, tpl, #n)%V (#s1, #s2)%V
    {{{ w, RET w; tryRem_post γs tracer sents n p w }}}.
  Proof.
    iIntros (Φ) "(#Hinv & [%Hn %Hlen] & Hp & #HpP & %HppP & #Hpk & %Hks & #HhP & %HpP') HΦ".
    wp_lam. wp_pures.
    wp_apply (wp_allocN with "[//]") as (empty) "[Hes _]"; first lia.
    rewrite Nat2Z.id.
    wp_let. wp_pure (InjL _). wp_pure (Rec _ _ _).
    assert (Hinit : 0 ≤ n ∧ length ([] : list wentry) = 0 ∧ length (replicate n #(Loc 0)) = n ∧
      youngest_ok pools [] NONEV (#0, #0)%V #(Loc 0) #(Loc 0) ∧
      ∀ j (A : loc), ([] : list wentry) !! j = Some (A, None) → replicate n #(Loc 0) !! j = Some #A).
    { split_and!; [lia|done|by rewrite length_replicate|by left|]. intros j A Hj. by rewrite lookup_nil in Hj. }
    iAssert ([∗ list] j ↦ w ∈ ([] : list wentry), pool_wit γs sents p j w)%I as "Hnil"; first done.
    iApply (scan_loop_spec γs n pools ctr sents tracer p pP kp s1 s2 tsP empty 0 [] _ NONEV (#0, #0)%V _ _
              Hn Hlen HppP Hks HpP' Hinit with "[$Hinv $HpP $Hpk $HhP $Hes $Hp $Hnil] HΦ").
  Qed.
End proof.
