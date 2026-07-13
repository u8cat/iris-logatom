(* enq.v — Enqueue wrapper spec. *)

From stdpp Require Import base list gmap propset.
From iris_logatom.pure_logic Require Import linear.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.metaconfig Require Import tracking.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants ghost_map ghost_var.
From iris.heap_lang Require Import notation proofmode diverge.
From iris_logatom.heap_lang Require Import mgc.

From case_studies.hw_queue Require Import impl.
From case_studies.hw_queue.metaconfig Require Import defs lemmas.
Import HWQMetaConfigNotation.
Local Existing Instance propset_signle_config_q_leibniz_equiv.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !hwqMcG Σ}.

  Lemma phase1_call_preserves_I_lang ts τ v_push :
    val_is_unboxed (SOMEV v_push) →
    τ ∉ ts.*1 →
    I_lang_hwq ts →
    I_lang_hwq (ts ++ [(τ, Call (encode_request (Push v_push)))]).
  Proof.
    intros Hunb Hfresh [(M' & s & π & Hsteps & Hin) Hwf].
    split; last by apply per_tag_wellformed_snoc_call_push.
    set (M'_new := ((λ x : single_config_q,
                       (x.1, <[τ:=(encode_request (Push v_push), None)]> x.2))
                      <$> M' : @meta_config hwq_model)).
    exists M'_new, s, (<[τ:=(encode_request (Push v_push), None)]> π).
    split.
    - eapply mcfg_steps_snoc; first exact Hsteps.
      replace M'_new with ((λ '(s', π'), (s', <[τ:=(encode_request (Push v_push), None)]> π'))
                            <$> M').
      2: { unfold M'_new. apply leibniz_equiv. intros [s_x π_x].
           rewrite !elem_of_PropSet. split.
           - intros ([s_y π_y] & Heq & Hin_y). simpl in Heq.
             eexists (_, _). simpl. split; first exact Heq. exact Hin_y.
           - intros ([s_y π_y] & Heq & Hin_y). simpl in Heq.
             eexists (_, _). simpl. split; first exact Heq. exact Hin_y. }
      apply (mcfg_step_call M' τ).
      + intros [s' π'] Hin_pre. simpl.
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hsteps Hin_pre) as Hdom_sub.
        intros Hin_dom. apply Hdom_sub in Hin_dom.
        apply elem_of_list_to_set in Hin_dom. contradiction.
      + left. exists v_push. done.
    - apply elem_of_PropSet. eexists (s, π). split; [done | exact Hin].
  Qed.

  Lemma phase4_ret_preserves_I_lang ts τ v_push :
    I_lang_hwq ts →
    filter (λ t, t.1 = τ) ts = [(τ, Call (encode_request (Push v_push)))] →
    (∃ (M_full : @meta_config hwq_model) s π,
        mcfg_steps mcfg_init M_full ts ∧ (s, π) ∈ M_full ∧
        π !! τ = Some (encode_request (Push v_push), Some #())) →
    I_lang_hwq (ts ++ [(τ, Ret #())]).
  Proof.
    intros [_ Hwf] Hfilter (M_full & s & π & Hsteps & Hin & Hπτ).
    split.
    - (* I_metaconfig: extend via mcfg_step_ret. *)
      set (M_full_new := (M_full ∩
        {[ (_, π') | snd <$> (π' !! τ) = Some (Some #()) ]})
        : @meta_config hwq_model).
      exists M_full_new, s, π.
      split.
      + eapply mcfg_steps_snoc; first exact Hsteps.
        apply (mcfg_step_ret M_full τ #()).
      + apply elem_of_intersection. split; first exact Hin.
        apply elem_of_PropSet. rewrite Hπτ /=. reflexivity.
    - by eapply per_tag_wellformed_snoc_ret.
  Qed.

  Lemma push_wrapper_spec γ tracer (q v_push : val) :
    val_is_unboxed (SOMEV v_push) →
    {{{ trace_inv tracer I_lang_hwq ∗ is_hwq tracer γ q }}}
      call_ret_wrapper tracer op q (encode_request (Push v_push))
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Hunb Φ) "[#Itrace #Ihwq] HΦ".
    rewrite /call_ret_wrapper.
    iDestruct "Ihwq" as (γM γ_status γ_slots γ_scan sz ar back) "(-> & %Hsz_nn & #Hmeta & #Hinv)".
    wp_pures.

    (* ──────────────────────────────────────────────────────────────────
       Phase 1 — trace_fresh: emit (τ, Call (Push v_push)).
       ──────────────────────────────────────────────────────────────── *)
    wp_bind (trace_fresh _ _).
    awp_apply (trace_fresh_spec _ (Call (encode_request (Push v_push)))
                (InjLV (encode_request (Push v_push))) I_lang_hwq with "Itrace");
      first reflexivity.
    iInv "Hinv" as (items back_val ts M_g stat slots scan_map)
      "(>Hback & >Har & >Hts & >%Hlen & >%Hbpos & >HγM & >Hstat & >Hslots & >Hscan & #Hslots_persist1 &
         >%Hmcfg_steps & >%Hne & >%Hpw & >%Hsc & >%Hsc_slots & >%Hwell & >%Htrst & >%Hlinw_seq & >%Hbnd & >%Hssi & >%Hcl_push & >%Hscan_dom & >%Hscan_lb)".
    iApply (fupd_mask_intro); first solve_ndisj. iIntros "Hclose_fupd".
    iFrame "Hts". iSplit.
    { (* Universal precondition. *)
      iPureIntro. intros τ Hfresh.
      apply phase1_call_preserves_I_lang; auto.
      split.
      - apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        exists (set_to_propset M_g), s_w, π_w. split; auto.
      - exact Hpw. }
    iSplit.
    { (* Abort branch: re-establish the invariant. *)
      iIntros "[Hts _]". iMod "Hclose_fupd" as "_". iModIntro.
      iSplitR "HΦ"; last done.
      iNext. iExists items, back_val, ts, M_g, stat, slots, scan_map.
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist1".
      iPureIntro. split_and!; assumption. }
    (* Commit branch. *)
    iIntros (τ) "[Hts %Hfresh]". iMod "Hclose_fupd" as "_".
    (* Update M_g via gset insert on each element. *)
    pose (M_g_new :=
      (set_map (λ x : single_config_q,
                  (x.1, <[τ:=(encode_request (Push v_push), None)]> x.2))
              M_g : gset single_config_q)).
    iMod (ghost_var_update M_g_new with "HγM") as "HγM".
    (* Insert τ into stat as OpEnqPending v_push. *)
    assert (Htau_fresh_stat : stat !! τ = None).
    { destruct (stat !! τ) as [s_op|] eqn:Hlookup; last reflexivity.
      exfalso.
      (* Use stat_consistent to derive (s_w, π_w) ∈ M_g with π_w[τ] ≠ None;
         then by mcfg_steps_dom_in_trace, τ ∈ ts.*1, contradicting Hfresh. *)
      pose proof (Hsc τ) as Hsc_τ. rewrite Hlookup in Hsc_τ.
      destruct s_op.
      - (* OpEnqPending v: single equation. *)
        apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom. eexists. exact (Hsc_τ s_w π_w Hw_in). }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction.
      - (* OpEnqReserved — now disjunctive (conj of ∀-disj and ∃-LP'd). *)
        destruct Hsc_τ as [Hsc_all _].
        apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom.
          destruct (Hsc_all s_w π_w Hw_in) as [Heq|Heq]; eexists; exact Heq. }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction.
      - (* OpEnqStored *)
        destruct Hsc_τ as [Hsc_all _].
        apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom.
          destruct (Hsc_all s_w π_w Hw_in) as [Heq|Heq]; eexists; exact Heq. }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction.
      - (* OpEnqDone *)
        apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom. eexists; exact (Hsc_τ s_w π_w Hw_in). }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction.
      - (* OpDeqPending *)
        apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom. destruct (Hsc_τ s_w π_w Hw_in) as [Hl | [v Hr]].
          - eexists. exact Hl.
          - eexists. exact Hr. }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction.
      - (* OpDeqLinearized v0: existential form; extract the witness. *)
        destruct Hsc_τ as (s_w & π_w & Hw_in & Hπ_w).
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom. eexists; exact Hπ_w. }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction.
      - (* OpDeqDone *)
        apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom. eexists; exact (Hsc_τ s_w π_w Hw_in). }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction. }
    iMod (ghost_map_insert τ (OpEnqPending v_push) with "Hstat") as "[Hstat Hstat_τ]";
      first exact Htau_fresh_stat.
    iModIntro.
    iSplitR "HΦ Hstat_τ".
    { iNext.
      iExists items, back_val, (ts ++ [(τ, Call (encode_request (Push v_push)))]),
              M_g_new, (<[τ:=OpEnqPending v_push]> stat), slots, scan_map.
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist1".
      iPureIntro. split_and!.
      - exact Hlen.
      - exact Hbpos.
      - (* mcfg_steps: extend by mcfg_step_call. We need
           mcfg_steps mcfg_init (set_to_propset M_g_new)
                      (ts ++ [(τ, Call ...)]).
           From IH: mcfg_steps mcfg_init (set_to_propset M_g) ts.
           The Call step transforms (set_to_propset M_g) by mapping each
           config to its τ-Call image. The result is
           (λ '(s, π), (s, <[τ:=...]> π)) <$> set_to_propset M_g, which is
           propset-EQUAL to set_to_propset M_g_new (since M_g_new is the
           gset image under the same map). Use gset_to_propset_set_map_call. *)
        eapply mcfg_steps_snoc; first exact Hmcfg_steps.
        unfold M_g_new.
        rewrite <- gset_to_propset_set_map_call.
        apply (mcfg_step_call (set_to_propset M_g) τ);
          last by left; exists v_push.
        intros [s' π'] Hin_pre.
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hin_pre) as Hdom_sub.
        intros Hin_dom. apply Hdom_sub in Hin_dom.
        apply elem_of_list_to_set in Hin_dom. contradiction.
      - intros Hempty. apply Hne.
        apply set_choose_L in Hne as [x Hx_in].
        exfalso.
        assert ((x.1, <[τ:=(encode_request (Push v_push), None)]> x.2) ∈
                (M_g_new : gset single_config_q)) as Hin_map.
        { unfold M_g_new. apply elem_of_map.
          exists x. destruct x as [s' π']. split; [done | exact Hx_in]. }
        clear -Hin_map Hempty. set_solver.
      - by apply per_tag_wellformed_snoc_call_push.
      - (* stat_consistent. *)
        intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
        + rewrite lookup_insert_eq.
          intros s' π' Hin_g.
          unfold M_g_new in Hin_g.
          apply elem_of_map in Hin_g as ([s'' π''] & Heq & Hin_g_old).
          injection Heq as -> ->.
          rewrite lookup_insert_eq. reflexivity.
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
          pose proof (Hsc τ') as Hsc_τ'.
          assert (Hkey : ∀ (s' : @S hwq_model) π',
                     (s', π') ∈ (M_g_new : gset single_config_q) →
                     ∃ s'' π'', (s'', π'') ∈ M_g ∧
                                s' = s'' ∧
                                π' = <[τ:=(encode_request (Push v_push), None)]> π'').
          { intros s' π' Hin_new.
            apply elem_of_map in Hin_new as ([s'' π''] & Heq & Hin_old).
            exists s'', π''. split; first exact Hin_old.
            injection Heq. intros -> ->. split; reflexivity. }
          destruct (stat !! τ') as [s_op|] eqn:Hlookup_τ'.
          * destruct s_op.
            -- (* OpEnqPending v0: ∀-Pending. *)
               intros s' π' Hin_new.
               destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               apply (Hsc_τ' s'' π'' Hin_old).
            -- (* OpEnqReserved — disjunctive (conj ∀-disj, ∃-LP'd), mirrors Stored. *)
               destruct Hsc_τ' as [Hsc_all Hsc_ex].
               split.
               { intros s' π' Hin_new.
                 destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
                 rewrite lookup_insert_ne;
                   last (intros ?; apply Hne_τ; congruence).
                 apply (Hsc_all s'' π'' Hin_old). }
               destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
               exists s_v, (<[τ:=(encode_request (Push v_push), None)]> π_v).
               split.
               { unfold M_g_new. apply elem_of_map.
                 exists (s_v, π_v). split; first reflexivity. exact Hin_v. }
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               exact Hπ_v.
            -- (* OpEnqStored — conj (∀ disjunction, ∃ linearized). *)
               destruct Hsc_τ' as [Hsc_all Hsc_ex].
               split.
               { intros s' π' Hin_new.
                 destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
                 rewrite lookup_insert_ne;
                   last (intros ?; apply Hne_τ; congruence).
                 apply (Hsc_all s'' π'' Hin_old). }
               destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
               exists s_v, (<[τ:=(encode_request (Push v_push), None)]> π_v).
               split.
               { unfold M_g_new. apply elem_of_map.
                 exists (s_v, π_v). split; first reflexivity. exact Hin_v. }
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               exact Hπ_v.
            -- intros s' π' Hin_new.
               destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               by apply (Hsc_τ' s'' π'' Hin_old).
            -- intros s' π' Hin_new.
               destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               by apply (Hsc_τ' s'' π'' Hin_old).
            -- (* OpDeqLinearized v0: ∃-form. Lift witness through M_g_new. *)
               destruct Hsc_τ' as (s_v & π_v & Hin_v & Hπ_v).
               pose (π_v_new := <[τ:=(encode_request (Push v_push), None)]> π_v).
               exists s_v, π_v_new. split.
               ++ unfold M_g_new. apply elem_of_map.
                  exists (s_v, π_v). split; first reflexivity. exact Hin_v.
               ++ unfold π_v_new. rewrite lookup_insert_ne;
                    last (intros ?; apply Hne_τ; congruence).
                  exact Hπ_v.
            -- intros s' π' Hin_new.
               destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               by apply (Hsc_τ' s'' π'' Hin_old).
          * intros s' π' Hin_new.
            destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
            rewrite lookup_insert_ne;
              last (intros ?; apply Hne_τ; congruence).
            by apply (Hsc_τ' s'' π'' Hin_old).
      - exact Hsc_slots.
      - exact Hwell.
      - (* trace_stat_consistent: insert τ → OpEnqPending v_push into stat;
           filter ts++[(τ, Call (Push v))] at each τ' updated accordingly. *)
        intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
        + rewrite lookup_insert_eq.
          rewrite filter_app filter_cons_True; last reflexivity.
          rewrite filter_nil /=.
          rewrite (filter_τ_fresh_nil _ _ Hfresh) /=. reflexivity.
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
          rewrite filter_app filter_cons_False;
            last (by intros Heq; apply Hne_τ).
          rewrite filter_nil app_nil_r.
          exact (Htrst τ').
      - intros A seq HgoodA HnodupSeq Hsetof HJInvSeq.
        (* Step 1: reduce new JInvSeq to old JInvSeq. *)
        assert (HJInvSeq_old : JInvSeq seq slots stat scan_map).
        { intros n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km.
          destruct (HJInvSeq n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km)
            as (τ_d & l & j_d & Hstat_d & Hscan_d & Hkl & Hkj).
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          - rewrite lookup_insert_eq in Hstat_d. discriminate.
          - exists τ_d, l, j_d. split_and!; try assumption.
            rewrite lookup_insert_ne in Hstat_d;
              last (intros ?; apply Hne_τd; congruence).
            exact Hstat_d. }
        (* Step 1b: reduce new GoodEnqSet to old. *)
        assert (HgoodA_old : GoodEnqSet A items stat).
        { destruct HgoodA as [Hgood1 Hgood2]. split; first exact Hgood1.
          intros k Hin_A. destruct (Hgood2 k Hin_A) as [Hcase | (τ_e & v_e & Hres)].
          - left. exact Hcase.
          - right. destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            + rewrite lookup_insert_eq in Hres. discriminate.
            + exists τ_e, v_e. rewrite lookup_insert_ne in Hres;
                last (intros ?; apply Hne_τe; congruence).
              exact Hres. }
        (* Step 2: apply IH to get config in M_g. *)
        destruct (Hlinw_seq A seq HgoodA_old HnodupSeq Hsetof HJInvSeq_old)
          as (s & π & Hin_g & Hlen_s & Hsmatch & Hsmatch_case & Henq_d & Hlin_d
              & Hdone_d & Hpending_d & Hstored_d & Hres_d).
        (* Step 3: lift to M_g_new. *)
        pose (π_new := <[τ:=(encode_request (Push v_push), None)]> π).
        exists s, π_new. split_and!.
        + unfold M_g_new. apply elem_of_map.
          exists (s, π). split; first reflexivity. exact Hin_g.
        + exact Hlen_s.
        + exact Hsmatch.
        + (* TLA+ items+stat case match. Phase 1: stat doesn't have any new
             OpEnqReserved (τ was just added at OpEnqPending). So OpEnqReserved
             clauses are preserved (τ_e ≠ τ). *)
          intros n k Hseq_n.
          destruct (Hsmatch_case n k Hseq_n) as
            [(v0 & Hitem & Hs) | (τ_e & v_e & Hres & Hs)].
          * left. by exists v0.
          * right. exists τ_e, v_e. split; last exact Hs.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            -- rewrite Htau_fresh_stat in Hres. discriminate.
            -- rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τe; congruence).
               exact Hres.
        + (* OpEnqDone case. *)
          intros τ_d v_d i_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            unfold π_new. rewrite lookup_insert_ne;
              last (intros ?; apply Hne_τd; congruence).
            exact (Henq_d τ_d v_d i_d Hstat_d_new).
        + (* OpDeqLinearized case. *)
          intros τ_d v_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            unfold π_new. rewrite lookup_insert_ne;
              last (intros ?; apply Hne_τd; congruence).
            exact (Hlin_d τ_d v_d Hstat_d_new).
        + (* OpDeqDone case. *)
          intros τ_d v_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            unfold π_new. rewrite lookup_insert_ne;
              last (intros ?; apply Hne_τd; congruence).
            exact (Hdone_d τ_d v_d Hstat_d_new).
        + (* OpDeqPending case. *)
          intros τ_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            unfold π_new. rewrite lookup_insert_ne;
              last (intros ?; apply Hne_τd; congruence).
            exact (Hpending_d τ_d Hstat_d_new).
        + (* OpEnqStored case. *)
          intros τ_e v_e i_e Hstat_e_new.
          destruct (decide (τ_e = τ)) as [-> | Hne_τe].
          * rewrite lookup_insert_eq in Hstat_e_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_e_new;
              last (intros ?; apply Hne_τe; congruence).
            unfold π_new. rewrite lookup_insert_ne;
              last (intros ?; apply Hne_τe; congruence).
            exact (Hstored_d τ_e v_e i_e Hstat_e_new).
        + (* OpEnqReserved case (new lin_witness_seq clause). *)
          intros τ_e v_e i_e Hres_e_new.
          destruct (decide (τ_e = τ)) as [-> | Hne_τe].
          * rewrite lookup_insert_eq in Hres_e_new. discriminate.
          * rewrite lookup_insert_ne in Hres_e_new;
              last (intros ?; apply Hne_τe; congruence).
            destruct (Hres_d τ_e v_e i_e Hres_e_new) as [HLP Hdisj].
            split.
            -- intros HinA. unfold π_new. rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τe; congruence).
               exact (HLP HinA).
            -- intros HninA. unfold π_new. rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τe; congruence).
               exact (Hdisj HninA).
      - (* slots_bounded: unchanged by ghost var update. *)
        exact Hbnd.
      - (* slots_stat_iff: τ inserted with OpEnqPending (no idx).
           Slots unchanged. Other τ' unchanged. *)
        destruct Hssi as (Hssi1 & Hssi2 & Hssi3 & Hssi_bnd). split_and!.
        + intros τ' v' i' Howns.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          * destruct Howns as [Howns | Howns];
              rewrite lookup_insert_eq in Howns; discriminate.
          * apply (Hssi1 τ' v' i').
            destruct Howns as [Howns | Howns].
            -- left. rewrite lookup_insert_ne in Howns;
                 last (intros ?; apply Hne_τ'; congruence).
               exact Howns.
            -- right. rewrite lookup_insert_ne in Howns;
                 last (intros ?; apply Hne_τ'; congruence).
               exact Howns.
        + intros i' v' Hslot'.
          destruct (Hssi2 i' v' Hslot') as (τ_w & Hstat_w).
          exists τ_w. destruct (decide (τ_w = τ)) as [-> | Hne_τw].
          * exfalso. destruct Hstat_w as [Hstat_w | Hstat_w];
              rewrite Htau_fresh_stat in Hstat_w; discriminate.
          * destruct Hstat_w as [Hstat_w | Hstat_w].
            -- left. rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τw; congruence).
               exact Hstat_w.
            -- right. rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τw; congruence).
               exact Hstat_w.
        + intros τ_1 τ_2 v_1 v_2 i' Hτ1 Hτ2.
          destruct (decide (τ_1 = τ)) as [-> | Hne_τ1];
            destruct (decide (τ_2 = τ)) as [-> | Hne_τ2].
          * reflexivity.
          * exfalso. destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
              rewrite lookup_insert_eq in Hτ1; discriminate.
          * exfalso. destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
              rewrite lookup_insert_eq in Hτ2; discriminate.
          * apply (Hssi3 τ_1 τ_2 v_1 v_2 i').
            -- destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                 rewrite lookup_insert_ne in Hτ1;
                 try (intros ?; apply Hne_τ1; congruence).
               ++ left. exact Hτ1.
               ++ right. left. exact Hτ1.
               ++ right. right. exact Hτ1.
            -- destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                 rewrite lookup_insert_ne in Hτ2;
                 try (intros ?; apply Hne_τ2; congruence).
               ++ left. exact Hτ2.
               ++ right. left. exact Hτ2.
               ++ right. right. exact Hτ2.
        + intros τ' v' i' Hstat'.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          * exfalso. destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
              rewrite lookup_insert_eq in Hstat'; discriminate.
          * apply (Hssi_bnd τ' v' i').
            destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
              rewrite lookup_insert_ne in Hstat';
              try (intros ?; apply Hne_τ'; congruence).
            -- left. exact Hstat'.
            -- right. left. exact Hstat'.
            -- right. right. exact Hstat'.
      - (* closure_push preserved under mcfg_step_call (Phase 1 Call enq).
           New stat'[τ] = OpEnqPending v_push. The closure_push's stat condition
           requires ∀ pv ∈ pushes, stat'[pv.1] ∈ {Reserved, Stored}. Since
           OpEnqPending ∉ {Reserved, Stored}, τ ∉ pushes.*1. So pushes only
           contains pre-existing FAA'd processes — lift via Hcl_push on pre-image. *)
        intros cfg pushes Hin Hnd Hsubset Hstat_pushes.
        unfold M_g_new in Hin. apply elem_of_map in Hin as (cfg_x & Heq & Hin_x).
        subst cfg.
        (* τ ∉ pushes.*1 because stat'[τ] = OpEnqPending, not Reserved/Stored. *)
        assert (Hτ_notin : τ ∉ pushes.*1).
        { intros Hin_τ.
          apply list_elem_of_fmap_1 in Hin_τ as (pv & Heq_τ & Hpv_in).
          destruct (Hstat_pushes pv Hpv_in) as (v' & i' & [Hs | Hs]);
            rewrite -Heq_τ in Hs; rewrite lookup_insert_eq in Hs; discriminate. }
        (* pushes ⊆ pending_push_of_config cfg_x (because τ has Pop-Push-None
           but τ ∉ pushes, so removing the τ entry doesn't matter). *)
        assert (Hsubset' : pushes ⊆ pending_push_of_config cfg_x).
        { intros pv Hpv_in.
          assert (Hpv_cfg : pv ∈ pending_push_of_config
                              (cfg_x.1, <[τ:=(encode_request (Push v_push), None)]>cfg_x.2)).
          { apply Hsubset. exact Hpv_in. }
          unfold pending_push_of_config in Hpv_cfg |- *.
          apply list_elem_of_omap in Hpv_cfg as ([τ' [req resp]] & Hin_list & Heq).
          apply elem_of_map_to_list in Hin_list. simpl in *.
          destruct (decide (τ' = τ)) as [Heq_τ | Hne_τ'].
          - subst τ'. rewrite lookup_insert_eq in Hin_list.
            injection Hin_list as Hreq Hresp. subst req. subst resp.
            simpl in Heq.
            unfold encode_request in Heq. simpl in Heq.
            injection Heq as Heq_pv. subst pv.
            exfalso. apply Hτ_notin.
            apply (list_elem_of_fmap_2 fst _ (τ, v_push)); exact Hpv_in.
          - rewrite lookup_insert_ne in Hin_list;
              last (intros ?; apply Hne_τ'; congruence).
            apply list_elem_of_omap. exists (τ', (req, resp)). split.
            + apply elem_of_map_to_list. exact Hin_list.
            + exact Heq. }
        assert (Hstat_pushes' : ∀ pv, pv ∈ pushes → ∃ v i,
                  stat !! pv.1 = Some (OpEnqReserved v i) ∨
                  stat !! pv.1 = Some (OpEnqStored v i)).
        { intros pv Hpv_in. destruct (Hstat_pushes pv Hpv_in) as (v' & i' & Hstat').
          exists v', i'. assert (Hne_pv_τ : pv.1 ≠ τ).
          { intros Heq_pv. apply Hτ_notin.
            rewrite -Heq_pv.
            apply (list_elem_of_fmap_2 fst _ pv); exact Hpv_in. }
          destruct Hstat' as [Hs | Hs].
          - left. rewrite lookup_insert_ne in Hs; last (intros ?; apply Hne_pv_τ; congruence).
            exact Hs.
          - right. rewrite lookup_insert_ne in Hs; last (intros ?; apply Hne_pv_τ; congruence).
            exact Hs. }
        pose proof (Hcl_push cfg_x pushes Hin_x Hnd Hsubset' Hstat_pushes') as Hcl_x.
        (* Map Hcl_x to M_g_new. *)
        unfold M_g_new. apply elem_of_map.
        exists (lineraize_pending_push pushes cfg_x). split; last exact Hcl_x.
        unfold lineraize_pending_push. simpl. f_equal.
        (* Need: <[τ:=(Push v_push, None)]>(map_imap ... cfg_x.2)
                = map_imap ... <[τ:=(Push v_push, None)]>cfg_x.2 *)
        apply map_eq. intros τ'.
        destruct (decide (τ' = τ)) as [-> | Hne_τ'].
        + rewrite lookup_insert_eq map_lookup_imap lookup_insert_eq /=.
          rewrite bool_decide_eq_false_2; first reflexivity.
          intros Hin_τ. apply Hτ_notin. exact Hin_τ.
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ'; congruence).
          rewrite !map_lookup_imap.
          rewrite lookup_insert_ne; last (intros ?; apply Hne_τ'; congruence).
          reflexivity.
      - (* scan_map_dom_in_stat maintenance at Phase 1 Call enq.
           stat_new = <[τ:=OpEnqPending v_push]>stat. scan_map unchanged. *)
        intros τ' Hstat'_None.
        destruct (decide (τ' = τ)) as [-> | Hne_τ'].
        + rewrite lookup_insert_eq in Hstat'_None. discriminate.
        + rewrite lookup_insert_ne in Hstat'_None;
            last (intros ?; apply Hne_τ'; congruence).
          apply (Hscan_dom τ' Hstat'_None).
      - (* scan_map_l_bounded: scan_map and back_val unchanged. *)
        exact Hscan_lb. }
    (* ──────────────────────────────────────────────────────────────────
       After Phase 1, the residual program is:
         let "res" := op q (SOMEV v_push) in
         trace_emit #l #τ (InjR "res");; "res"
       Stepping through [op] dispatches to [enqueue q v_push].
       ──────────────────────────────────────────────────────────────── *)
    wp_pures.
    rewrite /op.
    wp_pures.
    rewrite /encode_request /=.
    wp_pures.
    (* Now executing [enqueue q v_push]. *)
    rewrite /enqueue.
    wp_pures.

    (* ──────────────────────────────────────────────────────────────────
       Phase 2 — FAA on back to reserve a slot.
       ──────────────────────────────────────────────────────────────── *)
    wp_bind (FAA _ _).
    iInv "Hinv" as (items2 back_val2 ts2 M_g2 stat2 slots2 scan_map2)
      "(>Hback & >Har & >Hts & >%Hlen2 & >%Hbpos2 & >HγM & >Hstat & >Hslots & >Hscan & #Hslots_persist2 &
         >%Hmcfg_steps2 & >%Hne2 & >%Hpw2 & >%Hsc2 & >%Hsc_slots2 & >%Hwell2 & >%Htrst2 & >%Hlinw_seq2 & >%Hbnd2 & >%Hssi2 & >%Hcl_push2 & >%Hscan_dom2 & >%Hscan_lb2)".
    wp_faa.
    iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ.
    (* Expand M_g_new at Phase 2 FAA: τ transitions OpEnqPending → OpEnqReserved.
       Per TLA+'s E1 expansion, the closure_push now includes τ as closure-eligible.
       M_g_new := M_g2 ∪ M_g_LP_τ where M_g_LP_τ enumerates linearized configs
       for all valid pushes-lists containing τ. *)
    pose (stat2' := <[τ:=OpEnqReserved v_push (Z.to_nat back_val2)]>stat2).
    (* Boolean predicate: pv is stat-conformant if stat2'[pv.1] = Reserved/Stored. *)
    pose (pv_conformant := λ pv : positive * val,
      match stat2' !! pv.1 with
      | Some (OpEnqReserved _ _) | Some (OpEnqStored _ _) => true
      | _ => false
      end).
    (* Stat-conformant push_lists: filter all_push_lists to only those where
       each pv ∈ pushes has stat2'[pv.1] ∈ {Reserved, Stored}. *)
    pose (push_lists_filtered := λ cfg : single_config_q,
      List.filter (λ pushes : list (positive * val), forallb pv_conformant pushes)
        (all_push_lists (pending_push_of_config cfg))).
    (* Helper: pv_conformant pv ↔ stat2'[pv.1] is Reserved or Stored. *)
    assert (Hconf_iff : ∀ pv : positive * val,
              pv_conformant pv = true ↔
              ∃ v i, stat2' !! pv.1 = Some (OpEnqReserved v i) ∨
                     stat2' !! pv.1 = Some (OpEnqStored v i)).
    { intros pv. unfold pv_conformant. split.
      - destruct (stat2' !! pv.1) as [s_op|] eqn:Hlk;
          last (intros; discriminate).
        destruct s_op as [v0 | v0 i0 | v0 i0 | v0 i0 | | v0 | v0];
          try (intros; discriminate);
          intros _; exists v0, i0; [left | right]; reflexivity.
      - intros (v & i & [Hlk | Hlk]); rewrite Hlk; reflexivity. }
    (* M_g_LP_τ: linearized configs for stat-conformant pushes-lists only.
       τ' (at OpEnqPending) is not in any pushes here, preserving ∀-Pending
       stat_consistent for OpEnqPending τ'. *)
    pose (M_g_LP_τ :=
      (list_to_set
        (List.flat_map (λ cfg : single_config_q,
          List.map (λ pushes : list (positive * val),
                    lineraize_pending_push pushes cfg)
            (push_lists_filtered cfg))
          (elements M_g2)) : gset single_config_q)).
    pose (M_g_new2 := M_g2 ∪ M_g_LP_τ).
    iMod (ghost_var_update M_g_new2 with "HγM") as "HγM".
    (* Apply chain helper with restricted push_lists_filtered. *)
    pose (cfgs := elements M_g2).
    assert (Hcfgs_in : Forall (λ cfg, cfg ∈ (set_to_propset M_g2 : @meta_config hwq_model)) cfgs).
    { apply Forall_forall. intros cfg Hcfg_in_list.
      apply elem_of_set_to_propset. by apply elem_of_elements in Hcfg_in_list. }
    assert (Hcfgs_pushes : Forall (λ cfg, Forall (λ pushes,
                NoDup pushes.*1 ∧
                Forall (λ pv : positive * val,
                          cfg.2 !! pv.1 = Some (encode_request (Push pv.2), None)) pushes)
              (push_lists_filtered cfg)) cfgs).
    { apply Forall_forall. intros cfg Hcfg_in_list.
      apply Forall_forall. intros pushes Hpushes_in.
      unfold push_lists_filtered in Hpushes_in.
      apply list_elem_of_In in Hpushes_in.
      apply filter_In in Hpushes_in as [Hpushes_in_all _Hcond_forallb].
      apply list_elem_of_In in Hpushes_in_all.
      unfold all_push_lists in Hpushes_in_all.
      apply list_elem_of_bind in Hpushes_in_all as (sub & Hpushes_perm & Hsub_in_pset).
      rewrite permutations_Permutation in Hpushes_perm.
      rewrite powermset_submseteq in Hsub_in_pset.
      assert (Hpushes_subseteq : pushes ⊆ pending_push_of_config cfg).
      { intros pv Hpv_in. rewrite -Hpushes_perm in Hpv_in.
        eapply elem_of_submseteq; first exact Hpv_in. exact Hsub_in_pset. }
      assert (Hnd_pending_keys : NoDup (pending_push_of_config cfg).*1).
      { destruct cfg as [s_q π_q]. unfold pending_push_of_config. simpl.
        assert (Hkeys_sub : (omap (λ '(τ', v), if v is (InjRV v, None) then Some (τ',v) else None)
                                   (map_to_list π_q)).*1 `sublist_of` (map_to_list π_q).*1).
        { induction (map_to_list π_q) as [|[τ' [v' resp']] tl IH'].
          - apply sublist_nil.
          - simpl.
            destruct v' as [| | v_inner | |];
              try (simpl; apply sublist_cons; exact IH').
            destruct resp' as [v_resp |];
              try (simpl; apply sublist_cons; exact IH').
            simpl. apply sublist_skip. exact IH'. }
        eapply sublist_NoDup; last exact Hkeys_sub.
        apply NoDup_fst_map_to_list. }
      split.
      - assert (Hperm_keys : sub.*1 ≡ₚ pushes.*1).
        { apply fmap_Permutation. exact Hpushes_perm. }
        rewrite -Hperm_keys.
        assert (Hsub_keys : sub.*1 ⊆+ (pending_push_of_config cfg).*1).
        { apply (fmap_submseteq fst). exact Hsub_in_pset. }
        apply submseteq_sublist_l in Hsub_keys as (l2 & Hsublist & Hperm_l2).
        eapply sublist_NoDup; last exact Hsublist.
        rewrite Hperm_l2. exact Hnd_pending_keys.
      - apply Forall_forall. intros pv Hpv_in.
        destruct pv as [τ_pv v_pv].
        assert (Hpv_in_pending : (τ_pv, v_pv) ∈ pending_push_of_config cfg)
          by (by apply Hpushes_subseteq).
        unfold pending_push_of_config in Hpv_in_pending.
        apply list_elem_of_omap in Hpv_in_pending as ([τ_x [v_x resp]] & Hin_list & Hmatch).
        destruct v_x as [| | v_y | |]; try discriminate.
        destruct resp as [v_resp |]; try discriminate.
        simpl in Hmatch. injection Hmatch as Heq1 Heq2. subst.
        apply elem_of_map_to_list in Hin_list.
        exact Hin_list. }
    destruct (mcfg_steps_chain_lp_push_all_cfgs (set_to_propset M_g2) cfgs push_lists_filtered
                Hcfgs_in Hcfgs_pushes)
      as (M_full_new2 & Hmcfg_steps_new & Hsub_full_new & Hwit_LP & Hupper_perm).
    iMod (ghost_map_update (OpEnqReserved v_push (Z.to_nat back_val2))
            with "Hstat Hstat_τ") as "[Hstat Hstat_τ]".
    (* M_full_new2 = set_to_propset M_g2 ∪ {lineraize for stat-conformant pushes}
                   = set_to_propset M_g_new2 (since M_g_LP_τ is restricted). *)
    assert (HM_full_new2_eq : M_full_new2 = (set_to_propset M_g_new2 : @meta_config hwq_model)).
    { apply leibniz_equiv. intros y. split.
      - intros Hy.
        destruct (Hupper_perm y Hy) as
          [Hy_full | (cfg & pushes & prefix & Hcfg_in & Hpush_in & Hprefix & ->)].
        + apply elem_of_set_to_propset in Hy_full.
          apply elem_of_set_to_propset. unfold M_g_new2.
          apply elem_of_union. left. exact Hy_full.
        + (* y = lineraize_pending_push prefix cfg, where prefix `prefix_of` pushes,
             and pushes is stat-conformant. The PREFIX may also be stat-conformant
             (since it's a subset of conformant pushes). *)
          apply elem_of_set_to_propset. unfold M_g_new2.
          apply elem_of_union. right.
          unfold M_g_LP_τ. apply elem_of_list_to_set.
          apply list_elem_of_In, in_flat_map.
          exists cfg. split.
          * apply list_elem_of_In. unfold cfgs in Hcfg_in. exact Hcfg_in.
          * apply in_map_iff. exists prefix.
            split; first reflexivity.
            (* prefix is in push_lists_filtered cfg if it's a prefix of pushes
               (stat-conformant) — since stat-conformance is preserved by sublists,
               prefix is also stat-conformant; and it's a NoDup permutation-sublist
               of pending_push_of_config cfg. *)
            unfold push_lists_filtered.
            unfold push_lists_filtered in Hpush_in.
            apply list_elem_of_In in Hpush_in.
            apply filter_In in Hpush_in as [Hpush_in_all Hcond].
            apply filter_In. split.
            -- (* prefix is in all_push_lists(pending_push_of_config cfg). *)
               apply list_elem_of_In in Hpush_in_all.
               unfold all_push_lists in Hpush_in_all.
               apply list_elem_of_bind in Hpush_in_all as (sub & Hperm & Hsub_in_pset).
               rewrite permutations_Permutation in Hperm.
               rewrite powermset_submseteq in Hsub_in_pset.
               apply list_elem_of_In.
               unfold all_push_lists.
               apply list_elem_of_bind.
               destruct Hprefix as [k Hk].
               exists prefix. split.
               ++ apply permutations_refl.
               ++ apply powermset_submseteq.
                  assert (Hpref_sub : prefix ⊆+ pushes).
                  { rewrite Hk. apply submseteq_inserts_r. reflexivity. }
                  assert (Hpushes_sub : pushes ⊆+ sub).
                  { rewrite Hperm. reflexivity. }
                  etrans; first exact Hpref_sub.
                  etrans; first exact Hpushes_sub.
                  exact Hsub_in_pset.
            -- (* prefix is stat-conformant: prefix is a prefix of pushes which
                  is stat-conformant. *)
               apply forallb_forall.
               rewrite forallb_forall in Hcond.
               destruct Hprefix as [k Hk].
               intros pv Hpv_in. apply Hcond.
               rewrite Hk. apply in_app_iff. left. exact Hpv_in.
      - intros Hy. rewrite elem_of_set_to_propset in Hy.
        unfold M_g_new2 in Hy. apply elem_of_union in Hy as [Hy_g | Hy_lp].
        + apply Hsub_full_new. apply elem_of_set_to_propset. exact Hy_g.
        + unfold M_g_LP_τ in Hy_lp. apply elem_of_list_to_set in Hy_lp.
          apply list_elem_of_In, in_flat_map in Hy_lp as (cfg & Hcfg_in & Hy_in).
          apply list_elem_of_In in Hcfg_in.
          apply in_map_iff in Hy_in as (pushes & Hy_eq & Hpushes_in).
          apply list_elem_of_In in Hpushes_in.
          subst y.
          rewrite Forall_forall in Hwit_LP.
          assert (Hcfg_in_cfgs : cfg ∈ cfgs) by exact Hcfg_in.
          pose proof (Hwit_LP cfg Hcfg_in_cfgs) as Hwit_cfg.
          rewrite Forall_forall in Hwit_cfg.
          exact (Hwit_cfg pushes Hpushes_in). }
    iModIntro.
    iSplitR "HΦ Hstat_τ".
    { iNext.
      iExists items2, (back_val2 + 1)%Z, ts2, M_g_new2,
              (<[τ:=OpEnqReserved v_push (Z.to_nat back_val2)]> stat2), slots2, scan_map2.
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist2".
      iPureIntro. split_and!; try assumption.
      - lia.
      - (* mcfg_steps: combine Hmcfg_steps2 with Hmcfg_steps_new. *)
        rewrite -HM_full_new2_eq.
        replace ts2 with (ts2 ++ ([] : list (positive*trace))) by apply app_nil_r.
        eapply mcfg_steps_app; first exact Hmcfg_steps2.
        exact Hmcfg_steps_new.
      - (* M_g_new2 ≠ ∅: M_g_new2 ⊇ M_g2 ≠ ∅ (Hne2). Apply elem_of_union left. *)
        intros Habs.
        apply set_choose_L in Hne2 as [x Hx_in].
        assert (Hin_union : x ∈ (M_g_new2 : gset single_config_q)).
        { unfold M_g_new2. apply elem_of_union. left. exact Hx_in. }
        rewrite Habs in Hin_union. clear -Hin_union. set_solver.
      - (* stat_consistent on M_g_new2 = M_g2 ∪ M_g_LP_τ (restricted).
           With OpEnqReserved disjunctive, and M_g_LP_τ restricted to stat-conformant
           pushes, the proof goes through case analysis.

           Key helper: configs in M_g_LP_τ have shape lineraize_pending_push pushes cfg
           for some cfg ∈ M_g2 and stat-conformant pushes. The π of such config
           differs from π_cfg only at τ_pv ∈ pushes.*1 (LP'd to (Push v_pv, Some #())). *)
        intros τ'.
        (* Helper: destruct membership in M_g_new2. Use s_c, π_c for cfg. *)
        assert (Hmem_destruct : ∀ s' π', (s', π') ∈ M_g_new2 →
                  (s', π') ∈ M_g2 ∨
                  ∃ (s_c : list val) (π_c : gmap positive proc_status)
                    (pushes : list (positive * val)),
                    (s_c, π_c) ∈ M_g2 ∧
                    pushes ∈ all_push_lists (pending_push_of_config (s_c, π_c)) ∧
                    forallb pv_conformant pushes = true ∧
                    (s', π') = lineraize_pending_push pushes (s_c, π_c)).
        { intros s' π' Hin. unfold M_g_new2 in Hin.
          apply elem_of_union in Hin as [Hin_g | Hin_lp]; first by left.
          right.
          unfold M_g_LP_τ in Hin_lp.
          apply elem_of_list_to_set in Hin_lp.
          apply list_elem_of_In, in_flat_map in Hin_lp as (cfg & Hcfg_in & Hin_map).
          apply list_elem_of_In in Hcfg_in.
          unfold cfgs in Hcfg_in. apply elem_of_elements in Hcfg_in.
          apply in_map_iff in Hin_map as (pushes & Hy_eq & Hpushes_in).
          apply list_elem_of_In in Hpushes_in.
          unfold push_lists_filtered in Hpushes_in.
          apply list_elem_of_In, filter_In in Hpushes_in as [Hpushes_in_all Hcond].
          apply list_elem_of_In in Hpushes_in_all.
          destruct cfg as [s_c π_c].
          exists s_c, π_c, pushes.
          split_and!; try assumption.
          symmetry. exact Hy_eq. }
        (* Helper: for τ_d ≠ τ with stat2'[τ_d] = stat2[τ_d] (i.e., τ_d ≠ τ),
           the LP'd image π_LP differs from cfg's π only on τ_pv ∈ pushes.*1.
           τ_d ∉ pushes.*1 (since stat-conformant pushes have τ_pv ∈ {Reserved, Stored} in stat2'). *)
        assert (Hτd_notin_pushes : ∀ τ_d pushes,
                  τ_d ≠ τ →
                  forallb pv_conformant pushes = true →
                  (stat2 !! τ_d = None ∨
                   (∃ v, stat2 !! τ_d = Some (OpEnqPending v)) ∨
                   (∃ v i, stat2 !! τ_d = Some (OpEnqDone v i)) ∨
                   stat2 !! τ_d = Some OpDeqPending ∨
                   (∃ v, stat2 !! τ_d = Some (OpDeqLinearized v)) ∨
                   (∃ v, stat2 !! τ_d = Some (OpDeqDone v))) →
                  τ_d ∉ pushes.*1).
        { intros τ_d pushes Hne_τd Hcond Hstat_τd Hτd_in.
          apply list_elem_of_fmap_1 in Hτd_in as ([τ_d' v'] & Heq_τ & Hpv_in).
          simpl in Heq_τ. subst τ_d'.
          rewrite forallb_forall in Hcond.
          apply list_elem_of_In in Hpv_in.
          specialize (Hcond _ Hpv_in).
          unfold pv_conformant in Hcond. simpl in Hcond.
          unfold stat2' in Hcond.
          rewrite lookup_insert_ne in Hcond; last (intros ?; apply Hne_τd; congruence).
          destruct Hstat_τd as
            [Heq | [(v & Heq) | [(v & i & Heq) | [Heq | [(v & Heq) | (v & Heq)]]]]];
            rewrite Heq in Hcond; discriminate. }
        destruct (decide (τ' = τ)) as [-> | Hne_τ].
        + (* τ' = τ at NEW OpEnqReserved (v_push, back_val2). Disjunctive (∀-disj, ∃-LP'd). *)
          rewrite lookup_insert_eq.
          split.
          { (* ∀-disjunction: ∀ (s', π') ∈ M_g_new2, π'[τ] ∈ {Pending, LP'd}. *)
            intros s' π' Hin_new.
            destruct (Hmem_destruct s' π' Hin_new) as
              [Hin_g | (s_c & π_c & pushes & Hcfg_in & _Hpushes_in_all & _Hcond & Heq_lin)].
            - (* cfg ∈ M_g2: π'[τ] = Pending Push v_push by Hsc2 (OpEnqPending). *)
              left. pose proof (Hsc2 τ) as Hsc2_τ. rewrite Hstat_τ in Hsc2_τ.
              exact (Hsc2_τ s' π' Hin_g).
            - (* cfg ∈ M_g_LP_τ: case on whether τ ∈ pushes.*1. *)
              destruct (decide (τ ∈ pushes.*1)) as [Hτ_in | Hτ_notin].
              + (* τ ∈ pushes.*1: π_LP[τ] = LP'd. *)
                right.
                injection Heq_lin as -> ->.
                unfold lineraize_pending_push. cbn [snd].
                rewrite map_lookup_imap.
                pose proof (Hsc2 τ) as Hsc2_τ. rewrite Hstat_τ in Hsc2_τ.
                pose proof (Hsc2_τ _ _ Hcfg_in) as Hπ_cfg_τ.
                rewrite Hπ_cfg_τ /=.
                rewrite bool_decide_eq_true_2; last exact Hτ_in.
                reflexivity.
              + (* τ ∉ pushes.*1: π_LP[τ] = π_cfg[τ] = Pending. *)
                left.
                injection Heq_lin as -> ->.
                unfold lineraize_pending_push. cbn [snd].
                rewrite map_lookup_imap.
                pose proof (Hsc2 τ) as Hsc2_τ. rewrite Hstat_τ in Hsc2_τ.
                pose proof (Hsc2_τ _ _ Hcfg_in) as Hπ_cfg_τ.
                rewrite Hπ_cfg_τ /=.
                rewrite bool_decide_eq_false_2; last exact Hτ_notin.
                reflexivity. }
          (* ∃-LP'd witness: lineraize [(τ, v_push)] cfg for some cfg ∈ M_g2.
             pushes = [(τ, v_push)] is stat-conformant (stat2'[τ] = Reserved). *)
          apply set_choose_L in Hne2 as [[s_w π_w] Hw_in].
          pose (pushes_τ := [(τ, v_push)]).
          assert (Hpushes_τ_subseteq : pushes_τ ⊆ pending_push_of_config (s_w, π_w)).
          { intros pv Hpv_in. apply list_elem_of_singleton in Hpv_in. subst pv.
            apply pending_push_of_config_lookup. simpl.
            pose proof (Hsc2 τ) as Hsc2_τ. rewrite Hstat_τ in Hsc2_τ.
            exact (Hsc2_τ _ _ Hw_in). }
          assert (Hpushes_τ_in_all : pushes_τ ∈ all_push_lists (pending_push_of_config (s_w, π_w))).
          { unfold all_push_lists.
            apply list_elem_of_bind.
            exists pushes_τ. split.
            - apply permutations_refl.
            - apply powermset_submseteq.
              apply NoDup_submseteq.
              + apply NoDup_singleton.
              + exact Hpushes_τ_subseteq. }
          assert (Hpushes_τ_conform : forallb pv_conformant pushes_τ = true).
          { simpl. unfold pv_conformant. simpl. unfold stat2'.
            rewrite lookup_insert_eq. reflexivity. }
          exists (s_w ++ [v_push]),
            (map_imap (λ τ_x x, if bool_decide (τ_x ∈ [τ]) then Some (x.1, Some #()) else Some x) π_w).
          split.
          * (* The lineraized config is in M_g_LP_τ. *)
            unfold M_g_new2. apply elem_of_union. right.
            unfold M_g_LP_τ. apply elem_of_list_to_set.
            apply list_elem_of_In, in_flat_map.
            exists (s_w, π_w). split.
            -- apply list_elem_of_In. unfold cfgs. by apply elem_of_elements.
            -- apply in_map_iff. exists pushes_τ. split.
               ++ simpl. reflexivity.
               ++ apply list_elem_of_In.
                  unfold push_lists_filtered.
                  apply list_elem_of_In, filter_In. split.
                  ** apply list_elem_of_In. exact Hpushes_τ_in_all.
                  ** exact Hpushes_τ_conform.
          * (* π[τ] = LP'd. *)
            rewrite map_lookup_imap.
            pose proof (Hsc2 τ) as Hsc2_τ. rewrite Hstat_τ in Hsc2_τ.
            pose proof (Hsc2_τ _ _ Hw_in) as Hπ_w_τ.
            rewrite Hπ_w_τ /=.
            assert (Hτ_in_singleton : τ ∈ ([τ] : list positive))
              by (apply list_elem_of_singleton; reflexivity).
            rewrite bool_decide_eq_true_2; last exact Hτ_in_singleton.
            reflexivity.
        + (* τ' ≠ τ. Case-analyze stat2 !! τ'. *)
          rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
          pose proof (Hsc2 τ') as Hsc_τ'.
          (* Helper: for τ' ≠ τ with stat-conformant pushes, if stat2[τ'] ∈
             {Pending, Done, DeqPending, DeqLin, DeqDone, None}, then τ' ∉ pushes.
             Then π_LP[τ'] = π_cfg[τ']. *)
          assert (Hτ'_notin_pushes : ∀ pushes,
                    forallb pv_conformant pushes = true →
                    (∀ v i, stat2 !! τ' = Some (OpEnqReserved v i) → False) →
                    (∀ v i, stat2 !! τ' = Some (OpEnqStored v i) → False) →
                    τ' ∉ pushes.*1).
          { intros pushes Hcond Hnot_res Hnot_sto Hτ'_in.
            apply list_elem_of_fmap_1 in Hτ'_in as ([τ_d' v'] & Heq_τ & Hpv_in).
            simpl in Heq_τ. subst τ_d'.
            rewrite forallb_forall in Hcond.
            apply list_elem_of_In in Hpv_in.
            specialize (Hcond _ Hpv_in).
            unfold pv_conformant in Hcond. simpl in Hcond.
            unfold stat2' in Hcond.
            rewrite lookup_insert_ne in Hcond; last (intros ?; apply Hne_τ; congruence).
            destruct (stat2 !! τ') as [s_op|] eqn:Hlk; last discriminate.
            destruct s_op as [v0 | v0 i0 | v0 i0 | v0 i0 | | v0 | v0]; try discriminate.
            - by apply (Hnot_res v0 i0).
            - by apply (Hnot_sto v0 i0). }
          (* Helper: when τ' ∉ pushes.*1, π_LP[τ'] = π_cfg[τ']. *)
          assert (Hlift_τ' : ∀ s' π' s_c π_c pushes,
                    (s', π') = lineraize_pending_push pushes (s_c, π_c) →
                    τ' ∉ pushes.*1 →
                    π' !! τ' = π_c !! τ').
          { intros s' π' s_c π_c pushes Heq_lin Hτ'_notin.
            injection Heq_lin as -> ->.
            unfold lineraize_pending_push. cbn [snd].
            rewrite map_lookup_imap.
            destruct (π_c !! τ') as [x|] eqn:Hπ; rewrite Hπ /=; last reflexivity.
            rewrite bool_decide_eq_false_2; last exact Hτ'_notin.
            reflexivity. }
          destruct (stat2 !! τ') as [s_op|] eqn:Hlk.
          * destruct s_op as [v0 | v0 i0 | v0 i0 | v0 i0 | | v0 | v0].
            -- (* OpEnqPending v0: ∀-Pending in M_g_new2. *)
               intros s' π' Hin_new.
               destruct (Hmem_destruct s' π' Hin_new) as
                 [Hin_g | (s_c & π_c & pushes & Hcfg_in & _ & Hcond & Heq_lin)].
               ++ exact (Hsc_τ' s' π' Hin_g).
               ++ assert (Hτ'_notin : τ' ∉ pushes.*1).
                  { apply (Hτ'_notin_pushes pushes Hcond);
                      intros v i Habs; rewrite Habs in Hlk; discriminate. }
                  pose proof (Hlift_τ' s' π' s_c π_c pushes Heq_lin Hτ'_notin) as Hπ_eq.
                  rewrite Hπ_eq. exact (Hsc_τ' s_c π_c Hcfg_in).
            -- (* OpEnqReserved v0 i0: disjunctive (∀-disj, ∃-LP'd). *)
               destruct Hsc_τ' as [Hsc_all Hsc_ex].
               split.
               { intros s' π' Hin_new.
                 destruct (Hmem_destruct s' π' Hin_new) as
                   [Hin_g | (s_c & π_c & pushes & Hcfg_in & _ & Hcond & Heq_lin)].
                 - exact (Hsc_all s' π' Hin_g).
                 - destruct (decide (τ' ∈ pushes.*1)) as [Hτ'_in | Hτ'_notin].
                   + (* τ' ∈ pushes.*1: π_LP[τ'] = LP'd Push v0. *)
                     injection Heq_lin as -> ->.
                     right.
                     unfold lineraize_pending_push. cbn [snd].
                     rewrite map_lookup_imap.
                     destruct (Hsc_all s_c π_c Hcfg_in)
                       as [Hπ_cfg | Hπ_cfg]; rewrite Hπ_cfg /=;
                       rewrite bool_decide_eq_true_2; try exact Hτ'_in; reflexivity.
                   + (* τ' ∉ pushes.*1: π_LP[τ'] = π_cfg[τ']. *)
                     pose proof (Hlift_τ' s' π' s_c π_c pushes Heq_lin Hτ'_notin) as Hπ_eq.
                     rewrite Hπ_eq. exact (Hsc_all s_c π_c Hcfg_in). }
               (* ∃-LP'd at τ': lift OLD ∃-LP'd via Hsc_ex. M_g2 ⊆ M_g_new2. *)
               destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
               exists s_v, π_v. split; last exact Hπ_v.
               unfold M_g_new2. apply elem_of_union. left. exact Hin_v.
            -- (* OpEnqStored v0 i0: disjunctive. *)
               destruct Hsc_τ' as [Hsc_all Hsc_ex].
               split.
               { intros s' π' Hin_new.
                 destruct (Hmem_destruct s' π' Hin_new) as
                   [Hin_g | (s_c & π_c & pushes & Hcfg_in & _ & Hcond & Heq_lin)].
                 - exact (Hsc_all s' π' Hin_g).
                 - destruct (decide (τ' ∈ pushes.*1)) as [Hτ'_in | Hτ'_notin].
                   + injection Heq_lin as -> ->.
                     right.
                     unfold lineraize_pending_push. cbn [snd].
                     rewrite map_lookup_imap.
                     destruct (Hsc_all s_c π_c Hcfg_in)
                       as [Hπ_cfg | Hπ_cfg]; rewrite Hπ_cfg /=;
                       rewrite bool_decide_eq_true_2; try exact Hτ'_in; reflexivity.
                   + pose proof (Hlift_τ' s' π' s_c π_c pushes Heq_lin Hτ'_notin) as Hπ_eq.
                     rewrite Hπ_eq. exact (Hsc_all s_c π_c Hcfg_in). }
               destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
               exists s_v, π_v. split; last exact Hπ_v.
               unfold M_g_new2. apply elem_of_union. left. exact Hin_v.
            -- (* OpEnqDone v0 i0: ∀ LP'd. *)
               intros s' π' Hin_new.
               destruct (Hmem_destruct s' π' Hin_new) as
                 [Hin_g | (s_c & π_c & pushes & Hcfg_in & _ & Hcond & Heq_lin)].
               ++ exact (Hsc_τ' s' π' Hin_g).
               ++ assert (Hτ'_notin : τ' ∉ pushes.*1).
                  { apply (Hτ'_notin_pushes pushes Hcond);
                      intros v i Habs; rewrite Habs in Hlk; discriminate. }
                  pose proof (Hlift_τ' s' π' s_c π_c pushes Heq_lin Hτ'_notin) as Hπ_eq.
                  rewrite Hπ_eq. exact (Hsc_τ' s_c π_c Hcfg_in).
            -- (* OpDeqPending: ∀-disj. *)
               intros s' π' Hin_new.
               destruct (Hmem_destruct s' π' Hin_new) as
                 [Hin_g | (s_c & π_c & pushes & Hcfg_in & _ & Hcond & Heq_lin)].
               ++ exact (Hsc_τ' s' π' Hin_g).
               ++ assert (Hτ'_notin : τ' ∉ pushes.*1).
                  { apply (Hτ'_notin_pushes pushes Hcond);
                      intros v i Habs; rewrite Habs in Hlk; discriminate. }
                  pose proof (Hlift_τ' s' π' s_c π_c pushes Heq_lin Hτ'_notin) as Hπ_eq.
                  rewrite Hπ_eq. exact (Hsc_τ' s_c π_c Hcfg_in).
            -- (* OpDeqLinearized v0: ∃. *)
               destruct Hsc_τ' as (s_v & π_v & Hin_v & Hπ_v).
               exists s_v, π_v. split; last exact Hπ_v.
               unfold M_g_new2. apply elem_of_union. left. exact Hin_v.
            -- (* OpDeqDone v0: ∀ LP'd. *)
               intros s' π' Hin_new.
               destruct (Hmem_destruct s' π' Hin_new) as
                 [Hin_g | (s_c & π_c & pushes & Hcfg_in & _ & Hcond & Heq_lin)].
               ++ exact (Hsc_τ' s' π' Hin_g).
               ++ assert (Hτ'_notin : τ' ∉ pushes.*1).
                  { apply (Hτ'_notin_pushes pushes Hcond);
                      intros v i Habs; rewrite Habs in Hlk; discriminate. }
                  pose proof (Hlift_τ' s' π' s_c π_c pushes Heq_lin Hτ'_notin) as Hπ_eq.
                  rewrite Hπ_eq. exact (Hsc_τ' s_c π_c Hcfg_in).
          * (* stat2 !! τ' = None: ∀ π'[τ'] = None. *)
            intros s' π' Hin_new.
            destruct (Hmem_destruct s' π' Hin_new) as
              [Hin_g | (s_c & π_c & pushes & Hcfg_in & _ & Hcond & Heq_lin)].
            -- exact (Hsc_τ' s' π' Hin_g).
            -- assert (Hτ'_notin : τ' ∉ pushes.*1).
               { apply (Hτ'_notin_pushes pushes Hcond);
                   intros v i Habs; rewrite Habs in Hlk; discriminate. }
               pose proof (Hlift_τ' s' π' s_c π_c pushes Heq_lin Hτ'_notin) as Hπ_eq.
               rewrite Hπ_eq. exact (Hsc_τ' s_c π_c Hcfg_in).
      - (* trace_stat_consistent: OpEnqReserved has same trace footprint as OpEnqPending. *)
        intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
        + rewrite lookup_insert_eq.
          pose proof (Htrst2 τ) as Htrst_τ. rewrite Hstat_τ in Htrst_τ.
          exact Htrst_τ.
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
          exact (Htrst2 τ').
      - intros A seq HgoodA HnodupSeq Hsetof HJInvSeq.
        (* Common: stat_new[τ'] for τ' ≠ τ equals stat2[τ']. *)
        assert (Hstat_new_τ : (<[τ:=OpEnqReserved v_push (Z.to_nat back_val2)]> stat2) !! τ =
                              Some (OpEnqReserved v_push (Z.to_nat back_val2))).
        { rewrite lookup_insert_eq. reflexivity. }
        (* Common: helper for non-τ stat_new lookups. *)
        assert (Hstat_new_ne : ∀ τ' s,
                  τ' ≠ τ →
                  stat2 !! τ' = Some s →
                  (<[τ:=OpEnqReserved v_push (Z.to_nat back_val2)]> stat2) !! τ' = Some s).
        { intros τ' s Hne_τ' Hs.
          rewrite lookup_insert_ne; [exact Hs | intros ?; apply Hne_τ'; congruence]. }
        (* OLD JInvSeq, applicable in both cases (Phase 2 doesn't touch JInvSeq witnesses). *)
        assert (HJInvSeq_old_full : JInvSeq seq slots2 stat2 scan_map2).
        { intros n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km.
          destruct (HJInvSeq n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km)
            as (τ_d & l_d & j_d & Hstat_d & Hscan_d & Hkl & Hkj).
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          - rewrite lookup_insert_eq in Hstat_d. discriminate.
          - exists τ_d, l_d, j_d. split_and!; try assumption.
            rewrite lookup_insert_ne in Hstat_d;
              last (intros ?; apply Hne_τd; congruence).
            exact Hstat_d. }
        destruct (decide (Z.to_nat back_val2 ∈ A)) as [Hbv_in_A | Hbv_notin_A].
        + (* Case B: back_val2 ∈ A — TLA+ <4>3. *)
          (* Step B.1: PICK k such that seq[k] = back_val2 (since A = list_to_set seq). *)
          rewrite -Hsetof in Hbv_in_A. apply elem_of_list_to_set in Hbv_in_A.
          apply list_elem_of_lookup_1 in Hbv_in_A as [k Hseq_k].
          (* Step B.2: Characterize z > k slots — items NOT SOMEV. *)
          assert (Hsuffix_notSOMEV : ∀ z k_z w, (k < z)%nat → seq !! z = Some k_z →
                                    items2 !! k_z = Some (SOMEV w) → False).
          { intros z k_z w Hk_lt_z Hseq_z Hitem_z.
            (* SOMEV branch: items[k_z] = SOMEV w. Then slots[k_z] = Some w
               by slots_consistent direction 2. By slots_bounded2, k_z < back_val2.
               But then we have inversion (k, z, back_val2, k_z) with
               back_val2 > k_z. JInvSeq_old gives τ_d at OpDeqPending with
               scan_map[τ_d] = (l, j) and back_val2 < l. But scan_map_l_bounded
               says l ≤ back_val2. Contradiction. *)
            destruct Hsc_slots2 as [_ Hsc_slots2_b].
            pose proof (Hsc_slots2_b k_z w Hitem_z) as Hslot_kz.
            pose proof (Hbnd2 k_z w Hslot_kz) as Hkz_lt_bv.
            assert (Hkz_ne_bv : k_z ≠ Z.to_nat back_val2).
            { intros ->. lia. }
            assert (Hbv_gt_kz : (Z.to_nat back_val2 > k_z)%nat) by lia.
            assert (Hslot_kz_some : is_Some (slots2 !! k_z))
              by (eexists; exact Hslot_kz).
            destruct (HJInvSeq_old_full k z (Z.to_nat back_val2) k_z
                        Hk_lt_z Hseq_k Hseq_z Hbv_gt_kz Hslot_kz_some)
              as (τ_d & l_d & j_d & _ & Hscan_d & Hkl_d & _).
            pose proof (Hscan_lb2 τ_d l_d j_d Hscan_d) as Hl_d_le_bv. lia. }
          (* Actually we don't need that. Let me simplify and not require Hsuffix's None branch *)
          (* Define A_pre = list_to_set (take k seq), seq_pre = take k seq. *)
          pose (seq_pre := take k seq).
          pose (A_pre := (list_to_set seq_pre : gset nat)).
          (* Step B.3: GoodEnqSet(A_pre, items2, stat2) in OLD state. *)
          assert (Hgood_pre : GoodEnqSet A_pre items2 stat2).
          { split.
            - intros k' v' Hitem_k'.
              destruct HgoodA as [Hgood_a _].
              pose proof (Hgood_a k' v' Hitem_k') as Hk'_in_A.
              (* k' ∈ A means k' = seq[z] for some z. By NoDup, unique z. *)
              rewrite -Hsetof in Hk'_in_A. apply elem_of_list_to_set in Hk'_in_A.
              apply list_elem_of_lookup_1 in Hk'_in_A as [z Hseq_z].
              (* z ≠ k since seq[k] = back_val2 and slots[back_val2] = None
                 (back_val2 was pre-FAA back). *)
              assert (Hbv_no_slot : slots2 !! Z.to_nat back_val2 = None).
              { destruct (slots2 !! Z.to_nat back_val2) as [v_w|] eqn:Hbv_slot;
                  last reflexivity. exfalso.
                pose proof (Hbnd2 _ _ Hbv_slot). lia. }
              assert (Hitem_bv : items2 !! Z.to_nat back_val2 = Some NONEV ∨
                                  items2 !! Z.to_nat back_val2 = None).
              { destruct (items2 !! Z.to_nat back_val2) as [item|] eqn:Hitem_bv';
                  last (right; reflexivity). left.
                pose proof (Forall_lookup_1 _ _ _ _ Hwell2 Hitem_bv') as Hcases.
                destruct Hcases as [-> | (w & -> & _)]; first reflexivity.
                exfalso. destruct Hsc_slots2 as [_ Hsc_slots2_b].
                pose proof (Hsc_slots2_b _ _ Hitem_bv') as Hbv_slot_some.
                rewrite Hbv_no_slot in Hbv_slot_some. discriminate. }
              assert (Hk'_ne_bv : k' ≠ Z.to_nat back_val2).
              { intros ->. destruct Hitem_bv as [Habs|Habs];
                  rewrite Hitem_k' in Habs; discriminate. }
              assert (Hz_ne_k : z ≠ k).
              { intros ->. rewrite Hseq_k in Hseq_z.
                injection Hseq_z as Heq_kp.
                apply Hk'_ne_bv. symmetry. exact Heq_kp. }
              destruct (decide (z < k)%nat) as [Hzk | Hzk].
              + (* z < k: seq_pre[z] = seq[z] = k'. So k' ∈ A_pre. *)
                unfold A_pre. apply elem_of_list_to_set.
                apply list_elem_of_lookup_2 with z.
                unfold seq_pre. rewrite lookup_take_lt; [exact Hseq_z | exact Hzk].
              + (* z > k: by Hsuffix_notSOMEV, items[k'] is not SOMEV.
                   But items[k'] = Some (SOMEV v'). Contradiction. *)
                assert (Hk_lt_z : (k < z)%nat) by lia.
                exfalso. apply (Hsuffix_notSOMEV z k' v' Hk_lt_z Hseq_z Hitem_k').
            - intros k' Hk'_in_pre.
              unfold A_pre in Hk'_in_pre.
              apply elem_of_list_to_set in Hk'_in_pre.
              apply list_elem_of_lookup_1 in Hk'_in_pre as [n Hseq_pre_n].
              unfold seq_pre in Hseq_pre_n.
              pose proof (proj1 (lookup_take_Some _ _ _ _) Hseq_pre_n) as [Hseq_n Hn_lt_k].
              (* k' = seq[n] for n < k. k' ∈ A (NEW). *)
              assert (Hk'_in_A : k' ∈ A).
              { rewrite -Hsetof. apply elem_of_list_to_set.
                apply list_elem_of_lookup_2 with n. exact Hseq_n. }
              (* By NoDup: n ≠ k → k' ≠ back_val2. *)
              assert (Hk'_ne_bv : k' ≠ Z.to_nat back_val2).
              { intros ->. eapply NoDup_lookup in HnodupSeq;
                  [|exact Hseq_n|exact Hseq_k]. lia. }
              destruct HgoodA as [_ Hgood2].
              destruct (Hgood2 k' Hk'_in_A) as [(v' & Hitem_v') | (τ_e & v_e & Hres_e)].
              + left. by exists v'.
              + right. destruct (decide (τ_e = τ)) as [-> | Hne_τe].
                * (* τ_e = τ → i_e = back_val2 by NEW stat. But k' ≠ back_val2. *)
                  rewrite lookup_insert_eq in Hres_e.
                  injection Hres_e as _ Heq_k. exfalso. apply Hk'_ne_bv. symmetry. exact Heq_k.
                * exists τ_e, v_e.
                  rewrite lookup_insert_ne in Hres_e;
                    last (intros ?; apply Hne_τe; congruence).
                  exact Hres_e. }
          (* Step B.4: NoDup seq_pre. *)
          assert (Hnodup_pre : NoDup seq_pre).
          { unfold seq_pre.
            clear -HnodupSeq.
            generalize dependent k.
            induction seq as [|x xs IH]; intros k.
            - destruct k; simpl; apply NoDup_nil; auto.
            - destruct k; first apply NoDup_nil; first done.
              simpl. apply NoDup_cons in HnodupSeq as [Hx_ni HND_xs].
              apply NoDup_cons. split.
              + intros Hx_in. apply Hx_ni. apply list_elem_of_lookup_1 in Hx_in as [m Hm].
                pose proof (proj1 (lookup_take_Some _ _ _ _) Hm) as [Hm' _].
                by eapply list_elem_of_lookup_2.
              + by apply IH. }
          (* Step B.5: list_to_set seq_pre = A_pre. *)
          assert (Hsetof_pre : list_to_set seq_pre = A_pre) by reflexivity.
          (* Step B.6: JInvSeq(seq_pre, slots2, stat2, scan_map2). *)
          assert (HJInvSeq_pre : JInvSeq seq_pre slots2 stat2 scan_map2).
          { intros n m k_n k_m Hn_lt_m Hseq_pre_n Hseq_pre_m Hkn_gt_km Hsome_km.
            unfold seq_pre in Hseq_pre_n, Hseq_pre_m.
            pose proof (proj1 (lookup_take_Some _ _ _ _) Hseq_pre_n) as [Hseq_n _].
            pose proof (proj1 (lookup_take_Some _ _ _ _) Hseq_pre_m) as [Hseq_m _].
            apply (HJInvSeq_old_full n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km). }
          (* Step B.7: Apply OLD lin_witness_seq with (A_pre, seq_pre). *)
          destruct (Hlinw_seq2 A_pre seq_pre Hgood_pre Hnodup_pre Hsetof_pre HJInvSeq_pre)
            as (s_pre & π_pre & Hin_pre & Hlen_pre & Hsmatch_pre & Hsmatch_case_pre &
                Henq_pre & Hlin_pre & Hdone_pre & Hpending_pre & Hstored_pre & Hres_pre).
          (* Step B.8: Build the LP'd config via the chain helper.
             Define pushes = list of (τ_e_z, v_e_z) for z ∈ [k, length seq).
             For z = k: τ_e_z = τ, v_e_z = v_push (seq[k] = back_val2).
             For z > k: τ_e_z corresponds to OpEnqReserved at seq[z] in stat2.
             Existence: NEW GoodEnqSet for seq[z] ∈ A with z > k. Since
             items[seq[z]] ≠ SOMEV (Hsuffix_notSOMEV), the GoodEnqSet OpEnqReserved
             branch fires, yielding (τ_z, v_z). By NoDup seq, seq[z] ≠ back_val2,
             so τ_z ≠ τ (FAA-uniqueness), hence stat2[τ_z] = OpEnqReserved v_z
             seq[z] (lookup_insert_ne on stat_new). *)
          (* Helper: given any k_z ∈ A with items2[k_z] ≠ SOMEV, extract
             (τ_z, v_z) with stat2 !! τ_z = OpEnqReserved v_z k_z, τ_z ≠ τ. *)
          assert (Hsuffix_extract :
                    ∀ k_z, k_z ∈ A →
                      (∀ w, items2 !! k_z ≠ Some (SOMEV w)) →
                      k_z ≠ Z.to_nat back_val2 →
                      ∃ τv : positive * val,
                        stat2 !! τv.1 = Some (OpEnqReserved τv.2 k_z) ∧
                        τv.1 ≠ τ).
          { intros k_z Hk_z_in_A Hk_z_not_some Hk_z_ne_bv.
            destruct HgoodA as [_ HgoodA_b].
            destruct (HgoodA_b k_z Hk_z_in_A) as [(v' & Hitem) | (τ_e & v_e & Hres_e)].
            - exfalso. apply (Hk_z_not_some v'). exact Hitem.
            - exists (τ_e, v_e).
              destruct (decide (τ_e = τ)) as [-> | Hne_τe].
              + (* τ_e = τ: stat_new[τ] = OpEnqReserved v_push back_val2.
                    So k_z = back_val2, contradiction. *)
                exfalso.
                rewrite lookup_insert_eq in Hres_e.
                injection Hres_e as _ Heq_kz.
                apply Hk_z_ne_bv. symmetry. exact Heq_kz.
              + simpl. split; last (intros ?; apply Hne_τe; congruence).
                rewrite lookup_insert_ne in Hres_e;
                  last (intros ?; apply Hne_τe; congruence).
                exact Hres_e. }
          (* Build suffix_pushes: for each k_z in drop (Datatypes.S k) seq, extract
             (τ_z, v_z). We do this by induction over (drop (Datatypes.S k) seq) but
             keep track of the position in seq for the membership argument. *)
          (* Use Fix-style: take indices [S k .. length seq), produce pushes list. *)
          (* For simplicity: build via a function on the list (drop (Datatypes.S k) seq)
             with a strong invariant about each element. *)
          pose (suffix_list := drop (Datatypes.S k) seq).
          assert (Hsuffix_all_in_A : ∀ z' k_z, suffix_list !! z' = Some k_z →
                                     k_z ∈ A ∧
                                     (∀ w, items2 !! k_z ≠ Some (SOMEV w)) ∧
                                     k_z ≠ Z.to_nat back_val2).
          { intros z' k_z Hsuffix_z'.
            unfold suffix_list in Hsuffix_z'.
            (* k_z = seq !! (S k + z'). *)
            pose proof (lookup_drop seq (Datatypes.S k) z') as Hdrop_eq.
            rewrite Hdrop_eq in Hsuffix_z'.
            assert (Hseq_z : seq !! (Datatypes.S k + z') = Some k_z) by exact Hsuffix_z'.
            split_and!.
            - rewrite -Hsetof. apply elem_of_list_to_set.
              apply list_elem_of_lookup_2 with (Datatypes.S k + z'). exact Hseq_z.
            - intros w Hitem.
              eapply (Hsuffix_notSOMEV (Datatypes.S k + z') k_z); [|exact Hseq_z|exact Hitem]. lia.
            - intros Heq.
              eapply NoDup_lookup in HnodupSeq;
                [| exact Hseq_k | rewrite Heq in Hseq_z; exact Hseq_z]. lia. }
          (* Build suffix_pushes from suffix_list via dependent induction.
             We use a sig type to bundle the list together with its spec. *)
          assert (Hbuild_suffix :
                    ∃ suffix_pushes : list (positive * val),
                      length suffix_pushes = length suffix_list ∧
                      ∀ z' τ_z v_z,
                        suffix_pushes !! z' = Some (τ_z, v_z) →
                        ∃ k_z, suffix_list !! z' = Some k_z ∧
                               stat2 !! τ_z = Some (OpEnqReserved v_z k_z) ∧
                               τ_z ≠ τ).
          { clear -Hsuffix_extract Hsuffix_all_in_A.
            generalize dependent Hsuffix_all_in_A.
            generalize suffix_list as l. clear suffix_list.
            intros l.
            induction l as [|k_z l' IH]; intros Hl_correct.
            - exists []. split; first reflexivity.
              intros z' τ_z v_z Hpush. destruct z'; discriminate.
            - assert (H_kz : k_z ∈ A ∧
                            (∀ w, items2 !! k_z ≠ Some (SOMEV w)) ∧
                            k_z ≠ Z.to_nat back_val2).
              { apply (Hl_correct 0 k_z eq_refl). }
              destruct (Hsuffix_extract k_z (proj1 H_kz)
                                        (proj1 (proj2 H_kz))
                                        (proj2 (proj2 H_kz)))
                as [[τ_z v_z] [Hres Hne]].
              assert (Hl'_correct : ∀ z' k_z', l' !! z' = Some k_z' →
                                              k_z' ∈ A ∧
                                              (∀ w, items2 !! k_z' ≠ Some (SOMEV w)) ∧
                                              k_z' ≠ Z.to_nat back_val2).
              { intros z' k_z' Hz'.
                apply (Hl_correct (Datatypes.S z') k_z' Hz'). }
              destruct (IH Hl'_correct) as [suffix_tl [Hlen_tl Hspec_tl]].
              exists ((τ_z, v_z) :: suffix_tl). split.
              + simpl. f_equal. exact Hlen_tl.
              + intros z' τ_z' v_z' Hpush_z'.
                destruct z' as [|z''].
                * simpl in Hpush_z'. injection Hpush_z' as <- <-.
                  exists k_z. split_and!; try assumption.
                  reflexivity.
                * simpl in Hpush_z'.
                  destruct (Hspec_tl z'' τ_z' v_z' Hpush_z')
                    as (k_z' & Hsuffix_z'' & Hres' & Hne').
                  exists k_z'. split_and!; try assumption. }
          destruct Hbuild_suffix as [suffix_pushes [Hsuffix_pushes_len Hsuffix_pushes_spec]].
          pose (pushes := (τ, v_push) :: suffix_pushes).
          (* For each push in pushes, characterize (τ_z, v_z). *)
          assert (Hpushes_spec : ∀ z' τ_z v_z,
                    pushes !! z' = Some (τ_z, v_z) →
                    ∃ k_z, seq !! (k + z') = Some k_z ∧
                           ((<[τ:=OpEnqReserved v_push (Z.to_nat back_val2)]> stat2) !!
                              τ_z = Some (OpEnqReserved v_z k_z))).
          { intros z' τ_z v_z Hpush_z'.
            destruct z' as [|z'].
            - simpl in Hpush_z'. injection Hpush_z' as <- <-.
              exists (Z.to_nat back_val2). split.
              + rewrite -Hseq_k. f_equal. lia.
              + rewrite lookup_insert_eq. reflexivity.
            - simpl in Hpush_z'.
              destruct (Hsuffix_pushes_spec z' τ_z v_z Hpush_z')
                as (k_z & Hsuffix_z' & Hres & Hne_τz).
              exists k_z. split.
              + unfold suffix_list in Hsuffix_z'.
                rewrite lookup_drop in Hsuffix_z'.
                rewrite -Hsuffix_z'. f_equal. lia.
              + rewrite lookup_insert_ne; last (intros ?; apply Hne_τz; congruence).
                exact Hres. }
          (* Length of pushes is length seq - k. *)
          assert (Hpushes_len : length pushes = (length seq - k)%nat).
          { unfold pushes. simpl. rewrite Hsuffix_pushes_len.
            unfold suffix_list. rewrite length_drop.
            assert (Hk_lt : (k < length seq)%nat).
            { eapply lookup_lt_Some. exact Hseq_k. }
            lia. }
          (* NoDup pushes.*1. *)
          assert (Hnd_pushes_keys : NoDup pushes.*1).
          { apply NoDup_alt. intros i j x Hi Hj.
            rewrite list_lookup_fmap in Hi.
            rewrite list_lookup_fmap in Hj.
            apply fmap_Some in Hi as ([τ_i v_i] & Hpush_i & Heq_i).
            apply fmap_Some in Hj as ([τ_j v_j] & Hpush_j & Heq_j).
            simpl in Heq_i, Heq_j. subst x.
            assert (Hτj_eq : τ_i = τ_j) by congruence.
            destruct (Hpushes_spec i τ_i v_i Hpush_i)
              as (k_i & Hseq_i & Hstat_i).
            destruct (Hpushes_spec j τ_j v_j Hpush_j)
              as (k_j & Hseq_j & Hstat_j).
            (* From Hτj_eq : τ_i = τ_j, and Hstat_i, Hstat_j both give
               stat_new[τ_i] = Reserved at k_i (resp. k_j). Functional lookup → k_i = k_j. *)
            assert (Hki_eq_kj : k_i = k_j).
            { rewrite -Hτj_eq in Hstat_j.
              rewrite Hstat_i in Hstat_j. injection Hstat_j as _ Heq_kij. exact Heq_kij. }
            assert (Hi_lt : (i < length pushes)%nat).
            { eapply lookup_lt_Some. exact Hpush_i. }
            assert (Hj_lt : (j < length pushes)%nat).
            { eapply lookup_lt_Some. exact Hpush_j. }
            assert (Hki_lt : (k + i < length seq)%nat).
            { eapply lookup_lt_Some. exact Hseq_i. }
            assert (Hkj_lt : (k + j < length seq)%nat).
            { eapply lookup_lt_Some. exact Hseq_j. }
            assert (Heq_indices : k + i = k + j).
            { rewrite Hki_eq_kj in Hseq_i.
              eapply NoDup_lookup in HnodupSeq;
                [|exact Hseq_i|exact Hseq_j]. exact HnodupSeq. }
            lia. }
          (* Each push (τ_z, v_z) ∈ pushes has stat[τ_z] = OpEnqReserved v_z k_z
             (for new stat). For the chain helper, we need pushes ⊆
             pending_push_of_config (s_pre, π_pre). That's: π_pre[τ_z] = Pending. *)
          assert (Hpushes_pending : Forall
                    (λ pv : positive * val,
                       π_pre !! pv.1 = Some (encode_request (Push pv.2), None))
                    pushes).
          { apply Forall_lookup. intros z' [τ_z v_z] Hpush_z'.
            simpl.
            destruct (Hpushes_spec z' τ_z v_z Hpush_z') as (k_z & Hseq_z & Hstat_new_z).
            destruct (decide (τ_z = τ)) as [-> | Hne_τz].
            - (* τ_z = τ. π_pre[τ] = Pending Push v_push from Hsc2 τ. *)
              rewrite lookup_insert_eq in Hstat_new_z.
              injection Hstat_new_z as <- _.
              pose proof (Hsc2 τ) as Hsc2_τ.
              rewrite Hstat_τ in Hsc2_τ.
              apply (Hsc2_τ s_pre π_pre Hin_pre).
            - (* τ_z ≠ τ. stat2[τ_z] = OpEnqReserved v_z k_z. *)
              rewrite lookup_insert_ne in Hstat_new_z;
                last (intros ?; apply Hne_τz; congruence).
              (* From Hres_pre with i_e ∉ A_pre. We need to show k_z ∉ A_pre. *)
              destruct z' as [|z''].
              + (* z' = 0, k_z = back_val2. back_val2 ∉ A_pre? *)
                assert (Hk_z_eq_bv : k_z = Z.to_nat back_val2).
                { replace (k + 0)%nat with k in Hseq_z by lia.
                  rewrite Hseq_k in Hseq_z.
                  injection Hseq_z as ->. reflexivity. }
                rewrite Hk_z_eq_bv in Hstat_new_z.
                (* By Hres_pre OLD with i_e = back_val2 ∉ A_pre. *)
                destruct (Hres_pre τ_z v_z (Z.to_nat back_val2) Hstat_new_z)
                  as [_ Hres_pre_z].
                apply Hres_pre_z.
                (* Need back_val2 ∉ A_pre. *)
                intros Habs.
                unfold A_pre in Habs. apply elem_of_list_to_set in Habs.
                apply list_elem_of_lookup_1 in Habs as [n' Hseq_pre_n'].
                unfold seq_pre in Hseq_pre_n'.
                pose proof (proj1 (lookup_take_Some _ _ _ _) Hseq_pre_n')
                  as [Hseq_n' Hn'_lt_k].
                eapply NoDup_lookup in HnodupSeq;
                  [|exact Hseq_n'|exact Hseq_k]. lia.
              + (* z' = S z''. We need k_z ∉ A_pre. *)
                destruct (Hres_pre τ_z v_z k_z Hstat_new_z) as [_ Hres_pre_z].
                apply Hres_pre_z.
                (* k_z ∉ A_pre because k_z = seq[k + (S z'')] = seq[k+1+z''],
                   which is in the suffix. If k_z were in A_pre = take k seq,
                   by NoDup seq, k + (S z'') < k. Contradiction. *)
                intros Habs.
                unfold A_pre in Habs. apply elem_of_list_to_set in Habs.
                apply list_elem_of_lookup_1 in Habs as [n' Hseq_pre_n'].
                unfold seq_pre in Hseq_pre_n'.
                pose proof (proj1 (lookup_take_Some _ _ _ _) Hseq_pre_n')
                  as [Hseq_n' Hn'_lt_k].
                eapply NoDup_lookup in HnodupSeq;
                  [|exact Hseq_n'|exact Hseq_z]. lia. }
          (* pushes ⊆ pending_push_of_config (s_pre, π_pre). *)
          assert (Hpushes_subseteq : pushes ⊆ pending_push_of_config (s_pre, π_pre)).
          { intros pv Hpv_in.
            apply list_elem_of_lookup_1 in Hpv_in as [z' Hpv_z'].
            rewrite Forall_lookup in Hpushes_pending.
            specialize (Hpushes_pending z' pv Hpv_z').
            destruct pv as [τ_z v_z].
            simpl in Hpushes_pending.
            apply pending_push_of_config_lookup.
            simpl. exact Hpushes_pending. }
          (* pushes ∈ all_push_lists (pending_push_of_config (s_pre, π_pre)). *)
          assert (Hpushes_in_all : pushes ∈ all_push_lists
                                      (pending_push_of_config (s_pre, π_pre))).
          { unfold all_push_lists.
            apply list_elem_of_bind.
            exists pushes. split.
            - apply permutations_refl.
            - apply powermset_submseteq.
              apply NoDup_submseteq.
              + eapply NoDup_fmap_1. exact Hnd_pushes_keys.
              + exact Hpushes_subseteq. }
          (* pushes is stat-conformant: all pv have stat2'[pv.1] = Reserved.
             For z = 0: pv = (τ, v_push), stat2'[τ] = Reserved v_push back_val2.
             For z > 0: stat2'[pv.1] = stat2[pv.1] = Reserved v_z k_z (from Hpushes_spec). *)
          assert (Hpushes_conformant : forallb pv_conformant pushes = true).
          { apply forallb_forall. intros pv Hpv_in.
            apply list_elem_of_In in Hpv_in.
            apply list_elem_of_lookup_1 in Hpv_in as [z' Hpv_z'].
            destruct pv as [τ_z v_z].
            destruct (Hpushes_spec z' τ_z v_z Hpv_z') as (k_z & _ & Hstat_z).
            unfold pv_conformant. simpl. unfold stat2'. rewrite Hstat_z. reflexivity. }
          assert (Hpushes_in_filtered : pushes ∈ push_lists_filtered (s_pre, π_pre)).
          { unfold push_lists_filtered.
            apply list_elem_of_In, filter_In. split.
            - apply list_elem_of_In. exact Hpushes_in_all.
            - exact Hpushes_conformant. }
          (* Apply Hwit_LP to get linearized config in M_full_new2. *)
          assert (Hcfg_pre_in_cfgs : (s_pre, π_pre) ∈ cfgs).
          { unfold cfgs. by apply elem_of_elements. }
          rewrite Forall_forall in Hwit_LP.
          pose proof (Hwit_LP (s_pre, π_pre) Hcfg_pre_in_cfgs) as Hwit_cfg_pre.
          rewrite Forall_forall in Hwit_cfg_pre.
          pose proof (Hwit_cfg_pre pushes Hpushes_in_filtered) as Hlin_in_full.
          (* Move to M_g_new2 via HM_full_new2_eq. *)
          rewrite HM_full_new2_eq in Hlin_in_full.
          rewrite elem_of_set_to_propset in Hlin_in_full.
          (* Provide the linearized config as (s, π). *)
          set (lin_cfg := lineraize_pending_push pushes (s_pre, π_pre)) in *.
          exists lin_cfg.1, lin_cfg.2. split_and!.
          * (* Membership. Use surjective_pairing on lin_cfg. *)
            rewrite -(surjective_pairing lin_cfg). exact Hlin_in_full.
          * (* length: lin_cfg.1 = s_pre ++ pushes.*2, length = k + (length seq - k) = length seq. *)
            unfold lin_cfg, lineraize_pending_push.
            cbn [fst snd].
            rewrite length_app.
            (* Replace length pushes.*2 with length pushes via length_fmap. *)
            replace (length pushes.*2) with (length pushes)
              by (symmetry; apply length_fmap).
            assert (Hlen_seq_pre : length seq_pre = k).
            { unfold seq_pre. rewrite length_take.
              assert (Hk_lt : (k < length seq)%nat).
              { eapply lookup_lt_Some. exact Hseq_k. }
              lia. }
            simpl in Hlen_pre.
            rewrite Hlen_pre.
            rewrite Hlen_seq_pre.
            rewrite Hpushes_len.
            assert (Hk_lt : (k < length seq)%nat).
            { eapply lookup_lt_Some. exact Hseq_k. }
            lia.
          * (* slots-based match. *)
            intros n k_n Hseq_n v Hslot_kn.
            unfold lin_cfg, lineraize_pending_push. simpl.
            (* Case-split on n < k vs n ≥ k. *)
            destruct (decide (n < k)%nat) as [Hn_lt | Hn_ge].
            -- (* n < k: use Hsmatch_pre. *)
               rewrite lookup_app_l; last (rewrite Hlen_pre; unfold seq_pre;
                 rewrite length_take;
                 assert (Hk_lt : (k < length seq)%nat) by (eapply lookup_lt_Some; exact Hseq_k);
                 lia).
               apply Hsmatch_pre with k_n; last exact Hslot_kn.
               unfold seq_pre. rewrite lookup_take_lt; [exact Hseq_n | exact Hn_lt].
            -- (* n ≥ k. *)
               assert (Hn_ge' : (k ≤ n)%nat) by lia.
               (* For n = k: seq[k] = back_val2. But slots[back_val2] = None
                  (pre-FAA back). So Hslot_kn (slots[k_n] = Some v) requires k_n
                  ≠ back_val2. *)
               assert (Hbv_no_slot : slots2 !! Z.to_nat back_val2 = None).
               { destruct (slots2 !! Z.to_nat back_val2) as [v_w|] eqn:Hbv_slot;
                   last reflexivity. exfalso.
                 pose proof (Hbnd2 _ _ Hbv_slot). lia. }
               (* For n > k: by Hsuffix_notSOMEV, items[k_n] ≠ SOMEV.
                  But slots[k_n] = Some v means items[k_n] = SOMEV v or NONEV
                  (slots_consistent direction 1). Both cases need handling. *)
               destruct (decide (n = k)) as [-> | Hn_ne].
               ++ (* n = k. seq[k] = back_val2. *)
                  rewrite Hseq_n in Hseq_k. injection Hseq_k as ->.
                  rewrite Hbv_no_slot in Hslot_kn. discriminate.
               ++ (* n > k. *)
                  assert (Hk_lt_n : (k < n)%nat) by lia.
                  destruct Hsc_slots2 as [Hsc_a Hsc_b].
                  (* Need slots[k_n] = Some v → items[k_n] = SOMEV v ∨ NONEV. *)
                  pose proof (Hsc_a k_n v Hslot_kn) as [_ Hitems_kn].
                  destruct Hitems_kn as [Hitem_some | Hitem_none].
                  ** (* items[k_n] = SOMEV v. *)
                     exfalso.
                     eapply (Hsuffix_notSOMEV n k_n v);
                       [exact Hk_lt_n | exact Hseq_n | exact Hitem_some].
                  ** (* items[k_n] = NONEV. slots[k_n] = Some v.
                        By slots_stat_iff (b): ∃ τ_w with stat_owns at i = k_n.
                        That is, stat2[τ_w] = OpEnqStored v k_n or OpEnqDone v k_n.
                        For our seq matching: n = k + z' with z' > 0.
                        We need s_lin[n] = Some v.
                        s_lin = s_pre ++ pushes.*2.
                        For n = k + z' with z' < length pushes: s_lin[n] = pushes.*2[z' - 1]
                        wait z' = n - k.
                        suffix_pushes[z'-1] = (τ_z, v_z) with stat2[τ_z] = Reserved v_z k_n.
                        But stat[τ_w] = Stored/Done at k_n contradicts (FAA-uniqueness)
                        with stat[τ_z] = Reserved at k_n (different stat states for
                        same index k_n). So this case is impossible.
                        Hence we derive contradiction. *)
                     exfalso.
                     destruct Hssi2 as (_ & Hssi_b & Hssi_c & _).
                     destruct (Hssi_b k_n v Hslot_kn) as (τ_w & Hstat_w).
                     (* τ_w has stat[τ_w] ∈ {Stored, Done} at k_n. *)
                     assert (Hk_n_in_A : k_n ∈ A).
                     { rewrite -Hsetof. apply elem_of_list_to_set.
                       apply list_elem_of_lookup_2 with n. exact Hseq_n. }
                     assert (Hk_n_no_some : ∀ w, items2 !! k_n ≠ Some (SOMEV w)).
                     { intros w Habs. eapply (Hsuffix_notSOMEV n k_n w);
                         [exact Hk_lt_n | exact Hseq_n | exact Habs]. }
                     assert (Hk_n_ne_bv : k_n ≠ Z.to_nat back_val2).
                     { intros ->. eapply NoDup_lookup in HnodupSeq;
                         [|exact Hseq_n|exact Hseq_k]. lia. }
                     (* From GoodEnqSet (NEW), since items[k_n] = NONEV ≠ SOMEV:
                        ∃ τ_e, stat_new[τ_e] = OpEnqReserved v_e k_n. *)
                     destruct HgoodA as [_ HgoodA_b].
                     destruct (HgoodA_b k_n Hk_n_in_A)
                       as [(w' & Hitem_w') | (τ_e & v_e & Hres_e)].
                     --- exfalso. apply (Hk_n_no_some w'). exact Hitem_w'.
                     --- (* τ_e at OpEnqReserved at k_n in NEW. τ_w at Stored/Done at k_n in stat2. *)
                         (* First: τ_e ≠ τ since k_n ≠ back_val2. *)
                         assert (Hne_τe_τ : τ_e ≠ τ).
                         { intros ->. rewrite lookup_insert_eq in Hres_e.
                           injection Hres_e as _ Heq_kn. apply Hk_n_ne_bv. symmetry. exact Heq_kn. }
                         (* So stat2[τ_e] = OpEnqReserved v_e k_n. *)
                         assert (Hres_e_old : stat2 !! τ_e = Some (OpEnqReserved v_e k_n)).
                         { rewrite lookup_insert_ne in Hres_e;
                             [exact Hres_e | intros ?; apply Hne_τe_τ; congruence]. }
                         (* Apply OLD FAA-uniqueness Hssi_c on stat2. *)
                         assert (Hstat_e_old : stat_faad stat2 τ_e v_e k_n)
                           by (left; exact Hres_e_old).
                         assert (Hstat_w_old : stat_faad stat2 τ_w v k_n).
                         { destruct Hstat_w as [Hstat_w|Hstat_w].
                           - right. left. exact Hstat_w.
                           - right. right. exact Hstat_w. }
                         assert (Hτe_eq_τw : τ_e = τ_w)
                           by (apply (Hssi_c _ _ _ _ _ Hstat_e_old Hstat_w_old)).
                         subst τ_w.
                         destruct Hstat_w as [Hstat_w|Hstat_w];
                           rewrite Hres_e_old in Hstat_w; discriminate.
          * (* items+stat match: for each (n, k_n) ∈ seq, either items SOMEV with
               s[n] = v, OR ∃ τ_e at OpEnqReserved with i_e = k_n and s[n] = v_e. *)
            intros n k_n Hseq_n.
            (* Case-split on n < k vs n = k vs n > k. *)
            destruct (decide (n < k)%nat) as [Hn_lt | Hn_ge].
            -- (* n < k: use Hsmatch_case_pre for (A_pre, seq_pre). *)
               assert (Hseq_pre_n : seq_pre !! n = Some k_n).
               { unfold seq_pre. rewrite lookup_take_lt; [exact Hseq_n | exact Hn_lt]. }
               destruct (Hsmatch_case_pre n k_n Hseq_pre_n)
                 as [(v' & Hitem_v' & Hspre_n) | (τ_e & v_e & Hres_e & Hspre_n)].
               ++ left. exists v'. split; first exact Hitem_v'.
                  unfold lin_cfg, lineraize_pending_push. simpl.
                  rewrite lookup_app_l; last (rewrite Hlen_pre; unfold seq_pre;
                    rewrite length_take;
                    assert (Hk_lt : (k < length seq)%nat) by (eapply lookup_lt_Some; exact Hseq_k);
                    lia).
                  exact Hspre_n.
               ++ right. exists τ_e, v_e. split.
                  ** apply Hstat_new_ne; last exact Hres_e.
                     intros ->. rewrite Hres_e in Hstat_τ. discriminate.
                  ** unfold lin_cfg, lineraize_pending_push. simpl.
                     rewrite lookup_app_l; last (rewrite Hlen_pre; unfold seq_pre;
                       rewrite length_take;
                       assert (Hk_lt : (k < length seq)%nat) by (eapply lookup_lt_Some; exact Hseq_k);
                       lia).
                     exact Hspre_n.
            -- (* n ≥ k. Use the OpEnqReserved branch in the suffix. *)
               assert (Hn_ge' : (k ≤ n)%nat) by lia.
               right.
               (* Index z' = n - k. push at z' is (τ_z, v_z) with
                  stat_new[τ_z] = OpEnqReserved v_z (seq[k + z'] = k_n). *)
               set (z' := (n - k)%nat).
               assert (Hz'_eq : (k + z' = n)%nat) by lia.
               assert (Hz'_lt : (z' < length pushes)%nat).
               { rewrite Hpushes_len.
                 assert (Hn_lt_len : (n < length seq)%nat).
                 { eapply lookup_lt_Some. exact Hseq_n. }
                 lia. }
               (* pushes !! z' is Some (τ_z, v_z). *)
               destruct (pushes !! z') as [[τ_z v_z]|] eqn:Hpush_z';
                 last (exfalso; apply lookup_lt_is_Some_2 in Hz'_lt;
                       destruct Hz'_lt as [x Hbad]; rewrite Hbad in Hpush_z'; discriminate).
               destruct (Hpushes_spec z' τ_z v_z Hpush_z')
                 as (k_z & Hseq_z & Hstat_z).
               rewrite Hz'_eq in Hseq_z.
               rewrite Hseq_z in Hseq_n. injection Hseq_n as ->.
               exists τ_z, v_z.
               split; first exact Hstat_z.
               (* s_lin[n] = (s_pre ++ pushes.*2)[n] = pushes.*2[z'] = v_z. *)
               unfold lin_cfg, lineraize_pending_push. cbn [fst snd].
               rewrite lookup_app_r;
                 last (rewrite Hlen_pre; unfold seq_pre;
                       rewrite length_take;
                       assert (Hk_lt : (k < length seq)%nat) by (eapply lookup_lt_Some; exact Hseq_k);
                       lia).
               rewrite Hlen_pre.
               assert (Hlen_seq_pre : length seq_pre = k).
               { unfold seq_pre. rewrite length_take.
                 assert (Hk_lt : (k < length seq)%nat) by (eapply lookup_lt_Some; exact Hseq_k);
                 lia. }
               rewrite Hlen_seq_pre.
               replace (n - k)%nat with z' by lia.
               rewrite list_lookup_fmap. rewrite Hpush_z'. reflexivity.
          * (* OpEnqDone preservation. *)
            intros τ_d v_d i_d Hstat_d_new.
            unfold lin_cfg, lineraize_pending_push. simpl.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            -- rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_d_new;
                 last (intros ?; apply Hne_τd; congruence).
               (* π_pre[τ_d] = LP'd from OLD Henq_pre. Need π_lin[τ_d] = LP'd.
                  π_lin = map_imap (λ τ x, if τ ∈ pushes.*1 then LP'd else x) π_pre.
                  τ_d ∉ pushes.*1: pushes has Reserved τ's (in NEW stat), but
                  τ_d at OpEnqDone. By FAA-uniqueness, τ_d ≠ any τ_z in pushes
                  (their stat statuses differ at any i, by reasoning about
                  stat_faad-uniqueness; but easier: pushes only has (τ, _) and
                  (τ_z', _) with stat_new[τ_z'] = OpEnqReserved). For τ_d at
                  OpEnqDone, τ_d ≠ τ (already), and τ_d ≠ τ_z' since stat_new[τ_z']
                  = OpEnqReserved ≠ OpEnqDone. *)
               assert (Hτd_notin : τ_d ∉ pushes.*1).
               { intros Habs. apply list_elem_of_lookup_1 in Habs as [z' Hτd_z'].
                 rewrite list_lookup_fmap in Hτd_z'.
                 apply fmap_Some in Hτd_z' as ([τ_z v_z] & Hpush_z' & Heq).
                 simpl in Heq. subst τ_z.
                 destruct (Hpushes_spec z' τ_d v_z Hpush_z') as (k_z & _ & Hstat_z).
                 rewrite lookup_insert_ne in Hstat_z;
                   last (intros ?; apply Hne_τd; congruence).
                 rewrite Hstat_d_new in Hstat_z. discriminate. }
               rewrite map_lookup_imap.
               pose proof (Henq_pre τ_d v_d i_d Hstat_d_new) as Hπpre.
               rewrite Hπpre /=. rewrite bool_decide_eq_false_2; last exact Hτd_notin.
               reflexivity.
          * (* OpDeqLinearized preservation. *)
            intros τ_d v_d Hstat_d_new.
            unfold lin_cfg, lineraize_pending_push. simpl.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            -- rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_d_new;
                 last (intros ?; apply Hne_τd; congruence).
               assert (Hτd_notin : τ_d ∉ pushes.*1).
               { intros Habs. apply list_elem_of_lookup_1 in Habs as [z' Hτd_z'].
                 rewrite list_lookup_fmap in Hτd_z'.
                 apply fmap_Some in Hτd_z' as ([τ_z v_z] & Hpush_z' & Heq).
                 simpl in Heq. subst τ_z.
                 destruct (Hpushes_spec z' τ_d v_z Hpush_z') as (k_z & _ & Hstat_z).
                 rewrite lookup_insert_ne in Hstat_z;
                   last (intros ?; apply Hne_τd; congruence).
                 rewrite Hstat_d_new in Hstat_z. discriminate. }
               rewrite map_lookup_imap.
               pose proof (Hlin_pre τ_d v_d Hstat_d_new) as Hπpre.
               rewrite Hπpre /=. rewrite bool_decide_eq_false_2; last exact Hτd_notin.
               reflexivity.
          * (* OpDeqDone preservation. *)
            intros τ_d v_d Hstat_d_new.
            unfold lin_cfg, lineraize_pending_push. simpl.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            -- rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_d_new;
                 last (intros ?; apply Hne_τd; congruence).
               assert (Hτd_notin : τ_d ∉ pushes.*1).
               { intros Habs. apply list_elem_of_lookup_1 in Habs as [z' Hτd_z'].
                 rewrite list_lookup_fmap in Hτd_z'.
                 apply fmap_Some in Hτd_z' as ([τ_z v_z] & Hpush_z' & Heq).
                 simpl in Heq. subst τ_z.
                 destruct (Hpushes_spec z' τ_d v_z Hpush_z') as (k_z & _ & Hstat_z).
                 rewrite lookup_insert_ne in Hstat_z;
                   last (intros ?; apply Hne_τd; congruence).
                 rewrite Hstat_d_new in Hstat_z. discriminate. }
               rewrite map_lookup_imap.
               pose proof (Hdone_pre τ_d v_d Hstat_d_new) as Hπpre.
               rewrite Hπpre /=. rewrite bool_decide_eq_false_2; last exact Hτd_notin.
               reflexivity.
          * (* OpDeqPending preservation. *)
            intros τ_d Hstat_d_new.
            unfold lin_cfg, lineraize_pending_push. simpl.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            -- rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_d_new;
                 last (intros ?; apply Hne_τd; congruence).
               assert (Hτd_notin : τ_d ∉ pushes.*1).
               { intros Habs. apply list_elem_of_lookup_1 in Habs as [z' Hτd_z'].
                 rewrite list_lookup_fmap in Hτd_z'.
                 apply fmap_Some in Hτd_z' as ([τ_z v_z] & Hpush_z' & Heq).
                 simpl in Heq. subst τ_z.
                 destruct (Hpushes_spec z' τ_d v_z Hpush_z') as (k_z & _ & Hstat_z).
                 rewrite lookup_insert_ne in Hstat_z;
                   last (intros ?; apply Hne_τd; congruence).
                 rewrite Hstat_d_new in Hstat_z. discriminate. }
               rewrite map_lookup_imap.
               pose proof (Hpending_pre τ_d Hstat_d_new) as Hπpre.
               rewrite Hπpre /=. rewrite bool_decide_eq_false_2; last exact Hτd_notin.
               reflexivity.
          * (* OpEnqStored preservation: unconditional LP'd. *)
            intros τ_e v_e i_e Hstat_e_new.
            unfold lin_cfg, lineraize_pending_push. simpl.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            -- rewrite lookup_insert_eq in Hstat_e_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_e_new;
                 last (intros ?; apply Hne_τe; congruence).
               (* OLD STRENGTHENED Hstored_pre: π_pre[τ_e] = LP'd unconditionally. *)
               pose proof (Hstored_pre τ_e v_e i_e Hstat_e_new) as Hπpre_LP.
               assert (Hτe_notin : τ_e ∉ pushes.*1).
               { intros Habs. apply list_elem_of_lookup_1 in Habs as [z' Hτe_z'].
                 rewrite list_lookup_fmap in Hτe_z'.
                 apply fmap_Some in Hτe_z' as ([τ_z v_z] & Hpush_z' & Heq).
                 simpl in Heq. subst τ_z.
                 destruct (Hpushes_spec z' τ_e v_z Hpush_z') as (k_z & _ & Hstat_z).
                 rewrite lookup_insert_ne in Hstat_z;
                   last (intros ?; apply Hne_τe; congruence).
                 rewrite Hstat_e_new in Hstat_z. discriminate. }
               rewrite map_lookup_imap.
               rewrite Hπpre_LP /=.
               rewrite bool_decide_eq_false_2; last exact Hτe_notin.
               reflexivity.
          * (* OpEnqReserved disjunctive — main new case. *)
            intros τ_e v_e i_e Hstat_e_new.
            unfold lin_cfg, lineraize_pending_push. simpl.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            -- (* τ_e = τ: stat_new[τ] = OpEnqReserved v_push back_val2.
                  i_e = back_val2, v_e = v_push.
                  In Case B, back_val2 ∈ A.
                  τ ∈ pushes.*1 (at z' = 0). So π_lin[τ] = LP'd. *)
               rewrite lookup_insert_eq in Hstat_e_new.
               injection Hstat_e_new as <- <-.
               split.
               ++ intros _.
                  (* π_lin[τ] = LP'd: τ ∈ pushes.*1. *)
                  assert (Hτ_in : τ ∈ pushes.*1).
                  { apply list_elem_of_lookup_2 with 0.
                    rewrite list_lookup_fmap. simpl. reflexivity. }
                  rewrite map_lookup_imap.
                  pose proof (Hsc2 τ) as Hsc2_τ. rewrite Hstat_τ in Hsc2_τ.
                  pose proof (Hsc2_τ s_pre π_pre Hin_pre) as Hπpre_τ.
                  rewrite Hπpre_τ /=.
                  rewrite bool_decide_eq_true_2; last exact Hτ_in.
                  reflexivity.
               ++ intros Hbv_nin_A.
                  exfalso. apply Hbv_nin_A.
                  rewrite -Hsetof. apply elem_of_list_to_set.
                  apply list_elem_of_lookup_2 with k. exact Hseq_k.
            -- (* τ_e ≠ τ. stat2[τ_e] = OpEnqReserved v_e i_e. *)
               rewrite lookup_insert_ne in Hstat_e_new;
                 last (intros ?; apply Hne_τe; congruence).
               split.
               ++ (* i_e ∈ A: need π_lin[τ_e] = LP'd. *)
                  intros Hie_in_A.
                  (* i_e = seq[z] for some z. Cases: z < k, z = k, z > k. *)
                  rewrite -Hsetof in Hie_in_A. apply elem_of_list_to_set in Hie_in_A.
                  apply list_elem_of_lookup_1 in Hie_in_A as [z Hseq_z].
                  destruct (decide (z < k)%nat) as [Hzk | Hzk].
                  ** (* z < k. i_e ∈ A_pre. By OLD Hres_pre: π_pre[τ_e] = LP'd.
                        τ_e ∉ pushes.*1 (we need to show). *)
                     assert (Hi_e_in_A_pre : i_e ∈ A_pre).
                     { unfold A_pre. apply elem_of_list_to_set.
                       apply list_elem_of_lookup_2 with z.
                       unfold seq_pre. rewrite lookup_take_lt; [exact Hseq_z | exact Hzk]. }
                     destruct (Hres_pre τ_e v_e i_e Hstat_e_new) as [Hres_in _].
                     pose proof (Hres_in Hi_e_in_A_pre) as Hπpre_LP.
                     assert (Hτe_notin : τ_e ∉ pushes.*1).
                     { intros Habs. apply list_elem_of_lookup_1 in Habs as [z' Hτe_z'].
                       rewrite list_lookup_fmap in Hτe_z'.
                       apply fmap_Some in Hτe_z' as ([τ_z v_z] & Hpush_z' & Heq).
                       simpl in Heq. subst τ_z.
                       destruct (Hpushes_spec z' τ_e v_z Hpush_z') as (k_z & Hseq_kz & Hstat_z).
                       rewrite lookup_insert_ne in Hstat_z;
                         last (intros ?; apply Hne_τe; congruence).
                       (* stat2[τ_e] = Reserved v_e i_e and stat2[τ_e] = Reserved v_z k_z.
                          By functional lookup, v_z = v_e and k_z = i_e.
                          seq[z] = i_e = k_z = seq[k + z']. By NoDup seq, z = k + z'.
                          But z < k. So k + z' < k. So z' < 0, impossible.*)
                       rewrite Hstat_e_new in Hstat_z. injection Hstat_z as <- <-.
                       eapply NoDup_lookup in HnodupSeq;
                         [|exact Hseq_z|exact Hseq_kz]. lia. }
                     rewrite map_lookup_imap.
                     rewrite Hπpre_LP /=.
                     rewrite bool_decide_eq_false_2; last exact Hτe_notin.
                     reflexivity.
                  ** assert (Hk_le_z : (k ≤ z)%nat) by lia.
                     destruct (decide (z = k)) as [-> | Hzk_ne].
                     --- (* z = k: i_e = back_val2. But stat2[τ_e] = Reserved v_e back_val2
                            with τ_e ≠ τ. By slots_bounded2, Reserved index < back_val2.
                            But here index = back_val2. Contradiction. *)
                         rewrite Hseq_k in Hseq_z. injection Hseq_z as Heq_ie. subst i_e.
                         destruct Hssi2 as (_ & _ & _ & Hssi_d).
                         assert (Hstat_faad : stat_faad stat2 τ_e v_e (Z.to_nat back_val2))
                           by (left; exact Hstat_e_new).
                         pose proof (Hssi_d _ _ _ Hstat_faad). lia.
                     --- (* z > k. i_e = seq[z] is in the suffix.
                            τ_e is in pushes (at z' = z - k). So π_lin[τ_e] = LP'd. *)
                         assert (Hk_lt_z : (k < z)%nat) by lia.
                         set (z' := (z - k)%nat).
                         assert (Hz'_eq : (k + z' = z)%nat) by lia.
                         assert (Hz'_pos : (0 < z')%nat) by lia.
                         (* pushes !! z' = (τ_e', v_e') with stat2[τ_e'] = Reserved v_e' i_e. *)
                         assert (Hz'_lt : (z' < length pushes)%nat).
                         { rewrite Hpushes_len.
                           assert (Hz_lt : (z < length seq)%nat).
                           { eapply lookup_lt_Some. exact Hseq_z. }
                           lia. }
                         destruct (pushes !! z') as [[τ_e' v_e']|] eqn:Hpush_z';
                           last (exfalso; apply lookup_lt_is_Some_2 in Hz'_lt;
                                 destruct Hz'_lt as [x Hbad]; rewrite Hbad in Hpush_z'; discriminate).
                         destruct (Hpushes_spec z' τ_e' v_e' Hpush_z')
                           as (k_z & Hseq_kz & Hstat_z).
                         rewrite Hz'_eq in Hseq_kz.
                         rewrite Hseq_kz in Hseq_z. injection Hseq_z as Heq_ie. subst i_e.
                         (* Show τ_e' ≠ τ. *)
                         assert (Hne_τe'_τ : τ_e' ≠ τ).
                         { intros ->. rewrite lookup_insert_eq in Hstat_z.
                           injection Hstat_z as _ Heq_kz.
                           (* k_z = back_val2. So seq[z] = back_val2 = seq[k]. By NoDup, z = k. But k < z. *)
                           rewrite -Heq_kz in Hseq_kz.
                           eapply NoDup_lookup in HnodupSeq;
                             [|exact Hseq_kz|exact Hseq_k]. lia. }
                         rewrite lookup_insert_ne in Hstat_z;
                           [|intros ?; apply Hne_τe'_τ; congruence].
                         (* Apply FAA-uniqueness on stat2 to derive τ_e = τ_e'. *)
                         destruct Hssi2 as (_ & _ & Hssi_c & _).
                         assert (Hτe_eq_τe' : τ_e = τ_e').
                         { apply (Hssi_c τ_e τ_e' v_e v_e' k_z);
                             [left; exact Hstat_e_new | left; exact Hstat_z]. }
                         subst τ_e'.
                         (* So τ_e ∈ pushes.*1. *)
                         assert (Hτe_in : τ_e ∈ pushes.*1).
                         { apply list_elem_of_lookup_2 with z'.
                           rewrite list_lookup_fmap. rewrite Hpush_z'. simpl. reflexivity. }
                         rewrite map_lookup_imap.
                         pose proof (Hsc2 τ_e) as Hsc2_τe. rewrite Hstat_e_new in Hsc2_τe.
                         destruct Hsc2_τe as [Hsc2_τe_all _].
                         pose proof (Hsc2_τe_all s_pre π_pre Hin_pre) as Hπpre_τe.
                         destruct Hπpre_τe as [Hπpre_τe | Hπpre_τe];
                           rewrite Hπpre_τe /=;
                           rewrite bool_decide_eq_true_2; try exact Hτe_in;
                           reflexivity.
               ++ (* i_e ∉ A: need π_lin[τ_e] = Pending. *)
                  intros Hie_nin_A.
                  assert (Hi_e_nin_A_pre : i_e ∉ A_pre).
                  { intros Habs. apply Hie_nin_A.
                    unfold A_pre in Habs. apply elem_of_list_to_set in Habs.
                    apply list_elem_of_lookup_1 in Habs as [n' Hseq_pre_n'].
                    unfold seq_pre in Hseq_pre_n'.
                    pose proof (proj1 (lookup_take_Some _ _ _ _) Hseq_pre_n')
                      as [Hseq_n' _].
                    rewrite -Hsetof. apply elem_of_list_to_set.
                    apply list_elem_of_lookup_2 with n'. exact Hseq_n'. }
                  destruct (Hres_pre τ_e v_e i_e Hstat_e_new) as [_ Hres_nin].
                  pose proof (Hres_nin Hi_e_nin_A_pre) as Hπpre_Pending.
                  assert (Hτe_notin : τ_e ∉ pushes.*1).
                  { intros Habs. apply list_elem_of_lookup_1 in Habs as [z' Hτe_z'].
                    rewrite list_lookup_fmap in Hτe_z'.
                    apply fmap_Some in Hτe_z' as ([τ_z v_z] & Hpush_z' & Heq).
                    simpl in Heq. subst τ_z.
                    destruct (Hpushes_spec z' τ_e v_z Hpush_z') as (k_z & Hseq_kz & Hstat_z).
                    rewrite lookup_insert_ne in Hstat_z;
                      last (intros ?; apply Hne_τe; congruence).
                    rewrite Hstat_e_new in Hstat_z. injection Hstat_z as <- <-.
                    apply Hie_nin_A.
                    rewrite -Hsetof. apply elem_of_list_to_set.
                    apply list_elem_of_lookup_2 with (k + z'). exact Hseq_kz. }
                  rewrite map_lookup_imap.
                  rewrite Hπpre_Pending /=.
                  rewrite bool_decide_eq_false_2; last exact Hτe_notin.
                  reflexivity.
        + (* Case A: back_val2 ∉ A — straightforward. *)
          (* Derive OLD GoodEnqSet. *)
          assert (Hgood_old : GoodEnqSet A items2 stat2).
          { split.
            - intros k' v' Hitem_k'.
              destruct HgoodA as [Hgood_a _].
              exact (Hgood_a k' v' Hitem_k').
            - intros k' Hk'_in_A.
              destruct HgoodA as [_ Hgood2].
              destruct (Hgood2 k' Hk'_in_A) as [(v' & Hitem_v') | (τ_e & v_e & Hres_e)].
              + left. by exists v'.
              + right.
                destruct (decide (τ_e = τ)) as [-> | Hne_τe].
                * (* τ_e = τ. stat_new[τ] = OpEnqReserved at back_val2. So k' = back_val2.
                     But back_val2 ∉ A. Contradiction. *)
                  rewrite lookup_insert_eq in Hres_e.
                  injection Hres_e as _ Heq_k.
                  exfalso. apply Hbv_notin_A. rewrite Heq_k. exact Hk'_in_A.
                * exists τ_e, v_e.
                  rewrite lookup_insert_ne in Hres_e;
                    last (intros ?; apply Hne_τe; congruence).
                  exact Hres_e. }
          destruct (Hlinw_seq2 A seq Hgood_old HnodupSeq Hsetof HJInvSeq_old_full)
            as (s & π & Hin & HlenA & Hsmatch & Hsmatch_case & Henq & Hlin & Hdone & Hpending & Hstored & Hres).
          exists s, π. split_and!.
          * unfold M_g_new2. apply elem_of_union. left. exact Hin.
          * exact HlenA.
          * exact Hsmatch.
          * (* items+stat match: for each n, k_n in seq, either items SOMEV or OpEnqReserved.
               Lift via Hsmatch_case (OLD) but adjust stat for OpEnqReserved. *)
            intros n k_n Hseq_n.
            destruct (Hsmatch_case n k_n Hseq_n) as [Hitems_case | (τ_e & v_e & Hres_e & Hs_n)].
            -- left. exact Hitems_case.
            -- right. exists τ_e, v_e. split; last exact Hs_n.
               apply Hstat_new_ne; last exact Hres_e.
               intros ->. rewrite Hres_e in Hstat_τ. discriminate.
          * (* OpEnqDone preservation. *)
            intros τ_d v_d i_d Hstat_d_new.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            -- rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_d_new;
                 last (intros ?; apply Hne_τd; congruence).
               exact (Henq τ_d v_d i_d Hstat_d_new).
          * (* OpDeqLinearized preservation. *)
            intros τ_d v_d Hstat_d_new.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            -- rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_d_new;
                 last (intros ?; apply Hne_τd; congruence).
               exact (Hlin τ_d v_d Hstat_d_new).
          * (* OpDeqDone preservation. *)
            intros τ_d v_d Hstat_d_new.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            -- rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_d_new;
                 last (intros ?; apply Hne_τd; congruence).
               exact (Hdone τ_d v_d Hstat_d_new).
          * (* OpDeqPending preservation. *)
            intros τ_d Hstat_d_new.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            -- rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_d_new;
                 last (intros ?; apply Hne_τd; congruence).
               exact (Hpending τ_d Hstat_d_new).
          * (* OpEnqStored disjunctive preservation. *)
            intros τ_e v_e i_e Hstat_e_new.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            -- rewrite lookup_insert_eq in Hstat_e_new. discriminate.
            -- rewrite lookup_insert_ne in Hstat_e_new;
                 last (intros ?; apply Hne_τe; congruence).
               exact (Hstored τ_e v_e i_e Hstat_e_new).
          * (* OpEnqReserved disjunctive — main new case. *)
            intros τ_e v_e i_e Hstat_e_new.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            -- (* τ_e = τ: stat_new[τ] = OpEnqReserved v_push back_val2.
                  So i_e = back_val2. By Hbv_notin_A, back_val2 ∉ A. So we're in
                  the i_e ∉ A branch. We need π[τ] = (Push v_push, None).
                  From Hsc2 τ on M_g2: ∀ s π ∈ M_g2, π[τ] = (Push v_push, None).
                  (s, π) ∈ M_g2 from Hin. So done. *)
               rewrite lookup_insert_eq in Hstat_e_new.
               injection Hstat_e_new as <- <-.
               split.
               ++ intros HinA. exfalso. apply Hbv_notin_A. exact HinA.
               ++ intros _Hbv_ninA.
                  pose proof (Hsc2 τ) as Hsc2_τ. rewrite Hstat_τ in Hsc2_τ.
                  apply (Hsc2_τ s π Hin).
            -- rewrite lookup_insert_ne in Hstat_e_new;
                 last (intros ?; apply Hne_τe; congruence).
               exact (Hres τ_e v_e i_e Hstat_e_new).
      - (* slots_bounded: back_val grew from back_val2 to back_val2 + 1. *)
        intros i v Hslot. specialize (Hbnd2 i v Hslot). lia.
      - (* slots_stat_iff: τ now Reserved at back_val2. We use the back-bound
           clause to rule out collisions on back_val2. *)
        destruct Hssi2 as (Hssi_a & Hssi_b & Hssi_c & Hssi_d).
        assert (Hbv : (Z.of_nat (Z.to_nat back_val2) = back_val2)%Z)
          by lia.
        unfold stat_owns, stat_faad.
        split_and!.
        + intros τ' v' i' Howns.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          * destruct Howns as [Howns | Howns];
              rewrite lookup_insert_eq in Howns; discriminate.
          * apply (Hssi_a τ' v' i').
            destruct Howns as [Howns | Howns];
              rewrite lookup_insert_ne in Howns;
              try (intros ?; apply Hne_τ'; congruence);
              [left | right]; exact Howns.
        + intros i' v' Hslot'.
          destruct (Hssi_b i' v' Hslot') as (τ_w & Hstat_w).
          exists τ_w. destruct (decide (τ_w = τ)) as [-> | Hne_τw].
          * exfalso. destruct Hstat_w as [Hstat_w | Hstat_w];
              rewrite Hstat_τ in Hstat_w; discriminate.
          * destruct Hstat_w as [Hstat_w | Hstat_w];
              [left | right];
              rewrite lookup_insert_ne;
              try (intros ?; apply Hne_τw; congruence);
              exact Hstat_w.
        + intros τ_1 τ_2 v_1 v_2 i' Hτ1 Hτ2.
          destruct (decide (τ_1 = τ)) as [-> | Hne_τ1];
            destruct (decide (τ_2 = τ)) as [-> | Hne_τ2].
          * reflexivity.
          * (* τ_1=τ: Hτ1 has lookup_insert_eq giving the Reserved record. *)
            destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
              rewrite lookup_insert_eq in Hτ1; try discriminate.
            injection Hτ1 as Heqv Heqi. subst i'.
            (* τ_2 ≠ τ: Hτ2 is stat[τ_2] = Reserved/Stored/Done at back_val2. *)
            assert (Hτ2_old : stat_faad stat2 τ_2 v_2 (Z.to_nat back_val2)).
            { destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                rewrite lookup_insert_ne in Hτ2;
                try (intros ?; apply Hne_τ2; congruence).
              - left. exact Hτ2.
              - right. left. exact Hτ2.
              - right. right. exact Hτ2. }
            specialize (Hssi_d _ _ _ Hτ2_old). lia.
          * destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
              rewrite lookup_insert_eq in Hτ2; try discriminate.
            injection Hτ2 as Heqv Heqi. subst i'.
            assert (Hτ1_old : stat_faad stat2 τ_1 v_1 (Z.to_nat back_val2)).
            { destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                rewrite lookup_insert_ne in Hτ1;
                try (intros ?; apply Hne_τ1; congruence).
              - left. exact Hτ1.
              - right. left. exact Hτ1.
              - right. right. exact Hτ1. }
            specialize (Hssi_d _ _ _ Hτ1_old). lia.
          * (* Both ≠ τ: old uniq. *)
            assert (Hτ1_old : stat_faad stat2 τ_1 v_1 i').
            { destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                rewrite lookup_insert_ne in Hτ1;
                try (intros ?; apply Hne_τ1; congruence).
              - left. exact Hτ1.
              - right. left. exact Hτ1.
              - right. right. exact Hτ1. }
            assert (Hτ2_old : stat_faad stat2 τ_2 v_2 i').
            { destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                rewrite lookup_insert_ne in Hτ2;
                try (intros ?; apply Hne_τ2; congruence).
              - left. exact Hτ2.
              - right. left. exact Hτ2.
              - right. right. exact Hτ2. }
            apply (Hssi_c τ_1 τ_2 v_1 v_2 i' Hτ1_old Hτ2_old).
        + intros τ' v' i' Hstat'.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          * destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
              rewrite lookup_insert_eq in Hstat'; try discriminate.
            injection Hstat' as Heqv Heqi. subst i'.
            lia.
          * assert (Hstat'_old : stat_faad stat2 τ' v' i').
            { destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
                rewrite lookup_insert_ne in Hstat';
                try (intros ?; apply Hne_τ'; congruence).
              - left. exact Hstat'.
              - right. left. exact Hstat'.
              - right. right. exact Hstat'. }
            specialize (Hssi_d _ _ _ Hstat'_old). lia.
      - (* closure_push at Phase 2 FAA: τ transitions OpEnqPending → OpEnqReserved.
           Two cases on whether τ ∈ pushes.*1:
           - τ ∉ pushes.*1: lift via Hcl_push2 at pre-FAA stat2.
           - τ ∈ pushes.*1: requires M_g expansion via the helper lemma
             mcfg_steps_chain_lp_push_all_perm. *)
        intros cfg pushes Hin Hnd Hsubset Hstat_pushes.
        (* Helper: a config in M_g_new2 is either in M_g2 or is lineraize(inner_pushes, base) for some inner_pushes. *)
        assert (Hin_destruct :
                  cfg ∈ M_g2 ∨
                  ∃ (s_c : list val) (π_c : gmap positive proc_status)
                    (inner_pushes : list (positive * val)),
                    (s_c, π_c) ∈ M_g2 ∧
                    inner_pushes ∈ all_push_lists (pending_push_of_config (s_c, π_c)) ∧
                    forallb pv_conformant inner_pushes = true ∧
                    cfg = lineraize_pending_push inner_pushes (s_c, π_c)).
        { unfold M_g_new2 in Hin.
          apply elem_of_union in Hin as [Hin_g | Hin_lp]; first by left.
          right.
          unfold M_g_LP_τ in Hin_lp.
          apply elem_of_list_to_set in Hin_lp.
          apply list_elem_of_In, in_flat_map in Hin_lp as (cfg_base & Hcfg_in & Hin_map).
          apply list_elem_of_In in Hcfg_in.
          unfold cfgs in Hcfg_in. apply elem_of_elements in Hcfg_in.
          apply in_map_iff in Hin_map as (inner_pushes & Hy_eq & Hpushes_in).
          apply list_elem_of_In in Hpushes_in.
          unfold push_lists_filtered in Hpushes_in.
          apply list_elem_of_In, filter_In in Hpushes_in as [Hpushes_in_all Hcond].
          apply list_elem_of_In in Hpushes_in_all.
          destruct cfg_base as [s_c π_c].
          exists s_c, π_c, inner_pushes. split_and!.
          - exact Hcfg_in.
          - exact Hpushes_in_all.
          - exact Hcond.
          - symmetry. exact Hy_eq. }
        destruct (decide (τ ∈ pushes.*1)) as [Hτ_in | Hτ_notin].
        + destruct Hin_destruct as [Hin_g | (s_c & π_c & inner_pushes & Hbase_in & Hinner_in_all & Hinner_conf & ->)].
          * (* cfg ∈ M_g2: by construction of M_g_LP_τ. *)
            apply elem_of_union_r. unfold M_g_LP_τ.
            apply elem_of_list_to_set.
            apply list_elem_of_In, in_flat_map.
            exists cfg. split.
            -- apply list_elem_of_In. unfold cfgs. apply elem_of_elements. exact Hin_g.
            -- apply in_map_iff. exists pushes. split; first reflexivity.
               unfold push_lists_filtered.
               apply filter_In. split.
               ++ unfold all_push_lists.
                  apply list_elem_of_In, list_elem_of_bind.
                  exists pushes. split; first apply permutations_refl.
                  apply powermset_submseteq.
                  apply NoDup_submseteq; first (eapply NoDup_fmap_1; exact Hnd). exact Hsubset.
               ++ apply forallb_forall. intros pv Hpv_in.
                  apply list_elem_of_In in Hpv_in.
                  rewrite Hconf_iff. exact (Hstat_pushes pv Hpv_in).
          * (* cfg = lineraize inner_pushes (s_c, π_c).
               Combined pushes (inner ++ pushes) gives lineraize on base. *)
            (* Step 1: extract disjointness inner_pushes.*1 ∩ pushes.*1 = ∅. *)
            assert (Hinner_pending : Forall (λ pv,
                      π_c !! pv.1 = Some (encode_request (Push pv.2), None)) inner_pushes).
            { unfold all_push_lists in Hinner_in_all.
              apply list_elem_of_bind in Hinner_in_all as (sub & Hperm & Hsub_in_pset).
              rewrite permutations_Permutation in Hperm.
              rewrite powermset_submseteq in Hsub_in_pset.
              assert (Hinner_subset : inner_pushes ⊆ pending_push_of_config (s_c, π_c)).
              { intros pv Hpv_in. rewrite -Hperm in Hpv_in.
                eapply elem_of_submseteq; first exact Hpv_in. exact Hsub_in_pset. }
              apply Forall_forall. intros pv Hpv_in.
              destruct pv as [τ_x v_x].
              assert (Hpv_in_pending : (τ_x, v_x) ∈ pending_push_of_config (s_c, π_c))
                by (apply Hinner_subset; exact Hpv_in).
              unfold pending_push_of_config in Hpv_in_pending. simpl in *.
              apply list_elem_of_omap in Hpv_in_pending as ([τ_y [v_y resp]] & Hin_list & Hmatch).
              destruct v_y as [| | v_z | |]; try discriminate.
              destruct resp as [vr|]; try discriminate.
              simpl in Hmatch. injection Hmatch as -> ->.
              apply elem_of_map_to_list. exact Hin_list. }
            assert (Hinner_NoDup_fst : NoDup inner_pushes.*1).
            { unfold all_push_lists in Hinner_in_all.
              apply list_elem_of_bind in Hinner_in_all as (sub & Hperm & Hsub_in_pset).
              rewrite permutations_Permutation in Hperm.
              rewrite powermset_submseteq in Hsub_in_pset.
              assert (Hperm_keys : sub.*1 ≡ₚ inner_pushes.*1).
              { apply fmap_Permutation. exact Hperm. }
              rewrite -Hperm_keys.
              assert (Hsub_keys : sub.*1 ⊆+ (pending_push_of_config (s_c, π_c)).*1).
              { apply (fmap_submseteq fst). exact Hsub_in_pset. }
              apply submseteq_sublist_l in Hsub_keys as (l2 & Hsublist & Hperm_l2).
              eapply sublist_NoDup; last exact Hsublist.
              destruct (s_c, π_c) as [s_q π_q] eqn:Hbase_eq.
              unfold pending_push_of_config. simpl.
              assert (Hkeys_sub : (omap (λ '(τ', v), if v is (InjRV v, None) then Some (τ',v) else None)
                                          (map_to_list π_q)).*1 `sublist_of` (map_to_list π_q).*1).
              { induction (map_to_list π_q) as [|[τ' [v' resp']] tl IH'].
                - apply sublist_nil.
                - simpl.
                  destruct v' as [| | v_inner | |];
                    try (simpl; apply sublist_cons; exact IH').
                  destruct resp' as [v_resp |];
                    try (simpl; apply sublist_cons; exact IH').
                  simpl. apply sublist_skip. exact IH'. }
              rewrite Hperm_l2.
              eapply sublist_NoDup; last exact Hkeys_sub.
              apply NoDup_fst_map_to_list. }
            assert (Hdisjoint_keys : ∀ τ_x, τ_x ∈ inner_pushes.*1 → τ_x ∉ pushes.*1).
            { intros τ_x Hτx_inner Hτx_pushes.
              (* τ_x ∈ inner_pushes ⇒ cfg.2[τ_x] = LP'd (closed form via lineraize).
                 τ_x ∈ pushes ⇒ cfg.2[τ_x] = (Push, None). Contradiction. *)
              apply list_elem_of_fmap_1 in Hτx_inner as (pv_i & Heq_i & Hpv_i_in).
              apply list_elem_of_fmap_1 in Hτx_pushes as (pv_p & Heq_p & Hpv_p_in).
              specialize (Hsubset pv_p Hpv_p_in).
              unfold pending_push_of_config in Hsubset.
              apply list_elem_of_omap in Hsubset as ([τ_y [v_y resp]] & Hin_list & Hmatch).
              apply elem_of_map_to_list in Hin_list.
              destruct v_y as [| | v_z | |]; try discriminate.
              destruct resp as [vr|]; try discriminate.
              simpl in Hmatch. destruct pv_p as [τ_pp v_pp]. injection Hmatch as Heq_τ_y Heq_v_y.
              subst τ_y.
              (* From Hin_list: pv_i.1 = τ_x, τ_pp = τ_x, so τ_pp = pv_i.1. *)
              assert (Hτpp_pv1 : τ_pp = pv_i.1).
              { simpl in Heq_p. rewrite -Heq_p. exact Heq_i. }
              rewrite Hτpp_pv1 in Hin_list.
              (* Now Hin_list says (map_imap g_inner π_c) !! pv_i.1 = Some(Push v_pp, None). *)
              rewrite map_lookup_imap in Hin_list.
              rewrite Forall_forall in Hinner_pending.
              assert (Hπc_pvi : π_c !! pv_i.1 = Some (encode_request (Push pv_i.2), None))
                by exact (Hinner_pending pv_i Hpv_i_in).
              rewrite Hπc_pvi in Hin_list. simpl in Hin_list.
              rewrite bool_decide_eq_true_2 in Hin_list; last
                (apply (list_elem_of_fmap_2 fst _ pv_i); exact Hpv_i_in).
              discriminate. }
            (* Step 2: combined push_list. *)
            pose (combined := inner_pushes ++ pushes).
            assert (Hcombined_NoDup : NoDup combined.*1).
            { unfold combined. rewrite fmap_app.
              apply NoDup_app. split_and!.
              - exact Hinner_NoDup_fst.
              - intros τ_x Hτx_in. apply Hdisjoint_keys. exact Hτx_in.
              - exact Hnd. }
            (* Step 3: combined ⊆ pending_push_of_config (s_c, π_c). *)
            assert (Hcombined_subset : combined ⊆ pending_push_of_config (s_c, π_c)).
            { unfold combined. intros pv Hpv_in.
              apply elem_of_app in Hpv_in as [Hi | Hp].
              - rewrite Forall_forall in Hinner_pending.
                specialize (Hinner_pending pv Hi).
                destruct pv as [τ_z v_z]. simpl in Hinner_pending.
                apply pending_push_of_config_lookup. exact Hinner_pending.
              - (* pv ∈ pushes ⊆ pending_push_of_config cfg. *)
                assert (Hpv1_notin : pv.1 ∉ inner_pushes.*1).
                { intros Habs. eapply Hdisjoint_keys; first exact Habs.
                  apply (list_elem_of_fmap_2 fst _ pv); exact Hp. }
                specialize (Hsubset pv Hp).
                unfold pending_push_of_config in Hsubset.
                apply list_elem_of_omap in Hsubset as ([τ_y [v_w resp]] & Hin_list & Hmatch).
                apply elem_of_map_to_list in Hin_list.
                destruct v_w as [| | v_q | |]; try discriminate.
                destruct resp as [vr|]; try discriminate.
                destruct pv as [τ_pq v_pq]. simpl in Hmatch.
                injection Hmatch as Heq_pq1 Heq_pq2. subst.
                simpl in Hin_list. rewrite map_lookup_imap in Hin_list.
                destruct (π_c !! τ_pq) as [[req_z resp_z]|] eqn:Hπc_τy;
                  rewrite Hπc_τy in Hin_list; simpl in Hin_list; try discriminate.
                rewrite bool_decide_eq_false_2 in Hin_list; last exact Hpv1_notin.
                apply pending_push_of_config_lookup. simpl.
                rewrite Hπc_τy. exact Hin_list. }
            (* Step 4: combined is stat-conformant. *)
            assert (Hcombined_stat : ∀ pv, pv ∈ combined → ∃ v i,
                      stat2' !! pv.1 = Some (OpEnqReserved v i) ∨
                      stat2' !! pv.1 = Some (OpEnqStored v i)).
            { unfold combined. intros pv Hpv_in.
              apply elem_of_app in Hpv_in as [Hi | Hp].
              - rewrite forallb_forall in Hinner_conf.
                apply list_elem_of_In in Hi.
                specialize (Hinner_conf pv Hi).
                rewrite Hconf_iff in Hinner_conf.
                exact Hinner_conf.
              - exact (Hstat_pushes pv Hp). }
            (* Step 5: by construction of M_g_LP_τ, lineraize combined (s_c, π_c) ∈ M_g_LP_τ. *)
            assert (Hcombined_in_M_LP : lineraize_pending_push combined (s_c, π_c) ∈ M_g_LP_τ).
            { unfold M_g_LP_τ. apply elem_of_list_to_set.
              apply list_elem_of_In, in_flat_map. exists (s_c, π_c). split.
              - apply list_elem_of_In. unfold cfgs. apply elem_of_elements. exact Hbase_in.
              - apply in_map_iff. exists combined. split; first reflexivity.
                unfold push_lists_filtered.
                apply filter_In. split.
                + unfold all_push_lists.
                  apply list_elem_of_In, list_elem_of_bind.
                  exists combined. split; first apply permutations_refl.
                  apply powermset_submseteq.
                  apply NoDup_submseteq; first (eapply NoDup_fmap_1; exact Hcombined_NoDup).
                  exact Hcombined_subset.
                + apply forallb_forall. intros pv Hpv_in.
                  apply list_elem_of_In in Hpv_in.
                  rewrite Hconf_iff. exact (Hcombined_stat pv Hpv_in). }
            (* Step 6: algebraic identity:
                 lineraize pushes (lineraize inner_pushes (s_c, π_c))
               = lineraize combined (s_c, π_c). *)
            assert (Hcompose_eq : lineraize_pending_push pushes
                                    (lineraize_pending_push inner_pushes (s_c, π_c))
                                  = lineraize_pending_push combined (s_c, π_c)).
            { unfold lineraize_pending_push, combined. simpl.
              f_equal.
              - rewrite -app_assoc. f_equal. rewrite fmap_app. reflexivity.
              - apply map_eq. intros τ_x.
                rewrite map_lookup_imap.
                rewrite map_lookup_imap.
                rewrite map_lookup_imap.
                destruct (π_c !! τ_x) as [x|] eqn:Hpicx; rewrite Hpicx; simpl.
                2: { reflexivity. }
                rewrite fmap_app.
                destruct (decide (τ_x ∈ inner_pushes.*1)) as [Hi_in | Hi_out].
                + (* τ_x in inner: LHS first bool_decide = true. *)
                  rewrite (bool_decide_eq_true_2 _ Hi_in). simpl.
                  rewrite bool_decide_eq_false_2;
                    last (intros Habs; eapply Hdisjoint_keys; first exact Hi_in; exact Habs).
                  rewrite bool_decide_eq_true_2; first reflexivity.
                  apply (proj2 (elem_of_app _ _ _)); left; exact Hi_in.
                + destruct (decide (τ_x ∈ pushes.*1)) as [Hp_in | Hp_out].
                  * (* τ_x ∉ inner, ∈ pushes: LHS first bool_decide = false. *)
                    rewrite (bool_decide_eq_false_2 _ Hi_out). simpl.
                    rewrite bool_decide_eq_true_2; last exact Hp_in.
                    rewrite bool_decide_eq_true_2; first reflexivity.
                    apply (proj2 (elem_of_app _ _ _)); right; exact Hp_in.
                  * (* τ_x ∉ both. *)
                    rewrite (bool_decide_eq_false_2 _ Hi_out). simpl.
                    rewrite bool_decide_eq_false_2; last exact Hp_out.
                    rewrite bool_decide_eq_false_2; first reflexivity.
                    intros Habs; apply elem_of_app in Habs as [|]; contradiction. }
            rewrite Hcompose_eq.
            apply elem_of_union_r. exact Hcombined_in_M_LP.
        + assert (Hstat_pushes_old : ∀ pv, pv ∈ pushes → ∃ v i,
                    stat2 !! pv.1 = Some (OpEnqReserved v i) ∨
                    stat2 !! pv.1 = Some (OpEnqStored v i)).
          { intros pv Hpv_in. destruct (Hstat_pushes pv Hpv_in) as (v' & i' & Hstat').
            exists v', i'. assert (Hne_pv_τ : pv.1 ≠ τ).
            { intros Heq_pv. apply Hτ_notin.
              rewrite -Heq_pv. apply (list_elem_of_fmap_2 fst _ pv); exact Hpv_in. }
            destruct Hstat' as [Hs | Hs].
            - left. unfold stat2' in Hs. rewrite lookup_insert_ne in Hs;
                last (intros ?; apply Hne_pv_τ; congruence). exact Hs.
            - right. unfold stat2' in Hs. rewrite lookup_insert_ne in Hs;
                last (intros ?; apply Hne_pv_τ; congruence). exact Hs. }
          destruct Hin_destruct as [Hin_g | (s_c & π_c & inner_pushes & Hbase_in & Hinner_in_all & Hinner_conf & ->)].
          * (* cfg ∈ M_g2: direct Hcl_push2. *)
            pose proof (Hcl_push2 cfg pushes Hin_g Hnd Hsubset Hstat_pushes_old) as Hcl_x.
            apply elem_of_union_l. exact Hcl_x.
          * (* cfg = lineraize inner_pushes (s_c, π_c). Combined approach again, but go to M_g_LP_τ. *)
            (* Build inner_pending and inner_NoDup same as before. *)
            assert (Hinner_pending : Forall (λ pv,
                      π_c !! pv.1 = Some (encode_request (Push pv.2), None)) inner_pushes).
            { unfold all_push_lists in Hinner_in_all.
              apply list_elem_of_bind in Hinner_in_all as (sub & Hperm & Hsub_in_pset).
              rewrite permutations_Permutation in Hperm.
              rewrite powermset_submseteq in Hsub_in_pset.
              assert (Hinner_subset : inner_pushes ⊆ pending_push_of_config (s_c, π_c)).
              { intros pv Hpv_in. rewrite -Hperm in Hpv_in.
                eapply elem_of_submseteq; first exact Hpv_in. exact Hsub_in_pset. }
              apply Forall_forall. intros pv Hpv_in.
              destruct pv as [τ_x v_x].
              assert (Hpv_in_pending : (τ_x, v_x) ∈ pending_push_of_config (s_c, π_c))
                by (apply Hinner_subset; exact Hpv_in).
              unfold pending_push_of_config in Hpv_in_pending. simpl in *.
              apply list_elem_of_omap in Hpv_in_pending as ([τ_y [v_y resp]] & Hin_list & Hmatch).
              destruct v_y as [| | v_z | |]; try discriminate.
              destruct resp as [vr|]; try discriminate.
              simpl in Hmatch. injection Hmatch as -> ->.
              apply elem_of_map_to_list. exact Hin_list. }
            assert (Hinner_NoDup_fst : NoDup inner_pushes.*1).
            { unfold all_push_lists in Hinner_in_all.
              apply list_elem_of_bind in Hinner_in_all as (sub & Hperm & Hsub_in_pset).
              rewrite permutations_Permutation in Hperm.
              rewrite powermset_submseteq in Hsub_in_pset.
              assert (Hperm_keys : sub.*1 ≡ₚ inner_pushes.*1).
              { apply fmap_Permutation. exact Hperm. }
              rewrite -Hperm_keys.
              assert (Hsub_keys : sub.*1 ⊆+ (pending_push_of_config (s_c, π_c)).*1).
              { apply (fmap_submseteq fst). exact Hsub_in_pset. }
              apply submseteq_sublist_l in Hsub_keys as (l2 & Hsublist & Hperm_l2).
              eapply sublist_NoDup; last exact Hsublist.
              unfold pending_push_of_config. simpl.
              assert (Hkeys_sub : (omap (λ '(τ', v), if v is (InjRV v, None) then Some (τ',v) else None)
                                          (map_to_list π_c)).*1 `sublist_of` (map_to_list π_c).*1).
              { induction (map_to_list π_c) as [|[τ' [v' resp']] tl IH'].
                - apply sublist_nil.
                - simpl.
                  destruct v' as [| | v_inner | |];
                    try (simpl; apply sublist_cons; exact IH').
                  destruct resp' as [v_resp |];
                    try (simpl; apply sublist_cons; exact IH').
                  simpl. apply sublist_skip. exact IH'. }
              rewrite Hperm_l2.
              eapply sublist_NoDup; last exact Hkeys_sub.
              apply NoDup_fst_map_to_list. }
            assert (Hdisjoint_keys : ∀ τ_x, τ_x ∈ inner_pushes.*1 → τ_x ∉ pushes.*1).
            { intros τ_x Hτx_inner Hτx_pushes.
              apply list_elem_of_fmap_1 in Hτx_inner as (pv_i & Heq_i & Hpv_i_in).
              apply list_elem_of_fmap_1 in Hτx_pushes as (pv_p & Heq_p & Hpv_p_in).
              specialize (Hsubset pv_p Hpv_p_in).
              unfold pending_push_of_config in Hsubset.
              apply list_elem_of_omap in Hsubset as ([τ_y [v_y resp]] & Hin_list & Hmatch).
              apply elem_of_map_to_list in Hin_list.
              destruct v_y as [| | v_z | |]; try discriminate.
              destruct resp as [vr|]; try discriminate.
              simpl in Hmatch. destruct pv_p as [τ_pp v_pp]. injection Hmatch as Heq_τ_y Heq_v_y.
              subst τ_y.
              assert (Hτpp_pv1 : τ_pp = pv_i.1).
              { simpl in Heq_p. rewrite -Heq_p. exact Heq_i. }
              rewrite Hτpp_pv1 in Hin_list.
              rewrite map_lookup_imap in Hin_list.
              rewrite Forall_forall in Hinner_pending.
              assert (Hπc_pvi : π_c !! pv_i.1 = Some (encode_request (Push pv_i.2), None))
                by exact (Hinner_pending pv_i Hpv_i_in).
              rewrite Hπc_pvi in Hin_list. simpl in Hin_list.
              rewrite bool_decide_eq_true_2 in Hin_list; last
                (apply (list_elem_of_fmap_2 fst _ pv_i); exact Hpv_i_in).
              injection Hin_list as _ Hbad. discriminate. }
            pose (combined := inner_pushes ++ pushes).
            assert (Hcombined_NoDup : NoDup combined.*1).
            { unfold combined. rewrite fmap_app.
              apply NoDup_app. split_and!.
              - exact Hinner_NoDup_fst.
              - intros τ_x Hτx_in. apply Hdisjoint_keys. exact Hτx_in.
              - exact Hnd. }
            assert (Hcombined_subset : combined ⊆ pending_push_of_config (s_c, π_c)).
            { unfold combined. intros pv Hpv_in.
              apply elem_of_app in Hpv_in as [Hi | Hp].
              - rewrite Forall_forall in Hinner_pending.
                specialize (Hinner_pending pv Hi).
                destruct pv as [τ_z v_z]. simpl in Hinner_pending.
                apply pending_push_of_config_lookup. exact Hinner_pending.
              - assert (Hpv1_notin : pv.1 ∉ inner_pushes.*1).
                { intros Habs. eapply Hdisjoint_keys; first exact Habs.
                  apply (list_elem_of_fmap_2 fst _ pv); exact Hp. }
                specialize (Hsubset pv Hp).
                unfold pending_push_of_config in Hsubset.
                apply list_elem_of_omap in Hsubset as ([τ_y [v_w resp]] & Hin_list & Hmatch).
                apply elem_of_map_to_list in Hin_list.
                destruct v_w as [| | v_q | |]; try discriminate.
                destruct resp as [vr|]; try discriminate.
                destruct pv as [τ_pq v_pq]. simpl in Hmatch.
                injection Hmatch as Heq_pq1 Heq_pq2. subst.
                simpl in Hin_list. rewrite map_lookup_imap in Hin_list.
                destruct (π_c !! τ_pq) as [[req_z resp_z]|] eqn:Hπc_τy;
                  rewrite Hπc_τy in Hin_list; simpl in Hin_list; try discriminate.
                rewrite bool_decide_eq_false_2 in Hin_list; last exact Hpv1_notin.
                apply pending_push_of_config_lookup. simpl.
                rewrite Hπc_τy. exact Hin_list. }
            assert (Hcombined_stat : ∀ pv, pv ∈ combined → ∃ v i,
                      stat2' !! pv.1 = Some (OpEnqReserved v i) ∨
                      stat2' !! pv.1 = Some (OpEnqStored v i)).
            { unfold combined. intros pv Hpv_in.
              apply elem_of_app in Hpv_in as [Hi | Hp].
              - rewrite forallb_forall in Hinner_conf.
                apply list_elem_of_In in Hi.
                specialize (Hinner_conf pv Hi).
                rewrite Hconf_iff in Hinner_conf.
                exact Hinner_conf.
              - exact (Hstat_pushes pv Hp). }
            assert (Hcombined_in_M_LP : lineraize_pending_push combined (s_c, π_c) ∈ M_g_LP_τ).
            { unfold M_g_LP_τ. apply elem_of_list_to_set.
              apply list_elem_of_In, in_flat_map. exists (s_c, π_c). split.
              - apply list_elem_of_In. unfold cfgs. apply elem_of_elements. exact Hbase_in.
              - apply in_map_iff. exists combined. split; first reflexivity.
                unfold push_lists_filtered.
                apply filter_In. split.
                + unfold all_push_lists.
                  apply list_elem_of_In, list_elem_of_bind.
                  exists combined. split; first apply permutations_refl.
                  apply powermset_submseteq.
                  apply NoDup_submseteq; first (eapply NoDup_fmap_1; exact Hcombined_NoDup).
                  exact Hcombined_subset.
                + apply forallb_forall. intros pv Hpv_in.
                  apply list_elem_of_In in Hpv_in.
                  rewrite Hconf_iff. exact (Hcombined_stat pv Hpv_in). }
            assert (Hcompose_eq : lineraize_pending_push pushes
                                    (lineraize_pending_push inner_pushes (s_c, π_c))
                                  = lineraize_pending_push combined (s_c, π_c)).
            { unfold lineraize_pending_push, combined. simpl.
              f_equal.
              - rewrite -app_assoc. f_equal. rewrite fmap_app. reflexivity.
              - apply map_eq. intros τ_x.
                rewrite map_lookup_imap.
                rewrite map_lookup_imap.
                rewrite map_lookup_imap.
                destruct (π_c !! τ_x) as [x|] eqn:Hpicx; rewrite Hpicx; simpl.
                2: { reflexivity. }
                rewrite fmap_app.
                destruct (decide (τ_x ∈ inner_pushes.*1)) as [Hi_in | Hi_out].
                + (* τ_x in inner: LHS first bool_decide = true. *)
                  rewrite (bool_decide_eq_true_2 _ Hi_in). simpl.
                  rewrite bool_decide_eq_false_2;
                    last (intros Habs; eapply Hdisjoint_keys; first exact Hi_in; exact Habs).
                  rewrite bool_decide_eq_true_2; first reflexivity.
                  apply (proj2 (elem_of_app _ _ _)); left; exact Hi_in.
                + destruct (decide (τ_x ∈ pushes.*1)) as [Hp_in | Hp_out].
                  * (* τ_x ∉ inner, ∈ pushes: LHS first bool_decide = false. *)
                    rewrite (bool_decide_eq_false_2 _ Hi_out). simpl.
                    rewrite bool_decide_eq_true_2; last exact Hp_in.
                    rewrite bool_decide_eq_true_2; first reflexivity.
                    apply (proj2 (elem_of_app _ _ _)); right; exact Hp_in.
                  * (* τ_x ∉ both. *)
                    rewrite (bool_decide_eq_false_2 _ Hi_out). simpl.
                    rewrite bool_decide_eq_false_2; last exact Hp_out.
                    rewrite bool_decide_eq_false_2; first reflexivity.
                    intros Habs; apply elem_of_app in Habs as [|]; contradiction. }
            rewrite Hcompose_eq.
            apply elem_of_union_r. exact Hcombined_in_M_LP.
      - intros τ' Hstat_None.
        destruct (decide (τ' = τ)) as [-> | Hne_τ'].
        + rewrite lookup_insert_eq in Hstat_None. discriminate.
        + rewrite lookup_insert_ne in Hstat_None;
            last (intros ?; apply Hne_τ'; congruence).
          apply (Hscan_dom2 τ' Hstat_None).
      - (* scan_map_l_bounded: scan_map unchanged; back_val grew from
           back_val2 to back_val2 + 1, only widens bound. *)
        intros τ_p l j Hscan_τ_p. specialize (Hscan_lb2 τ_p l j Hscan_τ_p). lia. }
    wp_pures.

    (* ──────────────────────────────────────────────────────────────────
       Phase 3 — conditional check on bounds.
       ──────────────────────────────────────────────────────────────── *)
    case_bool_decide as Hcond; wp_pures; last first.
    { (* Out of bounds: diverge. *)
      wp_apply wp_diverge. }
    (* In bounds: back_val2 < sz. Store SOMEV v_push at ar[back_val2].
       This is the linearization point for this push. *)
    wp_bind (_ <- _)%E.
    iInv "Hinv" as (items3 back_val3 ts3 M_g3 stat3 slots3 scan_map3)
      "(>Hback & >Har & >Hts & >%Hlen3 & >%Hbpos3 & >HγM & >Hstat & >Hslots & >Hscan & #Hslots_persist3 &
         >%Hmcfg_steps3 & >%Hne3 & >%Hpw3 & >%Hsc3 & >%Hsc_slots3 & >%Hwell3 & >%Htrst3 & >%Hlinw_seq3 & >%Hbnd3 & >%Hssi3 & >%Hcl_push3 & >%Hscan_dom3 & >%Hscan_lb3)".
    (* The store needs back_val2 < length items3 and back_val2 ≥ 0. *)
    iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ3.
    pose proof (Hsc3 τ) as Hsc_τ3. rewrite Hstat_τ3 in Hsc_τ3.
    destruct Hsc_τ3 as [Hsc_τ3_all Hsc_τ3_ex].
    assert (Hbk_lt_items : (Z.to_nat back_val2 < length items3)%nat).
    { rewrite Hlen3. lia. }
    apply lookup_lt_is_Some in Hbk_lt_items as [a_old Hbk_eq].
    replace back_val2 with (Z.of_nat (Z.to_nat back_val2)) by lia.
    wp_apply (wp_store_offset _ _ _ (Z.to_nat back_val2) _ (SOMEV v_push) with "Har") as "Har";
      first by eexists; exact Hbk_eq.
    (* TLA+ E2 alignment: Phase 3 Store leaves M unchanged. M_g3_new := M_g3.
       The disjunctive OpEnqReserved already has a LP'd-τ witness in M_g3,
       which becomes the OpEnqStored LP'd-τ witness. *)
    pose (M_g3_new := M_g3 : gset single_config_q).
    iMod (ghost_var_update M_g3_new with "HγM") as "HγM".
    iMod (ghost_map_update (OpEnqStored v_push (Z.to_nat back_val2))
            with "Hstat Hstat_τ") as "[Hstat Hstat_τ]".
    (* Update slots: insert (back_val2, v_push). *)
    assert (Hslots_fresh : slots3 !! Z.to_nat back_val2 = None).
    { (* By slots_stat_iff: if slot back_val2 had value v_w, ∃ τ_w with
         stat3[τ_w] = Stored or Done v_w back_val2. By FAA-uniqueness with our
         τ at OpEnqReserved v_push back_val2, τ_w = τ. But τ has Reserved,
         τ_w has Stored/Done — contradiction. *)
      destruct (slots3 !! Z.to_nat back_val2) as [v_w|] eqn:Hlk; last reflexivity.
      exfalso. destruct Hssi3 as (_ & Hssi_dir2 & Hssi_uniq & _).
      destruct (Hssi_dir2 _ _ Hlk) as (τ_w & Hstat_w).
      assert (Hτ_eq : τ_w = τ).
      { eapply (Hssi_uniq τ_w τ v_w v_push).
        - destruct Hstat_w as [Hstat_w | Hstat_w].
          + right. left. exact Hstat_w.
          + right. right. exact Hstat_w.
        - left. exact Hstat_τ3. }
      subst τ_w. destruct Hstat_w as [Hstat_w | Hstat_w];
        rewrite Hstat_τ3 in Hstat_w; discriminate. }
    iMod (ghost_map_insert (Z.to_nat back_val2) v_push with "Hslots")
      as "[Hslots Hslot_τ]"; first exact Hslots_fresh.
    iMod (ghost_map_elem_persist with "Hslot_τ") as "#Hslot_persist_new".
    iAssert ([∗ map] i ↦ v ∈ <[Z.to_nat back_val2 := v_push]> slots3,
                i ↪[γ_slots]□ v)%I as "#Hslots_persist3_new".
    { iApply big_sepM_insert; first exact Hslots_fresh.
      iFrame "Hslot_persist_new Hslots_persist3". }
    iModIntro.
    iSplitR "HΦ Hstat_τ".
    { iNext.
      iExists (<[Z.to_nat back_val2 := SOMEV v_push]> items3),
              back_val3, ts3, M_g3_new,
              (<[τ:=OpEnqStored v_push (Z.to_nat back_val2)]> stat3),
              (<[Z.to_nat back_val2 := v_push]> slots3), scan_map3.
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist3_new".
      iPureIntro. split_and!.
      - rewrite length_insert. exact Hlen3.
      - exact Hbpos3.
      - (* TLA+ E2: Store leaves M unchanged. mcfg_steps appends []. *)
        unfold M_g3_new. exact Hmcfg_steps3.
      - (* non-empty: M_g3_new = M_g3 ≠ ∅ from Hne3. *)
        exact Hne3.
      - exact Hpw3.
      - (* stat_consistent preservation: M_g3_new = M_g3.
           For τ' = τ (now OpEnqStored, disjunctive):
             - ∀-disj: Hsc_τ3_all (OpEnqReserved disj) gives same form.
             - ∃-LP'd: Hsc_τ3_ex (OpEnqReserved disj) gives the witness.
           For τ' ≠ τ: M_g3 unchanged, lift directly from Hsc3 τ'. *)
        intros τ'.
        destruct (decide (τ' = τ)) as [-> | Hne_τ].
        + rewrite lookup_insert_eq.
          split.
          { intros s' π' Hin_new. unfold M_g3_new in Hin_new.
            exact (Hsc_τ3_all s' π' Hin_new). }
          destruct Hsc_τ3_ex as (s_v & π_v & Hin_v & Hπ_v).
          exists s_v, π_v. split; [unfold M_g3_new; exact Hin_v | exact Hπ_v].
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
          unfold M_g3_new.
          exact (Hsc3 τ').
      - (* slots_consistent preservation *)
        destruct Hsc_slots3 as [Hsc_dir1 Hsc_dir2].
        split.
        + intros i v Hlk.
          destruct (decide (i = Z.to_nat back_val2)) as [-> | Hne_i].
          * rewrite lookup_insert_eq in Hlk. injection Hlk as ->.
            rewrite length_insert. split; first by rewrite Hlen3; lia.
            left. rewrite list_lookup_insert_eq; first reflexivity.
            rewrite Hlen3. lia.
          * rewrite lookup_insert_ne in Hlk; last done.
            specialize (Hsc_dir1 i v Hlk) as [Hlt Hcase].
            rewrite length_insert.
            split; first exact Hlt.
            rewrite list_lookup_insert_ne; last done. exact Hcase.
        + intros i v Hlk.
          destruct (decide (i = Z.to_nat back_val2)) as [-> | Hne_i].
          * rewrite list_lookup_insert_eq in Hlk; last by rewrite Hlen3; lia.
            injection Hlk as ->. rewrite lookup_insert_eq. reflexivity.
          * rewrite list_lookup_insert_ne in Hlk; last done.
            rewrite lookup_insert_ne; last done.
            apply (Hsc_dir2 i v Hlk).
      - (* items_well_shaped preservation: insert SOMEV v_push at back_val2. *)
        apply Forall_insert; first exact Hwell3.
        right. exists v_push. split; first reflexivity. exact Hunb.
      - (* trace_stat_consistent: OpEnqStored has same trace footprint as
           OpEnqReserved/OpEnqPending — ts unchanged. *)
        intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
        + rewrite lookup_insert_eq.
          pose proof (Htrst3 τ) as Htrst_τ. rewrite Hstat_τ3 in Htrst_τ.
          exact Htrst_τ.
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
          exact (Htrst3 τ').
      - intros A seq HgoodA HnodupSeq Hsetof HJInvSeq.
        (* Step 1: Derive OLD GoodEnqSet from NEW. *)
        assert (HgoodA_old : GoodEnqSet A items3 stat3).
        { destruct HgoodA as [Hg1 Hg2]. split.
          - intros k v Hitem_k.
            apply Hg1 with v.
            destruct (decide (k = Z.to_nat back_val2)) as [-> | Hne_k].
            + rewrite list_lookup_insert_eq;
                last (rewrite Hlen3; lia).
              (* items_pre[back_val2] = NONEV; but we're using Hitem_k = items_pre[k] = SOMEV v.
                 Contradicts. *)
              exfalso. rewrite Hitem_k in Hbk_eq.
              (* Hbk_eq : items3 !! Z.to_nat back_val2 = Some a_old.
                 We're conflating items3 (pre) and items_new (post). Items3 !! back_val2 is
                 a_old (unknown). For OLD GoodEnqSet, k = back_val2 with items3[back_val2] = SOMEV v?
                 By slots_consistent, slots3[back_val2] = v. By slots_stat_iff, ∃ τ_w with
                 Stored/Done. But Hstat_τ3 = stat3[τ] = Reserved v_push back_val2. By FAA-uniqueness
                 τ_w = τ, but Reserved ≠ Stored/Done — contradiction. *)
              destruct Hssi3 as (Hssi_a3 & Hssi_b3 & Hssi_c3 & _).
              destruct Hsc_slots3 as [_ Hsc_dir2].
              pose proof (Hsc_dir2 (Z.to_nat back_val2) v Hitem_k) as Hslot_bk.
              destruct (Hssi_b3 _ _ Hslot_bk) as (τ_w & Hown_w).
              assert (Hτw_eq : τ_w = τ).
              { apply (Hssi_c3 τ_w τ v v_push (Z.to_nat back_val2)).
                - destruct Hown_w as [Hs | Hs].
                  + right. left. exact Hs.
                  + right. right. exact Hs.
                - left. exact Hstat_τ3. }
              subst τ_w. destruct Hown_w as [Hs | Hs];
                rewrite Hstat_τ3 in Hs; discriminate.
            + rewrite list_lookup_insert_ne; done.
          - intros k Hin_A. destruct (Hg2 k Hin_A) as [(v & Hi) | (τ_e & v_e & Hres)].
            + destruct (decide (k = Z.to_nat back_val2)) as [-> | Hne_k].
              * (* k = back_val2: in OLD, τ is at OpEnqReserved v_push back_val2. Use that. *)
                right. exists τ, v_push. exact Hstat_τ3.
              * left. exists v. rewrite list_lookup_insert_ne in Hi; done.
            + right. (* OpEnqReserved τ_e in stat_new (with insert τ → Stored). *)
              destruct (decide (τ_e = τ)) as [-> | Hne_τe].
              * rewrite lookup_insert_eq in Hres. discriminate.
              * exists τ_e, v_e. rewrite lookup_insert_ne in Hres;
                  last (intros ?; apply Hne_τe; congruence). exact Hres. }
        (* Step 2: Derive OLD JInvSeq from NEW. *)
        assert (HJInvSeq_old : JInvSeq seq slots3 stat3 scan_map3).
        { intros n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km_old.
          (* slots3 ⊆ slots_new (slots_new = insert back_val2 ↦ v_push slots3).
             is_Some (slots3[k_m]) → is_Some (slots_new[k_m]). *)
          assert (Hsome_km_new : is_Some (<[Z.to_nat back_val2:=v_push]>slots3 !! k_m)).
          { destruct (decide (k_m = Z.to_nat back_val2)) as [-> | Hne_km].
            - rewrite lookup_insert_eq. eexists. reflexivity.
            - rewrite lookup_insert_ne; done. }
          destruct (HJInvSeq n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km_new)
            as (τ_d & l & j_d & Hstat_d & Hscan_d & Hkl & Hkj).
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          - rewrite lookup_insert_eq in Hstat_d. discriminate.
          - exists τ_d, l, j_d. split_and!; try assumption.
            rewrite lookup_insert_ne in Hstat_d;
              last (intros ?; apply Hne_τd; congruence).
            exact Hstat_d. }
        (* Step 3: Apply Hlinw_seq3 to (A, seq) with OLD invariants. *)
        destruct (Hlinw_seq3 A seq HgoodA_old HnodupSeq Hsetof HJInvSeq_old)
          as (s & π & Hin_g & Hlen_s & Hsmatch & Hsmatch_case & Henq_d & Hlin_d
              & Hdone_d & Hpending_d & Hstored_d & Hres_d).
        (* Step 4: Build witness (s, π_new_lifted) where π_new_lifted just promotes
           τ's status appropriately. Since we want the same (A, seq), we lift the
           witness. Actually we directly use (s, π) ∈ M_g3 ⊆ M_g3_new. *)
        exists s, π. split_and!.
        + unfold M_g3_new. exact Hin_g.
        + exact Hlen_s.
        + (* slots-based match: for k = back_val2: slots_new[back_val2] = Some v_push.
             OLD slots3[back_val2] = None (Hslots_fresh), so OLD Hsmatch doesn't apply.
             We need to manually derive s[n] = v_push at the position where seq[n] = back_val2. *)
          intros n k Hseq_n v Hslot_k.
          destruct (decide (k = Z.to_nat back_val2)) as [-> | Hne_k].
          * rewrite lookup_insert_eq in Hslot_k. injection Hslot_k as <-.
            (* Need s[n] = v_push. Use OLD items+stat match: seq[n] = back_val2;
               items3[back_val2] = NONEV so disjunct 1 fails; τ at OpEnqReserved v_push
               back_val2, disjunct 2 gives s[n] = v_push. *)
            destruct (Hsmatch_case n (Z.to_nat back_val2) Hseq_n) as
              [(v0 & Hitem & _) | (τ_e & v_e & Hres & Hs)].
            -- (* items3[back_val2] = NONEV (since slots3[back_val2] = None means
                  items3[back_val2] is NONEV by slots_consistent direction 2 NOT,
                  but rather by direction 1's contrapositive: items3[back_val2] = SOMEV v0
                  → slots3[back_val2] = Some v0 ≠ None. So items3[back_val2] ≠ SOMEV.
                  Combined with items_well_shaped, items3[back_val2] = NONEV. *)
               exfalso.
               destruct Hsc_slots3 as [_ Hsc_dir2].
               pose proof (Hsc_dir2 _ _ Hitem) as Hslot_bk.
               rewrite Hslots_fresh in Hslot_bk. discriminate.
            -- (* τ_e at OpEnqReserved v_e back_val2. By FAA-uniqueness, τ_e = τ. *)
               destruct Hssi3 as (_ & _ & Hssi_c3 & _).
               assert (Hτ_eq : τ_e = τ).
               { apply (Hssi_c3 τ_e τ v_e v_push (Z.to_nat back_val2)).
                 - left. exact Hres.
                 - left. exact Hstat_τ3. }
               subst τ_e.
               assert (Heq_v : v_push = v_e).
               { rewrite Hstat_τ3 in Hres. by injection Hres. }
               rewrite Heq_v. exact Hs.
          * rewrite lookup_insert_ne in Hslot_k; last done.
            exact (Hsmatch n k Hseq_n v Hslot_k).
        + (* TLA+ items+stat case match for NEW. *)
          intros n k Hseq_n.
          destruct (Hsmatch_case n k Hseq_n) as
            [(v0 & Hitem & Hs) | (τ_e & v_e & Hres & Hs)].
          * (* items3[k] = SOMEV v0 → items_new[k] = SOMEV v0 (since k ≠ back_val2). *)
            left. exists v0.
            assert (Hk_ne : k ≠ Z.to_nat back_val2).
            { intros ->.
              destruct Hsc_slots3 as [_ Hsc_dir2].
              pose proof (Hsc_dir2 _ _ Hitem) as Hslot_bk.
              rewrite Hslots_fresh in Hslot_bk. discriminate. }
            split; last exact Hs.
            rewrite list_lookup_insert_ne; done.
          * (* OpEnqReserved at k. In stat_new = insert τ→Stored, τ_e ≠ τ implies
               same. If τ_e = τ, then k = back_val2 and v_e = v_push; for NEW:
               items_new[back_val2] = SOMEV v_push, use the SOMEV branch. *)
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            -- left. (* τ_e = τ: stat3[τ] = Reserved v_push back_val2 = Reserved v_e k.
                       So k = back_val2 and v_e = v_push. *)
               rewrite Hstat_τ3 in Hres.
               assert (Hv_e_eq : v_push = v_e) by by injection Hres.
               assert (Hk_eq : Z.to_nat back_val2 = k).
               { injection Hres. intros Hbi _. exact Hbi. }
               exists v_e. rewrite -Hk_eq list_lookup_insert_eq;
                 last (rewrite Hlen3; lia).
               split.
               ++ rewrite Hv_e_eq. reflexivity.
               ++ exact Hs.
            -- right. exists τ_e, v_e. rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τe; congruence).
               split; [exact Hres | exact Hs].
        + (* OpEnqDone case. *)
          intros τ_d v_d i_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            exact (Henq_d τ_d v_d i_d Hstat_d_new).
        + intros τ_d v_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            exact (Hlin_d τ_d v_d Hstat_d_new).
        + intros τ_d v_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            exact (Hdone_d τ_d v_d Hstat_d_new).
        + intros τ_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            exact (Hpending_d τ_d Hstat_d_new).
        + (* OpEnqStored case. NEW Hstored is UNCONDITIONAL.
             For τ_e = τ: stat_new[τ] = Stored v_push back_val2.
             items_new[back_val2] = SOMEV v_push (just stored), so NEW GoodEnqSet
             forces back_val2 ∈ A. Then OLD Hres_d's i_e ∈ A branch gives π[τ] LP'd.
             For τ_e ≠ τ: OLD STRENGTHENED Hstored_d gives π[τ_e] LP'd directly. *)
          intros τ_e v_e i_e Hstat_e_new.
          destruct (decide (τ_e = τ)) as [-> | Hne_τe].
          * rewrite lookup_insert_eq in Hstat_e_new.
            assert (Hve_eq : v_push = v_e).
            { by injection Hstat_e_new. }
            rewrite -Hve_eq.
            (* Derive back_val2 ∈ A from NEW GoodEnqSet on items_new[back_val2] = SOMEV v_push. *)
            assert (Hbv_in_A : Z.to_nat back_val2 ∈ A).
            { destruct HgoodA as [HgoodA_a _].
              apply (HgoodA_a (Z.to_nat back_val2) v_push).
              rewrite list_lookup_insert_eq; last (rewrite Hlen3; lia).
              reflexivity. }
            destruct (Hres_d τ v_push (Z.to_nat back_val2) Hstat_τ3) as [HLP _].
            exact (HLP Hbv_in_A).
          * rewrite lookup_insert_ne in Hstat_e_new;
              last (intros ?; apply Hne_τe; congruence).
            exact (Hstored_d τ_e v_e i_e Hstat_e_new).
        + (* OpEnqReserved case. For τ_e = τ: stat_new[τ] = Stored, not Reserved —
             so τ_e ≠ τ. Lift via Hres_d on stat3[τ_e]. *)
          intros τ_e v_e i_e Hres_e_new.
          destruct (decide (τ_e = τ)) as [-> | Hne_τe].
          * rewrite lookup_insert_eq in Hres_e_new. discriminate.
          * rewrite lookup_insert_ne in Hres_e_new;
              last (intros ?; apply Hne_τe; congruence).
            destruct (Hres_d τ_e v_e i_e Hres_e_new) as [HLP Hdisj].
            split; [exact HLP | exact Hdisj].
      - intros i v Hslot.
        destruct (decide (i = Z.to_nat back_val2)) as [-> | Hne_i].
        + destruct Hssi3 as (_ & _ & _ & Hssi_d3).
          specialize (Hssi_d3 τ v_push (Z.to_nat back_val2) (or_introl Hstat_τ3)).
          lia.
        + rewrite lookup_insert_ne in Hslot; last done.
          exact (Hbnd3 i v Hslot).
      - (* slots_stat_iff after Store LP: stat τ → OpEnqStored,
           slots inserts (back_val2, v_push). Preserve via old uniq + back-bound. *)
        destruct Hssi3 as (Hssi_a3 & Hssi_b3 & Hssi_c3 & Hssi_d3).
        unfold stat_owns, stat_faad.
        split_and!.
        + (* (a) stored/done → slot *)
          intros τ' v' i' Howns.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          * destruct Howns as [Howns | Howns];
              rewrite lookup_insert_eq in Howns; last discriminate.
            injection Howns as -> ->.
            rewrite lookup_insert_eq. reflexivity.
          * destruct (decide (i' = Z.to_nat back_val2)) as [-> | Hne_i'].
            -- (* contradiction via uniq: τ' has Stored/Done at back_val2,
                  τ has Reserved at back_val2 → τ' = τ. *)
               exfalso.
               assert (Heq_τ : τ' = τ).
               { eapply (Hssi_c3 τ' τ v' v_push (Z.to_nat back_val2)).
                 - destruct Howns as [Howns | Howns];
                     rewrite lookup_insert_ne in Howns;
                     try (intros ?; apply Hne_τ'; congruence).
                   + right. left. exact Howns.
                   + right. right. exact Howns.
                 - left. exact Hstat_τ3. }
               apply Hne_τ'. exact Heq_τ.
            -- rewrite lookup_insert_ne; last done.
               apply (Hssi_a3 τ' v' i').
               destruct Howns as [Howns | Howns];
                 rewrite lookup_insert_ne in Howns;
                 try (intros ?; apply Hne_τ'; congruence);
                 [left | right]; exact Howns.
        + (* (b) slot → stored/done *)
          intros i' v' Hslot'.
          destruct (decide (i' = Z.to_nat back_val2)) as [-> | Hne_i'].
          * rewrite lookup_insert_eq in Hslot'. injection Hslot' as ->.
            exists τ. left. apply lookup_insert_eq.
          * rewrite lookup_insert_ne in Hslot'; last done.
            destruct (Hssi_b3 _ _ Hslot') as (τ_w & Hstat_w).
            exists τ_w. destruct (decide (τ_w = τ)) as [-> | Hne_τw].
            -- exfalso. destruct Hstat_w as [Hstat_w | Hstat_w];
                 rewrite Hstat_τ3 in Hstat_w; discriminate.
            -- destruct Hstat_w as [Hstat_w | Hstat_w];
                 [left | right];
                 rewrite lookup_insert_ne;
                 try (intros ?; apply Hne_τw; congruence);
                 exact Hstat_w.
        + (* (c) uniq *)
          intros τ_1 τ_2 v_1 v_2 i' Hτ1 Hτ2.
          destruct (decide (τ_1 = τ)) as [-> | Hne_τ1];
            destruct (decide (τ_2 = τ)) as [-> | Hne_τ2].
          * reflexivity.
          * destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
              rewrite lookup_insert_eq in Hτ1; try discriminate.
            injection Hτ1 as Heqv Heqi. subst i'.
            (* τ_2 ≠ τ: old uniq gives τ = τ_2, contradicting Hne_τ2. *)
            assert (Hτ2_old : stat_faad stat3 τ_2 v_2 (Z.to_nat back_val2)).
            { destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                rewrite lookup_insert_ne in Hτ2;
                try (intros ?; apply Hne_τ2; congruence).
              - left. exact Hτ2.
              - right. left. exact Hτ2.
              - right. right. exact Hτ2. }
            exfalso. apply Hne_τ2.
            symmetry. eapply (Hssi_c3 τ τ_2 v_push v_2 (Z.to_nat back_val2)).
            -- left. exact Hstat_τ3.
            -- exact Hτ2_old.
          * destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
              rewrite lookup_insert_eq in Hτ2; try discriminate.
            injection Hτ2 as Heqv Heqi. subst i'.
            assert (Hτ1_old : stat_faad stat3 τ_1 v_1 (Z.to_nat back_val2)).
            { destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                rewrite lookup_insert_ne in Hτ1;
                try (intros ?; apply Hne_τ1; congruence).
              - left. exact Hτ1.
              - right. left. exact Hτ1.
              - right. right. exact Hτ1. }
            exfalso. apply Hne_τ1.
            eapply (Hssi_c3 τ_1 τ v_1 v_push (Z.to_nat back_val2)).
            -- exact Hτ1_old.
            -- left. exact Hstat_τ3.
          * assert (Hτ1_old : stat_faad stat3 τ_1 v_1 i').
            { destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                rewrite lookup_insert_ne in Hτ1;
                try (intros ?; apply Hne_τ1; congruence).
              - left. exact Hτ1.
              - right. left. exact Hτ1.
              - right. right. exact Hτ1. }
            assert (Hτ2_old : stat_faad stat3 τ_2 v_2 i').
            { destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                rewrite lookup_insert_ne in Hτ2;
                try (intros ?; apply Hne_τ2; congruence).
              - left. exact Hτ2.
              - right. left. exact Hτ2.
              - right. right. exact Hτ2. }
            apply (Hssi_c3 τ_1 τ_2 v_1 v_2 i' Hτ1_old Hτ2_old).
        + (* (d) back-bound: back unchanged at LP. *)
          intros τ' v' i' Hstat'.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          * destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
              rewrite lookup_insert_eq in Hstat'; try discriminate.
            injection Hstat' as Heqv Heqi. subst i'.
            exact (Hssi_d3 τ v_push (Z.to_nat back_val2) (or_introl Hstat_τ3)).
          * assert (Hstat'_old : stat_faad stat3 τ' v' i').
            { destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
                rewrite lookup_insert_ne in Hstat';
                try (intros ?; apply Hne_τ'; congruence).
              - left. exact Hstat'.
              - right. left. exact Hstat'.
              - right. right. exact Hstat'. }
            exact (Hssi_d3 τ' v' i' Hstat'_old).
      - (* closure_push at Phase 3 Store: M_g3_new = M_g3 (TLA+ E2 alignment).
           For cfg ∈ M_g3: lift via Hcl_push3. Stat condition: pushes pv with
           stat_new[pv.1] ∈ {Reserved, Stored} lifts to stat3[pv.1] same set,
           since τ goes Reserved → Stored (both eligible) and other τ' unchanged. *)
        intros cfg pushes Hin Hnd Hsubset Hstat_pushes.
        unfold M_g3_new in Hin.
        assert (Hstat_pushes3 : ∀ pv, pv ∈ pushes → ∃ v i,
                  stat3 !! pv.1 = Some (OpEnqReserved v i) ∨
                  stat3 !! pv.1 = Some (OpEnqStored v i)).
        { intros pv Hpv. destruct (Hstat_pushes pv Hpv) as (v' & i' & Hstat').
          destruct (decide (pv.1 = τ)) as [Heq | Hne_pv_τ].
          - (* pv.1 = τ: stat_new[τ] = Stored v_push back_val2; stat3[τ] = Reserved v_push back_val2. *)
            exists v_push, (Z.to_nat back_val2).
            rewrite Heq. left. exact Hstat_τ3.
          - exists v', i'. destruct Hstat' as [Hs|Hs].
            + left. rewrite lookup_insert_ne in Hs;
                last (intros ?; apply Hne_pv_τ; congruence). exact Hs.
            + right. rewrite lookup_insert_ne in Hs;
                last (intros ?; apply Hne_pv_τ; congruence). exact Hs. }
        unfold M_g3_new.
        exact (Hcl_push3 cfg pushes Hin Hnd Hsubset Hstat_pushes3).
      - intros τ' Hstat_None.
        destruct (decide (τ' = τ)) as [-> | Hne_τ'].
        + rewrite lookup_insert_eq in Hstat_None. discriminate.
        + rewrite lookup_insert_ne in Hstat_None;
            last (intros ?; apply Hne_τ'; congruence).
          apply (Hscan_dom3 τ' Hstat_None).
      - (* scan_map_l_bounded: scan_map and back_val unchanged. *)
        exact Hscan_lb3. }
    wp_pures.

    (* ──────────────────────────────────────────────────────────────────
       Phase 4 — trace_emit Ret #().
       ──────────────────────────────────────────────────────────────── *)
    wp_bind (trace_emit _ _ _).
    awp_apply (trace_emit_spec _ τ (Ret #()) (InjRV #()) I_lang_hwq with "Itrace");
      first reflexivity.
    iInv "Hinv" as (items4 back_val4 ts4 M_g4 stat4 slots4 scan_map4)
      "(>Hback & >Har & >Hts & >%Hlen4 & >%Hbpos4 & >HγM & >Hstat & >Hslots & >Hscan & #Hslots_persist4 &
         >%Hmcfg_steps4 & >%Hne4 & >%Hpw4 & >%Hsc4 & >%Hsc_slots4 & >%Hwell4 & >%Htrst4 & >%Hlinw_seq4 & >%Hbnd4 & >%Hssi4 & >%Hcl_push4 & >%Hscan_dom4 & >%Hscan_lb4)".
    iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ4_pre.
    iApply (fupd_mask_intro); first solve_ndisj. iIntros "Hclose_fupd".
    iFrame "Hts". iSplit.
    { iPureIntro.
      apply phase4_ret_preserves_I_lang with (τ := τ) (v_push := v_push); auto.
      - split.
        + apply set_choose_L in Hne4 as [[s_w π_w] Hw_in].
          assert ((s_w, π_w) ∈ (set_to_propset M_g4 : @meta_config hwq_model)) as Hw_full
              by (apply elem_of_set_to_propset; exact Hw_in).
          exists (set_to_propset M_g4), s_w, π_w. split; auto.
        + exact Hpw4.
      - (* filter ts4 = [(τ, Call (Push v_push))] from trace_stat_consistent. *)
        pose proof (Htrst4 τ) as Htrst_τ. rewrite Hstat_τ4_pre in Htrst_τ.
        exact Htrst_τ.
      - (* ∃ M_full s π with τ linearized in π. Use OpEnqStored's ∃ clause. *)
        pose proof (Hsc4 τ) as Hsc_τ. rewrite Hstat_τ4_pre in Hsc_τ.
        destruct Hsc_τ as [_ (s_v & π_v & Hin_v & Hπ_v)].
        assert ((s_v, π_v) ∈ (set_to_propset M_g4 : @meta_config hwq_model)) as Hin_full
            by (apply elem_of_set_to_propset; exact Hin_v).
        exists (set_to_propset M_g4), s_v, π_v. split; first auto. split; first exact Hin_full.
        exact Hπ_v. }
    iSplit.
    { iIntros "[Hts _]". iMod "Hclose_fupd" as "_". iModIntro.
      iSplitL "Hback Har Hts HγM Hstat Hslots Hscan".
      { iNext. iExists items4, back_val4, ts4, M_g4, stat4, slots4, scan_map4.
        iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist4".
        iPureIntro. split_and!; assumption. }
      iFrame "HΦ Hstat_τ". }
    iIntros "Hts". iMod "Hclose_fupd" as "_".
    iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ4.
    iMod (ghost_map_update (OpEnqDone v_push (Z.to_nat back_val2))
            with "Hstat Hstat_τ")
      as "[Hstat Hstat_τ]".
    (* Chain trick: LP τ in each τ-pending config of M_g4, then Ret filter.
       Each element of M_g4 maps to either itself (if τ already LP'd) or its
       LP'd version (if τ pending). The new M_g4_new survives the Ret filter
       and carries the original's witness properties. *)
    assert (Hsub4_self : set_to_propset M_g4 ⊆ (set_to_propset M_g4 : @meta_config hwq_model))
      by reflexivity.
    destruct (mcfg_steps_chain_lp_push_all (set_to_propset M_g4) M_g4 τ v_push Hsub4_self)
      as (M_full4_chained & Hchain_steps & Hchain_sub & Hchain_witnesses & Hchain_upper).
    pose (M_g4_new := set_map (lp_or_keep_τ_push τ v_push) M_g4
                     : gset single_config_q).
    iMod (ghost_var_update M_g4_new with "HγM") as "HγM".
    (* Leibniz equality assertion via propset_leibniz_equiv. *)
    assert (HM_full4_new_eq :
      (M_full4_chained ∩
        {[ (_, π) | snd <$> (π !! τ) = Some (Some #()) ]}
       : @meta_config hwq_model)
      = (set_to_propset M_g4_new : @meta_config hwq_model)).
    { pose proof (Hsc4 τ) as Hsc_τ. rewrite Hstat_τ4_pre in Hsc_τ.
      destruct Hsc_τ as [Hsc_τ_disj _].
      apply leibniz_equiv. intros [s π]. split.
      - intros [Hin_chained Hin_filter]%elem_of_intersection.
        assert (Hfilter_eq : snd <$> (π !! τ) = Some (Some #()))
          by (apply (elem_of_PropSet (λ x : single_config_q,
                       snd <$> (x.2 !! τ) = Some (Some #())) (s, π)); exact Hin_filter).
        destruct (Hchain_upper (s, π) Hin_chained) as [Hin_g | (x & Hx_g & Hxτ & Heq)].
        + apply elem_of_set_to_propset in Hin_g.
          apply elem_of_set_to_propset. unfold M_g4_new.
          apply elem_of_map. exists (s, π). split; last exact Hin_g.
          unfold lp_or_keep_τ_push. case_decide as Hπτ_pending.
          * exfalso. simpl in Hπτ_pending.
            rewrite Hπτ_pending in Hfilter_eq. simpl in Hfilter_eq. discriminate.
          * reflexivity.
        + apply elem_of_set_to_propset. unfold M_g4_new.
          apply elem_of_map. exists x. split; last exact Hx_g.
          unfold lp_or_keep_τ_push. case_decide as Hxτ_pending.
          * rewrite Heq. reflexivity.
          * exfalso. apply Hxτ_pending. exact Hxτ.
      - intros Hin_new. rewrite elem_of_set_to_propset in Hin_new.
        unfold M_g4_new in Hin_new.
        apply elem_of_map in Hin_new as (x & Heq & Hx_g).
        destruct x as [s_x π_x]. simpl in Heq.
        unfold lp_or_keep_τ_push in Heq. simpl in Heq.
        destruct (decide (π_x !! τ = Some (encode_request (Push v_push), None)))
          as [Hxτ_pending | Hxτ_no].
        + rewrite decide_True in Heq; last exact Hxτ_pending.
          injection Heq as Hs_eq Hπ_eq. subst.
          apply elem_of_intersection. split.
          * apply (Hchain_witnesses (s_x, π_x) Hx_g Hxτ_pending).
          * apply elem_of_PropSet. simpl. rewrite lookup_insert_eq. reflexivity.
        + rewrite decide_False in Heq; last exact Hxτ_no.
          injection Heq as Hs_eq Hπ_eq. subst.
          apply elem_of_intersection. split.
          * apply Hchain_sub. apply elem_of_set_to_propset. exact Hx_g.
          * apply elem_of_PropSet. simpl.
            specialize (Hsc_τ_disj s_x π_x Hx_g) as [Hpend | Hlin].
            -- exfalso. apply Hxτ_no. exact Hpend.
            -- rewrite Hlin. reflexivity. }
    iModIntro.
    iSplitR "HΦ".
    { iNext.
      iExists items4, back_val4, (ts4 ++ [(τ, Ret #())]),
              M_g4_new,
              (<[τ:=OpEnqDone v_push (Z.to_nat back_val2)]> stat4), slots4, scan_map4.
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist4".
      iPureIntro. split_and!.
      - exact Hlen4.
      - exact Hbpos4.
      - (* mcfg_steps: extend by chain LPs then mcfg_step_ret. *)
        rewrite -HM_full4_new_eq.
        eapply mcfg_steps_snoc.
        + replace ts4 with (ts4 ++ []) by by rewrite app_nil_r.
          eapply mcfg_steps_app; first exact Hmcfg_steps4.
          exact Hchain_steps.
        + apply (mcfg_step_ret M_full4_chained τ #()).
      - (* non-empty: set_map of a non-empty set is non-empty. *)
        intros Habs.
        apply set_choose_L in Hne4 as [x Hx_in].
        assert (Hlp_in : lp_or_keep_τ_push τ v_push x ∈ M_g4_new).
        { unfold M_g4_new. apply elem_of_map. exists x. split; done. }
        rewrite Habs in Hlp_in. clear -Hlp_in. set_solver.
      - eapply per_tag_wellformed_snoc_ret; first exact Hpw4.
        (* filter ts4 = [(τ, Call (Push v_push))] from trace_stat_consistent. *)
        pose proof (Htrst4 τ) as Htrst_τ. rewrite Hstat_τ4_pre in Htrst_τ.
        exact Htrst_τ.
      - (* stat_consistent OpEnqStored → OpEnqDone: M_g4_new = set_map LP. *)
        intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
        + rewrite lookup_insert_eq.
          intros s' π' Hin. unfold M_g4_new in Hin.
          apply elem_of_map in Hin as ([s_x π_x] & Heq & Hx_in).
          pose proof (Hsc4 τ) as Hsc_τ_inner. rewrite Hstat_τ4_pre in Hsc_τ_inner.
          destruct Hsc_τ_inner as [Hsc_all _].
          specialize (Hsc_all s_x π_x Hx_in).
          pose proof (lp_or_keep_τ_push_τ_lin τ v_push (s_x, π_x) Hsc_all) as Hlin.
          rewrite -Heq in Hlin. simpl in Hlin. exact Hlin.
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
          pose proof (Hsc4 τ') as Hsc_τ'.
          destruct (stat4 !! τ') as [s_op|].
          * destruct s_op.
            -- intros s' π' Hin; unfold M_g4_new in Hin;
                 apply elem_of_map in Hin as ([s_x π_x] & Heq & Hin_g);
                 pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                              (s_x, π_x) Hne_τ) as Hτ';
                 rewrite -Heq in Hτ'; simpl in Hτ';
                 rewrite Hτ'; by apply (Hsc_τ' s_x π_x Hin_g).
            -- (* OpEnqReserved — conj (∀-disj, ∃-LP'd). *)
               destruct Hsc_τ' as [Hsc_all Hsc_ex].
               split.
               { intros s' π' Hin; unfold M_g4_new in Hin;
                 apply elem_of_map in Hin as ([s_x π_x] & Heq & Hin_g);
                 pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                              (s_x, π_x) Hne_τ) as Hτ';
                 rewrite -Heq in Hτ'; simpl in Hτ';
                 rewrite Hτ'; by apply (Hsc_all s_x π_x Hin_g). }
               (* ∃ witness: use LP'd image of (s_v, π_v) at OLD ∃-LP'd τ'. *)
               destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
               destruct (lp_or_keep_τ_push τ v_push (s_v, π_v))
                  as [s_img π_img] eqn:Himg.
               exists s_img, π_img. split.
               ++ unfold M_g4_new. apply elem_of_map.
                  exists (s_v, π_v). split; [by rewrite Himg | exact Hin_v].
               ++ pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                                (s_v, π_v) Hne_τ) as Hτ'.
                  rewrite Himg in Hτ'. simpl in Hτ'. rewrite Hτ'. exact Hπ_v.
            -- (* OpEnqStored — conj. *)
               destruct Hsc_τ' as [Hsc_all Hsc_ex].
               split.
               { intros s' π' Hin; unfold M_g4_new in Hin;
                 apply elem_of_map in Hin as ([s_x π_x] & Heq & Hin_g);
                 pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                              (s_x, π_x) Hne_τ) as Hτ';
                 rewrite -Heq in Hτ'; simpl in Hτ';
                 rewrite Hτ'; by apply (Hsc_all s_x π_x Hin_g). }
               (* ∃ witness: use LP'd image of (s_v, π_v) which has both
                  τ' and τ linearized. *)
               destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
               destruct (lp_or_keep_τ_push τ v_push (s_v, π_v))
                  as [s_img π_img] eqn:Himg.
               exists s_img, π_img. split.
               ++ unfold M_g4_new. apply elem_of_map.
                  exists (s_v, π_v). split; [by rewrite Himg | exact Hin_v].
               ++ pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                                (s_v, π_v) Hne_τ) as Hτ'.
                  rewrite Himg in Hτ'. simpl in Hτ'. rewrite Hτ'. exact Hπ_v.
            -- intros s' π' Hin; unfold M_g4_new in Hin;
                 apply elem_of_map in Hin as ([s_x π_x] & Heq & Hin_g);
                 pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                              (s_x, π_x) Hne_τ) as Hτ';
                 rewrite -Heq in Hτ'; simpl in Hτ';
                 rewrite Hτ'; by apply (Hsc_τ' s_x π_x Hin_g).
            -- intros s' π' Hin; unfold M_g4_new in Hin;
                 apply elem_of_map in Hin as ([s_x π_x] & Heq & Hin_g);
                 pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                              (s_x, π_x) Hne_τ) as Hτ';
                 rewrite -Heq in Hτ'; simpl in Hτ';
                 rewrite Hτ'; by apply (Hsc_τ' s_x π_x Hin_g).
            -- (* OpDeqLinearized — chain trick provides the witness. *)
               destruct Hsc_τ' as (s_v & π_v & Hin_v & Hπ_v).
               destruct (lp_or_keep_τ_push τ v_push (s_v, π_v))
                  as [s_img π_img] eqn:Himg.
               exists s_img, π_img. split.
               ++ unfold M_g4_new. apply elem_of_map.
                  exists (s_v, π_v). split; [by rewrite Himg | exact Hin_v].
               ++ pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                                (s_v, π_v) Hne_τ) as Hτ'.
                  rewrite Himg in Hτ'. simpl in Hτ'. rewrite Hτ'. exact Hπ_v.
            -- intros s' π' Hin; unfold M_g4_new in Hin;
                 apply elem_of_map in Hin as ([s_x π_x] & Heq & Hin_g);
                 pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                              (s_x, π_x) Hne_τ) as Hτ';
                 rewrite -Heq in Hτ'; simpl in Hτ';
                 rewrite Hτ'; by apply (Hsc_τ' s_x π_x Hin_g).
          * intros s' π' Hin; unfold M_g4_new in Hin;
              apply elem_of_map in Hin as ([s_x π_x] & Heq & Hin_g);
              pose proof (lp_or_keep_τ_push_τ'_preserve τ τ' v_push
                           (s_x, π_x) Hne_τ) as Hτ';
              rewrite -Heq in Hτ'; simpl in Hτ';
              rewrite Hτ'; by apply (Hsc_τ' s_x π_x Hin_g).
      - (* slots_consistent unchanged. *)
        exact Hsc_slots4.
      - exact Hwell4.
      - (* trace_stat_consistent: stat[τ] := OpEnqDone, ts := ts ++ [(τ, Ret #())]. *)
        intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
        + rewrite lookup_insert_eq.
          pose proof (Htrst4 τ) as Htrst_τ. rewrite Hstat_τ4 in Htrst_τ.
          rewrite filter_app filter_cons_True; last reflexivity.
          rewrite filter_nil. rewrite Htrst_τ. reflexivity.
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
          rewrite filter_app filter_cons_False;
            last (by intros Heq; apply Hne_τ).
          rewrite filter_nil app_nil_r.
          exact (Htrst4 τ').
      - intros A seq HgoodA HnodupSeq Hsetof HJInvSeq.
        (* Step 1: Derive OLD GoodEnqSet. *)
        assert (HgoodA_old : GoodEnqSet A items4 stat4).
        { destruct HgoodA as [Hg1 Hg2]. split.
          - exact Hg1.
          - intros k Hin_A. destruct (Hg2 k Hin_A) as [Hcase | (τ_e & v_e & Hres)].
            + left. exact Hcase.
            + right. destruct (decide (τ_e = τ)) as [-> | Hne_τe].
              * rewrite lookup_insert_eq in Hres. discriminate.
              * exists τ_e, v_e. rewrite lookup_insert_ne in Hres;
                  last (intros ?; apply Hne_τe; congruence).
                exact Hres. }
        (* Step 2: Derive OLD JInvSeq. *)
        assert (HJInvSeq_old : JInvSeq seq slots4 stat4 scan_map4).
        { intros n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km.
          destruct (HJInvSeq n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km)
            as (τ_d & l & j_d & Hstat_d & Hscan_d & Hkl & Hkj).
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          - rewrite lookup_insert_eq in Hstat_d. discriminate.
          - exists τ_d, l, j_d. split_and!; try assumption.
            rewrite lookup_insert_ne in Hstat_d;
              last (intros ?; apply Hne_τd; congruence).
            exact Hstat_d. }
        (* Step 3: Apply OLD STRENGTHENED Hlinw_seq4. *)
        destruct (Hlinw_seq4 A seq HgoodA_old HnodupSeq Hsetof HJInvSeq_old)
          as (s_pre & π_pre & Hin_pre & Hlen_pre & Hsmatch_pre & Hsmatch_case_pre
              & Henq_pre & Hlin_pre & Hdone_pre & Hpending_pre & Hstored_pre & Hres_pre).
        (* π_pre[τ] = LP'd from OLD STRENGTHENED Hstored_pre. *)
        pose proof (Hstored_pre τ v_push (Z.to_nat back_val2) Hstat_τ4_pre) as Hπpre_τ_LP.
        (* lp_or_keep_τ_push τ v_push (s_pre, π_pre) = (s_pre, π_pre) since π_pre[τ] = LP'd. *)
        assert (Hlp_eq : lp_or_keep_τ_push τ v_push (s_pre, π_pre) = (s_pre, π_pre)).
        { unfold lp_or_keep_τ_push. rewrite decide_False; first reflexivity.
          simpl. rewrite Hπpre_τ_LP. intros Heq. discriminate. }
        exists s_pre, π_pre. split_and!.
        + (* (s_pre, π_pre) ∈ M_g4_new = set_map LP M_g4. *)
          unfold M_g4_new. apply elem_of_map.
          exists (s_pre, π_pre). split; [by rewrite Hlp_eq | exact Hin_pre].
        + exact Hlen_pre.
        + exact Hsmatch_pre.
        + (* TLA+ items+stat case match. items4 / slots4 unchanged.
             For OpEnqReserved fallback: τ_e ≠ τ (since stat_new[τ] = Done ≠ Reserved). *)
          intros n k Hseq_n.
          destruct (Hsmatch_case_pre n k Hseq_n) as
            [(v0 & Hitem & Hs) | (τ_e & v_e & Hres & Hs)].
          * left. by exists v0.
          * right. exists τ_e, v_e. split; last exact Hs.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            -- rewrite Hres in Hstat_τ4_pre. discriminate.
            -- rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τe; congruence).
               exact Hres.
        + (* OpEnqDone case. For τ_e = τ: NEW stat[τ] = OpEnqDone v_push back_val2.
             π_pre[τ] = LP'd by Hπpre_τ_LP. ✓
             For τ_d ≠ τ: OLD Henq_pre gives π_pre[τ_d] = LP'd. *)
          intros τ_d v_d i_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new.
            injection Hstat_d_new as <- _. exact Hπpre_τ_LP.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            exact (Henq_pre τ_d v_d i_d Hstat_d_new).
        + (* OpDeqLinearized case. *)
          intros τ_d v_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            exact (Hlin_pre τ_d v_d Hstat_d_new).
        + (* OpDeqDone case. *)
          intros τ_d v_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            exact (Hdone_pre τ_d v_d Hstat_d_new).
        + (* OpDeqPending case. *)
          intros τ_d Hstat_d_new.
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_d_new;
              last (intros ?; apply Hne_τd; congruence).
            exact (Hpending_pre τ_d Hstat_d_new).
        + (* OpEnqStored case. For τ_e ≠ τ: OLD STRENGTHENED Hstored_pre. *)
          intros τ_e v_e i_e Hstat_e_new.
          destruct (decide (τ_e = τ)) as [-> | Hne_τe].
          * rewrite lookup_insert_eq in Hstat_e_new. discriminate.
          * rewrite lookup_insert_ne in Hstat_e_new;
              last (intros ?; apply Hne_τe; congruence).
            exact (Hstored_pre τ_e v_e i_e Hstat_e_new).
        + (* OpEnqReserved case. For τ_e ≠ τ. *)
          intros τ_e v_e i_e Hres_e_new.
          destruct (decide (τ_e = τ)) as [-> | Hne_τe].
          * rewrite lookup_insert_eq in Hres_e_new. discriminate.
          * rewrite lookup_insert_ne in Hres_e_new;
              last (intros ?; apply Hne_τe; congruence).
            exact (Hres_pre τ_e v_e i_e Hres_e_new).
      - (* slots_bounded: unchanged. *)
        exact Hbnd4.
      - (* slots_stat_iff: stat τ → OpEnqDone, slots unchanged. *)
        destruct Hssi4 as (Hssi_a4 & Hssi_b4 & Hssi_c4 & Hssi_d4).
        unfold stat_owns, stat_faad.
        split_and!.
        + intros τ' v' i' Howns.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          * destruct Howns as [Howns | Howns];
              rewrite lookup_insert_eq in Howns; first discriminate.
            injection Howns as <- <-.
            exact (Hssi_a4 τ v_push (Z.to_nat back_val2) (or_introl Hstat_τ4_pre)).
          * apply (Hssi_a4 τ' v' i').
            destruct Howns as [Howns | Howns];
              rewrite lookup_insert_ne in Howns;
              try (intros ?; apply Hne_τ'; congruence);
              [left | right]; exact Howns.
        + intros i' v' Hslot'.
          destruct (Hssi_b4 _ _ Hslot') as (τ_w & Hstat_w).
          destruct (decide (τ_w = τ)) as [-> | Hne_τw].
          * exists τ. right.
            (* Hstat_w : stat[τ] = Stored ∨ Done. We know Hstat_τ4_pre = Stored. *)
            destruct Hstat_w as [Hstat_w | Hstat_w].
            -- (* Stored. Then slots[i'] = Some v', and we know slots[Z.to_nat back_val2] = Some v_push (via Hssi_a4 left). So i' = Z.to_nat back_val2, v' = v_push. *)
               rewrite Hstat_w in Hstat_τ4_pre. injection Hstat_τ4_pre as -> ->.
               apply lookup_insert_eq.
            -- (* Done. Hstat_w = stat[τ] = Done; but stat[τ] = Stored. Contradict. *)
               rewrite Hstat_w in Hstat_τ4_pre. discriminate.
          * exists τ_w. destruct Hstat_w as [Hstat_w | Hstat_w];
              [left | right];
              rewrite lookup_insert_ne;
              try (intros ?; apply Hne_τw; congruence);
              exact Hstat_w.
        + intros τ_1 τ_2 v_1 v_2 i' Hτ1 Hτ2.
          destruct (decide (τ_1 = τ)) as [-> | Hne_τ1];
            destruct (decide (τ_2 = τ)) as [-> | Hne_τ2].
          * reflexivity.
          * (* τ_1 = τ: Hτ1 says stat'[τ] = Reserved/Stored/Done at i'. *)
            destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
              rewrite lookup_insert_eq in Hτ1; try discriminate.
            injection Hτ1 as Heqv Heqi. subst i'.
            (* τ_2 ≠ τ: Hτ2 is old faad at back_val2. *)
            assert (Hτ2_old : stat_faad stat4 τ_2 v_2 (Z.to_nat back_val2)).
            { destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                rewrite lookup_insert_ne in Hτ2;
                try (intros ?; apply Hne_τ2; congruence).
              - left. exact Hτ2.
              - right. left. exact Hτ2.
              - right. right. exact Hτ2. }
            exfalso. apply Hne_τ2. symmetry.
            eapply (Hssi_c4 τ τ_2 v_push v_2 (Z.to_nat back_val2)).
            -- right. left. exact Hstat_τ4_pre.
            -- exact Hτ2_old.
          * destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
              rewrite lookup_insert_eq in Hτ2; try discriminate.
            injection Hτ2 as Heqv Heqi. subst i'.
            assert (Hτ1_old : stat_faad stat4 τ_1 v_1 (Z.to_nat back_val2)).
            { destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                rewrite lookup_insert_ne in Hτ1;
                try (intros ?; apply Hne_τ1; congruence).
              - left. exact Hτ1.
              - right. left. exact Hτ1.
              - right. right. exact Hτ1. }
            exfalso. apply Hne_τ1.
            eapply (Hssi_c4 τ_1 τ v_1 v_push (Z.to_nat back_val2)).
            -- exact Hτ1_old.
            -- right. left. exact Hstat_τ4_pre.
          * assert (Hτ1_old : stat_faad stat4 τ_1 v_1 i').
            { destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                rewrite lookup_insert_ne in Hτ1;
                try (intros ?; apply Hne_τ1; congruence).
              - left. exact Hτ1.
              - right. left. exact Hτ1.
              - right. right. exact Hτ1. }
            assert (Hτ2_old : stat_faad stat4 τ_2 v_2 i').
            { destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                rewrite lookup_insert_ne in Hτ2;
                try (intros ?; apply Hne_τ2; congruence).
              - left. exact Hτ2.
              - right. left. exact Hτ2.
              - right. right. exact Hτ2. }
            apply (Hssi_c4 τ_1 τ_2 v_1 v_2 i' Hτ1_old Hτ2_old).
        + intros τ' v' i' Hstat'.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          * destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
              rewrite lookup_insert_eq in Hstat'; try discriminate.
            injection Hstat' as Heqv Heqi. subst i'.
            exact (Hssi_d4 τ v_push (Z.to_nat back_val2)
                          (or_intror (or_introl Hstat_τ4_pre))).
          * assert (Hstat'_old : stat_faad stat4 τ' v' i').
            { destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
                rewrite lookup_insert_ne in Hstat';
                try (intros ?; apply Hne_τ'; congruence).
              - left. exact Hstat'.
              - right. left. exact Hstat'.
              - right. right. exact Hstat'. }
            exact (Hssi_d4 τ' v' i' Hstat'_old).
      - intros cfg pushes Hin Hnd Hsubset Hstat_pushes.
        unfold M_g4_new in Hin. apply elem_of_map in Hin as (cfg_x & Heq & Hin_x).
        subst cfg.
        (* τ ∉ pushes.*1 because stat_new[τ] = OpEnqDone, not Reserved/Stored. *)
        assert (Hτ_notin : τ ∉ pushes.*1).
        { intros Hin_τ.
          apply list_elem_of_fmap_1 in Hin_τ as (pv & Heq_τ & Hpv_in).
          destruct (Hstat_pushes pv Hpv_in) as (v' & i' & [Hs | Hs]);
            rewrite -Heq_τ in Hs; rewrite lookup_insert_eq in Hs; discriminate. }
        (* stat_pushes lifted from new stat to stat4 (drop τ since τ ∉ pushes). *)
        assert (Hstat_pushes_old : ∀ pv, pv ∈ pushes → ∃ v i,
                  stat4 !! pv.1 = Some (OpEnqReserved v i) ∨
                  stat4 !! pv.1 = Some (OpEnqStored v i)).
        { intros pv Hpv_in. destruct (Hstat_pushes pv Hpv_in) as (v' & i' & Hstat').
          exists v', i'. assert (Hne_pv_τ : pv.1 ≠ τ).
          { intros Heq_pv. apply Hτ_notin.
            rewrite -Heq_pv. apply (list_elem_of_fmap_2 fst _ pv); exact Hpv_in. }
          destruct Hstat' as [Hs | Hs].
          - left. rewrite lookup_insert_ne in Hs; last (intros ?; apply Hne_pv_τ; congruence).
            exact Hs.
          - right. rewrite lookup_insert_ne in Hs; last (intros ?; apply Hne_pv_τ; congruence).
            exact Hs. }
        (* Case split on whether cfg_x.2[τ] is Pending Push. *)
        destruct (decide (cfg_x.2 !! τ = Some (encode_request (Push v_push), None)))
          as [Hcfg_x_pending | Hcfg_x_npending].
        + (* cfg_x.2[τ] = Pending Push. LP cfg_x via closure_push_single. *)
          pose proof (closure_push_single M_g4 stat4 cfg_x τ v_push (Z.to_nat back_val2)
                      Hcl_push4 Hin_x Hcfg_x_pending (or_intror Hstat_τ4_pre)) as Hin_xLP.
          assert (HlpEq : lp_or_keep_τ_push τ v_push cfg_x
                       = (cfg_x.1 ++ [v_push], <[τ:=(encode_request (Push v_push), Some #())]>cfg_x.2)).
          { unfold lp_or_keep_τ_push. rewrite decide_True; first reflexivity. exact Hcfg_x_pending. }
          rewrite HlpEq.
          rewrite HlpEq in Hsubset.
          pose proof (Hcl_push4 _ pushes Hin_xLP Hnd Hsubset Hstat_pushes_old) as Hcl_xLP.
          unfold M_g4_new. apply elem_of_map.
          exists (lineraize_pending_push pushes
                    (cfg_x.1 ++ [v_push], <[τ:=(encode_request (Push v_push), Some #())]>cfg_x.2)).
          split; last exact Hcl_xLP.
          (* lp_or_keep is identity since τ already LP'd in this config. *)
          unfold lp_or_keep_τ_push.
          rewrite decide_False; first reflexivity.
          unfold lineraize_pending_push. simpl.
          rewrite map_lookup_imap lookup_insert_eq /=.
          rewrite bool_decide_eq_false_2; last (intros Hτ_in; apply Hτ_notin; exact Hτ_in).
          intros Habs. discriminate Habs.
        + (* cfg_x.2[τ] ≠ Pending Push: lp_or_keep is identity on cfg_x. *)
          assert (Hlp_id : lp_or_keep_τ_push τ v_push cfg_x = cfg_x).
          { unfold lp_or_keep_τ_push. rewrite decide_False; first reflexivity. exact Hcfg_x_npending. }
          rewrite Hlp_id in Hsubset.
          pose proof (Hcl_push4 cfg_x pushes Hin_x Hnd Hsubset Hstat_pushes_old) as Hcl_x.
          unfold M_g4_new. apply elem_of_map.
          exists (lineraize_pending_push pushes cfg_x). split; last exact Hcl_x.
          rewrite Hlp_id.
          unfold lp_or_keep_τ_push.
          rewrite decide_False; first reflexivity.
          unfold lineraize_pending_push. simpl.
          rewrite map_lookup_imap.
          destruct (cfg_x.2 !! τ) as [x|] eqn:Hcfgτ; simpl.
          * rewrite bool_decide_eq_false_2; last (intros Hτ_in; apply Hτ_notin; exact Hτ_in).
            intros Habs. apply Hcfg_x_npending.
            rewrite Hcfgτ /= in Habs. exact Habs.
          * intros Habs. rewrite Hcfgτ /= in Habs. discriminate.
      - intros τ' Hstat_None.
        destruct (decide (τ' = τ)) as [-> | Hne_τ'].
        + rewrite lookup_insert_eq in Hstat_None. discriminate.
        + rewrite lookup_insert_ne in Hstat_None;
            last (intros ?; apply Hne_τ'; congruence).
          apply (Hscan_dom4 τ' Hstat_None).
      - (* scan_map_l_bounded: scan_map and back_val unchanged. *)
        exact Hscan_lb4. }
    wp_pures. by iApply "HΦ".
  Qed.

End proof.
