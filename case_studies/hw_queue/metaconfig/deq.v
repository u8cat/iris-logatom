(* deq.v — Dequeue wrapper spec. *)

From stdpp Require Import base list gmap propset.
From iris_logatom.pure_logic Require Import encodable linear.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.metaconfig Require Import tracking.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants ghost_map ghost_var.
From iris.heap_lang Require Import notation proofmode.
From iris_logatom.heap_lang Require Import mgc.

From case_studies.hw_queue Require Import impl.
From case_studies.hw_queue.metaconfig Require Import defs lemmas.
Import HWQMetaConfigNotation.
Local Existing Instance propset_signle_config_q_leibniz_equiv.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !hwqMcG Σ}.

  (* Phase 1 helper: preservation of [I_lang_hwq] under [Call Pop]. *)
  Lemma phase1_call_preserves_I_lang_pop ts τ :
    τ ∉ ts.*1 →
    I_lang_hwq ts →
    I_lang_hwq (ts ++ [(τ, Call Pop #())]).
  Proof.
    intros Hfresh [(M' & s & π & Hsteps & Hin) Hwf].
    split; last by apply per_tag_wellformed_snoc_call_pop.
    set M'_new := ((λ '(s', π'), (s', <[τ:=(Pop, #(), None)]> π'))
                    <$> M' : @meta_config hwq_model).
    exists M'_new, s, (<[τ:=(Pop, #(), None)]> π).
    split.
    - eapply rtcL_r; first exact Hsteps.
      apply (mcfg_step_call M' τ Pop #()).
      + intros [s' π'] Hin_pre. simpl.
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hsteps Hin_pre) as Hdom_sub.
        intros Hin_dom. apply Hdom_sub in Hin_dom.
        apply elem_of_list_to_set in Hin_dom. contradiction.
      + done.
    - apply elem_of_PropSet. eexists (s, π). split; [done | exact Hin].
  Qed.

  (* Phase 4 helper: preservation under [Ret (SOMEV v)]
     when the trace already shows the matching Call (Pop) and there
     exists a config in [M_full] with τ linearized to (Pop, NonEmpty v). *)
  Lemma phase4_ret_preserves_I_lang_pop ts τ v :
    I_lang_hwq ts →
    filter (λ t, t.1 = τ) ts = [(τ, Call Pop #())] →
    (∃ (M_full : @meta_config hwq_model) s π,
        rtcL mcfg_step mcfg_init M_full ts ∧ (s, π) ∈ M_full ∧
        π !! τ = Some (Pop, #(),
                       Some (encode_response (NonEmpty v)))) →
    I_lang_hwq (ts ++ [(τ, Ret (encode_response (NonEmpty v)))]).
  Proof.
    intros [_ Hwf] Hfilter (M_full & s & π & Hsteps & Hin & Hπτ).
    split.
    - set (M_full_new := (M_full ∩
        {[ (_, π') | snd <$> (π' !! τ) =
                       Some (Some (encode_response (NonEmpty v))) ]})
        : @meta_config hwq_model).
      exists M_full_new, s, π. split.
      + eapply rtcL_r; first exact Hsteps.
        apply (mcfg_step_ret M_full τ (encode_response (NonEmpty v))).
      + apply elem_of_intersection. split; first exact Hin.
        apply elem_of_PropSet. rewrite Hπτ /=. reflexivity.
    - by eapply per_tag_wellformed_snoc_ret.
  Qed.

  (* ──────────────────────────────────────────────────────────────────────
     Proof sketch.

     Top-level structure of [pop_wrapper_spec]:

       wp_pures (unfold call_ret_wrapper)
       Phase 1 (trace_fresh, Call Pop):
         - awp_apply trace_fresh_spec; iInv invariant.
         - iSplit; apply phase1_call_preserves_I_lang_pop.
         - Commit; update M_g and stat[τ := OpDeqPending].
       Phase 2 (read back, recursive scan loop in dequeue_aux):
         - Use iLöb induction over the inner recursion.
         - Each loop iteration:
           * Load arr[j]; if NONE then recurse (no ghost change).
           * If SOMEV v then CmpXchg (Phase 3).
       Phase 3 (CmpXchg success — LINEARIZATION POINT):
         - iInv "Hinv". Witnessed by slots[i] = Some v from prior Phase-3-of-Enq.
         - Apply mcfg_step_interm with the witness (s, π) ∈ M_g where
           head s = v (the head of the queue's abstract state).
         - request_response s Pop (tail s) (NonEmpty v).
         - Update M_g; update stat[τ] to OpDeqLinearized v.
       Phase 4 (trace_emit (Ret (SOMEV v))):
         - awp_apply trace_emit_spec; iInv invariant.
         - For atomic-update: apply phase4_ret_preserves_I_lang_pop.
         - Commit; update M_g; update stat[τ] to OpDeqDone v.
       Final wp_pures; iApply "HΦ"; done.
     ──────────────────────────────────────────────────────────────────── *)

  Lemma pop_wrapper_spec γ tracer (q : val) :
    {{{ trace_inv tracer I_lang_hwq ∗ is_hwq tracer γ q }}}
      call_ret_wrapper tracer Pop (λ: "q" <>, SOME (dequeue "q"))%V q #()
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "[#Itrace #Ihwq] HΦ".
    rewrite /call_ret_wrapper.
    iDestruct "Ihwq" as (γM γ_status γ_slots γ_scan sz ar back) "(-> & %Hsz_nn & #Hmeta & #Hinv)".
    wp_pures.

    (* ──────────────────────────────────────────────────────────────────
       Phase 1 — trace_fresh: emit (τ, Call Pop).
       ──────────────────────────────────────────────────────────────── *)
    wp_bind (trace_fresh _ _).
    awp_apply (trace_fresh_spec _ (Call Pop #())
                (InjLV (#Pop, #())%V) I_lang_hwq with "Itrace");
      first exact (decode_encode_val (Call Pop #())).
    iInv "Hinv" as (items back_val ts M_g stat slots scan_map)
      "(>Hback & >Har & >Hts & >%Hlen & >%Hbpos & >HγM & >Hstat & >Hslots & >Hscan & #Hslots_persist1 &
         >%Hmcfg_steps & >%Hne & >%Hpw & >%Hsc & >%Hsc_slots & >%Hwell & >%Htrst & >%Hlinw_seq & >%Hbnd & >%Hssi & >%Hcl_push & >%Hscan_dom & >%Hscan_lb)".
    iApply (fupd_mask_intro); first solve_ndisj. iIntros "Hclose_fupd".
    iFrame "Hts". iSplit.
    { iPureIntro. intros τ Hfresh.
      apply phase1_call_preserves_I_lang_pop; auto.
      split.
      - apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        exists (set_to_propset M_g), s_w, π_w. split; auto.
      - exact Hpw. }
    iSplit.
    { iIntros "[Hts _]". iMod "Hclose_fupd" as "_". iModIntro.
      iSplitR "HΦ"; last done.
      iNext. iExists items, back_val, ts, M_g, stat, slots, scan_map.
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist1".
      iPureIntro. split_and!; assumption. }
    iIntros (τ) "[Hts %Hfresh]". iMod "Hclose_fupd" as "_".
    (* M_g_new = M_g_mapped. Just Call mapping (τ at Pop, None added to each cfg).
       We no longer build M_g_LP_pop — closure_pop has been dropped from
       the invariant, so we don't need to populate speculative LP'd-Pop configs. *)
    pose (M_g_mapped :=
      (set_map (λ x : single_config_q,
                  (x.1, <[τ:=(Pop, #(), None)]> x.2))
              M_g : gset single_config_q)).
    pose (M_g_new := M_g_mapped).
    iMod (ghost_var_update M_g_new with "HγM") as "HγM".
    (* Apply mcfg_step_call directly to get M_full_new (propset) of Call-mapped configs. *)
    assert (Hfresh_M_full : set_Forall (λ '(_, π), τ ∉ dom π)
                             (set_to_propset M_g : @meta_config hwq_model)).
    { intros [s' π'] Hin Hin_dom.
      pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hin) as Hdom_sub.
      apply Hdom_sub in Hin_dom.
      apply elem_of_list_to_set in Hin_dom. contradiction. }
    set (M_full_new :=
      ((λ '(s', π'), (s', <[τ:=(Pop, #(), None)]> π'))
         <$> (set_to_propset M_g : @meta_config hwq_model))
      : @meta_config hwq_model).
    assert (Hmcfg_steps_new :
      rtcL mcfg_step (set_to_propset M_g) M_full_new [(τ, Call Pop #())]).
    { apply rtcL_once.
      apply (mcfg_step_call (set_to_propset M_g) τ Pop #()).
      - exact Hfresh_M_full.
      - reflexivity. }
    assert (Htau_fresh_stat : stat !! τ = None).
    { destruct (stat !! τ) as [s_op|] eqn:Hlookup; last reflexivity.
      exfalso.
      pose proof (Hsc τ) as Hsc_τ. rewrite Hlookup in Hsc_τ.
      destruct s_op.
      - (* OpEnqPending *)
        apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom. eexists; exact (Hsc_τ s_w π_w Hw_in). }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction.
      - (* OpEnqReserved — now disjunctive (conj ∀-disj, ∃-LP'd). *)
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
      - (* OpEnqStored — conj (∀ disjunction, ∃ linearized) *)
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
      - (* OpDeqLinearized — existential *)
        destruct Hsc_τ as (s_w & π_w & Hw_in & Hπ_w).
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom. eexists; exact Hπ_w. }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction.
      - apply set_choose_L in Hne as [[s_w π_w] Hw_in].
        assert ((s_w, π_w) ∈ (set_to_propset M_g : @meta_config hwq_model)) as Hw_full
          by (apply elem_of_set_to_propset; exact Hw_in).
        pose proof (mcfg_steps_dom_in_trace _ _ _ _ Hmcfg_steps Hw_full) as Hdom_sub.
        assert (τ ∈ dom π_w) as Hτ_dom.
        { apply elem_of_dom. eexists; exact (Hsc_τ s_w π_w Hw_in). }
        apply Hdom_sub in Hτ_dom.
        apply elem_of_list_to_set in Hτ_dom. contradiction. }
    iMod (ghost_map_insert τ OpDeqPending with "Hstat") as "[Hstat Hstat_τ]";
      first exact Htau_fresh_stat.
    iMod (ghost_map_insert τ (0%nat, 0%nat) with "Hscan") as "[Hscan Hscan_τ]";
      first exact (Hscan_dom τ Htau_fresh_stat).
    (* M_full_new is the propset image of (set_to_propset M_g) under the
       Call mapping, which equals set_to_propset M_g_mapped = set_to_propset M_g_new. *)
    assert (HM_full_new_eq : M_full_new = (set_to_propset M_g_new : @meta_config hwq_model)).
    { apply leibniz_equiv. intros y. split.
      - intros Hy. apply elem_of_set_to_propset.
        unfold M_full_new in Hy.
        apply elem_of_PropSet in Hy as ([s_z π_z] & Heq & Hz_in).
        apply elem_of_set_to_propset in Hz_in.
        subst y. unfold M_g_new, M_g_mapped.
        apply elem_of_map. exists (s_z, π_z). split; [reflexivity | exact Hz_in].
      - intros Hy. rewrite elem_of_set_to_propset in Hy.
        unfold M_g_new, M_g_mapped in Hy.
        apply elem_of_map in Hy as (x & -> & Hx_in).
        destruct x as [s_x π_x]. unfold M_full_new.
        apply elem_of_PropSet. exists (s_x, π_x). split; first reflexivity.
        apply elem_of_set_to_propset. exact Hx_in. }
    iModIntro.
    iSplitR "HΦ Hstat_τ Hscan_τ".
    { iNext.
      iExists items, back_val, (ts ++ [(τ, Call Pop #())]),
              M_g_new, (<[τ:=OpDeqPending]> stat), slots,
              (<[τ:=(0%nat, 0%nat)]> scan_map).
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist1".
      iPureIntro. split_and!.
      - exact Hlen.
      - exact Hbpos.
      - (* mcfg_steps: combine prior steps with helper's Call+LP chain. *)
        rewrite -HM_full_new_eq.
        eapply rtcL_trans; first exact Hmcfg_steps.
        exact Hmcfg_steps_new.
      - intros Hempty. apply Hne.
        apply set_choose_L in Hne as [x Hx_in].
        exfalso.
        assert ((x.1, <[τ:=(Pop, #(), None)]> x.2) ∈
                (M_g_new : gset single_config_q)) as Hin_map.
        { unfold M_g_new, M_g_mapped. apply elem_of_map.
          exists x. destruct x as [s' π']. split; [done | exact Hx_in]. }
        clear -Hin_map Hempty. set_solver.
      - by apply per_tag_wellformed_snoc_call_pop.
      - intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
        + rewrite lookup_insert_eq.
          (* τ at OpDeqPending: disjunctive ∀; new configs have
             π[τ] = (Pop, #(), None) — left disjunct. *)
          intros s' π' Hin_g.
          unfold M_g_new, M_g_mapped in Hin_g.
          apply elem_of_map in Hin_g as ([s'' π''] & Heq & _Hin_g_old).
          injection Heq as -> ->.
          left. rewrite lookup_insert_eq. reflexivity.
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
          pose proof (Hsc τ') as Hsc_τ'.
          assert (Hkey : ∀ (s' : @S hwq_model) π',
                     (s', π') ∈ (M_g_new : gset single_config_q) →
                     ∃ s'' π'', (s'', π'') ∈ M_g ∧
                                s' = s'' ∧
                                π' = <[τ:=(Pop, #(), None)]> π'').
          { intros s' π' Hin_new.
            unfold M_g_new, M_g_mapped in Hin_new.
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
            -- (* OpEnqReserved — disjunctive (∀ disj + ∃ LP'd). *)
               destruct Hsc_τ' as [Hsc_all Hsc_ex].
               split.
               { intros s' π' Hin_new.
                 destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
                 rewrite lookup_insert_ne;
                   last (intros ?; apply Hne_τ; congruence).
                 apply (Hsc_all s'' π'' Hin_old). }
               destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
               exists s_v, (<[τ:=(Pop, #(), None)]> π_v).
               split.
               { unfold M_g_new, M_g_mapped. apply elem_of_map.
                 exists (s_v, π_v). split; first reflexivity. exact Hin_v. }
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               exact Hπ_v.
            -- (* OpEnqStored — conj (∀ disj + ∃ LP'd). *)
               destruct Hsc_τ' as [Hsc_all Hsc_ex].
               split.
               { intros s' π' Hin_new.
                 destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
                 rewrite lookup_insert_ne;
                   last (intros ?; apply Hne_τ; congruence).
                 apply (Hsc_all s'' π'' Hin_old). }
               destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
               exists s_v, (<[τ:=(Pop, #(), None)]> π_v).
               split.
               { unfold M_g_new, M_g_mapped. apply elem_of_map.
                 exists (s_v, π_v). split; first reflexivity. exact Hin_v. }
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               exact Hπ_v.
            -- (* OpEnqDone v0: ∀-LP'd. *)
               intros s' π' Hin_new.
               destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               by apply (Hsc_τ' s'' π'' Hin_old).
            -- (* OpDeqPending: ∀-disjunctive. *)
               intros s' π' Hin_new.
               destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               by apply (Hsc_τ' s'' π'' Hin_old).
            -- (* OpDeqLinearized: ∃-LP'd. Lift via Call mapping. *)
               destruct Hsc_τ' as (s_v & π_v & Hin_v & Hπ_v).
               exists s_v, (<[τ:=(Pop, #(), None)]> π_v).
               split.
               { unfold M_g_new, M_g_mapped. apply elem_of_map.
                 exists (s_v, π_v). split; first reflexivity. exact Hin_v. }
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               exact Hπ_v.
            -- (* OpDeqDone: ∀-LP'd. *)
               intros s' π' Hin_new.
               destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
               rewrite lookup_insert_ne;
                 last (intros ?; apply Hne_τ; congruence).
               by apply (Hsc_τ' s'' π'' Hin_old).
          * (* stat[τ'] = None: ∀, π[τ'] = None. *)
            intros s' π' Hin_new.
            destruct (Hkey s' π' Hin_new) as (s'' & π'' & Hin_old & -> & ->).
            rewrite lookup_insert_ne;
              last (intros ?; apply Hne_τ; congruence).
            by apply (Hsc_τ' s'' π'' Hin_old).
      - exact Hsc_slots.
      - exact Hwell.
      - (* trace_stat_consistent: insert τ → OpDeqPending into stat. *)
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
          - rewrite lookup_insert_eq in Hscan_d.
            injection Hscan_d as _ Hj_d_eq. subst j_d. lia.
          - exists τ_d, l, j_d. split_and!; try assumption.
            + rewrite lookup_insert_ne in Hstat_d;
                last (intros ?; apply Hne_τd; congruence).
              exact Hstat_d.
            + rewrite lookup_insert_ne in Hscan_d;
                last (intros ?; apply Hne_τd; congruence).
              exact Hscan_d. }
        (* Step 1b: reduce new GoodEnqSet to old. Phase 1 Call deq adds τ at
           OpDeqPending (NOT OpEnqReserved), so OpEnqReserved entries are unchanged. *)
        assert (HgoodA_old : GoodEnqSet A items stat).
        { destruct HgoodA as [Hg1 Hg2]. split; first exact Hg1.
          intros k Hin_A. destruct (Hg2 k Hin_A) as [Hi | (τ_e & v_e & Hres)].
          - left. exact Hi.
          - right. destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            + rewrite lookup_insert_eq in Hres. discriminate.
            + exists τ_e, v_e. rewrite lookup_insert_ne in Hres;
                last (intros ?; apply Hne_τe; congruence). exact Hres. }
        (* Step 2: apply IH to get config in M_g. *)
        destruct (Hlinw_seq A seq HgoodA_old HnodupSeq Hsetof HJInvSeq_old)
          as (s & π & Hin_g & Hlen_s & Hsmatch & Hsmatch_case & Henq_d & Hlin_d
              & Hdone_d & Hpending_d & Hstored_d & Hres_d).
        (* Step 3: lift to M_g_new via Call mapping (M_g_mapped). *)
        pose (π_new := <[τ:=(Pop, #(), None)]> π).
        exists s, π_new. split_and!.
        + unfold M_g_new, M_g_mapped. apply elem_of_map.
          exists (s, π). split; first reflexivity. exact Hin_g.
        + exact Hlen_s.
        + exact Hsmatch.
        + (* TLA+ items+stat case match. *)
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
          * unfold π_new. rewrite lookup_insert_eq. reflexivity.
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
        + (* OpEnqReserved case. *)
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
      - (* slots_stat_iff: τ inserted with OpDeqPending (no idx).
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
      - intros cfg pushes Hin Hnd Hsubset Hstat_pushes.
        unfold M_g_new, M_g_mapped in Hin.
        apply elem_of_map in Hin as (cfg_x & Heq & Hin_x).
        subst cfg.
        (* τ ∉ pushes.*1 because stat_new[τ] = OpDeqPending, not Reserved/Stored. *)
        assert (Hτ_notin : τ ∉ pushes.*1).
        { intros Hin_τ.
          apply list_elem_of_fmap_1 in Hin_τ as (pv & Heq_τ & Hpv_in).
          destruct (Hstat_pushes pv Hpv_in) as (v' & i' & [Hs | Hs]);
            rewrite -Heq_τ in Hs; rewrite lookup_insert_eq in Hs; discriminate. }
        (* pushes ⊆ pending_push_of_config cfg_x (because τ has Pop=InjLV,
           which is not Push=InjRV, so τ doesn't appear in pending_push). *)
        assert (Hsubset' : pushes ⊆ pending_push_of_config cfg_x).
        { intros pv Hpv_in.
          assert (Hpv_cfg : pv ∈ pending_push_of_config
                              (cfg_x.1, <[τ:=(Pop, #(), None)]>cfg_x.2)).
          { apply Hsubset. exact Hpv_in. }
          unfold pending_push_of_config in Hpv_cfg |- *.
          apply list_elem_of_omap in Hpv_cfg as ([τ' [req resp]] & Hin_list & Heq).
          apply elem_of_map_to_list in Hin_list. simpl in *.
          destruct (decide (τ' = τ)) as [Heq_τ | Hne_τ'].
          - subst τ'. rewrite lookup_insert_eq in Hin_list.
            injection Hin_list as Hreq Hresp. subst req. subst resp.
            simpl in Heq.
            unfold Pop in Heq. simpl in Heq.
            discriminate.
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
        unfold M_g_new, M_g_mapped. apply elem_of_map.
        exists (lineraize_pending_push pushes cfg_x). split; last exact Hcl_x.
        unfold lineraize_pending_push. simpl. f_equal.
        (* Need: <[τ:=(Pop, None)]>(map_imap ... cfg_x.2)
                = map_imap ... <[τ:=(Pop, None)]>cfg_x.2 *)
        apply map_eq. intros τ'.
        destruct (decide (τ' = τ)) as [-> | Hne_τ'].
        + rewrite lookup_insert_eq map_lookup_imap lookup_insert_eq /=.
          rewrite bool_decide_eq_false_2; first reflexivity.
          intros Hin_τ. apply Hτ_notin. exact Hin_τ.
        + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ'; congruence).
          rewrite !map_lookup_imap.
          rewrite lookup_insert_ne; last (intros ?; apply Hne_τ'; congruence).
          reflexivity.
      - intros τ' Hstat_None.
        destruct (decide (τ' = τ)) as [-> | Hne_τ'].
        + rewrite lookup_insert_eq in Hstat_None. discriminate.
        + rewrite lookup_insert_ne in Hstat_None;
            last (intros ?; apply Hne_τ'; congruence).
          rewrite lookup_insert_ne;
            last (intros ?; apply Hne_τ'; congruence).
          apply (Hscan_dom τ' Hstat_None).
      - (* scan_map_l_bounded: scan_map gains (τ, (0,0)); 0 ≤ back_val. *)
        intros τ_p l j Hscan_τ_p.
        destruct (decide (τ_p = τ)) as [-> | Hne_τp].
        + rewrite lookup_insert_eq in Hscan_τ_p.
          injection Hscan_τ_p as <- _. lia.
        + rewrite lookup_insert_ne in Hscan_τ_p;
            last (intros ?; apply Hne_τp; congruence).
          exact (Hscan_lb τ_p l j Hscan_τ_p). }
    (* ──────────────────────────────────────────────────────────────────
       After Phase 1, the residual program is:
         let "res" := (λ: "q" <>, SOME (dequeue "q")) q #() in
         trace_emit #l #τ (InjR "res");; "res"
       ──────────────────────────────────────────────────────────────── *)
    wp_pures.
    (* Now executing [SOME (dequeue q)]. We bind on [dequeue q]. *)
    wp_bind (dequeue _).

    (* ──────────────────────────────────────────────────────────────────
       Phase 2 — outer Löb on [dequeue q].
       The dequeue loops until it successfully grabs a value.
       Parameterized by scan_map[τ]'s current value (l_outer, j_outer) so
       that the inner-loop's i=0 re-entry can pass any value (subsumed by
       the Phase 2 read-back update). *)
    iAssert (∀ (l_outer j_outer : nat),
              τ ↪[γ_status] OpDeqPending -∗
              τ ↪[γ_scan] (l_outer, j_outer) -∗
              (∀ v : val, True -∗ Φ v) -∗
              WP (dequeue (#sz, #ar, #back)%V)%E
                {{ (v_ret : val),
                   WP (let: "res" := InjR v_ret in
                       trace_emit #tracer #(Z.pos τ) (InjR "res");; "res")%E
                   {{ (v' : val), Φ v' }} }})%I
      as "Houter"; last first.
    { iApply ("Houter" $! 0%nat 0%nat with "Hstat_τ Hscan_τ HΦ"). }
    iIntros (l_outer j_outer) "Hstat_τ Hscan_τ HΦ".
    iLöb as "IH_outer" forall (l_outer j_outer).
    rewrite /dequeue.
    wp_pures.

    (* Read back to get a snapshot of the current back counter, AND update
       scan_map[τ] to record the scan upper bound. This is the TLA+ JInvSeq
       step at the outer loop's read of back. *)
    wp_bind (! _)%E.
    iInv "Hinv" as (items2 back_val2 ts2 M_g2 stat2 slots2 scan_map2)
      "(>Hback & >Har & >Hts & >%Hlen2 & >%Hbpos2 & >HγM & >Hstat & >Hslots & >Hscan & #Hslots_persist2 &
         >%Hmcfg_steps2 & >%Hne2 & >%Hpw2 & >%Hsc2 & >%Hsc_slots2 & >%Hwell2 & >%Htrst2 & >%Hlinw_seq2 & >%Hbnd2 & >%Hssi2 & >%Hcl_push2 & >%Hscan_dom2 & >%Hscan_lb2)".
    wp_load.
    iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ2.
    iDestruct (ghost_map_lookup with "Hscan Hscan_τ") as %Hscan_τ2_pre.
    (* TLA+ alignment: at the read of back, update scan_map[τ] := (range_z, 0).
       This corresponds to JInvSeq scaffolding's outer-loop step. *)
    pose (range_z2_nat := Z.to_nat (back_val2 `min` sz)%Z).
    iMod (ghost_map_update (range_z2_nat, 0%nat) with "Hscan Hscan_τ")
      as "[Hscan Hscan_τ]".
    iModIntro.
    iSplitR "HΦ Hstat_τ Hscan_τ".
    { iNext. iExists items2, back_val2, ts2, M_g2, stat2, slots2,
                     (<[τ:=(range_z2_nat, 0%nat)]> scan_map2).
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist2".
      iPureIntro. split_and!; try assumption.
      - intros A seq HgoodA HnodupSeq Hsetof HJInvSeq.
        assert (HJInvSeq_old : JInvSeq seq slots2 stat2 scan_map2).
        { intros n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km.
          destruct (HJInvSeq n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km)
            as (τ_d & l & j_d & Hstat_d & Hscan_d & Hkl & Hkj).
          destruct (decide (τ_d = τ)) as [-> | Hne_τd].
          - rewrite lookup_insert_eq in Hscan_d.
            injection Hscan_d as _ Hj_d_eq. subst j_d. lia.
          - exists τ_d, l, j_d. split_and!; try assumption.
            rewrite lookup_insert_ne in Hscan_d;
              last (intros ?; apply Hne_τd; congruence).
            exact Hscan_d. }
        exact (Hlinw_seq2 A seq HgoodA HnodupSeq Hsetof HJInvSeq_old).
      - intros τ' Hstat_None.
        destruct (decide (τ' = τ)) as [-> | Hne_τ'].
        + rewrite Hstat_τ2 in Hstat_None. discriminate.
        + rewrite lookup_insert_ne;
            last (intros ?; apply Hne_τ'; congruence).
          apply (Hscan_dom2 τ' Hstat_None).
      - (* scan_map_l_bounded: scan_map updated at τ to (range_z2_nat, 0).
           range_z2_nat = Z.to_nat (back_val2 `min` sz) ≤ back_val2. *)
        intros τ_p l j Hscan_τ_p.
        destruct (decide (τ_p = τ)) as [-> | Hne_τp].
        + rewrite lookup_insert_eq in Hscan_τ_p.
          injection Hscan_τ_p as <- _.
          unfold range_z2_nat. rewrite Z2Nat.id; [|apply Z.min_glb; [lia|exact Hsz_nn]].
          apply Z.le_min_l.
        + rewrite lookup_insert_ne in Hscan_τ_p;
            last (intros ?; apply Hne_τp; congruence).
          exact (Hscan_lb2 τ_p l j Hscan_τ_p). }
    wp_pures.
    wp_apply minimum_spec.
    wp_pures.

    remember (back_val2 `min` sz)%Z as range_z eqn:Hrange_z.
    assert (Hrange_le_sz : (range_z ≤ sz)%Z).
    { subst range_z. apply Z.le_min_r. }
    assert (Hrange_pos : (0 ≤ range_z)%Z).
    { subst range_z. apply Z.min_glb; [exact Hbpos2 | exact Hsz_nn]. }
    assert (Hrange_z_eq : range_z2_nat = Z.to_nat range_z).
    { unfold range_z2_nat. by rewrite Hrange_z. }
    clear Hrange_z.

    (* ──────────────────────────────────────────────────────────────────
       Phase 3 — inner Löb on [dequeue_aux dequeue q range_z i].
       i decreases from range_z down to 0; j = range_z - i is the slot
       being scanned. At i=0 we recurse via IH_outer.
       scan_map[τ] is parameterized by j_scan reflecting current scan position.
       ──────────────────────────────────────────────────────────────── *)
    iAssert (∀ (i_iter : Z) (j_scan : nat),
              ⌜(0 ≤ i_iter ≤ range_z)%Z⌝ -∗
              ⌜Z.of_nat j_scan = (range_z - i_iter)%Z⌝ -∗
              τ ↪[γ_status] OpDeqPending -∗
              τ ↪[γ_scan] (Z.to_nat range_z, j_scan) -∗
              (∀ v : val, True -∗ Φ v) -∗
              WP (dequeue_aux dequeue (#sz, #ar, #back)%V #range_z #i_iter)%E
                {{ (v_ret : val),
                   WP (let: "res" := InjR v_ret in
                       trace_emit #tracer #(Z.pos τ) (InjR "res");; "res")%E
                   {{ (v' : val), Φ v' }} }})%I
      as "Hloop"; last first.
    { iSpecialize ("Hloop" $! range_z 0%nat with "[%] [%] Hstat_τ [Hscan_τ] HΦ");
        [lia | lia | by rewrite -Hrange_z_eq | iApply "Hloop"]. }
    iIntros (i_iter j_scan).
    iLöb as "IH_inner" forall (i_iter j_scan).
    iIntros (Hi_bounds Hj_scan_eq) "Hstat_τ Hscan_τ HΦ".

    wp_lam. wp_pures.

    (* Phase 3(a): if [i_iter = 0], tail-call into [dequeue]. Use [IH_outer].
       At outer Löb re-entry, scan_map[τ] holds (range_z, j_scan); IH_outer
       expects (0, 0). We discard the held value with a `iLöb`-style outer
       refresh: re-enter outer Löb which IMMEDIATELY does the Phase 2 update
       to (range_z_new, 0). Since the Phase 2 outer iInv overwrites whatever
       value scan_map[τ] has, we can pass the held value as the "init". *)
    case_bool_decide as Hi_zero.
    { wp_pures.
      iApply ("IH_outer" $! (Z.to_nat range_z) j_scan with "Hstat_τ Hscan_τ HΦ"). }
    wp_pures.

    (* Phase 3(b): compute j = range_z - i_iter, load ar[j]. *)
    assert (Hi_nz : (i_iter ≠ 0)%Z).
    { intros ->. apply Hi_zero. reflexivity. }
    pose (j := (range_z - i_iter)%Z).
    assert (Hj_bounds : (0 ≤ j ∧ j < range_z)%Z).
    { unfold j. split; lia. }
    wp_bind (! _)%E.
    iInv "Hinv" as (items3 back_val3 ts3 M_g3 stat3 slots3 scan_map3)
      "(>Hback & >Har & >Hts & >%Hlen3 & >%Hbpos3 & >HγM & >Hstat & >Hslots & >Hscan & #Hslots_persist3 &
         >%Hmcfg_steps3 & >%Hne3 & >%Hpw3 & >%Hsc3 & >%Hsc_slots3 & >%Hwell3 & >%Htrst3 & >%Hlinw_seq3 & >%Hbnd3 & >%Hssi3 & >%Hcl_push3 & >%Hscan_dom3 & >%Hscan_lb3)".
    (* Load at offset j requires j < length items3 = Z.to_nat sz. *)
    assert (Hj_lt_items : (Z.to_nat j < length items3)%nat).
    { rewrite Hlen3. lia. }
    apply lookup_lt_is_Some in Hj_lt_items as [a_j Hj_eq].
    replace (range_z - i_iter)%Z with (Z.of_nat (Z.to_nat j)) by (unfold j; lia).
    wp_apply (wp_load_offset _ _ _ _ (Z.to_nat j) _ _ with "Har") as "Har";
      first exact Hj_eq.
    (* TLA+ alignment (D3 atomic split):
       - The LOAD of arr[j] itself does not advance scan_map[τ].
       - The case-split on a_j (NONEV vs. SOMEV) is performed WHILE the
         invariant is still open. In the NONEV branch, we bump scan_map[τ]
         := (range_z, S j) — corresponding to TLA+ D3 NONEV where j[p] :=
         j[p]+1 with M unchanged. In the SOMEV branch, scan_map[τ] remains
         (range_z, j_scan), and the Phase 4 CAS performs the LP'd-Pop
         extension of M — corresponding to TLA+ D3 SOMEV where j[p]
         is unchanged. *)
    iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ3.
    iDestruct (ghost_map_lookup with "Hscan Hscan_τ") as %Hscan_τ3_pre.
    (* Case-split on a_j inside the open invariant. *)
    assert (Ha_j : a_j = NONEV ∨ ∃ w, a_j = SOMEV w ∧ val_is_unboxed (SOMEV w)).
    { eapply (Forall_lookup_1 _ items3 (Z.to_nat j) a_j Hwell3 Hj_eq). }
    destruct Ha_j as [-> | (w & -> & Hw_unb)].
    { (* a_j = NONEV: TLA+ D3 NONEV step.
         items3[j] = NONEV (= Hj_eq).
         Update scan_map[τ] := (range_z, S j); M_g unchanged.
         By IH_inner invariant Hj_scan_eq, j_scan = Z.to_nat j, so the
         widening is from (range_z, j_scan) to (range_z, S j_scan). *)
      assert (Hjscan_eq_j_nat : j_scan = Z.to_nat j).
      { unfold j. rewrite -Hj_scan_eq. by rewrite Nat2Z.id. }
      iMod (ghost_map_update (Z.to_nat range_z, Nat.succ (Z.to_nat j))
              with "Hscan Hscan_τ") as "[Hscan Hscan_τ]".
      iModIntro.
      iSplitR "HΦ Hstat_τ Hscan_τ".
      { iNext. iExists items3, back_val3, ts3, M_g3, stat3, slots3,
                       (<[τ:=(Z.to_nat range_z, Nat.succ (Z.to_nat j))]> scan_map3).
        iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist3".
        iPureIntro. split_and!; try assumption.
        - rewrite Hjscan_eq_j_nat in Hscan_τ3_pre.
          eapply lin_witness_seq_widen_τ_scan_nonev;
            [exact Hscan_τ3_pre | exact Hj_eq | exact Hssi3 | exact Hlinw_seq3].
        - intros τ' Hstat_None.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          + rewrite Hstat_τ3 in Hstat_None. discriminate.
          + rewrite lookup_insert_ne;
              last (intros ?; apply Hne_τ'; congruence).
            apply (Hscan_dom3 τ' Hstat_None).
        - (* scan_map_l_bounded: only j component updated, l unchanged. *)
          intros τ_p l_p j_p Hscan_τ_p.
          destruct (decide (τ_p = τ)) as [-> | Hne_τp].
          + rewrite lookup_insert_eq in Hscan_τ_p.
            injection Hscan_τ_p as <- _.
            exact (Hscan_lb3 τ (Z.to_nat range_z) j_scan Hscan_τ3_pre).
          + rewrite lookup_insert_ne in Hscan_τ_p;
              last (intros ?; apply Hne_τp; congruence).
            exact (Hscan_lb3 τ_p l_p j_p Hscan_τ_p). }
      wp_pures.
      iApply ("IH_inner" $! (i_iter - 1)%Z (Nat.succ (Z.to_nat j))
                with "[%] [%] Hstat_τ Hscan_τ HΦ").
      { lia. }
      { destruct Hj_bounds as [Hj_ge _].
        rewrite Nat2Z.inj_succ Z2Nat.id; last exact Hj_ge.
        unfold j. lia. } }
    (* a_j = SOMEV w (= InjRV w): TLA+ D3 SOMEV step — close invariant
       WITHOUT updating scan_map. The Phase 4 CAS will perform the
       LP'd-Pop extension of M_g.

       Before closing, extract a PERSISTENT fragment for slot j with value w
       from Hslots_persist3. This fragment will be used at Phase 4 CAS-FAIL
       to derive items4[j] = NONEV (the slot must have been popped). *)
    assert (Hslot_j3 : slots3 !! Z.to_nat j = Some w).
    { destruct Hsc_slots3 as [_ Hsc_dir2]. apply (Hsc_dir2 (Z.to_nat j) w).
      exact Hj_eq. }
    iDestruct (big_sepM_lookup with "Hslots_persist3") as "#Hslot_j_persist";
      first exact Hslot_j3.
    iModIntro.
    iSplitR "HΦ Hstat_τ Hscan_τ".
    { iNext. iExists items3, back_val3, ts3, M_g3, stat3, slots3, scan_map3.
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist3".
      iPureIntro. split_and!; assumption. }
    set (v_right := w).
    assert (Hsomev_unb : val_is_unboxed (InjRV v_right)) by exact Hw_unb.
    (* a_j = InjRV v_right: SOMEV v_right branch. CmpXchg with NONE. *)
    wp_pures.

    (* ──────────────────────────────────────────────────────────────────
       Phase 4 — CmpXchg ar[j] (SOME v_right) NONE.
       On success: LINEARIZATION POINT for this pop.
       On failure: recurse via IH_inner.
       ──────────────────────────────────────────────────────────────── *)
    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as (items4 back_val4 ts4 M_g4 stat4 slots4 scan_map4)
      "(>Hback & >Har & >Hts & >%Hlen4 & >%Hbpos4 & >HγM & >Hstat & >Hslots & >Hscan & #Hslots_persist4 &
         >%Hmcfg_steps4 & >%Hne4 & >%Hpw4 & >%Hsc4 & >%Hsc_slots4 & >%Hwell4 & >%Htrst4 & >%Hlinw_seq4 & >%Hbnd4 & >%Hssi4 & >%Hcl_push4 & >%Hscan_dom4 & >%Hscan_lb4)".
    assert (Hj_lt_items4 : (Z.to_nat j < length items4)%nat).
    { rewrite Hlen4. lia. }
    apply lookup_lt_is_Some in Hj_lt_items4 as [a_j' Hj_eq4].
    (* CmpXchg semantics: compare with InjRV v_right; on equal, store NONEV. *)
    destruct (decide (a_j' = InjRV v_right)) as [-> | Hne_aj'].
    + (* ────────────────────────────────────────────────────────────────
         CmpXchg succeeds: a_j' was InjRV v_right.
         THIS IS THE LINEARIZATION POINT for the dequeue (τ, Pop).
         The dequeued value is v_right.
         ────────────────────────────────────────────────────────────── *)
      wp_apply (wp_cmpxchg_suc_offset _ _ _ (Z.to_nat j) _ _ _ (InjLV #()) with "Har")
        as "Har"; [exact Hj_eq4 | reflexivity | by left |].
      iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ4.
      iDestruct (ghost_map_lookup with "Hscan Hscan_τ") as %Hscan_τ4.
      (* Hscan_τ4 : scan_map4 !! τ = Some (Z.to_nat range_z, j_scan).
         By the IH_inner invariant Hj_scan_eq, j_scan = Z.to_nat j (= the
         slot just loaded in Phase 3). Per the relaxed `pop_universal_v_at_head`
         premise (j ≤ j_p and j < l), this guarantees a witness config in
         M_g4 with v_right at the HEAD of the state. *)
      (* Step 1: From slots_consistent and items4[j] = SOMEV v_right,
         derive slots4 !! j = Some v_right (the slot was written by some
         prior enqueue). *)
      assert (Hslot_j : slots4 !! Z.to_nat j = Some v_right).
      { destruct Hsc_slots4 as [_ Hsc_dir2].
        apply (Hsc_dir2 (Z.to_nat j) v_right). exact Hj_eq4. }
      (* Step 2: Derive pop_universal_v_at_head locally via the derivation
         lemma from slots_consistent + lin_witness_seq.
         TLA+ alignment: at Phase 4 CAS LP (D3 SOMEV), scan_map[τ] =
         (range_z, j_scan) with j_scan = j (the LP target slot), so the
         v-at-head witness exists by JInvSeq-driven Inv_Main. *)
      pose proof (pop_universal_v_at_head_derive M_g4 items4 slots4 stat4 scan_map4
                    Hsc_slots4 Hlinw_seq4) as Hpop_vhead4.
      assert (Hj_scan_eq_nat : j_scan = Z.to_nat j).
      { unfold j. rewrite -Hj_scan_eq. by rewrite Nat2Z.id. }
      assert (Hj_le_jscan : (Z.to_nat j ≤ j_scan)%nat).
      { rewrite Hj_scan_eq_nat. lia. }
      assert (Hj_lt_range : (Z.to_nat j < Z.to_nat range_z)%nat).
      { destruct Hj_bounds as [Hj_ge_zero Hj_lt_range_Z].
        apply Z2Nat.inj_lt; lia. }
      destruct (Hpop_vhead4 (Z.to_nat j) v_right τ
                  (Z.to_nat range_z) j_scan
                  Hslot_j Hj_eq4 Hstat_τ4 Hscan_τ4 Hj_le_jscan Hj_lt_range)
        as (s_tail & π_pick & Hpick_in_full & Hπ_pick_τ &
            Henq_pick & Hlin_pick & Hdone_pick & Hpending_pick & Hstored_lin_pick).
      set (s_pick := v_right :: s_tail).
      assert (Hs_pick : s_pick = v_right :: s_tail) by reflexivity.
      assert (Hpick_in : (s_pick, π_pick) ∈ M_g4) by exact Hpick_in_full.
      (* Step 3: TLA+ D3 SOMEV — extend M_g4 with ALL LP'd-Pop versions for
         the head value v_right. For each (v_right :: s_t, π) ∈ M_g4 with
         π[τ] = (Pop, None), add (s_t, <[τ:=LP'd Pop NE v_right]>π) to
         M_g4_new. This subsumes the singleton from pop_universal_v_at_head
         and matches the set-valued D3 SOMEV semantics. *)
      pose (π_new := <[τ:=(Pop, #(),
                            Some (encode_response (NonEmpty v_right)))]> π_pick).
      pose (M_g4_LP_pop_vright :=
        set_omap (λ cfg : single_config_q,
          match cfg.1 with
          | v_h' :: s_t =>
              if decide (v_h' = v_right ∧
                         cfg.2 !! τ = Some (Pop, #(), None))
              then Some (s_t,
                         <[τ:=(Pop, #(),
                                Some (encode_response (NonEmpty v_right)))]>cfg.2)
              else None
          | [] => None
          end) M_g4 : gset single_config_q).
      pose (M_g4_new := (M_g4 ∪ M_g4_LP_pop_vright : gset single_config_q)).
      assert (Hπ_new_in_LP : (s_tail, π_new) ∈ M_g4_LP_pop_vright).
      { unfold M_g4_LP_pop_vright. apply elem_of_set_omap.
        exists (s_pick, π_pick). split; first exact Hpick_in.
        rewrite Hs_pick. simpl.
        rewrite decide_True; last by split; [reflexivity | exact Hπ_pick_τ].
        unfold π_new. reflexivity. }
      (* Helper: any element of M_g4_LP_pop_vright is an LP'd image of
         some config in M_g4. *)
      assert (HLP_inv : ∀ x : single_config_q,
                x ∈ M_g4_LP_pop_vright →
                ∃ s_t π_orig,
                  x = (s_t, <[τ:=(Pop, #(),
                                   Some (encode_response (NonEmpty v_right)))]>π_orig) ∧
                  (v_right :: s_t, π_orig) ∈ M_g4 ∧
                  π_orig !! τ = Some (Pop, #(), None)).
      { intros x Hx. unfold M_g4_LP_pop_vright in Hx.
        apply elem_of_set_omap in Hx as (cfg & Hcfg_in & Hcfg_eq).
        destruct cfg as [s_cfg π_cfg]. simpl in Hcfg_eq.
        destruct s_cfg as [|v_h' s_t]; first by inversion Hcfg_eq.
        case_decide as Hcond; last by inversion Hcfg_eq.
        destruct Hcond as [Heq_vh Hπcfg_τ].
        injection Hcfg_eq as Heq_x.
        exists s_t, π_cfg. split_and!.
        - symmetry. exact Heq_x.
        - subst v_h'. exact Hcfg_in.
        - exact Hπcfg_τ. }
      iMod (ghost_var_update M_g4_new with "HγM") as "HγM".
      iMod (ghost_map_update (OpDeqLinearized v_right) with "Hstat Hstat_τ")
        as "[Hstat Hstat_τ]".
      (* Step 4: We leave slots unchanged; slots_consistent allows
         slots[i] = Some v with items[i] = NONEV (slot already popped). *)
      iModIntro.
      iSplitR "HΦ Hstat_τ Hscan_τ".
      { iNext.
        iExists (<[Z.to_nat j := InjLV #()]> items4),
                back_val4, ts4, M_g4_new,
                (<[τ:=OpDeqLinearized v_right]> stat4),
                slots4, scan_map4.
        iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist4".
        iPureIntro. split_and!.
        - rewrite length_insert. exact Hlen4.
        - exact Hbpos4.
        - (* mcfg_steps: chain mcfg_step_interm for each (v_right :: s_t, π) ∈ M_g4
             with π[τ] = Pending Pop. The helper lemma constructs the chain. *)
          replace ts4 with (ts4 ++ []) by by rewrite app_nil_r.
          eapply rtcL_trans; first exact Hmcfg_steps4.
          destruct (mcfg_steps_chain_lp_pop_at_head
                      (set_to_propset M_g4) M_g4 τ v_right (reflexivity _))
            as (M_full' & Hsteps_chain & Hsubset_chain & Hwit_chain & Hupper_chain).
          (* Show set_to_propset M_g4_new = M_full'. *)
          assert (Hpset_eq : (set_to_propset M_g4_new : @meta_config hwq_model)
                             = M_full').
          { apply leibniz_equiv. intros y. split.
            - intros Hy_new.
              rewrite elem_of_set_to_propset in Hy_new.
              unfold M_g4_new in Hy_new.
              apply elem_of_union in Hy_new as [Hy_g | Hy_lp].
              + apply Hsubset_chain. rewrite elem_of_set_to_propset. exact Hy_g.
              + destruct (HLP_inv y Hy_lp) as
                  (s_t & π_orig & -> & Hin_orig & Hπτ_orig).
                apply (Hwit_chain s_t π_orig Hin_orig Hπτ_orig).
            - intros Hy_full.
              destruct (Hupper_chain y Hy_full) as
                [Hy_in_g | (s_t & π_orig & Hin_orig & Hπτ_orig & ->)].
              + rewrite elem_of_set_to_propset in Hy_in_g.
                rewrite elem_of_set_to_propset.
                unfold M_g4_new. apply elem_of_union. left. exact Hy_in_g.
              + rewrite elem_of_set_to_propset.
                unfold M_g4_new. apply elem_of_union. right.
                unfold M_g4_LP_pop_vright. apply elem_of_set_omap.
                exists (v_right :: s_t, π_orig). split; first exact Hin_orig.
                simpl. rewrite decide_True;
                  last by split; [reflexivity | exact Hπτ_orig].
                reflexivity. }
          rewrite Hpset_eq. exact Hsteps_chain.
        - (* non-empty: M_g4_new ⊇ M_g4 (which is non-empty). *)
          unfold M_g4_new. intros Heq_empty.
          apply Hne4. clear -Heq_empty. set_solver.
        - exact Hpw4.
        - (* stat_consistent: τ has OpDeqLinearized (existential — the new
             config provides the witness); other τ's preserved. *)
          intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
          + rewrite lookup_insert_eq.
            (* Existential: provide (s_tail, π_new) as the witness. *)
            exists s_tail, π_new. split.
            * unfold M_g4_new. apply elem_of_union. right. exact Hπ_new_in_LP.
            * unfold π_new. rewrite lookup_insert_eq. reflexivity.
          + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
            pose proof (Hsc4 τ') as Hsc_τ'.
            (* Helper: for any (s', π') ∈ M_g4_new, ∃ (s_M, π_M) ∈ M_g4 with
               π'[τ'] = π_M[τ'] (for τ' ≠ τ). *)
            assert (Hlift_τ' : ∀ s' π', (s', π') ∈ M_g4_new →
                       ∃ s_M π_M, (s_M, π_M) ∈ M_g4 ∧ π' !! τ' = π_M !! τ').
            { intros s' π' Hin. unfold M_g4_new in Hin.
              apply elem_of_union in Hin as [Hin_g | Hin_lp].
              - exists s', π'. split; [exact Hin_g | reflexivity].
              - destruct (HLP_inv (s', π') Hin_lp) as
                  (s_t & π_orig & Heq_x & Hin_orig & Hπ_orig_τ).
                injection Heq_x as -> ->.
                exists (v_right :: s_t), π_orig. split; first exact Hin_orig.
                rewrite lookup_insert_ne; first reflexivity.
                intros ?; apply Hne_τ; congruence. }
            destruct (stat4 !! τ') as [s_op|] eqn:Hlk.
            * destruct s_op; simpl in Hsc_τ'.
              -- (* OpEnqPending v0 *)
                 intros s' π' Hin.
                 destruct (Hlift_τ' s' π' Hin) as (s_M & π_M & Hin_M & Hπ_eq).
                 rewrite Hπ_eq. exact (Hsc_τ' s_M π_M Hin_M).
              -- (* OpEnqReserved v0 n — conj. *)
                 destruct Hsc_τ' as [Hsc_all Hsc_ex].
                 split.
                 { intros s' π' Hin.
                   destruct (Hlift_τ' s' π' Hin) as (s_M & π_M & Hin_M & Hπ_eq).
                   rewrite Hπ_eq. exact (Hsc_all s_M π_M Hin_M). }
                 destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
                 exists s_v, π_v. split; last exact Hπ_v.
                 unfold M_g4_new. apply elem_of_union. left. exact Hin_v.
              -- (* OpEnqStored v0 n — conj. *)
                 destruct Hsc_τ' as [Hsc_all Hsc_ex].
                 split.
                 { intros s' π' Hin.
                   destruct (Hlift_τ' s' π' Hin) as (s_M & π_M & Hin_M & Hπ_eq).
                   rewrite Hπ_eq. exact (Hsc_all s_M π_M Hin_M). }
                 destruct Hsc_ex as (s_v & π_v & Hin_v & Hπ_v).
                 exists s_v, π_v. split; last exact Hπ_v.
                 unfold M_g4_new. apply elem_of_union. left. exact Hin_v.
              -- (* OpEnqDone v0 *)
                 intros s' π' Hin.
                 destruct (Hlift_τ' s' π' Hin) as (s_M & π_M & Hin_M & Hπ_eq).
                 rewrite Hπ_eq. exact (Hsc_τ' s_M π_M Hin_M).
              -- (* OpDeqPending *)
                 intros s' π' Hin.
                 destruct (Hlift_τ' s' π' Hin) as (s_M & π_M & Hin_M & Hπ_eq).
                 rewrite Hπ_eq. exact (Hsc_τ' s_M π_M Hin_M).
              -- (* OpDeqLinearized v0 — existential, preserved as-is. *)
                 destruct Hsc_τ' as (s_w & π_w & Hin_w & Hπ_w).
                 exists s_w, π_w. split; last exact Hπ_w.
                 unfold M_g4_new. apply elem_of_union. left. exact Hin_w.
              -- (* OpDeqDone v0 *)
                 intros s' π' Hin.
                 destruct (Hlift_τ' s' π' Hin) as (s_M & π_M & Hin_M & Hπ_eq).
                 rewrite Hπ_eq. exact (Hsc_τ' s_M π_M Hin_M).
            * (* None case *)
              simpl in Hsc_τ'.
              intros s' π' Hin.
              destruct (Hlift_τ' s' π' Hin) as (s_M & π_M & Hin_M & Hπ_eq).
              rewrite Hπ_eq. exact (Hsc_τ' s_M π_M Hin_M).
        - (* slots_consistent preservation under store NONEV at j. *)
          destruct Hsc_slots4 as [Hsc_dir1 Hsc_dir2]. split.
          + intros i v Hlk.
            specialize (Hsc_dir1 i v Hlk) as [Hlt Hcase].
            rewrite length_insert. split; first exact Hlt.
            destruct (decide (i = Z.to_nat j)) as [-> | Hne_i].
            * right. rewrite list_lookup_insert_eq; first reflexivity.
              rewrite Hlen4. lia.
            * rewrite list_lookup_insert_ne; last done. exact Hcase.
          + intros i v Hlk.
            destruct (decide (i = Z.to_nat j)) as [-> | Hne_i].
            * rewrite list_lookup_insert_eq in Hlk; last by rewrite Hlen4; lia.
              discriminate.
            * rewrite list_lookup_insert_ne in Hlk; last done.
              apply (Hsc_dir2 i v Hlk).
        - (* items_well_shaped: insert NONEV at j. *)
          apply Forall_insert; first exact Hwell4. left. reflexivity.
        - (* trace_stat_consistent: insert τ → OpDeqLinearized v_right.
             ts unchanged; OpDeqLinearized has same trace as OpDeqPending. *)
          intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
          + rewrite lookup_insert_eq.
            pose proof (Htrst4 τ) as Htrst_τ. rewrite Hstat_τ4 in Htrst_τ.
            exact Htrst_τ.
          + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
            exact (Htrst4 τ').
        - intros A seq HgoodA HnodupSeq Hsetof HJInvSeq.
          (* j ∉ A by NEW GoodEnqSet: items_new[j] = NONEV. The OpEnqReserved
             fallback also requires no τ_e at OpEnqReserved with i_e = j; since
             stat_new[τ] = OpDeqLinearized and stat4 maps to OpDeqPending pre-LP
             (not Reserved), and other τ_e at Reserved would conflict with slots[j] = v_right
             via slots_stat_iff. *)
          assert (Hj_not_in_A : Z.to_nat j ∉ A).
          { intros Hin.
            destruct HgoodA as [_ Hgood2].
            destruct (Hgood2 _ Hin) as [(v & Hv_eq) | (τ_e & v_e & Hres_e)].
            - rewrite list_lookup_insert_eq in Hv_eq;
                last (rewrite Hlen4; lia).
              discriminate.
            - (* OpEnqReserved at j: contradicts slots_stat_iff via slots[j] = Some v_right. *)
              destruct (decide (τ_e = τ)) as [-> | Hne_τe].
              + rewrite lookup_insert_eq in Hres_e. discriminate.
              + rewrite lookup_insert_ne in Hres_e;
                  last (intros ?; apply Hne_τe; congruence).
                destruct Hssi4 as (_ & Hssi_b4 & Hssi_c4 & _).
                destruct (Hssi_b4 (Z.to_nat j) v_right Hslot_j) as (τ_w & Hown_w).
                assert (τ_w = τ_e) as ->.
                { apply (Hssi_c4 τ_w τ_e v_right v_e (Z.to_nat j)).
                  - destruct Hown_w as [Hs | Hs].
                    + right. left. exact Hs.
                    + right. right. exact Hs.
                  - left. exact Hres_e. }
                destruct Hown_w as [Hs | Hs]; rewrite Hres_e in Hs; discriminate. }
          (* Build A_old = A ∪ {j}, seq_old = j :: seq. *)
          pose (A_old := A ∪ {[Z.to_nat j]}).
          pose (seq_old := Z.to_nat j :: seq).
          (* OLD GoodEnqSet(A_old, items4, stat4). *)
          assert (HgoodA_old : GoodEnqSet A_old items4 stat4).
          { destruct HgoodA as [Hgood1 Hgood2]. split.
            - intros k v Hitem_k.
              destruct (decide (k = Z.to_nat j)) as [-> | Hne_k].
              + rewrite Hj_eq4 in Hitem_k. injection Hitem_k as ->.
                unfold A_old. clear. set_solver.
              + assert (Hitem_new_k : (<[Z.to_nat j := InjLV #()]> items4) !! k =
                                       Some (SOMEV v)).
                { rewrite list_lookup_insert_ne; done. }
                pose proof (Hgood1 k v Hitem_new_k) as HinA.
                unfold A_old. clear -HinA. set_solver.
            - intros k Hin_A_old.
              unfold A_old in Hin_A_old.
              apply elem_of_union in Hin_A_old as [HinA | Heq_j].
              + destruct (Hgood2 k HinA) as [(v & Hv_eq) | (τ_e & v_e & Hres_e)].
                * left. exists v. destruct (decide (k = Z.to_nat j)) as [-> | Hne_k].
                  -- exfalso. apply Hj_not_in_A. exact HinA.
                  -- rewrite list_lookup_insert_ne in Hv_eq; done.
                * right. destruct (decide (τ_e = τ)) as [-> | Hne_τe].
                  -- rewrite lookup_insert_eq in Hres_e. discriminate.
                  -- exists τ_e, v_e. rewrite lookup_insert_ne in Hres_e;
                       last (intros ?; apply Hne_τe; congruence). exact Hres_e.
              + apply elem_of_singleton in Heq_j. subst k.
                left. exists v_right. exact Hj_eq4. }
          (* NoDup seq_old. *)
          assert (Hnodup_old : NoDup seq_old).
          { unfold seq_old. apply NoDup_cons. split; last exact HnodupSeq.
            intros Hin. apply Hj_not_in_A.
            rewrite -Hsetof. apply elem_of_list_to_set. exact Hin. }
          (* list_to_set seq_old = A_old. *)
          assert (Hsetof_old : list_to_set seq_old = A_old).
          { unfold seq_old, A_old. simpl. rewrite Hsetof. clear. set_solver. }
          (* OLD JInvSeq(seq_old, slots4, stat4, scan_map4). *)
          assert (HJInvSeq_old : JInvSeq seq_old slots4 stat4 scan_map4).
          { intros n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km.
            unfold seq_old in Hseq_n, Hseq_m.
            destruct n as [|n'].
            - simpl in Hseq_n. injection Hseq_n as Heq_kn. subst k_n.
              destruct m as [|m']; first lia.
              simpl in Hseq_m.
              exists τ, (Z.to_nat range_z), j_scan.
              split_and!.
              + exact Hstat_τ4.
              + exact Hscan_τ4.
              + exact Hj_lt_range.
              + rewrite Hj_scan_eq_nat. lia.
            - destruct m as [|m']; first lia.
              simpl in Hseq_n, Hseq_m.
              apply Nat.succ_lt_mono in Hn_lt_m.
              destruct (HJInvSeq n' m' k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km)
                as (τ_d & l & j_d & Hstat_d & Hscan_d & Hkl & Hkj).
              destruct (decide (τ_d = τ)) as [-> | Hne_τd].
              + rewrite lookup_insert_eq in Hstat_d. discriminate.
              + exists τ_d, l, j_d. split_and!; try assumption.
                rewrite lookup_insert_ne in Hstat_d;
                  last (intros ?; apply Hne_τd; congruence).
                exact Hstat_d. }
          (* Apply Hlinw_seq4. *)
          destruct (Hlinw_seq4 A_old seq_old HgoodA_old Hnodup_old Hsetof_old
                      HJInvSeq_old)
            as (s_q & π_q & Hin_q & Hlen_q & Hsmatch_q & Hsmatch_case_q & Henq_q
                & Hlin_q & Hdone_q & Hpending_q & Hstored_q & Hres_q).
          (* s_q has length |seq_old| = |seq| + 1, and s_q[0] = slots4[j] = v_right. *)
          assert (Hs_q_first : s_q !! 0 = Some v_right).
          { eapply Hsmatch_q.
            - unfold seq_old. reflexivity.
            - exact Hslot_j. }
          destruct s_q as [| v_h s_q_tail]; first by inversion Hs_q_first.
          simpl in Hs_q_first. injection Hs_q_first as ->.
          (* By Hpending_q applied to τ at OpDeqPending: π_q[τ] = (Pop, None). *)
          pose proof (Hpending_q τ Hstat_τ4) as Hπ_q_τ.
          pose (π_q_new := <[τ:=(Pop, #(),
                                  Some (encode_response (NonEmpty v_right)))]> π_q).
          assert (Hin_lp : (s_q_tail, π_q_new) ∈ M_g4_LP_pop_vright).
          { unfold M_g4_LP_pop_vright. apply elem_of_set_omap.
            exists (v_right :: s_q_tail, π_q). split; first exact Hin_q.
            simpl. rewrite decide_True;
              last by split; [reflexivity | exact Hπ_q_τ].
            unfold π_q_new. reflexivity. }
          exists s_q_tail, π_q_new. split_and!.
          + unfold M_g4_new. apply elem_of_union. right. exact Hin_lp.
          + (* length s_q_tail = length seq. *)
            simpl in Hlen_q. unfold seq_old in Hlen_q. simpl in Hlen_q.
            lia.
          + (* s_q_tail matches seq under slots4. *)
            intros n k Hseq_n v Hslot_k.
            (* seq_old[n+1] = seq[n], s_q[n+1] = slots4[seq_old[n+1]] = slots4[seq[n]]. *)
            specialize (Hsmatch_q (Nat.succ n) k).
            assert (Hseq_old_n : seq_old !! (Nat.succ n) = Some k).
            { unfold seq_old. simpl. exact Hseq_n. }
            specialize (Hsmatch_q Hseq_old_n v Hslot_k).
            simpl in Hsmatch_q. exact Hsmatch_q.
          + (* TLA+ items+stat case match — for items_new (= items4 with j→NONEV)
               and stat_new (= stat4 with τ→OpDeqLinearized). *)
            intros n k Hseq_n.
            assert (Hseq_old_n : seq_old !! (Nat.succ n) = Some k).
            { unfold seq_old. simpl. exact Hseq_n. }
            destruct (Hsmatch_case_q (Nat.succ n) k Hseq_old_n) as
              [(v0 & Hitem & Hs) | (τ_e & v_e & Hres & Hs)].
            * left. exists v0. split; last by simpl in Hs.
              (* k ≠ j since k ∈ seq (and j ∉ seq). *)
              assert (Hk_ne_j : k ≠ Z.to_nat j).
              { intros ->. apply Hj_not_in_A.
                rewrite -Hsetof. apply elem_of_list_to_set.
                apply list_elem_of_lookup_2 with n. exact Hseq_n. }
              rewrite list_lookup_insert_ne; done.
            * right. exists τ_e, v_e. split; last by simpl in Hs.
              destruct (decide (τ_e = τ)) as [-> | Hne_τe].
              -- rewrite Hstat_τ4 in Hres. discriminate.
              -- rewrite lookup_insert_ne;
                   last (intros ?; apply Hne_τe; congruence).
                 exact Hres.
          + (* OpEnqDone case. *)
            intros τ_d v_d i_d Hstat_d_new.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            * rewrite lookup_insert_ne in Hstat_d_new;
                last (intros ?; apply Hne_τd; congruence).
              unfold π_q_new. rewrite lookup_insert_ne;
                last (intros ?; apply Hne_τd; congruence).
              exact (Henq_q τ_d v_d i_d Hstat_d_new).
          + (* OpDeqLinearized case. *)
            intros τ_d v_d Hstat_d_new.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            * unfold π_q_new. rewrite lookup_insert_eq.
              rewrite lookup_insert_eq in Hstat_d_new.
              injection Hstat_d_new as ->. reflexivity.
            * rewrite lookup_insert_ne in Hstat_d_new;
                last (intros ?; apply Hne_τd; congruence).
              unfold π_q_new. rewrite lookup_insert_ne;
                last (intros ?; apply Hne_τd; congruence).
              exact (Hlin_q τ_d v_d Hstat_d_new).
          + (* OpDeqDone case. *)
            intros τ_d v_d Hstat_d_new.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            * rewrite lookup_insert_ne in Hstat_d_new;
                last (intros ?; apply Hne_τd; congruence).
              unfold π_q_new. rewrite lookup_insert_ne;
                last (intros ?; apply Hne_τd; congruence).
              exact (Hdone_q τ_d v_d Hstat_d_new).
          + (* OpDeqPending case. *)
            intros τ_d Hstat_d_new.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            * rewrite lookup_insert_eq in Hstat_d_new. discriminate.
            * rewrite lookup_insert_ne in Hstat_d_new;
                last (intros ?; apply Hne_τd; congruence).
              unfold π_q_new. rewrite lookup_insert_ne;
                last (intros ?; apply Hne_τd; congruence).
              exact (Hpending_q τ_d Hstat_d_new).
          + (* OpEnqStored case. *)
            intros τ_e v_e i_e Hstat_e_new.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            * rewrite lookup_insert_eq in Hstat_e_new. discriminate.
            * rewrite lookup_insert_ne in Hstat_e_new;
                last (intros ?; apply Hne_τe; congruence).
              unfold π_q_new. rewrite lookup_insert_ne;
                last (intros ?; apply Hne_τe; congruence).
              exact (Hstored_q τ_e v_e i_e Hstat_e_new).
          + (* OpEnqReserved case. *)
            intros τ_e v_e i_e Hres_e_new.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            * rewrite lookup_insert_eq in Hres_e_new. discriminate.
            * rewrite lookup_insert_ne in Hres_e_new;
                last (intros ?; apply Hne_τe; congruence).
              destruct (Hres_q τ_e v_e i_e Hres_e_new) as [HLP Hdisj].
              split.
              -- intros HinA. unfold π_q_new. rewrite lookup_insert_ne;
                   last (intros ?; apply Hne_τe; congruence).
                 apply HLP. unfold A_old. clear -HinA. set_solver.
              -- intros HninA. unfold π_q_new. rewrite lookup_insert_ne;
                   last (intros ?; apply Hne_τe; congruence).
                 destruct (decide (i_e = Z.to_nat j)) as [-> | Hne_ie].
                 ++ exfalso. (* i_e = j but stat τ_e = Reserved at j. By slots_stat_iff,
                                slot j is owned by τ_e (Stored/Done), but we have Reserved. Contradiction. *)
                    destruct Hssi4 as (_ & Hssi_b' & Hssi_c' & _).
                    destruct (Hssi_b' (Z.to_nat j) v_right Hslot_j) as (τ_w & Hown_w).
                    assert (τ_w = τ_e) as Heq_τw.
                    { apply (Hssi_c' τ_w τ_e v_right v_e (Z.to_nat j)).
                      - destruct Hown_w as [Hs | Hs].
                        + right. left. exact Hs.
                        + right. right. exact Hs.
                      - left. exact Hres_e_new. }
                    subst τ_w.
                    destruct Hown_w as [Hs | Hs]; rewrite Hres_e_new in Hs; discriminate.
                 ++ apply Hdisj. unfold A_old. intros [Hin1 | Hin2]%elem_of_union.
                    ** apply HninA. exact Hin1.
                    ** apply elem_of_singleton in Hin2. by apply Hne_ie.
        - (* slots_bounded: unchanged (slots4 unchanged). *)
          exact Hbnd4.
        - (* slots_stat_iff: stat τ → OpDeqLinearized, slots unchanged.
             stat4[τ] was OpDeqPending — not Reserved/Stored/Done — so
             the new τ entry can't satisfy any slot_stat_iff clause,
             only OTHER τ' contribute. *)
          destruct Hssi4 as (Hssi_a4 & Hssi_b4 & Hssi_c4 & Hssi_d4).
          unfold stat_owns, stat_faad.
          split_and!.
          + intros τ' v' i' Howns.
            destruct (decide (τ' = τ)) as [-> | Hne_τ'].
            * destruct Howns as [Howns | Howns];
                rewrite lookup_insert_eq in Howns; discriminate.
            * apply (Hssi_a4 τ' v' i').
              destruct Howns as [Howns | Howns];
                rewrite lookup_insert_ne in Howns;
                try (intros ?; apply Hne_τ'; congruence);
                [left | right]; exact Howns.
          + intros i' v' Hslot'.
            destruct (Hssi_b4 _ _ Hslot') as (τ_w & Hstat_w).
            exists τ_w. destruct (decide (τ_w = τ)) as [-> | Hne_τw].
            * exfalso. destruct Hstat_w as [Hstat_w | Hstat_w];
                rewrite Hstat_τ4 in Hstat_w; discriminate.
            * destruct Hstat_w as [Hstat_w | Hstat_w];
                [left | right];
                rewrite lookup_insert_ne;
                try (intros ?; apply Hne_τw; congruence);
                exact Hstat_w.
          + intros τ_1 τ_2 v_1 v_2 i' Hτ1 Hτ2.
            destruct (decide (τ_1 = τ)) as [-> | Hne_τ1];
              destruct (decide (τ_2 = τ)) as [-> | Hne_τ2].
            * reflexivity.
            * exfalso. destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                rewrite lookup_insert_eq in Hτ1; discriminate.
            * exfalso. destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                rewrite lookup_insert_eq in Hτ2; discriminate.
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
            * exfalso. destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
                rewrite lookup_insert_eq in Hstat'; discriminate.
            * assert (Hstat'_old : stat_faad stat4 τ' v' i').
              { destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
                  rewrite lookup_insert_ne in Hstat';
                  try (intros ?; apply Hne_τ'; congruence).
                - left. exact Hstat'.
                - right. left. exact Hstat'.
                - right. right. exact Hstat'. }
              exact (Hssi_d4 τ' v' i' Hstat'_old).
        - intros cfg puL Hin Hnd Hsubset Hstat_pushes.
          (* τ ∉ puL.*1: new stat[τ] = OpDeqLinearized, not Reserved/Stored. *)
          assert (Hτ_notin : τ ∉ puL.*1).
          { intros Hin_τ.
            apply list_elem_of_fmap_1 in Hin_τ as (pv & Heq_τ & Hpv_in).
            destruct (Hstat_pushes pv Hpv_in) as (v' & i' & [Hs | Hs]);
              rewrite -Heq_τ in Hs; rewrite lookup_insert_eq in Hs; discriminate. }
          (* stat_pushes on stat4 (drop new τ insertion). *)
          assert (Hstat_pushes_old : ∀ pv, pv ∈ puL → ∃ v i,
                    stat4 !! pv.1 = Some (OpEnqReserved v i) ∨
                    stat4 !! pv.1 = Some (OpEnqStored v i)).
          { intros pv Hpv_in. destruct (Hstat_pushes pv Hpv_in) as (v' & i' & Hstat').
            exists v', i'. assert (Hne_pv_τ : pv.1 ≠ τ).
            { intros Heq_pv. apply Hτ_notin.
              rewrite -Heq_pv. apply (list_elem_of_fmap_2 fst _ pv); exact Hpv_in. }
            destruct Hstat' as [Hs | Hs].
            - left. rewrite lookup_insert_ne in Hs;
                last (intros ?; apply Hne_pv_τ; congruence). exact Hs.
            - right. rewrite lookup_insert_ne in Hs;
                last (intros ?; apply Hne_pv_τ; congruence). exact Hs. }
          (* Case split on cfg ∈ M_g4 vs M_g4_LP_pop_vright. *)
          apply elem_of_union in Hin as [Hin4 | Hin_LP].
          + (* cfg ∈ M_g4: direct application of Hcl_push4. *)
            pose proof (Hcl_push4 cfg puL Hin4 Hnd Hsubset Hstat_pushes_old) as Hcl_x.
            apply elem_of_union_l. exact Hcl_x.
          + (* cfg ∈ M_g4_LP_pop_vright: cfg = (s_t, <[τ:=LP'd Pop]>π_orig). *)
            destruct (HLP_inv cfg Hin_LP) as (s_t & π_orig & Hcfg_eq & Hπorig_in & Hπorig_τ).
            subst cfg.
            (* Lift pushes ⊆ pending_push_of_config of LP'd-version
               to pending_push_of_config (v_right :: s_t, π_orig). *)
            assert (Hsub_orig : puL ⊆ pending_push_of_config (v_right :: s_t, π_orig)).
            { intros pv Hpv_in.
              specialize (Hsubset pv Hpv_in).
              unfold pending_push_of_config in Hsubset |- *.
              simpl in Hsubset |- *.
              apply list_elem_of_omap in Hsubset as ([τ' [req resp]] & Hin_list & Heq_pv).
              apply elem_of_map_to_list in Hin_list.
              destruct (decide (τ' = τ)) as [-> | Hne_τ'].
              - rewrite lookup_insert_eq in Hin_list.
                injection Hin_list as Hreq Hresp. subst req. subst resp.
                simpl in Heq_pv. discriminate.
              - rewrite lookup_insert_ne in Hin_list;
                  last (intros ?; apply Hne_τ'; congruence).
                apply list_elem_of_omap. exists (τ', (req, resp)). split.
                + apply elem_of_map_to_list. exact Hin_list.
                + exact Heq_pv. }
            (* Apply Hcl_push4 on (v_right :: s_t, π_orig) with puL. *)
            pose proof (Hcl_push4 (v_right :: s_t, π_orig) puL Hπorig_in Hnd Hsub_orig
                                  Hstat_pushes_old) as Hcl_orig.
            (* Hcl_orig: (v_right :: s_t ++ puL.*2, map_imap ... π_orig) ∈ M_g4. *)
            (* Add to M_g4_LP_pop_vright. *)
            apply elem_of_union_r.
            unfold M_g4_LP_pop_vright.
            apply elem_of_set_omap.
            exists (lineraize_pending_push puL (v_right :: s_t, π_orig)).
            split; first exact Hcl_orig.
            unfold lineraize_pending_push. simpl.
            rewrite decide_True; last first.
            { split; first reflexivity.
              rewrite map_lookup_imap Hπorig_τ /=.
              rewrite bool_decide_eq_false_2; first reflexivity.
              intros Hτ_in. apply Hτ_notin. exact Hτ_in. }
            (* Now LHS = Some (s_t ++ puL.*2,
                 <[τ:=LP'd Pop]>(map_imap ... π_orig))
               RHS to prove equal to: Some (lineraize puL (s_t, <[τ:=LP'd Pop]>π_orig))
               which is Some (s_t ++ puL.*2, map_imap ... (<[τ:=LP'd Pop]>π_orig)).
               These differ in whether the τ-insert is before or after map_imap. *)
            f_equal. f_equal.
            apply map_eq. intros τ'.
            destruct (decide (τ' = τ)) as [-> | Hne_τ'].
            * rewrite lookup_insert_eq.
              rewrite map_lookup_imap lookup_insert_eq /=.
              rewrite bool_decide_eq_false_2; first reflexivity.
              intros Hτ_in. apply Hτ_notin. exact Hτ_in.
            * rewrite lookup_insert_ne;
                last (intros ?; apply Hne_τ'; congruence).
              rewrite !map_lookup_imap.
              rewrite lookup_insert_ne;
                last (intros ?; apply Hne_τ'; congruence).
              reflexivity.
        - intros τ' Hstat_None.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          + rewrite lookup_insert_eq in Hstat_None. discriminate.
          + rewrite lookup_insert_ne in Hstat_None;
              last (intros ?; apply Hne_τ'; congruence).
            apply (Hscan_dom4 τ' Hstat_None).
        - (* scan_map_l_bounded: scan_map and back_val unchanged. *)
          exact Hscan_lb4. }
      wp_pures.

      (* ────────────────────────────────────────────────────────────────
         Phase 5 — trace_emit Ret (SOMEV v_right).
         ────────────────────────────────────────────────────────────── *)
      wp_bind (trace_emit _ _ _).
      awp_apply (trace_emit_spec _ τ (Ret (encode_response (NonEmpty v_right)))
                  (InjRV (encode_response (NonEmpty v_right))) I_lang_hwq
                  with "Itrace");
        first reflexivity.
      iInv "Hinv" as (items5 back_val5 ts5 M_g5 stat5 slots5 scan_map5)
        "(>Hback & >Har & >Hts & >%Hlen5 & >%Hbpos5 & >HγM & >Hstat & >Hslots & >Hscan & #Hslots_persist5 &
           >%Hmcfg_steps5 & >%Hne5 & >%Hpw5 & >%Hsc5 & >%Hsc_slots5 & >%Hwell5 & >%Htrst5 & >%Hlinw_seq5 & >%Hbnd5 & >%Hssi5 & >%Hcl_push5 & >%Hscan_dom5 & >%Hscan_lb5)".
      iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ5_pre.
      iApply (fupd_mask_intro); first solve_ndisj. iIntros "Hclose_fupd".
      iFrame "Hts". iSplit.
      { iPureIntro.
        apply phase4_ret_preserves_I_lang_pop with (τ := τ) (v := v_right); auto.
        - split.
          + apply set_choose_L in Hne5 as [[s_w π_w] Hw_in].
            assert ((s_w, π_w) ∈ (set_to_propset M_g5 : @meta_config hwq_model)) as Hw_full
                by (apply elem_of_set_to_propset; exact Hw_in).
            exists (set_to_propset M_g5), s_w, π_w. split; auto.
          + exact Hpw5.
        - (* filter ts5 = [(τ, Call Pop)] from trace_stat_consistent at τ. *)
          pose proof (Htrst5 τ) as Htrst_τ. rewrite Hstat_τ5_pre in Htrst_τ.
          exact Htrst_τ.
        - (* ∃ M_full s π with π[τ] = Some (Pop, Some (NonEmpty v_right)).
             Use stat_consistent for OpDeqLinearized (existential witness)
             which gives us a config in M_g5 that's also in set_to_propset M_g5. *)
          pose proof (Hsc5 τ) as Hsc_τ. rewrite Hstat_τ5_pre in Hsc_τ.
          destruct Hsc_τ as (s_w & π_w & Hw_in & Hπ_w).
          assert ((s_w, π_w) ∈ (set_to_propset M_g5 : @meta_config hwq_model)) as Hw_full
              by (apply elem_of_set_to_propset; exact Hw_in).
          exists (set_to_propset M_g5), s_w, π_w. split; first auto. split; first auto.
          exact Hπ_w. }
      iSplit.
      { iIntros "[Hts _]". iMod "Hclose_fupd" as "_". iModIntro.
        iSplitL "Hback Har Hts HγM Hstat Hslots Hscan".
        { iNext. iExists items5, back_val5, ts5, M_g5, stat5, slots5, scan_map5.
          iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist5".
          iPureIntro. split_and!; assumption. }
        iFrame "HΦ Hstat_τ Hscan_τ". }
      iIntros "Hts". iMod "Hclose_fupd" as "_".
      iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ5.
      iMod (ghost_map_update (OpDeqDone v_right) with "Hstat Hstat_τ")
        as "[Hstat Hstat_τ]".
      (* Chain trick: get OpDeqLin ∃ witness (s_q, π_q), then chain LP τ_x
         for each currently-Stored τ_x with π_q[τ_x] pending. This gives
         configs with both τ_x and τ_p linearized — surviving Phase 5
         filter and providing OpEnqStored ∃ witnesses post-filter. *)
      pose proof (Hsc5 τ) as Hsc_τ_pop. rewrite Hstat_τ5 in Hsc_τ_pop.
      destruct Hsc_τ_pop as (s_q & π_q & Hin_q & Hπ_q_τ_p).
      assert (Hq_full : (s_q, π_q) ∈ (set_to_propset M_g5 : @meta_config hwq_model)).
      { apply elem_of_set_to_propset. exact Hin_q. }
      pose (pushes := pending_stored_pushes_at_π stat5 π_q).
      pose proof (pending_stored_pushes_at_π_Forall stat5 π_q) as Hpushes_Forall.
      destruct (mcfg_steps_chain_lp_push_list (set_to_propset M_g5) s_q π_q pushes
                  Hq_full Hpushes_Forall)
        as (M_full5_chained & Hchain_steps & Hchain_sub & Hchain_wit & Hchain_upper).
      pose (chained_configs :=
        (list_to_set (map (fun pv : positive * val =>
          ((s_q ++ [pv.2])%list,
           <[pv.1:=(Push, pv.2, Some #())]>π_q))
          pushes)) : gset single_config_q).
      pose (M_g5_extended := (M_g5 ∪ chained_configs) : gset single_config_q).
      pose (M_g5_new := (filter
        (λ x : single_config_q,
          x.2 !! τ = Some (Pop, #(),
                           Some (encode_response (NonEmpty v_right))))
        M_g5_extended)).
      iMod (ghost_var_update M_g5_new with "HγM") as "HγM".
      assert (HM_full5_new_eq :
        (M_full5_chained ∩
          {[ (_, π) | snd <$> (π !! τ) =
                        Some (Some (encode_response (NonEmpty v_right))) ]}
         : @meta_config hwq_model)
        = (set_to_propset M_g5_new : @meta_config hwq_model)).
      { (* Derive request-value uniqueness for τ from trace_stat_consistent:
           filter τ ts5 = [(τ, Call Pop #())]. *)
        pose proof (Htrst5 τ) as Htrst_τ. rewrite Hstat_τ5 in Htrst_τ.
        (* Htrst_τ : filter τ ts5 = [(τ, Call Pop #())] *)
        assert (Hreq_unique : set_Forall
                  (λ '(_, π), ∀ v_x v_resp,
                     π !! τ = Some (v_x, v_resp) → v_x = (Pop, #()))
                  (set_to_propset M_g5 : @meta_config hwq_model)).
        { eapply mcfg_steps_request_value_from_filter_eq; first exact Hmcfg_steps5.
          intros τ' n' v' Hin_ts Heq_τ. subst τ'.
          (* (τ, Call n' v') ∈ ts5 implies it is in filter τ ts5 = [(τ, Call Pop #())]. *)
          assert (Hin_filter : (τ, Call n' v') ∈ filter (λ t : positive * trace, t.1 = τ) ts5).
          { apply list_elem_of_filter. split; first reflexivity. exact Hin_ts. }
          rewrite Htrst_τ in Hin_filter.
          apply list_elem_of_singleton in Hin_filter. injection Hin_filter as -> ->.
          reflexivity. }
        apply leibniz_equiv. intros [s π]. split.
        - (* Forward *)
          intros [Hin_chained Hin_filter]%elem_of_intersection.
          assert (Hfilter_eq : snd <$> (π !! τ) =
                       Some (Some (encode_response (NonEmpty v_right))))
            by (apply (elem_of_PropSet
                         (λ x : single_config_q,
                           snd <$> (x.2 !! τ) =
                             Some (Some (encode_response (NonEmpty v_right))))
                         (s, π)); exact Hin_filter).
          apply elem_of_set_to_propset. unfold M_g5_new.
          apply elem_of_filter.
          (* Extract π[τ] = Some(v_t, Some v_r) form, with v_t the (op, arg) pair. *)
          destruct (π !! τ) as [[v_t v_resp]|] eqn:Hπτ; simpl in Hfilter_eq;
            try discriminate.
          destruct v_resp as [v_r|]; simpl in Hfilter_eq; try discriminate.
          injection Hfilter_eq as ->.
          (* Now we need v_t = (Pop, #()). Use Hchain_upper. *)
          destruct (Hchain_upper (s, π) Hin_chained) as
            [Hin_g | (pv & Hpv_in & Heq)].
          + (* (s, π) ∈ set_to_propset M_g5. Use request uniqueness. *)
            assert (v_t = (Pop, #())) as ->.
            { eapply (Hreq_unique (s, π) Hin_g v_t (Some _) Hπτ). }
            split.
            * exact Hπτ.
            * unfold M_g5_extended. apply elem_of_union. left.
              apply elem_of_set_to_propset in Hin_g. exact Hin_g.
          + (* (s, π) is the LP'd image. *)
            (* From Heq: (s, π) = ((s_q ++ [pv.2]), <[pv.1:=...]>π_q). *)
            injection Heq as Hs_eq Hπ_eq. subst s π.
            destruct (decide (pv.1 = τ)) as [Hpvτ | Hne_pvτ].
            * (* pv.1 = τ: contradiction with filter *)
              exfalso. rewrite Hpvτ lookup_insert_eq in Hπτ.
              injection Hπτ as _ Hresp.
              (* Hresp: Some #() = Some (encode_response (NonEmpty v_right)) *)
              discriminate Hresp.
            * (* pv.1 ≠ τ: π[τ] = π_q[τ] = (Pop, Some(NE v_right)) *)
              rewrite lookup_insert_ne in Hπτ;
                last (intros ?; apply Hne_pvτ; congruence).
              rewrite Hπτ in Hπ_q_τ_p. injection Hπ_q_τ_p as Hreq_eq.
              subst v_t.
              split.
              -- (* Goal: π[τ] = Some(Pop, #(), Some(encode_response (NE v_right))) *)
                 rewrite lookup_insert_ne;
                   last (intros ?; apply Hne_pvτ; congruence).
                 exact Hπτ.
              -- unfold M_g5_extended. apply elem_of_union. right.
                 unfold chained_configs. apply elem_of_list_to_set.
                 apply list_elem_of_In, in_map_iff.
                 exists pv. split; first reflexivity.
                 apply list_elem_of_In. exact Hpv_in.
        - (* Backward *)
          intros Hin_new. rewrite elem_of_set_to_propset in Hin_new.
          unfold M_g5_new in Hin_new.
          apply elem_of_filter in Hin_new as [Hπτ_lin Hin_ext].
          simpl in Hπτ_lin.
          apply elem_of_intersection. split.
          + (* (s, π) ∈ M_full5_chained *)
            unfold M_g5_extended in Hin_ext.
            apply elem_of_union in Hin_ext as [Hin_g5 | Hin_chained_set].
            * apply Hchain_sub. apply elem_of_set_to_propset. exact Hin_g5.
            * unfold chained_configs in Hin_chained_set.
              apply elem_of_list_to_set in Hin_chained_set.
              apply list_elem_of_In, in_map_iff in Hin_chained_set
                as (pv & Heq & Hpv_in).
              rewrite -Heq.
              rewrite Forall_forall in Hchain_wit.
              apply Hchain_wit.
              apply list_elem_of_In. exact Hpv_in.
          + (* filter predicate holds *)
            apply elem_of_PropSet. simpl. rewrite Hπτ_lin. reflexivity. }
      iModIntro.
      iSplitR "HΦ".
      { iNext.
        iExists items5, back_val5,
                (ts5 ++ [(τ, Ret (encode_response (NonEmpty v_right)))]),
                M_g5_new, (<[τ:=OpDeqDone v_right]> stat5), slots5, scan_map5.
        iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist5".
        iPureIntro. split_and!; try assumption.
        - (* mcfg_steps: chain LP pushes, then mcfg_step_ret. *)
          rewrite -HM_full5_new_eq.
          eapply rtcL_r.
          + replace ts5 with (ts5 ++ []) by by rewrite app_nil_r.
            eapply rtcL_trans; first exact Hmcfg_steps5.
            exact Hchain_steps.
          + apply (mcfg_step_ret M_full5_chained τ (encode_response (NonEmpty v_right))).
        - (* non-empty: M_g5_new contains the witness from OpDeqLinearized. *)
          pose proof (Hsc5 τ) as Hsc_τ. rewrite Hstat_τ5 in Hsc_τ.
          destruct Hsc_τ as (s_w & π_w & Hin_w & Hπ_w).
          intros Habs.
          assert (Hin_filter : (s_w, π_w) ∈ M_g5_new).
          { unfold M_g5_new. apply elem_of_filter.
            split; first exact Hπ_w.
            unfold M_g5_extended. apply elem_of_union. left. exact Hin_w. }
          rewrite Habs in Hin_filter. clear -Hin_filter. set_solver.
        - (* per_tag_wellformed snoc Ret. Derive filter ts5 = [(τ, Call Pop)]
             from Htrst5 at τ (stat5[τ] = OpDeqLinearized v_right). *)
          eapply per_tag_wellformed_snoc_ret; first exact Hpw5.
          pose proof (Htrst5 τ) as Htrst_τ. rewrite Hstat_τ5 in Htrst_τ.
          exact Htrst_τ.
        - (* stat_consistent: OpDeqLinearized (∃) → OpDeqDone (∀).
             After filter, all configs in M_g5_new have π[τ] = Some #(...). *)
          intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
          + rewrite lookup_insert_eq.
            intros s' π' Hin_new. unfold M_g5_new in Hin_new.
            apply elem_of_filter in Hin_new as [Hπτ _]. exact Hπτ.
          + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
            pose proof (Hsc5 τ') as Hsc_τ'.
            destruct (stat5 !! τ') as [s_op|] eqn:Hlk.
            * destruct s_op as [v0 | v0 i0 | v0 i0 | v0 i0 | | v0 | v0].
              -- (* OpEnqPending *)
                 intros s' π' Hin_new. unfold M_g5_new in Hin_new.
                 apply elem_of_filter in Hin_new as [_ Hin_ext].
                 unfold M_g5_extended in Hin_ext.
                 apply elem_of_union in Hin_ext as [Hin_g | Hin_ch].
                 ++ by apply (Hsc_τ' s' π' Hin_g).
                 ++ unfold chained_configs in Hin_ch.
                    apply (chained_config_destruct s_q π_q pushes s' π') in Hin_ch
                      as (τ_x & v_x & Hs_eq & Hπ_eq & Hpv).
                    subst.
                    apply pending_stored_pushes_at_π_implies_stored in Hpv
                      as (i_x & Hstat_τ_x).
                    destruct (decide (τ_x = τ')) as [-> | Hne_τx].
                    ** rewrite Hstat_τ_x in Hlk. discriminate.
                    ** rewrite lookup_insert_ne;
                         last (intros ?; apply Hne_τx; congruence).
                       by apply (Hsc_τ' s_q π_q Hin_q).
              -- (* OpEnqReserved — conj (∀-disj, ∃-LP'd).
                    Note: chained configs only LP τ_x ∈ pending_stored_pushes,
                    which by pending_stored_pushes_at_π_implies_stored have
                    stat[τ_x] = OpEnqStored, never Reserved. So τ_x ≠ τ' for
                    τ' at OpEnqReserved. *)
                 destruct Hsc_τ' as [Hsc_all Hsc_ex].
                 split.
                 { intros s' π' Hin_new. unfold M_g5_new in Hin_new.
                   apply elem_of_filter in Hin_new as [_ Hin_ext].
                   unfold M_g5_extended in Hin_ext.
                   apply elem_of_union in Hin_ext as [Hin_g | Hin_ch].
                   ++ by apply (Hsc_all s' π' Hin_g).
                   ++ unfold chained_configs in Hin_ch.
                      apply (chained_config_destruct s_q π_q pushes s' π') in Hin_ch
                        as (τ_x & v_x & Hs_eq & Hπ_eq & Hpv).
                      subst.
                      apply pending_stored_pushes_at_π_implies_stored in Hpv
                        as (i_x & Hstat_τ_x).
                      destruct (decide (τ_x = τ')) as [-> | Hne_τx].
                      ** rewrite Hstat_τ_x in Hlk. discriminate.
                      ** rewrite lookup_insert_ne;
                           last (intros ?; apply Hne_τx; congruence).
                         by apply (Hsc_all s_q π_q Hin_q). }
                 (* ∃-LP'd: case-split π_q[τ']. *)
                 pose proof (Hsc_all s_q π_q Hin_q) as Hπ_q_τ'.
                 destruct Hπ_q_τ' as [Hπ_q_pending | Hπ_q_lin].
                 ++ (* π_q[τ'] = (Push, None): apply closure_push_single. *)
                    pose proof (closure_push_single M_g5 stat5 (s_q, π_q) τ' v0 i0
                                  Hcl_push5 Hin_q Hπ_q_pending (or_introl Hlk))
                      as Hin_cp.
                    simpl in Hin_cp.
                    exists (s_q ++ [v0])%list,
                      (<[τ':=(Push, v0, Some #())]>π_q).
                    split.
                    ** unfold M_g5_new. apply elem_of_filter. split.
                       --- rewrite lookup_insert_ne;
                             last (intros ?; apply Hne_τ; congruence).
                           exact Hπ_q_τ_p.
                       --- unfold M_g5_extended. apply elem_of_union. left. exact Hin_cp.
                    ** apply lookup_insert_eq.
                 ++ (* π_q[τ'] = Some #(): use (s_q, π_q) directly. *)
                    exists s_q, π_q. split; last exact Hπ_q_lin.
                    unfold M_g5_new. apply elem_of_filter. split.
                    ** exact Hπ_q_τ_p.
                    ** unfold M_g5_extended. apply elem_of_union. left. exact Hin_q.
              -- (* OpEnqStored — conj. Use chain trick for ∃ witness. *)
                 destruct Hsc_τ' as [Hsc_all Hsc_ex].
                 split.
                 { intros s' π' Hin_new. unfold M_g5_new in Hin_new.
                   apply elem_of_filter in Hin_new as [_ Hin_ext].
                   unfold M_g5_extended in Hin_ext.
                   apply elem_of_union in Hin_ext as [Hin_g | Hin_ch].
                   ++ by apply (Hsc_all s' π' Hin_g).
                   ++ unfold chained_configs in Hin_ch.
                      apply (chained_config_destruct s_q π_q pushes s' π') in Hin_ch
                        as (τ_x & v_x & Hs_eq & Hπ_eq & Hpv).
                      subst.
                      apply pending_stored_pushes_at_π_implies_stored in Hpv
                        as (i_x & Hstat_τ_x).
                      destruct (decide (τ_x = τ')) as [-> | Hne_τx].
                      ** rewrite Hstat_τ_x in Hlk. injection Hlk as <- _.
                         right. apply lookup_insert_eq.
                      ** rewrite lookup_insert_ne;
                           last (intros ?; apply Hne_τx; congruence).
                         by apply (Hsc_all s_q π_q Hin_q). }
                 (* ∃ witness: case-split π_q[τ']. *)
                 pose proof (Hsc_all s_q π_q Hin_q) as Hπ_q_τ'.
                 destruct Hπ_q_τ' as [Hπ_q_pending | Hπ_q_lin].
                 ++ (* π_q[τ'] = (Push, None): use chained config. *)
                    exists ((s_q ++ [v0])%list),
                      (<[τ':=(Push, v0, Some #())]>π_q).
                    split.
                    ** unfold M_g5_new. apply elem_of_filter. split.
                       --- rewrite lookup_insert_ne;
                             last (intros ?; apply Hne_τ; congruence).
                           exact Hπ_q_τ_p.
                       --- unfold M_g5_extended. apply elem_of_union. right.
                           unfold chained_configs. apply elem_of_list_to_set.
                           apply list_elem_of_fmap. exists (τ', v0).
                           split; first reflexivity.
                           apply (pending_stored_pushes_at_π_complete stat5 π_q
                                    τ' v0 i0 Hlk Hπ_q_pending).
                    ** apply lookup_insert_eq.
                 ++ (* π_q[τ'] = Some #(): use (s_q, π_q) directly. *)
                    exists s_q, π_q. split; last exact Hπ_q_lin.
                    unfold M_g5_new. apply elem_of_filter. split.
                    ** exact Hπ_q_τ_p.
                    ** unfold M_g5_extended. apply elem_of_union. left. exact Hin_q.
              -- (* OpEnqDone *)
                 intros s' π' Hin_new. unfold M_g5_new in Hin_new.
                 apply elem_of_filter in Hin_new as [_ Hin_ext].
                 unfold M_g5_extended in Hin_ext.
                 apply elem_of_union in Hin_ext as [Hin_g | Hin_ch].
                 ++ by apply (Hsc_τ' s' π' Hin_g).
                 ++ unfold chained_configs in Hin_ch.
                    apply (chained_config_destruct s_q π_q pushes s' π') in Hin_ch
                      as (τ_x & v_x & Hs_eq & Hπ_eq & Hpv).
                    subst.
                    apply pending_stored_pushes_at_π_implies_stored in Hpv
                      as (i_x & Hstat_τ_x).
                    destruct (decide (τ_x = τ')) as [-> | Hne_τx].
                    ** rewrite Hstat_τ_x in Hlk. discriminate.
                    ** rewrite lookup_insert_ne;
                         last (intros ?; apply Hne_τx; congruence).
                       by apply (Hsc_τ' s_q π_q Hin_q).
              -- (* OpDeqPending *)
                 intros s' π' Hin_new. unfold M_g5_new in Hin_new.
                 apply elem_of_filter in Hin_new as [_ Hin_ext].
                 unfold M_g5_extended in Hin_ext.
                 apply elem_of_union in Hin_ext as [Hin_g | Hin_ch].
                 ++ by apply (Hsc_τ' s' π' Hin_g).
                 ++ unfold chained_configs in Hin_ch.
                    apply (chained_config_destruct s_q π_q pushes s' π') in Hin_ch
                      as (τ_x & v_x & Hs_eq & Hπ_eq & Hpv).
                    subst.
                    apply pending_stored_pushes_at_π_implies_stored in Hpv
                      as (i_x & Hstat_τ_x).
                    destruct (decide (τ_x = τ')) as [-> | Hne_τx].
                    ** rewrite Hstat_τ_x in Hlk. discriminate.
                    ** rewrite lookup_insert_ne;
                         last (intros ?; apply Hne_τx; congruence).
                       by apply (Hsc_τ' s_q π_q Hin_q).
              -- (* OpDeqLinearized — use pop_universal_witness (derived locally). *)
                 pose proof (pop_universal_witness_derive M_g5 items5 slots5 stat5 scan_map5
                              Hsc_slots5 Hlinw_seq5) as Hpop_uw5.
                 destruct Hpop_uw5 as (s_uw & π_uw & Hin_uw & Hpop_lin_uw & _).
                 exists s_uw, π_uw. split.
                 ++ unfold M_g5_new. apply elem_of_filter.
                    split; last (unfold M_g5_extended; apply elem_of_union; left; exact Hin_uw).
                    apply (Hpop_lin_uw τ v_right Hstat_τ5).
                 ++ apply (Hpop_lin_uw τ' v0 Hlk).
              -- (* OpDeqDone *)
                 intros s' π' Hin_new. unfold M_g5_new in Hin_new.
                 apply elem_of_filter in Hin_new as [_ Hin_ext].
                 unfold M_g5_extended in Hin_ext.
                 apply elem_of_union in Hin_ext as [Hin_g | Hin_ch].
                 ++ by apply (Hsc_τ' s' π' Hin_g).
                 ++ unfold chained_configs in Hin_ch.
                    apply (chained_config_destruct s_q π_q pushes s' π') in Hin_ch
                      as (τ_x & v_x & Hs_eq & Hπ_eq & Hpv).
                    subst.
                    apply pending_stored_pushes_at_π_implies_stored in Hpv
                      as (i_x & Hstat_τ_x).
                    destruct (decide (τ_x = τ')) as [-> | Hne_τx].
                    ** rewrite Hstat_τ_x in Hlk. discriminate.
                    ** rewrite lookup_insert_ne;
                         last (intros ?; apply Hne_τx; congruence).
                       by apply (Hsc_τ' s_q π_q Hin_q).
            * (* None case *)
              intros s' π' Hin_new. unfold M_g5_new in Hin_new.
              apply elem_of_filter in Hin_new as [_ Hin_ext].
              unfold M_g5_extended in Hin_ext.
              apply elem_of_union in Hin_ext as [Hin_g | Hin_ch].
              -- by apply (Hsc_τ' s' π' Hin_g).
              -- unfold chained_configs in Hin_ch.
                 apply (chained_config_destruct s_q π_q pushes s' π') in Hin_ch
                   as (τ_x & v_x & Hs_eq & Hπ_eq & Hpv).
                 subst.
                 apply pending_stored_pushes_at_π_implies_stored in Hpv
                   as (i_x & Hstat_τ_x).
                 destruct (decide (τ_x = τ')) as [-> | Hne_τx].
                 ++ rewrite Hstat_τ_x in Hlk. discriminate.
                 ++ rewrite lookup_insert_ne;
                      last (intros ?; apply Hne_τx; congruence).
                    by apply (Hsc_τ' s_q π_q Hin_q).
        - (* trace_stat_consistent: stat[τ] := OpDeqDone v_right, ts extended with Ret. *)
          intros τ'. destruct (decide (τ' = τ)) as [-> | Hne_τ].
          + rewrite lookup_insert_eq.
            pose proof (Htrst5 τ) as Htrst_τ. rewrite Hstat_τ5 in Htrst_τ.
            rewrite filter_app filter_cons_True; last reflexivity.
            rewrite filter_nil. rewrite Htrst_τ. reflexivity.
          + rewrite lookup_insert_ne; last (intros ?; apply Hne_τ; congruence).
            rewrite filter_app filter_cons_False;
              last (by intros Heq; apply Hne_τ).
            rewrite filter_nil app_nil_r.
            exact (Htrst5 τ').
        - intros A seq HgoodA HnodupSeq Hsetof HJInvSeq.
          (* Step 1: reduce NEW GoodEnqSet to OLD. *)
          assert (HgoodA_old : GoodEnqSet A items5 stat5).
          { destruct HgoodA as [Hgood1 Hgood2]. split; first exact Hgood1.
            intros k Hin_A. destruct (Hgood2 k Hin_A) as [Hcase | (τ_e & v_e & Hres)].
            - left. exact Hcase.
            - right. destruct (decide (τ_e = τ)) as [-> | Hne_τe].
              + rewrite lookup_insert_eq in Hres. discriminate.
              + exists τ_e, v_e. rewrite lookup_insert_ne in Hres;
                  last (intros ?; apply Hne_τe; congruence).
                exact Hres. }
          (* Step 2: reduce NEW JInvSeq to OLD. *)
          assert (HJInvSeq_old : JInvSeq seq slots5 stat5 scan_map5).
          { intros n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km.
            destruct (HJInvSeq n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km)
              as (τ_d & l & j_d & Hstat_d & Hscan_d & Hkl & Hkj).
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            - rewrite lookup_insert_eq in Hstat_d. discriminate.
            - exists τ_d, l, j_d. split_and!; try assumption.
              rewrite lookup_insert_ne in Hstat_d;
                last (intros ?; apply Hne_τd; congruence).
              exact Hstat_d. }
          (* Step 3: apply OLD Hlinw_seq5. *)
          destruct (Hlinw_seq5 A seq HgoodA_old HnodupSeq Hsetof HJInvSeq_old)
            as (s & π & Hin5 & Hlen_s & Hmatch_slots & Hmatch_items & Henq & Hlin & Hdone & Hpending & Hstored & Hreserved).
          exists s, π. split_and!.
          + (* (s, π) ∈ M_g5_new: passes filter because π[τ] = LP'd Pop NE v_right. *)
            unfold M_g5_new. apply elem_of_filter.
            split.
            * (* π[τ] = LP'd Pop NE v_right from Hlin applied to stat5[τ] = OpDeqLinearized v_right. *)
              apply (Hlin τ v_right Hstat_τ5).
            * unfold M_g5_extended. apply elem_of_union. left. exact Hin5.
          + exact Hlen_s.
          + exact Hmatch_slots.
          + intros n k Hseq_n.
            destruct (Hmatch_items n k Hseq_n) as [Hcase | (τ_e & v_e & Hres & Hsn)].
            * left. exact Hcase.
            * right. destruct (decide (τ_e = τ)) as [-> | Hne_τe].
              -- rewrite Hstat_τ5 in Hres. discriminate.
              -- exists τ_e, v_e. split; last exact Hsn.
                 rewrite lookup_insert_ne;
                   last (intros ?; apply Hne_τe; congruence).
                 exact Hres.
          + intros τ_d v_d i_d Hstat_d.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            * rewrite lookup_insert_eq in Hstat_d. discriminate.
            * rewrite lookup_insert_ne in Hstat_d;
                last (intros ?; apply Hne_τd; congruence).
              by apply (Henq τ_d v_d i_d).
          + intros τ_d v_d Hstat_d.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            * rewrite lookup_insert_eq in Hstat_d. discriminate.
            * rewrite lookup_insert_ne in Hstat_d;
                last (intros ?; apply Hne_τd; congruence).
              by apply (Hlin τ_d v_d).
          + intros τ_d v_d Hstat_d.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            * rewrite lookup_insert_eq in Hstat_d. injection Hstat_d as <-.
              (* π[τ] = LP'd Pop NE v_right comes from Hlin at OLD OpDeqLinearized. *)
              apply (Hlin τ v_right Hstat_τ5).
            * rewrite lookup_insert_ne in Hstat_d;
                last (intros ?; apply Hne_τd; congruence).
              by apply (Hdone τ_d v_d).
          + intros τ_d Hstat_d.
            destruct (decide (τ_d = τ)) as [-> | Hne_τd].
            * rewrite lookup_insert_eq in Hstat_d. discriminate.
            * rewrite lookup_insert_ne in Hstat_d;
                last (intros ?; apply Hne_τd; congruence).
              by apply (Hpending τ_d).
          + intros τ_e v_e i_e Hstat_e.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            * rewrite lookup_insert_eq in Hstat_e. discriminate.
            * rewrite lookup_insert_ne in Hstat_e;
                last (intros ?; apply Hne_τe; congruence).
              by apply (Hstored τ_e v_e i_e).
          + intros τ_e v_e i_e Hstat_e.
            destruct (decide (τ_e = τ)) as [-> | Hne_τe].
            * rewrite lookup_insert_eq in Hstat_e. discriminate.
            * rewrite lookup_insert_ne in Hstat_e;
                last (intros ?; apply Hne_τe; congruence).
              by apply (Hreserved τ_e v_e i_e).
        - (* slots_stat_iff: stat τ → OpDeqDone, slots unchanged.
             stat5[τ] was OpDeqLinearized — not Reserved/Stored/Done — and
             OpDeqDone is also not Reserved/Stored/Done. So new τ entry
             can't satisfy any slot_stat_iff clause. *)
          destruct Hssi5 as (Hssi_a5 & Hssi_b5 & Hssi_c5 & Hssi_d5).
          unfold stat_owns, stat_faad.
          split_and!.
          + intros τ' v' i' Howns.
            destruct (decide (τ' = τ)) as [-> | Hne_τ'].
            * destruct Howns as [Howns | Howns];
                rewrite lookup_insert_eq in Howns; discriminate.
            * apply (Hssi_a5 τ' v' i').
              destruct Howns as [Howns | Howns];
                rewrite lookup_insert_ne in Howns;
                try (intros ?; apply Hne_τ'; congruence);
                [left | right]; exact Howns.
          + intros i' v' Hslot'.
            destruct (Hssi_b5 _ _ Hslot') as (τ_w & Hstat_w).
            exists τ_w. destruct (decide (τ_w = τ)) as [-> | Hne_τw].
            * exfalso. destruct Hstat_w as [Hstat_w | Hstat_w];
                rewrite Hstat_τ5 in Hstat_w; discriminate.
            * destruct Hstat_w as [Hstat_w | Hstat_w];
                [left | right];
                rewrite lookup_insert_ne;
                try (intros ?; apply Hne_τw; congruence);
                exact Hstat_w.
          + intros τ_1 τ_2 v_1 v_2 i' Hτ1 Hτ2.
            destruct (decide (τ_1 = τ)) as [-> | Hne_τ1];
              destruct (decide (τ_2 = τ)) as [-> | Hne_τ2].
            * reflexivity.
            * exfalso. destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                rewrite lookup_insert_eq in Hτ1; discriminate.
            * exfalso. destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                rewrite lookup_insert_eq in Hτ2; discriminate.
            * assert (Hτ1_old : stat_faad stat5 τ_1 v_1 i').
              { destruct Hτ1 as [Hτ1|[Hτ1|Hτ1]];
                  rewrite lookup_insert_ne in Hτ1;
                  try (intros ?; apply Hne_τ1; congruence).
                - left. exact Hτ1.
                - right. left. exact Hτ1.
                - right. right. exact Hτ1. }
              assert (Hτ2_old : stat_faad stat5 τ_2 v_2 i').
              { destruct Hτ2 as [Hτ2|[Hτ2|Hτ2]];
                  rewrite lookup_insert_ne in Hτ2;
                  try (intros ?; apply Hne_τ2; congruence).
                - left. exact Hτ2.
                - right. left. exact Hτ2.
                - right. right. exact Hτ2. }
              apply (Hssi_c5 τ_1 τ_2 v_1 v_2 i' Hτ1_old Hτ2_old).
          + intros τ' v' i' Hstat'.
            destruct (decide (τ' = τ)) as [-> | Hne_τ'].
            * exfalso. destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
                rewrite lookup_insert_eq in Hstat'; discriminate.
            * assert (Hstat'_old : stat_faad stat5 τ' v' i').
              { destruct Hstat' as [Hstat'|[Hstat'|Hstat']];
                  rewrite lookup_insert_ne in Hstat';
                  try (intros ?; apply Hne_τ'; congruence).
                - left. exact Hstat'.
                - right. left. exact Hstat'.
                - right. right. exact Hstat'. }
              exact (Hssi_d5 τ' v' i' Hstat'_old).
        - intros cfg puL Hin Hnd Hsubset Hstat_pushes.
          unfold M_g5_new in Hin. apply elem_of_filter in Hin as [Hπ_filter Hin_ext].
          (* τ ∉ puL.*1: new stat[τ] = OpDeqDone, not Reserved/Stored. *)
          assert (Hτ_notin : τ ∉ puL.*1).
          { intros Hin_τ.
            apply list_elem_of_fmap_1 in Hin_τ as (pv & Heq_τ & Hpv_in).
            destruct (Hstat_pushes pv Hpv_in) as (v' & i' & [Hs | Hs]);
              rewrite -Heq_τ in Hs; rewrite lookup_insert_eq in Hs; discriminate. }
          (* stat_pushes on stat5 (drop new τ insertion). *)
          assert (Hstat_pushes_old : ∀ pv, pv ∈ puL → ∃ v i,
                    stat5 !! pv.1 = Some (OpEnqReserved v i) ∨
                    stat5 !! pv.1 = Some (OpEnqStored v i)).
          { intros pv Hpv_in. destruct (Hstat_pushes pv Hpv_in) as (v' & i' & Hstat').
            exists v', i'. assert (Hne_pv_τ : pv.1 ≠ τ).
            { intros Heq_pv. apply Hτ_notin.
              rewrite -Heq_pv. apply (list_elem_of_fmap_2 fst _ pv); exact Hpv_in. }
            destruct Hstat' as [Hs | Hs].
            - left. rewrite lookup_insert_ne in Hs;
                last (intros ?; apply Hne_pv_τ; congruence). exact Hs.
            - right. rewrite lookup_insert_ne in Hs;
                last (intros ?; apply Hne_pv_τ; congruence). exact Hs. }
          (* Show cfg ∈ M_g5: case split on M_g5_extended = M_g5 ∪ chained_configs. *)
          assert (Hcfg_in_M_g5 : cfg ∈ M_g5).
          { apply elem_of_union in Hin_ext as [Hin5 | Hin_chained_cfg].
            - exact Hin5.
            - unfold chained_configs in Hin_chained_cfg.
              apply elem_of_list_to_set in Hin_chained_cfg.
              apply list_elem_of_In, in_map_iff in Hin_chained_cfg
                as (pv & Hcfg_eq & Hpv_in).
              subst cfg.
              assert (Hpv_in_set : pv ∈ pushes).
              { apply list_elem_of_In. exact Hpv_in. }
              assert (Hpv_pending : π_q !! pv.1 = Some (Push, pv.2, None)).
              { rewrite Forall_forall in Hpushes_Forall.
                exact (Hpushes_Forall pv Hpv_in_set). }
              assert (Hpv_stored : ∃ i, stat5 !! pv.1 = Some (OpEnqStored pv.2 i)).
              { destruct (pending_stored_pushes_at_π_implies_stored stat5 π_q pv.1 pv.2)
                  as (i & Hi).
                - unfold pushes in Hpv_in_set.
                  rewrite (surjective_pairing pv) in Hpv_in_set.
                  exact Hpv_in_set.
                - exists i. exact Hi. }
              destruct Hpv_stored as (i_pv & Hpv_stored).
              exact (closure_push_single M_g5 stat5 (s_q, π_q) pv.1 pv.2 i_pv
                       Hcl_push5 Hin_q Hpv_pending (or_intror Hpv_stored)). }
          (* Now apply Hcl_push5 directly on cfg (in M_g5). *)
          pose proof (Hcl_push5 cfg puL Hcfg_in_M_g5 Hnd Hsubset Hstat_pushes_old) as Hcl_x.
          unfold M_g5_new. apply elem_of_filter. split; last first.
          + apply elem_of_union_l. exact Hcl_x.
          + (* Show (lineraize puL cfg).2[τ] = LP'd Pop NE v_right *)
            unfold lineraize_pending_push. simpl.
            rewrite map_lookup_imap.
            rewrite Hπ_filter. simpl.
            rewrite bool_decide_eq_false_2;
              last (intros Hτ_in; apply Hτ_notin; exact Hτ_in).
            reflexivity.
        - intros τ' Hstat_None.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          + rewrite lookup_insert_eq in Hstat_None. discriminate.
          + rewrite lookup_insert_ne in Hstat_None;
              last (intros ?; apply Hne_τ'; congruence).
            apply (Hscan_dom5 τ' Hstat_None). }
      wp_pures. by iApply "HΦ".
    + (* ────────────────────────────────────────────────────────────────
         CmpXchg fails: a_j' ≠ InjRV v_right, recurse via IH_inner with
         the SOMEV branch's j_scan widened to S j to maintain the invariant
         (since the next iteration handles slot j+1). *)
      wp_apply (wp_cmpxchg_fail_offset _ _ _ _ (Z.to_nat j) with "Har")
        as "Har"; [exact Hj_eq4 | done | by right |].
      (* Widen scan_map[τ] := (range_z, S j) before recursing —
         for IH_inner we need j_scan = Z.to_nat (j+1).
         CAS-fail derives items4[j] = NONEV via the persistent slots fragment
         captured at Phase 3 load, enabling the NONEV widening lemma. *)
      iDestruct (ghost_map_lookup with "Hstat Hstat_τ") as %Hstat_τ4_now.
      iDestruct (ghost_map_lookup with "Hscan Hscan_τ") as %Hscan_τ4_pre.
      (* Use the persistent fragment captured at Phase 3 load to derive
         slots4[j] = Some w. *)
      iDestruct (ghost_map_lookup with "Hslots Hslot_j_persist") as %Hslot_j4.
      iMod (ghost_map_update (Z.to_nat range_z, Nat.succ (Z.to_nat j))
              with "Hscan Hscan_τ") as "[Hscan Hscan_τ]".
      (* From slots_consistent + Hslot_j4: items4[j] ∈ {SOMEV w, NONEV}.
         CAS-fail's hypothesis Hne_aj' : a_j' ≠ InjRV v_right (= InjRV w).
         a_j' = items4[j] (from Hj_eq4). So items4[j] ≠ InjRV w, hence
         items4[j] = NONEV. *)
      assert (Hitems_nonev : items4 !! Z.to_nat j = Some NONEV).
      { destruct Hsc_slots4 as [Hsc_dir1 _].
        destruct (Hsc_dir1 (Z.to_nat j) w Hslot_j4) as (_ & [Hsomev | Hnonev]).
        - (* items4[j] = SOMEV w. Then a_j' = items4[j] = InjRV w = InjRV v_right.
             But Hne_aj' says a_j' ≠ InjRV v_right. Contradiction. *)
          exfalso. apply Hne_aj'.
          rewrite Hj_eq4 in Hsomev. injection Hsomev as ->. reflexivity.
        - exact Hnonev. }
      iModIntro.
      iSplitR "HΦ Hstat_τ Hscan_τ".
      { iNext. iExists items4, back_val4, ts4, M_g4, stat4, slots4,
                       (<[τ:=(Z.to_nat range_z, Nat.succ (Z.to_nat j))]> scan_map4).
        iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_persist4".
        iPureIntro. split_and!; try assumption.
        - assert (Hjscan_eq_j_nat : j_scan = Z.to_nat j).
          { unfold j. rewrite -Hj_scan_eq. by rewrite Nat2Z.id. }
          rewrite Hjscan_eq_j_nat in Hscan_τ4_pre.
          eapply lin_witness_seq_widen_τ_scan_nonev;
            [exact Hscan_τ4_pre | exact Hitems_nonev | exact Hssi4 | exact Hlinw_seq4].
        - intros τ' Hstat_None.
          destruct (decide (τ' = τ)) as [-> | Hne_τ'].
          + rewrite Hstat_τ4_now in Hstat_None. discriminate.
          + rewrite lookup_insert_ne;
              last (intros ?; apply Hne_τ'; congruence).
            apply (Hscan_dom4 τ' Hstat_None).
        - (* scan_map_l_bounded: only j component updated, l unchanged. *)
          intros τ_p l_p j_p Hscan_τ_p.
          destruct (decide (τ_p = τ)) as [-> | Hne_τp].
          + rewrite lookup_insert_eq in Hscan_τ_p.
            injection Hscan_τ_p as <- _.
            exact (Hscan_lb4 τ (Z.to_nat range_z) j_scan Hscan_τ4_pre).
          + rewrite lookup_insert_ne in Hscan_τ_p;
              last (intros ?; apply Hne_τp; congruence).
            exact (Hscan_lb4 τ_p l_p j_p Hscan_τ_p). }
      wp_pures.
      iApply ("IH_inner" $! (i_iter - 1)%Z (Nat.succ (Z.to_nat j))
                with "[%] [%] Hstat_τ Hscan_τ HΦ").
      { lia. }
      { destruct Hj_bounds as [Hj_ge _].
        rewrite Nat2Z.inj_succ Z2Nat.id; last exact Hj_ge.
        unfold j. lia. }
  Qed.

End proof.
