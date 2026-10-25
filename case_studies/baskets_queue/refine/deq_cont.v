(* refine_deq_cont.v: proof of [op_spec_deq_cont] — the dequeue
  branch of [op_spec] for the Baskets Queue.

  ** What this lemma will eventually prove.
  Given a thread holding the [op_info] fragment for a fresh
  [OpDeq [] rng_init] identifier [τ], the WP runs the impl-level
  [dequeue] body and then [trace_emit]s the dequeue's [Ret].

  The dequeue is where the *future-dependent linearisation points*
  of the matching basket enqueues are fixed.  At each successful
  mark-CAS:
    - one node [(l_e, τ_e, d)] is dequeued from the unmarked head of
      the chain;
    - the AbsQ transition fired is [absq_step_lin_deq1], which
      requires [τ_e ∈ absq_min absq_O absq_lt] — the dequeued node's
      enqueue must be *minimal* under the happens-before relation.
      The proof of minimality uses the [bq_sim] clause "[absq_lt]
      respects list order": any [absq_lt]-predecessor [k] of [τ_e]
      must already have left [absq_O] via an earlier dequeue, since
      its node would otherwise lie strictly closer to head than
      [l_e] in the unmarked-suffix and the dequeue's [walk] would
      have stopped there first;
    - the same CAS additionally records [τ]'s return value in
      [dq_map], which propagates through to [absq_rv] for the final
      [trace_emit] of [Ret] via the [dq_inv] clause.

  Empty-queue dequeue: when the [walk] reaches the tail with every
  intermediate next-pointer marked, [absq_step_lin_deq2] fires.
  Its precondition (every enqueue still in [absq_O] is [PEND]) is
  discharged by the dequeue-observation invariant, exactly as in
  HWQ (every storer the walk passed over has been dequeued, so any
  surviving [absq_O] members are pre-link enqueues that have not
  yet committed their [LIN-ENQ]-equivalent).

  The marked-prefix walk's recursion is factored into
  [op_spec_deq_walk] in [refine_deq_walk.v]; this file
  handles the outer retry loop, Phase 1/2 loads, the LIN-DEQ1
  mark-CAS for an immediate empty-or-singleton walk start, and
  the LIN-DEQ2 empty branch. *)

From iris.algebra Require Import auth excl gmap gset agree mono_nat mono_list.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.baskets_queue Require Import impl refine.defs refine.deq_trace refine.deq_walk.

Section bq_skeleton_deq_cont.
  Context `{!traceG Σ, !bqG Σ}.

  Local Notation valid_value := bq_valid_value.
  Local Notation Nbq := Nbq.
  Local Notation bq_inv_body := bq_inv_body.
  Local Notation is_bq := is_bq.

  Lemma op_spec_deq_cont
    `{!heapGS Σ} (γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w : gname) (l head tail : loc)
    (τ : positive) (rng_init : nat) (Φ : val → iProp Σ) :
    inv Nbq (bq_inv_body γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w head tail l) -∗
    trace_inv l (I_lang_bq) -∗
    own γ (◯ {[τ := Excl {| op_info_kind := OpDeq [] rng_init;
                            op_info_node := None;
                            op_info_linked := false |}]}) -∗
    (∀ v : val, True -∗ Φ v) -∗
    WP (let: "τ" := #(Z.pos τ) in
        let: "res" := (λ: "q" <>, dequeue "q")%V (#head, #tail)%V #() in
        trace_emit #l "τ" (InjR "res");; "res")
    {{ Φ }}.
  Proof.
    iIntros "#Hinv #Htrace_inv Hfrag HΦ".
    wp_pures.
    rewrite /dequeue. wp_pures.
    iLöb as "IH".
    wp_pures.

    (* Phase 1: load [head].  No AbsQ step.  Extract three persistent
       witnesses needed at phase 2:
       - [Hhead_frag]: [node_map !! head_val = Some (τ_h, v_h)],
         re-establishes "[head_val] is in the chain" across inv
         close/reopen;
       - [Hdel_lb]: [del_pref ≥ i_h] (mono_nat lower bound) — combined
         with [Hcalls_frag], lifts "[τ_h ∉ absq_O]" to phase 2;
       - [Hcalls_frag]: [τ_h ∈ dom absq_cp] (or [τ_h = 1] for the
         dummy) — together with [absq_steps_O_sticky], propagates
         "[τ_h ∉ absq_O]" forward. *)
    wp_bind (! _)%E.
    iInv Nbq as (nodes del_pref head_val tail_val dummy_loc ts s ls op_map node_map dq_map no_O_set witness_map)
      "(>Hhead & >Htail & Hchain & >Htrace & >Hauth_op & >Hauth_nm & Hfrag_nm
        & >Hauth_dq & Hfrag_dq & >Hauth_del & >Hauth_calls & >Hauth_no_O & >Hauth_ls & >Hauth_w & Hfrag_w
        & >%Hsteps & >%Hts_eq & >%Hsim
        & >%Hdummy & >%Hnvi & >%Hdqi & >%Hno_O_inv & >%Hcoi & >%Hwit)".
    wp_load.
    destruct Hsim as (Hlen & Hdel & Hcp_in_ts & Hdomsub & Hnm_dom & Henq_clause
                     & Hdeq_clause & Hinj & Hcorr & Hlt_pos & _Htbd & Hcomp_link
                     & Htail_in & Hhead_in & Hnm_chain & Hsome_at_pos).
    destruct Hhead_in as (i_h & τ_h_opt & v_h & Hi_h_le & Hhead_at).
    pose proof (Hnm_chain _ _ _ _ Hhead_at) as Hnm_head.
    (* (a) persistent node_map frag for head_val. *)
    iDestruct (own_mono _ _ (◯ {[head_val := to_agree ((τ_h_opt, v_h) : leibnizO node_info)]})
                with "Hfrag_nm") as "#Hhead_frag".
    { apply auth_frag_mono. rewrite /to_nodemap.
      apply (proj2 (singleton_included_l _ _ _)).
      exists (to_agree ((τ_h_opt, v_h) : leibnizO node_info)). split.
      - rewrite lookup_fmap Hnm_head //=.
      - reflexivity. }
    (* (b) persistent del_pref lb of i_h. *)
    iEval (rewrite mono_nat_auth_lb_op) in "Hauth_del".
    iDestruct "Hauth_del" as "[Hauth_del #Hdel_lb_full]".
    iAssert (own γ_del (◯MN i_h)) as "#Hdel_lb".
    { iApply (own_mono with "Hdel_lb_full"). by apply mono_nat_lb_mono. }
    (* (c) persistent γ_calls frag for τ_h_real (when [τ_h_opt = Some τ_h_real]).
       For the dummy (i_h = 0, τ_h_opt = None), no frag needed. *)
    iMod (own_update _ _ (● dom s.(absq_cp) ⋅ ◯ dom s.(absq_cp))
            with "Hauth_calls") as "[Hauth_calls #Hcalls_dom]".
    { apply auth_update_dfrac_alloc.
      - apply _.
      - apply gset_included. clear; set_solver. }
    (* (c') persistent γ_no_O frag for τ_h_real (non-dummy case).  The
       update adds [τ_h_real] to [no_O_set] and extracts a persistent
       fragment.  In the dummy case the update is trivial: it adds [∅]
       and the fragment is also [∅]. *)
    set (extra_no_O := match τ_h_opt with
                       | Some t => {[t]} : gset positive
                       | None => ∅
                       end).
    assert (extra_no_O ⊆ dom s.(absq_cp) ∖ s.(absq_O)) as Hextra_no_O_sub.
    { subst extra_no_O. destruct τ_h_opt as [τ_h_real|]; last (clear; set_solver).
      destruct (decide (i_h = 0%nat)) as [Hi_zero|Hi_pos].
      - (* If i_h = 0, by Hdummy chain[0] = (dummy_loc, None, _).  But here
           we have nodes !! 0 = Some (head_val, Some τ_h_real, v_h), which
           by Hdummy contradicts None ≠ Some.  So [extra_no_O ⊆ ∅]
           vacuously by contradiction in the antecedent.  *)
        exfalso. subst i_h. rewrite Hdummy in Hhead_at.
        injection Hhead_at as _ Habs _. discriminate.
      - assert (1 ≤ i_h)%nat as Hi_h_pos by lia.
        destruct (Hcorr _ _ _ _ Hi_h_pos Hhead_at) as (_ & (f & Hℓ_τ_h) & Hin_iff).
        destruct s as [O_s lt_s l_s rv_s cp_s]; simpl in *.
        pose proof (absq_wf_steps _ _ _ _ _ Hsteps (absq_wf_init _)) as Hwf.
        pose proof (absq_wf_dom _ _ Hwf) as Hwf_dom. simpl in Hwf_dom.
        assert (τ_h_real ∈ dom l_s) as Hin_l
          by (apply elem_of_dom; by exists (v_h, f)).
        rewrite elem_of_subseteq. intros x Hx.
        rewrite elem_of_singleton in Hx. subst x.
        rewrite elem_of_difference. split.
        + clear -Hwf_dom Hin_l. set_solver.
        + rewrite Hin_iff. lia. }
    iMod (own_update _ _
            (● (no_O_set ∪ extra_no_O : gsetUR positive) ⋅ ◯ (no_O_set ∪ extra_no_O : gsetUR positive)
              : authR (gsetUR positive))
            with "Hauth_no_O") as "[Hauth_no_O #Hno_O_full]".
    { apply auth_update_alloc, gset_local_update. clear; set_solver. }
    iAssert (own γ_no_O (◯ (extra_no_O : gsetUR positive))) as "#Hno_O_frag".
    { iApply (own_mono with "Hno_O_full").
      apply auth_frag_mono. apply gset_included. clear; set_solver. }
    iClear "Hno_O_full".
    iAssert (⌜τ_h_opt = None ∧ i_h = 0%nat⌝ ∨
             ∃ τ_h_real, ⌜τ_h_opt = Some τ_h_real ∧ (1 ≤ i_h)%nat⌝ ∗
                          own γ_calls (◯ ({[τ_h_real]} : gsetUR positive)))%I
      as "#Hcalls_frag".
    { destruct (decide (i_h = 0%nat)) as [Hi_zero|Hi_pos].
      - (* Dummy case: i_h = 0, by Hdummy chain[0] is the dummy with None tag. *)
        subst i_h. rewrite Hdummy in Hhead_at. injection Hhead_at as -> -> _.
        iLeft. done.
      - (* Non-dummy: i_h ≥ 1.  By Hsome_at_pos, τ_h_opt = Some τ_h_real.
           Then by Hcorr, τ_h_real ∈ dom absq_l, hence in dom absq_cp.
           Extract γ_calls fragment. *)
        iRight.
        assert (1 ≤ i_h)%nat as Hi_h_pos by lia.
        destruct (Hsome_at_pos _ _ _ _ Hi_h_pos Hhead_at) as [τ_h_real ->].
        iExists τ_h_real. iSplit; first done.
        iApply (own_mono with "Hcalls_dom").
        apply auth_frag_mono. apply gset_included.
        intros x. rewrite elem_of_singleton. intros ->.
        destruct (Hcorr _ _ _ _ Hi_h_pos Hhead_at) as (_ & (f & Hℓ_τ_h) & _).
        destruct s as [O_s lt_s l_s rv_s cp_s]; simpl in *.
        pose proof (absq_wf_steps _ _ _ _ _ Hsteps (absq_wf_init _)) as Hwf.
        pose proof (absq_wf_dom _ _ Hwf) as Hwf_dom. simpl in Hwf_dom.
        assert (τ_h_real ∈ dom l_s) as Hin_l by (apply elem_of_dom; by exists (v_h, f)).
        clear -Hwf_dom Hin_l. set_solver. }
    (* (d) Persistent prefix witness for [ls]. *)
    iDestruct (own_mono _ _ (◯ML (ls : list (leibnizO (positive * absq_action))))
                with "Hauth_ls") as "#Hls_lb".
    { apply mono_list_included. }
    (* Phase-1 Coq fact: encapsulate the trajectory and the dom/¬∈
       witnesses about τ_h_real (only meaningful for the non-dummy case). *)
    iAssert (⌜∃ s_1, rtcL (absq_step MayEmpty valid_value) absq_init s_1 ls ∧
                     (∀ τ_h_real, τ_h_opt = Some τ_h_real → (1 ≤ i_h)%nat →
                       τ_h_real ∈ dom s_1.(absq_cp) ∧ τ_h_real ∉ s_1.(absq_O))⌝)%I
      as "#Hphase1".
    { iPureIntro. exists s. split; first exact Hsteps.
      intros τ_h_real Hτ_eq Hi_pos.
      assert (nodes !! i_h = Some (head_val, Some τ_h_real, v_h)) as Hhead_at_some
        by (rewrite Hτ_eq in Hhead_at; exact Hhead_at).
      destruct (Hcorr _ _ _ _ Hi_pos Hhead_at_some) as (_ & (f & Hℓ_τ_h) & Hin_iff).
      split.
      - destruct s as [O_s lt_s l_s rv_s cp_s]; simpl in *.
        pose proof (absq_wf_steps _ _ _ _ _ Hsteps (absq_wf_init _)) as Hwf.
        pose proof (absq_wf_dom _ _ Hwf) as Hwf_dom. simpl in Hwf_dom.
        assert (τ_h_real ∈ dom l_s) as Hin_l by (apply elem_of_dom; by exists (v_h, f)).
        clear -Hwf_dom Hin_l. set_solver.
      - rewrite Hin_iff. lia. }
    iModIntro.
    iSplitL "Hhead Htail Hchain Htrace Hauth_op Hauth_nm Hfrag_nm Hauth_dq Hfrag_dq Hauth_del Hauth_calls Hauth_no_O Hauth_ls Hauth_w Hfrag_w".
    { iNext. iExists nodes, del_pref, head_val, tail_val, dummy_loc, ts, s, ls,
        op_map, node_map, dq_map, (no_O_set ∪ extra_no_O).
      iFrame. iPureIntro. split_and!; auto.
      - repeat split_and!; auto. exists i_h, τ_h_opt, v_h. split; auto.
      - destruct Hno_O_inv as [Hsub _]. clear -Hsub Hextra_no_O_sub. set_solver.
      - destruct Hno_O_inv as [_ Hdisj]. clear -Hdisj Hextra_no_O_sub. set_solver. }
    wp_pures.

    (* PHASE 2: load [head_val.next].  This is the LP for the empty
       case (LIN-DEQ2).  Open the invariant, locate [head_val] in
       [chain_2] via the persistent [Hhead_frag], extract the
       next-cell via [bq_chain_lookup_acc], [wp_load], case-split on
       [(mark_at, succ_at)].  In the empty case [(false, None)] we
       fire [absq_step_lin_deq2] inside the same inv-open and propagate
       the new abstract state; the [(true, Some)] marked-pointer case
       hands off to [op_spec_deq_walk]; the [(false, Some)]
       mark-CAS case fires LIN-DEQ1 directly. *)
    wp_bind (! _)%E.
    iInv Nbq as (nodes_2 del_pref_2 head_val_2 tail_val_2 dummy_loc_2 ts_2 s_2 ls_2
                 op_map_2 node_map_2 dq_map_2 no_O_set_2 witness_map_2)
      "(>Hhead2 & >Htail2 & Hchain2 & >Htrace2 & >Hauth_op2 & >Hauth_nm2 & Hfrag_nm2
        & >Hauth_dq2 & Hfrag_dq2 & >Hauth_del2 & >Hauth_calls2 & >Hauth_no_O2 & >Hauth_ls2 & >Hauth_w2 & Hfrag_w2
        & >%Hsteps2 & >%Hts_eq2 & >%Hsim2 & >%Hdummy2 & >%Hnvi2 & >%Hdqi2 & >%Hno_O_inv2 & >%Hcoi2 & >%Hwit2)".
    (* Find [head_val]'s chain_2 position via [Hhead_frag] agreement. *)
    iDestruct (own_valid_2 with "Hauth_nm2 Hhead_frag") as %Hnm_agree.
    apply auth_both_valid_discrete in Hnm_agree as [Hincl _].
    apply singleton_included_l in Hincl as (av & Hav_lookup & Hav_incl).
    rewrite /to_nodemap lookup_fmap in Hav_lookup.
    apply fmap_Some_equiv in Hav_lookup as (info_2 & Hnm2_lookup & Hav_eq).
    rewrite Hav_eq in Hav_incl. rewrite Some_included in Hav_incl.
    assert ((τ_h_opt, v_h) = info_2 :> leibnizO node_info) as Hinfo_2_eq.
    { destruct Hav_incl as [Heq|Hincl_eq].
      - by apply (inj to_agree), leibniz_equiv in Heq.
      - rewrite to_agree_included in Hincl_eq. by apply leibniz_equiv. }
    rewrite -Hinfo_2_eq in Hnm2_lookup. clear Hav_eq Hav_incl Hinfo_2_eq info_2.
    pose proof Hsim2 as (Hlen2 & Hdel2 & Hcp_in_ts2 & Hdomsub2 & Hnm_dom2 & Henq_clause2
                       & Hdeq_clause2 & Hinj2 & Hcorr2 & Hlt_pos2 & _Htbd2 & Hcomp_link2
                       & Htail_in2 & Hhead_in2 & Hnm_chain2 & Hsome_at_pos2).
    destruct (Hnm_dom2 _ _ _ Hnm2_lookup) as (i_2 & Hi_2_lookup).
    (* Extract [head_val]'s next-cell. *)
    iDestruct (bq_chain_lookup_acc _ del_pref_2 i_2 head_val τ_h_opt v_h Hi_2_lookup
                with "Hchain2") as "[Hv2 [Hn2 HW2]]".
    wp_load.
    (* Case-split on the loaded value via [(mark_at, succ_at)]. *)
    destruct (mark_at del_pref_2 i_2) eqn:Hmark_2;
    destruct (succ_at nodes_2 i_2) as [l_succ_2|] eqn:Hsucc_2.
    - (* (true, Some l_succ_2): marked-pointer.  Walk forward case.
         Derive l_succ_2's persistent γ_nm fragment + γ_no_O for
         τ_succ_2, then close inv and hand off to
         [op_spec_deq_walk]. *)
      rewrite /succ_at in Hsucc_2.
      destruct (nodes_2 !! (i_2 + 1)%nat) as [[[lk_succ_2 τ_succ_2_opt] v_succ_2]|]
        eqn:Hnext_lookup_2; last discriminate.
      simpl in Hsucc_2. injection Hsucc_2 as ->.
      assert (Hi_succ_2_pos : (1 ≤ i_2 + 1)%nat) by lia.
      destruct (Hsome_at_pos2 _ _ _ _ Hi_succ_2_pos Hnext_lookup_2)
        as [τ_succ_2 ->].
      pose proof (Hnm_chain2 _ _ _ _ Hnext_lookup_2) as Hnm_l_succ_2.
      iDestruct (own_mono _ _ (◯ {[l_succ_2 := to_agree
                  ((Some τ_succ_2, v_succ_2) : leibnizO node_info)]})
                  with "Hfrag_nm2") as "#Hl_succ_frag".
      { apply auth_frag_mono. rewrite /to_nodemap.
        apply (proj2 (singleton_included_l _ _ _)).
        exists (to_agree ((Some τ_succ_2, v_succ_2) : leibnizO node_info)). split.
        - rewrite lookup_fmap Hnm_l_succ_2 //=.
        - reflexivity. }
      (* Derive del_pref_2 ≥ i_2 + 1 from mark_at_2 = true. *)
      rewrite /mark_at in Hmark_2.
      apply bool_decide_eq_true in Hmark_2.
      (* Alloc γ_no_O for τ_succ_2: τ_succ_2 ∉ O via clause 9. *)
      destruct (Hcorr2 _ _ _ _ Hi_succ_2_pos Hnext_lookup_2)
        as (_ & (f_τ_succ_2 & Hℓ_τ_succ_2) & Hin_iff_τ_succ_2).
      assert (τ_succ_2 ∉ s_2.(absq_O)) as Hτ_succ_2_not_O.
      { intros Habs. apply Hin_iff_τ_succ_2 in Habs. lia. }
      assert (τ_succ_2 ∈ dom s_2.(absq_cp)) as Hτ_succ_2_in_cp.
      { pose proof (absq_wf_steps _ _ _ _ _ Hsteps2 (absq_wf_init _)) as Hwf2.
        apply (absq_wf_dom _ _ Hwf2).
        apply elem_of_dom. by exists (v_succ_2, f_τ_succ_2). }
      iMod (own_update _ _
              (● (no_O_set_2 ∪ {[τ_succ_2]} : gsetUR positive)
                 ⋅ ◯ (no_O_set_2 ∪ {[τ_succ_2]} : gsetUR positive)
                : authR (gsetUR positive))
              with "Hauth_no_O2") as "[Hauth_no_O2 #Hno_O_full_τ_succ_2]".
      { apply auth_update_alloc, gset_local_update.
        apply union_subseteq_l. }
      iAssert (own γ_no_O (◯ ({[τ_succ_2]} : gsetUR positive)))
        as "#Hno_O_τ_succ_2_frag".
      { iApply (own_mono with "Hno_O_full_τ_succ_2").
        apply auth_frag_mono. apply gset_included.
        apply union_subseteq_r. }
      iClear "Hno_O_full_τ_succ_2".
      iDestruct ("HW2" with "[$Hv2 $Hn2]") as "Hchain2".
      iModIntro.
      iSplitL "Hhead2 Htail2 Hchain2 Htrace2 Hauth_op2 Hauth_nm2 Hfrag_nm2
               Hauth_dq2 Hfrag_dq2 Hauth_del2 Hauth_calls2 Hauth_no_O2
               Hauth_ls2 Hauth_w2 Hfrag_w2".
      { iNext. iExists nodes_2, del_pref_2, head_val_2, tail_val_2, dummy_loc_2,
          ts_2, s_2, ls_2, op_map_2, node_map_2, dq_map_2,
          (no_O_set_2 ∪ {[τ_succ_2]}), witness_map_2.
        iFrame. iPureIntro. split_and!; auto.
        - destruct Hno_O_inv2 as [Hsub _].
          assert (τ_succ_2 ∈ dom s_2.(absq_cp) ∖ s_2.(absq_O))
            as Hτ_succ_2_diff
            by (rewrite elem_of_difference; split; assumption).
          clear -Hsub Hτ_succ_2_diff. set_solver.
        - destruct Hno_O_inv2 as [_ Hdisj].
          clear -Hdisj Hτ_succ_2_not_O. set_solver. }
      wp_pures.
      (* The wp_pures reduced past the outer rec applied + walk's
         match dispatch on InjRV #l_succ_2.  We're now at the
         next-iteration's load: [let next2 := !(l_succ_2 +ₗ 1) in
         walk l_succ_2 next2].  Open inv to load l_succ_2.next, then
         dispatch on its (mark_at, succ_at) at l_succ_2's chain pos.
         In each case, build the appropriate Hnext disjunct + iApply
         the walk lemma with iter := l_succ_2. *)
      wp_bind (! _)%E.
      iInv Nbq as (nodes_3 del_pref_3 head_val_3 tail_val_3 dummy_loc_3 ts_3 s_3 ls_3
                   op_map_3 node_map_3 dq_map_3 no_O_set_3 witness_map_3)
        "(>Hhead3 & >Htail3 & Hchain3 & >Htrace3 & >Hauth_op3 & >Hauth_nm3 & Hfrag_nm3
          & >Hauth_dq3 & Hfrag_dq3 & >Hauth_del3 & >Hauth_calls3 & >Hauth_no_O3 & >Hauth_ls3 & >Hauth_w3 & Hfrag_w3
          & >%Hsteps3 & >%Hts_eq3 & >%Hsim3 & >%Hdummy3 & >%Hnvi3 & >%Hdqi3 & >%Hno_O_inv3 & >%Hcoi3 & >%Hwit3)".
      (* Find l_succ_2's position in chain_3. *)
      iDestruct (own_valid_2 with "Hauth_nm3 Hl_succ_frag") as %Hagree_3.
      apply auth_both_valid_discrete in Hagree_3 as [Hincl_3 _].
      apply singleton_included_l in Hincl_3 as (av_3 & Hav_lookup_3 & Hav_incl_3).
      rewrite /to_nodemap lookup_fmap in Hav_lookup_3.
      apply fmap_Some_equiv in Hav_lookup_3 as (info_3 & Hnm3_l_succ & Hav_eq_3).
      rewrite Hav_eq_3 in Hav_incl_3. rewrite Some_included in Hav_incl_3.
      assert ((Some τ_succ_2, v_succ_2) = info_3 :> leibnizO node_info) as Hinfo_3_eq.
      { destruct Hav_incl_3 as [Heq|Hin].
        - by apply (inj to_agree), leibniz_equiv in Heq.
        - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
      rewrite -Hinfo_3_eq in Hnm3_l_succ.
      clear Hav_eq_3 Hav_incl_3 Hinfo_3_eq info_3.
      pose proof Hsim3 as (_ & _ & _ & _ & Hnm_dom3 & _ & _ & _ & Hcorr3 & _ & _ & _ & _ & _ & Hnm_chain3 & Hsome_at_pos3).
      destruct (Hnm_dom3 _ _ _ Hnm3_l_succ) as (i_succ_3 & Hi_succ_3_lookup).
      assert (1 ≤ i_succ_3)%nat as Hi_succ_3_pos.
      { destruct (decide (1 ≤ i_succ_3)%nat) as [|Hlt]; first done.
        assert (i_succ_3 = 0%nat) as -> by lia.
        rewrite Hdummy3 in Hi_succ_3_lookup.
        injection Hi_succ_3_lookup as _ Habs _. discriminate. }
      iDestruct (bq_chain_lookup_acc _ del_pref_3 i_succ_3 l_succ_2
                   (Some τ_succ_2) v_succ_2 Hi_succ_3_lookup
                   with "Hchain3") as "[Hv3 [Hn3 HW3]]".
      simpl. wp_load.
      iDestruct ("HW3" with "[$Hv3 $Hn3]") as "Hchain3".
      (* Derive del_pref_3 ≥ i_succ_3 via Hno_O_τ_succ_2_frag. *)
      iDestruct (own_valid_2 with "Hauth_no_O3 Hno_O_τ_succ_2_frag") as %Hno_O_both3.
      apply auth_both_valid_discrete in Hno_O_both3 as [Hno_O_incl3 _].
      apply gset_included in Hno_O_incl3.
      assert (τ_succ_2 ∈ no_O_set_3) as Hτ_succ_in_no_O_3
        by (clear -Hno_O_incl3; set_solver).
      assert (τ_succ_2 ∉ s_3.(absq_O)) as Hτ_succ_2_not_O_3
        by (destruct Hno_O_inv3 as [_ Hdisj]; clear -Hdisj Hτ_succ_in_no_O_3; set_solver).
      destruct (Hcorr3 _ _ _ _ Hi_succ_3_pos Hi_succ_3_lookup) as (_ & _ & Hin_iff_3).
      assert (i_succ_3 ≤ del_pref_3)%nat as Hdel_ge_i_succ_3.
      { destruct (decide (del_pref_3 < i_succ_3)%nat) as [Hlt|]; last lia.
        exfalso. apply Hτ_succ_2_not_O_3. by apply Hin_iff_3. }
      iEval (rewrite mono_nat_auth_lb_op) in "Hauth_del3".
      iDestruct "Hauth_del3" as "[Hauth_del3 #Hdel_lb_full_3]".
      iAssert (own γ_del (◯MN i_succ_3)) as "#Hdel_lb_succ_3".
      { iApply (own_mono with "Hdel_lb_full_3").
        apply mono_nat_lb_mono. lia. }
      (* Dispatch on (mark_at del_pref_3 i_succ_3, succ_at nodes_3 i_succ_3). *)
      destruct (mark_at del_pref_3 i_succ_3) eqn:Hmark_3;
      destruct (succ_at nodes_3 i_succ_3) as [l_succ_3|] eqn:Hsucc_3.
      + (* (true, Some l_succ_3): walk recurses; build Case A disjunct
           with γ_no_O for τ_succ_3. *)
        rewrite /succ_at in Hsucc_3.
        destruct (nodes_3 !! (i_succ_3 + 1)%nat) as [[[lk τ_l_opt] v_l]|]
          eqn:Hnext_lookup_3; last discriminate.
        simpl in Hsucc_3. injection Hsucc_3 as ->.
        assert (Hi_l_pos : (1 ≤ i_succ_3 + 1)%nat) by lia.
        destruct (Hsome_at_pos3 _ _ _ _ Hi_l_pos Hnext_lookup_3) as [τ_l_succ_3 ->].
        pose proof (Hnm_chain3 _ _ _ _ Hnext_lookup_3) as Hnm_l_succ_3.
        iDestruct (own_mono _ _ (◯ {[l_succ_3 := to_agree
                    ((Some τ_l_succ_3, v_l) : leibnizO node_info)]})
                    with "Hfrag_nm3") as "#Hl_succ_3_frag".
        { apply auth_frag_mono. rewrite /to_nodemap.
          apply (proj2 (singleton_included_l _ _ _)).
          exists (to_agree ((Some τ_l_succ_3, v_l) : leibnizO node_info)). split.
          - rewrite lookup_fmap Hnm_l_succ_3 //=.
          - reflexivity. }
        rewrite /mark_at in Hmark_3.
        apply bool_decide_eq_true in Hmark_3.
        destruct (Hcorr3 _ _ _ _ Hi_l_pos Hnext_lookup_3)
          as (_ & (f_τ_l_succ & Hℓ_τ_l_succ) & Hin_iff_τ_l).
        assert (τ_l_succ_3 ∉ s_3.(absq_O)) as Hτ_l_succ_3_not_O.
        { intros Habs. apply Hin_iff_τ_l in Habs. lia. }
        assert (τ_l_succ_3 ∈ dom s_3.(absq_cp)) as Hτ_l_succ_3_in_cp.
        { pose proof (absq_wf_steps _ _ _ _ _ Hsteps3 (absq_wf_init _)) as Hwf3.
          apply (absq_wf_dom _ _ Hwf3).
          apply elem_of_dom. by exists (v_l, f_τ_l_succ). }
        iMod (own_update _ _
                (● (no_O_set_3 ∪ {[τ_l_succ_3]} : gsetUR positive)
                   ⋅ ◯ (no_O_set_3 ∪ {[τ_l_succ_3]} : gsetUR positive)
                  : authR (gsetUR positive))
                with "Hauth_no_O3") as "[Hauth_no_O3 #Hno_O_full_τ_l]".
        { apply auth_update_alloc, gset_local_update.
          apply union_subseteq_l. }
        iAssert (own γ_no_O (◯ ({[τ_l_succ_3]} : gsetUR positive)))
          as "#Hno_O_τ_l_succ_3_frag".
        { iApply (own_mono with "Hno_O_full_τ_l").
          apply auth_frag_mono. apply gset_included.
          apply union_subseteq_r. }
        iClear "Hno_O_full_τ_l".
        iModIntro.
        iSplitL "Hhead3 Htail3 Hchain3 Htrace3 Hauth_op3 Hauth_nm3 Hfrag_nm3
                 Hauth_dq3 Hfrag_dq3 Hauth_del3 Hauth_calls3 Hauth_no_O3
                 Hauth_ls3 Hauth_w3 Hfrag_w3".
        { iNext. iExists nodes_3, del_pref_3, head_val_3, tail_val_3, dummy_loc_3,
            ts_3, s_3, ls_3, op_map_3, node_map_3, dq_map_3,
            (no_O_set_3 ∪ {[τ_l_succ_3]}), witness_map_3.
          iFrame. iPureIntro. split_and!; auto.
          - destruct Hno_O_inv3 as [Hsub _].
            assert (τ_l_succ_3 ∈ dom s_3.(absq_cp) ∖ s_3.(absq_O)) as Hτ_l_diff
              by (rewrite elem_of_difference; split; assumption).
            clear -Hsub Hτ_l_diff. set_solver.
          - destruct Hno_O_inv3 as [_ Hdisj].
            clear -Hdisj Hτ_l_succ_3_not_O. set_solver. }
        cbn [next_value_of].
        wp_let.
        wp_bind ((rec: "walk" "iter" "next" := _)%V _ _).
        (* Build Houter explicitly from IH so it has the exact shape
           the lemma expects.  This avoids iApply's confusion when
           specializing the ▷-protected outer-recursion hypothesis. *)
        iAssert
          (▷ (own γ (◯ {[τ := Excl {| op_info_kind := OpDeq [] rng_init;
                                       op_info_node := None;
                                       op_info_linked := false |}]}) -∗
              (∀ v : val, True -∗ Φ v) -∗
              WP (rec: "outer" <> :=
                    let: "head1" := !#head in
                    let: "next" := !("head1" +ₗ #1) in
                    (rec: "walk" "iter" "next" :=
                       match: "next" with
                         InjL "p" =>
                           if: "p" = #() then InjL #()
                           else
                             let: "v" := !"p" in
                             if: Snd (CmpXchg ("iter" +ₗ #1) "next" (InjR "p"))
                             then Snd (CmpXchg #head "head1" "p");; InjR "v"
                             else "outer" #()
                       | InjR "p" =>
                           if: "p" = #() then "outer" #()
                           else
                             let: "next2" := !("p" +ₗ #1) in
                             "walk" "p" "next2"
                       end) "head1" "next")%V #()
              {{ deq_walk_cont l τ Φ }}))%I as "Houter".
        { iNext. iIntros "Hfrag2 HΦ2".
          wp_pures.
          rewrite /deq_walk_cont.
          iApply (wp_bind_inv
                    (fill [AppRCtx (λ: "res",
                            trace_emit #l #(Z.pos τ) (InjR "res");; "res")%E])).
          simpl. iApply ("IH" with "Hfrag2 HΦ2"). }
        iApply (op_spec_deq_walk
                  γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                  l head tail
                  head_val l_succ_2
                  τ_h_opt v_h
                  (Some τ_succ_2) v_succ_2
                  τ rng_init i_succ_3
                  (InjRV #l_succ_3) extra_no_O
                  (rec: "outer" <> :=
                     let: "head1" := !#head in
                     let: "next" := !("head1" +ₗ #1) in
                     (rec: "walk" "iter" "next" :=
                        match: "next" with
                          InjL "p" =>
                            if: "p" = #() then InjL #()
                            else
                              let: "v" := !"p" in
                              if: Snd (CmpXchg ("iter" +ₗ #1) "next" (InjR "p"))
                              then Snd (CmpXchg #head "head1" "p");; InjR "v"
                              else "outer" #()
                        | InjR "p" =>
                            if: "p" = #() then "outer" #()
                            else
                              let: "next2" := !("p" +ₗ #1) in
                              "walk" "p" "next2"
                        end) "head1" "next")%V
                  Φ
                  with "Hinv Htrace_inv Hfrag Hhead_frag Hl_succ_frag
                        Hno_O_frag [//] [] Hdel_lb_succ_3 [] Houter HΦ").
        { iRight. iExists τ_succ_2. iSplit; first done.
          iApply "Hno_O_τ_succ_2_frag". }
        { iRight. iRight.
          iExists τ_l_succ_3, l_succ_3, v_l. iSplit; first done.
          iSplit.
          - iApply "Hl_succ_3_frag".
          - iApply "Hno_O_τ_l_succ_3_frag". }
      + (* (true, None): impossible. *)
        exfalso.
        rewrite /mark_at in Hmark_3.
        apply bool_decide_eq_true in Hmark_3.
        rewrite /succ_at in Hsucc_3.
        destruct (nodes_3 !! (i_succ_3 + 1)%nat) eqn:Hnext_3; first discriminate.
        apply lookup_ge_None_1 in Hnext_3.
        pose proof Hsim3 as (_ & Hdel3 & _).
        lia.
      + (* (false, Some l_succ_3): build Case B disjunct. *)
        rewrite /succ_at in Hsucc_3.
        destruct (nodes_3 !! (i_succ_3 + 1)%nat) as [[[lk τ_l_opt] v_l]|]
          eqn:Hnext_lookup_3; last discriminate.
        simpl in Hsucc_3. injection Hsucc_3 as ->.
        assert (Hi_l_pos : (1 ≤ i_succ_3 + 1)%nat) by lia.
        destruct (Hsome_at_pos3 _ _ _ _ Hi_l_pos Hnext_lookup_3) as [τ_l_succ_3 ->].
        pose proof (Hnm_chain3 _ _ _ _ Hnext_lookup_3) as Hnm_l_succ_3.
        iDestruct (own_mono _ _ (◯ {[l_succ_3 := to_agree
                    ((Some τ_l_succ_3, v_l) : leibnizO node_info)]})
                    with "Hfrag_nm3") as "#Hl_succ_3_frag".
        { apply auth_frag_mono. rewrite /to_nodemap.
          apply (proj2 (singleton_included_l _ _ _)).
          exists (to_agree ((Some τ_l_succ_3, v_l) : leibnizO node_info)). split.
          - rewrite lookup_fmap Hnm_l_succ_3 //=.
          - reflexivity. }
        iModIntro.
        iSplitL "Hhead3 Htail3 Hchain3 Htrace3 Hauth_op3 Hauth_nm3 Hfrag_nm3
                 Hauth_dq3 Hfrag_dq3 Hauth_del3 Hauth_calls3 Hauth_no_O3
                 Hauth_ls3 Hauth_w3 Hfrag_w3".
        { iNext. iExists nodes_3, del_pref_3, head_val_3, tail_val_3, dummy_loc_3,
            ts_3, s_3, ls_3, op_map_3, node_map_3, dq_map_3, no_O_set_3, witness_map_3.
          iFrame. iPureIntro. split_and!; auto.
          - apply Hno_O_inv3.
          - apply Hno_O_inv3. }
        cbn [next_value_of].
        wp_let.
        wp_bind ((rec: "walk" "iter" "next" := _)%V _ _).
        iAssert
          (▷ (own γ (◯ {[τ := Excl {| op_info_kind := OpDeq [] rng_init;
                                       op_info_node := None;
                                       op_info_linked := false |}]}) -∗
              (∀ v : val, True -∗ Φ v) -∗
              WP (rec: "outer" <> :=
                    let: "head1" := !#head in
                    let: "next" := !("head1" +ₗ #1) in
                    (rec: "walk" "iter" "next" :=
                       match: "next" with
                         InjL "p" =>
                           if: "p" = #() then InjL #()
                           else
                             let: "v" := !"p" in
                             if: Snd (CmpXchg ("iter" +ₗ #1) "next" (InjR "p"))
                             then Snd (CmpXchg #head "head1" "p");; InjR "v"
                             else "outer" #()
                       | InjR "p" =>
                           if: "p" = #() then "outer" #()
                           else
                             let: "next2" := !("p" +ₗ #1) in
                             "walk" "p" "next2"
                       end) "head1" "next")%V #()
              {{ deq_walk_cont l τ Φ }}))%I as "Houter".
        { iNext. iIntros "Hfrag2 HΦ2".
          wp_pures.
          rewrite /deq_walk_cont.
          iApply (wp_bind_inv
                    (fill [AppRCtx (λ: "res",
                            trace_emit #l #(Z.pos τ) (InjR "res");; "res")%E])).
          simpl. iApply ("IH" with "Hfrag2 HΦ2"). }
        iApply (op_spec_deq_walk
                  γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                  l head tail
                  head_val l_succ_2
                  τ_h_opt v_h
                  (Some τ_succ_2) v_succ_2
                  τ rng_init i_succ_3
                  (InjLV #l_succ_3) extra_no_O
                  (rec: "outer" <> :=
                     let: "head1" := !#head in
                     let: "next" := !("head1" +ₗ #1) in
                     (rec: "walk" "iter" "next" :=
                        match: "next" with
                          InjL "p" =>
                            if: "p" = #() then InjL #()
                            else
                              let: "v" := !"p" in
                              if: Snd (CmpXchg ("iter" +ₗ #1) "next" (InjR "p"))
                              then Snd (CmpXchg #head "head1" "p");; InjR "v"
                              else "outer" #()
                        | InjR "p" =>
                            if: "p" = #() then "outer" #()
                            else
                              let: "next2" := !("p" +ₗ #1) in
                              "walk" "p" "next2"
                        end) "head1" "next")%V
                  Φ
                  with "Hinv Htrace_inv Hfrag Hhead_frag Hl_succ_frag
                        Hno_O_frag [//] [] Hdel_lb_succ_3 [] Houter HΦ").
        { iRight. iExists τ_succ_2. iSplit; first done.
          iApply "Hno_O_τ_succ_2_frag". }
        { iRight. iLeft.
          iExists τ_l_succ_3, l_succ_3, v_l. iSplit; first done.
          iApply "Hl_succ_3_frag". }
      + (* (false, None): empty queue at l_succ_2.  Fire LIN-DEQ2
           inline (analogous to walk lemma's Case A's (false, None)
           sub-case) at this inv-open, then wp_pures past walk
           recursion to NONE, then trace_emit. *)
        pose proof Hsim3 as (Hlen3 & Hdel3 & Hcp_in_ts3 & Hdomsub3 & _
                            & Henq_clause3 & Hdeq_clause3 & Hinj3 & _
                            & Hlt_pos3 & _Htbd3 & Hcomp_link3
                            & Htail_in3 & Hhead_in3 & _ & _).
        (* Step 1: del_pref_3 = i_succ_3.  Have [i_succ_3 ≤ del_pref_3]
           via Hdel_ge_i_succ_3.  From Hmark_3 = false:
           del_pref_3 ≤ i_succ_3. *)
        rewrite /mark_at in Hmark_3.
        apply bool_decide_eq_false in Hmark_3.
        assert (del_pref_3 = i_succ_3) as Hdel_eq_i_succ_3 by lia.
        (* Step 2: length nodes_3 = i_succ_3 + 1. *)
        rewrite /succ_at in Hsucc_3.
        destruct (nodes_3 !! (i_succ_3 + 1)%nat) eqn:Hnext_3;
          first discriminate.
        apply lookup_ge_None_1 in Hnext_3.
        pose proof (lookup_lt_Some _ _ _ Hi_succ_3_lookup) as Hlen_lower3.
        assert (length nodes_3 = (i_succ_3 + 1)%nat) as Hlen_eq3 by lia.
        (* Step 3: extract op_map info via Hfrag (linked = false). *)
        iDestruct (own_valid_2 with "Hauth_op3 Hfrag") as %Hτ_both3.
        apply auth_both_valid_discrete in Hτ_both3 as [Hτ_incl3 Hτ_valid3].
        apply singleton_included_exclusive_l in Hτ_incl3; [|apply _|done].
        rewrite lookup_fmap in Hτ_incl3.
        apply leibniz_equiv in Hτ_incl3.
        apply fmap_Some_1 in Hτ_incl3 as (info_τ3 & Hτ_in_op3 & Hinfo_τ3).
        destruct info_τ3 as [kd nd lk]; injection Hinfo_τ3 as <- <- <-.
        destruct (Hdeq_clause3 _ _ _ _ _ Hτ_in_op3) as (_ & Hcp_τ_R1_pre3 & _).
        specialize (Hcp_τ_R1_pre3 eq_refl).
        (* Step 4: γ_op update — set linked := true. *)
        set (new_τ_info := {| op_info_kind := OpDeq [] rng_init;
                              op_info_node := None;
                              op_info_linked := true |}).
        iMod (own_update_2 _ _ _
                (● to_opmap (<[τ := new_τ_info]> op_map_3)
                   ⋅ ◯ {[τ := Excl new_τ_info]})
                with "Hauth_op3 Hfrag") as "[Hauth_op3 Hfrag]".
        { apply auth_update.
          rewrite /to_opmap fmap_insert.
          apply: singleton_local_update.
          { rewrite lookup_fmap Hτ_in_op3 //. }
          by apply exclusive_local_update. }
        (* Step 5: dq_map_3 !! τ = None. *)
        assert (absq_wf valid_value s_3) as Hwf3.
        { eapply absq_wf_steps; [exact Hsteps3|apply absq_wf_init]. }
        assert (dq_map_3 !! τ = None) as Hdq_τ_none3.
        { destruct (dq_map_3 !! τ) as [v_old|] eqn:Heq; last done.
          exfalso. pose proof (Hdqi3 _ _ Heq) as Hrv_τ.
          destruct (absq_wf_rv _ _ Hwf3 τ (mk_is_Some _ _ Hrv_τ))
            as [Hcp|Hcp]; rewrite Hcp_τ_R1_pre3 in Hcp; discriminate. }
        (* Step 6: γ_dq update with NONEV. *)
        iMod (own_update_2 _ _ _
                (● to_dqmap (<[τ := NONEV]> dq_map_3)
                   ⋅ ◯ to_dqmap (<[τ := NONEV]> dq_map_3))
                with "Hauth_dq3 Hfrag_dq3") as "[Hauth_dq3 Hfrag_dq3]".
        { apply auth_update.
          rewrite /to_dqmap !fmap_insert.
          apply: alloc_local_update; [|done].
          rewrite lookup_fmap Hdq_τ_none3 //. }
        iDestruct (own_mono _ _ (◯ {[τ := to_agree NONEV]}) with "Hfrag_dq3")
          as "#Hdq_τ_frag".
        { apply auth_frag_mono. rewrite /to_dqmap.
          apply singleton_included_l.
          exists (to_agree NONEV). split.
          - rewrite lookup_fmap lookup_insert_eq //.
          - reflexivity. }
        (* Step 7: γ_ls update — append [(τ, ALinDeq NONEV)]. *)
        iMod (own_update _ _
                (●ML (ls_3 ++ [(τ, ALinDeq NONEV)]
                       : list (leibnizO (positive * absq_action))))
                with "Hauth_ls3") as "Hauth_ls3".
        { apply mono_list_update. by apply prefix_app_r. }
        (* Step 8: discharge LIN-DEQ2 premise (HallPend). *)
        assert (s_3.(absq_O) ⊆ dom s_3.(absq_l)) as HO_in_l3.
        { eapply absq_steps_O_in_l; [exact Hsteps3|]. simpl. clear; set_solver. }
        assert (∀ o, o ∈ s_3.(absq_O) → ∃ d, s_3.(absq_l) !! o = Some (d, PEND))
          as HallPend3.
        { intros o Ho_O.
          destruct (proj1 (elem_of_dom _ _) (HO_in_l3 _ Ho_O)) as [[d f] Hℓ_o].
          destruct f as [|].
          - by exists d.
          - exfalso.
            destruct (Hcomp_link3 _ _ Hℓ_o) as (p & l_p & Hp_pos & Hp_lookup).
            destruct (Hcorr3 _ _ _ _ Hp_pos Hp_lookup) as (_ & _ & Hin_iff).
            apply Hin_iff in Ho_O.
            apply lookup_lt_Some in Hp_lookup. lia. }
        (* Step 9: build the LIN-DEQ2 successor state and close inv. *)
        destruct s_3 as [O_3 lt_3 ℓ_3 rv_3 cp_3]; simpl in *.
        iModIntro.
        iSplitL "Hhead3 Htail3 Hchain3 Htrace3 Hauth_op3 Hauth_nm3 Hfrag_nm3
                 Hauth_dq3 Hfrag_dq3 Hauth_del3 Hauth_calls3 Hauth_no_O3
                 Hauth_ls3 Hauth_w3 Hfrag_w3".
        { iNext.
          iExists nodes_3, del_pref_3, head_val_3, tail_val_3, dummy_loc_3, ts_3,
            {| absq_O := O_3; absq_lt := lt_3; absq_l := ℓ_3;
               absq_rv := <[τ := NONEV]> rv_3;
               absq_cp := <[τ := R2]> cp_3 |},
            (ls_3 ++ [(τ, ALinDeq NONEV)]),
            (<[τ := new_τ_info]> op_map_3), node_map_3,
            (<[τ := NONEV]> dq_map_3), no_O_set_3, witness_map_3.
          iFrame "Hhead3 Htail3 Hchain3 Htrace3 Hauth_op3 Hauth_nm3 Hfrag_nm3
                  Hauth_dq3 Hfrag_dq3 Hauth_del3 Hauth_ls3
                  Hauth_no_O3 Hauth_w3 Hfrag_w3".
          assert (τ ∈ dom cp_3) as Hτ_in_cp_3
            by (apply elem_of_dom; eexists; exact Hcp_τ_R1_pre3).
          rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre3)).
          iFrame "Hauth_calls3".
          iPureIntro. split_and!.
          - eapply rtcL_r; [exact Hsteps3|].
            apply absq_step_lin_deq2; [done|exact Hcp_τ_R1_pre3|exact HallPend3].
          - rewrite Hts_eq3 /trace_of_absq_labels map_app /= filter_app.
            rewrite filter_cons_False; [by rewrite app_nil_r|].
            by compute.
          - split_and!; simpl.
            + exact Hlen3.
            + exact Hdel3.
            + rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre3)).
              exact Hcp_in_ts3.
            + rewrite !dom_insert_L.
              clear -Hdomsub3 Hτ_in_cp_3. set_solver.
            + exact Hnm_dom3.
            + intros τ' d' node' linked' Hop'.
              destruct (decide (τ' = τ)) as [->|Hne].
              { rewrite lookup_insert_eq in Hop'.
                injection Hop' as Habs. discriminate. }
              rewrite lookup_insert_ne in Hop'; last done.
              destruct (Henq_clause3 _ _ _ _ Hop')
                as (Hcp & Hℓ & Hpre & Hpost).
              split_and!.
              { rewrite lookup_insert_ne; [exact Hcp|done]. }
              { exact Hℓ. }
              { exact Hpre. }
              { exact Hpost. }
            + intros τ' obs' rng' node' linked' Hop'.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_insert_eq in Hop'.
                injection Hop' as <- <- <- <-.
                split_and!.
                { reflexivity. }
                { intros [=]. }
                { intros _. rewrite lookup_insert_eq. split; first done.
                  exists NONEV. by rewrite lookup_insert_eq. }
              * rewrite lookup_insert_ne in Hop'; last done.
                destruct (Hdeq_clause3 _ _ _ _ _ Hop') as (Hnone & Hpre & Hpost).
                split_and!.
                { exact Hnone. }
                { intros Hb. rewrite lookup_insert_ne; [|done]. by apply Hpre. }
                { intros Hb. destruct (Hpost Hb) as (Hcp_R2' & v_rv' & Hrv_v').
                  split.
                  - rewrite lookup_insert_ne; [exact Hcp_R2'|done].
                  - exists v_rv'. rewrite lookup_insert_ne; [exact Hrv_v'|done]. }
            + exact Hinj3.
            + exact Hcorr3.
            + exact Hlt_pos3.
            + done.
            + exact Hcomp_link3.
            + exact Htail_in3.
            + exact Hhead_in3.
            + exact Hnm_chain3.
            + exact Hsome_at_pos3.
          - exact Hdummy3.
          - exact Hnvi3.
          - intros τ' v Hlk.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hlk. injection Hlk as <-.
              by rewrite lookup_insert_eq. }
            rewrite lookup_insert_ne in Hlk; last done.
            rewrite lookup_insert_ne; last done.
            by apply Hdqi3.
          - apply Hno_O_inv3.
          - apply Hno_O_inv3.
          - intros i loc τ' v Hpos Hlk info Hop_lk.
            pose proof (Hcoi3 _ _ _ _ Hpos Hlk) as Hlinked.
            destruct (decide (τ' = τ)) as [->|Hne].
            + exfalso. specialize (Hlinked _ Hτ_in_op3). discriminate.
            + rewrite lookup_insert_ne in Hop_lk; [|done].
              exact (Hlinked _ Hop_lk).
          - destruct Hwit3 as [Hwit_dom Hwit_per].
            split.
            { simpl. clear -Hwit_dom. set_solver. }
            intros τ_w tail_loc snap Hwit_lookup.
            exact (Hwit_per τ_w tail_loc snap Hwit_lookup). }
        (* Step 10: wp_pures past walk recursion → NONE. *)
        simpl.
        wp_pures.
        (* Step 11: trace_emit handoff with v_dq := NONEV. *)
        unfold new_τ_info in *.
        wp_apply (op_spec_deq_trace_emit
                  γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                  l head tail τ rng_init NONEV
                  with "Hinv Htrace_inv Hfrag Hdq_τ_frag HΦ").
    - (* (true, None): marked-null.  Impossible: [mark_at del_pref_2
         i_2 = true] gives [i_2 + 1 ≤ del_pref_2], and [succ_at
         nodes_2 i_2 = None] gives [length nodes_2 ≤ i_2 + 1].
         Combined with clause 2 ([del_pref_2 < length nodes_2]) we
         get [length nodes_2 ≤ i_2 + 1 ≤ del_pref_2 < length
         nodes_2], contradiction. *)
      exfalso.
      rewrite /mark_at in Hmark_2.
      apply bool_decide_eq_true in Hmark_2.
      rewrite /succ_at in Hsucc_2.
      destruct (nodes_2 !! (i_2 + 1)%nat) eqn:Hnext_2; first discriminate.
      apply lookup_ge_None_1 in Hnext_2.
      lia.
    - (* (false, Some l_succ_2): unmarked-pointer.  Mark-CAS branch.
         Fires LIN-DEQ1 on CAS success.

         Plan:
         (a) Derive [l_succ_2]'s persistent γ_nm fragment + its chain
             position [i_2 + 1] in [chain_2].
         (b) Close inv unchanged.
         (c) Open inv at [chain_3] to load [!l_succ_2] (the value
             cell).  Close inv unchanged.
         (d) Open inv at [chain_4] for the mark CAS.  CAS dispatch:
             - Success: fire [absq_step_lin_deq1] with [k' = τ-tag at
               i_4 + 1].  Discharge minimality via clause 10 +
               clause 9.  Update [del_pref_4 → i_4 + 1], op_map,
               dq_map, ls.  Close inv with new state.
             - Failure: head_val.next has changed (marked by another
               dequeue).  Close inv unchanged, recurse via IH. *)
      (* (a) Derive l_succ_2's chain position + persistent γ_nm. *)
      rewrite /succ_at in Hsucc_2.
      destruct (nodes_2 !! (i_2 + 1)%nat) as [[[lk_succ_2 τ_succ_2_opt] v_succ_2]|]
        eqn:Hnext_lookup_2; last discriminate.
      simpl in Hsucc_2. injection Hsucc_2 as ->.
      (* By clause 16, l_succ_2's position i_2 + 1 ≥ 1 carries Some τ. *)
      assert (Hi_succ_2_pos : (1 ≤ i_2 + 1)%nat) by lia.
      destruct (Hsome_at_pos2 _ _ _ _ Hi_succ_2_pos Hnext_lookup_2)
        as [τ_succ_2 ->].
      pose proof (Hnm_chain2 _ _ _ _ Hnext_lookup_2) as Hnm_l_succ_2.
      iDestruct (own_mono _ _ (◯ {[l_succ_2 := to_agree
                  ((Some τ_succ_2, v_succ_2) : leibnizO node_info)]})
                  with "Hfrag_nm2") as "#Hl_succ_frag".
      { apply auth_frag_mono. rewrite /to_nodemap.
        apply (proj2 (singleton_included_l _ _ _)).
        exists (to_agree ((Some τ_succ_2, v_succ_2) : leibnizO node_info)). split.
        - rewrite lookup_fmap Hnm_l_succ_2 //=.
        - reflexivity. }
      (* Also extract op_map fragment for τ_succ_2 (the dequeued
         enqueue), via clause 9: τ_succ_2 ∈ dom absq_l_2.  We'll need
         this for LIN-DEQ1 minimality. *)
      destruct (Hcorr2 _ _ _ _ Hi_succ_2_pos Hnext_lookup_2)
        as (_ & (f_succ_2 & Hℓ_τ_succ_2) & Hin_iff_succ_2).
      (* (b) Close inv unchanged. *)
      iDestruct ("HW2" with "[$Hv2 $Hn2]") as "Hchain2".
      iModIntro.
      iSplitL "Hhead2 Htail2 Hchain2 Htrace2 Hauth_op2 Hauth_nm2 Hfrag_nm2 Hauth_dq2 Hfrag_dq2 Hauth_del2 Hauth_calls2 Hauth_no_O2 Hauth_ls2 Hauth_w2 Hfrag_w2".
      { iNext. iExists nodes_2, del_pref_2, head_val_2, tail_val_2, dummy_loc_2, ts_2, s_2, ls_2,
          op_map_2, node_map_2, dq_map_2, no_O_set_2, witness_map_2.
        iFrame. iPureIntro. split_and!; auto.
        - apply Hno_O_inv2.
        - apply Hno_O_inv2. }
      wp_pures.

      (* (c) Open inv at [chain_3] to load [!l_succ_2]. *)
      wp_bind (! _)%E.
      iInv Nbq as (nodes_3 del_pref_3 head_val_3 tail_val_3 dummy_loc_3 ts_3 s_3 ls_3
                   op_map_3 node_map_3 dq_map_3 no_O_set_3 witness_map_3)
        "(>Hhead3 & >Htail3 & Hchain3 & >Htrace3 & >Hauth_op3 & >Hauth_nm3 & Hfrag_nm3
          & >Hauth_dq3 & Hfrag_dq3 & >Hauth_del3 & >Hauth_calls3 & >Hauth_no_O3 & >Hauth_ls3 & >Hauth_w3 & Hfrag_w3
          & >%Hsteps3 & >%Hts_eq3 & >%Hsim3 & >%Hdummy3 & >%Hnvi3 & >%Hdqi3 & >%Hno_O_inv3 & >%Hcoi3 & >%Hwit3)".
      (* Find l_succ_2's position in chain_3 via Hl_succ_frag agreement. *)
      iDestruct (own_valid_2 with "Hauth_nm3 Hl_succ_frag") as %Hagree_3.
      apply auth_both_valid_discrete in Hagree_3 as [Hincl_3 _].
      apply singleton_included_l in Hincl_3 as (av_3 & Hav_lookup_3 & Hav_incl_3).
      rewrite /to_nodemap lookup_fmap in Hav_lookup_3.
      apply fmap_Some_equiv in Hav_lookup_3 as (info_3 & Hnm3_l_succ & Hav_eq_3).
      rewrite Hav_eq_3 in Hav_incl_3. rewrite Some_included in Hav_incl_3.
      assert ((Some τ_succ_2, v_succ_2) = info_3 :> leibnizO node_info) as Hinfo_3_eq.
      { destruct Hav_incl_3 as [Heq|Hin].
        - by apply (inj to_agree), leibniz_equiv in Heq.
        - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
      rewrite -Hinfo_3_eq in Hnm3_l_succ.
      clear Hav_eq_3 Hav_incl_3 Hinfo_3_eq info_3.
      pose proof Hsim3 as (Hlen3 & Hdel3 & _ & _ & Hnm_dom3 & _ & _ & _ & _ & _
                          & _ & _ & _ & _ & Hnm_chain3 & _).
      destruct (Hnm_dom3 _ _ _ Hnm3_l_succ) as (i_succ_3 & Hi_succ_3_lookup).
      iDestruct (bq_chain_lookup_acc _ del_pref_3 i_succ_3 l_succ_2
                   (Some τ_succ_2) v_succ_2 Hi_succ_3_lookup
                   with "Hchain3") as "[Hv3 [Hn3 HW3]]".
      simpl. wp_load.
      iDestruct ("HW3" with "[$Hv3 $Hn3]") as "Hchain3".
      iModIntro.
      iSplitL "Hhead3 Htail3 Hchain3 Htrace3 Hauth_op3 Hauth_nm3 Hfrag_nm3 Hauth_dq3 Hfrag_dq3 Hauth_del3 Hauth_calls3 Hauth_no_O3 Hauth_ls3 Hauth_w3 Hfrag_w3".
      { iNext. iExists nodes_3, del_pref_3, head_val_3, tail_val_3, dummy_loc_3, ts_3, s_3, ls_3,
          op_map_3, node_map_3, dq_map_3, no_O_set_3, witness_map_3.
        iFrame. iPureIntro. split_and!; auto.
        - apply Hno_O_inv3.
        - apply Hno_O_inv3. }
      wp_pures.

      (* (d) Open inv at [chain_4] for the mark CAS. *)
      wp_bind (CmpXchg _ _ _).
      iInv Nbq as (nodes_4 del_pref_4 head_val_4 tail_val_4 dummy_loc_4 ts_4 s_4 ls_4
                   op_map_4 node_map_4 dq_map_4 no_O_set_4 witness_map_4)
        "(>Hhead4 & >Htail4 & Hchain4 & >Htrace4 & >Hauth_op4 & >Hauth_nm4 & Hfrag_nm4
          & >Hauth_dq4 & Hfrag_dq4 & >Hauth_del4 & >Hauth_calls4 & >Hauth_no_O4 & >Hauth_ls4 & >Hauth_w4 & Hfrag_w4
          & >%Hsteps4 & >%Hts_eq4 & >%Hsim4 & >%Hdummy4 & >%Hnvi4 & >%Hdqi4 & >%Hno_O_inv4 & >%Hcoi4 & >%Hwit4)".
      (* Find head_val's position in chain_4. *)
      iDestruct (own_valid_2 with "Hauth_nm4 Hhead_frag") as %Hagree_4_h.
      apply auth_both_valid_discrete in Hagree_4_h as [Hincl_4_h _].
      apply singleton_included_l in Hincl_4_h as (av_4_h & Hav_lookup_4_h & Hav_incl_4_h).
      rewrite /to_nodemap lookup_fmap in Hav_lookup_4_h.
      apply fmap_Some_equiv in Hav_lookup_4_h as (info_4_h & Hnm4_head & Hav_eq_4_h).
      rewrite Hav_eq_4_h in Hav_incl_4_h. rewrite Some_included in Hav_incl_4_h.
      assert ((τ_h_opt, v_h) = info_4_h :> leibnizO node_info) as Hinfo_4_h_eq.
      { destruct Hav_incl_4_h as [Heq|Hin].
        - by apply (inj to_agree), leibniz_equiv in Heq.
        - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
      rewrite -Hinfo_4_h_eq in Hnm4_head.
      clear Hav_eq_4_h Hav_incl_4_h Hinfo_4_h_eq info_4_h.
      pose proof Hsim4 as (Hlen4 & Hdel4 & Hcp_in_ts4 & Hdomsub4 & Hnm_dom4 & Henq_clause4
                          & Hdeq_clause4 & Hinj4 & Hcorr4 & Hlt_pos4 & _Htbd4 & Hcomp_link4
                          & Htail_in4 & Hhead_in4 & Hnm_chain4 & Hsome_at_pos4).
      destruct (Hnm_dom4 _ _ _ Hnm4_head) as (i_h_4 & Hi_h_4_lookup).
      (* CAS dispatch on (mark_at del_pref_4 i_h_4, succ_at nodes_4 i_h_4).
         Each sub-case extracts head_val_4's next-cell with the
         appropriate decomposition (lookup_acc for the no-heap-update
         sub-cases; split_at for the (false, Some) CAS-success case
         which advances [del_pref_4] by 1). *)
      destruct (mark_at del_pref_4 i_h_4) eqn:Hmark_4;
      destruct (succ_at nodes_4 i_h_4) as [l_succ_4|] eqn:Hsucc_4.
      + (* (true, Some l_succ_4): head_val.next is [InjRV #l_succ_4]
           (marked).  CAS expects [InjLV #l_succ_2] — fails. *)
        iDestruct (bq_chain_lookup_acc _ del_pref_4 i_h_4 head_val
                     τ_h_opt v_h Hi_h_4_lookup with "Hchain4")
          as "[Hv4 [Hn4 HW4]]".
        iEval (rewrite Hmark_4 Hsucc_4 /next_value_of) in "Hn4".
        wp_cmpxchg_fail.
        iDestruct ("HW4" with "[Hv4 Hn4]") as "Hchain4".
        { rewrite Hmark_4 Hsucc_4 /next_value_of. iFrame. }
        iModIntro.
        iSplitL "Hhead4 Htail4 Hchain4 Htrace4 Hauth_op4 Hauth_nm4 Hfrag_nm4 Hauth_dq4 Hfrag_dq4 Hauth_del4 Hauth_calls4 Hauth_no_O4 Hauth_ls4 Hauth_w4 Hfrag_w4".
        { iNext. iExists nodes_4, del_pref_4, head_val_4, tail_val_4, dummy_loc_4, ts_4, s_4, ls_4,
            op_map_4, node_map_4, dq_map_4, no_O_set_4, witness_map_4.
          iFrame. iPureIntro. split_and!; auto.
          - apply Hno_O_inv4.
          - apply Hno_O_inv4. }
        wp_pures.
        iApply ("IH" with "Hfrag HΦ").
      + (* (true, None): head_val.next is marked-null.  Same as
           (true, None) earlier in this proof — impossible. *)
        exfalso.
        rewrite /mark_at in Hmark_4.
        apply bool_decide_eq_true in Hmark_4.
        rewrite /succ_at in Hsucc_4.
        destruct (nodes_4 !! (i_h_4 + 1)%nat) eqn:Hnext_4; first discriminate.
        apply lookup_ge_None_1 in Hnext_4. lia.
      + (* (false, Some l_succ_4): head_val.next is [InjLV #l_succ_4]
           (unmarked-pointer).  CAS expects [InjLV #l_succ_2].
             - If [l_succ_4 = l_succ_2]: CAS succeeds — fire LIN-DEQ1.
             - If [l_succ_4 ≠ l_succ_2]: CAS fails. *)
        destruct (decide (l_succ_4 = l_succ_2)) as [->|Hne_succ].
        * (* CAS success: use [bq_chain_split_at] so we can rebuild
             [bq_chain] at the new [del_pref_4 + 1]. *)
          iDestruct (bq_chain_split_at _ del_pref_4 head_val
                       τ_h_opt v_h i_h_4 Hi_h_4_lookup with "Hchain4")
            as "(Hpref4 & Hv4 & Hn4 & Hsuf4)".
          iEval (rewrite Hmark_4 Hsucc_4 /next_value_of) in "Hn4".
          wp_cmpxchg_suc.

          (* === LIN-DEQ1 firing.  Mirrors the LIN-DEQ2 case below
             but with the additional advance of [del_pref] and the
             minimality argument for the dequeued [τ_e]. === *)

          (* Step 1: derive [del_pref_4 = i_h_4] (same trick as
             LIN-DEQ2: combine [mark_at = false] with the no-O
             persistent witness for [τ_h_real]). *)
          assert (del_pref_4 ≤ i_h_4)%nat as Hdel_le_i_h_4.
          { rewrite /mark_at in Hmark_4.
            apply bool_decide_eq_false in Hmark_4. lia. }
          iAssert (⌜i_h_4 ≤ del_pref_4⌝)%I as %Hi_h_4_le_del.
          { destruct τ_h_opt as [τ_h_real|] eqn:Hτ_eq.
            - assert (1 ≤ i_h_4)%nat as Hi_h_4_pos.
              { destruct (decide (1 ≤ i_h_4)%nat) as [|Hlt]; first done.
                assert (i_h_4 = 0%nat) as -> by lia.
                rewrite Hdummy4 in Hi_h_4_lookup.
                injection Hi_h_4_lookup as _ Habs _. discriminate. }
              assert (extra_no_O = ({[τ_h_real]} : gset positive)) as Hextra_eq.
              { subst extra_no_O. reflexivity. }
              iDestruct (own_valid_2 with "Hauth_no_O4 Hno_O_frag") as %Hno_O_both.
              apply auth_both_valid_discrete in Hno_O_both as [Hno_O_incl _].
              apply gset_included in Hno_O_incl.
              rewrite Hextra_eq in Hno_O_incl.
              assert (τ_h_real ∈ no_O_set_4) as Hτ_h_in_no_O.
              { clear -Hno_O_incl. set_solver. }
              assert (τ_h_real ∉ s_4.(absq_O)) as Hτ_h_not_O.
              { destruct Hno_O_inv4 as [_ Hdisj].
                clear -Hdisj Hτ_h_in_no_O. set_solver. }
              destruct (Hcorr4 _ _ _ _ Hi_h_4_pos Hi_h_4_lookup)
                as (_ & _ & Hin_iff).
              iPureIntro.
              destruct (decide (del_pref_4 < i_h_4)%nat) as [Hlt|Hge]; last lia.
              exfalso. apply Hτ_h_not_O. by apply Hin_iff.
            - assert (¬ (1 ≤ i_h_4)%nat) as Hi_h_4_zero.
              { intros Hge.
                destruct (Hsome_at_pos4 _ _ _ _ Hge Hi_h_4_lookup) as [? Habs].
                discriminate. }
              iPureIntro. lia. }
          assert (del_pref_4 = i_h_4) as Hdel_eq_i_h_4 by lia.

          (* Step 2: identify [τ_e] (the τ-tag at chain_4 position
             i_h_4 + 1).  By [Hsucc_4 = Some l_succ_2] and clause 16,
             this position carries [Some τ_e]. *)
          rewrite /succ_at in Hsucc_4.
          destruct (nodes_4 !! (i_h_4 + 1)%nat) as [[[lk_4 τ_succ_4_opt] v_succ_4]|]
            eqn:Hnext_lookup_4; last discriminate.
          simpl in Hsucc_4. injection Hsucc_4 as ->.
          assert (Hi_succ_4_pos : (1 ≤ i_h_4 + 1)%nat) by lia.
          destruct (Hsome_at_pos4 _ _ _ _ Hi_succ_4_pos Hnext_lookup_4)
            as [τ_e ->].
          (* Step 2b: reconcile (Some τ_e, v_succ_4) with Hl_succ_frag's
             (Some τ_succ_2, v_succ_2). *)
          pose proof (Hnm_chain4 _ _ _ _ Hnext_lookup_4) as Hnm_l_succ_4.
          iDestruct (own_valid_2 with "Hauth_nm4 Hl_succ_frag") as %Hagree_l_succ.
          apply auth_both_valid_discrete in Hagree_l_succ as [Hincl_l_succ _].
          apply singleton_included_l in Hincl_l_succ as (av_l & Hav_l_lookup & Hav_l_incl).
          rewrite /to_nodemap lookup_fmap in Hav_l_lookup.
          apply fmap_Some_equiv in Hav_l_lookup as (info_l & Hnm_l_succ_4_2 & Hav_l_eq).
          rewrite Hav_l_eq in Hav_l_incl. rewrite Some_included in Hav_l_incl.
          assert ((Some τ_succ_2, v_succ_2) = info_l :> leibnizO node_info)
            as Hinfo_l_eq.
          { destruct Hav_l_incl as [Heq|Hin].
            - by apply (inj to_agree), leibniz_equiv in Heq.
            - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
          rewrite -Hinfo_l_eq in Hnm_l_succ_4_2.
          rewrite Hnm_l_succ_4 in Hnm_l_succ_4_2.
          injection Hnm_l_succ_4_2 as Hτ_eq Hv_eq.
          subst τ_e v_succ_4.
          (* Now τ_succ_2 is the τ-tag at i_h_4 + 1; v_succ_2 is its value. *)

          (* Step 3: extract [op_map_4 !! τ] via [Hfrag] (the dequeue
             call's own fragment) and derive [absq_cp_4 !! τ = Some
             R1] from clause 7. *)
          iDestruct (own_valid_2 with "Hauth_op4 Hfrag") as %Hτ_both.
          apply auth_both_valid_discrete in Hτ_both as [Hτ_incl Hτ_valid].
          apply singleton_included_exclusive_l in Hτ_incl; [|apply _|done].
          rewrite lookup_fmap in Hτ_incl.
          apply leibniz_equiv in Hτ_incl.
          apply fmap_Some_1 in Hτ_incl as (info_τ & Hτ_in_op4 & Hinfo_τ).
          destruct info_τ as [kd_τ nd_τ lk_τ];
            injection Hinfo_τ as <- <- <-.
          destruct (Hdeq_clause4 _ _ _ _ _ Hτ_in_op4) as (_ & Hcp_τ_R1_pre & _).
          specialize (Hcp_τ_R1_pre eq_refl).

          (* Step 4: γ_op update — set [linked := true]. *)
          set (new_τ_info := {| op_info_kind := OpDeq [] rng_init;
                                op_info_node := None;
                                op_info_linked := true |}).
          iMod (own_update_2 _ _ _
                  (● to_opmap (<[τ := new_τ_info]> op_map_4)
                     ⋅ ◯ {[τ := Excl new_τ_info]})
                  with "Hauth_op4 Hfrag") as "[Hauth_op4 Hfrag]".
          { apply auth_update.
            rewrite /to_opmap fmap_insert.
            apply: singleton_local_update.
            { rewrite lookup_fmap Hτ_in_op4 //. }
            by apply exclusive_local_update. }

          (* Step 5: derive [τ_succ_2 ∈ absq_min (absq_O s_4) (absq_lt
             s_4)].  Membership: by clause 9 at position i_h_4 + 1
             with [del_pref_4 = i_h_4 < i_h_4 + 1].  Minimality:
             ∀ k ∈ O_4, (k, τ_succ_2) ∉ lt_4.  Suppose the contrary;
             by clause 10 there is p_k ≥ 1 with [k]'s tag at chain_4
             pos p_k and p_k < i_h_4 + 1, i.e., p_k ≤ i_h_4 =
             del_pref_4.  Then by clause 9 at p_k, k ∈ O_4 ↔
             del_pref_4 < p_k, contradicting p_k ≤ del_pref_4. *)
          assert (Hτ_succ_2_in_O : τ_succ_2 ∈ s_4.(absq_O)).
          { destruct (Hcorr4 _ _ _ _ Hi_succ_4_pos Hnext_lookup_4)
              as (_ & _ & Hin_iff_succ).
            apply Hin_iff_succ. lia. }
          assert (Hτ_succ_2_min : τ_succ_2 ∈ absq_min s_4.(absq_O) s_4.(absq_lt)).
          { rewrite /absq_min elem_of_filter. split; [|exact Hτ_succ_2_in_O].
            intros k Hk_in_O.
            intros Hkin_lt.
            destruct (Hlt_pos4 _ _ Hkin_lt)
              as (p_k & l_k & d_k & Hp_k_pos & Hp_k_lookup & Hp_imp).
            specialize (Hp_imp (i_h_4 + 1)%nat l_succ_2 v_succ_2
                                Hi_succ_4_pos Hnext_lookup_4).
            assert (Hp_k_le_i : (p_k ≤ i_h_4)%nat) by lia.
            destruct (Hcorr4 _ _ _ _ Hp_k_pos Hp_k_lookup)
              as (_ & _ & Hin_iff_k).
            apply Hin_iff_k in Hk_in_O. lia. }
          (* Extract τ_succ_2's ℓ-entry from chain_4's correspondence. *)
          destruct (Hcorr4 _ _ _ _ Hi_succ_4_pos Hnext_lookup_4)
            as (_ & (f_succ_2_4 & Hℓ_τ_succ_2_4) & _).

          (* Step 6: derive [dq_map_4 !! τ = None]. *)
          assert (absq_wf valid_value s_4) as Hwf_4.
          { eapply absq_wf_steps; [exact Hsteps4|apply absq_wf_init]. }
          assert (dq_map_4 !! τ = None) as Hdq_τ_none.
          { destruct (dq_map_4 !! τ) as [v_old|] eqn:Heq; last done.
            exfalso. pose proof (Hdqi4 _ _ Heq) as Hrv_τ.
            destruct (absq_wf_rv _ _ Hwf_4 τ (mk_is_Some _ _ Hrv_τ))
              as [Hcp|Hcp]; rewrite Hcp_τ_R1_pre in Hcp; discriminate. }

          (* Step 7: γ_dq update — record [SOMEV v_succ_2]. *)
          iMod (own_update_2 _ _ _
                  (● to_dqmap (<[τ := SOMEV v_succ_2]> dq_map_4)
                     ⋅ ◯ to_dqmap (<[τ := SOMEV v_succ_2]> dq_map_4))
                  with "Hauth_dq4 Hfrag_dq4") as "[Hauth_dq4 Hfrag_dq4]".
          { apply auth_update.
            rewrite /to_dqmap !fmap_insert.
            apply: alloc_local_update; [|done].
            rewrite lookup_fmap Hdq_τ_none //. }
          iDestruct (own_mono _ _ (◯ {[τ := to_agree (SOMEV v_succ_2)]}) with "Hfrag_dq4")
            as "#Hdq_τ_frag".
          { apply auth_frag_mono. rewrite /to_dqmap.
            apply singleton_included_l.
            exists (to_agree (SOMEV v_succ_2)). split.
            - rewrite lookup_fmap lookup_insert_eq //.
            - reflexivity. }

          (* Step 8: γ_ls append [(τ, ALinDeq (SOMEV v_succ_2))]. *)
          iMod (own_update _ _
                  (●ML (ls_4 ++ [(τ, ALinDeq (SOMEV v_succ_2))]
                         : list (leibnizO (positive * absq_action))))
                  with "Hauth_ls4") as "Hauth_ls4".
          { apply mono_list_update. by apply prefix_app_r. }

          (* Step 9: γ_del update — advance [del_pref_4 → i_h_4 + 1]. *)
          iMod (own_update _ _ (●MN (i_h_4 + 1)%nat)
                  with "Hauth_del4") as "Hauth_del4".
          { apply mono_nat_update. lia. }

          (* Step 9b: γ_no_O update — record τ_succ_2 as ∉ O.  Used at
             the post-LIN-DEQ1 head CAS to derive [l_succ_2]'s position
             ≤ del_pref_5 across inv-opens (since [no_O_set] is
             monotonic and [no_O_set ## absq_O] holds). *)
          iMod (own_update _ _
                  (● (no_O_set_4 ∪ {[τ_succ_2]} : gsetUR positive)
                     ⋅ ◯ (no_O_set_4 ∪ {[τ_succ_2]} : gsetUR positive)
                    : authR (gsetUR positive))
                  with "Hauth_no_O4") as "[Hauth_no_O4 #Hno_O_full_τ_succ]".
          { apply auth_update_alloc, gset_local_update.
            apply union_subseteq_l. }
          iAssert (own γ_no_O (◯ ({[τ_succ_2]} : gsetUR positive)))
            as "#Hno_O_τ_succ_frag".
          { iApply (own_mono with "Hno_O_full_τ_succ").
            apply auth_frag_mono. apply gset_included.
            apply union_subseteq_r. }
          iClear "Hno_O_full_τ_succ".

          (* Step 10: rebuild [bq_chain] at the new [del_pref_4 + 1].
             [Hn4] (post-CAS) has [(head_val +ₗ 1) ↦ InjRV #l_succ_2 =
             next_value_of true (Some l_succ_2) = next_value_of (mark_at
             (i_h_4 + 1) i_h_4) (succ_at nodes_4 i_h_4)] (using
             [Hnext_lookup_4] for [succ_at] and [bool_decide_eq_true]
             for [mark_at]). *)
          assert (Hsucc_4_eq : succ_at nodes_4 i_h_4 = Some l_succ_2).
          { rewrite /succ_at Hnext_lookup_4 //. }
          assert (Hmark_new : mark_at (i_h_4 + 1)%nat i_h_4 = true).
          { rewrite /mark_at. apply bool_decide_eq_true. lia. }
          assert (Hi_lookup_del : nodes_4 !! del_pref_4 = Some (head_val, τ_h_opt, v_h)).
          { rewrite Hdel_eq_i_h_4. exact Hi_h_4_lookup. }
          iAssert (bq_chain nodes_4 (i_h_4 + 1)%nat)
            with "[Hpref4 Hv4 Hn4 Hsuf4]" as "Hchain4'".
          { rewrite -Hdel_eq_i_h_4.
            iApply (bq_chain_advance _ del_pref_4 head_val τ_h_opt v_h
                      Hi_lookup_del).
            iSplitL "Hpref4".
            { rewrite Hdel_eq_i_h_4. iFrame. }
            iSplitL "Hv4"; first iFrame.
            iSplitL "Hn4".
            { rewrite Hdel_eq_i_h_4 Hmark_new Hsucc_4_eq /next_value_of.
              iFrame. }
            rewrite Hdel_eq_i_h_4. iFrame "Hsuf4". }

          (* Step 11: close inv with the LIN-DEQ1 successor state. *)
          destruct s_4 as [O_4 lt_4 ℓ_4 rv_4 cp_4]; simpl in *.
          iModIntro.
          iSplitL "Hhead4 Htail4 Hchain4' Htrace4 Hauth_op4 Hauth_nm4 Hfrag_nm4 Hauth_dq4 Hfrag_dq4 Hauth_del4 Hauth_calls4 Hauth_no_O4 Hauth_ls4 Hauth_w4 Hfrag_w4".
          { iNext.
            iExists nodes_4, (i_h_4 + 1)%nat, head_val_4, tail_val_4, dummy_loc_4, ts_4,
              {| absq_O := O_4 ∖ {[τ_succ_2]};
                 absq_lt := absq_remove lt_4 τ_succ_2;
                 absq_l := ℓ_4;
                 absq_rv := <[τ := SOMEV v_succ_2]> rv_4;
                 absq_cp := <[τ := R2]> cp_4 |},
              (ls_4 ++ [(τ, ALinDeq (SOMEV v_succ_2))]),
              (<[τ := new_τ_info]> op_map_4), node_map_4,
              (<[τ := SOMEV v_succ_2]> dq_map_4),
              (no_O_set_4 ∪ {[τ_succ_2]}), witness_map_4.
            iFrame "Hhead4 Htail4 Hchain4' Htrace4 Hauth_op4 Hauth_nm4 Hfrag_nm4
                    Hauth_dq4 Hfrag_dq4 Hauth_del4 Hauth_ls4 Hauth_no_O4 Hauth_w4 Hfrag_w4".
            assert (τ ∈ dom cp_4) as Hτ_in_cp_4
              by (apply elem_of_dom; eexists; exact Hcp_τ_R1_pre).
            rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre)).
            iFrame "Hauth_calls4".
            iPureIntro. split_and!.
            - (* rtcL absq_step with one more LIN-DEQ1 step *)
              eapply rtcL_r; [exact Hsteps4|].
              apply absq_step_lin_deq1 with (f := f_succ_2_4);
                [exact Hcp_τ_R1_pre|exact Hτ_succ_2_min|exact Hℓ_τ_succ_2_4].
            - (* ts unchanged: ALinDeq is a lin event, filtered out *)
              rewrite Hts_eq4 /trace_of_absq_labels map_app /= filter_app.
              rewrite filter_cons_False; [by rewrite app_nil_r|].
              by compute.
            - (* bq_sim — 16 clauses for the LIN-DEQ1 successor state. *)
              split_and!; simpl.
              + exact Hlen4.
              + (* del_pref_5 = i_h_4 + 1 < length nodes_4 *)
                apply lookup_lt_Some in Hnext_lookup_4. lia.
              + (* dom cp_5 = dom cp_4 ⊆ list_to_set ts_4.*1 *)
                rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre)).
                exact Hcp_in_ts4.
              + (* dom op_map_5 ⊆ dom cp_5 *)
                rewrite !dom_insert_L.
                clear -Hdomsub4 Hτ_in_cp_4. set_solver.
              + exact Hnm_dom4.
              + (* clause 6: per-enqueue *)
                intros τ' d' node' linked' Hop'.
                destruct (decide (τ' = τ)) as [->|Hne].
                { rewrite lookup_insert_eq in Hop'.
                  injection Hop' as Habs. discriminate. }
                rewrite lookup_insert_ne in Hop'; last done.
                destruct (Henq_clause4 _ _ _ _ Hop')
                  as (Hcp & Hℓ & Hpre & Hpost).
                split_and!.
                { rewrite lookup_insert_ne; [exact Hcp|done]. }
                { exact Hℓ. }
                { intros Hlinked.
                  (* If τ' = τ_succ_2 with linked = false, contradicts
                     [chain_op_inv] (τ_succ_2 is at chain pos i_h_4 + 1
                     with Some τ_succ_2 tag, so linked = true). *)
                  destruct (decide (τ' = τ_succ_2)) as [->|Hne_τ_succ].
                  - exfalso.
                    pose proof (Hcoi4 _ _ _ _ Hi_succ_4_pos Hnext_lookup_4
                                  _ Hop') as Habs.
                    simpl in Habs. rewrite Hlinked in Habs. discriminate.
                  - rewrite elem_of_difference. split.
                    + by apply Hpre.
                    + clear -Hne_τ_succ. set_solver. }
                { intros Hlinked.
                  destruct (Hpost Hlinked)
                    as (l_e & i_e & Hnode_e & Hi_e_pos & Hi_e_lookup
                         & Hnm_e & Hin_iff_e).
                  exists l_e, i_e. split_and!; auto.
                  (* τ' ∈ O_5 ↔ del_pref_5 < i_e.
                     O_5 = O_4 ∖ {τ_succ_2}; del_pref_5 = del_pref_4 + 1. *)
                  destruct (decide (τ' = τ_succ_2)) as [->|Hne_τ_succ].
                  - (* τ' = τ_succ_2.  By injectivity, i_e = i_h_4 + 1. *)
                    pose proof (Hinj4 _ _ _ _ _ _ _ Hi_e_pos Hi_succ_4_pos
                                  Hi_e_lookup Hnext_lookup_4).
                    subst i_e.
                    rewrite elem_of_difference. split.
                    + intros [_ Habs]. exfalso. apply Habs.
                      apply elem_of_singleton. reflexivity.
                    + lia.
                  - (* τ' ≠ τ_succ_2.  By injectivity, i_e ≠ i_h_4 + 1. *)
                    rewrite elem_of_difference.
                    split.
                    + intros [HinO _]. apply Hin_iff_e in HinO.
                      assert (i_e ≠ i_h_4 + 1)%nat as Hi_ne.
                      { intros ->. apply Hne_τ_succ.
                        rewrite Hnext_lookup_4 in Hi_e_lookup. congruence. }
                      lia.
                    + intros Hlt.
                      assert (i_e ≠ i_h_4 + 1)%nat as Hi_ne by lia.
                      assert (del_pref_4 < i_e)%nat by lia.
                      split.
                      * by apply Hin_iff_e.
                      * clear -Hne_τ_succ. set_solver. }
              + (* clause 7: per-dequeue *)
                intros τ' obs' rng' node' linked' Hop'.
                destruct (decide (τ' = τ)) as [->|Hne].
                * rewrite lookup_insert_eq in Hop'.
                  injection Hop' as <- <- <- <-.
                  split_and!.
                  { reflexivity. }
                  { intros [=]. }
                  { intros _. rewrite lookup_insert_eq. split; first done.
                    exists (SOMEV v_succ_2). by rewrite lookup_insert_eq. }
                * rewrite lookup_insert_ne in Hop'; last done.
                  destruct (Hdeq_clause4 _ _ _ _ _ Hop') as (Hnone & Hpre & Hpost).
                  split_and!.
                  { exact Hnone. }
                  { intros Hb. rewrite lookup_insert_ne; [|done]. by apply Hpre. }
                  { intros Hb. destruct (Hpost Hb) as (Hcp_R2' & v_rv' & Hrv_v').
                    split.
                    - rewrite lookup_insert_ne; [exact Hcp_R2'|done].
                    - exists v_rv'. rewrite lookup_insert_ne; [exact Hrv_v'|done]. }
              + exact Hinj4.
              + (* clause 9: correspondence with new state *)
                intros i l_i τ_i v_i Hi_pos Hi_lookup.
                destruct (Hcorr4 _ _ _ _ Hi_pos Hi_lookup)
                  as (Hnm_l & Hℓ_τ_i & Hin_iff).
                split_and!.
                * exact Hnm_l.
                * exact Hℓ_τ_i.
                * destruct (decide (τ_i = τ_succ_2)) as [->|Hne_τ].
                  -- pose proof (Hinj4 _ _ _ _ _ _ _ Hi_pos Hi_succ_4_pos
                                   Hi_lookup Hnext_lookup_4).
                     subst i.
                     rewrite elem_of_difference. split.
                     ++ intros [_ Habs]. exfalso. apply Habs.
                        apply elem_of_singleton. reflexivity.
                     ++ lia.
                  -- assert (i ≠ i_h_4 + 1)%nat as Hi_ne.
                     { intros ->. apply Hne_τ.
                       rewrite Hnext_lookup_4 in Hi_lookup. congruence. }
                     rewrite elem_of_difference.
                     split.
                     ++ intros [HinO _]. apply Hin_iff in HinO. lia.
                     ++ intros Hlt.
                        assert (del_pref_4 < i)%nat by lia.
                        split.
                        ** by apply Hin_iff.
                        ** clear -Hne_τ. set_solver.
              + (* clause 10: lt-edges *)
                intros k k_e Hkk.
                rewrite /absq_remove elem_of_filter /= in Hkk.
                destruct Hkk as [_ Hkk_lt].
                exact (Hlt_pos4 _ _ Hkk_lt).
              + done.
              + (* clause 12: COMP enqueues linked (ℓ unchanged) *)
                exact Hcomp_link4.
              + (* clause 13: tail in chain *) exact Htail_in4.
              + (* clause 14: head in marked prefix.
                   Old: ∃ i_h ≤ del_pref_4 with head at i_h.
                   New: need ≤ del_pref_5 = del_pref_4 + 1.  Old's i_h
                   suffices. *)
                destruct Hhead_in4 as (i_h_old & τ_h_old & v_h_old & Hi_h_le_old & Hhead_at_old).
                exists i_h_old, τ_h_old, v_h_old. split.
                * lia.
                * exact Hhead_at_old.
              + exact Hnm_chain4.
              + exact Hsome_at_pos4.
            - exact Hdummy4.
            - (* node_val_inv: ℓ unchanged, node_map unchanged *) exact Hnvi4.
            - (* dq_inv: dq_map_5 = <[τ := SOMEV v_succ_2]> dq_map_4,
                 rv_5 = <[τ := SOMEV v_succ_2]> rv_4. *)
              intros τ' v Hlk.
              destruct (decide (τ' = τ)) as [->|Hne].
              { rewrite lookup_insert_eq in Hlk. injection Hlk as <-.
                by rewrite lookup_insert_eq. }
              rewrite lookup_insert_ne in Hlk; last done.
              rewrite lookup_insert_ne; last done.
              by apply Hdqi4.
            - (* (no_O_set_4 ∪ {τ_succ_2}) ⊆ dom cp_5: dom cp_5 = dom cp_4
                 (insertion of existing key).  τ_succ_2 ∈ dom cp_4 because
                 ℓ_4[τ_succ_2] = Some (v_succ_2, _) (Hℓ_τ_succ_2_4) and absq_wf
                 says dom ℓ ⊆ dom cp.  *)
              simpl.
              destruct Hno_O_inv4 as [Hsub _].
              destruct Hwf_4 as [Hwf_dom _].
              simpl in Hwf_dom.
              assert (τ_succ_2 ∈ dom ℓ_4) as Hτ_succ_in_ℓ
                by (apply elem_of_dom; eexists; exact Hℓ_τ_succ_2_4).
              clear -Hsub Hwf_dom Hτ_succ_in_ℓ. set_solver.
            - (* (no_O_set_4 ∪ {τ_succ_2}) ## absq_O_5: O_5 = O_4 ∖ {τ_succ_2}.
                 τ_succ_2 is removed, so {τ_succ_2} ## O_5.  no_O_set_4 ## O_4 ⊇ O_5. *)
              simpl. destruct Hno_O_inv4 as [_ Hdisj].
              clear -Hdisj. set_solver.
            - (* chain_op_inv: nodes_4 unchanged; new op_map' = <[τ := new_τ_info]> op_map_4. *)
              intros i loc τ' v Hpos Hlk info Hop_lk.
              destruct (decide (τ' = τ)) as [->|Hne].
              + rewrite lookup_insert_eq in Hop_lk.
                injection Hop_lk as <-. reflexivity.
              + rewrite lookup_insert_ne in Hop_lk; [|done].
                exact (Hcoi4 _ _ _ _ Hpos Hlk _ Hop_lk).
            - (* chain_witness_inv: nodes_4 unchanged, witness_map_4 unchanged.
                 New lt is a subset of old, so per-key lt-edges still hold. *)
              destruct Hwit4 as [Hwit_dom Hwit_per].
              split.
              { simpl. clear -Hwit_dom. set_solver. }
              intros τ_w tail_loc snap Hwit_lookup.
              destruct (Hwit_per τ_w tail_loc snap Hwit_lookup)
                as (Hsub & Hlen_w & Hsucc_w & Hsnap_end & Hlt_in_w).
              split_and!; [exact Hsub|exact Hlen_w|exact Hsucc_w|exact Hsnap_end|].
              intros k Hkin.
              (* Hkin : (k, τ_w) ∈ absq_remove lt_4 τ_succ_2.
                 Membership filter says k ≠ τ_succ_2 and τ_w ≠ τ_succ_2,
                 plus (k, τ_w) ∈ lt_4. *)
              rewrite /absq_remove elem_of_filter /= in Hkin.
              destruct Hkin as [_ Hkin_lt].
              by apply Hlt_in_w. }

          (* Step 12: best-effort head CAS [head head_val l_succ_2].
             Reduce the success branch's conditional and bind the CAS. *)
          wp_pures.
          wp_bind (CmpXchg _ _ _).
          iInv Nbq as (nodes_5 del_pref_5 head_val_5 tail_val_5 dummy_loc_5 ts_5 s_5 ls_5
                       op_map_5 node_map_5 dq_map_5 no_O_set_5 witness_map_5)
            "(>Hhead5 & >Htail5 & Hchain5 & >Htrace5 & >Hauth_op5 & >Hauth_nm5 & Hfrag_nm5
              & >Hauth_dq5 & Hfrag_dq5 & >Hauth_del5 & >Hauth_calls5 & >Hauth_no_O5 & >Hauth_ls5 & >Hauth_w5 & Hfrag_w5
              & >%Hsteps5 & >%Hts_eq5 & >%Hsim5 & >%Hdummy5 & >%Hnvi5 & >%Hdqi5 & >%Hno_O_inv5 & >%Hcoi5 & >%Hwit5)".
          destruct (decide (head_val_5 = head_val)) as [Heq_h|Hne_h].
          ** (* Head CAS success: advance head to l_succ_2. *)
             subst head_val_5.
             wp_cmpxchg_suc.
             (* Locate l_succ_2 in chain_5 via Hl_succ_frag. *)
             iDestruct (own_valid_2 with "Hauth_nm5 Hl_succ_frag") as %Hagree_5.
             apply auth_both_valid_discrete in Hagree_5 as [Hincl_5 _].
             apply singleton_included_l in Hincl_5 as (av_5 & Hav_lookup_5 & Hav_incl_5).
             rewrite /to_nodemap lookup_fmap in Hav_lookup_5.
             apply fmap_Some_equiv in Hav_lookup_5 as (info_5 & Hnm_5_l_succ & Hav_eq_5).
             rewrite Hav_eq_5 in Hav_incl_5. rewrite Some_included in Hav_incl_5.
             assert ((Some τ_succ_2, v_succ_2) = info_5 :> leibnizO node_info)
               as Hinfo_5_eq.
             { destruct Hav_incl_5 as [Heq|Hin].
               - by apply (inj to_agree), leibniz_equiv in Heq.
               - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
             rewrite -Hinfo_5_eq in Hnm_5_l_succ.
             clear Hav_eq_5 Hav_incl_5 Hinfo_5_eq info_5.
             pose proof Hsim5 as (Hlen5 & Hdel5 & Hcp_in_ts5 & Hdomsub5 & Hnm_dom5
                                  & Henq_clause5 & Hdeq_clause5 & Hinj5 & Hcorr5
                                  & Hlt_pos5 & _Htbd5 & Hcomp_link5 & Htail_in5
                                  & _ & Hnm_chain5 & Hsome_at_pos5).
             destruct (Hnm_dom5 _ _ _ Hnm_5_l_succ) as (i_succ_5 & Hi_succ_5_lookup).
             (* Derive 1 ≤ i_succ_5: position 0 is the dummy with [None] tag,
                but i_succ_5 carries [Some τ_succ_2]. *)
             assert (1 ≤ i_succ_5)%nat as Hi_succ_5_pos.
             { destruct (decide (1 ≤ i_succ_5)%nat) as [|Hlt]; first done.
               assert (i_succ_5 = 0%nat) as -> by lia.
               rewrite Hdummy5 in Hi_succ_5_lookup.
               injection Hi_succ_5_lookup as _ Habs _. discriminate. }
             (* Use [Hno_O_τ_succ_frag] + [Hauth_no_O5] to get τ_succ_2 ∈
                no_O_set_5.  Combined with [Hno_O_inv5.2 : no_O_set_5 ##
                O_5], we get τ_succ_2 ∉ O_5.  Then by clause 9 at i_succ_5,
                del_pref_5 ≥ i_succ_5. *)
             iDestruct (own_valid_2 with "Hauth_no_O5 Hno_O_τ_succ_frag")
               as %Hno_O_5_both.
             apply auth_both_valid_discrete in Hno_O_5_both as [Hno_O_5_incl _].
             apply gset_included in Hno_O_5_incl.
             assert (τ_succ_2 ∈ no_O_set_5) as Hτ_succ_in_no_O_5.
             { clear -Hno_O_5_incl. set_solver. }
             assert (τ_succ_2 ∉ s_5.(absq_O)) as Hτ_succ_not_O_5.
             { destruct Hno_O_inv5 as [_ Hdisj].
               clear -Hdisj Hτ_succ_in_no_O_5. set_solver. }
             destruct (Hcorr5 _ _ _ _ Hi_succ_5_pos Hi_succ_5_lookup)
               as (_ & _ & Hin_iff_5).
             assert (i_succ_5 ≤ del_pref_5)%nat as Hi_succ_5_le_del.
             { destruct (decide (del_pref_5 < i_succ_5)%nat) as [Hlt|]; last lia.
               exfalso. apply Hτ_succ_not_O_5. by apply Hin_iff_5. }
             (* Close inv with new head_loc = l_succ_2. *)
             iModIntro.
             iSplitL "Hhead5 Htail5 Hchain5 Htrace5 Hauth_op5 Hauth_nm5 Hfrag_nm5 Hauth_dq5 Hfrag_dq5 Hauth_del5 Hauth_calls5 Hauth_no_O5 Hauth_ls5 Hauth_w5 Hfrag_w5".
             { iNext. iExists nodes_5, del_pref_5, l_succ_2, tail_val_5, dummy_loc_5,
                 ts_5, s_5, ls_5, op_map_5, node_map_5, dq_map_5, no_O_set_5, witness_map_5.
               iFrame. iPureIntro. split_and!.
               - exact Hsteps5.
               - exact Hts_eq5.
               - (* bq_sim: only clause 14 (head_loc) changes. *)
                 split_and!.
                 + exact Hlen5.
                 + exact Hdel5.
                 + exact Hcp_in_ts5.
                 + exact Hdomsub5.
                 + exact Hnm_dom5.
                 + exact Henq_clause5.
                 + exact Hdeq_clause5.
                 + exact Hinj5.
                 + exact Hcorr5.
                 + exact Hlt_pos5.
                 + exact _Htbd5.
                 + exact Hcomp_link5.
                 + exact Htail_in5.
                 + (* clause 14: head_loc = l_succ_2 at i_succ_5 ≤ del_pref_5 *)
                   exists i_succ_5, (Some τ_succ_2), v_succ_2.
                   split; [exact Hi_succ_5_le_del|exact Hi_succ_5_lookup].
                 + exact Hnm_chain5.
                 + exact Hsome_at_pos5.
               - exact Hdummy5.
               - exact Hnvi5.
               - exact Hdqi5.
               - apply Hno_O_inv5.
               - apply Hno_O_inv5.
               - exact Hcoi5.
               - exact Hwit5. }
             wp_pures.
             unfold new_τ_info in *.
             iApply (op_spec_deq_trace_emit
                       γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                       l head tail τ rng_init (InjRV v_succ_2)
                       with "Hinv Htrace_inv Hfrag Hdq_τ_frag HΦ").
          ** (* Head CAS fail: head pointer unchanged.  Close inv. *)
             assert (#head_val_5 ≠ #head_val) as Hne_h_inj.
             { intros [=Habs]. by apply Hne_h. }
             wp_cmpxchg_fail.
             iModIntro.
             iSplitL "Hhead5 Htail5 Hchain5 Htrace5 Hauth_op5 Hauth_nm5 Hfrag_nm5 Hauth_dq5 Hfrag_dq5 Hauth_del5 Hauth_calls5 Hauth_no_O5 Hauth_ls5 Hauth_w5 Hfrag_w5".
             { iNext. iExists nodes_5, del_pref_5, head_val_5, tail_val_5, dummy_loc_5, ts_5, s_5, ls_5,
                 op_map_5, node_map_5, dq_map_5, no_O_set_5, witness_map_5.
               iFrame. iPureIntro. split_and!; auto.
               - apply Hno_O_inv5.
               - apply Hno_O_inv5. }
             wp_pures.
             unfold new_τ_info in *.
             wp_apply (op_spec_deq_trace_emit
                       γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                       l head tail τ rng_init (InjRV v_succ_2)
                       with "Hinv Htrace_inv Hfrag Hdq_τ_frag HΦ").
        * (* CAS fail (different successor) *)
          iDestruct (bq_chain_lookup_acc _ del_pref_4 i_h_4 head_val
                       τ_h_opt v_h Hi_h_4_lookup with "Hchain4")
            as "[Hv4 [Hn4 HW4]]".
          iEval (rewrite Hmark_4 Hsucc_4 /next_value_of) in "Hn4".
          assert (InjLV #l_succ_4 ≠ InjLV #l_succ_2) as Hne_inj.
          { intros [=Habs]. apply Hne_succ. exact Habs. }
          wp_cmpxchg_fail.
          iDestruct ("HW4" with "[Hv4 Hn4]") as "Hchain4".
          { rewrite Hmark_4 Hsucc_4 /next_value_of. iFrame. }
          iModIntro.
          iSplitL "Hhead4 Htail4 Hchain4 Htrace4 Hauth_op4 Hauth_nm4 Hfrag_nm4 Hauth_dq4 Hfrag_dq4 Hauth_del4 Hauth_calls4 Hauth_no_O4 Hauth_ls4 Hauth_w4 Hfrag_w4".
          { iNext. iExists nodes_4, del_pref_4, head_val_4, tail_val_4, dummy_loc_4, ts_4, s_4, ls_4,
              op_map_4, node_map_4, dq_map_4, no_O_set_4, witness_map_4.
            iFrame. iPureIntro. split_and!; auto.
            - apply Hno_O_inv4.
            - apply Hno_O_inv4. }
          wp_pures.
          iApply ("IH" with "Hfrag HΦ").
      + (* (false, None): head_val.next is [InjLV #()] (unmarked-null).
           CAS expects [InjLV #l_succ_2] — fails. *)
        iDestruct (bq_chain_lookup_acc _ del_pref_4 i_h_4 head_val
                     τ_h_opt v_h Hi_h_4_lookup with "Hchain4")
          as "[Hv4 [Hn4 HW4]]".
        iEval (rewrite Hmark_4 Hsucc_4 /next_value_of) in "Hn4".
        wp_cmpxchg_fail.
        iDestruct ("HW4" with "[Hv4 Hn4]") as "Hchain4".
        { rewrite Hmark_4 Hsucc_4 /next_value_of. iFrame. }
        iModIntro.
        iSplitL "Hhead4 Htail4 Hchain4 Htrace4 Hauth_op4 Hauth_nm4 Hfrag_nm4 Hauth_dq4 Hfrag_dq4 Hauth_del4 Hauth_calls4 Hauth_no_O4 Hauth_ls4 Hauth_w4 Hfrag_w4".
        { iNext. iExists nodes_4, del_pref_4, head_val_4, tail_val_4, dummy_loc_4, ts_4, s_4, ls_4,
            op_map_4, node_map_4, dq_map_4, no_O_set_4, witness_map_4.
          iFrame. iPureIntro. split_and!; auto.
          - apply Hno_O_inv4.
          - apply Hno_O_inv4. }
        wp_pures.
        iApply ("IH" with "Hfrag HΦ").
    - (* (false, None): EMPTY BRANCH.  Fire [absq_step_lin_deq2]. *)
      (* Step 1: derive [del_pref_2 = i_2].
         - [Hmark_2 : mark_at del_pref_2 i_2 = false] gives
           [del_pref_2 ≤ i_2].
         - The other direction ([i_2 ≤ del_pref_2]) splits via
           [Hcalls_frag]:
           + Dummy case: [i_h = 0], [τ_h_opt = None].  By clause 16
             (positions ≥ 1 carry [Some τ]), [Hi_2_lookup] forces
             [i_2 = 0].  Then [del_pref_2 ≤ 0] gives [del_pref_2 = 0
             = i_2].
           + Non-dummy case: [τ_h_opt = Some τ_h_real], [i_h ≥ 1].  By
             clause 16, [i_2 ≥ 1].  Use [Hno_O_frag] with [Hauth_no_O2]
             to get [τ_h_real ∈ no_O_set_2 ⊆ dom cp_2 ∖ absq_O_2],
             hence [τ_h_real ∉ absq_O_2].  By clause 9 with
             [Hi_2_lookup] and [τ_h_opt = Some τ_h_real], [τ_h_real ∈
             absq_O_2 ↔ del_pref_2 < i_2], so [del_pref_2 ≥ i_2]. *)
      assert (del_pref_2 ≤ i_2)%nat as Hdel_le_i_2.
      { rewrite /mark_at in Hmark_2.
        apply bool_decide_eq_false in Hmark_2. lia. }
      iAssert (⌜i_2 ≤ del_pref_2⌝)%I as %Hi_2_le_del.
      { destruct τ_h_opt as [τ_h_real|] eqn:Hτ_eq.
        - (* Non-dummy: τ_h_opt = Some τ_h_real. *)
          assert (1 ≤ i_2)%nat as Hi_2_pos.
          { destruct (decide (1 ≤ i_2)%nat) as [|Hlt]; first done.
            assert (i_2 = 0%nat) as -> by lia.
            rewrite Hdummy2 in Hi_2_lookup.
            injection Hi_2_lookup as _ Habs _. discriminate. }
          (* Hno_O_frag witnesses τ_h_real ∈ no_O_set_2. *)
          assert (extra_no_O = ({[τ_h_real]} : gset positive)) as Hextra_eq.
          { subst extra_no_O. reflexivity. }
          iDestruct (own_valid_2 with "Hauth_no_O2 Hno_O_frag") as %Hno_O_both.
          apply auth_both_valid_discrete in Hno_O_both as [Hno_O_incl _].
          apply gset_included in Hno_O_incl.
          rewrite Hextra_eq in Hno_O_incl.
          assert (τ_h_real ∈ no_O_set_2) as Hτ_h_in_no_O
            by (clear -Hno_O_incl; set_solver).
          assert (τ_h_real ∉ s_2.(absq_O)) as Hτ_h_not_O.
          { destruct Hno_O_inv2 as [_ Hdisj].
            clear -Hdisj Hτ_h_in_no_O. set_solver. }
          destruct (Hcorr2 _ _ _ _ Hi_2_pos Hi_2_lookup)
            as (_ & _ & Hin_iff).
          iPureIntro.
          destruct (decide (del_pref_2 < i_2)%nat) as [Hlt|Hge]; last lia.
          exfalso. apply Hτ_h_not_O. by apply Hin_iff.
        - (* Dummy: τ_h_opt = None.  By clause 16, i_2 = 0. *)
          assert (¬ (1 ≤ i_2)%nat) as Hi_2_zero.
          { intros Hge.
            destruct (Hsome_at_pos2 _ _ _ _ Hge Hi_2_lookup) as [? Habs].
            discriminate. }
          iPureIntro. lia. }
      assert (del_pref_2 = i_2) as Hdel_eq_i_2 by lia.
      (* Step 2: length nodes_2 = i_2 + 1. *)
      assert (length nodes_2 = i_2 + 1)%nat as Hlen_eq.
      { rewrite /succ_at in Hsucc_2.
        destruct (nodes_2 !! (i_2 + 1)%nat) as [lτv|] eqn:Hnext; last first.
        - apply lookup_ge_None in Hnext.
          apply lookup_lt_Some in Hi_2_lookup. lia.
        - discriminate. }
      (* Step 3: extract op_map fragment for [τ]. *)
      iDestruct (own_valid_2 with "Hauth_op2 Hfrag") as %Hτ_both.
      apply auth_both_valid_discrete in Hτ_both as [Hτ_incl Hτ_valid].
      apply singleton_included_exclusive_l in Hτ_incl; [|apply _|done].
      rewrite lookup_fmap in Hτ_incl.
      apply leibniz_equiv in Hτ_incl.
      apply fmap_Some_1 in Hτ_incl as (info_τ & Hτ_in_op2 & Hinfo_τ).
      destruct info_τ as [kd nd lk]; injection Hinfo_τ as <- <- <-.
      (* By clause 7: linked = false ⟹ absq_cp_2[τ] = R1. *)
      destruct (Hdeq_clause2 _ _ _ _ _ Hτ_in_op2) as (_ & Hcp_τ_R1_pre & _).
      specialize (Hcp_τ_R1_pre eq_refl).
      (* Step 4: γ_op update — set linked to true. *)
      set (new_τ_info := {| op_info_kind := OpDeq [] rng_init;
                            op_info_node := None;
                            op_info_linked := true |}).
      iMod (own_update_2 _ _ _
              (● to_opmap (<[τ := new_τ_info]> op_map_2) ⋅ ◯ {[τ := Excl new_τ_info]})
              with "Hauth_op2 Hfrag") as "[Hauth_op2 Hfrag]".
      { apply auth_update.
        rewrite /to_opmap fmap_insert.
        apply: singleton_local_update.
        { rewrite lookup_fmap Hτ_in_op2 //. }
        by apply exclusive_local_update. }
      (* Step 5: derive [dq_map_2 !! τ = None] via [Hdqi2 + absq_wf_rv]. *)
      assert (absq_wf valid_value s_2) as Hwf_2.
      { eapply absq_wf_steps; [exact Hsteps2|apply absq_wf_init]. }
      assert (dq_map_2 !! τ = None) as Hdq_τ_none.
      { destruct (dq_map_2 !! τ) as [v_old|] eqn:Heq; last done.
        exfalso. pose proof (Hdqi2 _ _ Heq) as Hrv_τ.
        destruct (absq_wf_rv _ _ Hwf_2 τ (mk_is_Some _ _ Hrv_τ))
          as [Hcp|Hcp]; rewrite Hcp_τ_R1_pre in Hcp; discriminate. }
      iMod (own_update_2 _ _ _
              (● to_dqmap (<[τ := NONEV]> dq_map_2)
                 ⋅ ◯ to_dqmap (<[τ := NONEV]> dq_map_2))
              with "Hauth_dq2 Hfrag_dq2") as "[Hauth_dq2 Hfrag_dq2]".
      { apply auth_update.
        rewrite /to_dqmap !fmap_insert.
        apply: alloc_local_update; [|done].
        rewrite lookup_fmap Hdq_τ_none //. }
      iDestruct (own_mono _ _ (◯ {[τ := to_agree NONEV]}) with "Hfrag_dq2")
        as "#Hdq_τ_frag".
      { apply auth_frag_mono. rewrite /to_dqmap.
        apply singleton_included_l.
        exists (to_agree NONEV). split.
        - rewrite lookup_fmap lookup_insert_eq //.
        - reflexivity. }
      (* Step 6: γ_ls append [(τ, ALinDeq NONEV)]. *)
      iMod (own_update _ _
              (●ML (ls_2 ++ [(τ, ALinDeq NONEV)] : list (leibnizO (positive * absq_action))))
              with "Hauth_ls2") as "Hauth_ls2".
      { apply mono_list_update. by apply prefix_app_r. }
      (* Step 7: discharge LIN-DEQ2 premise.  For any o ∈ absq_O_2,
         o ∈ dom absq_l_2 (by absq_steps_O_in_l from absq_init).  Case
         on flag: PEND ✓; COMP ⟹ by clause 12, o is at chain position
         p ≥ 1 with p ≤ length - 1 = i_2 = del_pref_2; by clause 9,
         o ∈ absq_O_2 ↔ del_pref_2 < p, contradicting p ≤ del_pref_2. *)
      assert (s_2.(absq_O) ⊆ dom s_2.(absq_l)) as HO_in_l.
      { eapply absq_steps_O_in_l; [exact Hsteps2|]. simpl. clear; set_solver. }
      assert (∀ o, o ∈ s_2.(absq_O) → ∃ d, s_2.(absq_l) !! o = Some (d, PEND)) as HallPend.
      { intros o Ho_O.
        destruct (proj1 (elem_of_dom _ _) (HO_in_l _ Ho_O)) as [[d f] Hℓ_o].
        destruct f as [|].
        - by exists d.
        - exfalso.
          destruct (Hcomp_link2 _ _ Hℓ_o) as (p & l_p & Hp_pos & Hp_lookup).
          destruct (Hcorr2 _ _ _ _ Hp_pos Hp_lookup) as (_ & _ & Hin_iff).
          apply Hin_iff in Ho_O.
          apply lookup_lt_Some in Hp_lookup. lia. }
      (* Step 8: build new abstract state s_3 = LIN-DEQ2 successor. *)
      destruct s_2 as [O_2 lt_2 ℓ_2 rv_2 cp_2]; simpl in *.
      (* Step 9: re-establish bq_chain via the wand. *)
      iDestruct ("HW2" with "[Hv2 Hn2]") as "Hchain2"; first by iFrame.
      (* Step 10: close inv with new state. *)
      iModIntro.
      iSplitL "Hhead2 Htail2 Hchain2 Htrace2 Hauth_op2 Hauth_nm2 Hfrag_nm2 Hauth_dq2 Hfrag_dq2 Hauth_del2 Hauth_calls2 Hauth_no_O2 Hauth_ls2 Hauth_w2 Hfrag_w2".
      { iNext.
        iExists nodes_2, del_pref_2, head_val_2, tail_val_2, dummy_loc_2, ts_2,
          {| absq_O := O_2; absq_lt := lt_2; absq_l := ℓ_2;
             absq_rv := <[τ := NONEV]> rv_2;
             absq_cp := <[τ := R2]> cp_2 |},
          (ls_2 ++ [(τ, ALinDeq NONEV)]),
          (<[τ := new_τ_info]> op_map_2), node_map_2,
          (<[τ := NONEV]> dq_map_2), no_O_set_2, witness_map_2.
        iFrame "Hhead2 Htail2 Hchain2 Htrace2 Hauth_op2 Hauth_nm2 Hfrag_nm2
                Hauth_dq2 Hfrag_dq2 Hauth_del2 Hauth_ls2 Hauth_no_O2 Hauth_w2 Hfrag_w2".
        (* dom cp_3 = dom cp_2 since τ ∈ dom cp_2. *)
        assert (τ ∈ dom cp_2) as Hτ_in_cp_2
          by (apply elem_of_dom; eexists; exact Hcp_τ_R1_pre).
        rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre)).
        iFrame "Hauth_calls2".
        iPureIntro. split_and!.
        - eapply rtcL_r; [exact Hsteps2|].
          apply absq_step_lin_deq2; [done|exact Hcp_τ_R1_pre|exact HallPend].
        - rewrite Hts_eq2 /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_False; [by rewrite app_nil_r|].
          by compute.
        - (* bq_sim *)
          split_and!; simpl.
          + exact Hlen2.
          + exact Hdel2.
          + (* dom cp_3 ⊆ list_to_set ts_2.*1 *)
            rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre)).
            exact Hcp_in_ts2.
          + (* dom op_map_3 ⊆ dom cp_3 *)
            rewrite !dom_insert_L. clear -Hdomsub2. set_solver.
          + exact Hnm_dom2.
          + (* clause 6: per-enqueue *)
            intros τ' d' node' linked' Hop'.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hop'.
              injection Hop' as Habs. discriminate. }
            rewrite lookup_insert_ne in Hop'; last done.
            destruct (Henq_clause2 _ _ _ _ Hop') as (Hcp & Hℓ & Hpre & Hpost).
            split_and!.
            { rewrite lookup_insert_ne; [exact Hcp|done]. }
            { exact Hℓ. }
            { exact Hpre. }
            { exact Hpost. }
          + (* clause 7: per-dequeue *)
            intros τ' obs' rng' node' linked' Hop'.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hop'.
              injection Hop' as <- <- <- <-.
              split_and!.
              { reflexivity. }
              { intros [=]. }
              { intros _. rewrite lookup_insert_eq. split; first done.
                exists NONEV. by rewrite lookup_insert_eq. }
            * rewrite lookup_insert_ne in Hop'; last done.
              destruct (Hdeq_clause2 _ _ _ _ _ Hop') as (Hnone & Hpre & Hpost).
              split_and!.
              { exact Hnone. }
              { intros Hb. rewrite lookup_insert_ne; [|done]. by apply Hpre. }
              { intros Hb. destruct (Hpost Hb) as (Hcp_R2 & v & Hrv_v).
                split.
                - rewrite lookup_insert_ne; [exact Hcp_R2|done].
                - exists v. rewrite lookup_insert_ne; [exact Hrv_v|done]. }
          + exact Hinj2.
          + (* clause 9: node-list correspondence (l, rv unchanged). *)
            exact Hcorr2.
          + exact Hlt_pos2.
          + done.
          + exact Hcomp_link2.
          + exact Htail_in2.
          + exact Hhead_in2.
          + exact Hnm_chain2.
          + exact Hsome_at_pos2.
        - exact Hdummy2.
        - (* node_val_inv: ℓ unchanged, node_map unchanged. *) exact Hnvi2.
        - (* dq_inv for dq_map_3, rv_3. *)
          intros τ' v Hlk.
          destruct (decide (τ' = τ)) as [->|Hne].
          { rewrite lookup_insert_eq in Hlk. injection Hlk as <-.
            by rewrite lookup_insert_eq. }
          rewrite lookup_insert_ne in Hlk; last done.
          rewrite lookup_insert_ne; last done.
          by apply Hdqi2.
        - apply Hno_O_inv2.
        - apply Hno_O_inv2.
        - (* chain_op_inv: τ here is a dequeue (OpDeq, linked=false).  No
             chain position can carry τ as tag, since the old chain_op_inv
             would force linked=true. *)
          intros i loc τ' v Hpos Hlk info Hop_lk.
          pose proof (Hcoi2 _ _ _ _ Hpos Hlk) as Hlinked.
          destruct (decide (τ' = τ)) as [->|Hne].
          + exfalso. specialize (Hlinked _ Hτ_in_op2). discriminate.
          + rewrite lookup_insert_ne in Hop_lk; [|done].
            exact (Hlinked _ Hop_lk).
        - (* chain_witness_inv: LIN-DEQ2 doesn't change chain or lt; cp unchanged
             (just transitions τ from R1 to R2).  Witness invariant preserved. *)
          destruct Hwit2 as [Hwit_dom Hwit_per].
          split.
          { simpl. clear -Hwit_dom. set_solver. }
          intros τ' snap Hwit_lookup.
          exact (Hwit_per τ' snap Hwit_lookup). }
      (* Step 11: pure dispatch.  next = InjLV #() ⟹ walk returns NONE.
         Then [trace_emit] for [Ret NONEV]. *)
      wp_pures.
      (* Step 12: trace_emit RET-DEQ. *)
      wp_bind (trace_emit _ _ _)%E.
      awp_apply (trace_emit_spec l τ (Ret NONEV) (InjRV NONEV) I_lang_bq
                  with "Htrace_inv"); first done.
      iInv Nbq as (nodes_4 del_pref_4 head_val_4 tail_val_4 dummy_loc_4 ts_4 s_4 ls_4
                   op_map_4 node_map_4 dq_map_4 no_O_set_4 witness_map_4)
        "(>Hhead4 & >Htail4 & Hchain4 & >Htrace4 & >Hauth_op4 & >Hauth_nm4 & Hfrag_nm4
          & >Hauth_dq4 & Hfrag_dq4 & >Hauth_del4 & >Hauth_calls4 & >Hauth_no_O4 & >Hauth_ls4 & >Hauth_w4 & Hfrag_w4
          & >%Hsteps4 & >%Hts_eq4 & >%Hsim4 & >%Hdummy4 & >%Hnvi4 & >%Hdqi4 & >%Hno_O_inv4 & >%Hcoi4 & >%Hwit4)".
      iDestruct (own_valid_2 with "Hauth_op4 Hfrag") as %Hτ_both4.
      apply auth_both_valid_discrete in Hτ_both4 as [Hτ_incl4 Hτ_valid4].
      apply singleton_included_exclusive_l in Hτ_incl4; [|apply _|done].
      rewrite lookup_fmap in Hτ_incl4.
      apply leibniz_equiv in Hτ_incl4.
      apply fmap_Some_1 in Hτ_incl4 as (info_τ4 & Hτ_in_op4 & Hinfo_τ4).
      destruct info_τ4; injection Hinfo_τ4 as <- <- <-.
      pose proof Hsim4 as (_ & _ & Hcp_in_ts4 & _ & _ & _ & Hdeq_clause4 & _).
      destruct (Hdeq_clause4 _ _ _ _ _ Hτ_in_op4) as (_ & _ & Hcp_τ_R2_post).
      specialize (Hcp_τ_R2_post eq_refl) as (Hcp_τ_R2 & v_rv & Hrv_τ_v).
      (* Use Hdq_τ_frag (persistent [◯ {τ := to_agree NONEV}]) to identify v_rv = NONEV. *)
      iDestruct (own_valid_2 with "Hauth_dq4 Hdq_τ_frag") as %Hdq_both4.
      apply auth_both_valid_discrete in Hdq_both4 as [Hdq_incl4 _].
      apply singleton_included_l in Hdq_incl4 as (q & Hq_lookup & Hq_incl).
      rewrite /to_dqmap lookup_fmap in Hq_lookup.
      apply fmap_Some_equiv in Hq_lookup as (v_stored & Hdq_τ & Hq_eq).
      rewrite Hq_eq in Hq_incl.
      rewrite Some_included in Hq_incl.
      assert (v_stored = NONEV) as Hv_eq.
      { destruct Hq_incl as [Heq|Hin].
        - symmetry. by apply (inj to_agree), leibniz_equiv in Heq.
        - symmetry. rewrite to_agree_included in Hin. by apply leibniz_equiv. }
      rewrite Hv_eq in Hdq_τ.
      pose proof (Hdqi4 _ _ Hdq_τ) as Hrv_τ_NONEV.
      assert (v_rv = NONEV) as -> by (rewrite Hrv_τ_v in Hrv_τ_NONEV; injection Hrv_τ_NONEV; done).
      destruct s_4 as [O_4 lt_4 ℓ_4 rv_4 cp_4]; simpl in Hcp_τ_R2, Hrv_τ_v.
      iAssert (trace_is l ts_4 ∗
               ⌜I_lang_bq (ts_4 ++ [(τ, Ret NONEV)])⌝)%I
        with "[$Htrace4]" as "Halpha".
      { iPureIntro.
        exists (AbsQState O_4 lt_4 ℓ_4 rv_4 (<[τ := R3]> cp_4)),
               (ls_4 ++ [(τ, ARetDeq NONEV)]).
        split.
        - eapply rtcL_r; [exact Hsteps4|].
          by apply absq_step_ret_deq.
        - rewrite Hts_eq4 /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute. }
      iAaccIntro with "Halpha".
      { iIntros "[Htrace4 _]". iModIntro.
        rewrite bi.sep_assoc. iSplitR "Hfrag"; last eauto.
        iSplitR "HΦ"; last by eauto.
        iNext. iExists nodes_4, del_pref_4, head_val_4, tail_val_4, dummy_loc_4, ts_4,
          {| absq_O := O_4; absq_lt := lt_4; absq_l := ℓ_4;
             absq_rv := rv_4; absq_cp := cp_4 |}, ls_4,
          op_map_4, node_map_4, dq_map_4, no_O_set_4, witness_map_4.
        iFrame. iPureIntro.
        split; [exact Hsteps4|].
        split; [exact Hts_eq4|].
        split; [exact Hsim4|].
        split; [exact Hdummy4|].
        split; [exact Hnvi4|].
        split; [exact Hdqi4|].
        split; [exact Hno_O_inv4|].
        split; [exact Hcoi4|]. exact Hwit4. }
      iIntros "Htrace4".
      iMod (own_update_2 _ _ _ (● to_opmap (delete τ op_map_4))
              with "Hauth_op4 Hfrag") as "Hauth_op4".
      { apply auth_update_dealloc.
        rewrite /to_opmap fmap_delete.
        apply: delete_singleton_local_update. }
      iMod (own_update _ _
              (●ML (ls_4 ++ [(τ, ARetDeq NONEV)] : list (leibnizO (positive * absq_action))))
              with "Hauth_ls4") as "Hauth_ls4".
      { apply mono_list_update. by apply prefix_app_r. }
      iModIntro.
      iSplitL "Hhead4 Htail4 Hchain4 Htrace4 Hauth_op4 Hauth_nm4 Hfrag_nm4 Hauth_dq4 Hfrag_dq4 Hauth_del4 Hauth_calls4 Hauth_no_O4 Hauth_ls4 Hauth_w4 Hfrag_w4".
      { iNext.
        iExists nodes_4, del_pref_4, head_val_4, tail_val_4, dummy_loc_4,
          (ts_4 ++ [(τ, Ret NONEV)]),
          {| absq_O := O_4; absq_lt := lt_4; absq_l := ℓ_4; absq_rv := rv_4;
             absq_cp := <[τ := R3]> cp_4 |},
          (ls_4 ++ [(τ, ARetDeq NONEV)]), (delete τ op_map_4),
          node_map_4, dq_map_4, no_O_set_4, witness_map_4.
        iFrame "Hhead4 Htail4 Hchain4 Htrace4 Hauth_op4 Hauth_nm4 Hfrag_nm4
                Hauth_dq4 Hfrag_dq4 Hauth_del4 Hauth_ls4 Hauth_no_O4 Hauth_w4 Hfrag_w4".
        rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R2)). iFrame "Hauth_calls4".
        iPureIntro. split_and!.
        - eapply rtcL_r; [exact Hsteps4|].
          by apply absq_step_ret_deq.
        - rewrite Hts_eq4 /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute.
        - (* bq_sim *)
          destruct Hsim4 as (Hlen4 & Hdel4 & _ & Hdomsub4 & Hnm_dom4 & Henq_clause4
                             & _ & Hinj4 & Hcorr4 & Hlt_pos4 & _Htbd4 & Hcomp_link4
                             & Htail_in4 & Hhead_in4 & Hnm_chain4 & Hsome_at_pos4).
          split_and!; simpl.
          + exact Hlen4.
          + exact Hdel4.
          + rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R2)) fmap_app /= list_to_set_app_L.
            clear -Hcp_in_ts4. set_solver.
          + rewrite dom_insert_L dom_delete_L.
            assert (τ ∈ dom cp_4) as Hτ_in_cp_4 by (apply elem_of_dom; by eexists).
            clear -Hdomsub4 Hτ_in_cp_4. set_solver.
          + exact Hnm_dom4.
          + (* clause 6 *)
            intros τ' d' node' linked' Hop'.
            assert (τ' ≠ τ) as Hne.
            { intros ->. rewrite lookup_delete_eq in Hop'. discriminate. }
            rewrite lookup_delete_ne in Hop'; last done.
            destruct (Henq_clause4 _ _ _ _ Hop') as (Hcp & Hℓ & Hpre & Hpost).
            split_and!.
            { rewrite lookup_insert_ne; [exact Hcp|done]. }
            { exact Hℓ. }
            { exact Hpre. }
            { exact Hpost. }
          + (* clause 7 *)
            intros τ' obs' rng' node' linked' Hop'.
            assert (τ' ≠ τ) as Hne.
            { intros ->. rewrite lookup_delete_eq in Hop'. discriminate. }
            rewrite lookup_delete_ne in Hop'; last done.
            destruct (Hdeq_clause4 _ _ _ _ _ Hop') as (Hnone & Hpre & Hpost).
            split_and!.
            { exact Hnone. }
            { intros Hb. rewrite lookup_insert_ne; [|done]. by apply Hpre. }
            { intros Hb. destruct (Hpost Hb) as (Hcp_R2' & v_rv' & Hrv_v').
              rewrite lookup_insert_ne; [|done]. split; first done. by exists v_rv'. }
          + exact Hinj4.
          + exact Hcorr4.
          + exact Hlt_pos4.
          + done.
          + exact Hcomp_link4.
          + exact Htail_in4.
          + exact Hhead_in4.
          + exact Hnm_chain4.
          + exact Hsome_at_pos4.
        - exact Hdummy4.
        - exact Hnvi4.
        - exact Hdqi4.
        - apply Hno_O_inv4.
        - apply Hno_O_inv4.
        - (* chain_op_inv: τ deleted from op_map; for τ' at chain pos,
             new op_map at τ' equals old via lookup_delete_ne. *)
          intros i loc τ' v Hpos Hlk info Hop_lk.
          pose proof (Hcoi4 _ _ _ _ Hpos Hlk) as Hlinked.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_delete_eq in Hop_lk. discriminate.
          + rewrite lookup_delete_ne in Hop_lk; [|done].
            exact (Hlinked _ Hop_lk).
        - (* chain_witness_inv: RET-DEQ doesn't change chain or lt; cp gains
             entries (τ moves R2 → R3, still in cp).  Witness preserved. *)
          destruct Hwit4 as [Hwit_dom Hwit_per].
          split.
          { simpl. clear -Hwit_dom. set_solver. }
          intros τ' snap Hwit_lookup.
          exact (Hwit_per τ' snap Hwit_lookup). }
      wp_pures.
      iApply ("HΦ" $! NONEV with "[//]").
  Qed.

End bq_skeleton_deq_cont.
