(* refine_op_spec.v: proof of [op_spec] — the
  [call_ret_wrapper]-level Hoare triple for the entries of [impl.ops]
  that [bdgjst_free] consumes.  Handles the CALL commit
  via [trace_fresh] and delegates the bulk of the body to
  [op_spec_enq_cont] / [op_spec_deq_cont]. *)

From iris.algebra Require Import auth excl gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import encodable linear adequacy.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.hw_queue Require Import impl refine.defs
                                          refine.enq_cont refine.deq_cont.

Section hwq_skeleton_op_spec.
  Context `{!traceG Σ, !hwqG Σ}.
  Context (sz : Z).
  Hypothesis sz_pos : (0 < sz)%Z.

  Local Notation valid_value := hwq_valid_value.
  Local Notation Nhwq := Nhwq.
  Local Notation hwq_inv_body := (hwq_inv_body sz).
  Local Notation is_hwq := (is_hwq sz).
  Local Notation hwq_repr := (hwq_repr sz).
  Local Notation op_spec_enq_cont :=
    (op_spec_enq_cont sz sz_pos).
  Local Notation op_spec_deq_cont :=
    (op_spec_deq_cont sz sz_pos).

  Lemma op_spec :
    ∀ `(!heapGS Σ), call_ret_wrapper_spec_type
      hwq_repr NotStuck (queue_model NeverEmpty valid_value).(valid_requests) ops.
  Proof.
    iIntros (Hheap n γ l obj req Hvalid Φ) "[#Htrace_inv #Hq] HΦ".
    iDestruct "Hq" as (ar back γ_sv γ_dq) "[%Heq #Hinv]". subst obj.
    (* [queue_model] declares exactly the two operations [Push] and [Pop]. *)
    assert (Hop : (n = Push ∧ valid_value req) ∨ (n = Pop ∧ req = #())).
    { destruct n as [|[|n]]; simpl in Hvalid;
        [by left|by right|by destruct Hvalid]. }
    rewrite /call_ret_wrapper. wp_pures.
    wp_bind (trace_fresh _ _).
    awp_apply (trace_fresh_spec _ (Call n req) (InjLV (#n, req)%V) (I_lang_hwq)
                with "Htrace_inv").
    { exact (decode_encode_val (Call n req)). }
    iInv Nhwq as (items back_val ts s ls op_map stored_at cell_val_map dq_map)
      "(>Hback & >Har & >Htrace & >Hauth & >Hauth_sv & Hfrag_sv & >Hauth_dq & Hfrag_dq & >%Hsteps & >%Hts_eq & >%Hsim & >%Hcvi & >%Hdqi)".
    destruct s as [O_s lt_s l_s rv_s cp_s].
    iAssert (trace_is l ts ∗
      ⌜∀ τ, τ ∉ ts.*1 →
            I_lang_hwq (ts ++ [(τ, Call n req)])⌝)%I
      with "[$Htrace]" as "Halpha".
    { iPureIntro. intros τ Hτ_fresh.
      assert (τ ∉ dom cp_s) as Hτ_notin_cp.
      { destruct Hsim as (_ & _ & _ & Hcp_in_ts & _). simpl in *. set_solver. }
      destruct Hop as [(-> & Hd_valid) | (-> & ->)]; first rename req into d.
      - eexists _, (ls ++ [(τ, ACallEnq d)]).
        split.
        + eapply rtcL_r; [exact Hsteps|].
          apply absq_step_call_enq; done.
        + rewrite Hts_eq /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True.
          { done. }
          by compute.
      - eexists _, (ls ++ [(τ, ACallDeq)]).
        split.
        + eapply rtcL_r; [exact Hsteps|].
          apply absq_step_call_deq; done.
        + rewrite Hts_eq /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True.
          { done. }
          by compute. }
    iAaccIntro with "Halpha".
    { iIntros "[Htrace _]". iModIntro.
      iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq"; last done.
      iNext. iExists items, back_val, ts, _, ls, op_map, stored_at, cell_val_map, dq_map. by iFrame. }
    iIntros (τ) "[Htrace %Hτ_fresh]".
    assert (τ ∉ dom cp_s) as Hτ_notin_cp.
    { destruct Hsim as (_ & _ & _ & Hcp_in_ts & _). simpl in *. set_solver. }
    assert (op_map !! τ = None) as Hτ_notin_opmap.
    { destruct Hsim as (_ & _ & _ & _ & Hdomsub & _). simpl in *.
      apply not_elem_of_dom. set_solver. }
    destruct Hop as [(-> & Hd_valid) | (-> & ->)]; first rename req into d.
    - (* Enqueue case: CALL-ENQ commit. *)
      pose proof (valid_value_unbox _ Hd_valid) as Hd_unboxed.
      set (new_info := {| op_info_kind := OpEnq d;
                          op_info_reserved := None;
                          op_info_stored := false |}).
      iMod (own_update _ _
              (● to_opmap (<[τ := new_info]> op_map)
               ⋅ ◯ {[τ := Excl new_info]}) with "Hauth") as "[Hauth Hfrag]".
      { apply (auth_update_alloc _ (to_opmap (<[τ := new_info]> op_map))
                 ({[τ := Excl new_info]})).
        rewrite /to_opmap fmap_insert.
        apply: alloc_singleton_local_update; [|done].
        rewrite lookup_fmap Hτ_notin_opmap //. }
      iModIntro.
      iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
      { iNext.
        iExists items, back_val, (ts ++ [(τ, Call Push d)]),
          {| absq_O := O_s ∪ {[τ]};
             absq_lt := lt_s ∪ set_map (λ k', (k', τ)) (absq_COMP O_s l_s);
             absq_l := <[τ := (d, PEND)]> l_s;
             absq_rv := rv_s;
             absq_cp := <[τ := A1]> cp_s |},
          (ls ++ [(τ, ACallEnq d)]),
          (<[τ := new_info]> op_map), stored_at, cell_val_map, dq_map.
        iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
        iPureIntro. split_and!.
        - eapply rtcL_r; [exact Hsteps|].
          apply absq_step_call_enq; done.
        - rewrite Hts_eq /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute.
        - destruct Hsim as
            (Hlen & Hback_lo & Hslots_free & Hcp_fresh
             & Hdomsub & Henq_clause & Hdeq_clause & Hreserved_unique
             & Hcells_wf & Hcells_fwd & Hstored & Hstored_inj & Hcells_stored & Hnot_stored & Hstored_link & Hres_fresh & Hobs_hist & Hlt_res & Hobs_struct & Hcomp_stored & Hlt_stored & Hrng_τ_bound & Hlt_res_obs & Hlt_res_obs_st).
          split_and!; simpl in *.
          + exact Hlen.
          + exact Hback_lo.
          + exact Hslots_free.
          + rewrite dom_insert_L fmap_app /= list_to_set_app_L.
            clear -Hcp_fresh. set_solver.
          + rewrite !dom_insert_L. clear -Hdomsub. set_solver.
          + intros τ' d' r' b' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              injection Hlookup as Hkind Hres Hstore; subst.
              split_and!.
              { by rewrite lookup_insert_eq. }
              { by rewrite lookup_insert_eq. }
              { intros _. clear. set_solver. }
              intros i Hr_eq. discriminate.
            * rewrite lookup_insert_ne in Hlookup; last done.
              destruct (Henq_clause _ _ _ _ Hlookup)
                as (Hcp_eq & Hl_eq & HbO & Hreserv).
              split_and!.
              { rewrite lookup_insert_ne //. }
              { rewrite lookup_insert_ne //. }
              { intros Hb_false. specialize (HbO Hb_false). clear -HbO. set_solver. }
              intros i Hr_eq.
              destruct (Hreserv _ Hr_eq) as (Hrng & Himpl).
              split_and!.
              -- lia.
              -- lia.
              -- intros Hi_lt_sz.
                 destruct (Himpl Hi_lt_sz) as (Hfalse_case & Htrue_case).
                 split.
                 ++ intros Hb_false. by apply Hfalse_case.
                 ++ intros Hb_true.
                    destruct (Htrue_case Hb_true) as [Hin Hout].
                    split.
                    *** intros Hτ'_in. apply Hin. clear -Hne Hτ'_in. set_solver.
                    *** intros Hτ'_out. apply Hout. clear -Hτ'_out. set_solver.
          + intros τ' obs' rng_τ' r' b' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              injection Hlookup as Hkind. discriminate.
            * rewrite lookup_insert_ne in Hlookup; last done.
              destruct (Hdeq_clause _ _ _ _ _ Hlookup) as (Hcp_false & Hcp_true).
              split.
              -- intros Hbf. rewrite lookup_insert_ne //. by apply Hcp_false.
              -- intros Hbt. destruct (Hcp_true Hbt) as (Hcp & d_t & Hrv).
                 rewrite lookup_insert_ne //. split; [exact Hcp|].
                 exists d_t. exact Hrv.
          + intros τ_a τ_b d_a d_b i b_a b_b.
            destruct (decide (τ_a = τ)) as [->|Hne_a].
            { rewrite lookup_insert_eq. intros [=]. }
            destruct (decide (τ_b = τ)) as [->|Hne_b].
            { rewrite lookup_insert_eq. intros _ [=]. }
            rewrite !lookup_insert_ne; [|done|done].
            by apply Hreserved_unique.
          + exact Hcells_wf.
          + intros i d' Hitems_i.
            destruct (Hcells_fwd _ _ Hitems_i) as (k_e & Hk_e_O & f' & Hℓ_k_e).
            exists k_e. split_and!; simpl; [clear -Hk_e_O; set_solver|].
            exists f'.
            assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s))
              as Hwf_s.
            { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
            assert (k_e ≠ τ) as Hk_e_ne.
            { intros ->. apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s).
              apply elem_of_dom. by exists (d', f'). }
            by rewrite lookup_insert_ne.
          + intros τ' i' Hlookup.
            destruct (Hstored _ _ Hlookup)
              as (Hbound' & d' & f' & Hℓ' & HinO' & HnotO').
            split; [exact Hbound'|].
            assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s))
              as Hwf_s.
            { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
            assert (τ' ≠ τ) as Hτ'_ne.
            { intros ->. apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s).
              apply elem_of_dom. by exists (d', f'). }
            exists d', f'. split_and!; simpl.
            * rewrite lookup_insert_ne //.
            * intros Hτ'_inO. apply HinO'.
              move: Hτ'_inO. simpl. clear -Hτ'_ne. set_solver.
            * intros Hτ'_notinO. apply HnotO'.
              move: Hτ'_notinO. simpl. clear. set_solver.
          + exact Hstored_inj.
          + intros i d' Hitems_i.
            destruct (Hcells_stored _ _ Hitems_i)
              as (τ' & Hstored_τ' & Hτ'_O & f' & Hℓ_τ').
            assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s))
              as Hwf_s.
            { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
            assert (τ' ≠ τ) as Hτ'_ne.
            { intros ->. apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s).
              apply elem_of_dom. by exists (d', f'). }
            exists τ'. split_and!.
            * exact Hstored_τ'.
            * simpl. clear -Hτ'_O. set_solver.
            * exists f'. rewrite lookup_insert_ne //.
          + intros τ' d' r' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * destruct (stored_at !! τ) eqn:Hst; last done.
              exfalso.
              destruct (Hstored _ _ Hst) as (_ & d'' & f'' & Hℓ'' & _).
              assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s))
                as Hwf_s.
              { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
              apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s).
              apply elem_of_dom. by exists (d'', f'').
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply Hnot_stored.
          + intros τ' d' i' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              injection Hlookup as _ _ Hstore. discriminate Hstore.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply Hstored_link.
          + intros τ' d' r' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              subst new_info. inversion Hlookup.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply Hres_fresh.
          + intros τ' obs' rng_τ' r' b' Hlookup Hb' j k' Hk'_in.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              subst new_info. inversion Hlookup.
            * rewrite lookup_insert_ne in Hlookup; last done.
              destruct (Hobs_hist _ _ _ _ _ Hlookup Hb' _ _ Hk'_in)
                as (Hstored_k' & Hk'_notO).
              assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s))
                as Hwf_s.
              { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
              assert (k' ≠ τ) as Hk'_ne.
              { intros ->.
                destruct (Hstored _ _ Hstored_k')
                  as (_ & d_k' & f_k' & Hℓ_k' & _).
                apply Hτ_notin_cp.
                apply (absq_wf_dom _ _ Hwf_s).
                apply elem_of_dom. by eexists. }
              split; [exact Hstored_k'|].
              simpl. intros Hk_in.
              apply elem_of_union in Hk_in as [HkO|HkS];
                [contradiction|].
              apply elem_of_singleton in HkS. by subst.
          + (* Hlt_res (CALL-ENQ): new τ has reserved=None so the
              OpEnq-with-Some pattern fails on τ.  For existing (k, k_e)
              ∈ lt: k_e ≠ τ (τ is fresh); op_map, stored_at unchanged. *)
            intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
            destruct (decide (k_e' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              subst new_info. injection Hlookup as _ Hres _.
              discriminate Hres.
            * rewrite lookup_insert_ne in Hlookup; last done.
              (* lt grew by (k', τ) pairs; for existing (k, k_e') ∈ lt_s, apply. *)
              assert ((k, k_e') ∈ lt_s) as Hlt_old.
              { simpl in Hlt.
                apply elem_of_union in Hlt as [Hlt_l|Hlt_r]; [done|].
                apply elem_of_map in Hlt_r as (k'' & Heq & _).
                inversion Heq. contradiction. }
              by eapply (Hlt_res _ _ _ _ _ Hlt_old Hlookup _ Hstored_k).
          + (* Hobs_struct (CALL-ENQ): new τ is OpEnq, pattern mismatch.
              Other τ' ≠ τ unchanged. *)
            intros τ' obs' rng_τ' r' b' Hlookup Hb' i_idx Hi_lt.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              subst new_info. inversion Hlookup.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply (Hobs_struct _ _ _ _ _ Hlookup Hb' _ Hi_lt).
          + (* Hcomp_stored (CALL-ENQ): new τ has ℓ[τ]=(d, PEND), not
              COMP; existing entries unchanged. *)
            intros k d_k Hℓ_k.
            destruct (decide (k = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hℓ_k. inversion Hℓ_k.
            * rewrite lookup_insert_ne in Hℓ_k; last done.
              by eapply Hcomp_stored.
          + (* Hlt_stored (CALL-ENQ): stored_at unchanged; lt grows by
              (k', τ) pairs but stored_at[τ]=None so vacuous. *)
            intros k k_e' r_k r_k_e Hlt Hstored_k Hstored_k_e.
            (* stored_at[τ] = None since τ fresh. *)
            assert (stored_at !! τ = None) as Hst_τ.
            { destruct (stored_at !! τ) eqn:Hst; last done.
              exfalso.
              destruct (Hstored _ _ Hst) as (_ & d_τ & f_τ & Hℓ_τ & _).
              assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s))
                as Hwf_s.
              { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
              apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s).
              apply elem_of_dom. by eexists. }
            assert (k_e' ≠ τ) as Hne_e.
            { intros ->. rewrite Hst_τ in Hstored_k_e. discriminate. }
            assert (k ≠ τ) as Hne_k.
            { intros ->. rewrite Hst_τ in Hstored_k. discriminate. }
            assert ((k, k_e') ∈ lt_s) as Hlt_old.
            { simpl in Hlt.
              apply elem_of_union in Hlt as [Hlt_l|Hlt_r]; [done|].
              apply elem_of_map in Hlt_r as (k'' & Heq & _).
              inversion Heq. contradiction. }
            by eapply (Hlt_stored _ _ _ _ Hlt_old Hstored_k Hstored_k_e).
          + (* Hrng_τ_bound (CALL-ENQ): back_val unchanged; new τ is
              OpEnq so pattern mismatch. *)
            intros τ' obs' rng_τ' r' b' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              injection Hlookup as Hkind _ _. discriminate.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply Hrng_τ_bound.
          + (* Hlt_res_obs (CALL-ENQ): new lt edges (k', τ) have
              [op_map τ] = OpEnq with [reserved = None], so the
              [Some r_e] premise fails.  For existing edges: unchanged. *)
            intros τ' obs' rng_τ' r' Hlookup
                   k k_e d' r_e b_e Hlt Hlookup_e Hr_e_lt
                   r_k Hstored_k Hr_k_lt.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hlookup.
              injection Hlookup as Hkind _. discriminate. }
            rewrite lookup_insert_ne in Hlookup; last done.
            destruct (decide (k_e = τ)) as [->|Hne_e].
            { rewrite lookup_insert_eq in Hlookup_e.
              injection Hlookup_e as _ Hres _. discriminate. }
            rewrite lookup_insert_ne in Hlookup_e; last done.
            assert ((k, k_e) ∈ lt_s) as Hlt_old.
            { simpl in Hlt.
              apply elem_of_union in Hlt as [Hlt_l|Hlt_r]; [done|].
              apply elem_of_map in Hlt_r as (k'' & Heq & _).
              inversion Heq. contradiction. }
            by eapply (Hlt_res_obs _ _ _ _ Hlookup _ _ _ _ _
                         Hlt_old Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
          + (* Hlt_res_obs_st (CALL-ENQ): new lt edges (k', τ) have
              τ not in stored_at yet.  For existing (k, k_e): unchanged. *)
            intros τ' obs' rng_τ' r' Hlookup
                   k k_e r_k_e Hlt Hstored_k_e Hr_k_e_lt
                   r_k Hstored_k Hr_k_lt.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hlookup.
              injection Hlookup as Hkind _. discriminate. }
            rewrite lookup_insert_ne in Hlookup; last done.
            (* stored_at τ = None (τ fresh). *)
            assert (stored_at !! τ = None) as Hst_τ.
            { destruct (stored_at !! τ) eqn:Hst; last done.
              exfalso.
              destruct (Hstored _ _ Hst) as (_ & d_τ & f_τ & Hℓ_τ & _).
              assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s))
                as Hwf_s.
              { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
              apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s).
              apply elem_of_dom. by eexists. }
            assert (k_e ≠ τ) as Hne_e.
            { intros ->. rewrite Hst_τ in Hstored_k_e. discriminate. }
            assert (k ≠ τ) as Hne_k.
            { intros ->. rewrite Hst_τ in Hstored_k. discriminate. }
            assert ((k, k_e) ∈ lt_s) as Hlt_old.
            { simpl in Hlt.
              apply elem_of_union in Hlt as [Hlt_l|Hlt_r]; [done|].
              apply elem_of_map in Hlt_r as (k'' & Heq & _).
              inversion Heq. contradiction. }
            by eapply (Hlt_res_obs_st _ _ _ _ Hlookup _ _ _
                         Hlt_old Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt).
        - (* cell_val_inv (CALL-ENQ): stored_at unchanged; ℓ gains
            (τ, (d, PEND)), but τ is fresh so it's not in stored_at;
            cell_val_map also unchanged.  Both directions preserved. *)
          destruct Hsim as
            (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstored_cvi
             & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
          destruct Hcvi as (Hcvi_fwd & Hcvi_bwd).
          split; simpl.
          + intros τ_any i d_any f_any Hst Hℓ.
            destruct (decide (τ_any = τ)) as [->|Hne_τ].
            * exfalso.
              destruct (Hstored_cvi _ _ Hst) as (_ & d' & f' & Hℓ' & _).
              assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s))
                as Hwf_s.
              { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
              apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s).
              apply elem_of_dom. by exists (d', f').
            * rewrite lookup_insert_ne in Hℓ; last done.
              by eapply (Hcvi_fwd _ _ _ _ Hst Hℓ).
          + intros i v Hlookup_cv.
            destruct (Hcvi_bwd _ _ Hlookup_cv)
              as (τ_old & f_old & Hst_old & Hℓ_old).
            exists τ_old.
            destruct (decide (τ_old = τ)) as [->|Hne_τ].
            * exfalso.
              destruct (Hstored_cvi _ _ Hst_old) as (_ & d' & f' & Hℓ' & _).
              assert (absq_wf valid_value (AbsQState O_s lt_s l_s rv_s cp_s))
                as Hwf_s.
              { eapply absq_wf_steps; [exact Hsteps|apply absq_wf_init]. }
              apply Hτ_notin_cp.
              apply (absq_wf_dom _ _ Hwf_s).
              apply elem_of_dom. by exists (d', f').
            * exists f_old. split; [exact Hst_old|].
              by rewrite lookup_insert_ne.
        - (* dq_inv (CALL-ENQ): dq_map, rv both unchanged. *)
          exact Hdqi. }
      iApply (op_spec_enq_cont γ γ_sv γ_dq l ar back τ d Φ Hd_valid Hd_unboxed
                with "Hinv Htrace_inv Hfrag HΦ").
    - (* Dequeue case: CALL-DEQ commit + continuation.  [rng_τ] snapshot =
         [back_val] (at τ's CALL-DEQ); refreshed at each outer-Löb reset. *)
      set (new_info := {| op_info_kind := OpDeq [] back_val;
                          op_info_reserved := None;
                          op_info_stored := false |}).
      iMod (own_update _ _
              (● to_opmap (<[τ := new_info]> op_map)
               ⋅ ◯ {[τ := Excl new_info]}) with "Hauth") as "[Hauth Hfrag]".
      { apply (auth_update_alloc _ (to_opmap (<[τ := new_info]> op_map))
                 ({[τ := Excl new_info]})).
        rewrite /to_opmap fmap_insert.
        apply: alloc_singleton_local_update; [|done].
        rewrite lookup_fmap Hτ_notin_opmap //. }
      iModIntro.
      iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
      { iNext.
        iExists items, back_val, (ts ++ [(τ, Call Pop #())]),
          {| absq_O := O_s;
             absq_lt := lt_s;
             absq_l := l_s;
             absq_rv := rv_s;
             absq_cp := <[τ := R1]> cp_s |},
          (ls ++ [(τ, ACallDeq)]), (<[τ := new_info]> op_map), stored_at, cell_val_map, dq_map.
        iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
        iPureIntro. split_and!.
        - eapply rtcL_r; [exact Hsteps|].
          apply absq_step_call_deq; done.
        - rewrite Hts_eq /trace_of_absq_labels map_app /= filter_app.
          rewrite filter_cons_True; [done|]. by compute.
        - destruct Hsim as (Hlen & Hback_lo & Hslots_free & Hcp_fresh
                            & Hdomsub & Henq_clause & Hdeq_clause & Hreserved_unique
                            & Hcells_wf & Hcells_fwd & Hstored & Hstored_inj & Hcells_stored & Hnot_stored & Hstored_link & Hres_fresh & Hobs_hist & Hlt_res & Hobs_struct & Hcomp_stored & Hlt_stored & Hrng_τ_bound & Hlt_res_obs & Hlt_res_obs_st).
          split_and!; simpl in *.
          + exact Hlen.
          + exact Hback_lo.
          + exact Hslots_free.
          + rewrite dom_insert_L fmap_app /= list_to_set_app_L. clear -Hdomsub Hcp_fresh. set_solver.
          + rewrite !dom_insert_L. clear -Hdomsub Hcp_fresh. set_solver.
          + intros τ' d' r' b' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup. inversion Hlookup.
            * rewrite lookup_insert_ne in Hlookup; last done.
              destruct (Henq_clause _ _ _ _ Hlookup)
                as (Hcp_eq & Hl_eq & HbO & Hreserv).
              split_and!.
              { rewrite lookup_insert_ne //. }
              { exact Hl_eq. }
              { done. }
              intros i Hr_eq. destruct (Hreserv _ Hr_eq) as (Hrng & Himpl).
              split_and!; [lia|lia|exact Himpl].
          + intros τ' obs' rng_τ' r' b' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              inversion Hlookup; subst.
              split.
              { intros _. by rewrite lookup_insert_eq. }
              { intros [=]. }
            * rewrite lookup_insert_ne in Hlookup; last done.
              destruct (Hdeq_clause _ _ _ _ _ Hlookup) as (Hcp_false & Hcp_true).
              split.
              { intros Hbf. rewrite lookup_insert_ne //. by apply Hcp_false. }
              { intros Hbt. destruct (Hcp_true Hbt) as (Hcp & d_t & Hrv).
                rewrite lookup_insert_ne //. split; [exact Hcp|].
                exists d_t. exact Hrv. }
          + intros τ_a τ_b d_a d_b i b_a b_b.
            destruct (decide (τ_a = τ)) as [->|Hne_a].
            { rewrite lookup_insert_eq. inversion 1. }
            destruct (decide (τ_b = τ)) as [->|Hne_b].
            { rewrite lookup_insert_eq. intros _. inversion 1. }
            rewrite !lookup_insert_ne; [|done|done].
            by apply Hreserved_unique.
          + exact Hcells_wf.
          + exact Hcells_fwd.
          + exact Hstored.
          + exact Hstored_inj.
          + exact Hcells_stored.
          + intros τ' d' r' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup. discriminate.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply Hnot_stored.
          + intros τ' d' i' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup. discriminate.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply Hstored_link.
          + intros τ' d' r' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup. discriminate.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply Hres_fresh.
          + intros τ' obs' rng_τ' r' b' Hlookup Hb' j k' Hk'_in.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              subst new_info. inversion Hlookup; subst.
              inversion Hk'_in.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply (Hobs_hist _ _ _ _ _ Hlookup Hb' _ _ Hk'_in).
          + (* Hlt_res (CALL-DEQ): τ is OpDeq, pattern mismatch for k_e=τ.
              lt unchanged.  For k_e ≠ τ: apply Hlt_res. *)
            intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
            destruct (decide (k_e' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup. discriminate.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply Hlt_res.
          + (* Hobs_struct (CALL-DEQ): new τ has obs = [], vacuous.
              For τ' ≠ τ unchanged. *)
            intros τ' obs' rng_τ' r' b' Hlookup Hb' i_idx Hi_lt.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              subst new_info. inversion Hlookup; subst obs'.
              inversion Hi_lt.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply (Hobs_struct _ _ _ _ _ Hlookup Hb' _ Hi_lt).
          + (* Hcomp_stored (CALL-DEQ): ℓ, stored_at unchanged. *)
            exact Hcomp_stored.
          + (* Hlt_stored (CALL-DEQ): lt, stored_at unchanged. *)
            exact Hlt_stored.
          + (* Hrng_τ_bound (CALL-DEQ): new τ has rng_τ = back_val; others
              unchanged. *)
            intros τ' obs' rng_τ' r' b' Hlookup.
            destruct (decide (τ' = τ)) as [->|Hne].
            * rewrite lookup_insert_eq in Hlookup.
              subst new_info. injection Hlookup as _ <- _ _. lia.
            * rewrite lookup_insert_ne in Hlookup; last done.
              by eapply Hrng_τ_bound.
          + (* Hlt_res_obs (CALL-DEQ): τ's new obs = [], length 0
              impossible.  For τ' ≠ τ: unchanged. *)
            intros τ' obs' rng_τ' r' Hlookup
                   k k_e d' r_e b_e Hlt Hlookup_e Hr_e_lt
                   r_k Hstored_k Hr_k_lt.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hlookup.
              subst new_info. injection Hlookup as <- <- <-.
              simpl in Hr_k_lt. lia. }
            rewrite lookup_insert_ne in Hlookup; last done.
            destruct (decide (k_e = τ)) as [->|Hne_e].
            { rewrite lookup_insert_eq in Hlookup_e. discriminate. }
            rewrite lookup_insert_ne in Hlookup_e; last done.
            by eapply (Hlt_res_obs _ _ _ _ Hlookup _ _ _ _ _
                         Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
          + (* Hlt_res_obs_st (CALL-DEQ): τ's new obs = [], vacuous.
              For τ' ≠ τ: stored_at unchanged, obs unchanged. *)
            intros τ' obs' rng_τ' r' Hlookup
                   k k_e r_k_e Hlt Hstored_k_e Hr_k_e_lt
                   r_k Hstored_k Hr_k_lt.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hlookup.
              subst new_info. injection Hlookup as <- <- <-.
              simpl in Hr_k_lt. lia. }
            rewrite lookup_insert_ne in Hlookup; last done.
            by eapply (Hlt_res_obs_st _ _ _ _ Hlookup _ _ _
                         Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt).
        - (* cell_val_inv (CALL-DEQ): stored_at, ℓ unchanged. *)
          simpl. exact Hcvi.
        - (* dq_inv (CALL-DEQ): dq_map, rv both unchanged. *)
          simpl. exact Hdqi. }
      iApply (op_spec_deq_cont γ γ_sv γ_dq l ar back τ back_val Φ
                with "Hinv Htrace_inv Hfrag HΦ").
  Qed.

End hwq_skeleton_op_spec.
