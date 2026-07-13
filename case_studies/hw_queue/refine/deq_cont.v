(* refine_deq_cont.v: proof of [op_spec_deq_cont] — the
  dequeue branch of [op_spec].  Covers the outer Löb retry
  loop, the inner dequeue_aux loop with NONEV/SOMEV load and CAS
  success/fail, the LIN-DEQ1 linearisation step, and the RET-DEQ
  commit.  CAS-success minimality discharge (task #47), SOMEV-e
  CAS-fail impossibility (task #58+#59, cross-iInv agreeR on
  [γ_sv]), and RET-DEQ commit (task #49, via [γ_dq] agreeR) are
  all fully proved. *)

From iris.algebra Require Import auth excl gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.hw_queue Require Import impl refine.defs.

Section hwq_skeleton_deq_cont.
  Context `{!traceG Σ, !hwqG Σ}.
  Context (sz : Z).
  Hypothesis sz_pos : (0 < sz)%Z.

  Local Notation valid_value := hwq_valid_value.
  Local Notation Nhwq := Nhwq.
  Local Notation hwq_inv_body := (hwq_inv_body sz).
  Local Notation is_hwq := (is_hwq sz).

  (* Dequeue continuation — Pass 2.  [rng_init] is the [back_val]
    snapshot from CALL-DEQ, bundled into the initial [OpDeq] fragment.
    Each outer-Löb reset refreshes this to the current [back_val]. *)
  Lemma op_spec_deq_cont
    `{!heapGS Σ} (γ γ_sv γ_dq : gname) (l ar back : loc)
    (τ : positive) (rng_init : Z) (Φ : val → iProp Σ) :
    inv Nhwq (hwq_inv_body γ γ_sv γ_dq ar back l) -∗
    trace_inv l (I_lang_hwq) -∗
    own γ (◯ {[τ := Excl {| op_info_kind := OpDeq [] rng_init;
                            op_info_reserved := None;
                            op_info_stored := false |}]}) -∗
    (∀ v : val, True -∗ Φ v) -∗
    WP (let: "τ" := #(Z.pos τ) in
        let: "res" := op (#sz, #ar, #back)%V NONEV in
        trace_emit #l "τ" (InjR "res");; "res")
    {{ Φ }}.
  Proof.
    iIntros "#Hinv #Htrace_inv Hfrag HΦ".
    wp_pures.
    rewrite /op. wp_pures.
    wp_bind (dequeue _)%E.
    iAssert (∀ (obs : list (Z * option positive)) (rng_τ : Z),
      own γ (◯ {[τ := Excl {| op_info_kind := OpDeq obs rng_τ;
                              op_info_reserved := None;
                              op_info_stored := false |}]}) -∗
      WP dequeue (#sz, #ar, #back)%V {{ v, ∃ obs_f rng_τ_f,
        own γ (◯ {[τ := Excl {| op_info_kind := OpDeq obs_f rng_τ_f;
                                op_info_reserved := None;
                                op_info_stored := true |}]}) ∗
        own γ_dq (◯ {[τ := to_agree v]}) }})%I
      with "[]" as "Hdeq_spec".
    { iIntros (obs rng_τ) "Hfrag".
      iLöb as "IH_outer" forall (obs rng_τ) "Hfrag".
      rewrite /dequeue. wp_pure _. wp_pures.
      wp_bind (! _)%E.
      iInv Nhwq as (items back_val ts s ls op_map stored_at cell_val_map dq_map)
        "(>Hback & >Har & >Htrace & >Hauth & >Hauth_sv & Hfrag_sv & >Hauth_dq & Hfrag_dq & >%Hsteps & >%Hts_eq & >%Hsim & >%Hcvi & >%Hdqi)".
      wp_load.
      (* Reset τ's [observed] list to [] at the start of each outer
         epoch: the length invariant [length obs' = Z.to_nat (rng - i)]
         requires [obs' = []] at inner entry with [i = rng], so we
         ghost-update the fragment here before entering the inner Löb. *)
      iDestruct (own_valid_2 with "Hauth Hfrag") as %Hboth_out.
      apply auth_both_valid_discrete in Hboth_out as [Hincl_out Hvalid_out].
      apply singleton_included_exclusive_l in Hincl_out; [|apply _|done].
      rewrite lookup_fmap in Hincl_out.
      apply leibniz_equiv in Hincl_out.
      apply fmap_Some_1 in Hincl_out
        as (info_τ_out & Hτ_in_opmap_out & Hinfo_τ_out).
      destruct info_τ_out; injection Hinfo_τ_out as <- <- <-.
      destruct Hsim as (Hlen_out & Hback_lo_out & Hslots_free_out & Hcp_fresh_out
                        & Hdomsub_out & Henq_clause_out & Hdeq_clause_out & Hruniq_out
                        & Hcells_wf_out & Hcells_fwd_out & Hstored_out & Hstored_inj_out
                        & Hcells_stored_out & Hnot_stored_out & Hstored_link_out
                        & Hres_fresh_out & Hobs_hist_out & Hlt_res_out & Hobs_struct_out
                        & Hcomp_stored_out & Hlt_stored_out
                        & Hrng_τ_bound_out & Hlt_res_obs_out & Hlt_res_obs_st_out).
      set (reset_info :=
        {| op_info_kind := OpDeq [] back_val;
           op_info_reserved := None;
           op_info_stored := false |}).
      iMod (own_update_2 _ _ _
              (● to_opmap (<[τ := reset_info]> op_map)
               ⋅ ◯ {[τ := Excl reset_info]}) with "Hauth Hfrag")
        as "[Hauth Hfrag]".
      { apply auth_update.
        rewrite /to_opmap fmap_insert.
        apply: singleton_local_update.
        { rewrite lookup_fmap Hτ_in_opmap_out //. }
        by apply exclusive_local_update. }
      iModIntro.
      iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
      { iNext.
        iExists items, back_val, ts, s, ls,
          (<[τ := reset_info]> op_map), stored_at, cell_val_map, dq_map.
        iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
        iPureIntro. split_and!; [exact Hsteps|exact Hts_eq| |exact Hcvi|exact Hdqi].
        split_and!; [exact Hlen_out|exact Hback_lo_out|exact Hslots_free_out
                    |exact Hcp_fresh_out| | | |
                    |exact Hcells_wf_out|exact Hcells_fwd_out
                    |exact Hstored_out|exact Hstored_inj_out
                    |exact Hcells_stored_out| | | | | | | | | | | ].
        - (* dom_sub: τ already in dom op_map. *)
          rewrite dom_insert_L.
          assert (τ ∈ dom op_map) as Hτ_dom.
          { apply elem_of_dom. by eexists. }
          clear -Hdomsub_out Hτ_dom. set_solver.
        - (* enq_clause: τ is OpDeq, pattern mismatch; else Henq_clause_out. *)
          intros τ' d' r' b' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            subst reset_info. injection Hlookup as Hkind. discriminate.
          + rewrite lookup_insert_ne in Hlookup; last done.
            exact (Henq_clause_out _ _ _ _ Hlookup).
        - (* deq_clause: τ's new entry still has stored=false, cp=R1. *)
          intros τ' obs'' rng_τ'' r' b' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            subst reset_info. injection Hlookup as <- <- <- <-.
            destruct (Hdeq_clause_out τ obs rng_τ None false Hτ_in_opmap_out)
              as (Hcp_false & Hcp_true).
            split; [exact Hcp_false|exact Hcp_true].
          + rewrite lookup_insert_ne in Hlookup; last done.
            exact (Hdeq_clause_out _ _ _ _ _ Hlookup).
        - (* reserved_unique: τ is OpDeq, pattern mismatch. *)
          intros τ_a τ_b d_a d_b i' b_a b_b Ha Hb.
          destruct (decide (τ_a = τ)) as [->|Hne_a].
          { rewrite lookup_insert_eq in Ha.
            injection Ha as Hkind. discriminate. }
          destruct (decide (τ_b = τ)) as [->|Hne_b].
          { rewrite lookup_insert_eq in Hb.
            injection Hb as Hkind. discriminate. }
          rewrite !lookup_insert_ne in Ha, Hb; [|done|done].
          by eapply Hruniq_out.
        - (* Hnot_stored: τ is OpDeq, pattern mismatch. *)
          intros τ' d' r' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup. discriminate.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply Hnot_stored_out.
        - (* Hstored_link: τ is OpDeq, pattern mismatch. *)
          intros τ' d' i' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup. discriminate.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply Hstored_link_out.
        - (* Hres_fresh: τ is OpDeq, OpEnq pattern fails. *)
          intros τ' d' r' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup. discriminate.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply Hres_fresh_out.
        - (* Hobs_hist: new obs=[], no Some entries; for other τ' unchanged. *)
          intros τ' obs'' rng_τ'' r' b' Hlookup Hb' j k' Hk'_in.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            subst reset_info. injection Hlookup as <- <- <- <-.
            inversion Hk'_in.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply (Hobs_hist_out _ _ _ _ _ Hlookup Hb' _ _ Hk'_in).
        - (* Hlt_res: τ is OpDeq, k_e=τ fails OpEnq pattern; else Hlt_res_out. *)
          intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
          destruct (decide (k_e' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup. discriminate.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply Hlt_res_out.
        - (* Hobs_struct (outer reset): τ's new obs is [] (vacuous).
            For τ' ≠ τ with OpDeq: unchanged. *)
          intros τ' obs' rng_τ' r' b' Hlookup Hb' i_idx Hi_lt.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            subst reset_info. injection Hlookup as <- <- <- <-.
            inversion Hi_lt.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply (Hobs_struct_out _ _ _ _ _ Hlookup Hb' _ Hi_lt).
        - (* Hcomp_stored (outer reset): ℓ, stored_at unchanged. *)
          exact Hcomp_stored_out.
        - (* Hlt_stored (outer reset): lt, stored_at unchanged. *)
          exact Hlt_stored_out.
        - (* Hrng_τ_bound (outer reset): τ's rng_τ = back_val (fresh
            snapshot); others unchanged, use Hrng_τ_bound_out. *)
          intros τ' obs'' rng_τ'' r' b' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            subst reset_info. injection Hlookup as _ <- _ _. lia.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply Hrng_τ_bound_out.
        - (* Hlt_res_obs (outer reset): τ's new obs is [], vacuous
            (r_k < length [] is impossible).  For τ' ≠ τ, unchanged. *)
          intros τ' obs'' rng_τ'' r' Hlookup k k_e d r_e b_e Hlt Hlookup_e Hr_e_lt
                 r_k Hstored_k Hr_k_lt.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            subst reset_info. injection Hlookup as <- <- <-.
            simpl in Hr_k_lt. lia.
          + rewrite lookup_insert_ne in Hlookup; last done.
            destruct (decide (k_e = τ)) as [->|Hne_e].
            * rewrite lookup_insert_eq in Hlookup_e. discriminate.
            * rewrite lookup_insert_ne in Hlookup_e; last done.
              by eapply (Hlt_res_obs_out _ _ _ _ Hlookup _ _ _ _ _ Hlt
                           Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
        - (* Hlt_res_obs_st (outer reset): τ's new obs is [], vacuous. *)
          intros τ' obs'' rng_τ'' r' Hlookup k k_e r_k_e Hlt
                 Hstored_k_e Hr_k_e_lt r_k Hstored_k Hr_k_lt.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            subst reset_info. injection Hlookup as <- <- <-.
            simpl in Hr_k_lt. lia.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply (Hlt_res_obs_st_out _ _ _ _ Hlookup _ _ _ Hlt
                         Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt). }
      wp_pures.
      wp_apply minimum_spec.
      wp_pures.
      set (rng := (back_val `min` sz)%Z).
      assert (Hrng_lo : (0 ≤ rng)%Z) by (subst rng; lia).
      assert (Hrng_hi : (rng ≤ sz)%Z) by (subst rng; lia).
      iAssert (∀ (i : Z) (obs' : list (Z * option positive)),
        ⌜(0 ≤ i ≤ rng)%Z⌝ -∗
        ⌜length obs' = Z.to_nat (rng - i)⌝ -∗
        own γ (◯ {[τ := Excl {| op_info_kind := OpDeq obs' back_val;
                                op_info_reserved := None;
                                op_info_stored := false |}]}) -∗
        WP dequeue_aux dequeue (#sz, #ar, #back)%V #rng #i {{ v, ∃ obs_f rng_τ_f,
          own γ (◯ {[τ := Excl {| op_info_kind := OpDeq obs_f rng_τ_f;
                                  op_info_reserved := None;
                                  op_info_stored := true |}]}) ∗
          own γ_dq (◯ {[τ := to_agree v]}) }})%I
        with "[]" as "Hdeq_aux_spec".
      { iIntros (i obs') "%Hi_range %Hlen_obs Hfrag".
        iRevert (Hi_range Hlen_obs) "Hfrag".
        iLöb as "IH_inner" forall (i obs').
        iIntros (Hi_range Hlen_obs) "Hfrag".
        rewrite /dequeue_aux. wp_pure _. wp_pures.
        destruct (decide (i = 0%Z)) as [->|Hi_ne].
        - wp_pures.
          iApply ("IH_outer" $! obs' back_val with "Hfrag").
        - rewrite bool_decide_eq_false_2; [|intros [=]; done].
          wp_pures.
          wp_bind (! _)%E.
          iInv Nhwq as (items2 back_val2 ts2 s2 ls2 op_map2 stored_at2 cell_val_map2 dq_map2)
            "(>Hback & >Har & >Htrace & >Hauth & >Hauth_sv & Hfrag_sv & >Hauth_dq & Hfrag_dq & >%Hsteps2 & >%Hts_eq2 & >%Hsim2 & >%Hcvi2 & >%Hdqi2)".
          destruct Hsim2 as (Hlen2 & Hback_lo2 & Hslots_free2 & Hcp_fresh2
                             & Hdomsub2 & Henq_clause2 & Hdeq_clause2 & Hruniq2
                             & Hcells_wf2 & Hcells_fwd2 & Hstored2 & Hstored_inj2 & Hcells_stored2 & Hnot_stored2 & Hstored_link2 & Hres_fresh2 & Hobs_hist2 & Hlt_res2 & Hobs_struct2 & Hcomp_stored2 & Hlt_stored2 & Hrng_τ_bound2 & Hlt_res_obs2 & Hlt_res_obs_st2).
          assert (is_Some (items2 !! Z.to_nat (rng - i))) as [v_j Hv_j].
          { apply lookup_lt_is_Some_2. rewrite Hlen2. lia. }
          iDestruct (update_array _ _ _ _ _ Hv_j with "Har")
            as "[Hcell Hmerge]".
          assert (Hlocconv : (ar +ₗ Z.of_nat (Z.to_nat (rng - i)))%Z
                               = (ar +ₗ (rng - i))%Z).
          { f_equal. apply Z2Nat.id. lia. }
          rewrite Hlocconv.
          wp_load.
          iDestruct ("Hmerge" $! v_j with "[Hcell]") as "Har".
          { rewrite -Hlocconv. iFrame. }
          rewrite list_insert_id; last exact Hv_j.
          (* Case-split on [v_j] INSIDE the iInv so the NONEV branch
             can extend τ's [observed] list with the (offset, storer)
             pair before closing the invariant.  [Hcells_wf2] is pure
             so this split stays available post-close as well. *)
          assert (v_j = NONEV ∨
                  ∃ d, v_j = SOMEV d ∧ valid_value d ∧ val_is_unboxed (SOMEV d))
            as [->|(d & -> & Hd_valid & Hd_unboxed)].
          { destruct (Hcells_wf2 (Z.to_nat (rng - i)) ltac:(lia)) as [Hnone|(d & Hsome & ? & ?)].
            - left. rewrite Hv_j in Hnone. by inversion Hnone.
            - right. exists d. rewrite Hv_j in Hsome. inversion Hsome; subst.
              split_and!; done. }
          + (* NONEV: extend [observed] with (rng - i, storer-at-obs),
             where storer-at-obs is [Some k_obs] iff some [k_obs] had
             [stored_at[k_obs] = Some (Z.to_nat (rng - i))] at this
             moment, and [None] otherwise.  By [Hstored2] applied to
             the storer (when it exists), [k_obs ∉ O] since
             [items2[rng-i] = NONEV] at this moment. *)
            iDestruct (own_valid_2 with "Hauth Hfrag") as %Hboth2.
            apply auth_both_valid_discrete in Hboth2 as [Hincl2 Hvalid2].
            apply singleton_included_exclusive_l in Hincl2; [|apply _|done].
            rewrite lookup_fmap in Hincl2.
            apply leibniz_equiv in Hincl2.
            apply fmap_Some_1 in Hincl2
              as (info_τ2 & Hτ_in_opmap2 & Hinfo_τ2).
            destruct info_τ2; injection Hinfo_τ2 as <- <- <-.
            pose proof (gmap_image_dec stored_at2 (Z.to_nat (rng - i)))
              as Hstorer_case.
            destruct Hstorer_case as [[k_obs Hk_obs]|Hno_storer].
            * (* Storer [k_obs] exists: record [Some k_obs] in obs. *)
              set (new_obs :=
                obs' ++ [((rng - i)%Z, Some k_obs) : Z * option positive]).
              set (new_deq_info :=
                {| op_info_kind := OpDeq new_obs back_val;
                   op_info_reserved := None;
                   op_info_stored := false |}).
              iMod (own_update_2 _ _ _
                      (● to_opmap (<[τ := new_deq_info]> op_map2)
                       ⋅ ◯ {[τ := Excl new_deq_info]}) with "Hauth Hfrag")
                as "[Hauth Hfrag]".
              { apply auth_update.
                rewrite /to_opmap fmap_insert.
                apply: singleton_local_update.
                { rewrite lookup_fmap Hτ_in_opmap2 //. }
                by apply exclusive_local_update. }
              iModIntro.
              iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
              { iNext. iExists items2, back_val2, ts2, s2, ls2,
                  (<[τ := new_deq_info]> op_map2), stored_at2, cell_val_map2, dq_map2.
                iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
                iPureIntro. split_and!; [exact Hsteps2|exact Hts_eq2| |exact Hcvi2|exact Hdqi2].
                split_and!; [exact Hlen2|exact Hback_lo2|exact Hslots_free2
                            |exact Hcp_fresh2| | | |
                            |exact Hcells_wf2|exact Hcells_fwd2
                            |exact Hstored2|exact Hstored_inj2
                            |exact Hcells_stored2| | | | | | | | | | | ].
                - rewrite dom_insert_L.
                  assert (τ ∈ dom op_map2) as Hτ_dom.
                  { apply elem_of_dom. by eexists. }
                  clear -Hdomsub2 Hτ_dom. set_solver.
                - intros τ' d' r' b' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as Hkind.
                    discriminate Hkind.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    exact (Henq_clause2 _ _ _ _ Hlookup).
                - intros τ' obs'' rng_τ'' r' b' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as <- <- <- <-.
                    destruct (Hdeq_clause2 τ obs' back_val None false Hτ_in_opmap2)
                      as (Hcp_false & Hcp_true).
                    split; [exact Hcp_false|exact Hcp_true].
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    exact (Hdeq_clause2 _ _ _ _ _ Hlookup).
                - (* reserved_unique: τ is OpDeq in new op_map, so
                      OpEnq pattern fails on τ.  For τ' ≠ τ, use Hruniq2. *)
                  intros τ_a τ_b d_a d_b i' b_a b_b Ha Hb.
                  destruct (decide (τ_a = τ)) as [->|Hne_a].
                  { rewrite lookup_insert_eq in Ha.
                    injection Ha as Hkind. discriminate. }
                  destruct (decide (τ_b = τ)) as [->|Hne_b].
                  { rewrite lookup_insert_eq in Hb.
                    injection Hb as Hkind. discriminate. }
                  rewrite !lookup_insert_ne in Ha, Hb; [|done|done].
                  by eapply Hruniq2.
                - intros τ' d' r' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup. discriminate.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hnot_stored2.
                - intros τ' d' i' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup. discriminate.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hstored_link2.
                - intros τ' d' r' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup. discriminate.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hres_fresh2.
                - (* Hobs_hist: new entry (rng - i, Some k_obs).  By
                      [Hstored2] on [Hk_obs], k_obs has an ℓ entry; if
                      k_obs ∈ O then items2[rng-i] = SOMEV (contradicting
                      [v_j = NONEV]), so k_obs ∉ O. *)
                  intros τ' obs'' rng_τ'' r' b' Hlookup Hb' j k' Hk'_in.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as Hkind _ _ _.
                    inversion Hkind; subst obs''.
                    subst new_obs.
                    apply elem_of_app in Hk'_in as [Hin_old | Hin_new].
                    * by eapply (Hobs_hist2 _ _ _ _ _ Hτ_in_opmap2 eq_refl _ _ Hin_old).
                    * apply list_elem_of_singleton in Hin_new.
                      inversion Hin_new; subst j k'.
                      split; [exact Hk_obs|].
                      destruct (Hstored2 _ _ Hk_obs)
                        as (_ & d' & f' & _ & HinO' & _).
                      intros Hk_obs_O. specialize (HinO' Hk_obs_O).
                      rewrite Hv_j in HinO'. inversion HinO'.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply (Hobs_hist2 _ _ _ _ _ Hlookup Hb' _ _ Hk'_in).
                - (* Hlt_res: lt and stored_at unchanged; op_map's only
                    change is τ (OpDeq).  k_e = τ: OpDeq vs OpEnq, vacuous.
                    k_e ≠ τ: use Hlt_res2. *)
                  intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
                  destruct (decide (k_e' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup. discriminate.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hlt_res2.
                - (* Hobs_struct (NONEV-Some): new obs extends obs' by
                    one entry [(rng-i, Some k_obs)].  For i_idx < length
                    obs', use Hobs_struct2.  For i_idx = length obs', the
                    new entry's first component is [rng - i = Z.of_nat
                    (length obs')] by the length invariant [Hlen_obs]. *)
                  intros τ' obs'' rng_τ'' r' b' Hlookup Hb' i_idx Hi_lt.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as Hkind _ _ _.
                    inversion Hkind; subst obs''.
                    subst new_obs.
                    rewrite length_app /= in Hi_lt.
                    destruct (decide (i_idx < length obs')%nat) as [Hold | Hnew].
                    * rewrite lookup_app_l; last done.
                      by eapply (Hobs_struct2 _ _ _ _ _ Hτ_in_opmap2 eq_refl _ Hold).
                    * assert (i_idx = length obs') as -> by lia.
                      rewrite lookup_app_r; last done.
                      rewrite Nat.sub_diag /=.
                      eexists. f_equal.
                      rewrite Hlen_obs. rewrite Z2Nat.id; [done|lia].
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply (Hobs_struct2 _ _ _ _ _ Hlookup Hb' _ Hi_lt).
                - (* Hcomp_stored: ℓ, stored_at unchanged. *)
                  exact Hcomp_stored2.
                - (* Hlt_stored: lt, stored_at unchanged. *)
                  exact Hlt_stored2.
                - (* Hrng_τ_bound (NONEV-Some): τ's rng_τ = back_val
                    preserved; back_val unchanged; apply Hrng_τ_bound2. *)
                  intros τ' obs'' rng_τ'' r' b' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as _ <- _ _.
                    by eapply (Hrng_τ_bound2 _ _ _ _ _ Hτ_in_opmap2).
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hrng_τ_bound2.
                - (* Hlt_res_obs (NONEV-Some): new obs has (rng-i, Some
                    k_obs) at the tail; old entries unchanged. *)
                  intros τ' obs'' rng_τ'' r' Hlookup k k_e d' r_e b_e Hlt
                         Hlookup_e Hr_e_lt r_k Hstored_k Hr_k_lt.
                  destruct (decide (k_e = τ)) as [->|Hne_e].
                  { rewrite lookup_insert_eq in Hlookup_e. discriminate. }
                  rewrite lookup_insert_ne in Hlookup_e; last done.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as <- <- <-.
                    subst new_obs.
                    rewrite length_app /= in Hr_k_lt.
                    destruct (decide (r_k < length obs')%nat) as [Hold|Hnew].
                    * rewrite lookup_app_l; last done.
                      by eapply (Hlt_res_obs2 _ _ _ _ Hτ_in_opmap2 _ _ _ _ _
                                   Hlt Hlookup_e Hr_e_lt _ Hstored_k Hold).
                    * assert (r_k = length obs') as -> by lia.
                      exists k_obs.
                      rewrite lookup_app_r; last done.
                      rewrite Nat.sub_diag /=. f_equal.
                      f_equal. rewrite Hlen_obs Z2Nat.id; [done|lia].
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply (Hlt_res_obs2 _ _ _ _ Hlookup _ _ _ _ _
                                 Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
                - (* Hlt_res_obs_st (NONEV-Some): stored_at-form.  Same
                    entry-lookup logic. *)
                  intros τ' obs'' rng_τ'' r' Hlookup
                         k k_e r_k_e Hlt Hstored_k_e Hr_k_e_lt
                         r_k Hstored_k Hr_k_lt.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as <- <- <-.
                    subst new_obs.
                    rewrite length_app /= in Hr_k_lt.
                    destruct (decide (r_k < length obs')%nat) as [Hold|Hnew].
                    * rewrite lookup_app_l; last done.
                      by eapply (Hlt_res_obs_st2 _ _ _ _ Hτ_in_opmap2 _ _ _
                                   Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hold).
                    * assert (r_k = length obs') as -> by lia.
                      exists k_obs.
                      rewrite lookup_app_r; last done.
                      rewrite Nat.sub_diag /=. f_equal.
                      f_equal. rewrite Hlen_obs Z2Nat.id; [done|lia].
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply (Hlt_res_obs_st2 _ _ _ _ Hlookup _ _ _
                                 Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt). }
              do 6 wp_pure.
              wp_apply ("IH_inner").
              { iPureIntro. lia. }
              { iPureIntro.
                assert (length new_obs = length obs' + 1) as ->.
                { subst new_obs. by rewrite length_app /=. }
                lia. }
              iFrame.
            * (* No storer at obs: record [None] in obs. *)
              set (new_obs :=
                obs' ++ [((rng - i)%Z, @None positive) : Z * option positive]).
              set (new_deq_info :=
                {| op_info_kind := OpDeq new_obs back_val;
                   op_info_reserved := None;
                   op_info_stored := false |}).
              iMod (own_update_2 _ _ _
                      (● to_opmap (<[τ := new_deq_info]> op_map2)
                       ⋅ ◯ {[τ := Excl new_deq_info]}) with "Hauth Hfrag")
                as "[Hauth Hfrag]".
              { apply auth_update.
                rewrite /to_opmap fmap_insert.
                apply: singleton_local_update.
                { rewrite lookup_fmap Hτ_in_opmap2 //. }
                by apply exclusive_local_update. }
              iModIntro.
              iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
              { iNext. iExists items2, back_val2, ts2, s2, ls2,
                  (<[τ := new_deq_info]> op_map2), stored_at2, cell_val_map2, dq_map2.
                iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
                iPureIntro. split_and!; [exact Hsteps2|exact Hts_eq2| |exact Hcvi2|exact Hdqi2].
                split_and!; [exact Hlen2|exact Hback_lo2|exact Hslots_free2
                            |exact Hcp_fresh2| | | |
                            |exact Hcells_wf2|exact Hcells_fwd2
                            |exact Hstored2|exact Hstored_inj2
                            |exact Hcells_stored2| | | | | | | | | | | ].
                - rewrite dom_insert_L.
                  assert (τ ∈ dom op_map2) as Hτ_dom.
                  { apply elem_of_dom. by eexists. }
                  clear -Hdomsub2 Hτ_dom. set_solver.
                - intros τ' d' r' b' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as Hkind.
                    discriminate Hkind.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    exact (Henq_clause2 _ _ _ _ Hlookup).
                - intros τ' obs'' rng_τ'' r' b' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as <- <- <- <-.
                    destruct (Hdeq_clause2 τ obs' back_val None false Hτ_in_opmap2)
                      as (Hcp_false & Hcp_true).
                    split; [exact Hcp_false|exact Hcp_true].
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    exact (Hdeq_clause2 _ _ _ _ _ Hlookup).
                - (* reserved_unique: τ is OpDeq in new op_map, so
                      OpEnq pattern fails on τ.  For τ' ≠ τ, use Hruniq2. *)
                  intros τ_a τ_b d_a d_b i' b_a b_b Ha Hb.
                  destruct (decide (τ_a = τ)) as [->|Hne_a].
                  { rewrite lookup_insert_eq in Ha.
                    injection Ha as Hkind. discriminate. }
                  destruct (decide (τ_b = τ)) as [->|Hne_b].
                  { rewrite lookup_insert_eq in Hb.
                    injection Hb as Hkind. discriminate. }
                  rewrite !lookup_insert_ne in Ha, Hb; [|done|done].
                  by eapply Hruniq2.
                - intros τ' d' r' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup. discriminate.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hnot_stored2.
                - intros τ' d' i' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup. discriminate.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hstored_link2.
                - intros τ' d' r' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup. discriminate.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hres_fresh2.
                - (* Hobs_hist: new entry (rng - i, None), which imposes
                      no constraint (V1B-a only covers [Some] entries). *)
                  intros τ' obs'' rng_τ'' r' b' Hlookup Hb' j k' Hk'_in.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as Hkind _ _ _.
                    inversion Hkind; subst obs''.
                    subst new_obs.
                    apply elem_of_app in Hk'_in as [Hin_old | Hin_new].
                    * by eapply (Hobs_hist2 _ _ _ _ _ Hτ_in_opmap2 eq_refl _ _ Hin_old).
                    * apply list_elem_of_singleton in Hin_new.
                      inversion Hin_new.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply (Hobs_hist2 _ _ _ _ _ Hlookup Hb' _ _ Hk'_in).
                - (* Hlt_res: same as Some-branch. *)
                  intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
                  destruct (decide (k_e' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup. discriminate.
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hlt_res2.
                - (* Hobs_struct (NONEV-None): same as Some-branch. *)
                  intros τ' obs'' rng_τ'' r' b' Hlookup Hb' i_idx Hi_lt.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as Hkind _ _ _.
                    inversion Hkind; subst obs''.
                    subst new_obs.
                    rewrite length_app /= in Hi_lt.
                    destruct (decide (i_idx < length obs')%nat) as [Hold | Hnew].
                    * rewrite lookup_app_l; last done.
                      by eapply (Hobs_struct2 _ _ _ _ _ Hτ_in_opmap2 eq_refl _ Hold).
                    * assert (i_idx = length obs') as -> by lia.
                      rewrite lookup_app_r; last done.
                      rewrite Nat.sub_diag /=.
                      eexists. f_equal.
                      rewrite Hlen_obs. rewrite Z2Nat.id; [done|lia].
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply (Hobs_struct2 _ _ _ _ _ Hlookup Hb' _ Hi_lt).
                - (* Hcomp_stored (NONEV-None): ℓ, stored_at unchanged. *)
                  exact Hcomp_stored2.
                - (* Hlt_stored (NONEV-None): lt, stored_at unchanged. *)
                  exact Hlt_stored2.
                - (* Hrng_τ_bound (NONEV-None): τ's rng_τ preserved. *)
                  intros τ' obs'' rng_τ'' r' b' Hlookup.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as _ <- _ _.
                    by eapply (Hrng_τ_bound2 _ _ _ _ _ Hτ_in_opmap2).
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply Hrng_τ_bound2.
                - (* Hlt_res_obs (NONEV-None): the new obs entry is
                    [(rng-i, None)].  By Hno_storer at obs time, no k
                    has [stored_at k = Some (Z.to_nat (rng-i))], so
                    premise [stored_at k = Some r_k] with [r_k = length
                    obs'] contradicts.  Older entries unchanged. *)
                  intros τ' obs'' rng_τ'' r' Hlookup k k_e d' r_e b_e Hlt
                         Hlookup_e Hr_e_lt r_k Hstored_k Hr_k_lt.
                  destruct (decide (k_e = τ)) as [->|Hne_e].
                  { rewrite lookup_insert_eq in Hlookup_e. discriminate. }
                  rewrite lookup_insert_ne in Hlookup_e; last done.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as <- <- <-.
                    subst new_obs.
                    rewrite length_app /= in Hr_k_lt.
                    destruct (decide (r_k < length obs')%nat) as [Hold|Hnew].
                    * rewrite lookup_app_l; last done.
                      by eapply (Hlt_res_obs2 _ _ _ _ Hτ_in_opmap2 _ _ _ _ _
                                   Hlt Hlookup_e Hr_e_lt _ Hstored_k Hold).
                    * assert (r_k = length obs') as Hrk_eq by lia.
                      exfalso.
                      rewrite Hlen_obs in Hrk_eq.
                      rewrite Hrk_eq in Hstored_k.
                      by apply (Hno_storer k).
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply (Hlt_res_obs2 _ _ _ _ Hlookup _ _ _ _ _
                                 Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
                - (* Hlt_res_obs_st (NONEV-None): stored_at-form. *)
                  intros τ' obs'' rng_τ'' r' Hlookup
                         k k_e r_k_e Hlt Hstored_k_e Hr_k_e_lt
                         r_k Hstored_k Hr_k_lt.
                  destruct (decide (τ' = τ)) as [->|Hne].
                  + rewrite lookup_insert_eq in Hlookup.
                    subst new_deq_info. injection Hlookup as <- <- <-.
                    subst new_obs.
                    rewrite length_app /= in Hr_k_lt.
                    destruct (decide (r_k < length obs')%nat) as [Hold|Hnew].
                    * rewrite lookup_app_l; last done.
                      by eapply (Hlt_res_obs_st2 _ _ _ _ Hτ_in_opmap2 _ _ _
                                   Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hold).
                    * assert (r_k = length obs') as Hrk_eq by lia.
                      exfalso.
                      rewrite Hlen_obs in Hrk_eq.
                      rewrite Hrk_eq in Hstored_k.
                      by apply (Hno_storer k).
                  + rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply (Hlt_res_obs_st2 _ _ _ _ Hlookup _ _ _
                                 Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt). }
              do 6 wp_pure.
              wp_apply ("IH_inner").
              { iPureIntro. lia. }
              { iPureIntro.
                assert (length new_obs = length obs' + 1) as ->.
                { subst new_obs. by rewrite length_app /=. }
                lia. }
              iFrame.
          + (* SOMEV: extract persistent [γ_sv]-frag for the observed
              value [d] at offset [rng-i], close iInv unchanged, then
              carry the persistent frag through to the CAS-fail
              discharge. *)
            destruct (Hcells_stored2 (Z.to_nat (rng - i)) d Hv_j)
              as (τ_storer_d & Hst_d & _ & f_d & Hℓ_d).
            assert (cell_val_map2 !! Z.to_nat (rng - i) = Some d) as Hcvm_d.
            { by eapply (proj1 Hcvi2 _ _ _ _ Hst_d Hℓ_d). }
            iDestruct (own_mono _ _ (◯ {[Z.to_nat (rng - i) := to_agree d]})
                         with "Hfrag_sv") as "#Hsv_frag_d".
            { apply auth_frag_mono.
              rewrite /to_svmap.
              apply singleton_included_l.
              exists (to_agree d). split.
              - rewrite lookup_fmap Hcvm_d //.
              - reflexivity. }
            iModIntro.
            iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
            { iNext. iExists items2, back_val2, ts2, s2, ls2, op_map2, stored_at2, cell_val_map2, dq_map2.
              iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
              iPureIntro. split_and!; [exact Hsteps2|exact Hts_eq2| |exact Hcvi2|exact Hdqi2].
              split_and!; [exact Hlen2|exact Hback_lo2|exact Hslots_free2
                          |exact Hcp_fresh2|exact Hdomsub2|exact Henq_clause2
                          |exact Hdeq_clause2|exact Hruniq2|exact Hcells_wf2
                          |exact Hcells_fwd2|exact Hstored2|exact Hstored_inj2
                          |exact Hcells_stored2|exact Hnot_stored2
                          |exact Hstored_link2|exact Hres_fresh2|exact Hobs_hist2|exact Hlt_res2|exact Hobs_struct2|exact Hcomp_stored2|exact Hlt_stored2|exact Hrng_τ_bound2|exact Hlt_res_obs2|exact Hlt_res_obs_st2]. }
            wp_pures.
            wp_bind (CmpXchg _ _ _)%E.
            iInv Nhwq as (items3 back_val3 ts3 s3 ls3 op_map3 stored_at3 cell_val_map3 dq_map3)
              "(>Hback & >Har & >Htrace & >Hauth & >Hauth_sv & Hfrag_sv & >Hauth_dq & Hfrag_dq & >%Hsteps3 & >%Hts_eq3 & >%Hsim3 & >%Hcvi3 & >%Hdqi3)".
            destruct Hsim3 as (Hlen3 & Hback_lo3 & Hslots_free3 & Hcp_fresh3
                               & Hdomsub3 & Henq_clause3 & Hdeq_clause3 & Hruniq3
                               & Hcells_wf3 & Hcells_fwd3 & Hstored3 & Hstored_inj3 & Hcells_stored3 & Hnot_stored3 & Hstored_link3 & Hres_fresh3 & Hobs_hist3 & Hlt_res3 & Hobs_struct3 & Hcomp_stored3 & Hlt_stored3 & Hrng_τ_bound3 & Hlt_res_obs3 & Hlt_res_obs_st3).
            assert (is_Some (items3 !! Z.to_nat (rng - i))) as [v_j' Hv_j'].
            { apply lookup_lt_is_Some_2. rewrite Hlen3. lia. }
            iDestruct (update_array _ _ _ _ _ Hv_j' with "Har")
              as "[Hcell Hmerge]".
            assert (Hlocconv3 : (ar +ₗ Z.of_nat (Z.to_nat (rng - i)))%Z
                                  = (ar +ₗ (rng - i))%Z).
            { f_equal. apply Z2Nat.id. lia. }
            rewrite Hlocconv3.
            assert (Hcomp : vals_compare_safe v_j' (InjRV d)).
            { left.
              destruct (Hcells_wf3 (Z.to_nat (rng - i)) ltac:(lia))
                as [Hnone|(d'' & Hsome & _ & Hd''_ub)].
              - rewrite Hv_j' in Hnone. inversion Hnone; subst. done.
              - rewrite Hv_j' in Hsome. inversion Hsome; subst. exact Hd''_ub. }
            destruct (decide (v_j' = SOMEV d)) as [->|Hne_cas].
            * wp_cmpxchg_suc.
              iDestruct ("Hmerge" $! NONEV with "[Hcell]") as "Har".
              { rewrite -Hlocconv3. iFrame. }
              iDestruct (own_valid_2 with "Hauth Hfrag") as %Hτ_both.
              apply auth_both_valid_discrete in Hτ_both as [Hτ_incl Hτ_valid].
              apply singleton_included_exclusive_l in Hτ_incl;
                [|apply _|done].
              rewrite lookup_fmap in Hτ_incl.
              apply leibniz_equiv in Hτ_incl.
              apply fmap_Some_1 in Hτ_incl as (info_τ & Hτ_in_opmap3 & Hinfo_τ).
              destruct info_τ; injection Hinfo_τ as <- <- <-.
              set (new_deq_info := {| op_info_kind := OpDeq obs' back_val;
                                      op_info_reserved := None;
                                      op_info_stored := true |}).
              iMod (own_update_2 _ _ _
                      (● to_opmap (<[τ := new_deq_info]> op_map3)
                       ⋅ ◯ {[τ := Excl new_deq_info]}) with "Hauth Hfrag")
                as "[Hauth Hfrag]".
              { apply auth_update.
                rewrite /to_opmap fmap_insert.
                apply: singleton_local_update.
                { rewrite lookup_fmap Hτ_in_opmap3 //. }
                by apply exclusive_local_update. }
              destruct (Hcells_stored3 (Z.to_nat (rng - i)) d Hv_j')
                as (k_e & Hstored_k_e & Hk_e_O & f_e & Hℓ_k_e).
              destruct (Hdeq_clause3 τ obs' back_val None false Hτ_in_opmap3)
                as (Hcp_τ_false & _).
              pose proof (Hcp_τ_false eq_refl) as Hcp_τ_eq.
              (* Minimality of [k_e]: task #47's discharge.  Given any
                 [k' ∈ O] with [(k', k_e) ∈ lt_s3], we derive [False].
                 [absq_wf_lt_COMP] gives [ℓ[k'] = (d_k', COMP)];
                 [Hcomp_stored3] lifts that to [stored_at[k'] = Some
                 r_k']; [Hlt_stored3] bounds [r_k' < r_k_e = Z.to_nat
                 (rng - i)].  The length invariant [Hlen_obs] and
                 [Hobs_struct3] locate the obs entry at index [r_k']
                 as [(Z.of_nat r_k', k_opt)].  Case-splitting [k_opt]:
                 [Some k''] is the common case — [Hobs_hist3] forces
                 [k'' ∉ O], and [Hstored_inj3] shows [k'' = k'],
                 contradicting [k' ∈ O].  [None] is ruled out by
                 [Hlt_res_obs_st3]: stored_at k_e = Some (rng-i) with
                 rng-i < rng_τ gives [obs[r_k'] = Some (_, Some _)],
                 contradicting the None lookup. *)
              assert (k_e ∈ absq_min s3.(absq_O) s3.(absq_lt))
                as Hk_e_min.
              { apply elem_of_filter. split; [|exact Hk_e_O].
                intros k' Hk'_O Hlt'.
                assert (absq_wf valid_value s3) as Hwf3.
                { eapply absq_wf_steps; [exact Hsteps3|apply absq_wf_init]. }
                destruct (absq_wf_lt_COMP _ _ Hwf3 _ _ Hlt') as (d_k' & Hℓ_k').
                destruct (Hcomp_stored3 _ _ Hℓ_k') as (r_k' & Hstored_k').
                pose proof (Hlt_stored3 _ _ _ _ Hlt' Hstored_k' Hstored_k_e)
                  as Hr_k'_lt.
                (* r_k' < Z.to_nat (rng - i); by length invariant,
                   r_k' < length obs'. *)
                assert (r_k' < length obs')%nat as Hr_k'_lt_len.
                { rewrite Hlen_obs. exact Hr_k'_lt. }
                destruct (Hobs_struct3 _ _ _ _ _ Hτ_in_opmap3 eq_refl _ Hr_k'_lt_len)
                  as (k_opt & Hobs_lookup).
                (* Hlt_res_obs_st3 turns the [None] case into a
                   contradiction: stored_at k_e = Some (Z.to_nat (rng-i))
                   (Hstored_k_e), Z.of_nat(Z.to_nat(rng-i)) = rng-i <
                   rng_τ (via Hrng_τ_bound3 + the rng = back_val `min`
                   sz ≤ rng_τ chain); stored_at k' = Some r_k' with
                   r_k' < length obs'.  The conclusion [∃k'', obs' !!
                   r_k' = Some (Z.of_nat r_k', Some k'')] rules out the
                   [None] obs entry. *)
                assert ((Z.of_nat (Z.to_nat (rng - i)) < back_val)%Z)
                  as Hrke_lt_bv.
                { rewrite Z2Nat.id; lia. }
                destruct (Hlt_res_obs_st3 _ _ _ _ Hτ_in_opmap3 _ _ _
                            Hlt' Hstored_k_e Hrke_lt_bv _ Hstored_k' Hr_k'_lt_len)
                  as (k''_from_st & Hobs_st).
                destruct k_opt as [k''|].
                - (* Some k'': Hstored_inj gives k'' = k'. *)
                  assert ((Z.of_nat r_k', Some k'') ∈ obs') as Hin.
                  { by apply list_elem_of_lookup_2 in Hobs_lookup. }
                  destruct (Hobs_hist3 _ _ _ _ _ Hτ_in_opmap3 eq_refl _ _ Hin)
                    as (Hstored_k'' & Hk''_notO).
                  rewrite Nat2Z.id in Hstored_k''.
                  assert (k'' = k') as ->.
                  { by eapply (Hstored_inj3 _ _ _ Hstored_k'' Hstored_k'). }
                  contradiction.
                - (* None: Hlt_res_obs_st3 gives (r_k', Some k''_from_st);
                     combined with Hobs_struct3 giving (r_k', None) at
                     the same position, Some ≠ None. *)
                  rewrite Hobs_lookup in Hobs_st. discriminate. }
              destruct s3 as [O_s3 lt_s3 l_s3 rv_s3 cp_s3].
              simpl in Hk_e_O, Hℓ_k_e, Hcp_τ_eq, Hk_e_min, Hsteps3,
                Hts_eq3, Hcells_fwd3, Hcells_wf3, Hcp_fresh3,
                Hdomsub3, Henq_clause3, Hdeq_clause3, Hslots_free3,
                Hback_lo3, Hruniq3.
              (* γ_dq update: allocate [dq_map[τ := d]].  The slot was
                 empty: cp_s3 τ = R1 (Hcp_τ_eq) forces rv_s3 τ = None
                 via absq_wf_rv; dq_inv3 then rules out a prior entry. *)
              assert (absq_wf valid_value
                        (AbsQState O_s3 lt_s3 l_s3 rv_s3 cp_s3)) as Hwf3.
              { eapply absq_wf_steps;
                  [exact Hsteps3|apply absq_wf_init]. }
              assert (dq_map3 !! τ = None) as Hdq_τ_none.
              { destruct (dq_map3 !! τ) as [d_old|] eqn:Heq; last done.
                exfalso. pose proof (Hdqi3 _ _ Heq) as Hrv_τ.
                simpl in Hrv_τ.
                destruct (absq_wf_rv _ _ Hwf3 τ
                            (mk_is_Some _ _ Hrv_τ))
                  as [Hcp|Hcp]; rewrite Hcp_τ_eq in Hcp; discriminate. }
              iMod (own_update_2 _ _ _
                      (● to_dqmap (<[τ := d]> dq_map3)
                       ⋅ ◯ to_dqmap (<[τ := d]> dq_map3))
                      with "Hauth_dq Hfrag_dq") as "[Hauth_dq #Hfrag_dq]".
              { apply auth_update.
                rewrite /to_dqmap !fmap_insert.
                apply: alloc_local_update; [|done].
                rewrite lookup_fmap Hdq_τ_none //. }
              iDestruct (own_mono _ _ (◯ {[τ := to_agree d]})
                           with "Hfrag_dq") as "#Hdq_frag".
              { apply auth_frag_mono. rewrite /to_dqmap.
                apply singleton_included_l.
                exists (to_agree d). split.
                - rewrite lookup_fmap lookup_insert_eq //.
                - reflexivity. }
              iModIntro.
              iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq".
              { iNext.
                iExists (<[Z.to_nat (rng - i) := NONEV]> items3),
                  back_val3, ts3,
                  {| absq_O := O_s3 ∖ {[k_e]};
                     absq_lt := absq_remove lt_s3 k_e;
                     absq_l := l_s3;
                     absq_rv := <[τ := SOMEV d]> rv_s3;
                     absq_cp := <[τ := R2]> cp_s3 |},
                  (ls3 ++ [(τ, ALinDeq (SOMEV d))]),
                  (<[τ := new_deq_info]> op_map3), stored_at3, cell_val_map3,
                  (<[τ := d]> dq_map3).
                iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
                iPureIntro. split_and!.
                - eapply lts_steps_app; [exact Hsteps3|].
                  eapply lts_steps_cons; [|apply lts_steps_nil].
                  eapply absq_step_lin_deq1;
                    [exact Hcp_τ_eq|exact Hk_e_min|exact Hℓ_k_e].
                - rewrite Hts_eq3 /trace_of_absq_labels map_app /= filter_app.
                  rewrite filter_cons_False; [|by compute].
                  by rewrite filter_nil app_nil_r.
                - split_and!; simpl.
                  + rewrite length_insert. exact Hlen3.
                  + exact Hback_lo3.
                  + intros j Hj.
                    destruct (decide (j = Z.to_nat (rng - i))) as [->|Hne].
                    * rewrite list_lookup_insert_eq;
                        last (rewrite Hlen3; lia).
                      done.
                    * rewrite list_lookup_insert_ne; last done.
                      exact (Hslots_free3 _ Hj).
                  + rewrite dom_insert_L.
                    assert (τ ∈ dom cp_s3) as Hτ_dom.
                    { apply elem_of_dom. by exists R1. }
                    clear -Hdomsub3 Hcp_fresh3 Hτ_dom. set_solver.
                  + rewrite !dom_insert_L.
                    assert (τ ∈ dom op_map3) as Hτ_op.
                    { apply elem_of_dom. by exists {| op_info_kind := OpDeq obs' back_val;
                                                     op_info_reserved := None;
                                                     op_info_stored := false |}. }
                    assert (τ ∈ dom cp_s3) as Hτ_cp.
                    { apply elem_of_dom. by exists R1. }
                    clear -Hdomsub3 Hcp_fresh3 Hτ_cp. set_solver.
                  + intros τ' d' r' b' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hτ'_ne].
                    * rewrite lookup_insert_eq in Hlookup.
                      injection Hlookup as Hkind. discriminate.
                    * rewrite lookup_insert_ne in Hlookup; last done.
                      destruct (Henq_clause3 _ _ _ _ Hlookup)
                        as (Hcp_eq' & Hl_eq' & HbO' & Hreserv').
                      split_and!.
                      -- by rewrite lookup_insert_ne.
                      -- exact Hl_eq'.
                      -- intros Hb_false.
                         specialize (HbO' Hb_false); subst b'.
                         assert (τ' ≠ k_e) as Hτ'_ne_k_e.
                         { intros ->.
                           pose proof (Hnot_stored3 _ _ _ Hlookup) as Hnone.
                           rewrite Hnone in Hstored_k_e. discriminate. }
                         apply elem_of_difference. split; [exact HbO'|].
                         by apply not_elem_of_singleton.
                      -- intros i' Hr_eq.
                         destruct (Hreserv' _ Hr_eq) as (Hrng' & Himpl').
                         split; [exact Hrng'|].
                         intros Hi_ltsz.
                         destruct (Himpl' Hi_ltsz) as (Hfalse' & Htrue').
                         split.
                         ++ intros Hb_false.
                            destruct (decide
                              (Z.to_nat i' = Z.to_nat (rng - i))) as [Heq|Hne_i].
                            ** rewrite Heq list_lookup_insert_eq;
                                 last (rewrite Hlen3; lia). done.
                            ** rewrite list_lookup_insert_ne; last done.
                               by apply Hfalse'.
                         ++ intros Hb_true.
                            destruct (Htrue' Hb_true) as [Hin Hout].
                            split.
                            ** intros Hτ'_in_O'.
                               assert (τ' ∈ O_s3) as Hτ'_in_O.
                               { by apply elem_of_difference in Hτ'_in_O'
                                   as [? _]. }
                               pose proof (Hin Hτ'_in_O) as Hitems3_i'.
                               destruct (decide
                                 (Z.to_nat i' = Z.to_nat (rng - i)))
                                 as [Heq|Hne_i].
                               --- exfalso.
                                   subst b'. subst r'.
                                   pose proof (Hstored_link3 _ _ _ Hlookup)
                                     as Hst_τ'.
                                   rewrite Heq in Hst_τ'.
                                   assert (τ' = k_e) as Hτ'_eq.
                                   { by eapply (Hstored_inj3 _ _ _ Hst_τ'
                                                 Hstored_k_e). }
                                   rewrite Hτ'_eq in Hτ'_in_O'.
                                   apply elem_of_difference in Hτ'_in_O'
                                     as [_ Hne_sing].
                                   apply Hne_sing.
                                   apply elem_of_singleton. reflexivity.
                               --- rewrite list_lookup_insert_ne; last done.
                                   exact Hitems3_i'.
                            ** intros Hτ'_notin_O'.
                               destruct (decide (τ' ∈ O_s3)) as [HτO|HτnotO].
                               --- assert (τ' = k_e) as Hτ'_eq.
                                   { destruct (decide (τ' = k_e))
                                       as [->|Hne]; [done|].
                                     exfalso. apply Hτ'_notin_O'.
                                     apply elem_of_difference. split.
                                     - exact HτO.
                                     - by apply not_elem_of_singleton. }
                                   subst τ' b' r'.
                                   pose proof (Hstored_link3 _ _ _ Hlookup)
                                     as Hst_τ'.
                                   rewrite Hstored_k_e in Hst_τ'.
                                   assert (Z.to_nat i' = Z.to_nat (rng - i))
                                     as Hi_eq
                                     by (by injection Hst_τ').
                                   rewrite Hi_eq list_lookup_insert_eq;
                                     last (rewrite Hlen3; lia).
                                   done.
                               --- pose proof (Hout HτnotO) as Hitems3_i'.
                                   destruct (decide
                                     (Z.to_nat i' = Z.to_nat (rng - i)))
                                     as [Heq|Hne_i].
                                   +++ rewrite Heq list_lookup_insert_eq;
                                         last (rewrite Hlen3; lia). done.
                                   +++ rewrite list_lookup_insert_ne;
                                         last done. exact Hitems3_i'.
                  + intros τ' obs'' rng_τ'' r' b' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    * rewrite lookup_insert_eq in Hlookup.
                      injection Hlookup as <- <- <- <-.
                      split; [done|].
                      intros _. split.
                      { by rewrite lookup_insert_eq. }
                      exists (SOMEV d). by rewrite lookup_insert_eq.

                    * rewrite lookup_insert_ne in Hlookup; last done.
                      destruct (Hdeq_clause3 _ _ _ _ _ Hlookup)
                        as (Hcp_false & Hcp_true).
                      split.
                      -- intros Hbf. rewrite lookup_insert_ne //.
                         by apply Hcp_false.
                      -- intros Hbt. destruct (Hcp_true Hbt) as (Hcp & d_t & Hrv).
                         rewrite lookup_insert_ne //. split; [exact Hcp|].
                         exists d_t. rewrite lookup_insert_ne //.
                  + intros τ_a τ_b d_a d_b i' b_a b_b Ha Hb.
                    destruct (decide (τ_a = τ)) as [->|Hne_a].
                    { rewrite lookup_insert_eq in Ha.
                      injection Ha as Hkind. discriminate. }
                    destruct (decide (τ_b = τ)) as [->|Hne_b].
                    { rewrite lookup_insert_eq in Hb.
                      injection Hb as Hkind. discriminate. }
                    rewrite !lookup_insert_ne in Ha, Hb; [|done|done].
                    by eapply Hruniq3.
                  + intros j Hj.
                    destruct (decide (j = Z.to_nat (rng - i))) as [->|Hne].
                    * rewrite list_lookup_insert_eq;
                        last (rewrite Hlen3; lia).
                      by left.
                    * rewrite list_lookup_insert_ne; last done.
                      exact (Hcells_wf3 _ Hj).
                  + intros j d'' Hitems_j.
                    destruct (decide (j = Z.to_nat (rng - i))) as [->|Hne].
                    * rewrite list_lookup_insert_eq in Hitems_j;
                        last (rewrite Hlen3; lia).
                      inversion Hitems_j.
                    * rewrite list_lookup_insert_ne in Hitems_j; last done.
                      pose proof (Hcells_stored3 _ _ Hitems_j) as Hex.
                      destruct Hex as (witness & Hw_stored & Hw_O & f'' & Hw_ℓ).
                      assert (witness ≠ k_e) as Hw_ne.
                      { intros Heq. apply Hne.
                        rewrite Heq in Hw_stored.
                        rewrite Hstored_k_e in Hw_stored.
                        by injection Hw_stored. }
                      exists witness. split.
                      { apply elem_of_difference. split; [exact Hw_O|].
                        by apply not_elem_of_singleton. }
                      exists f''. exact Hw_ℓ.
                  + intros τ' i' Hlookup.
                    destruct (Hstored3 _ _ Hlookup)
                      as (Hbound' & d' & f' & Hℓ' & HinO' & HnotO').
                    split; [exact Hbound'|].
                    exists d', f'. split_and!; [exact Hℓ'| |].
                    * intros Hτ'_in_O'.
                      assert (τ' ∈ O_s3) as Hτ'_O
                        by (by apply elem_of_difference in Hτ'_in_O' as [? _]).
                      specialize (HinO' Hτ'_O).
                      destruct (decide (i' = Z.to_nat (rng - i))) as [->|Hne_i].
                      -- exfalso.
                        pose proof (Hstored_inj3 _ _ _ Hlookup Hstored_k_e).
                        apply elem_of_difference in Hτ'_in_O' as [_ Hne_sing].
                        apply Hne_sing. rewrite (Hstored_inj3 _ _ _ Hlookup Hstored_k_e).
                        apply elem_of_singleton. reflexivity.
                      -- rewrite list_lookup_insert_ne; last done. exact HinO'.
                    * intros Hτ'_notO'.
                      destruct (decide (τ' ∈ O_s3)) as [Hτ'O|Hτ'notO].
                      -- assert (τ' = k_e) as ->.
                        { destruct (decide (τ' = k_e)) as [->|Hne']; [done|].
                          exfalso. apply Hτ'_notO'.
                          apply elem_of_difference. split; [exact Hτ'O|].
                          by apply not_elem_of_singleton. }
                        assert (i' = Z.to_nat (rng - i)) as ->.
                        { rewrite Hlookup in Hstored_k_e.
                          by injection Hstored_k_e. }
                        rewrite list_lookup_insert_eq;
                          last (rewrite Hlen3; lia). done.
                      -- specialize (HnotO' Hτ'notO).
                         destruct (decide (i' = Z.to_nat (rng - i))) as [->|Hne_i].
                         ++ rewrite list_lookup_insert_eq;
                              last (rewrite Hlen3; lia). done.
                         ++ rewrite list_lookup_insert_ne; last done. exact HnotO'.
                  + exact Hstored_inj3.
                  + intros j d'' Hitems_j.
                    destruct (decide (j = Z.to_nat (rng - i))) as [->|Hne].
                    * rewrite list_lookup_insert_eq in Hitems_j;
                        last (rewrite Hlen3; lia). inversion Hitems_j.
                    * rewrite list_lookup_insert_ne in Hitems_j; last done.
                      pose proof (Hcells_stored3 _ _ Hitems_j) as Hex2.
                      destruct Hex2 as (σ_w & Hσw_stored & Hσw_O & f_σ & Hℓ_σw).
                      assert (σ_w ≠ k_e) as Hσw_ne.
                      { intros Heq. apply Hne.
                        rewrite Heq in Hσw_stored.
                        rewrite Hstored_k_e in Hσw_stored.
                        by injection Hσw_stored. }
                      exists σ_w. split_and!; [exact Hσw_stored| |by exists f_σ].
                      apply elem_of_difference. split; [exact Hσw_O|].
                      by apply not_elem_of_singleton.
                  + intros τ' d' r' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    * rewrite lookup_insert_eq in Hlookup. discriminate.
                    * rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hnot_stored3.
                  + intros τ' d' i' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    * rewrite lookup_insert_eq in Hlookup. discriminate.
                    * rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hstored_link3.
                  + intros τ' d' r' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    * rewrite lookup_insert_eq in Hlookup. discriminate.
                    * rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hres_fresh3.
                  + intros τ' obs'' rng_τ'' r' b' Hlookup Hb' j k' Hk'_in.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    * rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as _ _ _ Hstore.
                      rewrite Hb' in Hstore. discriminate.
                    * rewrite lookup_insert_ne in Hlookup; last done.
                      destruct (Hobs_hist3 _ _ _ _ _ Hlookup Hb' _ _ Hk'_in)
                        as (Hstored_k' & Hk'_notO).
                      split; [exact Hstored_k'|].
                      simpl. intros Hk_in.
                      apply elem_of_difference in Hk_in as [HkO _].
                      contradiction.
                  + (* Hlt_res (LIN-DEQ1): new absq_lt = absq_remove lt_s3
                      k_e, a subset of lt_s3.  op_map changes τ to OpDeq
                      (with stored=true), so OpEnq pattern fails on τ.
                      stored_at unchanged. *)
                    intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
                    apply elem_of_filter in Hlt as [_ Hlt].
                    destruct (decide (k_e' = τ)) as [->|Hne_e].
                    * rewrite lookup_insert_eq in Hlookup. discriminate.
                    * rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hlt_res3.
                  + (* Hobs_struct (LIN-DEQ1): τ's new entry has stored=true,
                      vacuous under b=false.  For τ' ≠ τ, unchanged. *)
                    intros τ' obs'' rng_τ'' r' b' Hlookup Hb' i_idx Hi_lt.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    * rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as _ _ _ Hstore.
                      rewrite Hb' in Hstore. discriminate.
                    * rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply (Hobs_struct3 _ _ _ _ _ Hlookup Hb' _ Hi_lt).
                  + (* Hcomp_stored (LIN-DEQ1): ℓ, stored_at unchanged. *)
                    exact Hcomp_stored3.
                  + (* Hlt_stored (LIN-DEQ1): stored_at unchanged; lt
                      shrinks via [absq_remove], surviving pairs are in
                      old lt, apply Hlt_stored3. *)
                    intros k k_e' r_k r_k_e' Hlt Hstored_k_arg Hstored_ke_arg.
                    apply elem_of_filter in Hlt as [_ Hlt].
                    by eapply Hlt_stored3.
                  + (* Hrng_τ_bound (LIN-DEQ1): back_val unchanged; τ's
                      rng_τ preserved (only stored flag flips). *)
                    intros τ' obs'' rng_τ'' r' b' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    * rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as _ <- _ _.
                      by eapply (Hrng_τ_bound3 _ _ _ _ _ Hτ_in_opmap3).
                    * rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hrng_τ_bound3.
                  + (* Hlt_res_obs (LIN-DEQ1): τ's entry is now
                      stored=true, so the pre-LIN premise fails.  lt
                      shrunk via absq_remove, surviving edges still in
                      old lt.  Use Hlt_res_obs3 for τ' ≠ τ. *)
                    intros τ' obs'' rng_τ'' r' Hlookup
                           k k_e' d' r_e' b_e' Hlt
                           Hlookup_e Hr_e_lt r_k Hstored_k Hr_k_lt.
                    apply elem_of_filter in Hlt as [_ Hlt].
                    destruct (decide (τ' = τ)) as [->|Hne].
                    { rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as _ _ _ Hstore.
                      discriminate. }
                    rewrite lookup_insert_ne in Hlookup; last done.
                    destruct (decide (k_e' = τ)) as [->|Hne_e].
                    { rewrite lookup_insert_eq in Hlookup_e.
                      subst new_deq_info. injection Hlookup_e as Hkind _ _.
                      discriminate. }
                    rewrite lookup_insert_ne in Hlookup_e; last done.
                    by eapply (Hlt_res_obs3 _ _ _ _ Hlookup _ _ _ _ _
                                 Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
                  + (* Hlt_res_obs_st (LIN-DEQ1): stored_at-form. *)
                    intros τ' obs'' rng_τ'' r' Hlookup
                           k k_e' r_k_e' Hlt
                           Hstored_k_e' Hr_k_e_lt r_k Hstored_k' Hr_k_lt.
                    apply elem_of_filter in Hlt as [_ Hlt].
                    destruct (decide (τ' = τ)) as [->|Hne].
                    { rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as _ _ _ Hstore.
                      discriminate. }
                    rewrite lookup_insert_ne in Hlookup; last done.
                    by eapply (Hlt_res_obs_st3 _ _ _ _ Hlookup _ _ _
                                 Hlt Hstored_k_e' Hr_k_e_lt _ Hstored_k' Hr_k_lt).
                - (* cell_val_inv (LIN-DEQ1): stored_at, ℓ values
                    unchanged; cell_val_map unchanged.  IH directly. *)
                  simpl. exact Hcvi3.
                - (* dq_inv (LIN-DEQ1): dq_map gains (τ, d); rv gains
                    (τ, d); both match.  For τ' ≠ τ, both passthrough
                    to Hdqi3. *)
                  simpl.
                  intros τ' d' Hlookup_dq.
                  destruct (decide (τ' = τ)) as [->|Hne_τ].
                  + rewrite lookup_insert_eq in Hlookup_dq.
                    injection Hlookup_dq as <-.
                    by rewrite lookup_insert_eq.
                  + rewrite lookup_insert_ne in Hlookup_dq; last done.
                    rewrite lookup_insert_ne; last done.
                    exact (Hdqi3 _ _ Hlookup_dq). }
              wp_pures.
              iExists obs', back_val. by iFrame "Hfrag Hdq_frag".
            * wp_cmpxchg_fail.
              iDestruct ("Hmerge" $! v_j' with "[Hcell]") as "Har".
              { rewrite -Hlocconv3. iFrame. }
              rewrite list_insert_id; last exact Hv_j'.
              (* CAS-fail means [v_j' ≠ SOMEV d].  [Hcells_wf3] makes
                 [v_j'] either [NONEV] or [SOMEV e].  The SOMEV case is
                 actually impossible at this point (by storer-uniqueness
                 + [ℓ] value-monotonicity — since the load saw [SOMEV d],
                 the position's fixed storer carries [d], so any current
                 [SOMEV e] would force [e = d], contradicting [Hne_cas])
                 but deriving that requires a cross-iInv monotonicity
                 argument; we defer it by case-splitting and recording
                 the observation only on the NONEV sub-case. *)
              destruct (Hcells_wf3 (Z.to_nat (rng - i)) ltac:(lia))
                as [Hnone3 | (e & Hsome3 & _ & _)];
                last first.
              { (* SOMEV e: IMPOSSIBLE — derive False via the γ_sv
                   agreeR mechanism.  [Hsv_frag_d] from the outer iInv
                   pins offset [rng-i] to value [d]; extract a frag
                   [Hsv_frag_e] pinning the same offset to [e]; own_valid_2
                   forces [d = e], contradicting [Hne_cas]. *)
                destruct (Hcells_stored3 (Z.to_nat (rng - i)) e Hsome3)
                  as (τ_storer_e & Hst_e & _ & f_e & Hℓ_e).
                assert (cell_val_map3 !! Z.to_nat (rng - i) = Some e) as Hcvm_e.
                { by eapply (proj1 Hcvi3 _ _ _ _ Hst_e Hℓ_e). }
                iDestruct (own_mono _ _ (◯ {[Z.to_nat (rng - i) := to_agree e]})
                             with "Hfrag_sv") as "#Hsv_frag_e".
                { apply auth_frag_mono.
                  rewrite /to_svmap.
                  apply singleton_included_l.
                  exists (to_agree e). split.
                  - rewrite lookup_fmap Hcvm_e //.
                  - reflexivity. }
                iDestruct (own_valid_2 with "Hsv_frag_d Hsv_frag_e")
                  as %Hvalid_de.
                rewrite -auth_frag_op auth_frag_valid singleton_op
                        singleton_valid in Hvalid_de.
                apply to_agree_op_inv_L in Hvalid_de.
                assert (v_j' = SOMEV e) as ->.
                { rewrite Hv_j' in Hsome3. by injection Hsome3. }
                exfalso. apply Hne_cas. by rewrite Hvalid_de. }
              (* NONEV case: proceed with ghost update. *)
              assert (v_j' = NONEV) as ->.
              { rewrite Hv_j' in Hnone3. by injection Hnone3. }
              iDestruct (own_valid_2 with "Hauth Hfrag") as %Hboth3'.
              apply auth_both_valid_discrete in Hboth3' as [Hincl3' Hvalid3'].
              apply singleton_included_exclusive_l in Hincl3'; [|apply _|done].
              rewrite lookup_fmap in Hincl3'.
              apply leibniz_equiv in Hincl3'.
              apply fmap_Some_1 in Hincl3'
                as (info_τ3 & Hτ_in_opmap3 & Hinfo_τ3).
              destruct info_τ3; injection Hinfo_τ3 as <- <- <-.
              pose proof (gmap_image_dec stored_at3 (Z.to_nat (rng - i)))
                as Hstorer_case3.
              destruct Hstorer_case3 as [[k_obs Hk_obs]|Hno_storer].
              -- (* Storer [k_obs] exists. *)
                set (new_obs :=
                  obs' ++ [((rng - i)%Z, Some k_obs) : Z * option positive]).
                set (new_deq_info :=
                  {| op_info_kind := OpDeq new_obs back_val;
                     op_info_reserved := None;
                     op_info_stored := false |}).
                iMod (own_update_2 _ _ _
                        (● to_opmap (<[τ := new_deq_info]> op_map3)
                         ⋅ ◯ {[τ := Excl new_deq_info]}) with "Hauth Hfrag")
                  as "[Hauth Hfrag]".
                { apply auth_update.
                  rewrite /to_opmap fmap_insert.
                  apply: singleton_local_update.
                  { rewrite lookup_fmap Hτ_in_opmap3 //. }
                  by apply exclusive_local_update. }
                iModIntro.
                iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
                { iNext. iExists items3, back_val3, ts3, s3, ls3,
                    (<[τ := new_deq_info]> op_map3), stored_at3, cell_val_map3, dq_map3.
                  iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
                  iPureIntro. split_and!; [exact Hsteps3|exact Hts_eq3| |exact Hcvi3|exact Hdqi3].
                  split_and!; [exact Hlen3|exact Hback_lo3|exact Hslots_free3
                              |exact Hcp_fresh3| | | |
                              |exact Hcells_wf3|exact Hcells_fwd3
                              |exact Hstored3|exact Hstored_inj3
                              |exact Hcells_stored3| | | | | | | | | | | ].
                  - rewrite dom_insert_L.
                    assert (τ ∈ dom op_map3) as Hτ_dom.
                    { apply elem_of_dom. by eexists. }
                    clear -Hdomsub3 Hτ_dom. set_solver.
                  - intros τ' d' r' b' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as Hkind.
                      discriminate Hkind.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      exact (Henq_clause3 _ _ _ _ Hlookup).
                  - intros τ' obs'' rng_τ'' r' b' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as <- <- <- <-.
                      destruct (Hdeq_clause3 τ obs' back_val None false Hτ_in_opmap3)
                        as (Hcp_false & Hcp_true).
                      split; [exact Hcp_false|exact Hcp_true].
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      exact (Hdeq_clause3 _ _ _ _ _ Hlookup).
                  - intros τ_a τ_b d_a d_b i' b_a b_b Ha Hb.
                    destruct (decide (τ_a = τ)) as [->|Hne_a].
                    { rewrite lookup_insert_eq in Ha.
                      injection Ha as Hkind. discriminate. }
                    destruct (decide (τ_b = τ)) as [->|Hne_b].
                    { rewrite lookup_insert_eq in Hb.
                      injection Hb as Hkind. discriminate. }
                    rewrite !lookup_insert_ne in Ha, Hb; [|done|done].
                    by eapply Hruniq3.
                  - intros τ' d' r' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup. discriminate.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hnot_stored3.
                  - intros τ' d' i' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup. discriminate.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hstored_link3.
                  - intros τ' d' r' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup. discriminate.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hres_fresh3.
                  - intros τ' obs'' rng_τ'' r' b' Hlookup Hb' j k' Hk'_in.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as Hkind _ _ _.
                      inversion Hkind; subst obs''.
                      subst new_obs.
                      apply elem_of_app in Hk'_in as [Hin_old | Hin_new].
                      * by eapply (Hobs_hist3 _ _ _ _ _ Hτ_in_opmap3 eq_refl _ _ Hin_old).
                      * apply list_elem_of_singleton in Hin_new.
                        inversion Hin_new; subst j k'.
                        split; [exact Hk_obs|].
                        destruct (Hstored3 _ _ Hk_obs)
                          as (_ & d'' & f' & _ & HinO' & _).
                        intros Hk_obs_O. specialize (HinO' Hk_obs_O).
                        rewrite Hv_j' in HinO'. inversion HinO'.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply (Hobs_hist3 _ _ _ _ _ Hlookup Hb' _ _ Hk'_in).
                  - (* Hlt_res: lt and stored_at unchanged; τ's OpDeq
                      entry rules out the OpEnq pattern for k_e = τ. *)
                    intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
                    destruct (decide (k_e' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup. discriminate.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hlt_res3.
                  - (* Hobs_struct (CAS-fail NONEV-Some): extension. *)
                    intros τ' obs'' rng_τ'' r' b' Hlookup Hb' i_idx Hi_lt.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as Hkind _ _ _.
                      inversion Hkind; subst obs''.
                      subst new_obs.
                      rewrite length_app /= in Hi_lt.
                      destruct (decide (i_idx < length obs')%nat) as [Hold | Hnew].
                      * rewrite lookup_app_l; last done.
                        by eapply (Hobs_struct3 _ _ _ _ _ Hτ_in_opmap3 eq_refl _ Hold).
                      * assert (i_idx = length obs') as -> by lia.
                        rewrite lookup_app_r; last done.
                        rewrite Nat.sub_diag /=.
                        eexists. f_equal.
                        rewrite Hlen_obs. rewrite Z2Nat.id; [done|lia].
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply (Hobs_struct3 _ _ _ _ _ Hlookup Hb' _ Hi_lt).
                  - (* Hcomp_stored: ℓ, stored_at unchanged. *)
                    exact Hcomp_stored3.
                  - (* Hlt_stored: lt, stored_at unchanged. *)
                    exact Hlt_stored3.
                  - (* Hrng_τ_bound (CAS-fail NONEV-Some): rng_τ preserved. *)
                    intros τ' obs'' rng_τ'' r' b' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as _ <- _ _.
                      by eapply (Hrng_τ_bound3 _ _ _ _ _ Hτ_in_opmap3).
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hrng_τ_bound3.
                  - (* Hlt_res_obs (CAS-fail NONEV-Some): new entry is
                      [(rng-i, Some k_obs)]; older entries unchanged. *)
                    intros τ' obs'' rng_τ'' r' Hlookup
                           k k_e' d'' r_e' b_e' Hlt
                           Hlookup_e Hr_e_lt r_k Hstored_k Hr_k_lt.
                    destruct (decide (k_e' = τ)) as [->|Hne_e].
                    { rewrite lookup_insert_eq in Hlookup_e. discriminate. }
                    rewrite lookup_insert_ne in Hlookup_e; last done.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as <- <- <-.
                      subst new_obs.
                      rewrite length_app /= in Hr_k_lt.
                      destruct (decide (r_k < length obs')%nat) as [Hold|Hnew].
                      * rewrite lookup_app_l; last done.
                        by eapply (Hlt_res_obs3 _ _ _ _ Hτ_in_opmap3 _ _ _ _ _
                                     Hlt Hlookup_e Hr_e_lt _ Hstored_k Hold).
                      * assert (r_k = length obs') as -> by lia.
                        exists k_obs.
                        rewrite lookup_app_r; last done.
                        rewrite Nat.sub_diag /=. f_equal.
                        f_equal. rewrite Hlen_obs Z2Nat.id; [done|lia].
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply (Hlt_res_obs3 _ _ _ _ Hlookup _ _ _ _ _
                                   Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
                  - (* Hlt_res_obs_st (CAS-fail NONEV-Some): stored_at-form. *)
                    intros τ' obs'' rng_τ'' r' Hlookup
                           k k_e' r_k_e Hlt Hstored_k_e Hr_k_e_lt
                           r_k Hstored_k Hr_k_lt.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as <- <- <-.
                      subst new_obs.
                      rewrite length_app /= in Hr_k_lt.
                      destruct (decide (r_k < length obs')%nat) as [Hold|Hnew].
                      * rewrite lookup_app_l; last done.
                        by eapply (Hlt_res_obs_st3 _ _ _ _ Hτ_in_opmap3 _ _ _
                                     Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hold).
                      * assert (r_k = length obs') as -> by lia.
                        exists k_obs.
                        rewrite lookup_app_r; last done.
                        rewrite Nat.sub_diag /=. f_equal.
                        f_equal. rewrite Hlen_obs Z2Nat.id; [done|lia].
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply (Hlt_res_obs_st3 _ _ _ _ Hlookup _ _ _
                                   Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt). }
                do 5 wp_pure.
                wp_apply ("IH_inner").
                { iPureIntro; lia. }
                { iPureIntro.
                assert (length new_obs = length obs' + 1) as ->.
                { subst new_obs. by rewrite length_app /=. }
                lia. }
                iFrame.
              -- (* No storer at obs: record [None]. *)
                set (new_obs :=
                  obs' ++ [((rng - i)%Z, @None positive) : Z * option positive]).
                set (new_deq_info :=
                  {| op_info_kind := OpDeq new_obs back_val;
                     op_info_reserved := None;
                     op_info_stored := false |}).
                iMod (own_update_2 _ _ _
                        (● to_opmap (<[τ := new_deq_info]> op_map3)
                         ⋅ ◯ {[τ := Excl new_deq_info]}) with "Hauth Hfrag")
                  as "[Hauth Hfrag]".
                { apply auth_update.
                  rewrite /to_opmap fmap_insert.
                  apply: singleton_local_update.
                  { rewrite lookup_fmap Hτ_in_opmap3 //. }
                  by apply exclusive_local_update. }
                iModIntro.
                iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
                { iNext. iExists items3, back_val3, ts3, s3, ls3,
                    (<[τ := new_deq_info]> op_map3), stored_at3, cell_val_map3, dq_map3.
                  iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
                  iPureIntro. split_and!; [exact Hsteps3|exact Hts_eq3| |exact Hcvi3|exact Hdqi3].
                  split_and!; [exact Hlen3|exact Hback_lo3|exact Hslots_free3
                              |exact Hcp_fresh3| | | |
                              |exact Hcells_wf3|exact Hcells_fwd3
                              |exact Hstored3|exact Hstored_inj3
                              |exact Hcells_stored3| | | | | | | | | | | ].
                  - rewrite dom_insert_L.
                    assert (τ ∈ dom op_map3) as Hτ_dom.
                    { apply elem_of_dom. by eexists. }
                    clear -Hdomsub3 Hτ_dom. set_solver.
                  - intros τ' d' r' b' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as Hkind.
                      discriminate Hkind.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      exact (Henq_clause3 _ _ _ _ Hlookup).
                  - intros τ' obs'' rng_τ'' r' b' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as <- <- <- <-.
                      destruct (Hdeq_clause3 τ obs' back_val None false Hτ_in_opmap3)
                        as (Hcp_false & Hcp_true).
                      split; [exact Hcp_false|exact Hcp_true].
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      exact (Hdeq_clause3 _ _ _ _ _ Hlookup).
                  - intros τ_a τ_b d_a d_b i' b_a b_b Ha Hb.
                    destruct (decide (τ_a = τ)) as [->|Hne_a].
                    { rewrite lookup_insert_eq in Ha.
                      injection Ha as Hkind. discriminate. }
                    destruct (decide (τ_b = τ)) as [->|Hne_b].
                    { rewrite lookup_insert_eq in Hb.
                      injection Hb as Hkind. discriminate. }
                    rewrite !lookup_insert_ne in Ha, Hb; [|done|done].
                    by eapply Hruniq3.
                  - intros τ' d' r' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup. discriminate.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hnot_stored3.
                  - intros τ' d' i' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup. discriminate.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hstored_link3.
                  - intros τ' d' r' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup. discriminate.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hres_fresh3.
                  - intros τ' obs'' rng_τ'' r' b' Hlookup Hb' j k' Hk'_in.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as Hkind _ _ _.
                      inversion Hkind; subst obs''.
                      subst new_obs.
                      apply elem_of_app in Hk'_in as [Hin_old | Hin_new].
                      * by eapply (Hobs_hist3 _ _ _ _ _ Hτ_in_opmap3 eq_refl _ _ Hin_old).
                      * apply list_elem_of_singleton in Hin_new.
                        inversion Hin_new.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply (Hobs_hist3 _ _ _ _ _ Hlookup Hb' _ _ Hk'_in).
                  - (* Hlt_res: same as Some-branch. *)
                    intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
                    destruct (decide (k_e' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup. discriminate.
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hlt_res3.
                  - (* Hobs_struct (CAS-fail NONEV-None): same as Some. *)
                    intros τ' obs'' rng_τ'' r' b' Hlookup Hb' i_idx Hi_lt.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as Hkind _ _ _.
                      inversion Hkind; subst obs''.
                      subst new_obs.
                      rewrite length_app /= in Hi_lt.
                      destruct (decide (i_idx < length obs')%nat) as [Hold | Hnew].
                      * rewrite lookup_app_l; last done.
                        by eapply (Hobs_struct3 _ _ _ _ _ Hτ_in_opmap3 eq_refl _ Hold).
                      * assert (i_idx = length obs') as -> by lia.
                        rewrite lookup_app_r; last done.
                        rewrite Nat.sub_diag /=.
                        eexists. f_equal.
                        rewrite Hlen_obs. rewrite Z2Nat.id; [done|lia].
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply (Hobs_struct3 _ _ _ _ _ Hlookup Hb' _ Hi_lt).
                  - (* Hcomp_stored: ℓ, stored_at unchanged. *)
                    exact Hcomp_stored3.
                  - (* Hlt_stored: lt, stored_at unchanged. *)
                    exact Hlt_stored3.
                  - (* Hrng_τ_bound (CAS-fail NONEV-None): rng_τ preserved. *)
                    intros τ' obs'' rng_τ'' r' b' Hlookup.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as _ <- _ _.
                      by eapply (Hrng_τ_bound3 _ _ _ _ _ Hτ_in_opmap3).
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply Hrng_τ_bound3.
                  - (* Hlt_res_obs (CAS-fail NONEV-None): new entry is
                      [(rng-i, None)]; Hno_storer rules out the new tail. *)
                    intros τ' obs'' rng_τ'' r' Hlookup
                           k k_e' d'' r_e' b_e' Hlt
                           Hlookup_e Hr_e_lt r_k Hstored_k Hr_k_lt.
                    destruct (decide (k_e' = τ)) as [->|Hne_e].
                    { rewrite lookup_insert_eq in Hlookup_e. discriminate. }
                    rewrite lookup_insert_ne in Hlookup_e; last done.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as <- <- <-.
                      subst new_obs.
                      rewrite length_app /= in Hr_k_lt.
                      destruct (decide (r_k < length obs')%nat) as [Hold|Hnew].
                      * rewrite lookup_app_l; last done.
                        by eapply (Hlt_res_obs3 _ _ _ _ Hτ_in_opmap3 _ _ _ _ _
                                     Hlt Hlookup_e Hr_e_lt _ Hstored_k Hold).
                      * assert (r_k = length obs') as Hrk_eq by lia.
                        exfalso.
                        rewrite Hlen_obs in Hrk_eq.
                        rewrite Hrk_eq in Hstored_k.
                        by apply (Hno_storer k).
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply (Hlt_res_obs3 _ _ _ _ Hlookup _ _ _ _ _
                                   Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
                  - (* Hlt_res_obs_st (CAS-fail NONEV-None): stored_at-form. *)
                    intros τ' obs'' rng_τ'' r' Hlookup
                           k k_e' r_k_e Hlt Hstored_k_e Hr_k_e_lt
                           r_k Hstored_k Hr_k_lt.
                    destruct (decide (τ' = τ)) as [->|Hne].
                    + rewrite lookup_insert_eq in Hlookup.
                      subst new_deq_info. injection Hlookup as <- <- <-.
                      subst new_obs.
                      rewrite length_app /= in Hr_k_lt.
                      destruct (decide (r_k < length obs')%nat) as [Hold|Hnew].
                      * rewrite lookup_app_l; last done.
                        by eapply (Hlt_res_obs_st3 _ _ _ _ Hτ_in_opmap3 _ _ _
                                     Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hold).
                      * assert (r_k = length obs') as Hrk_eq by lia.
                        exfalso.
                        rewrite Hlen_obs in Hrk_eq.
                        rewrite Hrk_eq in Hstored_k.
                        by apply (Hno_storer k).
                    + rewrite lookup_insert_ne in Hlookup; last done.
                      by eapply (Hlt_res_obs_st3 _ _ _ _ Hlookup _ _ _
                                   Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt). }
                do 5 wp_pure.
                wp_apply ("IH_inner").
                { iPureIntro; lia. }
                { iPureIntro.
                assert (length new_obs = length obs' + 1) as ->.
                { subst new_obs. by rewrite length_app /=. }
                lia. }
                iFrame. }
      iApply ("Hdeq_aux_spec" $! rng [] with "[%] [%] Hfrag").
      { lia. }
      { rewrite /= Z.sub_diag. done. } }
    iApply (wp_wand with "[Hfrag]").
    { iApply ("Hdeq_spec" $! [] rng_init with "Hfrag"). }
    iIntros (v) "(%obs_f & %rng_τ_f & Hfrag & #Hdq_frag)".
    wp_pures.
    (* RET-DEQ commit (task #49). *)
    wp_bind (trace_emit _ _ _)%E.
    awp_apply (trace_emit_spec l τ (Ret (SOMEV v)) (InjRV (SOMEV v))
                 (I_lang_hwq) with "Htrace_inv"); first done.
    iInv Nhwq as (items5 back_val5 ts5 s5 ls5 op_map5 stored_at5
                  cell_val_map5 dq_map5)
      "(>Hback & >Har & >Htrace & >Hauth & >Hauth_sv & Hfrag_sv &
        >Hauth_dq & Hfrag_dq & >%Hsteps5 & >%Hts_eq5 & >%Hsim5 &
        >%Hcvi5 & >%Hdqi5)".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hboth5.
    apply auth_both_valid_discrete in Hboth5 as [Hincl5 Hvalid5].
    apply singleton_included_exclusive_l in Hincl5; [|apply _|done].
    rewrite lookup_fmap in Hincl5.
    apply leibniz_equiv in Hincl5.
    apply fmap_Some_1 in Hincl5 as (info_τ5 & Hτ_in_opmap5 & Hinfo_τ5).
    destruct info_τ5; injection Hinfo_τ5 as <- <- <-.
    destruct Hsim5 as (Hlen5 & Hback_lo5 & Hslots_free5 & Hcp_fresh5
                       & Hdomsub5 & Henq_clause5 & Hdeq_clause5 & Hruniq5
                       & Hcells_wf5 & Hcells_fwd5 & Hstored5 & Hstored_inj5
                       & Hcells_stored5 & Hnot_stored5 & Hstored_link5
                       & Hres_fresh5 & Hobs_hist5 & Hlt_res5 & Hobs_struct5
                       & Hcomp_stored5 & Hlt_stored5 & Hrng_τ_bound5
                       & Hlt_res_obs5 & Hlt_res_obs_st5).
    destruct (Hdeq_clause5 τ obs_f rng_τ_f None true Hτ_in_opmap5)
      as (_ & Hcp_τ_true).
    destruct (Hcp_τ_true eq_refl) as (Hcp_R2 & d_rv & Hrv_d).
    (* Link [v] to [rv τ] via [Hdq_frag]. *)
    iDestruct (own_valid_2 with "Hauth_dq Hdq_frag") as %Hdq_both.
    apply auth_both_valid_discrete in Hdq_both as [Hdq_incl _].
    apply singleton_included_l in Hdq_incl as (q & Hq_lookup & Hq_incl).
    rewrite /to_dqmap lookup_fmap in Hq_lookup.
    apply fmap_Some_equiv in Hq_lookup as (v_stored & Hdq_τ & Hq_eq).
    rewrite Hq_eq in Hq_incl.
    rewrite Some_included in Hq_incl.
    assert (v_stored = v) as Hv_eq.
    { destruct Hq_incl as [Heq|Hincl].
      - symmetry. by apply (inj to_agree), leibniz_equiv in Heq.
      - symmetry. by apply to_agree_included_L in Hincl. }
    rewrite Hv_eq in Hdq_τ.
    pose proof (Hdqi5 _ _ Hdq_τ) as Hrv_v.
    simpl in Hrv_v.
    assert (d_rv = SOMEV v) as Hdrv_v by (rewrite Hrv_d in Hrv_v;
      injection Hrv_v; done).
    rewrite Hdrv_v in Hrv_d.
    clear Hq_incl Hq_eq Hdrv_v d_rv Hrv_v.
    clear v_stored Hv_eq.
    destruct s5 as [O5 lt5 l5 rv5 cp5].
    simpl in Hcp_R2, Hrv_d, Hsteps5, Hts_eq5, Hcp_fresh5, Hdomsub5.
    iAssert (trace_is l ts5 ∗
             ⌜I_lang_hwq (ts5 ++ [(τ, Ret (SOMEV v))])⌝)%I
      with "[$Htrace]" as "Halpha".
    { iPureIntro.
      exists (AbsQState O5 lt5 l5 rv5 (<[τ := R3]> cp5)),
             (ls5 ++ [(τ, ARetDeq (SOMEV v))]).
      split.
      - eapply lts_steps_app; [exact Hsteps5|].
        eapply lts_steps_cons; [|apply lts_steps_nil].
        by apply absq_step_ret_deq.
      - rewrite Hts_eq5 /trace_of_absq_labels map_app /= filter_app.
        rewrite filter_cons_True; [done|]. by compute. }
    iAaccIntro with "Halpha".
    { iIntros "[Htrace _]". iModIntro.
      rewrite bi.sep_assoc. iSplitR "Hfrag"; last eauto.
      iSplitR "HΦ"; last by eauto.
      iNext. iExists items5, back_val5, ts5, _, ls5, op_map5, stored_at5,
        cell_val_map5, dq_map5.
      by iFrame. }
    iIntros "Htrace".
    iMod (own_update_2 _ _ _ (● to_opmap (delete τ op_map5))
            with "Hauth Hfrag") as "Hauth".
    { apply auth_update_dealloc.
      rewrite /to_opmap fmap_delete.
      apply: delete_singleton_local_update. }
    iModIntro.
    iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq";
      last (wp_pures; by iApply "HΦ").
    iNext.
    iExists items5, back_val5, (ts5 ++ [(τ, Ret (SOMEV v))]),
      {| absq_O := O5; absq_lt := lt5; absq_l := l5;
         absq_rv := rv5;
         absq_cp := <[τ := R3]> cp5 |},
      (ls5 ++ [(τ, ARetDeq (SOMEV v))]), (delete τ op_map5), stored_at5,
      cell_val_map5, dq_map5.
    iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
    iPureIntro. split_and!.
    - eapply lts_steps_app; [exact Hsteps5|].
      eapply lts_steps_cons; [|apply lts_steps_nil].
      by apply absq_step_ret_deq.
    - rewrite Hts_eq5 /trace_of_absq_labels map_app /= filter_app.
      rewrite filter_cons_True; [done|]. by compute.
    - split_and!; simpl.
      + exact Hlen5.
      + exact Hback_lo5.
      + exact Hslots_free5.
      + (* Hcp_fresh: τ already in dom cp5. *)
        rewrite dom_insert_L fmap_app /= list_to_set_app_L.
        assert (τ ∈ dom cp5) as Hτ_dom.
        { apply elem_of_dom. by eexists. }
        clear -Hcp_fresh5 Hτ_dom. set_solver.
      + rewrite dom_insert_L dom_delete_L.
        clear -Hdomsub5. set_solver.
      + intros τ' d' r' b' Hlookup.
        assert (τ' ≠ τ) as Hne.
        { intros ->. rewrite lookup_delete_eq in Hlookup. discriminate. }
        rewrite lookup_delete_ne in Hlookup; last done.
        destruct (Henq_clause5 _ _ _ _ Hlookup)
          as (Hcp' & Hl' & HbO' & Hreserv').
        split_and!.
        * rewrite lookup_insert_ne //.
        * exact Hl'.
        * exact HbO'.
        * exact Hreserv'.
      + intros τ' obs' rng_τ'' r' b' Hlookup.
        assert (τ' ≠ τ) as Hne.
        { intros ->. rewrite lookup_delete_eq in Hlookup. discriminate. }
        rewrite lookup_delete_ne in Hlookup; last done.
        destruct (Hdeq_clause5 _ _ _ _ _ Hlookup) as (Hcp_false' & Hcp_true').
        split.
        * intros Hbf. rewrite lookup_insert_ne //. by apply Hcp_false'.
        * intros Hbt. destruct (Hcp_true' Hbt) as (Hcp'' & d_rv' & Hrv').
          rewrite lookup_insert_ne //. split; [exact Hcp''|]. by eexists.
      + intros τ_a τ_b d_a d_b i b_a b_b Ha Hb.
        destruct (decide (τ_a = τ)) as [->|Hne_a];
          [rewrite lookup_delete_eq in Ha; discriminate|].
        destruct (decide (τ_b = τ)) as [->|Hne_b];
          [rewrite lookup_delete_eq in Hb; discriminate|].
        rewrite !lookup_delete_ne in Ha, Hb; [|done|done].
        by eapply Hruniq5.
      + exact Hcells_wf5.
      + exact Hcells_fwd5.
      + exact Hstored5.
      + exact Hstored_inj5.
      + exact Hcells_stored5.
      + intros τ' d' r' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne];
          [rewrite lookup_delete_eq in Hlookup; discriminate|].
        rewrite lookup_delete_ne in Hlookup; last done.
        by eapply Hnot_stored5.
      + intros τ' d' i' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne];
          [rewrite lookup_delete_eq in Hlookup; discriminate|].
        rewrite lookup_delete_ne in Hlookup; last done.
        by eapply Hstored_link5.
      + intros τ' d' r' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne];
          [rewrite lookup_delete_eq in Hlookup; discriminate|].
        rewrite lookup_delete_ne in Hlookup; last done.
        by eapply Hres_fresh5.
      + intros τ' obs' rng_τ'' r' b' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne];
          [rewrite lookup_delete_eq in Hlookup; discriminate|].
        rewrite lookup_delete_ne in Hlookup; last done.
        by eapply Hobs_hist5.
      + intros k k_e d' r_e b' Hlt Hlookup r_k Hstored_k.
        destruct (decide (k_e = τ)) as [->|Hne];
          [rewrite lookup_delete_eq in Hlookup; discriminate|].
        rewrite lookup_delete_ne in Hlookup; last done.
        by eapply Hlt_res5.
      + intros τ' obs' rng_τ'' r' b' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne];
          [rewrite lookup_delete_eq in Hlookup; discriminate|].
        rewrite lookup_delete_ne in Hlookup; last done.
        by eapply Hobs_struct5.
      + exact Hcomp_stored5.
      + exact Hlt_stored5.
      + intros τ' obs' rng_τ'' r' b' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne];
          [rewrite lookup_delete_eq in Hlookup; discriminate|].
        rewrite lookup_delete_ne in Hlookup; last done.
        by eapply Hrng_τ_bound5.
      + intros τ' obs' rng_τ'' r' Hlookup
               k k_e d' r_e b_e Hlt Hlookup_e Hr_e_lt
               r_k Hstored_k Hr_k_lt.
        destruct (decide (τ' = τ)) as [->|Hne];
          [rewrite lookup_delete_eq in Hlookup; discriminate|].
        rewrite lookup_delete_ne in Hlookup; last done.
        destruct (decide (k_e = τ)) as [->|Hne_e];
          [rewrite lookup_delete_eq in Hlookup_e; discriminate|].
        rewrite lookup_delete_ne in Hlookup_e; last done.
        by eapply (Hlt_res_obs5 _ _ _ _ Hlookup _ _ _ _ _
                     Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
      + intros τ' obs' rng_τ'' r' Hlookup
               k k_e r_k_e Hlt Hstored_k_e Hr_k_e_lt
               r_k Hstored_k Hr_k_lt.
        destruct (decide (τ' = τ)) as [->|Hne];
          [rewrite lookup_delete_eq in Hlookup; discriminate|].
        rewrite lookup_delete_ne in Hlookup; last done.
        by eapply (Hlt_res_obs_st5 _ _ _ _ Hlookup _ _ _
                     Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt).
    - simpl. exact Hcvi5.
    - simpl. exact Hdqi5.
  Qed.

End hwq_skeleton_deq_cont.
