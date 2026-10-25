(* refine_enq_cont.v: proof of [op_spec_enq_cont] — the
  enqueue branch of [op_spec].  Covers FAA, conditional store,
  RET-ENQ1/2 commit via trace_emit, and the diverge case when
  back ≥ sz. *)

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

Section hwq_skeleton_enq_cont.
  Context `{!traceG Σ, !hwqG Σ}.
  Context (sz : Z).
  Hypothesis sz_pos : (0 < sz)%Z.

  Local Notation valid_value := hwq_valid_value.
  Local Notation Nhwq := Nhwq.
  Local Notation hwq_inv_body := (hwq_inv_body sz).
  Local Notation is_hwq := (is_hwq sz).

  Lemma op_spec_enq_cont
    `{!heapGS Σ} (γ γ_sv γ_dq : gname) (l ar back : loc)
    (τ : positive) (d : val) (Φ : val → iProp Σ) :
    valid_value d →
    val_is_unboxed (SOMEV d) →
    inv Nhwq (hwq_inv_body γ γ_sv γ_dq ar back l) -∗
    trace_inv l (I_lang_hwq) -∗
    own γ (◯ {[τ := Excl {| op_info_kind := OpEnq d;
                            op_info_reserved := None;
                            op_info_stored := false |}]}) -∗
    (∀ v : val, True -∗ Φ v) -∗
    WP (let: "τ" := #(Z.pos τ) in
        let: "res" := enqueue (#sz, #ar, #back)%V d in
        trace_emit #l "τ" (InjR "res");; "res")
    {{ Φ }}.
  Proof.
    intros Hd_valid Hd_unboxed.
    iIntros "#Hinv #Htrace_inv Hfrag HΦ".
    wp_pures.
    rewrite /enqueue. wp_pures.
    (* PHASE 2: FAA on [back]. *)
    wp_bind (FAA _ _).
    iInv Nhwq as (items2 back_val2 ts2 s2 ls2 op_map2 stored_at2 cell_val_map2 dq_map2)
      "(>Hback & >Har & >Htrace & >Hauth & >Hauth_sv & Hfrag_sv & >Hauth_dq & Hfrag_dq & >%Hsteps2 & >%Hts_eq2 & >%Hsim2 & >%Hcvi2 & >%Hdqi2)".
    wp_faa.
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hboth.
    apply auth_both_valid_discrete in Hboth as [Hincl Hvalid_m].
    apply singleton_included_exclusive_l in Hincl; [| apply _ | done].
    rewrite lookup_fmap in Hincl.
    apply leibniz_equiv in Hincl.
    apply fmap_Some_1 in Hincl as (info_τ & Hτ_lookup & Hinfo_τ).
    destruct info_τ; injection Hinfo_τ as <- <- <-.
    rename Hτ_lookup into Hτ_in_opmap.
    set (new_info' := {| op_info_kind := OpEnq d;
                         op_info_reserved := Some back_val2;
                         op_info_stored := false |}).
    iMod (own_update_2 _ _ _
            (● to_opmap (<[τ := new_info']> op_map2)
             ⋅ ◯ {[τ := Excl new_info']}) with "Hauth Hfrag")
      as "[Hauth Hfrag]".
    { apply auth_update.
      rewrite /to_opmap fmap_insert.
      apply: singleton_local_update.
      { rewrite lookup_fmap Hτ_in_opmap //. }
      by apply exclusive_local_update. }
    destruct Hsim2 as (Hlen2 & Hback_lo2 & Hslots_free2 & Hcp_fresh2
                       & Hdomsub2 & Henq_clause2 & Hdeq_clause2 & Hruniq2
                       & Hcells_wf2 & Hcells_fwd2 & Hstored2 & Hstored_inj2 & Hcells_stored2 & Hnot_stored2 & Hstored_link2 & Hres_fresh2 & Hobs_hist2 & Hlt_res2 & Hobs_struct2 & Hcomp_stored2 & Hlt_stored2 & Hrng_τ_bound2 & Hlt_res_obs2 & Hlt_res_obs_st2).
    iModIntro.
    iSplitL "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
    { iNext.
      iExists items2, (back_val2 + 1)%Z, ts2, s2, ls2,
        (<[τ := new_info']> op_map2), stored_at2, cell_val_map2, dq_map2.
      iFrame "Hback Har Htrace Hauth Hauth_sv Hfrag_sv Hauth_dq Hfrag_dq".
      iPureIntro.
      split_and!; [exact Hsteps2 | exact Hts_eq2 | | exact Hcvi2 | exact Hdqi2].
      split_and!.
      - exact Hlen2.
      - lia.
      - intros i Hi. apply Hslots_free2. lia.
      - exact Hcp_fresh2.
      - rewrite dom_insert_L.
        assert (τ ∈ dom s2.(absq_cp)) as Hτ_in.
        { apply Hdomsub2. apply elem_of_dom. by eexists. }
        clear -Hcp_fresh2 Hdomsub2 Hτ_in. set_solver.
      - intros τ' d' r' b' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne].
        + rewrite lookup_insert_eq in Hlookup.
          inversion Hlookup as [Heq_info].
          subst new_info'; simpl in Heq_info.
          assert (d' = d ∧ r' = Some back_val2 ∧ b' = false)
            as (-> & -> & ->).
          { inversion Heq_info. done. }
          destruct (Henq_clause2 τ d None false Hτ_in_opmap)
            as (Hcp_eq & Hl_eq & HbO & _).
          split_and!; [done|done|done|].
          intros i Hr_eq. injection Hr_eq as <-.
          split_and!.
          * lia.
          * lia.
          * intros Hi_lt_sz.
            split.
            -- intros _. apply Hslots_free2. lia.
            -- intros [=].
        + rewrite lookup_insert_ne in Hlookup; last done.
          destruct (Henq_clause2 _ _ _ _ Hlookup)
            as (Hcp_eq & Hl_eq & HbO & Hreserv).
          split_and!; [done|done|done|].
          intros i' Hr_eq'. destruct (Hreserv _ Hr_eq') as (Hrng & Himpl).
          split_and!.
          * lia.
          * lia.
          * intros Hi_lt_sz. exact (Himpl Hi_lt_sz).
      - intros τ' obs' rng_τ' r' b' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne].
        + rewrite lookup_insert_eq in Hlookup.
          injection Hlookup as Hkind. discriminate.
        + rewrite lookup_insert_ne in Hlookup; last done.
          exact (Hdeq_clause2 _ _ _ _ _ Hlookup).
      - intros τ_a τ_b d_a d_b i b_a b_b Ha Hb.
        destruct (decide (τ_a = τ)) as [->|Hne_a].
        { rewrite lookup_insert_eq in Ha. inversion Ha; subst.
          destruct (decide (τ_b = τ)) as [->|Hne_b]; [done|].
          rewrite lookup_insert_ne in Hb; last done.
          destruct (Henq_clause2 _ _ _ _ Hb) as (_ & _ & _ & Hreserv).
          destruct (Hreserv _ eq_refl) as (Hrng & _). lia. }
        destruct (decide (τ_b = τ)) as [->|Hne_b].
        { rewrite lookup_insert_eq in Hb. inversion Hb; subst.
          rewrite lookup_insert_ne in Ha; last done.
          destruct (Henq_clause2 _ _ _ _ Ha) as (_ & _ & _ & Hreserv).
          destruct (Hreserv _ eq_refl) as (Hrng & _). lia. }
        rewrite !lookup_insert_ne in Ha, Hb; [|done|done].
        by eapply Hruniq2.
      - (* cells_wf (FAA): items unchanged. *) exact Hcells_wf2.
      - (* cells_fwd (FAA): items and absq state unchanged. *) exact Hcells_fwd2.
      - (* Hstored (FAA): stored_at unchanged; the back_val bound
          [i < back_val2] is weakened to [i < back_val2 + 1]. *)
        intros τ' i' Hlookup.
        destruct (Hstored2 _ _ Hlookup) as (Hbound & d' & f' & Hℓ' & HinO' & HnotO').
        split; [lia|].
        exists d', f'. split_and!; [exact Hℓ'|exact HinO'|exact HnotO'].
      - (* Hstored_inj (FAA): stored_at unchanged. *) exact Hstored_inj2.
      - (* Hcells_stored (FAA): items, stored_at, absq unchanged. *) exact Hcells_stored2.
      - (* Hnot_stored (FAA): new τ had r=None b=false; stored_at2 τ = None
          via Hnot_stored2 on pre-state.  Other τ' ≠ τ unchanged. *)
        intros τ' d' r' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne].
        + by eapply (Hnot_stored2 _ _ _ Hτ_in_opmap).
        + rewrite lookup_insert_ne in Hlookup; last done.
          by eapply Hnot_stored2.
      - (* Hstored_link (FAA): new τ has stored=false — pattern
          mismatches.  Other τ' ≠ τ unchanged. *)
        intros τ' d' i' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne].
        + rewrite lookup_insert_eq in Hlookup.
          injection Hlookup as <- <- Hstore. discriminate.
        + rewrite lookup_insert_ne in Hlookup; last done.
          by eapply Hstored_link2.
      - (* Hres_fresh (FAA): new τ's reservation is [back_val2] and
          [Hstored2] gives [i < back_val2] for every stored_at entry,
          so Z.to_nat back_val2 ≠ i.  Other τ' ≠ τ with a pre-store
          reservation r: [Hres_fresh2] applies (stored_at unchanged). *)
        intros τ' d' r' Hlookup τ'' i' Hstored_τ''.
        destruct (decide (τ' = τ)) as [->|Hne].
        + rewrite lookup_insert_eq in Hlookup.
          inversion Hlookup as [Heq_info].
          subst new_info'; simpl in Heq_info.
          assert (r' = back_val2) as ->.
          { inversion Heq_info. done. }
          destruct (Hstored2 _ _ Hstored_τ'') as (Hbound & _).
          lia.
        + rewrite lookup_insert_ne in Hlookup; last done.
          by eapply Hres_fresh2.
      - (* Hobs_hist (FAA): new τ has OpEnq kind — pattern mismatch.
          Other τ' ≠ τ unchanged. *)
        intros τ' obs' rng_τ' r' b' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne].
        + rewrite lookup_insert_eq in Hlookup.
          subst new_info'. injection Hlookup as Hkind _ _.
          discriminate Hkind.
        + rewrite lookup_insert_ne in Hlookup; last done.
          by eapply Hobs_hist2.
      - (* Hlt_res (FAA): [lt] unchanged.  For [(k, τ) ∈ lt] with new
          τ's reservation [Some back_val2], [Hstored2] applied to
          [stored_at[k] = Some r_k] gives [r_k < back_val2] directly.
          For other [(k, k_e) ∈ lt] with [k_e ≠ τ]: [op_map[k_e]]
          unchanged; apply [Hlt_res2]. *)
        intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
        destruct (decide (k_e' = τ)) as [->|Hne].
        + rewrite lookup_insert_eq in Hlookup.
          subst new_info'. injection Hlookup as _ Hres _.
          inversion Hres; subst r_e'.
          destruct (Hstored2 _ _ Hstored_k) as (Hbound & _).
          exact Hbound.
        + rewrite lookup_insert_ne in Hlookup; last done.
          by eapply Hlt_res2.
      - (* Hobs_struct (FAA): new τ is OpEnq; for τ' ≠ τ, OpDeq
          unchanged. *)
        intros τ' obs' rng_τ' r' b' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne].
        + rewrite lookup_insert_eq in Hlookup.
          subst new_info'. injection Hlookup as Hkind _ _.
          discriminate Hkind.
        + rewrite lookup_insert_ne in Hlookup; last done.
          by eapply Hobs_struct2.
      - (* Hcomp_stored (FAA): ℓ, stored_at unchanged. *)
        exact Hcomp_stored2.
      - (* Hlt_stored (FAA): lt, stored_at unchanged. *)
        exact Hlt_stored2.
      - (* Hrng_τ_bound (FAA): back_val grows by 1; rng_τ unchanged. *)
        intros τ' obs' rng_τ' r' b' Hlookup.
        destruct (decide (τ' = τ)) as [->|Hne].
        + rewrite lookup_insert_eq in Hlookup.
          subst new_info'. injection Hlookup as Hkind _ _. discriminate.
        + rewrite lookup_insert_ne in Hlookup; last done.
          specialize (Hrng_τ_bound2 _ _ _ _ _ Hlookup). lia.
      - (* Hlt_res_obs (FAA): for the newly assigned [k_e_new = τ]
          with reservation [Some back_val2], [Hrng_τ_bound2] gives
          [rng_τ ≤ back_val2], so the premise [r_e = back_val2 < rng_τ]
          fails.  For edges to other k_e ≠ τ: unchanged, apply IH. *)
        intros τ' obs' rng_τ' r' Hlookup
               k k_e d' r_e b_e Hlt Hlookup_e Hr_e_lt r_k Hstored_k Hr_k_lt.
        destruct (decide (τ' = τ)) as [->|Hne].
        { rewrite lookup_insert_eq in Hlookup.
          subst new_info'. injection Hlookup as Hkind _. discriminate. }
        rewrite lookup_insert_ne in Hlookup; last done.
        destruct (decide (k_e = τ)) as [->|Hne_e].
        { rewrite lookup_insert_eq in Hlookup_e.
          subst new_info'. injection Hlookup_e as _ Hres _.
          inversion Hres; subst r_e.
          specialize (Hrng_τ_bound2 _ _ _ _ _ Hlookup). lia. }
        rewrite lookup_insert_ne in Hlookup_e; last done.
        by eapply (Hlt_res_obs2 _ _ _ _ Hlookup _ _ _ _ _
                     Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
      - (* Hlt_res_obs_st (FAA): stored_at unchanged; for (k, τ) ∈ lt
          with τ the new enqueue, stored_at τ undefined pre and post
          (store hasn't happened).  For other k_e: unchanged. *)
        intros τ' obs' rng_τ' r' Hlookup
               k k_e r_k_e Hlt Hstored_k_e Hr_k_e_lt r_k Hstored_k Hr_k_lt.
        destruct (decide (τ' = τ)) as [->|Hne].
        { rewrite lookup_insert_eq in Hlookup.
          subst new_info'. injection Hlookup as Hkind _. discriminate. }
        rewrite lookup_insert_ne in Hlookup; last done.
        by eapply (Hlt_res_obs_st2 _ _ _ _ Hlookup _ _ _
                     Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt). }
    (* Conditional: [if: i < q_size then store else diverge]. *)
    wp_pures.
    destruct (decide (back_val2 < sz)%Z) as [Hi_lt_sz | Hi_ge_sz].
    + (* Store branch. *)
      rewrite bool_decide_eq_true_2; last lia.
      wp_pures.
      wp_bind (_ <- _)%E.
      iInv Nhwq as (items3 back_val3 ts3 s3 ls3 op_map3 stored_at3 cell_val_map3 dq_map3)
        "(>Hback3 & >Har3 & >Htrace3 & >Hauth3 & >Hauth_sv3 & Hfrag_sv3 & >Hauth_dq3 & Hfrag_dq3 & >%Hsteps3 & >%Hts_eq3 & >%Hsim3 & >%Hcvi3 & >%Hdqi3)"
        "Hclose".
      iDestruct (own_valid_2 with "Hauth3 Hfrag") as %Hboth3.
      apply auth_both_valid_discrete in Hboth3 as [Hincl3 Hvalid3].
      apply singleton_included_exclusive_l in Hincl3; [| apply _ | done].
      rewrite lookup_fmap in Hincl3.
      apply leibniz_equiv in Hincl3.
      apply fmap_Some_1 in Hincl3 as (info3 & Hτ_in_opmap3 & Hinfo3).
      destruct info3; injection Hinfo3 as <- <- <-.
      destruct Hsim3 as (Hlen3 & Hback_lo3 & Hslots_free3 & Hcp_fresh3
                         & Hdomeq3 & Henq_clause3 & Hdeq_clause3 & Hruniq3
                         & Hcells_wf3 & Hcells_fwd3 & Hstored3 & Hstored_inj3 & Hcells_stored3 & Hnot_stored3 & Hstored_link3 & Hres_fresh3 & Hobs_hist3 & Hlt_res3 & Hobs_struct3 & Hcomp_stored3 & Hlt_stored3 & Hrng_τ_bound3 & Hlt_res_obs3 & Hlt_res_obs_st3).
      destruct (Henq_clause3 τ d (Some back_val2) false Hτ_in_opmap3)
        as (Hcp_eq3 & Hl_eq3 & HbO3 & Hreserv3).
      assert (τ ∈ s3.(absq_O)) as HτO3 by exact (HbO3 eq_refl).
      destruct (Hreserv3 back_val2 eq_refl) as (Hrng3 & Himpl3).
      assert (is_Some (items3 !! Z.to_nat back_val2)) as [items3_at Hitems3_at].
      { apply lookup_lt_is_Some_2. rewrite Hlen3. lia. }
      iDestruct (update_array _ _ _ _ _ Hitems3_at with "Har3")
        as "[Hcell Hmerge]".
      assert (Hlocconv : (ar +ₗ Z.of_nat (Z.to_nat back_val2))%Z
                           = (ar +ₗ back_val2)%Z).
      { f_equal. apply Z2Nat.id. lia. }
      rewrite Hlocconv.
      wp_store.
      iDestruct ("Hmerge" $! (SOMEV d) with "[Hcell]") as "Har3".
      { rewrite -Hlocconv. iFrame. }
      set (new_info'' := {| op_info_kind := OpEnq d;
                            op_info_reserved := Some back_val2;
                            op_info_stored := true |}).
      iMod (own_update_2 _ _ _
              (● to_opmap (<[τ := new_info'']> op_map3)
               ⋅ ◯ {[τ := Excl new_info'']}) with "Hauth3 Hfrag")
        as "[Hauth3 Hfrag]".
      { apply auth_update.
        rewrite /to_opmap fmap_insert.
        apply: singleton_local_update.
        { rewrite lookup_fmap Hτ_in_opmap3 //. }
        by apply exclusive_local_update. }
      (* γ_sv update: add [(Z.to_nat back_val2, d)] to [cell_val_map3].
        [Hres_fresh3] rules out a pre-existing entry at that offset. *)
      iMod (own_update_2 _ _ _
              (● to_svmap (<[Z.to_nat back_val2 := d]> cell_val_map3)
               ⋅ ◯ to_svmap (<[Z.to_nat back_val2 := d]> cell_val_map3))
              with "Hauth_sv3 Hfrag_sv3") as "[Hauth_sv3 #Hfrag_sv3]".
      { apply auth_update.
        rewrite /to_svmap !fmap_insert.
        apply: alloc_local_update; [|done].
        rewrite lookup_fmap.
        destruct (cell_val_map3 !! Z.to_nat back_val2) as [v|] eqn:Heq; last done.
        exfalso.
        destruct (proj2 Hcvi3 _ _ Heq) as (τ_prev & f_prev & Hst_prev & _).
        by eapply (Hres_fresh3 τ d back_val2 Hτ_in_opmap3 _ _ Hst_prev). }
      iMod ("Hclose" with "[Hback3 Har3 Htrace3 Hauth3 Hauth_sv3 Hauth_dq3 Hfrag_dq3]") as "_".
      { iNext.
        iExists (<[Z.to_nat back_val2 := SOMEV d]> items3), back_val3,
          ts3, s3, ls3, (<[τ := new_info'']> op_map3),
          (<[τ := Z.to_nat back_val2]> stored_at3),
          (<[Z.to_nat back_val2 := d]> cell_val_map3),
          dq_map3.
        iFrame "Hback3 Har3 Htrace3 Hauth3 Hauth_sv3 Hfrag_sv3 Hauth_dq3 Hfrag_dq3".
        iPureIntro. split_and!; [exact Hsteps3 | exact Hts_eq3 | | | exact Hdqi3].
        split_and!.
        - rewrite length_insert. exact Hlen3.
        - exact Hback_lo3.
        - intros i Hi. rewrite list_lookup_insert_ne;
            [apply Hslots_free3; lia | lia].
        - exact Hcp_fresh3.
        - rewrite dom_insert_L.
          assert (τ ∈ dom op_map3) as Hτ_in.
          { apply elem_of_dom. by eexists. }
          clear -Hdomeq3 Hτ_in. set_solver.
        - intros τ' d' r' b' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            inversion Hlookup as [Heq_info].
            subst new_info''; simpl in Heq_info.
            assert (d' = d ∧ r' = Some back_val2 ∧ b' = true)
              as (-> & -> & ->).
            { inversion Heq_info. done. }
            split_and!; [done|done|done|].
            intros i Hr_eq. injection Hr_eq as <-.
            split_and!.
            * lia.
            * lia.
            * intros Hi_ltsz.
              split.
              -- intros [=].
              -- intros _. split.
                 ++ intros _.
                    rewrite list_lookup_insert_eq;
                      last (rewrite Hlen3; lia).
                    done.
                 ++ intros Hout. exfalso. apply Hout. exact HτO3.
          + rewrite lookup_insert_ne in Hlookup; last done.
            destruct (Henq_clause3 _ _ _ _ Hlookup)
              as (Hcp_eq' & Hl_eq' & HbO' & Hreserv').
            split_and!; [done|done|done|].
            intros i' Hr_eq'.
            destruct (Hreserv' _ Hr_eq') as (Hrng' & Himpl').
            split; [exact Hrng'|].
            intros Hi_lt_sz'.
            destruct (Himpl' Hi_lt_sz') as (Hfalse' & Htrue').
            destruct (decide (Z.to_nat i' = Z.to_nat back_val2)) as [Hieq|Hine].
            * assert (i' = back_val2) as -> by lia.
              subst r'.
              exfalso. apply Hne.
              eapply Hruniq3; [exact Hlookup | exact Hτ_in_opmap3].
            * rewrite list_lookup_insert_ne; last by lia.
              split.
              -- intros Hb_false_eq. by apply Hfalse'.
              -- intros Hb_true_eq.
                 destruct (Htrue' Hb_true_eq) as [Hin Hout].
                 split; [intros; by apply Hin | intros; by apply Hout].
        - intros τ' obs' rng_τ' r' b' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            subst new_info''. inversion Hlookup.
          + rewrite lookup_insert_ne in Hlookup; last done.
            exact (Hdeq_clause3 _ _ _ _ _ Hlookup).
        - intros τ_a τ_b d_a d_b i b_a b_b Ha Hb.
          destruct (decide (τ_a = τ)) as [->|Hne_a].
          { rewrite lookup_insert_eq in Ha. inversion Ha; subst.
            destruct (decide (τ_b = τ)) as [->|Hne_b]; [done|].
            rewrite lookup_insert_ne in Hb; last done.
            eapply Hruniq3; [exact Hτ_in_opmap3 | exact Hb]. }
          destruct (decide (τ_b = τ)) as [->|Hne_b].
          { rewrite lookup_insert_eq in Hb. inversion Hb; subst.
            rewrite lookup_insert_ne in Ha; last done.
            eapply Hruniq3; [exact Ha | exact Hτ_in_opmap3]. }
          rewrite !lookup_insert_ne in Ha, Hb; [|done|done].
          by eapply Hruniq3.
        - (* cells_wf (store): items[back_val2] := SOMEV d. *)
          intros i Hi.
          destruct (decide (i = Z.to_nat back_val2)) as [->|Hne].
          + rewrite list_lookup_insert_eq; last (rewrite Hlen3; lia).
            right. exists d. split_and!; done.
          + rewrite list_lookup_insert_ne; last done.
            exact (Hcells_wf3 _ Hi).
        - (* cells_fwd (store): witness for the new SOMEV d cell is [τ]
            itself, which is in [O] (from [HτO3]) and has [ℓ(τ) = (d,
            PEND)] (from [Hl_eq3]).  Other cells unchanged. *)
          intros i d' Hitems_i.
          destruct (decide (i = Z.to_nat back_val2)) as [->|Hne].
          + rewrite list_lookup_insert_eq in Hitems_i;
              last (rewrite Hlen3; lia).
            injection Hitems_i as <-.
            exists τ. split; [exact HτO3|]. exists PEND. exact Hl_eq3.
          + rewrite list_lookup_insert_ne in Hitems_i; last done.
            exact (Hcells_fwd3 _ _ Hitems_i).
        - (* Hstored (store): new stored_at has τ → back_val2 added.
            For τ itself: back_val2 < back_val3 trivially (we stored at
            pre-FAA position, but wait this is post-FAA).  Actually at
            store site we have the POST-FAA state where back_val2 is
            the reserved slot < new back_val3 = back_val2 + 1. *)
          intros τ' i' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            injection Hlookup as <-.
            split.
            * (* Z.to_nat back_val2 < Z.to_nat back_val3 from Hrng3. *)
              lia.
            * exists d, PEND. split_and!.
              { exact Hl_eq3. }
              { intros _. rewrite list_lookup_insert_eq;
                  last (rewrite Hlen3; lia). done. }
              { intros HnotO. exfalso. apply HnotO. exact HτO3. }
          + rewrite lookup_insert_ne in Hlookup; last done.
            destruct (Hstored3 _ _ Hlookup)
              as (Hi_bound & d_τ' & f_τ' & Hℓ_τ' & HinO' & HnotO').
            split; [exact Hi_bound|].
            exists d_τ', f_τ'. split_and!; [exact Hℓ_τ'| | ].
            { intros Hτ'inO. specialize (HinO' Hτ'inO).
              (* If i' = Z.to_nat back_val2, HinO' says items3[back_val2]
                 = SOMEV d_τ', but Himpl3 (b=false sub-clause for τ's
                 reserved=back_val2) gives items3[back_val2] = NONEV —
                 contradiction. *)
              destruct (decide (i' = Z.to_nat back_val2)) as [->|Hne_i].
              - exfalso.
                pose proof (Himpl3 Hi_lt_sz) as [Hfalse_impl _].
                specialize (Hfalse_impl eq_refl).
                rewrite Hfalse_impl in HinO'. inversion HinO'.
              - rewrite list_lookup_insert_ne; last done. exact HinO'. }
            { intros Hτ'notO. specialize (HnotO' Hτ'notO).
              destruct (decide (i' = Z.to_nat back_val2)) as [->|Hne_i].
              - (* τ' ∉ O_s3 ∧ stored_at3 τ' = Some back_val2:
                 contradicts Hres_fresh3 applied to τ's pre-store op_map
                 entry (reserved back_val2, b=false). *)
                exfalso.
                eapply (Hres_fresh3 τ d back_val2 Hτ_in_opmap3
                          τ' (Z.to_nat back_val2) Hlookup).
                reflexivity.
              - rewrite list_lookup_insert_ne; last done. exact HnotO'. }
        - (* Hstored_inj (store): injective after adding τ → back_val2.
            τ_a ≠ τ with stored_at3 τ_a = Some back_val2 is ruled out
            by Hres_fresh3 on τ's pre-store op_map entry. *)
          intros τ_a τ_b i_x Ha Hb.
          destruct (decide (τ_a = τ)) as [->|Hne_a].
          + rewrite lookup_insert_eq in Ha. injection Ha as <-.
            destruct (decide (τ_b = τ)) as [->|Hne_b]; [done|].
            rewrite lookup_insert_ne in Hb; last done.
            exfalso.
            eapply (Hres_fresh3 τ d back_val2 Hτ_in_opmap3
                      τ_b (Z.to_nat back_val2) Hb).
            reflexivity.
          + rewrite lookup_insert_ne in Ha; last done.
            destruct (decide (τ_b = τ)) as [->|Hne_b].
            * rewrite lookup_insert_eq in Hb. injection Hb as <-.
              exfalso.
              eapply (Hres_fresh3 τ d back_val2 Hτ_in_opmap3
                        τ_a (Z.to_nat back_val2) Ha).
              reflexivity.
            * rewrite lookup_insert_ne in Hb; last done.
              by eapply Hstored_inj3.
        - (* Hcells_stored (store): items updated at back_val2; witness
            is τ itself (now in stored_at).  Other cells unchanged. *)
          intros i d' Hitems_i.
          destruct (decide (i = Z.to_nat back_val2)) as [->|Hne].
          + rewrite list_lookup_insert_eq in Hitems_i;
              last (rewrite Hlen3; lia).
            injection Hitems_i as <-.
            exists τ. split_and!.
            * by rewrite lookup_insert_eq.
            * exact HτO3.
            * exists PEND. exact Hl_eq3.
          + rewrite list_lookup_insert_ne in Hitems_i; last done.
            destruct (Hcells_stored3 _ _ Hitems_i)
              as (τ' & Hstored_τ' & Hτ'_O & f' & Hℓ_τ').
            (* τ' ≠ τ: τ has stored_at3 = None (Hnot_stored3 on
               Hτ_in_opmap3), so a τ' witnessing this cell can't
               be τ. *)
            assert (τ' ≠ τ) as Hτ'_ne_τ.
            { intros ->.
              pose proof (Hnot_stored3 _ _ _ Hτ_in_opmap3) as Hnone.
              rewrite Hnone in Hstored_τ'. discriminate. }
            exists τ'. split_and!; [|exact Hτ'_O|by exists f'].
            rewrite lookup_insert_ne //.
        - (* Hnot_stored (store): τ now has stored=true so the clause
            for τ's entry is vacuous; other τ' with b'=false unchanged. *)
          intros τ' d' r' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            injection Hlookup as Hkind Hres Hstore.
            discriminate Hstore.
          + rewrite lookup_insert_ne in Hlookup; last done.
            rewrite lookup_insert_ne.
            * by eapply Hnot_stored3.
            * intros ->.
              pose proof (Hnot_stored3 _ _ _ Hlookup) as Hnone.
              done.
        - (* Hstored_link (store): τ is newly stored — new op_map entry
            has b=true, reserved=Some back_val2, stored_at has
            τ → Z.to_nat back_val2. *)
          intros τ' d' i' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            inversion Hlookup; subst.
            by rewrite lookup_insert_eq.
          + rewrite lookup_insert_ne in Hlookup; last done.
            rewrite lookup_insert_ne; last done.
            by eapply Hstored_link3.
        - (* Hres_fresh (store): τ transitioned to b=true so is vacuous
            for τ' = τ.  For τ' ≠ τ (still pre-store with reservation
            r'): need stored_at3[τ:=back_val2] τ'' ≠ Some (Z.to_nat r').
            For τ'' = τ: new entry is back_val2, and Hruniq3 gives
            r' ≠ back_val2 (else τ = τ').  For τ'' ≠ τ: Hres_fresh3. *)
          intros τ' d' r' Hlookup τ'' i' Hstored_τ''.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            injection Hlookup as Hkind Hres Hstore.
            discriminate Hstore.
          + rewrite lookup_insert_ne in Hlookup; last done.
            destruct (decide (τ'' = τ)) as [->|Hne''].
            * rewrite lookup_insert_eq in Hstored_τ''.
              injection Hstored_τ'' as <-.
              intros Heq_r.
              assert (r' = back_val2) as Hr'_eq.
              { assert (0 ≤ r')%Z as Hr'_nn.
                { destruct (Henq_clause3 _ _ _ _ Hlookup)
                    as (_ & _ & _ & Hreserv).
                  destruct (Hreserv _ eq_refl) as (Hrng & _). lia. }
                lia. }
              subst r'.
              assert (τ' = τ); [|done].
              eapply Hruniq3; [exact Hlookup | exact Hτ_in_opmap3].
            * rewrite lookup_insert_ne in Hstored_τ''; last done.
              by eapply Hres_fresh3.
        - (* Hobs_hist (store): τ is OpEnq so pattern mismatch for τ.
            For other τ' ≠ τ with OpDeq obs: obs unchanged.  Any
            recorded [(j, Some k')] has [k' ≠ τ] because pre-store
            [stored_at τ = None] (Hnot_stored3) contradicts
            [stored_at k' = Some (Z.to_nat j)] from Hobs_hist3.  Thus
            the stored_at update [τ → back_val2] doesn't affect
            [stored_at k'] for any recorded [k']. *)
          intros τ' obs' rng_τ' r' b' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            injection Hlookup as Hkind. discriminate Hkind.
          + rewrite lookup_insert_ne in Hlookup; last done.
            intros Hb' j k' Hk'_in.
            destruct (Hobs_hist3 _ _ _ _ _ Hlookup Hb' _ _ Hk'_in)
              as (Hstored_k' & Hk'_notO).
            assert (k' ≠ τ) as Hk'_ne.
            { intros ->.
              pose proof (Hnot_stored3 _ _ _ Hτ_in_opmap3) as Hnone.
              rewrite Hnone in Hstored_k'. discriminate. }
            split; [|exact Hk'_notO].
            rewrite lookup_insert_ne; done.
        - (* Hlt_res (store): [lt] unchanged, [op_map] updates τ's
            entry only in the stored flag (b=false→true), reserved
            stays at [Some back_val2].  [stored_at] adds [τ → Z.to_nat
            back_val2].  For [(k, k_e) ∈ lt]: if [k_e = τ], the
            post-state reservation is still [back_val2]; pre-state
            [Hlt_res3] suffices.  If [k = τ], then pre-store
            [stored_at[τ] = None] (Hnot_stored3), but [(τ, k_e) ∈ lt]
            requires [ℓ[τ] = (_, COMP)] by [absq_wf_lt_COMP], yet
            [Henq_clause3] gives [ℓ[τ] = (d, PEND)] — contradiction. *)
          intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
          assert (absq_wf valid_value s3) as Hwf3.
          { eapply absq_wf_steps; [exact Hsteps3|apply absq_wf_init]. }
          (* [k ≠ τ]: otherwise [ℓ[τ] = (_, COMP)] contradicts [Hl_eq3]. *)
          assert (k ≠ τ) as Hne_k.
          { intros ->.
            destruct (absq_wf_lt_COMP _ _ Hwf3 _ _ Hlt) as (d'' & Hℓ_τ).
            rewrite Hl_eq3 in Hℓ_τ. inversion Hℓ_τ. }
          rewrite lookup_insert_ne in Hstored_k; last done.
          destruct (decide (k_e' = τ)) as [->|Hne_e].
          + rewrite lookup_insert_eq in Hlookup.
            injection Hlookup as _ Hres _.
            inversion Hres; subst r_e'.
            by eapply (Hlt_res3 k τ d back_val2 false Hlt Hτ_in_opmap3 r_k Hstored_k).
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply (Hlt_res3 _ _ _ _ _ Hlt Hlookup _ Hstored_k).
        - (* Hobs_struct (store): τ is OpEnq; for τ' ≠ τ, OpDeq unchanged. *)
          intros τ' obs' rng_τ' r' b' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            injection Hlookup as Hkind. discriminate.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply Hobs_struct3.
        - (* Hcomp_stored (store): ℓ unchanged; stored_at grows monotonically. *)
          intros k d' Hℓ_k.
          destruct (Hcomp_stored3 _ _ Hℓ_k) as (r & Hst).
          destruct (decide (k = τ)) as [->|Hne_k].
          + exists (Z.to_nat back_val2). by rewrite lookup_insert_eq.
          + exists r. rewrite lookup_insert_ne //.
        - (* Hlt_stored (store): stored_at adds [τ → Z.to_nat back_val2].
            For (k, τ) ∈ lt: impossible by [absq_wf_lt_COMP] + pre-store
            [ℓ τ = (d, PEND)] (COMP vs PEND).  For (τ, k_e) ∈ lt: same
            impossibility.  For other (k, k_e) with k, k_e ≠ τ: apply
            pre-state [Hlt_stored3]. *)
          intros k k_e r_k r_k_e Hlt Hstored_k Hstored_k_e.
          assert (absq_wf valid_value s3) as Hwf3.
          { eapply absq_wf_steps; [exact Hsteps3|apply absq_wf_init]. }
          assert (k ≠ τ) as Hne_k.
          { intros ->.
            destruct (absq_wf_lt_COMP _ _ Hwf3 _ _ Hlt) as (d' & Hℓ_τ).
            rewrite Hl_eq3 in Hℓ_τ. inversion Hℓ_τ. }
          rewrite lookup_insert_ne in Hstored_k; last done.
          destruct (decide (k_e = τ)) as [->|Hne_e].
          + rewrite lookup_insert_eq in Hstored_k_e.
            injection Hstored_k_e as <-.
            by eapply (Hlt_res3 k τ d back_val2 false Hlt Hτ_in_opmap3 _ Hstored_k).
          + rewrite lookup_insert_ne in Hstored_k_e; last done.
            by eapply (Hlt_stored3 _ _ _ _ Hlt Hstored_k Hstored_k_e).
        - (* Hrng_τ_bound (store): back_val unchanged; τ's pattern
            mismatches OpDeq (τ is OpEnq).  For τ' ≠ τ, rng_τ same. *)
          intros τ' obs' rng_τ' r' b' Hlookup.
          destruct (decide (τ' = τ)) as [->|Hne].
          + rewrite lookup_insert_eq in Hlookup.
            injection Hlookup as Hkind _ _. discriminate.
          + rewrite lookup_insert_ne in Hlookup; last done.
            by eapply Hrng_τ_bound3.
        - (* Hlt_res_obs (store): lt unchanged.  For (k, k_e) ∈ lt with
            k_e ∈ op_map: k_e = τ possible (τ's entry flipped to
            stored=true, kind+reserved unchanged).  stored_at adds [τ →
            Z.to_nat back_val2].  For (k, k_e) with k = τ, [(τ, _) ∈ lt]
            contradicts [ℓ τ = (d, PEND)] via absq_wf_lt_COMP.  For
            other k with stored_at unchanged: use Hlt_res_obs3.  obs
            entries unchanged. *)
          intros τ' obs' rng_τ' r' Hlookup
                 k k_e d' r_e b_e Hlt Hlookup_e Hr_e_lt r_k Hstored_k Hr_k_lt.
          destruct (decide (τ' = τ)) as [->|Hne].
          { rewrite lookup_insert_eq in Hlookup.
            injection Hlookup as Hkind _ _. discriminate. }
          rewrite lookup_insert_ne in Hlookup; last done.
          (* [k ≠ τ]: otherwise [ℓ τ = (_, COMP)] contradicts [ℓ τ =
             (d, PEND)] pre-store. *)
          assert (absq_wf valid_value s3) as Hwf3.
          { eapply absq_wf_steps; [exact Hsteps3|apply absq_wf_init]. }
          assert (k ≠ τ) as Hne_k.
          { intros ->.
            destruct (absq_wf_lt_COMP _ _ Hwf3 _ _ Hlt) as (d'' & Hℓ_τ).
            rewrite Hl_eq3 in Hℓ_τ. inversion Hℓ_τ. }
          rewrite lookup_insert_ne in Hstored_k; last done.
          destruct (decide (k_e = τ)) as [->|Hne_e].
          + rewrite lookup_insert_eq in Hlookup_e.
            injection Hlookup_e as _ Hres _.
            inversion Hres; subst r_e.
            by eapply (Hlt_res_obs3 _ _ _ _ Hlookup _ _ _ _ _
                         Hlt Hτ_in_opmap3 Hr_e_lt _ Hstored_k Hr_k_lt).
          + rewrite lookup_insert_ne in Hlookup_e; last done.
            by eapply (Hlt_res_obs3 _ _ _ _ Hlookup _ _ _ _ _
                         Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
        - (* Hlt_res_obs_st (store): stored_at gains τ → back_val2.
            For (k, τ) ∈ lt: impossible by absq_wf_lt_COMP + [ℓ τ =
            (d, PEND)].  For (τ, k_e) ∈ lt: same.  For other (k, k_e)
            with k, k_e ≠ τ: apply Hlt_res_obs_st3.  obs unchanged. *)
          intros τ' obs' rng_τ' r' Hlookup
                 k k_e r_k_e Hlt Hstored_k_e Hr_k_e_lt r_k Hstored_k Hr_k_lt.
          destruct (decide (τ' = τ)) as [->|Hne].
          { rewrite lookup_insert_eq in Hlookup.
            injection Hlookup as Hkind _ _. discriminate. }
          rewrite lookup_insert_ne in Hlookup; last done.
          (* [k ≠ τ]: otherwise [ℓ τ = (_, COMP)] contradicts PEND. *)
          assert (absq_wf valid_value s3) as Hwf3.
          { eapply absq_wf_steps; [exact Hsteps3|apply absq_wf_init]. }
          assert (k ≠ τ) as Hne_k.
          { intros ->.
            destruct (absq_wf_lt_COMP _ _ Hwf3 _ _ Hlt) as (d'' & Hℓ_τ).
            rewrite Hl_eq3 in Hℓ_τ. inversion Hℓ_τ. }
          rewrite lookup_insert_ne in Hstored_k; last done.
          destruct (decide (k_e = τ)) as [->|Hne_e].
          { rewrite lookup_insert_eq in Hstored_k_e.
            injection Hstored_k_e as Hrk_e_eq.
            (* Use Hlt_res_obs3 on op_map τ (pre-store OpEnq entry)
               to reach obs[r_k] = Some; back_val2 < rng_τ' follows
               from Hr_k_e_lt + Hrk_e_eq. *)
            assert ((back_val2 < rng_τ')%Z) as Hbv2_lt.
            { rewrite -Hrk_e_eq in Hr_k_e_lt.
              rewrite Z2Nat.id in Hr_k_e_lt; [exact Hr_k_e_lt|exact Hback_lo2]. }
            by eapply (Hlt_res_obs3 _ _ _ _ Hlookup k τ d back_val2 false
                         Hlt Hτ_in_opmap3 Hbv2_lt _ Hstored_k Hr_k_lt). }
          rewrite lookup_insert_ne in Hstored_k_e; last done.
          by eapply (Hlt_res_obs_st3 _ _ _ _ Hlookup _ _ _
                       Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt).
        - (* cell_val_inv (store): forward direction: for any storer
            (τ_any, i), cell_val_map has the entry.  Reverse direction:
            every cell_val_map entry is backed by a storer.  Both
            extended with the (τ, Z.to_nat back_val2, d) pair. *)
          destruct Hcvi3 as (Hcvi3_fwd & Hcvi3_bwd).
          split; simpl.
          + (* forward: stored_at τ → ℓ τ → cell_val_map i = d *)
            intros τ_any i_any d_any f_any Hst Hℓ.
            destruct (decide (τ_any = τ)) as [->|Hne_τ].
            * rewrite lookup_insert_eq in Hst.
              injection Hst as <-.
              rewrite lookup_insert_eq.
              rewrite Hl_eq3 in Hℓ. injection Hℓ as <- _.
              done.
            * rewrite lookup_insert_ne in Hst; last done.
              destruct (decide (i_any = Z.to_nat back_val2)) as [->|Hne_i].
              -- exfalso. by eapply (Hres_fresh3 τ d back_val2 Hτ_in_opmap3 _ _ Hst).
              -- rewrite lookup_insert_ne; last done.
                 by eapply (Hcvi3_fwd _ _ _ _ Hst Hℓ).
          + (* reverse: cell_val_map i = Some v → ∃ τ f, ... *)
            intros i v Hlookup_cv.
            destruct (decide (i = Z.to_nat back_val2)) as [->|Hne_i].
            * rewrite lookup_insert_eq in Hlookup_cv.
              injection Hlookup_cv as <-.
              exists τ, PEND. split; [by rewrite lookup_insert_eq|exact Hl_eq3].
            * rewrite lookup_insert_ne in Hlookup_cv; last done.
              destruct (Hcvi3_bwd _ _ Hlookup_cv)
                as (τ_old & f_old & Hst_old & Hℓ_old).
              exists τ_old, f_old. split; [|exact Hℓ_old].
              rewrite lookup_insert_ne //.
              intros ->. rewrite (Hnot_stored3 _ _ _ Hτ_in_opmap3)
                in Hst_old. discriminate. }
      iModIntro.
      wp_pures.
      (* PHASE 3: RET commit via trace_emit. *)
      awp_apply (trace_emit_spec l τ (Ret #()) (InjRV #())
                   (I_lang_hwq) with "Htrace_inv"); first done.
      iInv Nhwq as (items4 back_val4 ts4 s4 ls4 op_map4 stored_at4 cell_val_map4 dq_map4)
        "(>Hback4 & >Har4 & >Htrace4 & >Hauth4 & >Hauth_sv4 & Hfrag_sv4
           & >Hauth_dq4 & Hfrag_dq4
           & >%Hsteps4 & >%Hts_eq4 & >%Hsim4 & >%Hcvi4 & >%Hdqi4)".
      iDestruct (own_valid_2 with "Hauth4 Hfrag") as %Hboth4.
      apply auth_both_valid_discrete in Hboth4 as [Hincl4 Hvalid4].
      apply singleton_included_exclusive_l in Hincl4; [| apply _ | done].
      rewrite lookup_fmap in Hincl4.
      apply leibniz_equiv in Hincl4.
      apply fmap_Some_1 in Hincl4 as (info4 & Hτ_in_opmap4 & Hinfo4).
      destruct info4; injection Hinfo4 as <- <- <-.
      destruct Hsim4 as (Hlen4 & Hback_lo4 & Hslots_free4 & Hcp_fresh4
                         & Hdomsub4 & Henq_clause4 & Hdeq_clause4 & Hruniq4
                         & Hcells_wf4 & Hcells_fwd4 & Hstored4 & Hstored_inj4 & Hcells_stored4 & Hnot_stored4 & Hstored_link4 & Hres_fresh4 & Hobs_hist4 & Hlt_res4 & Hobs_struct4 & Hcomp_stored4 & Hlt_stored4 & Hrng_τ_bound4 & Hlt_res_obs4 & Hlt_res_obs_st4).
      destruct (Henq_clause4 τ d (Some back_val2) true Hτ_in_opmap4)
        as (Hcp_eq4 & Hl_eq4 & _).
      destruct s4 as [O_s4 lt_s4 l_s4 rv_s4 cp_s4].
      simpl in Hcp_eq4, Hl_eq4.
      iAssert (trace_is l ts4 ∗
               ⌜I_lang_hwq (ts4 ++ [(τ, Ret #())])⌝)%I
        with "[$Htrace4]" as "Halpha".
      { iPureIntro.
        destruct (decide (τ ∈ O_s4)) as [HinO | HnotO].
        - (* RET-ENQ1 *)
          eexists _, (ls4 ++ [(τ, ARetEnq)]).
          split.
          + eapply rtcL_r; [exact Hsteps4|].
            apply absq_step_ret_enq1 with (d := d); done.
          + rewrite Hts_eq4 /trace_of_absq_labels map_app /= filter_app.
            rewrite filter_cons_True; [done|]. by compute.
        - (* RET-ENQ2 *)
          eexists _, (ls4 ++ [(τ, ARetEnq)]).
          split.
          + eapply rtcL_r; [exact Hsteps4|].
            apply absq_step_ret_enq2; done.
          + rewrite Hts_eq4 /trace_of_absq_labels map_app /= filter_app.
            rewrite filter_cons_True; [done|]. by compute. }
      iAaccIntro with "Halpha".
      { iIntros "[Htrace4 _]".
        iModIntro. rewrite bi.sep_assoc. iSplitR "Hfrag"; last eauto.
        iSplitR "HΦ"; last by eauto.
        iNext. iExists items4, back_val4, ts4, _, ls4, op_map4, stored_at4,
          cell_val_map4, dq_map4.
        by iFrame. }
      iIntros "Htrace4".
      iMod (own_update_2 _ _ _ (● to_opmap (delete τ op_map4))
              with "Hauth4 Hfrag") as "Hauth4".
      { apply auth_update_dealloc.
        rewrite /to_opmap fmap_delete.
        apply: delete_singleton_local_update. }
      destruct (decide (τ ∈ O_s4)) as [HinO | HnotO].
      { (* RET-ENQ1 close *)
        iModIntro.
        iSplitL "Hback4 Har4 Htrace4 Hauth4 Hauth_sv4 Hfrag_sv4 Hauth_dq4 Hfrag_dq4";
          last (wp_pures; by iApply "HΦ").
        iNext.
        iExists items4, back_val4, (ts4 ++ [(τ, Ret #())]),
          {| absq_O := O_s4; absq_lt := lt_s4;
             absq_l := <[τ := (d, COMP)]> l_s4;
             absq_rv := rv_s4;
             absq_cp := <[τ := A2]> cp_s4 |},
          (ls4 ++ [(τ, ARetEnq)]), (delete τ op_map4), stored_at4, cell_val_map4,
          dq_map4.
          iFrame "Hback4 Har4 Htrace4 Hauth4 Hauth_sv4 Hfrag_sv4 Hauth_dq4 Hfrag_dq4".
          iPureIntro. split_and!.
          - eapply rtcL_r; [exact Hsteps4|].
            apply absq_step_ret_enq1 with (d := d); done.
          - rewrite Hts_eq4 /trace_of_absq_labels map_app /= filter_app.
            rewrite filter_cons_True; [done|]. by compute.
          - split_and!; simpl.
            + exact Hlen4.
            + exact Hback_lo4.
            + exact Hslots_free4.
            + rewrite fmap_app /= list_to_set_app_L dom_insert_L.
              assert (τ ∈ dom cp_s4) as Hτ_in.
              { apply Hdomsub4. apply elem_of_dom. by eexists. }
              clear -Hcp_fresh4 Hdomsub4 Hτ_in. set_solver.
            + rewrite dom_insert_L dom_delete_L.
              assert (τ ∈ dom cp_s4) as Hτ_in.
              { apply Hdomsub4. apply elem_of_dom. by eexists. }
              clear -Hcp_fresh4 Hdomsub4 Hτ_in. set_solver.
            + intros τ' d' r' b' Hlookup.
              assert (τ' ≠ τ) as Hne.
              { intros ->. rewrite lookup_delete_eq in Hlookup.
                discriminate. }
              rewrite lookup_delete_ne in Hlookup; last done.
              destruct (Henq_clause4 _ _ _ _ Hlookup)
                as (Hcp' & Hl' & HbO' & Hreserv').
              split_and!.
              * rewrite lookup_insert_ne //.
              * rewrite lookup_insert_ne //.
              * exact HbO'.
              * intros i' Hr_eq'.
                destruct (Hreserv' _ Hr_eq') as (Hrng' & Himpl').
                split; [exact Hrng'|].
                intros Hi_lt_sz'.
                destruct (Himpl' Hi_lt_sz') as (Hf' & Ht').
                split; [exact Hf'|].
                intros Hbeq. simpl. exact (Ht' Hbeq).
            + intros τ' obs' rng_τ' r' b' Hlookup.
              assert (τ' ≠ τ) as Hne.
              { intros ->. rewrite lookup_delete_eq in Hlookup.
                discriminate. }
              rewrite lookup_delete_ne in Hlookup; last done.
              destruct (Hdeq_clause4 _ _ _ _ _ Hlookup) as (Hcp_false & Hcp_true).
              split.
              * intros Hbf. rewrite lookup_insert_ne //. by apply Hcp_false.
              * intros Hbt. rewrite lookup_insert_ne //. by apply Hcp_true.
            + intros τ_a τ_b d_a d_b i b_a b_b Ha Hb.
              destruct (decide (τ_a = τ)) as [->|Hne_a];
                [rewrite lookup_delete_eq in Ha; discriminate|].
              destruct (decide (τ_b = τ)) as [->|Hne_b];
                [rewrite lookup_delete_eq in Hb; discriminate|].
              rewrite !lookup_delete_ne in Ha, Hb; [|done|done].
              by eapply Hruniq4.
            + (* cells_wf (RET-ENQ1): items unchanged. *) exact Hcells_wf4.
            + (* cells_fwd (RET-ENQ1): items unchanged; [ℓ] flag flip
                for τ preserves [ℓ(k_e) = (d, _)] — if [k_e = τ] then
                [ℓ(τ) = (d, PEND) = (d', PEND)] forces [d' = d], and
                the new flag is [COMP]; else unchanged. *)
              intros i d' Hitems_i.
              destruct (Hcells_fwd4 _ _ Hitems_i) as (k_e & Hk_e_O & f' & Hℓ_k_e).
              exists k_e. split; [exact Hk_e_O|].
              destruct (decide (k_e = τ)) as [->|Hk_e_ne].
              * exists COMP. rewrite lookup_insert_eq.
                rewrite Hl_eq4 in Hℓ_k_e. inversion Hℓ_k_e. done.
              * exists f'. rewrite lookup_insert_ne //.
            + (* Hstored (RET-ENQ1): stored_at unchanged; ℓ(τ) flipped
                to COMP.  For τ' ≠ τ: unchanged.  For τ' = τ: ℓ now
                COMP, still exists. *)
              intros τ' i' Hlookup.
              destruct (Hstored4 _ _ Hlookup)
                as (Hbound' & d' & f' & Hℓ' & HinO' & HnotO').
              split; [exact Hbound'|].
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite Hl_eq4 in Hℓ'.
                assert (d' = d) as Hdd' by (inversion Hℓ'; done).
                subst d'.
                exists d, COMP. split_and!.
                { by rewrite lookup_insert_eq. }
                { intros _. by apply HinO'. }
                { intros HτnotO. by apply HnotO'. }
              * exists d', f'. split_and!.
                { rewrite lookup_insert_ne //. }
                { exact HinO'. }
                { exact HnotO'. }
            + (* Hstored_inj (RET-ENQ1): stored_at unchanged. *)
              exact Hstored_inj4.
            + (* Hcells_stored (RET-ENQ1): items unchanged; each SOMEV
                cell still has a storer in [O]; the ℓ flag may flip. *)
              intros i d' Hitems_i.
              destruct (Hcells_stored4 _ _ Hitems_i)
                as (τ' & Hstored_τ' & Hτ'_O & f' & Hℓ_τ').
              exists τ'. split_and!; [exact Hstored_τ'|exact Hτ'_O|].
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite Hl_eq4 in Hℓ_τ'.
                assert (d = d') as -> by (inversion Hℓ_τ'; done).
                exists COMP. by rewrite lookup_insert_eq.
              * exists f'. by rewrite lookup_insert_ne.
            + (* Hnot_stored (RET-ENQ1): τ was deleted from op_map.
                For τ' ≠ τ: use Hnot_stored4.  For τ = τ: not in map. *)
              intros τ' d' r' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hnot_stored4.
            + (* Hstored_link (RET-ENQ1): τ deleted; for τ' ≠ τ use
                Hstored_link4.  For τ = τ: not in map. *)
              intros τ' d' i' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hstored_link4.
            + (* Hres_fresh (RET-ENQ1): τ deleted; stored_at unchanged.
                For τ' ≠ τ still in op_map with pre-store reservation,
                Hres_fresh4 applies. *)
              intros τ' d' r' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hres_fresh4.
            + (* Hobs_hist (RET-ENQ1): τ deleted (OpEnq, not OpDeq);
                stored_at, O unchanged.  For τ' ≠ τ with OpDeq: unchanged. *)
              intros τ' obs' rng_τ' r' b' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hobs_hist4.
            + (* Hlt_res (RET-ENQ1): τ deleted.  [lt] and [stored_at]
                unchanged.  For [(k, k_e) ∈ lt] with [k_e = τ]:
                [op_map'[τ] = None], vacuous.  For [k_e ≠ τ]: unchanged;
                apply [Hlt_res4]. *)
              intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
              destruct (decide (k_e' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hlt_res4.
            + (* Hobs_struct (RET-ENQ1): τ deleted; for τ' ≠ τ, OpDeq unchanged. *)
              intros τ' obs' rng_τ' r' b' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hobs_struct4.
            + (* Hcomp_stored (RET-ENQ1): ℓ[τ] becomes (d, COMP); use
                 pre-step [Hstored_link4] on [op_map τ = OpEnq d (Some
                 back_val2) true] (post-store) to get [stored_at τ =
                 Some (Z.to_nat back_val2)].  For k ≠ τ with ℓ[k] = COMP
                 (unchanged pre→post except τ): use Hcomp_stored4. *)
              intros k d' Hℓ_k.
              destruct (decide (k = τ)) as [->|Hne_k].
              * exists (Z.to_nat back_val2).
                by eapply Hstored_link4.
              * rewrite lookup_insert_ne in Hℓ_k; last done.
                by eapply Hcomp_stored4.
            + (* Hlt_stored (RET-ENQ1): lt, stored_at unchanged. *)
              exact Hlt_stored4.
            + (* Hrng_τ_bound (RET-ENQ1): τ deleted (OpEnq), back_val
                unchanged.  For τ' ≠ τ, unchanged. *)
              intros τ' obs' rng_τ' r' b' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hrng_τ_bound4.
            + (* Hlt_res_obs (RET-ENQ1): τ deleted; [lt] unchanged.
                For (k, k_e) ∈ lt with k_e = τ: op_map'[τ] = None, vacuous.
                For k_e ≠ τ: unchanged; use Hlt_res_obs4. *)
              intros τ' obs' rng_τ' r' Hlookup
                     k k_e d' r_e b_e Hlt Hlookup_e Hr_e_lt r_k Hstored_k Hr_k_lt.
              destruct (decide (τ' = τ)) as [->|Hne].
              { rewrite lookup_delete_eq in Hlookup. discriminate. }
              rewrite lookup_delete_ne in Hlookup; last done.
              destruct (decide (k_e = τ)) as [->|Hne_e].
              { rewrite lookup_delete_eq in Hlookup_e. discriminate. }
              rewrite lookup_delete_ne in Hlookup_e; last done.
              by eapply (Hlt_res_obs4 _ _ _ _ Hlookup _ _ _ _ _
                           Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
            + (* Hlt_res_obs_st (RET-ENQ1): stored_at unchanged; lt
                unchanged; obs unchanged; τ deleted from op_map but
                op_map τ wasn't the premise. *)
              intros τ' obs' rng_τ' r' Hlookup
                     k k_e r_k_e Hlt Hstored_k_e Hr_k_e_lt r_k Hstored_k Hr_k_lt.
              destruct (decide (τ' = τ)) as [->|Hne].
              { rewrite lookup_delete_eq in Hlookup. discriminate. }
              rewrite lookup_delete_ne in Hlookup; last done.
              by eapply (Hlt_res_obs_st4 _ _ _ _ Hlookup _ _ _
                           Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt).
          - (* cell_val_inv (RET-ENQ1): stored_at unchanged; ℓ τ
              flipped from (d, PEND) to (d, COMP), same value.  Both
              directions preserved. *)
            destruct Hcvi4 as (Hcvi4_fwd & Hcvi4_bwd).
            split; simpl.
            + intros τ_any i d_any f_any Hst Hℓ.
              destruct (decide (τ_any = τ)) as [->|Hne_τ].
              * rewrite lookup_insert_eq in Hℓ.
                injection Hℓ as <- _.
                by eapply (Hcvi4_fwd _ _ _ PEND Hst Hl_eq4).
              * rewrite lookup_insert_ne in Hℓ; last done.
                by eapply (Hcvi4_fwd _ _ _ _ Hst Hℓ).
            + intros i v Hlookup_cv.
              destruct (Hcvi4_bwd _ _ Hlookup_cv)
                as (τ_old & f_old & Hst_old & Hℓ_old).
              exists τ_old. destruct (decide (τ_old = τ)) as [->|Hne_τ].
              * exists COMP. rewrite Hl_eq4 in Hℓ_old.
                injection Hℓ_old as <- _.
                split; [exact Hst_old|by rewrite lookup_insert_eq].
              * exists f_old. split; [exact Hst_old|].
                by rewrite lookup_insert_ne.
          - (* dq_inv (RET-ENQ1): dq_map unchanged; rv unchanged. *)
            simpl. exact Hdqi4. }
      { (* RET-ENQ2 close *)
        iModIntro.
        iSplitL "Hback4 Har4 Htrace4 Hauth4 Hauth_sv4 Hfrag_sv4 Hauth_dq4 Hfrag_dq4";
          last (wp_pures; by iApply "HΦ").
        iNext.
        iExists items4, back_val4, (ts4 ++ [(τ, Ret #())]),
          {| absq_O := O_s4; absq_lt := lt_s4;
             absq_l := l_s4;
             absq_rv := rv_s4;
             absq_cp := <[τ := A2]> cp_s4 |},
          (ls4 ++ [(τ, ARetEnq)]), (delete τ op_map4), stored_at4, cell_val_map4,
          dq_map4.
          iFrame "Hback4 Har4 Htrace4 Hauth4 Hauth_sv4 Hfrag_sv4 Hauth_dq4 Hfrag_dq4".
          iPureIntro. split_and!.
          - eapply rtcL_r; [exact Hsteps4|].
            apply absq_step_ret_enq2; done.
          - rewrite Hts_eq4 /trace_of_absq_labels map_app /= filter_app.
            rewrite filter_cons_True; [done|]. by compute.
          - split_and!; simpl.
            + exact Hlen4.
            + exact Hback_lo4.
            + exact Hslots_free4.
            + rewrite fmap_app /= list_to_set_app_L dom_insert_L.
              assert (τ ∈ dom cp_s4) as Hτ_in.
              { apply Hdomsub4. apply elem_of_dom. by eexists. }
              clear -Hcp_fresh4 Hdomsub4 Hτ_in. set_solver.
            + rewrite dom_insert_L dom_delete_L.
              assert (τ ∈ dom cp_s4) as Hτ_in.
              { apply Hdomsub4. apply elem_of_dom. by eexists. }
              clear -Hcp_fresh4 Hdomsub4 Hτ_in. set_solver.
            + intros τ' d' r' b' Hlookup.
              assert (τ' ≠ τ) as Hne.
              { intros ->. rewrite lookup_delete_eq in Hlookup.
                discriminate. }
              rewrite lookup_delete_ne in Hlookup; last done.
              destruct (Henq_clause4 _ _ _ _ Hlookup)
                as (Hcp' & Hl' & HbO' & Hreserv').
              split_and!.
              * rewrite lookup_insert_ne //.
              * exact Hl'.
              * exact HbO'.
              * exact Hreserv'.
            + intros τ' obs' rng_τ' r' b' Hlookup.
              assert (τ' ≠ τ) as Hne.
              { intros ->. rewrite lookup_delete_eq in Hlookup.
                discriminate. }
              rewrite lookup_delete_ne in Hlookup; last done.
              destruct (Hdeq_clause4 _ _ _ _ _ Hlookup) as (Hcp_false & Hcp_true).
              split.
              * intros Hbf. rewrite lookup_insert_ne //. by apply Hcp_false.
              * intros Hbt. rewrite lookup_insert_ne //. by apply Hcp_true.
            + intros τ_a τ_b d_a d_b i b_a b_b Ha Hb.
              destruct (decide (τ_a = τ)) as [->|Hne_a];
                [rewrite lookup_delete_eq in Ha; discriminate|].
              destruct (decide (τ_b = τ)) as [->|Hne_b];
                [rewrite lookup_delete_eq in Hb; discriminate|].
              rewrite !lookup_delete_ne in Ha, Hb; [|done|done].
              by eapply Hruniq4.
            + (* cells_wf (RET-ENQ2): items unchanged. *) exact Hcells_wf4.
            + (* cells_fwd (RET-ENQ2): items, [ℓ], [O] unchanged. *)
              exact Hcells_fwd4.
            + (* Hstored (RET-ENQ2): items, ℓ, O unchanged. *) exact Hstored4.
            + (* Hstored_inj (RET-ENQ2): stored_at unchanged. *) exact Hstored_inj4.
            + (* Hcells_stored (RET-ENQ2): items, ℓ, O unchanged. *) exact Hcells_stored4.
            + (* Hnot_stored (RET-ENQ2): τ deleted; for τ' ≠ τ use Hnot_stored4. *)
              intros τ' d' r' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hnot_stored4.
            + (* Hstored_link (RET-ENQ2): τ deleted; for τ' ≠ τ use Hstored_link4. *)
              intros τ' d' i' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hstored_link4.
            + (* Hres_fresh (RET-ENQ2): τ deleted; stored_at unchanged. *)
              intros τ' d' r' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hres_fresh4.
            + (* Hobs_hist (RET-ENQ2): same as RET-ENQ1. *)
              intros τ' obs' rng_τ' r' b' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hobs_hist4.
            + (* Hlt_res (RET-ENQ2): same as RET-ENQ1. *)
              intros k k_e' d' r_e' b' Hlt Hlookup r_k Hstored_k.
              destruct (decide (k_e' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hlt_res4.
            + (* Hobs_struct (RET-ENQ2): same as RET-ENQ1. *)
              intros τ' obs' rng_τ' r' b' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hobs_struct4.
            + (* Hcomp_stored (RET-ENQ2): ℓ, stored_at unchanged. *)
              exact Hcomp_stored4.
            + (* Hlt_stored (RET-ENQ2): lt, stored_at unchanged. *)
              exact Hlt_stored4.
            + (* Hrng_τ_bound (RET-ENQ2): τ deleted; rest unchanged. *)
              intros τ' obs' rng_τ' r' b' Hlookup.
              destruct (decide (τ' = τ)) as [->|Hne].
              * rewrite lookup_delete_eq in Hlookup. discriminate.
              * rewrite lookup_delete_ne in Hlookup; last done.
                by eapply Hrng_τ_bound4.
            + (* Hlt_res_obs (RET-ENQ2): same as RET-ENQ1. *)
              intros τ' obs' rng_τ' r' Hlookup
                     k k_e d' r_e b_e Hlt Hlookup_e Hr_e_lt r_k Hstored_k Hr_k_lt.
              destruct (decide (τ' = τ)) as [->|Hne].
              { rewrite lookup_delete_eq in Hlookup. discriminate. }
              rewrite lookup_delete_ne in Hlookup; last done.
              destruct (decide (k_e = τ)) as [->|Hne_e].
              { rewrite lookup_delete_eq in Hlookup_e. discriminate. }
              rewrite lookup_delete_ne in Hlookup_e; last done.
              by eapply (Hlt_res_obs4 _ _ _ _ Hlookup _ _ _ _ _
                           Hlt Hlookup_e Hr_e_lt _ Hstored_k Hr_k_lt).
            + (* Hlt_res_obs_st (RET-ENQ2): same as RET-ENQ1. *)
              intros τ' obs' rng_τ' r' Hlookup
                     k k_e r_k_e Hlt Hstored_k_e Hr_k_e_lt r_k Hstored_k Hr_k_lt.
              destruct (decide (τ' = τ)) as [->|Hne].
              { rewrite lookup_delete_eq in Hlookup. discriminate. }
              rewrite lookup_delete_ne in Hlookup; last done.
              by eapply (Hlt_res_obs_st4 _ _ _ _ Hlookup _ _ _
                           Hlt Hstored_k_e Hr_k_e_lt _ Hstored_k Hr_k_lt).
          - (* cell_val_inv (RET-ENQ2): stored_at, ℓ values unchanged
              (RET-ENQ2 leaves ℓ untouched).  Direct Hcvi4. *)
            simpl. exact Hcvi4.
          - (* dq_inv (RET-ENQ2): dq_map unchanged; rv unchanged. *)
            simpl. exact Hdqi4. }
    + (* Diverge branch: [back_val2 ≥ sz]. *)
      rewrite bool_decide_eq_false_2; last lia.
      wp_pures.
      wp_apply wp_diverge.
  Qed.

End hwq_skeleton_enq_cont.
