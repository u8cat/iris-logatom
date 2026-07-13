(* refine_enq_basket.v: spec for [enq_basket].

  [enq_basket "tail1" "nd"] tries to attach the freshly-allocated [nd]
  as the new head of the basket whose leader's predecessor is
  [tail1].  It returns:
    - [#true]:  [nd] has been spliced into [tail1]'s next chain (with
                an unmarked next-pointer); op_map[τ] now has
                [linked = true] and [node = Some nd].
    - [#false]: [tail1]'s next has become marked (the basket leader
                was dequeued) and the basket has dissolved; the
                caller should restart [enqueue].

  The proof mirrors phases 6a–7 of [refine_enq_cont.v] but on a
  basket head (mid-list) rather than the chain tail, and is invoked
  by the three CAS-fail sub-cases of phase 6a so they dispatch
  cleanly without re-deriving the basket protocol invariants. *)

From iris.algebra Require Import auth excl gmap agree mono_list.
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

From case_studies.baskets_queue Require Import impl refine.defs.

Section bq_skeleton_enq_basket.
  Context `{!traceG Σ, !bqG Σ}.

  Local Notation valid_value := bq_valid_value.
  Local Notation Nbq := Nbq.
  Local Notation bq_inv_body := bq_inv_body.

  Lemma op_spec_enq_basket
    `{!heapGS Σ} (γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w : gname)
    (l head tail tail1 nd : loc)
    (τ : positive) (d : val) :
    ⌜valid_value d⌝ -∗
    inv Nbq (bq_inv_body γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w head tail l) -∗
    trace_inv l (I_lang_bq) -∗
    own γ (◯ {[τ := Excl {| op_info_kind := OpEnq d;
                            op_info_node := None;
                            op_info_linked := false |}]}) -∗
    nd ↦ d -∗
    (* The basket loop overwrites [(nd +ₗ 1)] on each iteration's
       [(false, Some _)] branch via [nextf "nd" <- "next2"], so the
       precondition cannot pin its content; it must be an existential.
       Likewise the false-postcondition. *)
    (∃ nx, (nd +ₗ 1) ↦ nx) -∗
    (* tail1 was observed as a chain location at some past inv-open *)
    (∃ τ_t v_t,
       own γ_nm (◯ {[tail1 := to_agree
         ((τ_t, v_t) : leibnizO node_info)]})) -∗
    (* Chain-snapshot witness for τ from refine_enq_cont's phase 4: at
       past inv-open during τ's body, chain was [snap] with [tail1] at
       the chain-end (succ_at = None at length snap - 1).  Used in the
       splice-success (false, Some l_succ) sub-case to bound any
       (k, τ) ∈ lt's k-position by tail1's current position.  The
       witness is keyed by (τ, tail1) so the basket can use
       chain-id injectivity to link the witness's chain-end to the
       basket's [tail1] parameter. *)
    (∃ snap, own γ_w (◯ {[(τ, tail1) := to_agree
       (snap : leibnizO chain_snapshot)]})) -∗
    WP enq_basket #tail1 #nd {{ b,
      ⌜b = #true⌝ ∗
        own γ (◯ {[τ := Excl {| op_info_kind := OpEnq d;
                                op_info_node := Some nd;
                                op_info_linked := true |}]}) ∨
      ⌜b = #false⌝ ∗
        own γ (◯ {[τ := Excl {| op_info_kind := OpEnq d;
                                op_info_node := None;
                                op_info_linked := false |}]}) ∗
        nd ↦ d ∗ (∃ nx, (nd +ₗ 1) ↦ nx) }}.
  Proof.
    iIntros "%Hd_valid #Hinv #Htrace_inv Hfrag Hnd_v Hnd_n_ex #Htail1_witness #Hsnap_witness".
    iLöb as "IH".
    iDestruct "Hnd_n_ex" as (nx) "Hnd_n".
    rewrite /enq_basket. wp_pures.
    (* Load [tail1.next] via the persistent witness. *)
    wp_bind (! _)%E.
    iInv Nbq as (nodes del_pref head_val tail_val dummy_loc ts s ls
                 op_map node_map dq_map no_O_set witness_map)
      "(>Hhead & >Htail & >Hchain & >Htrace & >Hauth_op & >Hauth_nm & Hfrag_nm
        & >Hauth_dq & Hfrag_dq & >Hauth_del & >Hauth_calls & >Hauth_no_O & >Hauth_ls & >Hauth_w & Hfrag_w
        & >%Hsteps & >%Hts_eq & >%Hsim & >%Hdummy & >%Hnvi & >%Hdqi
        & >%Hno_O_inv & >%Hcoi & >%Hwit)".
    (* Locate [tail1] in the chain via [Htail1_witness]. *)
    iDestruct "Htail1_witness" as (τ_t v_t) "Htail1_frag".
    iDestruct (own_valid_2 with "Hauth_nm Htail1_frag") as %Hagree.
    apply auth_both_valid_discrete in Hagree as [Hincl _].
    apply singleton_included_l in Hincl as (av & Hav_lookup & Hav_incl).
    rewrite /to_nodemap lookup_fmap in Hav_lookup.
    apply fmap_Some_equiv in Hav_lookup as (info & Hnm_lookup & Hav_eq).
    rewrite Hav_eq in Hav_incl. rewrite Some_included in Hav_incl.
    assert ((τ_t, v_t) = info :> leibnizO node_info) as Hinfo_eq.
    { destruct Hav_incl as [Heq|Hin].
      - by apply (inj to_agree), leibniz_equiv in Heq.
      - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
    rewrite -Hinfo_eq in Hnm_lookup. clear Hav_eq Hav_incl Hinfo_eq info.
    pose proof Hsim as (Hlen & Hdel & _ & _ & Hnm_dom & _ & _ & _ & _ & _ & _
                       & _ & _ & _ & Hnm_chain & _).
    destruct (Hnm_dom _ _ _ Hnm_lookup) as (i_t & Hi_t_lookup).
    iDestruct (bq_chain_lookup_acc _ del_pref i_t tail1 τ_t v_t Hi_t_lookup
                with "Hchain") as "[Hv [Hn HW]]".
    wp_load.
    (* Persistent witness for the successor (if any), used in the
       CAS-success case to re-locate [l] in the post-CAS chain. *)
    iAssert (∀ lk τ_opt v,
              ⌜nodes !! (i_t + 1)%nat = Some (lk, τ_opt, v)⌝ -∗
              own γ_nm (◯ {[lk := to_agree
                ((τ_opt, v) : leibnizO node_info)]}))%I
      as "#Hsucc_lookup_to_frag".
    { iIntros (lk τ_opt v) "%Hlookup".
      pose proof (Hnm_chain _ _ _ _ Hlookup) as Hnm_l_succ.
      iApply (own_mono with "Hfrag_nm").
      apply auth_frag_mono. rewrite /to_nodemap.
      apply (proj2 (singleton_included_l _ _ _)).
      exists (to_agree ((τ_opt, v) : leibnizO node_info)). split.
      - rewrite lookup_fmap Hnm_l_succ //=.
      - reflexivity. }
    iDestruct ("HW" with "[$Hv $Hn]") as "Hchain".
    iModIntro.
    iSplitL "Hhead Htail Hchain Htrace Hauth_op Hauth_nm Hfrag_nm
             Hauth_dq Hfrag_dq Hauth_del Hauth_calls Hauth_no_O Hauth_ls Hauth_w Hfrag_w".
    { iNext. iExists nodes, del_pref, head_val, tail_val, dummy_loc, ts, s, ls,
        op_map, node_map, dq_map, no_O_set, witness_map.
      iFrame. iPureIntro.
      split_and!; auto. apply Hno_O_inv. apply Hno_O_inv. }
    wp_pures.
    (* Dispatch on the loaded value [next_value_of (mark_at) (succ_at)]. *)
    destruct (mark_at del_pref i_t) eqn:Hmark;
    destruct (succ_at nodes i_t) as [l_succ|] eqn:Hsucc;
      cbn [next_value_of].
    - (* (true, Some l_succ): InjRV #l_succ.  Match enters InjR; return
         #false (basket dissolved). *)
      wp_pures.
      iModIntro. iRight. iFrame "Hfrag Hnd_v". iSplit; first done.
      by iExists _.
    - (* (true, None): InjRV #().  Match enters InjR; return #false. *)
      wp_pures.
      iModIntro. iRight. iFrame "Hfrag Hnd_v". iSplit; first done.
      by iExists _.
    - (* (false, Some l_succ): InjLV #l_succ with [l_succ ≠ #()].
         Match enters InjL with p = #l_succ.  if p = #() is false
         (loc ≠ unit), so we take the else branch — store, CAS, dispatch. *)
      (* From [Hsucc] derive the chain lookup at position [i_t + 1]. *)
      rewrite /succ_at in Hsucc.
      destruct (nodes !! (i_t + 1)%nat) as [[[lk_succ τ_succ] v_succ]|]
        eqn:Hnext_lookup; last discriminate.
      injection Hsucc as ->.
      iAssert (own γ_nm (◯ {[l_succ := to_agree
                ((τ_succ, v_succ) : leibnizO node_info)]}))%I
        as "#Hl_succ_frag".
      { iApply "Hsucc_lookup_to_frag". iPureIntro. done. }
      wp_pures.
      (* Note: (#l_succ = #()) evaluates to false because LitLoc ≠ LitUnit. *)
      wp_store.  (* nd.next := InjLV #l_succ *)
      wp_pures.
      (* Splice CAS: middle insertion of [nd] between [tail1] and
         [l_succ] via CmpXchg tail1.next from InjLV #l_succ to
         InjLV #nd. *)
      wp_bind (CmpXchg _ _ _).
      iInv Nbq as (nodes_x del_pref_x head_val_x tail_val_x dummy_loc_x
                   ts_x s_x ls_x op_map_x node_map_x dq_map_x no_O_set_x witness_map_x)
        "(>Hhead_x & >Htail_x & >Hchain_x & >Htrace_x & >Hauth_op_x
          & >Hauth_nm_x & Hfrag_nm_x & >Hauth_dq_x & Hfrag_dq_x
          & >Hauth_del_x & >Hauth_calls_x & >Hauth_no_O_x & >Hauth_ls_x & >Hauth_w_x & Hfrag_w_x
          & >%Hsteps_x & >%Hts_eq_x & >%Hsim_x & >%Hdummy_x & >%Hnvi_x
          & >%Hdqi_x & >%Hno_O_inv_x & >%Hcoi_x & >%Hwit_x)".
      (* Locate [tail1] in [nodes_x] via [Htail1_frag]. *)
      iDestruct (own_valid_2 with "Hauth_nm_x Htail1_frag") as %Hnm_agree_x.
      apply auth_both_valid_discrete in Hnm_agree_x as [Hincl_x _].
      apply singleton_included_l in Hincl_x as (av_x & Hav_lookup_x & Hav_incl_x).
      rewrite /to_nodemap lookup_fmap in Hav_lookup_x.
      apply fmap_Some_equiv in Hav_lookup_x as (info_x & Hnm_x_lookup & Hav_eq_x).
      rewrite Hav_eq_x in Hav_incl_x. rewrite Some_included in Hav_incl_x.
      assert ((τ_t, v_t) = info_x :> leibnizO node_info) as Hinfo_x_eq.
      { destruct Hav_incl_x as [Heq|Hin].
        - by apply (inj to_agree), leibniz_equiv in Heq.
        - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
      rewrite -Hinfo_x_eq in Hnm_x_lookup.
      clear Hav_eq_x Hav_incl_x Hinfo_x_eq info_x.
      pose proof Hsim_x as (Hlen_x & Hdel_x & Hcp_in_ts_x & Hdomsub_x
                          & Hnm_dom_x & Henq_clause_x & Hdeq_clause_x
                          & Hinj_x & Hcorr_x & Hlt_pos_x & _Htbd_x
                          & Hcomp_link_x & Htail_in_x & Hhead_in_x
                          & Hnm_chain_x & Hsome_at_pos_x).
      destruct (Hnm_dom_x _ _ _ Hnm_x_lookup) as (i_t_x & Hi_t_x_lookup).
      (* Dispatch on (mark_at, succ_at) at i_t_x.  Three CAS-fail cases
         (any value other than [InjLV #l_succ]), plus the (false, Some
         l_succ_x) case which further branches on l_succ_x = l_succ. *)
      destruct (mark_at del_pref_x i_t_x) eqn:Hmark_x;
      destruct (succ_at nodes_x i_t_x) as [l_succ_x|] eqn:Hsucc_x.
      + (* (true, Some l_succ_x): cell [InjRV #l_succ_x].  CAS fails. *)
        iDestruct (bq_chain_lookup_acc _ del_pref_x i_t_x tail1 τ_t v_t
                     Hi_t_x_lookup with "Hchain_x") as "[Hv_x [Hn_x HW_x]]".
        iEval (rewrite Hmark_x Hsucc_x /next_value_of) in "Hn_x".
        wp_cmpxchg_fail.
        iDestruct ("HW_x" with "[$Hv_x Hn_x]") as "Hchain_x".
        { rewrite Hmark_x Hsucc_x /next_value_of. iFrame. }
        iModIntro.
        iSplitL "Hhead_x Htail_x Hchain_x Htrace_x Hauth_op_x Hauth_nm_x
                 Hfrag_nm_x Hauth_dq_x Hfrag_dq_x Hauth_del_x Hauth_calls_x
                 Hauth_no_O_x Hauth_ls_x Hauth_w_x Hfrag_w_x".
        { iNext. iExists nodes_x, del_pref_x, head_val_x, tail_val_x, dummy_loc_x,
            ts_x, s_x, ls_x, op_map_x, node_map_x, dq_map_x, no_O_set_x, witness_map_x.
          iFrame. iPureIntro. split_and!; auto. apply Hno_O_inv_x. apply Hno_O_inv_x. }
        do 2 (wp_pure _).
        iAssert (∃ nx', (nd +ₗ 1) ↦ nx')%I with "[Hnd_n]" as "Hnd_n_ex";
          first by iExists _.
        iSpecialize ("IH" with "Hfrag Hnd_v Hnd_n_ex").
        iExact "IH".
      + (* (true, None): cell [InjRV #()].  CAS fails. *)
        iDestruct (bq_chain_lookup_acc _ del_pref_x i_t_x tail1 τ_t v_t
                     Hi_t_x_lookup with "Hchain_x") as "[Hv_x [Hn_x HW_x]]".
        iEval (rewrite Hmark_x Hsucc_x /next_value_of) in "Hn_x".
        wp_cmpxchg_fail.
        iDestruct ("HW_x" with "[$Hv_x Hn_x]") as "Hchain_x".
        { rewrite Hmark_x Hsucc_x /next_value_of. iFrame. }
        iModIntro.
        iSplitL "Hhead_x Htail_x Hchain_x Htrace_x Hauth_op_x Hauth_nm_x
                 Hfrag_nm_x Hauth_dq_x Hfrag_dq_x Hauth_del_x Hauth_calls_x
                 Hauth_no_O_x Hauth_ls_x Hauth_w_x Hfrag_w_x".
        { iNext. iExists nodes_x, del_pref_x, head_val_x, tail_val_x, dummy_loc_x,
            ts_x, s_x, ls_x, op_map_x, node_map_x, dq_map_x, no_O_set_x, witness_map_x.
          iFrame. iPureIntro. split_and!; auto. apply Hno_O_inv_x. apply Hno_O_inv_x. }
        do 2 (wp_pure _).
        iAssert (∃ nx', (nd +ₗ 1) ↦ nx')%I with "[Hnd_n]" as "Hnd_n_ex";
          first by iExists _.
        iSpecialize ("IH" with "Hfrag Hnd_v Hnd_n_ex").
        iExact "IH".
      + (* (false, Some l_succ_x): cell [InjLV #l_succ_x].  Sub-case
           on whether [l_succ_x = l_succ] (CAS success) or not (fail). *)
        destruct (decide (l_succ_x = l_succ)) as [Heq_succ|Hne_succ].
        * (* CAS success: splice [nd] between [tail1] and [l_succ]. *)
          subst l_succ_x.
          (* Derive [del_pref_x ≤ i_t_x] from [Hmark_x] (cell unmarked). *)
          assert (Hdel_le : (del_pref_x ≤ i_t_x)%nat).
          { rewrite /mark_at in Hmark_x.
            apply bool_decide_eq_false in Hmark_x. lia. }
          (* From [Hsucc_x] derive [nodes_x !! (i_t_x + 1) = Some (l_succ, _, _)]. *)
          rewrite /succ_at in Hsucc_x.
          destruct (nodes_x !! (i_t_x + 1)%nat) as [[[lk_succ_x τ_succ_x] v_succ_x]|]
            eqn:Hnext_x_lookup; last discriminate.
          injection Hsucc_x as ->.
          (* Cross-check via [Hl_succ_frag]: [(τ_succ_x, v_succ_x) = (τ_succ, v_succ)]. *)
          iDestruct (own_valid_2 with "Hauth_nm_x Hl_succ_frag") as %Hsucc_agree_x.
          apply auth_both_valid_discrete in Hsucc_agree_x as [Hsucc_incl_x _].
          apply singleton_included_l in Hsucc_incl_x as (av_s_x & Hav_s_lookup_x & Hav_s_incl_x).
          rewrite /to_nodemap lookup_fmap in Hav_s_lookup_x.
          apply fmap_Some_equiv in Hav_s_lookup_x as (info_s_x & Hnm_s_x_lookup & Hav_s_eq_x).
          rewrite Hav_s_eq_x in Hav_s_incl_x. rewrite Some_included in Hav_s_incl_x.
          assert ((τ_succ, v_succ) = info_s_x :> leibnizO node_info) as Hinfo_s_x_eq.
          { destruct Hav_s_incl_x as [Heq|Hin].
            - by apply (inj to_agree), leibniz_equiv in Heq.
            - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
          rewrite -Hinfo_s_x_eq in Hnm_s_x_lookup.
          clear Hav_s_eq_x Hav_s_incl_x Hinfo_s_x_eq info_s_x.
          (* From the chain at i_t_x + 1 and node_map injectivity,
             (τ_succ_x, v_succ_x) must equal (τ_succ, v_succ). *)
          pose proof (Hnm_chain_x _ _ _ _ Hnext_x_lookup) as Hnm_succ_x.
          rewrite Hnm_s_x_lookup in Hnm_succ_x.
          injection Hnm_succ_x as <- <-.
          (* Freshness of nd vs node_map_x. *)
          iAssert ⌜node_map_x !! nd = None⌝%I as %Hnd_fresh.
          { destruct (node_map_x !! nd) as [[τ_opt' v']|] eqn:Hnd_lk; last done.
            destruct (Hnm_dom_x _ _ _ Hnd_lk) as (j & Hj_lookup).
            iDestruct (big_sepL_lookup _ _ _ _ Hj_lookup with "Hchain_x")
              as "[Hv_j _]".
            simpl. by iDestruct (pointsto_ne with "Hnd_v Hv_j") as %?. }
          (* Split the chain at position i_t_x to get prefix, tail1's
             cell, and suffix. *)
          iDestruct (bq_chain_split_at _ del_pref_x tail1 τ_t v_t i_t_x
                       Hi_t_x_lookup with "Hchain_x") as "(Hpref_x & Hv_x & Hn_x & Hsuf_x)".
          iEval (rewrite /succ_at Hnext_x_lookup Hmark_x /next_value_of /=) in "Hn_x".
          wp_cmpxchg_suc.
          (* === Step A: extract op_map_x !! τ via Hfrag. === *)
          iDestruct (own_valid_2 with "Hauth_op_x Hfrag") as %Hτ_both.
          apply auth_both_valid_discrete in Hτ_both as [Hτ_incl Hτ_valid].
          apply singleton_included_exclusive_l in Hτ_incl; [|apply _|done].
          rewrite lookup_fmap in Hτ_incl.
          apply leibniz_equiv in Hτ_incl.
          apply fmap_Some_1 in Hτ_incl as (info_τ & Hτ_in_op_x & Hinfo_τ).
          destruct info_τ as [kd nd_τ lk]; injection Hinfo_τ as <- <- <-.
          destruct (Henq_clause_x _ _ _ _ Hτ_in_op_x)
            as (Hcp_τ_A1 & Hℓ_τ_PEND & Hτ_pre & _).
          specialize (Hτ_pre eq_refl).
          (* === Step B: γ_op update — linked := true, node := Some nd. === *)
          set (new_τ_info := {| op_info_kind := OpEnq d;
                                op_info_node := Some nd;
                                op_info_linked := true |}).
          iMod (own_update_2 _ _ _
                  (● to_opmap (<[τ := new_τ_info]> op_map_x)
                     ⋅ ◯ {[τ := Excl new_τ_info]})
                  with "Hauth_op_x Hfrag") as "[Hauth_op_x Hfrag]".
          { apply auth_update.
            rewrite /to_opmap fmap_insert.
            apply: singleton_local_update.
            { rewrite lookup_fmap Hτ_in_op_x //. }
            by apply exclusive_local_update. }
          (* === Step C: γ_nm update — allocate fresh entry for nd. === *)
          iMod (own_update_2 _ _ _
                  (● to_nodemap (<[nd := (Some τ, d) : node_info]> node_map_x)
                     ⋅ ◯ to_nodemap (<[nd := (Some τ, d) : node_info]> node_map_x))
                  with "Hauth_nm_x Hfrag_nm_x") as "[Hauth_nm_x Hfrag_nm_x]".
          { apply auth_update.
            rewrite /to_nodemap !fmap_insert.
            apply: alloc_local_update; [|done].
            rewrite lookup_fmap Hnd_fresh //. }
          (* === Step D: re-assemble chain via bq_chain_insert. === *)
          iDestruct (bq_chain_insert nodes_x del_pref_x tail1 τ_t v_t i_t_x
                       l_succ τ_succ v_succ nd (Some τ) d
                       Hdel_le Hi_t_x_lookup Hnext_x_lookup
                       with "[$Hpref_x $Hv_x $Hn_x $Hnd_v $Hnd_n $Hsuf_x]")
            as "Hchain_x".
          set (new_nodes := take (i_t_x + 1)%nat nodes_x
                            ++ [(nd, Some τ, d) : (loc * option positive * val)]
                            ++ drop (i_t_x + 1)%nat nodes_x).
          (* === Step E: close inv with new chain.  Re-establishing
                bq_sim's 16 clauses for middle insertion is analogous
                to phase 6a of refine_enq_cont but with index shifts in
                the suffix.  The chain layout is:
                - positions 0 .. i_t_x:    [take (i_t_x + 1) nodes_x]
                - position  i_t_x + 1:     [(nd, Some τ, d)]
                - positions i_t_x + 2 ..:  [drop (i_t_x + 1) nodes_x]
                  shifted by +1 from the old chain. *)
          assert (Hi_t_x_lt_len : (i_t_x < length nodes_x)%nat)
            by (apply lookup_lt_Some in Hi_t_x_lookup; lia).
          assert (Hi_tp1_lt_len : (i_t_x + 1 < length nodes_x)%nat)
            by (apply lookup_lt_Some in Hnext_x_lookup; lia).
          assert (Hlen_take_x : length (take (i_t_x + 1)%nat nodes_x) = (i_t_x + 1)%nat)
            by (apply length_take_le; lia).
          assert (Hnew_length :
                   length new_nodes = (length nodes_x + 1)%nat).
          { subst new_nodes. rewrite !length_app /= Hlen_take_x length_drop. lia. }
          assert (Hnew_lookup_le : ∀ (i : nat), (i ≤ i_t_x)%nat →
                   new_nodes !! i = nodes_x !! i).
          { intros i Hi. subst new_nodes.
            rewrite lookup_app_l; [|rewrite Hlen_take_x; lia].
            rewrite lookup_take_lt; [done|lia]. }
          assert (Hnew_lookup_t1 :
                    new_nodes !! (i_t_x + 1)%nat = Some (nd, Some τ, d)).
          { subst new_nodes.
            rewrite lookup_app_r; [|rewrite Hlen_take_x; lia].
            rewrite Hlen_take_x.
            replace (i_t_x + 1 - (i_t_x + 1))%nat with 0%nat by lia.
            done. }
          assert (Hnew_lookup_gt : ∀ (i : nat), (i_t_x + 1 ≤ i)%nat →
                   new_nodes !! (i + 1)%nat = nodes_x !! i).
          { intros i Hi. subst new_nodes.
            rewrite lookup_app_r; [|rewrite Hlen_take_x; lia].
            rewrite Hlen_take_x.
            replace (i + 1 - (i_t_x + 1))%nat with (Datatypes.S (i - (i_t_x + 1)))%nat by lia.
            cbn. rewrite lookup_drop. f_equal. lia. }
          (* Inverse direction: every new_nodes lookup decomposes into
             one of three sources. *)
          assert (Hnew_lookup_inv : ∀ (i : nat) lk τ_opt v,
                   new_nodes !! i = Some (lk, τ_opt, v) →
                   ((i ≤ i_t_x)%nat ∧ nodes_x !! i = Some (lk, τ_opt, v)) ∨
                   (i = (i_t_x + 1)%nat ∧ lk = nd ∧ τ_opt = Some τ ∧ v = d) ∨
                   ((i_t_x + 2 ≤ i)%nat
                      ∧ nodes_x !! (i - 1)%nat = Some (lk, τ_opt, v))).
          { intros i lk τ_opt v Hi_lookup.
            destruct (Nat.le_gt_cases i i_t_x) as [Hi_le|Hi_gt].
            - left. split; first done. by rewrite -Hnew_lookup_le.
            - destruct (Nat.eq_dec i (i_t_x + 1)) as [Hi_eq|Hi_ne].
              + right. left.
                rewrite Hi_eq Hnew_lookup_t1 in Hi_lookup.
                injection Hi_lookup as <- <- <-. by (split_and!; auto; lia).
              + right. right.
                assert (i_t_x + 2 ≤ i)%nat by lia. split; first lia.
                rewrite -Hnew_lookup_gt; last lia.
                replace (i - 1 + 1)%nat with i by lia. done. }
          (* Prevent τ from appearing twice in the chain by [chain_op_inv]. *)
          assert (Hτ_not_in_chain : ∀ (i_old : nat) l_old d_old,
                    (1 ≤ i_old)%nat →
                    nodes_x !! i_old = Some (l_old, Some τ, d_old) → False).
          { intros i_old l_old d_old Hpos Hlk.
            pose proof (Hcoi_x _ _ _ _ Hpos Hlk _ Hτ_in_op_x) as Habs.
            discriminate. }
          (* Extract the chain-snapshot witness's pure fact: [snap_τ]
             is in [witness_map_x] at key [(τ, tail1)]. *)
          iDestruct "Hsnap_witness" as (snap_τ) "#Hwit_τ".
          iDestruct (own_valid_2 with "Hauth_w_x Hwit_τ") as %Hwit_valid_x.
          apply auth_both_valid_discrete in Hwit_valid_x as [Hwit_incl_x _].
          apply singleton_included_l in Hwit_incl_x
            as (av_w & Hav_w_lookup & Hav_w_incl).
          rewrite /to_witnessmap lookup_fmap in Hav_w_lookup.
          apply fmap_Some_equiv in Hav_w_lookup
            as (snap_w & Hwit_lookup_x & Hav_w_eq).
          rewrite Hav_w_eq in Hav_w_incl.
          rewrite Some_included in Hav_w_incl.
          assert (snap_τ = snap_w :> leibnizO chain_snapshot)
            as Hsnap_τ_eq.
          { destruct Hav_w_incl as [Heq|Hin].
            - by apply (inj to_agree), leibniz_equiv in Heq.
            - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
          rewrite -Hsnap_τ_eq in Hwit_lookup_x.
          clear Hav_w_eq Hav_w_incl Hsnap_τ_eq snap_w.
          iModIntro.
          iSplitL "Hhead_x Htail_x Hchain_x Htrace_x Hauth_op_x Hauth_nm_x
                   Hfrag_nm_x Hauth_dq_x Hfrag_dq_x Hauth_del_x Hauth_calls_x
                   Hauth_no_O_x Hauth_ls_x Hauth_w_x Hfrag_w_x".
          { iNext.
            iExists new_nodes, del_pref_x, head_val_x, tail_val_x, dummy_loc_x,
              ts_x, s_x, ls_x,
              (<[τ := new_τ_info]> op_map_x),
              (<[nd := (Some τ, d) : node_info]> node_map_x),
              dq_map_x, no_O_set_x.
            iFrame. iPureIntro. split_and!.
            - exact Hsteps_x.
            - exact Hts_eq_x.
            - (* === bq_sim — 16 clauses. === *)
              split_and!; simpl.
              + (* 1: 1 ≤ length new_nodes *) lia.
              + (* 2: del_pref_x < length new_nodes *) lia.
              + (* 3: dom (absq_cp s_x) ⊆ list_to_set ts_x.*1 *)
                exact Hcp_in_ts_x.
              + (* 4: dom op_map ⊆ dom (absq_cp s_x) *)
                rewrite dom_insert_L.
                apply union_least; [|exact Hdomsub_x].
                apply singleton_subseteq_l, elem_of_dom; eauto.
              + (* 5: node_map → chain *)
                intros lk τ_opt v Hlk.
                destruct (decide (lk = nd)) as [->|Hne].
                * rewrite lookup_insert_eq in Hlk.
                  injection Hlk as <- <-.
                  exists (i_t_x + 1)%nat. exact Hnew_lookup_t1.
                * rewrite lookup_insert_ne in Hlk; [|done].
                  destruct (Hnm_dom_x _ _ _ Hlk) as (i & Hi).
                  destruct (Nat.le_gt_cases i i_t_x) as [Hi_le|Hi_gt].
                  -- exists i. by rewrite Hnew_lookup_le.
                  -- exists (i + 1)%nat. rewrite Hnew_lookup_gt; last lia. exact Hi.
              + (* 6: per-enqueue clause *)
                intros τ' d' node' linked' Hop'.
                destruct (decide (τ' = τ)) as [->|Hne].
                * rewrite lookup_insert_eq in Hop'.
                  injection Hop' as <- <- <-.
                  split_and!.
                  ** exact Hcp_τ_A1.
                  ** exact Hℓ_τ_PEND.
                  ** discriminate.
                  ** intros _.
                     exists nd, (i_t_x + 1)%nat.
                     split_and!.
                     *** reflexivity.
                     *** lia.
                     *** exact Hnew_lookup_t1.
                     *** by rewrite lookup_insert_eq.
                     *** split.
                         { intros _. lia. }
                         { intros _. exact Hτ_pre. }
                * rewrite lookup_insert_ne in Hop'; [|done].
                  destruct (Henq_clause_x _ _ _ _ Hop')
                    as (Hcp' & Hℓ' & Hpre' & Hpost').
                  split_and!.
                  ** exact Hcp'.
                  ** exact Hℓ'.
                  ** exact Hpre'.
                  ** intros Hlinked.
                     destruct (Hpost' Hlinked)
                       as (l_old & i_old & Hnode_eq & Hi_pos & Hi_lookup
                            & Hnm_old & Hin_iff).
                     destruct (Nat.le_gt_cases i_old i_t_x) as [Hi_le|Hi_gt].
                     --- exists l_old, i_old.
                         split_and!.
                         +++ exact Hnode_eq.
                         +++ exact Hi_pos.
                         +++ rewrite Hnew_lookup_le; [exact Hi_lookup|lia].
                         +++ destruct (decide (l_old = nd)) as [->|Hne_l].
                             { exfalso. rewrite Hnd_fresh in Hnm_old. discriminate. }
                             rewrite lookup_insert_ne; [exact Hnm_old | done].
                         +++ exact Hin_iff.
                     --- exists l_old, (i_old + 1)%nat.
                         split_and!.
                         +++ exact Hnode_eq.
                         +++ lia.
                         +++ rewrite Hnew_lookup_gt; [exact Hi_lookup|lia].
                         +++ destruct (decide (l_old = nd)) as [->|Hne_l].
                             { exfalso. rewrite Hnd_fresh in Hnm_old. discriminate. }
                             rewrite lookup_insert_ne; [exact Hnm_old | done].
                         +++ rewrite Hin_iff. split; lia.
              + (* 7: per-dequeue clause *)
                intros τ' obs' rng' node' linked' Hop'.
                destruct (decide (τ' = τ)) as [->|Hne].
                * rewrite lookup_insert_eq in Hop'.
                  inversion Hop'.
                * rewrite lookup_insert_ne in Hop'; [|done].
                  exact (Hdeq_clause_x _ _ _ _ _ Hop').
              + (* 8: chain-id injectivity *)
                intros i j l_i l_j τ' d_i d_j Hi_pos Hj_pos Hi_lookup Hj_lookup.
                pose proof Hi_lookup as Hi_inv.
                pose proof Hj_lookup as Hj_inv.
                apply Hnew_lookup_inv in Hi_inv.
                apply Hnew_lookup_inv in Hj_inv.
                destruct Hi_inv as [(Hi_le & Hi_old)
                                  | [(Hi_eq & Hl_eq & Hτ_eq & Hd_eq)
                                  | (Hi_ge & Hi_old)]];
                destruct Hj_inv as [(Hj_le & Hj_old)
                                  | [(Hj_eq & Hl_eq2 & Hτ_eq2 & Hd_eq2)
                                  | (Hj_ge & Hj_old)]].
                * (* le, le *)
                  exact (Hinj_x _ _ _ _ _ _ _ Hi_pos Hj_pos Hi_old Hj_old).
                * (* le, mid: τ' = τ from Hτ_eq2, contradicts Hτ_not_in_chain *)
                  exfalso. injection Hτ_eq2 as ->.
                  exact (Hτ_not_in_chain _ _ _ Hi_pos Hi_old).
                * (* le, ge: Hinj_x gives i = j - 1, contradicts indices *)
                  exfalso.
                  assert (j - 1 ≥ 1)%nat as Hjm1_pos by lia.
                  pose proof (Hinj_x i (j - 1)%nat _ _ _ _ _ Hi_pos Hjm1_pos Hi_old Hj_old).
                  lia.
                * (* mid, le: τ' = τ from Hτ_eq, contradicts Hτ_not_in_chain on j *)
                  exfalso. injection Hτ_eq as ->.
                  exact (Hτ_not_in_chain _ _ _ Hj_pos Hj_old).
                * (* mid, mid *)
                  congruence.
                * (* mid, ge: τ' = τ from Hτ_eq, contradicts Hτ_not_in_chain on (j-1) *)
                  exfalso. injection Hτ_eq as ->.
                  apply (Hτ_not_in_chain (j - 1)%nat l_j d_j); [lia|exact Hj_old].
                * (* ge, le: Hinj_x gives i - 1 = j, contradicts indices *)
                  exfalso.
                  assert (i - 1 ≥ 1)%nat as Him1_pos by lia.
                  pose proof (Hinj_x (i - 1)%nat j _ _ _ _ _ Him1_pos Hj_pos Hi_old Hj_old).
                  lia.
                * (* ge, mid: τ' = τ from Hτ_eq2, contradicts Hτ_not_in_chain on (i-1) *)
                  exfalso. injection Hτ_eq2 as ->.
                  apply (Hτ_not_in_chain (i - 1)%nat l_i d_i); [lia|exact Hi_old].
                * (* ge, ge: Apply Hinj_x to (i-1) and (j-1). *)
                  assert (i - 1 ≥ 1)%nat as Him1_pos by lia.
                  assert (j - 1 ≥ 1)%nat as Hjm1_pos by lia.
                  pose proof (Hinj_x (i - 1)%nat (j - 1)%nat _ _ _ _ _ Him1_pos Hjm1_pos Hi_old Hj_old).
                  lia.
              + (* 9: chain ↔ absq_l correspondence *)
                intros i lk τ' v Hi_pos Hi_lookup.
                pose proof (Hnew_lookup_inv _ _ _ _ Hi_lookup) as Hi_inv.
                destruct Hi_inv as [(Hi_le & Hi_old)
                                  | [(Hi_eq & Hl_eq & Hτ_eq & Hd_eq)
                                  | (Hi_ge & Hi_old)]].
                * destruct (Hcorr_x _ _ _ _ Hi_pos Hi_old)
                    as (Hnm_l & Habs_l & Hin_iff).
                  split_and!.
                  -- destruct (decide (lk = nd)) as [->|Hne_l].
                     { exfalso. rewrite Hnd_fresh in Hnm_l. discriminate. }
                     rewrite lookup_insert_ne; [exact Hnm_l | done].
                  -- exact Habs_l.
                  -- exact Hin_iff.
                * injection Hτ_eq as ->. subst. split_and!.
                  -- by rewrite lookup_insert_eq.
                  -- eexists. exact Hℓ_τ_PEND.
                  -- split.
                     { intros _. lia. }
                     { intros _. exact Hτ_pre. }
                * assert (Hi1 : (1 ≤ i - 1)%nat) by lia.
                  destruct (Hcorr_x (i - 1)%nat _ _ _ Hi1 Hi_old)
                    as (Hnm_l & Habs_l & Hin_iff).
                  split_and!.
                  -- destruct (decide (lk = nd)) as [->|Hne_l].
                     { exfalso. rewrite Hnd_fresh in Hnm_l. discriminate. }
                     rewrite lookup_insert_ne; [exact Hnm_l | done].
                  -- exact Habs_l.
                  -- rewrite Hin_iff. split; lia.
              + (* 10: happens-before respects list order *)
                intros k k_e Hkk.
                destruct (Hlt_pos_x _ _ Hkk)
                  as (p_k & l_k & d_k & Hp_k_pos & Hp_k_lookup & Hp_ke_imp).
                destruct (Nat.le_gt_cases p_k i_t_x) as [Hp_le|Hp_gt].
                * exists p_k, l_k, d_k.
                  split_and!.
                  -- exact Hp_k_pos.
                  -- by rewrite Hnew_lookup_le.
                  -- intros p_ke l_ke d_ke Hp_ke_pos Hnodes_ke.
                     pose proof (Hnew_lookup_inv _ _ _ _ Hnodes_ke) as Hp_ke_inv.
                     destruct Hp_ke_inv as [(Hp_ke_le & Hp_ke_old)
                                          | [(Hp_ke_eq & _ & Hτ_eq2 & _)
                                          | (Hp_ke_ge & Hp_ke_old)]].
                     ++ apply (Hp_ke_imp _ _ _ Hp_ke_pos Hp_ke_old).
                     ++ injection Hτ_eq2 as <-.
                        (* p_k ≤ i_t_x (current case) and p_ke = i_t_x + 1 (the
                           new node), so p_k < p_ke trivially. *)
                        lia.
                     ++ assert (Hp_ke_minus1_pos : (1 ≤ p_ke - 1)%nat) by lia.
                        pose proof (Hp_ke_imp (p_ke - 1)%nat l_ke d_ke
                                     Hp_ke_minus1_pos Hp_ke_old). lia.
                * exists (p_k + 1)%nat, l_k, d_k.
                  split_and!.
                  -- lia.
                  -- rewrite Hnew_lookup_gt; [exact Hp_k_lookup|lia].
                  -- intros p_ke l_ke d_ke Hp_ke_pos Hnodes_ke.
                     pose proof (Hnew_lookup_inv _ _ _ _ Hnodes_ke) as Hp_ke_inv.
                     destruct Hp_ke_inv as [(Hp_ke_le & Hp_ke_old)
                                          | [(Hp_ke_eq & _ & Hτ_eq2 & _)
                                          | (Hp_ke_ge & Hp_ke_old)]].
                     ++ pose proof (Hp_ke_imp _ _ _ Hp_ke_pos Hp_ke_old) as Hcontra. lia.
                     ++ assert (k_e = τ) as Hke_eq by congruence; subst k_e.
                        (* (k, τ) ∈ lt with k linked past tail1 in the
                           current chain, where τ is being spliced at
                           i_t_x + 1.  Use the chain-snapshot witness:
                           at past phase 4, chain was [snap_τ] with
                           tail1 at the chain-end.  By chain_witness_inv,
                           l_k corresponds to a snap_τ position.  By
                           sublist + chain-id injectivity, l_k's current
                           position ≤ tail1's current position = i_t_x,
                           contradicting p_k > i_t_x. *)
                        exfalso.
                        destruct Hwit_x as [_ Hwit_per].
                        destruct (Hwit_per τ tail1 snap_τ Hwit_lookup_x)
                          as (Hsub & Hsnap_len & Hsnap_succ & Hsnap_chain_end & Hsnap_lt).
                        destruct (Hsnap_lt k Hkk)
                          as (i_snap & l_snap & d_snap & Hi_snap_lookup & Hi_snap_pos).
                        destruct Hsnap_chain_end as (τ_t' & v_t' & Hsnap_end).
                        (* Derive NoDup of nodes_x from chain invariants. *)
                        assert (Hnd_nodes : NoDup nodes_x).
                        { apply NoDup_alt. intros i_a i_b [[l_a τ_opt_a] v_a] Hi_a Hi_b.
                          (* Two positions with same triple — show same position. *)
                          destruct τ_opt_a as [τ_some|].
                          - assert (Hi_a_pos : (1 ≤ i_a)%nat).
                            { destruct i_a as [|i_a']; [|lia].
                              rewrite Hdummy_x in Hi_a. inversion Hi_a. }
                            assert (Hi_b_pos : (1 ≤ i_b)%nat).
                            { destruct i_b as [|i_b']; [|lia].
                              rewrite Hdummy_x in Hi_b. inversion Hi_b. }
                            apply (Hinj_x i_a i_b _ _ τ_some _ _
                                     Hi_a_pos Hi_b_pos Hi_a Hi_b).
                          - destruct i_a as [|i_a'].
                            + destruct i_b as [|i_b'].
                              * reflexivity.
                              * assert (Hpos : (1 ≤ Datatypes.S i_b')%nat) by lia.
                                pose proof (Hsome_at_pos_x (Datatypes.S i_b') l_a None v_a
                                              Hpos Hi_b) as (τ_some & Habs).
                                discriminate.
                            + assert (Hpos : (1 ≤ Datatypes.S i_a')%nat) by lia.
                              pose proof (Hsome_at_pos_x (Datatypes.S i_a') l_a None v_a
                                            Hpos Hi_a) as (τ_some & Habs).
                              discriminate. }
                        (* (l_snap, Some k, d_snap) ∈ nodes_x. *)
                        assert (Hsnap_in_nodes : (l_snap, Some k, d_snap) ∈ nodes_x).
                        { apply (sublist_subseteq _ _ Hsub).
                          apply list_elem_of_lookup_2 with i_snap. exact Hi_snap_lookup. }
                        apply list_elem_of_lookup_1 in Hsnap_in_nodes
                          as (p_snap & Hp_snap).
                        (* By Hinj_x: p_snap = p_k. *)
                        assert (Hp_snap_pos : (1 ≤ p_snap)%nat).
                        { destruct p_snap as [|p_snap']; [|lia].
                          rewrite Hdummy_x in Hp_snap. inversion Hp_snap. }
                        assert (Hp_snap_eq : p_snap = p_k).
                        { apply (Hinj_x p_snap p_k _ _ k _ _
                                   Hp_snap_pos Hp_k_pos Hp_snap Hp_k_lookup). }
                        (* (tail1, τ_t', v_t') ∈ nodes_x. *)
                        assert (Htail_in_nodes : (tail1, τ_t', v_t') ∈ nodes_x).
                        { apply (sublist_subseteq _ _ Hsub).
                          apply list_elem_of_lookup_2 with (length snap_τ - 1)%nat.
                          exact Hsnap_end. }
                        apply list_elem_of_lookup_1 in Htail_in_nodes
                          as (p_tail & Hp_tail).
                        (* p_tail = i_t_x: both nodes_x !! _ have location tail1.
                           By Hnm_chain_x, node_map[tail1] = (τ_t', v_t') (from p_tail)
                           AND = (τ_t, v_t) (from i_t_x).  So τ_t' = τ_t. *)
                        pose proof (Hnm_chain_x _ _ _ _ Hp_tail) as Hnm_t1.
                        pose proof (Hnm_chain_x _ _ _ _ Hi_t_x_lookup) as Hnm_t2.
                        rewrite Hnm_t1 in Hnm_t2.
                        injection Hnm_t2 as <- <-.
                        assert (Hp_tail_eq : p_tail = i_t_x).
                        { destruct τ_t' as [τ_t_some|].
                          - assert (Hp_tail_pos : (1 ≤ p_tail)%nat).
                            { destruct p_tail as [|p_tail']; [|lia].
                              rewrite Hdummy_x in Hp_tail. inversion Hp_tail. }
                            assert (Hi_t_x_pos : (1 ≤ i_t_x)%nat).
                            { destruct i_t_x as [|i_t_x']; [|lia].
                              rewrite Hdummy_x in Hi_t_x_lookup. inversion Hi_t_x_lookup. }
                            apply (Hinj_x p_tail i_t_x _ _ τ_t_some _ _
                                     Hp_tail_pos Hi_t_x_pos Hp_tail Hi_t_x_lookup).
                          - (* tail1 = dummy at position 0 *)
                            destruct p_tail as [|p_tail'].
                            + destruct i_t_x as [|i_t_x']; [reflexivity|].
                              assert (Hpos : (1 ≤ Datatypes.S i_t_x')%nat) by lia.
                              pose proof (Hsome_at_pos_x (Datatypes.S i_t_x') tail1 None v_t'
                                            Hpos Hi_t_x_lookup)
                                as (τ_some & Habs). discriminate.
                            + assert (Hpos : (1 ≤ Datatypes.S p_tail')%nat) by lia.
                              pose proof (Hsome_at_pos_x (Datatypes.S p_tail') tail1 None v_t'
                                            Hpos Hp_tail) as (τ_some & Habs).
                              discriminate. }
                        (* Apply NoDup_sublist_lookup_mono. *)
                        assert (Hsnap_len_pos : (i_snap < length snap_τ)%nat).
                        { apply lookup_lt_Some in Hi_snap_lookup. exact Hi_snap_lookup. }
                        assert (Hi_snap_le : (i_snap ≤ length snap_τ - 1)%nat) by lia.
                        pose proof (NoDup_sublist_lookup_mono _ _ Hnd_nodes Hsub
                                      i_snap (length snap_τ - 1)%nat _ _
                                      p_snap p_tail
                                      Hi_snap_lookup Hsnap_end Hi_snap_le
                                      Hp_snap Hp_tail) as Hp_le.
                        lia.
                     ++ assert (Hp_ke_minus1_pos : (1 ≤ p_ke - 1)%nat) by lia.
                        pose proof (Hp_ke_imp (p_ke - 1)%nat l_ke d_ke
                                     Hp_ke_minus1_pos Hp_ke_old). lia.
              + (* 11: TBD *) done.
              + (* 12: COMP enqueues are linked *)
                intros τ' d' Hℓ_τ'.
                destruct (Hcomp_link_x _ _ Hℓ_τ') as (p & l_p & Hp_pos & Hp_lookup).
                destruct (Nat.le_gt_cases p i_t_x) as [Hp_le|Hp_gt].
                * exists p, l_p. split.
                  -- exact Hp_pos.
                  -- by rewrite Hnew_lookup_le.
                * exists (p + 1)%nat, l_p. split.
                  -- lia.
                  -- rewrite Hnew_lookup_gt; [exact Hp_lookup|lia].
              + (* 13: tail_loc names a chain position *)
                destruct Htail_in_x as (i_tail & τ_tail & v_tail & Hi_tail_lt & Htail_at).
                destruct (Nat.le_gt_cases i_tail i_t_x) as [Hi_le|Hi_gt].
                * exists i_tail, τ_tail, v_tail. split.
                  -- lia.
                  -- by rewrite Hnew_lookup_le.
                * exists (i_tail + 1)%nat, τ_tail, v_tail. split.
                  -- lia.
                  -- rewrite Hnew_lookup_gt; [exact Htail_at|lia].
              + (* 14: head_loc *)
                destruct Hhead_in_x as (i_h & τ_h & v_h & Hi_h_le & Hhead_at).
                (* head's position in old chain ≤ del_pref_x.  del_pref_x ≤ i_t_x,
                   so head's position is ≤ i_t_x.  No shift needed. *)
                exists i_h, τ_h, v_h. split.
                * exact Hi_h_le.
                * rewrite Hnew_lookup_le; [exact Hhead_at|lia].
              + (* 15: chain → node_map *)
                intros i lk τ_opt v Hi.
                pose proof (Hnew_lookup_inv _ _ _ _ Hi) as Hi_inv.
                destruct Hi_inv as [(Hi_le & Hi_old)
                                  | [(Hi_eq & Hl_eq & Hτ_eq & Hd_eq)
                                  | (Hi_ge & Hi_old)]].
                * pose proof (Hnm_chain_x _ _ _ _ Hi_old) as Hnm_l.
                  destruct (decide (lk = nd)) as [->|Hne_l].
                  -- exfalso. rewrite Hnd_fresh in Hnm_l. discriminate.
                  -- rewrite lookup_insert_ne; [exact Hnm_l | done].
                * subst. by rewrite lookup_insert_eq.
                * pose proof (Hnm_chain_x _ _ _ _ Hi_old) as Hnm_l.
                  destruct (decide (lk = nd)) as [->|Hne_l].
                  -- exfalso. rewrite Hnd_fresh in Hnm_l. discriminate.
                  -- rewrite lookup_insert_ne; [exact Hnm_l | done].
              + (* 16: non-dummy positions carry Some τ *)
                intros i lk τ_opt v Hi_pos Hi_lookup.
                pose proof (Hnew_lookup_inv _ _ _ _ Hi_lookup) as Hi_inv.
                destruct Hi_inv as [(Hi_le & Hi_old)
                                  | [(Hi_eq & Hl_eq & Hτ_eq & Hd_eq)
                                  | (Hi_ge & Hi_old)]].
                * apply (Hsome_at_pos_x _ _ _ _ Hi_pos Hi_old).
                * subst. by exists τ.
                * assert (1 ≤ i - 1)%nat as Him1_pos by lia.
                  apply (Hsome_at_pos_x (i - 1)%nat _ _ _ Him1_pos Hi_old).
            - (* dummy lookup *)
              rewrite Hnew_lookup_le; [exact Hdummy_x|lia].
            - (* node_val_inv *)
              split.
              + intros lk τ' d' Hlk.
                destruct (decide (lk = nd)) as [->|Hne].
                * rewrite lookup_insert_eq in Hlk.
                  injection Hlk as <- <-.
                  exists PEND. exact Hℓ_τ_PEND.
                * rewrite lookup_insert_ne in Hlk; [|done].
                  apply (proj1 Hnvi_x _ _ _ Hlk).
              + intros l₁ l₂ τ' d₁ d₂ Hlk₁ Hlk₂.
                destruct (decide (l₁ = nd)) as [Hl₁_eq|Hne₁];
                destruct (decide (l₂ = nd)) as [Hl₂_eq|Hne₂].
                * by rewrite Hl₁_eq Hl₂_eq.
                * subst l₁. rewrite lookup_insert_eq in Hlk₁.
                  injection Hlk₁ as <- <-.
                  rewrite lookup_insert_ne in Hlk₂; [|done].
                  exfalso.
                  destruct (Hnm_dom_x _ _ _ Hlk₂) as (j & Hj_lookup).
                  destruct j as [|j'].
                  -- rewrite Hdummy_x in Hj_lookup. injection Hj_lookup as ? ? ?.
                     discriminate.
                  -- eapply (Hτ_not_in_chain (Datatypes.S j')); [lia|exact Hj_lookup].
                * subst l₂. rewrite lookup_insert_eq in Hlk₂.
                  injection Hlk₂ as <- <-.
                  rewrite lookup_insert_ne in Hlk₁; [|done].
                  exfalso.
                  destruct (Hnm_dom_x _ _ _ Hlk₁) as (j & Hj_lookup).
                  destruct j as [|j'].
                  -- rewrite Hdummy_x in Hj_lookup. injection Hj_lookup as ? ? ?.
                     discriminate.
                  -- eapply (Hτ_not_in_chain (Datatypes.S j')); [lia|exact Hj_lookup].
                * rewrite lookup_insert_ne in Hlk₁; [|done].
                  rewrite lookup_insert_ne in Hlk₂; [|done].
                  apply (proj2 Hnvi_x _ _ _ _ _ Hlk₁ Hlk₂).
            - exact Hdqi_x.
            - apply Hno_O_inv_x.
            - apply Hno_O_inv_x.
            - (* chain_op_inv for new_nodes / new_op_map *)
              intros i lk τ' v Hpos Hlk info Hop_lk.
              pose proof (Hnew_lookup_inv _ _ _ _ Hlk) as Hi_inv.
              destruct Hi_inv as [(Hi_le & Hi_old)
                                | [(Hi_eq & Hl_eq & Hτ_eq & Hd_eq)
                                | (Hi_ge & Hi_old)]].
              + destruct (decide (τ' = τ)) as [->|Hne_τ].
                * exfalso. exact (Hτ_not_in_chain _ _ _ Hpos Hi_old).
                * rewrite lookup_insert_ne in Hop_lk; [|done].
                  exact (Hcoi_x _ _ _ _ Hpos Hi_old _ Hop_lk).
              + injection Hτ_eq as ->. subst. rewrite lookup_insert_eq in Hop_lk.
                injection Hop_lk as <-. reflexivity.
              + destruct (decide (τ' = τ)) as [->|Hne_τ].
                * exfalso.
                  apply (Hτ_not_in_chain (i - 1)%nat lk v); [lia|exact Hi_old].
                * rewrite lookup_insert_ne in Hop_lk; [|done].
                  assert (Hi1 : (1 ≤ i - 1)%nat) by lia.
                  exact (Hcoi_x (i - 1)%nat _ _ _ Hi1 Hi_old _ Hop_lk).
            - (* chain_witness_inv: splice extends chain via insertion at
                 position i_t_x + 1; existing snaps stay sublists.  τ
                 is now linked, but witness_map's invariant is over τ's
                 still-pending status — for τ specifically, we check if
                 τ ∈ dom witness_map and reason from there.  cp unchanged. *)
              destruct Hwit_x as [Hwit_dom Hwit_per].
              split.
              { simpl. exact Hwit_dom. }
              intros τ_w tail_loc_w snap Hwit_lookup.
              destruct (Hwit_per τ_w tail_loc_w snap Hwit_lookup)
                as (Hsub & Hlen_w & Hsucc_w & Hsnap_end_w & Hlt_in_w).
              split_and!; [|exact Hlen_w|exact Hsucc_w|exact Hsnap_end_w|].
              { (* sublist preserved by insertion at position i_t_x + 1 *)
                subst new_nodes.
                pose proof (sublist_insert_at snap nodes_x (i_t_x + 1)%nat
                              (nd, Some τ, d) Hsub) as Hres.
                exact Hres. }
              intros k Hkin.
              by apply Hlt_in_w. }
          (* WP continuation: CmpXchg returned (InjLV #l_succ, #true).
             Snd reduces to #true, then if #true reduces to #true. *)
          wp_pures.
          iModIntro. iLeft. iFrame. done.
        * (* CAS fail: l_succ_x ≠ l_succ.  Cell [InjLV #l_succ_x]
             differs from [InjLV #l_succ]. *)
          iDestruct (bq_chain_lookup_acc _ del_pref_x i_t_x tail1 τ_t v_t
                       Hi_t_x_lookup with "Hchain_x") as "[Hv_x [Hn_x HW_x]]".
          iEval (rewrite Hmark_x Hsucc_x /next_value_of) in "Hn_x".
          assert (Hne_v : InjLV #l_succ_x ≠ InjLV #l_succ).
          { intros [= ->]. by apply Hne_succ. }
          wp_cmpxchg_fail.
          iDestruct ("HW_x" with "[$Hv_x Hn_x]") as "Hchain_x".
          { rewrite Hmark_x Hsucc_x /next_value_of. iFrame. }
          iModIntro.
          iSplitL "Hhead_x Htail_x Hchain_x Htrace_x Hauth_op_x Hauth_nm_x
                   Hfrag_nm_x Hauth_dq_x Hfrag_dq_x Hauth_del_x Hauth_calls_x
                   Hauth_no_O_x Hauth_ls_x Hauth_w_x Hfrag_w_x".
          { iNext. iExists nodes_x, del_pref_x, head_val_x, tail_val_x, dummy_loc_x,
              ts_x, s_x, ls_x, op_map_x, node_map_x, dq_map_x, no_O_set_x, witness_map_x.
            iFrame. iPureIntro. split_and!; auto. apply Hno_O_inv_x. apply Hno_O_inv_x. }
          do 2 (wp_pure _).
          iAssert (∃ nx', (nd +ₗ 1) ↦ nx')%I with "[Hnd_n]" as "Hnd_n_ex";
            first by iExists _.
          iSpecialize ("IH" with "Hfrag Hnd_v Hnd_n_ex").
          iExact "IH".
      + (* (false, None): cell [InjLV #()].  CAS fails (loc ≠ unit). *)
        iDestruct (bq_chain_lookup_acc _ del_pref_x i_t_x tail1 τ_t v_t
                     Hi_t_x_lookup with "Hchain_x") as "[Hv_x [Hn_x HW_x]]".
        iEval (rewrite Hmark_x Hsucc_x /next_value_of) in "Hn_x".
        wp_cmpxchg_fail.
        iDestruct ("HW_x" with "[$Hv_x Hn_x]") as "Hchain_x".
        { rewrite Hmark_x Hsucc_x /next_value_of. iFrame. }
        iModIntro.
        iSplitL "Hhead_x Htail_x Hchain_x Htrace_x Hauth_op_x Hauth_nm_x
                 Hfrag_nm_x Hauth_dq_x Hfrag_dq_x Hauth_del_x Hauth_calls_x
                 Hauth_no_O_x Hauth_ls_x Hauth_w_x Hfrag_w_x".
        { iNext. iExists nodes_x, del_pref_x, head_val_x, tail_val_x, dummy_loc_x,
            ts_x, s_x, ls_x, op_map_x, node_map_x, dq_map_x, no_O_set_x, witness_map_x.
          iFrame. iPureIntro. split_and!; auto. apply Hno_O_inv_x. apply Hno_O_inv_x. }
        do 2 (wp_pure _).
        iAssert (∃ nx', (nd +ₗ 1) ↦ nx')%I with "[Hnd_n]" as "Hnd_n_ex";
          first by iExists _.
        iSpecialize ("IH" with "Hfrag Hnd_v Hnd_n_ex").
        iExact "IH".
    - (* (false, None): InjLV #().  Match enters InjL with p = #(),
         so if p = #() is true, taking the then branch — return
         #false (basket has dissolved).  *)
      wp_pures.
      iModIntro. iRight. iFrame "Hfrag Hnd_v". iSplit; first done.
      by iExists _.
  Qed.

End bq_skeleton_enq_basket.
