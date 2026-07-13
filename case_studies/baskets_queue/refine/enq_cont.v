(* refine_enq_cont.v: proof of [op_spec_enq_cont] — the enqueue
  branch of [op_spec] for the Baskets Queue.

  ** What this lemma will eventually prove.
  Given a thread holding the [op_info] fragment for a fresh
  [OpEnq d] identifier [τ], the WP runs the impl-level [enqueue]
  body and then [trace_emit]s the enqueue's [Ret]; in the abstract
  model the lemma must commit:
    - allocation of [nd], registering its location into [op_info_node];
    - the splice CAS at the current [tail.next], which transitions [τ]
      from pre-link to post-link without changing AbsQ — the LP of the
      enqueue is *not* fired here.  The enqueue stays at control point
      [A1] with [absq_l τ = (d, PEND)].
    - the [trace_emit] of [Ret #()], which advances [τ] to [A2] via
      either [absq_step_ret_enq1] (if [τ] is still in [absq_O]) or
      [absq_step_ret_enq2] (if a concurrent dequeue has already
      removed [τ] from [absq_O] via the matching mark CAS).

  The basket-internal *FIFO* order between [τ] and other in-list
  enqueues is *not* fixed at any point in this WP; it is fixed
  later, when the matching dequeue's mark CAS fires (see
  [refine_deq_cont.v]).

  The proof phases:
    (1) alloc + initial-store of [new_node];
    (2) outer-loop entry (via [iLöb]);
    (3) load of [tail];
    (4) load of [tail.next] via [bq_chain_lookup_acc];
    (5) consistency check + match dispatch;
    (6) direct-branch mark CAS;
    (7) best-effort [tail] advance;
    (8) [trace_emit] RET-ENQ commit (factored into
        [op_spec_enq_trace_emit]).
  The basket branch dispatches to [op_spec_enq_basket]. *)

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

From case_studies.baskets_queue Require Import impl refine.defs refine.enq_trace
                                                refine.enq_basket.

Section bq_skeleton_enq_cont.
  Context `{!traceG Σ, !bqG Σ}.

  Local Notation valid_value := bq_valid_value.
  Local Notation Nbq := Nbq.
  Local Notation bq_inv_body := bq_inv_body.
  Local Notation is_bq := is_bq.

  Lemma op_spec_enq_cont
    `{!heapGS Σ} (γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w : gname) (l head tail : loc)
    (τ : positive) (d : val) (Φ : val → iProp Σ) :
    valid_value d →
    val_is_unboxed (SOMEV d) →
    inv Nbq (bq_inv_body γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w head tail l) -∗
    trace_inv l (I_lang_bq) -∗
    own γ (◯ {[τ := Excl {| op_info_kind := OpEnq d;
                            op_info_node := None;
                            op_info_linked := false |}]}) -∗
    (∀ v : val, True -∗ Φ v) -∗
    WP (let: "τ" := #(Z.pos τ) in
        let: "res" := op (#head, #tail)%V (SOMEV d) in
        trace_emit #l "τ" (InjR "res");; "res")
    {{ Φ }}.
  Proof.
    intros Hd_valid Hd_unboxed.
    iIntros "#Hinv #Htrace_inv Hfrag HΦ".
    (* Phase 1: unfold the dispatcher and the enqueue's prelude.  This
       is purely structural — no invariant interaction yet.  After this
       block we hold:
         - [nd] : a freshly-allocated 2-cell node;
         - [Hnd_v] : [nd ↦ d] (value cell);
         - [Hnd_n] : [(nd +ₗ 1) ↦ InjLV #()] (next cell, unmarked-null);
         - [Hfrag] : the [op_info] fragment for [τ], still pre-link. *)
    wp_pures.
    rewrite /op. wp_pures.
    rewrite /enqueue. wp_pures.
    rewrite /new_node. wp_pures.
    wp_alloc nd as "Hnd"; first lia.
    rewrite array_cons array_cons array_nil.
    iDestruct "Hnd" as "(Hnd_v & Hnd_n & _)".
    wp_pures.
    wp_store. wp_pures.
    wp_store. wp_pures.

    (* Phase 2: outer loop.  We use [iLöb] to obtain the IH for the
       recursive calls in the non-direct branches.  Within the loop's
       body the proof shape is:
         - load [tail]   (atomic, uses inv);
         - load [tail.next]  (atomic, uses inv + clause 13);
         - re-load [tail] for consistency  (atomic);
         - dispatch on [next]:
             * [InjL #()]  → direct-CAS branch (target of this proof);
             * [InjL #p] with [p ≠ #()]  → tail-lagging help, recurse;
             * [InjR _]    → stale tail, recurse.
       At the direct-CAS branch we additionally:
         - store [InjLV #()] at [nd]'s next (this is no-op semantically
           because the alloc already wrote it, but the impl repeats it);
         - CAS [tail.next] from [InjLV #()] to [InjLV #nd];
         - on success, advance [tail] best-effort (CAS [tail tail1 nd])
           and break out of the loop with [#()];
         - on failure, dispatch into [enq_basket].  *)
    (* Wrap [Hnd_n] as an existential before [iLöb] so that the IH
       accepts arbitrary contents at [(nd +ₗ 1)].  The basket helper's
       inner CAS-fail recursion overwrites [(nd +ₗ 1)] without ever
       restoring [InjLV #()], so the OUTER iLöb IH must accept the
       weaker shape [∃ nx, (nd +ₗ 1) ↦ nx] and the body destructures
       it (re-store sites overwrite the value regardless). *)
    iAssert (∃ nx, (nd +ₗ 1) ↦ nx)%I with "[Hnd_n]" as "Hnd_n_ex";
      first by iExists _.
    iLöb as "IH".
    iDestruct "Hnd_n_ex" as (nx) "Hnd_n".
    wp_pures.

    (* Phase 3: load [tail].  No AbsQ step; the inv is closed
       unchanged.  We additionally extract a persistent [node_map]
       fragment for [tail_val]'s identifier and value so that phase 4's
       chain-position lookup at the next inv-open finds the same entry. *)
    wp_bind (! _)%E.
    iInv Nbq as (nodes del_pref head_val tail_val dummy_loc ts s ls op_map node_map dq_map no_O_set witness_map)
      "(>Hhead & >Htail & Hchain & >Htrace & >Hauth_op & >Hauth_nm & Hfrag_nm
        & >Hauth_dq & Hfrag_dq & >Hauth_del & >Hauth_calls & >Hauth_no_O & >Hauth_ls & >Hauth_w & Hfrag_w
        & >%Hsteps & >%Hts_eq & >%Hsim & >%Hdummy & >%Hnvi & >%Hdqi & >%Hno_O_inv & >%Hcoi & >%Hwit)".
    wp_load.
    pose proof Hsim as (Hlen & Hdel & Hcp_in_ts & Hdomsub & Hnm_dom & Henq_clause
                       & Hdeq_clause & Hinj & Hcorr & Hlt_pos & _Htbd & Hcomp_link
                       & Htail_in & Hhead_in & Hnm_chain & Hsome_at_pos).
    destruct Htail_in as (i_t & τ_t_opt & v_t & Hi_t_lt & Htail_at).
    pose proof (Hnm_chain _ _ _ _ Htail_at) as Hnm_tail.
    (* Persistent [node_map] fragment for [tail_val]. *)
    iDestruct (own_mono _ _ (◯ {[tail_val := to_agree ((τ_t_opt, v_t) : leibnizO node_info)]})
                with "Hfrag_nm") as "#Htail_frag".
    { apply auth_frag_mono. rewrite /to_nodemap.
      apply (proj2 (singleton_included_l _ _ _)).
      exists (to_agree ((τ_t_opt, v_t) : leibnizO node_info)). split.
      - rewrite lookup_fmap Hnm_tail //=.
      - reflexivity. }
    iModIntro.
    iSplitL "Hhead Htail Hchain Htrace Hauth_op Hauth_nm Hfrag_nm Hauth_dq Hfrag_dq Hauth_del Hauth_calls Hauth_no_O Hauth_ls Hauth_w Hfrag_w".
    { iNext. iExists nodes, del_pref, head_val, tail_val, dummy_loc, ts, s, ls, op_map, node_map, dq_map, no_O_set, witness_map.
      by iFrame. }
    wp_pures.

    (* PHASE 4: load [tail_val.next].  Open the inv, find [tail_val]'s
       chain_4 position via [Htail_frag], extract the next-cell via
       [bq_chain_lookup_acc], [wp_load], close inv unchanged. *)
    wp_bind (! _)%E.
    iInv Nbq as (nodes_4 del_pref_4 head_val_4 tail_val_4 dummy_loc_4 ts_4 s_4 ls_4
                 op_map_4 node_map_4 dq_map_4 no_O_set_4 witness_map_4)
      "(>Hhead4 & >Htail4 & Hchain4 & >Htrace4 & >Hauth_op4 & >Hauth_nm4 & Hfrag_nm4
        & >Hauth_dq4 & Hfrag_dq4 & >Hauth_del4 & >Hauth_calls4 & >Hauth_no_O4 & >Hauth_ls4 & >Hauth_w4 & Hfrag_w4
        & >%Hsteps4 & >%Hts_eq4 & >%Hsim4 & >%Hdummy4 & >%Hnvi4 & >%Hdqi4 & >%Hno_O_inv4 & >%Hcoi4 & >%Hwit4)".
    (* Use [Htail_frag] to find [tail_val] in chain_4. *)
    iDestruct (own_valid_2 with "Hauth_nm4 Htail_frag") as %Hnm_agree_4.
    apply auth_both_valid_discrete in Hnm_agree_4 as [Hincl_4 _].
    apply singleton_included_l in Hincl_4 as (av_4 & Hav_lookup_4 & Hav_incl_4).
    rewrite /to_nodemap lookup_fmap in Hav_lookup_4.
    apply fmap_Some_equiv in Hav_lookup_4 as (info_4 & Hnm4_lookup & Hav_eq_4).
    rewrite Hav_eq_4 in Hav_incl_4. rewrite Some_included in Hav_incl_4.
    assert ((τ_t_opt, v_t) = info_4 :> leibnizO node_info) as Hinfo_4_eq.
    { destruct Hav_incl_4 as [Heq|Hin].
      - by apply (inj to_agree), leibniz_equiv in Heq.
      - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
    rewrite -Hinfo_4_eq in Hnm4_lookup. clear Hav_eq_4 Hav_incl_4 Hinfo_4_eq info_4.
    pose proof Hsim4 as (Hlen4 & Hdel4 & _ & _ & Hnm_dom4 & _ & _ & _ & _ & _ & _
                       & _ & _ & _ & Hnm_chain4 & _).
    destruct (Hnm_dom4 _ _ _ Hnm4_lookup) as (i_t_4 & Hi_t_4_lookup).
    iDestruct (bq_chain_lookup_acc _ del_pref_4 i_t_4 tail_val τ_t_opt v_t Hi_t_4_lookup
                with "Hchain4") as "[Hv4 [Hn4 HW4]]".
    wp_load.
    iDestruct ("HW4" with "[$Hv4 $Hn4]") as "Hchain4".
    (* Persistent [γ_nm] witness: from any chain lookup at phase 4, get
       the persistent fragment.  Used by the (false, Some) tail-lagging
       branch in phase 6 to re-locate [l_succ_4] in the chain after the
       inv has been closed and re-opened. *)
    iAssert (∀ lk τ_opt v,
              ⌜nodes_4 !! (i_t_4 + 1)%nat = Some (lk, τ_opt, v)⌝ -∗
              own γ_nm (◯ {[lk := to_agree
                ((τ_opt, v) : leibnizO node_info)]}))%I
      as "#Hsucc_lookup_to_frag".
    { iIntros (lk τ_opt v) "%Hlookup".
      pose proof (Hnm_chain4 _ _ _ _ Hlookup) as Hnm_l_succ.
      iApply (own_mono with "Hfrag_nm4").
      apply auth_frag_mono. rewrite /to_nodemap.
      apply (proj2 (singleton_included_l _ _ _)).
      exists (to_agree ((τ_opt, v) : leibnizO node_info)). split.
      - rewrite lookup_fmap Hnm_l_succ //=.
      - reflexivity. }
    (* Derive [op_map_4 !! τ = Some _] unconditionally; needed both
       to discharge the [chain_witness_inv] domain clause in the
       [None] branch's mint case and to verify [τ ∈ dom op_map_4]. *)
    iDestruct (own_valid_2 with "Hauth_op4 Hfrag") as %Hτ_both4.
    apply auth_both_valid_discrete in Hτ_both4 as [Hτ_incl4 Hτ_valid4].
    apply singleton_included_exclusive_l in Hτ_incl4; [|apply _|done].
    rewrite lookup_fmap in Hτ_incl4.
    apply leibniz_equiv in Hτ_incl4.
    apply fmap_Some_1 in Hτ_incl4 as (info_τ4 & Hτ_in_op4 & _).

    (* Outer dispatch on [succ_at_4]: the chain-snapshot witness mint
       is gated on [succ_at nodes_4 i_t_4 = None], because the
       [chain_witness_inv] lt-edges clause requires it.  Freshness in
       the [None] branch is closed by extract-or-mint (use the
       existing fragment if [(τ, tail_val)] is already in
       [witness_map_4]).  In the [Some] branch no mint is needed: the
       (false, None) post-phase-5 sub-case (the only one that calls
       into [enq_basket]) is unreachable, since [next_value_of (mark)
       (Some _)] has [Some _] which never matches [InjLV #()]. *)
    destruct (succ_at nodes_4 i_t_4) as [l_succ_4_at_4|] eqn:Hsucc_4_eqn.

    - (* succ_at_4 = Some l_succ_4_at_4: skip the mint.  Derive
         [l_succ_4_at_4]'s persistent γ_nm fragment for the
         tail-lagging branch, then close inv unchanged. *)
      assert (Hnext_lookup_4 :
                ∃ τ_succ_4 v_succ_4,
                  nodes_4 !! (i_t_4 + 1)%nat = Some (l_succ_4_at_4, τ_succ_4, v_succ_4)).
      { rewrite /succ_at in Hsucc_4_eqn.
        destruct (nodes_4 !! (i_t_4 + 1)%nat) as [[[lk τ'] v']|] eqn:Hlk;
          last discriminate.
        simpl in Hsucc_4_eqn. injection Hsucc_4_eqn as ->.
        eauto. }
      destruct Hnext_lookup_4 as (τ_succ_4 & v_succ_4 & Hnext_lookup_4).
      iAssert (own γ_nm (◯ {[l_succ_4_at_4 := to_agree
                ((τ_succ_4, v_succ_4) : leibnizO node_info)]}))%I
        as "#Hl_succ_frag".
      { iApply "Hsucc_lookup_to_frag". iPureIntro. exact Hnext_lookup_4. }
      iModIntro.
      iSplitL "Hhead4 Htail4 Hchain4 Htrace4 Hauth_op4 Hauth_nm4 Hfrag_nm4 Hauth_dq4 Hfrag_dq4 Hauth_del4 Hauth_calls4 Hauth_no_O4 Hauth_ls4 Hauth_w4 Hfrag_w4".
      { iNext. iExists nodes_4, del_pref_4, head_val_4, tail_val_4, dummy_loc_4, ts_4, s_4, ls_4,
          op_map_4, node_map_4, dq_map_4, no_O_set_4, witness_map_4.
        by iFrame. }
      wp_pures.

      (* PHASE 5 (succ_at_4 = Some): consistency check + 2-way mark
         dispatch.  Inner (mark = false) takes the tail-lagging
         branch via CAS [tail tail_val l_succ_4_at_4]; (mark = true)
         recurses via IH. *)
      wp_bind (! _)%E.
      iInv Nbq as (nodes_5 del_pref_5 head_val_5 tail_val_5 dummy_loc_5 ts_5 s_5 ls_5
                   op_map_5 node_map_5 dq_map_5 no_O_set_5 witness_map_5)
        "(>Hhead5 & >Htail5 & Hchain5 & >Htrace5 & >Hauth_op5 & >Hauth_nm5 & Hfrag_nm5
          & >Hauth_dq5 & Hfrag_dq5 & >Hauth_del5 & >Hauth_calls5 & >Hauth_no_O5 & >Hauth_ls5 & >Hauth_w5 & Hfrag_w5
          & >%Hsteps5 & >%Hts_eq5 & >%Hsim5 & >%Hdummy5 & >%Hnvi5 & >%Hdqi5 & >%Hno_O_inv5 & >%Hcoi5 & >%Hwit5)".
      wp_load.
      iModIntro.
      iSplitL "Hhead5 Htail5 Hchain5 Htrace5 Hauth_op5 Hauth_nm5 Hfrag_nm5 Hauth_dq5 Hfrag_dq5 Hauth_del5 Hauth_calls5 Hauth_no_O5 Hauth_ls5 Hauth_w5 Hfrag_w5".
      { iNext. iExists nodes_5, del_pref_5, head_val_5, tail_val_5, dummy_loc_5, ts_5, s_5, ls_5,
          op_map_5, node_map_5, dq_map_5, no_O_set_5, witness_map_5.
        by iFrame. }
      wp_op. case_bool_decide as Hcmp.
      + (* tail_val_5 = tail_val: dispatch on mark only. *)
        assert (tail_val_5 = tail_val) as -> by congruence.
        wp_pures.
        rewrite /next_value_of.
        destruct (mark_at del_pref_4 i_t_4) eqn:Hmark_4.
        * (* mark = true: marked-pointer, recurse via IH. *)
          wp_pures.
          iApply ("IH" with "Hfrag HΦ Hnd_v [Hnd_n]"); first by iExists _.
        * (* mark = false: tail-lagging — CAS [tail tail_val
             l_succ_4_at_4] then recurse via IH. *)
          wp_pures.
          wp_bind (CmpXchg _ _ _).
          iInv Nbq as (nodes_x del_pref_x head_val_x tail_val_x dummy_loc_x ts_x s_x ls_x
                       op_map_x node_map_x dq_map_x no_O_set_x witness_map_x)
            "(>Hhead_x & >Htail_x & >Hchain_x & >Htrace_x & >Hauth_op_x & >Hauth_nm_x
              & Hfrag_nm_x & >Hauth_dq_x & Hfrag_dq_x & >Hauth_del_x & >Hauth_calls_x
              & >Hauth_no_O_x & >Hauth_ls_x & >Hauth_w_x & Hfrag_w_x & >%Hsteps_x & >%Hts_eq_x & >%Hsim_x
              & >%Hdummy_x & >%Hnvi_x & >%Hdqi_x & >%Hno_O_inv_x & >%Hcoi_x & >%Hwit_x)".
          destruct (decide (tail_val_x = tail_val)) as [Heq_t|Hne_t].
          ** (* CAS success: tail advances to l_succ_4_at_4. *)
             subst tail_val_x.
             wp_cmpxchg_suc.
             iDestruct (own_valid_2 with "Hauth_nm_x Hl_succ_frag") as %Hagree_x.
             apply auth_both_valid_discrete in Hagree_x as [Hincl_x _].
             apply singleton_included_l in Hincl_x as (av_x & Hav_lookup_x & Hav_incl_x).
             rewrite /to_nodemap lookup_fmap in Hav_lookup_x.
             apply fmap_Some_equiv in Hav_lookup_x as (info_x & Hnm_x_lookup & Hav_eq_x).
             rewrite Hav_eq_x in Hav_incl_x. rewrite Some_included in Hav_incl_x.
             assert ((τ_succ_4, v_succ_4) = info_x :> leibnizO node_info)
               as Hinfo_x_eq.
             { destruct Hav_incl_x as [Heq|Hin].
               - by apply (inj to_agree), leibniz_equiv in Heq.
               - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
             rewrite -Hinfo_x_eq in Hnm_x_lookup.
             clear Hav_eq_x Hav_incl_x Hinfo_x_eq info_x.
             pose proof Hsim_x as (Hlen_x & Hdel_x & Hcp_in_ts_x & Hdomsub_x & Hnm_dom_x
                                   & Henq_clause_x & Hdeq_clause_x & Hinj_x & Hcorr_x
                                   & Hlt_pos_x & _Htbd_x & Hcomp_link_x & _ & Hhead_in_x
                                   & Hnm_chain_x & Hsome_at_pos_x).
             destruct (Hnm_dom_x _ _ _ Hnm_x_lookup) as (i_succ_x & Hi_succ_x_lookup).
             iModIntro.
             iSplitL "Hhead_x Htail_x Hchain_x Htrace_x Hauth_op_x Hauth_nm_x
                      Hfrag_nm_x Hauth_dq_x Hfrag_dq_x Hauth_del_x Hauth_calls_x
                      Hauth_no_O_x Hauth_ls_x Hauth_w_x Hfrag_w_x".
             { iNext.
               iExists nodes_x, del_pref_x, head_val_x, l_succ_4_at_4, dummy_loc_x,
                 ts_x, s_x, ls_x, op_map_x, node_map_x, dq_map_x, no_O_set_x, witness_map_x.
               iFrame. iPureIntro. split_and!.
               - exact Hsteps_x.
               - exact Hts_eq_x.
               - split_and!.
                 + exact Hlen_x.
                 + exact Hdel_x.
                 + exact Hcp_in_ts_x.
                 + exact Hdomsub_x.
                 + exact Hnm_dom_x.
                 + exact Henq_clause_x.
                 + exact Hdeq_clause_x.
                 + exact Hinj_x.
                 + exact Hcorr_x.
                 + exact Hlt_pos_x.
                 + exact _Htbd_x.
                 + exact Hcomp_link_x.
                 + exists i_succ_x, τ_succ_4, v_succ_4. split.
                   * apply lookup_lt_Some in Hi_succ_x_lookup. lia.
                   * exact Hi_succ_x_lookup.
                 + exact Hhead_in_x.
                 + exact Hnm_chain_x.
                 + exact Hsome_at_pos_x.
               - exact Hdummy_x.
               - exact Hnvi_x.
               - exact Hdqi_x.
               - apply Hno_O_inv_x.
               - apply Hno_O_inv_x.
               - exact Hcoi_x.
               - exact Hwit_x. }
             wp_pures.
             iApply ("IH" with "Hfrag HΦ Hnd_v [Hnd_n]"); first by iExists _.
          ** (* CAS fail: tail unchanged. *)
             wp_cmpxchg_fail.
             iModIntro.
             iSplitL "Hhead_x Htail_x Hchain_x Htrace_x Hauth_op_x Hauth_nm_x
                      Hfrag_nm_x Hauth_dq_x Hfrag_dq_x Hauth_del_x Hauth_calls_x
                      Hauth_no_O_x Hauth_ls_x Hauth_w_x Hfrag_w_x".
             { iNext.
               iExists nodes_x, del_pref_x, head_val_x, tail_val_x, dummy_loc_x,
                 ts_x, s_x, ls_x, op_map_x, node_map_x, dq_map_x, no_O_set_x, witness_map_x.
               iFrame. iPureIntro. split_and!.
               - exact Hsteps_x.
               - exact Hts_eq_x.
               - exact Hsim_x.
               - exact Hdummy_x.
               - exact Hnvi_x.
               - exact Hdqi_x.
               - apply Hno_O_inv_x.
               - apply Hno_O_inv_x.
               - exact Hcoi_x.
               - exact Hwit_x. }
             wp_pures.
             iApply ("IH" with "Hfrag HΦ Hnd_v [Hnd_n]"); first by iExists _.
      + (* tail_val_5 ≠ tail_val: stale tail, recurse via IH. *)
        wp_pures.
        iApply ("IH" with "Hfrag HΦ Hnd_v [Hnd_n]"); first by iExists _.

    - (* succ_at_4 = None: extract-or-mint the chain-snapshot witness
         for [(τ, tail_val)], then close inv with the (potentially
         updated) witness map.  Sharing the close-inv between Extract
         and Mint via a single existential [wm']. *)
      iAssert (|={⊤ ∖ ↑Nbq}=>
                ∃ wm', own γ_w (● to_witnessmap wm')
                       ∗ own γ_w (◯ to_witnessmap wm')
                       ∗ (∃ snap, own γ_w (◯ {[(τ, tail_val) := to_agree
                                            (snap : leibnizO chain_snapshot)]}))
                       ∗ ⌜chain_witness_inv wm' nodes_4 s_4⌝)%I
        with "[Hauth_w4 Hfrag_w4]"
        as ">(%wm' & Hauth_w4 & Hfrag_w4 & #Hwit_τ_frag & %Hwit_inv')".
      { destruct (witness_map_4 !! (τ, tail_val)) as [snap_existing|]
          eqn:Hwit_τ_lookup.
        - (* Extract: existing fragment, no auth update. *)
          iAssert (∃ snap, own γ_w (◯ {[(τ, tail_val) := to_agree
                       (snap : leibnizO chain_snapshot)]}))%I
            as "#Hwit_part".
          { iExists snap_existing.
            iApply (own_mono with "Hfrag_w4").
            apply auth_frag_mono.
            apply (proj2 (singleton_included_l _ _ _)).
            exists (to_agree (snap_existing : leibnizO chain_snapshot)).
            split; last reflexivity.
            rewrite /to_witnessmap lookup_fmap Hwit_τ_lookup //=. }
          iModIntro. iExists witness_map_4.
          iFrame "Hauth_w4 Hfrag_w4 Hwit_part".
          iPureIntro. exact Hwit4.
        - (* Mint: alloc fresh entry. *)
          pose (snap_τ := take (i_t_4 + 1)%nat nodes_4 : chain_snapshot).
          iMod (own_update_2 _ _ _
                  (● to_witnessmap (<[(τ, tail_val) := snap_τ]> witness_map_4)
                   ⋅ ◯ to_witnessmap (<[(τ, tail_val) := snap_τ]> witness_map_4))
                  with "Hauth_w4 Hfrag_w4") as "[Hauth_w4 Hfrag_w4]".
          { apply auth_update.
            rewrite /to_witnessmap !fmap_insert.
            apply: alloc_local_update; [|done].
            rewrite lookup_fmap Hwit_τ_lookup //. }
          iAssert (∃ snap, own γ_w (◯ {[(τ, tail_val) := to_agree
                       (snap : leibnizO chain_snapshot)]}))%I
            as "#Hwit_part".
          { iExists snap_τ.
            iApply (own_mono with "Hfrag_w4").
            apply auth_frag_mono.
            apply (proj2 (singleton_included_l _ _ _)).
            exists (to_agree (snap_τ : leibnizO chain_snapshot)).
            split; last reflexivity.
            rewrite /to_witnessmap lookup_fmap lookup_insert_eq //=. }
          iModIntro.
          iExists (<[(τ, tail_val) := snap_τ]> witness_map_4).
          iFrame "Hauth_w4 Hfrag_w4 Hwit_part".
          iPureIntro.
          (* chain_witness_inv preservation across mint, using
             [Hsucc_4_eqn = None] to discharge the lt-edges clause. *)
          destruct Hwit4 as [Hwit_dom Hwit_per].
          split.
          { intros [τ' tail_loc'] Hk.
            rewrite dom_insert_L in Hk.
            rewrite elem_of_union elem_of_singleton in Hk.
            destruct Hk as [Heq|Hold].
            - assert (τ' = τ) as -> by congruence.
              simpl.
              destruct Hsim4 as (_ & _ & _ & Hdomsub' & _).
              apply Hdomsub'. apply elem_of_dom. by exists info_τ4.
            - exact (Hwit_dom (τ', tail_loc') Hold). }
          intros τ' tail_loc' snap' Hwit_lookup'.
          destruct (decide ((τ', tail_loc') = (τ, tail_val))) as [Heq|Hne].
          + injection Heq as -> ->.
            rewrite lookup_insert_eq in Hwit_lookup'.
            injection Hwit_lookup' as <-.
            assert (Hi_t_4_lt : (i_t_4 < length nodes_4)%nat).
            { apply lookup_lt_Some in Hi_t_4_lookup. exact Hi_t_4_lookup. }
            unfold snap_τ.
            assert (Hlen_take : length (take (i_t_4 + 1)%nat nodes_4) = (i_t_4 + 1)%nat).
            { apply length_take_le. lia. }
            assert (Hlen_nodes : length nodes_4 = (i_t_4 + 1)%nat).
            { rewrite /succ_at in Hsucc_4_eqn.
              destruct (nodes_4 !! (i_t_4 + 1)%nat) eqn:Hi_t_p1; [discriminate|].
              apply lookup_ge_None_1 in Hi_t_p1. lia. }
            split_and!.
            * apply sublist_take.
            * lia.
            * rewrite /succ_at Hlen_take.
              replace (i_t_4 + 1 - 1)%nat with i_t_4 by lia.
              rewrite lookup_ge_None_2; first done. rewrite Hlen_take. lia.
            * exists τ_t_opt, v_t.
              rewrite Hlen_take.
              replace (i_t_4 + 1 - 1)%nat with i_t_4 by lia.
              rewrite lookup_take_lt; [|lia]. exact Hi_t_4_lookup.
            * (* lt-edges: discharged using [Hsucc_4_eqn = None] and
                 [Hlen_nodes = i_t_4 + 1]. *)
              intros k Hkin.
              destruct Hsim4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hlt_pos4 & _).
              destruct (Hlt_pos4 k τ Hkin) as (p_k & l_k & d_k & Hp_k_pos & Hp_k_lookup & _).
              assert (p_k ≤ i_t_4)%nat as Hp_k_le.
              { apply lookup_lt_Some in Hp_k_lookup. lia. }
              exists p_k, l_k, d_k. split.
              -- rewrite lookup_take_lt; [exact Hp_k_lookup|lia].
              -- exact Hp_k_pos.
          + rewrite lookup_insert_ne in Hwit_lookup'; [|done].
            exact (Hwit_per τ' tail_loc' snap' Hwit_lookup'). }
      iModIntro.
      iSplitL "Hhead4 Htail4 Hchain4 Htrace4 Hauth_op4 Hauth_nm4 Hfrag_nm4 Hauth_dq4 Hfrag_dq4 Hauth_del4 Hauth_calls4 Hauth_no_O4 Hauth_ls4 Hauth_w4 Hfrag_w4".
      { iNext. iExists nodes_4, del_pref_4, head_val_4, tail_val_4, dummy_loc_4, ts_4, s_4, ls_4,
          op_map_4, node_map_4, dq_map_4, no_O_set_4, wm'.
        by iFrame. }
      wp_pures.

      (* PHASE 5 (succ_at_4 = None): consistency check + 2-way mark
         dispatch.  Inner (mark = false) takes the splice branch
         using [Hwit_τ_frag] for the basket call; (mark = true)
         recurses via IH. *)
      wp_bind (! _)%E.
      iInv Nbq as (nodes_5 del_pref_5 head_val_5 tail_val_5 dummy_loc_5 ts_5 s_5 ls_5
                   op_map_5 node_map_5 dq_map_5 no_O_set_5 witness_map_5)
        "(>Hhead5 & >Htail5 & Hchain5 & >Htrace5 & >Hauth_op5 & >Hauth_nm5 & Hfrag_nm5
          & >Hauth_dq5 & Hfrag_dq5 & >Hauth_del5 & >Hauth_calls5 & >Hauth_no_O5 & >Hauth_ls5 & >Hauth_w5 & Hfrag_w5
          & >%Hsteps5 & >%Hts_eq5 & >%Hsim5 & >%Hdummy5 & >%Hnvi5 & >%Hdqi5 & >%Hno_O_inv5 & >%Hcoi5 & >%Hwit5)".
      wp_load.
      iModIntro.
      iSplitL "Hhead5 Htail5 Hchain5 Htrace5 Hauth_op5 Hauth_nm5 Hfrag_nm5 Hauth_dq5 Hfrag_dq5 Hauth_del5 Hauth_calls5 Hauth_no_O5 Hauth_ls5 Hauth_w5 Hfrag_w5".
      { iNext. iExists nodes_5, del_pref_5, head_val_5, tail_val_5, dummy_loc_5, ts_5, s_5, ls_5,
          op_map_5, node_map_5, dq_map_5, no_O_set_5, witness_map_5.
        by iFrame. }
      wp_op. case_bool_decide as Hcmp.
      + (* tail_val_5 = tail_val: dispatch on mark only. *)
        assert (tail_val_5 = tail_val) as -> by congruence.
        wp_pures.
        rewrite /next_value_of.
        destruct (mark_at del_pref_4 i_t_4) eqn:Hmark_4.
        * (* mark = true: marked-null, recurse via IH. *)
          wp_pures.
          iApply ("IH" with "Hfrag HΦ Hnd_v [Hnd_n]"); first by iExists _.
        * (* mark = false: direct splice — phase 6 + 7 + 8.  Body
             below is the verbatim original (false, None) sub-case
             with bullets renamed [* → **] and [** → ***]. *)
        wp_pures.
        wp_store.  (* nd.next := InjL #() — redundant store *)
        wp_pures.
        wp_bind (CmpXchg _ _ _).
        iInv Nbq as (nodes_6 del_pref_6 head_val_6 tail_val_6 dummy_loc_6 ts_6 s_6 ls_6
                     op_map_6 node_map_6 dq_map_6 no_O_set_6 witness_map_6)
          "(>Hhead6 & >Htail6 & >Hchain6 & >Htrace6 & >Hauth_op6 & >Hauth_nm6 & Hfrag_nm6
            & >Hauth_dq6 & Hfrag_dq6 & >Hauth_del6 & >Hauth_calls6 & >Hauth_no_O6 & >Hauth_ls6 & >Hauth_w6 & Hfrag_w6
            & >%Hsteps6 & >%Hts_eq6 & >%Hsim6 & >%Hdummy6 & >%Hnvi6 & >%Hdqi6 & >%Hno_O_inv6 & >%Hcoi6 & >%Hwit6)".
        (* Find [tail_val]'s position in chain_6 via [Htail_frag]. *)
        iDestruct (own_valid_2 with "Hauth_nm6 Htail_frag") as %Hnm_agree_6.
        apply auth_both_valid_discrete in Hnm_agree_6 as [Hincl_6 _].
        apply singleton_included_l in Hincl_6 as (av_6 & Hav_lookup_6 & Hav_incl_6).
        rewrite /to_nodemap lookup_fmap in Hav_lookup_6.
        apply fmap_Some_equiv in Hav_lookup_6 as (info_6 & Hnm6_lookup & Hav_eq_6).
        rewrite Hav_eq_6 in Hav_incl_6. rewrite Some_included in Hav_incl_6.
        assert ((τ_t_opt, v_t) = info_6 :> leibnizO node_info) as Hinfo_6_eq.
        { destruct Hav_incl_6 as [Heq|Hin].
          - by apply (inj to_agree), leibniz_equiv in Heq.
          - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
        rewrite -Hinfo_6_eq in Hnm6_lookup.
        clear Hav_eq_6 Hav_incl_6 Hinfo_6_eq info_6.
        pose proof Hsim6 as (Hlen6 & Hdel6 & Hcp_in_ts6 & Hdomsub6 & Hnm_dom6 & Henq_clause6
                           & Hdeq_clause6 & Hinj6 & Hcorr6 & Hlt_pos6 & _Htbd6 & Hcomp_link6
                           & Htail_in6 & Hhead_in6 & Hnm_chain6 & Hsome_at_pos6).
        destruct (Hnm_dom6 _ _ _ Hnm6_lookup) as (i_t_6 & Hi_t_6_lookup).
        (* Case-split on (mark_at, succ_at) at chain_6 BEFORE accessing
           the chain.  CAS-success [(false, None)] uses
           [bq_chain_split_last] so the prefix can be re-used with
           [bq_chain_snoc] to extend the chain.  The three CAS-fail
           cases use [bq_chain_lookup_acc] and re-close [bq_chain] with
           the unchanged next-cell. *)
        destruct (mark_at del_pref_6 i_t_6) eqn:Hmark_6;
        destruct (succ_at nodes_6 i_t_6) as [l_succ_6|] eqn:Hsucc_6.
        ** (* (true, Some l_succ_6): cell value [InjRV #l_succ_6].
             CAS fails (mismatch with [InjLV #()]).  After the CAS
             returns [#false] the impl dispatches to [enq_basket]. *)
          iDestruct (bq_chain_lookup_acc _ del_pref_6 i_t_6 tail_val τ_t_opt v_t
                       Hi_t_6_lookup with "Hchain6") as "[Hv6 [Hn6 HW6]]".
          iEval (rewrite Hmark_6 Hsucc_6 /next_value_of) in "Hn6".
          wp_cmpxchg_fail.
          iDestruct ("HW6" with "[$Hv6 Hn6]") as "Hchain6".
          { rewrite Hmark_6 Hsucc_6 /next_value_of. iFrame. }
          iModIntro.
          iSplitL "Hhead6 Htail6 Hchain6 Htrace6 Hauth_op6 Hauth_nm6 Hfrag_nm6
                   Hauth_dq6 Hfrag_dq6 Hauth_del6 Hauth_calls6 Hauth_no_O6
                   Hauth_ls6 Hauth_w6 Hfrag_w6".
          { iNext. iExists nodes_6, del_pref_6, head_val_6, tail_val_6, dummy_loc_6,
              ts_6, s_6, ls_6, op_map_6, node_map_6, dq_map_6, no_O_set_6, witness_map_6.
            iFrame. iPureIntro. split_and!.
            - exact Hsteps6.
            - exact Hts_eq6.
            - exact Hsim6.
            - exact Hdummy6.
            - exact Hnvi6.
            - exact Hdqi6.
            - apply Hno_O_inv6.
            - apply Hno_O_inv6.
            - exact Hcoi6.
            - exact Hwit6. }
          (* Dispatch to [enq_basket]: returns either [#true] (nd
             linked) or [#false] (basket dissolved, resources
             returned).  Use [wp_wand] to bridge the lemma's
             disjunctive post-condition and the bind continuation;
             each branch of [iIntros]'s case analysis independently
             owns [HΦ] and the iLöb [IH] in its proof context. *)
          wp_pures.
          wp_bind (enq_basket _ _).
          iApply (wp_wand with "[Hfrag Hnd_v Hnd_n]").
          { iApply (op_spec_enq_basket γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                      l head tail tail_val nd τ d
                      with "[%//] Hinv Htrace_inv Hfrag Hnd_v [Hnd_n] [Htail_frag] [#]");
              [by iExists _ | by iExists τ_t_opt, v_t | iApply "Hwit_τ_frag"]. }
          iIntros (b) "[(-> & Hfrag)|(-> & Hfrag & Hnd_v & (%nxb & Hnd_n))]".
          *** (* basket attach succeeded: nd is linked.  Continue with
                trace_emit (phase 8 helper). *)
             wp_pures.
             iApply (op_spec_enq_trace_emit
                       γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                       l head tail nd τ d
                       with "Hinv Htrace_inv Hfrag HΦ").
          *** (* basket dissolved: restart via [IH]. *)
             wp_pures.
             iApply ("IH" with "Hfrag HΦ Hnd_v [Hnd_n]"); first by iExists _.
        ** (* (true, None): cell value [InjRV #()].  CAS fails. *)
          iDestruct (bq_chain_lookup_acc _ del_pref_6 i_t_6 tail_val τ_t_opt v_t
                       Hi_t_6_lookup with "Hchain6") as "[Hv6 [Hn6 HW6]]".
          iEval (rewrite Hmark_6 Hsucc_6 /next_value_of) in "Hn6".
          wp_cmpxchg_fail.
          iDestruct ("HW6" with "[$Hv6 Hn6]") as "Hchain6".
          { rewrite Hmark_6 Hsucc_6 /next_value_of. iFrame. }
          iModIntro.
          iSplitL "Hhead6 Htail6 Hchain6 Htrace6 Hauth_op6 Hauth_nm6 Hfrag_nm6
                   Hauth_dq6 Hfrag_dq6 Hauth_del6 Hauth_calls6 Hauth_no_O6
                   Hauth_ls6 Hauth_w6 Hfrag_w6".
          { iNext. iExists nodes_6, del_pref_6, head_val_6, tail_val_6, dummy_loc_6,
              ts_6, s_6, ls_6, op_map_6, node_map_6, dq_map_6, no_O_set_6, witness_map_6.
            iFrame. iPureIntro. split_and!.
            - exact Hsteps6.
            - exact Hts_eq6.
            - exact Hsim6.
            - exact Hdummy6.
            - exact Hnvi6.
            - exact Hdqi6.
            - apply Hno_O_inv6.
            - apply Hno_O_inv6.
            - exact Hcoi6.
            - exact Hwit6. }
          (* Dispatch to [enq_basket]: returns either [#true] (nd
             linked) or [#false] (basket dissolved, resources
             returned).  Use [wp_wand] to bridge the lemma's
             disjunctive post-condition and the bind continuation;
             each branch of [iIntros]'s case analysis independently
             owns [HΦ] and the iLöb [IH] in its proof context. *)
          wp_pures.
          wp_bind (enq_basket _ _).
          iApply (wp_wand with "[Hfrag Hnd_v Hnd_n]").
          { iApply (op_spec_enq_basket γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                      l head tail tail_val nd τ d
                      with "[%//] Hinv Htrace_inv Hfrag Hnd_v [Hnd_n] [Htail_frag] [#]");
              [by iExists _ | by iExists τ_t_opt, v_t | iApply "Hwit_τ_frag"]. }
          iIntros (b) "[(-> & Hfrag)|(-> & Hfrag & Hnd_v & (%nxb & Hnd_n))]".
          *** (* basket attach succeeded: nd is linked.  Continue with
                trace_emit (phase 8 helper). *)
             wp_pures.
             iApply (op_spec_enq_trace_emit
                       γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                       l head tail nd τ d
                       with "Hinv Htrace_inv Hfrag HΦ").
          *** (* basket dissolved: restart via [IH]. *)
             wp_pures.
             iApply ("IH" with "Hfrag HΦ Hnd_v [Hnd_n]"); first by iExists _.
        ** (* (false, Some l_succ_6): cell value [InjLV #l_succ_6] with
             [l_succ_6 ≠ #()].  CAS fails (loc ≠ unit). *)
          iDestruct (bq_chain_lookup_acc _ del_pref_6 i_t_6 tail_val τ_t_opt v_t
                       Hi_t_6_lookup with "Hchain6") as "[Hv6 [Hn6 HW6]]".
          iEval (rewrite Hmark_6 Hsucc_6 /next_value_of) in "Hn6".
          wp_cmpxchg_fail.
          iDestruct ("HW6" with "[$Hv6 Hn6]") as "Hchain6".
          { rewrite Hmark_6 Hsucc_6 /next_value_of. iFrame. }
          iModIntro.
          iSplitL "Hhead6 Htail6 Hchain6 Htrace6 Hauth_op6 Hauth_nm6 Hfrag_nm6
                   Hauth_dq6 Hfrag_dq6 Hauth_del6 Hauth_calls6 Hauth_no_O6
                   Hauth_ls6 Hauth_w6 Hfrag_w6".
          { iNext. iExists nodes_6, del_pref_6, head_val_6, tail_val_6, dummy_loc_6,
              ts_6, s_6, ls_6, op_map_6, node_map_6, dq_map_6, no_O_set_6, witness_map_6.
            iFrame. iPureIntro. split_and!.
            - exact Hsteps6.
            - exact Hts_eq6.
            - exact Hsim6.
            - exact Hdummy6.
            - exact Hnvi6.
            - exact Hdqi6.
            - apply Hno_O_inv6.
            - apply Hno_O_inv6.
            - exact Hcoi6.
            - exact Hwit6. }
          (* Dispatch to [enq_basket]: returns either [#true] (nd
             linked) or [#false] (basket dissolved, resources
             returned).  Use [wp_wand] to bridge the lemma's
             disjunctive post-condition and the bind continuation;
             each branch of [iIntros]'s case analysis independently
             owns [HΦ] and the iLöb [IH] in its proof context. *)
          wp_pures.
          wp_bind (enq_basket _ _).
          iApply (wp_wand with "[Hfrag Hnd_v Hnd_n]").
          { iApply (op_spec_enq_basket γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                      l head tail tail_val nd τ d
                      with "[%//] Hinv Htrace_inv Hfrag Hnd_v [Hnd_n] [Htail_frag] [#]");
              [by iExists _ | by iExists τ_t_opt, v_t | iApply "Hwit_τ_frag"]. }
          iIntros (b) "[(-> & Hfrag)|(-> & Hfrag & Hnd_v & (%nxb & Hnd_n))]".
          *** (* basket attach succeeded: nd is linked.  Continue with
                trace_emit (phase 8 helper). *)
             wp_pures.
             iApply (op_spec_enq_trace_emit
                       γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                       l head tail nd τ d
                       with "Hinv Htrace_inv Hfrag HΦ").
          *** (* basket dissolved: restart via [IH]. *)
             wp_pures.
             iApply ("IH" with "Hfrag HΦ Hnd_v [Hnd_n]"); first by iExists _.
        ** (* (false, None): cell value [InjLV #()].  CAS succeeds —
             this is the LP-fixing splice that links [nd] into the
             chain. *)
          (* From [Hsucc_6 = None] and [Hi_t_6_lookup] derive
             [length nodes_6 = i_t_6 + 1] (i.e., [tail_val] is the
             chain's last cell). *)
          assert (length nodes_6 = i_t_6 + 1)%nat as Hlen_eq.
          { rewrite /succ_at in Hsucc_6.
            destruct (nodes_6 !! (i_t_6 + 1)%nat) as [lτv|] eqn:Hnext; last first.
            - apply lookup_ge_None in Hnext.
              apply lookup_lt_Some in Hi_t_6_lookup. lia.
            - discriminate. }
          assert (Hlast_lookup_6 :
                    nodes_6 !! (length nodes_6 - 1)%nat
                    = Some (tail_val, τ_t_opt, v_t)).
          { rewrite Hlen_eq.
            replace (i_t_6 + 1 - 1)%nat with i_t_6 by lia.
            exact Hi_t_6_lookup. }
          (* Before destructuring the chain, derive freshness of [nd]
             vs [node_map_6]: every recorded location is a chain
             location (clause 5) and therefore [≠ nd] by [pointsto_ne]
             against [Hnd_v]. *)
          iAssert ⌜node_map_6 !! nd = None⌝%I as %Hnd_fresh.
          { destruct (node_map_6 !! nd) as [[τ_opt' v']|] eqn:Hnd_lk; last done.
            destruct (Hnm_dom6 _ _ _ Hnd_lk) as (j & Hj_lookup).
            iDestruct (big_sepL_lookup _ _ _ _ Hj_lookup with "Hchain6")
              as "[Hv_j _]".
            simpl. by iDestruct (pointsto_ne with "Hnd_v Hv_j") as %?. }
          (* Split the chain at the last cell to get the prefix in
             addition to [tail_val]'s value- and next-cells. *)
          iDestruct (bq_chain_split_last _ _ tail_val τ_t_opt v_t Hlen6
                       Hlast_lookup_6 with "Hchain6")
            as "(Hpref6 & Hv6 & Hn6)".
          assert (Hidx_eq : (length nodes_6 - 1)%nat = i_t_6) by lia.
          iEval (rewrite Hidx_eq Hmark_6 Hsucc_6 /next_value_of) in "Hn6".
          wp_cmpxchg_suc.
          (* === Step A: Extract [op_map_6 !! τ] via [Hfrag]. === *)
          iDestruct (own_valid_2 with "Hauth_op6 Hfrag") as %Hτ_both.
          apply auth_both_valid_discrete in Hτ_both as [Hτ_incl Hτ_valid].
          apply singleton_included_exclusive_l in Hτ_incl; [|apply _|done].
          rewrite lookup_fmap in Hτ_incl.
          apply leibniz_equiv in Hτ_incl.
          apply fmap_Some_1 in Hτ_incl as (info_τ & Hτ_in_op6 & Hinfo_τ).
          destruct info_τ as [kd nd_τ lk]; injection Hinfo_τ as <- <- <-.
          (* From [Henq_clause6] for [τ]: cp[τ] = A1, ℓ[τ] = (d, PEND),
             τ ∈ absq_O. *)
          destruct (Henq_clause6 _ _ _ _ Hτ_in_op6)
            as (Hcp_τ_A1 & Hℓ_τ_PEND & Hτ_pre & _).
          specialize (Hτ_pre eq_refl).
          (* === Step B: γ_op update — [linked := true, node := Some nd]. === *)
          set (new_τ_info := {| op_info_kind := OpEnq d;
                                 op_info_node := Some nd;
                                 op_info_linked := true |}).
          iMod (own_update_2 _ _ _
                  (● to_opmap (<[τ := new_τ_info]> op_map_6)
                     ⋅ ◯ {[τ := Excl new_τ_info]})
                  with "Hauth_op6 Hfrag") as "[Hauth_op6 Hfrag]".
          { apply auth_update.
            rewrite /to_opmap fmap_insert.
            apply: singleton_local_update.
            { rewrite lookup_fmap Hτ_in_op6 //. }
            by apply exclusive_local_update. }
          (* === Step C: γ_nm update — allocate fresh entry [nd ↦ (Some τ, d)]. === *)
          iMod (own_update_2 _ _ _
                  (● to_nodemap (<[nd := (Some τ, d) : node_info]> node_map_6)
                     ⋅ ◯ to_nodemap (<[nd := (Some τ, d) : node_info]> node_map_6))
                  with "Hauth_nm6 Hfrag_nm6") as "[Hauth_nm6 Hfrag_nm6]".
          { apply auth_update.
            rewrite /to_nodemap !fmap_insert.
            apply: alloc_local_update; [|done].
            rewrite lookup_fmap Hnd_fresh //. }
          (* === Step D: Extend the chain via [bq_chain_snoc]. === *)
          iDestruct (bq_chain_snoc nodes_6 tail_val τ_t_opt v_t nd (Some τ) d
                       del_pref_6 Hlen6 Hdel6 Hlast_lookup_6
                       with "[$Hpref6 $Hv6 $Hn6 $Hnd_v $Hnd_n]") as "Hchain6".
          set (new_nodes := nodes_6 ++ [(nd, Some τ, d) : (loc * option positive * val)]).
          (* Discharge "no chain position has [Some τ] tag" via the
             [chain_op_inv] invariant from the inv-open: if position
             [i_old] had tag [Some τ], [Hcoi6] specialized at
             [Hτ_in_op6] would give [linked = true], contradicting
             [linked = false] from [Hτ_in_op6]'s destructure. *)
          assert (Hτ_not_in_chain : ∀ i_old l_old d_old,
                    (1 ≤ i_old)%nat →
                    nodes_6 !! i_old = Some (l_old, Some τ, d_old) → False).
          { intros i_old l_old d_old Hpos Hlk.
            pose proof (Hcoi6 _ _ _ _ Hpos Hlk _ Hτ_in_op6) as Habs.
            discriminate. }
          (* === Step E: Close inv with new chain, op_map, node_map. === *)
          iModIntro.
          iSplitL "Hhead6 Htail6 Hchain6 Htrace6 Hauth_op6 Hauth_nm6 Hfrag_nm6
                   Hauth_dq6 Hfrag_dq6 Hauth_del6 Hauth_calls6 Hauth_no_O6
                   Hauth_ls6 Hauth_w6 Hfrag_w6".
          { iNext.
            iExists new_nodes, del_pref_6, head_val_6, tail_val_6, dummy_loc_6,
              ts_6, s_6, ls_6,
              (<[τ := new_τ_info]> op_map_6),
              (<[nd := (Some τ, d) : node_info]> node_map_6),
              dq_map_6, no_O_set_6.
            iFrame.
            iPureIntro. split_and!.
            - exact Hsteps6.
            - exact Hts_eq6.
            - (* === bq_sim — 16 clauses. === *)
              split_and!; simpl.
              + (* 1: 1 ≤ length new_nodes *)
                subst new_nodes; rewrite length_app /=; lia.
              + (* 2: del_pref < length new_nodes *)
                subst new_nodes; rewrite length_app /=; lia.
              + (* 3: dom cp ⊆ ts.*1 — unchanged *)
                exact Hcp_in_ts6.
              + (* 4: dom op_map ⊆ dom cp *)
                rewrite dom_insert_L.
                apply union_least; [|exact Hdomsub6].
                apply singleton_subseteq_l, elem_of_dom; eauto.
              + (* 5: node_map → chain *)
                intros lk τ_opt v Hlk.
                destruct (decide (lk = nd)) as [->|Hne].
                * rewrite lookup_insert_eq in Hlk.
                  injection Hlk as <- <-.
                  exists (length nodes_6).
                  subst new_nodes. rewrite lookup_app_r; [|lia].
                  by replace (length nodes_6 - length nodes_6)%nat with 0%nat by lia.
                * rewrite lookup_insert_ne in Hlk; [|done].
                  destruct (Hnm_dom6 _ _ _ Hlk) as (i & Hi).
                  exists i. subst new_nodes. rewrite lookup_app_l; [exact Hi|].
                  apply lookup_lt_Some in Hi. lia.
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
                     exists nd, (length nodes_6).
                     split_and!.
                     *** reflexivity.
                     *** lia.
                     *** subst new_nodes. rewrite lookup_app_r; [|lia].
                         by replace (length nodes_6 - length nodes_6)%nat with 0%nat by lia.
                     *** by rewrite lookup_insert_eq.
                     *** split.
                         { intros _. lia. }
                         { intros _. exact Hτ_pre. }
                * rewrite lookup_insert_ne in Hop'; [|done].
                  destruct (Henq_clause6 _ _ _ _ Hop')
                    as (Hcp' & Hℓ' & Hpre' & Hpost').
                  split_and!.
                  ** exact Hcp'.
                  ** exact Hℓ'.
                  ** exact Hpre'.
                  ** intros Hlinked.
                     destruct (Hpost' Hlinked)
                       as (l_old & i_old & Hnode_eq & Hi_pos & Hi_lookup
                            & Hnm_old & Hin_iff).
                     exists l_old, i_old.
                     split_and!.
                     *** exact Hnode_eq.
                     *** exact Hi_pos.
                     *** subst new_nodes. rewrite lookup_app_l; [exact Hi_lookup|].
                         apply lookup_lt_Some in Hi_lookup. lia.
                     *** destruct (decide (l_old = nd)) as [->|Hne_l].
                         { exfalso. rewrite Hnd_fresh in Hnm_old. discriminate. }
                         rewrite lookup_insert_ne; [exact Hnm_old | done].
                     *** exact Hin_iff.
              + (* 7: per-dequeue clause *)
                intros τ' obs' rng' node' linked' Hop'.
                destruct (decide (τ' = τ)) as [->|Hne].
                * rewrite lookup_insert_eq in Hop'.
                  inversion Hop'.
                * rewrite lookup_insert_ne in Hop'; [|done].
                  exact (Hdeq_clause6 _ _ _ _ _ Hop').
              + (* 8: chain-id injectivity *)
                intros i j l_i l_j τ' d_i d_j Hi_pos Hj_pos Hi_lookup Hj_lookup.
                apply lookup_lt_Some in Hi_lookup as Hi_lt.
                apply lookup_lt_Some in Hj_lookup as Hj_lt.
                subst new_nodes. rewrite length_app /= in Hi_lt, Hj_lt.
                destruct (Nat.eq_dec i (length nodes_6)) as [Hi_eq|Hi_ne];
                destruct (Nat.eq_dec j (length nodes_6)) as [Hj_eq|Hj_ne].
                * congruence.
                * subst i.
                  rewrite lookup_app_r in Hi_lookup; [|lia].
                  replace (length nodes_6 - length nodes_6)%nat with 0%nat in Hi_lookup
                    by lia.
                  simpl in Hi_lookup. injection Hi_lookup as <- <- <-.
                  assert (j < length nodes_6)%nat by lia.
                  rewrite lookup_app_l in Hj_lookup; [|done].
                  exfalso. eapply (Hτ_not_in_chain _ _ _ Hj_pos Hj_lookup).
                * subst j.
                  rewrite lookup_app_r in Hj_lookup; [|lia].
                  replace (length nodes_6 - length nodes_6)%nat with 0%nat in Hj_lookup
                    by lia.
                  simpl in Hj_lookup. injection Hj_lookup as <- <- <-.
                  assert (i < length nodes_6)%nat by lia.
                  rewrite lookup_app_l in Hi_lookup; [|done].
                  exfalso. eapply (Hτ_not_in_chain _ _ _ Hi_pos Hi_lookup).
                * assert (i < length nodes_6)%nat by lia.
                  assert (j < length nodes_6)%nat by lia.
                  rewrite lookup_app_l in Hi_lookup; [|done].
                  rewrite lookup_app_l in Hj_lookup; [|done].
                  apply (Hinj6 _ _ _ _ _ _ _ Hi_pos Hj_pos Hi_lookup Hj_lookup).
              + (* 9: chain ↔ absq_l correspondence *)
                intros i lk τ' v Hi_pos Hi_lookup.
                apply lookup_lt_Some in Hi_lookup as Hi_lt.
                subst new_nodes. rewrite length_app /= in Hi_lt.
                destruct (Nat.eq_dec i (length nodes_6)) as [Hi_eq|Hi_ne].
                * subst i.
                  rewrite lookup_app_r in Hi_lookup; [|lia].
                  replace (length nodes_6 - length nodes_6)%nat with 0%nat in Hi_lookup
                    by lia.
                  simpl in Hi_lookup. injection Hi_lookup as <- <- <-.
                  split_and!.
                  ** by rewrite lookup_insert_eq.
                  ** eexists. exact Hℓ_τ_PEND.
                  ** split.
                     { intros _. lia. }
                     { intros _. exact Hτ_pre. }
                * assert (i < length nodes_6)%nat by lia.
                  rewrite lookup_app_l in Hi_lookup; [|done].
                  destruct (Hcorr6 _ _ _ _ Hi_pos Hi_lookup)
                    as (Hnm_l & Habs_l & Hin_iff).
                  split_and!.
                  ** destruct (decide (lk = nd)) as [->|Hne_l].
                     { exfalso. rewrite Hnd_fresh in Hnm_l. discriminate. }
                     rewrite lookup_insert_ne; [exact Hnm_l | done].
                  ** exact Habs_l.
                  ** exact Hin_iff.
              + (* 10: happens-before respects list order *)
                intros k k_e Hkk.
                destruct (Hlt_pos6 _ _ Hkk)
                  as (p_k & l_k & d_k & Hp_k_pos & Hp_k_lookup & Hp_ke_imp).
                exists p_k, l_k, d_k.
                split_and!.
                * exact Hp_k_pos.
                * subst new_nodes. rewrite lookup_app_l; [exact Hp_k_lookup|].
                  apply lookup_lt_Some in Hp_k_lookup. lia.
                * intros p_ke l_ke d_ke Hp_ke_pos Hnodes_ke.
                  apply lookup_lt_Some in Hnodes_ke as Hp_ke_lt.
                  subst new_nodes. rewrite length_app /= in Hp_ke_lt.
                  destruct (Nat.eq_dec p_ke (length nodes_6)) as [->|Hp_ke_ne].
                  ** apply lookup_lt_Some in Hp_k_lookup. lia.
                  ** assert (p_ke < length nodes_6)%nat by lia.
                     rewrite lookup_app_l in Hnodes_ke; [|done].
                     apply (Hp_ke_imp _ _ _ Hp_ke_pos Hnodes_ke).
              + (* 11: TBD *)
                done.
              + (* 12: COMP enqueues are linked *)
                intros τ' d' Hℓ_τ'.
                destruct (Hcomp_link6 _ _ Hℓ_τ') as (p & l_p & Hp_pos & Hp_lookup).
                exists p, l_p. split.
                * exact Hp_pos.
                * subst new_nodes. rewrite lookup_app_l; [exact Hp_lookup|].
                  apply lookup_lt_Some in Hp_lookup. lia.
              + (* 13: tail_loc names a chain position *)
                destruct Htail_in6 as (i_tail6 & τ_t6 & v_t6 & Hi_tail_lt & Htail_at6).
                exists i_tail6, τ_t6, v_t6. split.
                * subst new_nodes. rewrite length_app /=. lia.
                * subst new_nodes. rewrite lookup_app_l; [exact Htail_at6 | lia].
              + (* 14: head_loc *)
                destruct Hhead_in6 as (i_h6 & τ_h6 & v_h6 & Hi_h_le6 & Hhead_at6).
                exists i_h6, τ_h6, v_h6. split.
                * exact Hi_h_le6.
                * subst new_nodes. rewrite lookup_app_l; [exact Hhead_at6|].
                  apply lookup_lt_Some in Hhead_at6. lia.
              + (* 15: chain → node_map *)
                intros i lk τ_opt v Hi.
                apply lookup_lt_Some in Hi as Hi_lt.
                subst new_nodes. rewrite length_app /= in Hi_lt.
                destruct (Nat.eq_dec i (length nodes_6)) as [->|Hi_ne].
                * rewrite lookup_app_r in Hi; [|lia].
                  replace (length nodes_6 - length nodes_6)%nat with 0%nat in Hi
                    by lia.
                  simpl in Hi. injection Hi as <- <- <-.
                  by rewrite lookup_insert_eq.
                * assert (i < length nodes_6)%nat by lia.
                  rewrite lookup_app_l in Hi; [|done].
                  pose proof (Hnm_chain6 _ _ _ _ Hi) as Hnm_l.
                  destruct (decide (lk = nd)) as [->|Hne_l].
                  ** exfalso. rewrite Hnd_fresh in Hnm_l. discriminate.
                  ** rewrite lookup_insert_ne; [exact Hnm_l | done].
              + (* 16: non-dummy positions carry Some τ *)
                intros i lk τ_opt v Hi_pos Hi_lookup.
                apply lookup_lt_Some in Hi_lookup as Hi_lt.
                subst new_nodes. rewrite length_app /= in Hi_lt.
                destruct (Nat.eq_dec i (length nodes_6)) as [->|Hi_ne].
                * rewrite lookup_app_r in Hi_lookup; [|lia].
                  replace (length nodes_6 - length nodes_6)%nat with 0%nat in Hi_lookup
                    by lia.
                  simpl in Hi_lookup. injection Hi_lookup as <- <- <-.
                  by exists τ.
                * assert (i < length nodes_6)%nat by lia.
                  rewrite lookup_app_l in Hi_lookup; [|done].
                  apply (Hsome_at_pos6 _ _ _ _ Hi_pos Hi_lookup).
            - (* dummy lookup *)
              subst new_nodes. rewrite lookup_app_l; [exact Hdummy6|].
              apply lookup_lt_Some in Hdummy6. lia.
            - (* node_val_inv *)
              split.
              + intros lk τ' d' Hlk.
                destruct (decide (lk = nd)) as [->|Hne].
                * rewrite lookup_insert_eq in Hlk.
                  injection Hlk as <- <-.
                  exists PEND. exact Hℓ_τ_PEND.
                * rewrite lookup_insert_ne in Hlk; [|done].
                  apply (proj1 Hnvi6 _ _ _ Hlk).
              + intros l₁ l₂ τ' d₁ d₂ Hlk₁ Hlk₂.
                destruct (decide (l₁ = nd)) as [Hl₁_eq|Hne₁];
                destruct (decide (l₂ = nd)) as [Hl₂_eq|Hne₂].
                * by rewrite Hl₁_eq Hl₂_eq.
                * subst l₁. rewrite lookup_insert_eq in Hlk₁.
                  injection Hlk₁ as <- <-.
                  rewrite lookup_insert_ne in Hlk₂; [|done].
                  exfalso.
                  destruct (Hnm_dom6 _ _ _ Hlk₂) as (j & Hj_lookup).
                  destruct j as [|j'].
                  ** rewrite Hdummy6 in Hj_lookup. injection Hj_lookup as ? ? ?.
                     discriminate.
                  ** eapply (Hτ_not_in_chain (Datatypes.S j')); [lia|exact Hj_lookup].
                * subst l₂. rewrite lookup_insert_eq in Hlk₂.
                  injection Hlk₂ as <- <-.
                  rewrite lookup_insert_ne in Hlk₁; [|done].
                  exfalso.
                  destruct (Hnm_dom6 _ _ _ Hlk₁) as (j & Hj_lookup).
                  destruct j as [|j'].
                  ** rewrite Hdummy6 in Hj_lookup. injection Hj_lookup as ? ? ?.
                     discriminate.
                  ** eapply (Hτ_not_in_chain (Datatypes.S j')); [lia|exact Hj_lookup].
                * rewrite lookup_insert_ne in Hlk₁; [|done].
                  rewrite lookup_insert_ne in Hlk₂; [|done].
                  apply (proj2 Hnvi6 _ _ _ _ _ Hlk₁ Hlk₂).
            - exact Hdqi6.
            - apply Hno_O_inv6.
            - apply Hno_O_inv6.
            - (* chain_op_inv for new_nodes = nodes_6 ++ [(nd, Some τ, d)]
                 and new_op_map = <[τ := new_τ_info]> op_map_6 *)
              intros i lk τ' v Hpos Hlk info Hop_lk.
              subst new_nodes.
              apply lookup_lt_Some in Hlk as Hlt.
              rewrite length_app /= in Hlt.
              destruct (Nat.eq_dec i (length nodes_6)) as [->|Hne_i].
              + rewrite lookup_app_r in Hlk; [|lia].
                replace (length nodes_6 - length nodes_6)%nat with 0%nat in Hlk by lia.
                simpl in Hlk. injection Hlk as <- <- <-.
                rewrite lookup_insert_eq in Hop_lk.
                injection Hop_lk as <-. reflexivity.
              + assert (i < length nodes_6)%nat by lia.
                rewrite lookup_app_l in Hlk; [|done].
                destruct (decide (τ' = τ)) as [->|Hne].
                * exfalso. exact (Hτ_not_in_chain _ _ _ Hpos Hlk).
                * rewrite lookup_insert_ne in Hop_lk; [|done].
                  exact (Hcoi6 _ _ _ _ Hpos Hlk _ Hop_lk).
            - (* chain_witness_inv: snoc preserves sublist; cp unchanged *)
              destruct Hwit6 as [Hwit_dom Hwit_per].
              split.
              { simpl. exact Hwit_dom. }
              intros τ' tail_loc_w snap Hwit_lookup.
              destruct (Hwit_per τ' tail_loc_w snap Hwit_lookup)
                as (Hsub & Hlen_w & Hsucc_w & Hsnap_end_w & Hlt_in_w).
              split_and!; [|exact Hlen_w|exact Hsucc_w|exact Hsnap_end_w|].
              { (* sublist preserved: snap ⊑ nodes_6 → snap ⊑ nodes_6 ++ [_] *)
                eapply sublist_inserts_r. exact Hsub. }
              intros k Hkin. by apply Hlt_in_w. }
          (* === PHASE 7: best-effort tail-advance CAS.  CAS [tail
             tail_val nd]; success advances [tail] to [nd], failure
             leaves the inv unchanged (some other thread already moved
             [tail] forward).  No AbsQ step. === *)
          wp_pures.
          wp_bind (CmpXchg _ _ _).
          iInv Nbq as (nodes_7 del_pref_7 head_val_7 tail_val_7 dummy_loc_7
                       ts_7 s_7 ls_7 op_map_7 node_map_7 dq_map_7 no_O_set_7 witness_map_7)
            "(>Hhead7 & >Htail7 & >Hchain7 & >Htrace7 & >Hauth_op7 & >Hauth_nm7
              & Hfrag_nm7 & >Hauth_dq7 & Hfrag_dq7 & >Hauth_del7 & >Hauth_calls7
              & >Hauth_no_O7 & >Hauth_ls7 & >Hauth_w7 & Hfrag_w7 & >%Hsteps7 & >%Hts_eq7 & >%Hsim7
              & >%Hdummy7 & >%Hnvi7 & >%Hdqi7 & >%Hno_O_inv7 & >%Hcoi7 & >%Hwit7)".
          destruct (decide (tail_val_7 = tail_val)) as [Heq_t|Hne_t].
          *** (* Phase 7 success: [tail] advances to [nd]. *)
             subst tail_val_7.
             wp_cmpxchg_suc.
             (* Find [nd]'s chain position via [Hfrag] + clause 6. *)
             iDestruct (own_valid_2 with "Hauth_op7 Hfrag") as %Hτ_both7.
             apply auth_both_valid_discrete in Hτ_both7 as [Hτ_incl7 Hτ_valid7].
             apply singleton_included_exclusive_l in Hτ_incl7; [|apply _|done].
             rewrite lookup_fmap in Hτ_incl7.
             apply leibniz_equiv in Hτ_incl7.
             apply fmap_Some_1 in Hτ_incl7 as (info_τ7 & Hτ_in_op7 & Hinfo_τ7).
             destruct info_τ7 as [kd7 nd_τ7 lk7]; injection Hinfo_τ7 as <- <- <-.
             pose proof Hsim7 as (Hlen7 & Hdel7 & Hcp_in_ts7 & Hdomsub7 & Hnm_dom7
                                  & Henq_clause7 & Hdeq_clause7 & Hinj7 & Hcorr7
                                  & Hlt_pos7 & _Htbd7 & Hcomp_link7 & _ & Hhead_in7
                                  & Hnm_chain7 & Hsome_at_pos7).
             destruct (Henq_clause7 _ _ _ _ Hτ_in_op7) as (_ & _ & _ & Hpost7).
             destruct (Hpost7 eq_refl) as (l_τ7 & i_τ7 & Hnode_eq7 & Hi_τ_pos7
                                            & Hi_τ_lookup7 & _ & _).
             injection Hnode_eq7 as Hl_τ_eq. subst l_τ7.
             iModIntro.
             iSplitL "Hhead7 Htail7 Hchain7 Htrace7 Hauth_op7 Hauth_nm7
                      Hfrag_nm7 Hauth_dq7 Hfrag_dq7 Hauth_del7 Hauth_calls7
                      Hauth_no_O7 Hauth_ls7 Hauth_w7 Hfrag_w7".
             { iNext.
               iExists nodes_7, del_pref_7, head_val_7, nd, dummy_loc_7,
                 ts_7, s_7, ls_7, op_map_7, node_map_7, dq_map_7, no_O_set_7, witness_map_7.
               iFrame.
               iPureIntro. split_and!.
               - exact Hsteps7.
               - exact Hts_eq7.
               - split_and!.
                 + exact Hlen7.
                 + exact Hdel7.
                 + exact Hcp_in_ts7.
                 + exact Hdomsub7.
                 + exact Hnm_dom7.
                 + exact Henq_clause7.
                 + exact Hdeq_clause7.
                 + exact Hinj7.
                 + exact Hcorr7.
                 + exact Hlt_pos7.
                 + exact _Htbd7.
                 + exact Hcomp_link7.
                 + (* clause 13: tail = nd, at chain position i_τ7 *)
                   exists i_τ7, (Some τ), d.
                   split.
                   * apply lookup_lt_Some in Hi_τ_lookup7. lia.
                   * exact Hi_τ_lookup7.
                 + exact Hhead_in7.
                 + exact Hnm_chain7.
                 + exact Hsome_at_pos7.
               - exact Hdummy7.
               - exact Hnvi7.
               - exact Hdqi7.
               - apply Hno_O_inv7.
               - apply Hno_O_inv7.
               - exact Hcoi7.
               - exact Hwit7. }
             (* === PHASE 8: trace_emit RET-ENQ — dispatched to the
                helper [op_spec_enq_trace_emit] in
                refine_enq_trace.v.  See that file for the full body. === *)
             wp_pures.
             iApply (op_spec_enq_trace_emit
                       γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                       l head tail nd τ d
                       with "Hinv Htrace_inv Hfrag HΦ").
          *** (* Phase 7 failure: tail unchanged. *)
             wp_cmpxchg_fail.
             iModIntro.
             iSplitL "Hhead7 Htail7 Hchain7 Htrace7 Hauth_op7 Hauth_nm7
                      Hfrag_nm7 Hauth_dq7 Hfrag_dq7 Hauth_del7 Hauth_calls7
                      Hauth_no_O7 Hauth_ls7 Hauth_w7 Hfrag_w7".
             { iNext.
               iExists nodes_7, del_pref_7, head_val_7, tail_val_7, dummy_loc_7,
                 ts_7, s_7, ls_7, op_map_7, node_map_7, dq_map_7, no_O_set_7, witness_map_7.
               iFrame.
               iPureIntro. split_and!.
               - exact Hsteps7.
               - exact Hts_eq7.
               - exact Hsim7.
               - exact Hdummy7.
               - exact Hnvi7.
               - exact Hdqi7.
               - apply Hno_O_inv7.
               - apply Hno_O_inv7.
               - exact Hcoi7.
               - exact Hwit7. }
             (* === PHASE 8: trace_emit RET-ENQ — dispatched to the
                helper [op_spec_enq_trace_emit] in
                refine_enq_trace.v.  See that file for the full body. === *)
             wp_pures.
             iApply (op_spec_enq_trace_emit
                       γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                       l head tail nd τ d
                       with "Hinv Htrace_inv Hfrag HΦ").
      + (* tail_val_5 ≠ tail_val: stale tail, recurse via IH. *)
        wp_pures.
        iApply ("IH" with "Hfrag HΦ Hnd_v [Hnd_n]"); first by iExists _.
  Qed.

End bq_skeleton_enq_cont.
