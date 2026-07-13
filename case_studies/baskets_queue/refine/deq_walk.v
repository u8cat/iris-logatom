(* refine_deq_walk.v: helper lemma for the inner [walk] recursion of
  [dequeue], factored out of [op_spec_deq_cont] in
  [refine_deq_cont.v].

  ** Why a separate lemma.

  The implementation of [dequeue] contains a nested recursive function:
  the outer retry loop ([rec: outer ...]) loads [head] and the head's
  next-pointer, then enters an inner walk ([rec: walk iter next ...])
  that traces forward through the marked-prefix of the chain.  Each
  walk iteration sees a different chain position, advancing [iter] one
  step at a time.

  The walk's recursion warrants its own iLöb induction.  The
  (true, Some) case at [refine_deq_cont.v:268] is exactly the entry
  point for this walk: it advances [iter] from [head_val_outer] to
  [l_succ_2] and recurses into the walk.

  ** Walk dispatch.

  Inside the walk body, after loading [iter.next] (mirroring the
  outer body's "phase-2 load"), we case-split on
  [(mark_at del_pref i_iter, succ_at nodes i_iter)]:

  - (true, Some l_succ): [iter.next] is marked.  Recurse with
    [iter := l_succ], [next := !l_succ.next] — Case A below.

  - (false, Some l_succ): [iter.next] is unmarked.  Mark-CAS branch:
    on success, fire [absq_step_lin_deq1] (LIN-DEQ1); on failure,
    recurse to outer.  Case B.

  - (false, None): [iter.next] is unmarked-null (empty queue).  Fire
    [absq_step_lin_deq2] (LIN-DEQ2) and return [NONE].  Case C.

  - (true, None): [iter.next] is marked-null.  Impossible by
    [bq_sim] clause 2 ([del_pref < length nodes]).  Case D.

  Cases B and C ultimately fire the trace_emit and hand off to
  [op_spec_deq_trace_emit].  Case A recurses via the lemma's
  iLöb.  Case A's marked-null and Case B's CAS-fail invoke the outer
  recursion via the [Houter] hypothesis. *)

From iris.algebra Require Import auth excl gmap gset agree mono_nat mono_list.
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

From case_studies.baskets_queue Require Import impl refine.defs refine.deq_trace.

Section bq_skeleton_deq_walk.
  Context `{!traceG Σ, !bqG Σ}.

  Local Notation valid_value := bq_valid_value.
  Local Notation Nbq := Nbq.
  Local Notation bq_inv_body := bq_inv_body.

  (* Post-walk continuation: trace_emit the dequeue's [Ret], then
     return.  Used uniformly for the lemma's WP postcondition and for
     the [outer_v #()] hypothesis. *)
  Definition deq_walk_cont
    `{!heapGS Σ} (l : loc) (τ : positive) (Φ : val → iProp Σ)
    : val → iProp Σ :=
    λ res, (WP (let: "res" := res in
                trace_emit #l #(Z.pos τ) (InjR "res");; "res") {{ Φ }})%I.

  (* Persistent witnesses passed across iLöb iterations:
     - [Hhead_frag_outer]: outer head's [γ_nm] fragment, used by
       Case B's post-LIN-DEQ1 best-effort head CAS.
     - [Hiter_frag]: current iter's [γ_nm] fragment.
     - [Hno_O_outer]: outer head's [γ_no_O] fragment ([extra_no_O]).
     - [Hno_O_iter]: case-split — head case (p_iter =
       head_val_outer, where [extra_no_O] suffices); walked-to case
       (Some τ_iter, with fresh [◯ {[τ_iter]}]).
     - [Hnext]: characterisation of [next_loaded] as one of four
       shapes plus a [γ_nm] fragment for any loc it carries.  Cases:
         - [InjLV #()]: empty-queue (Case C).
         - [InjRV #()]: marked-null (Case D — operationally calls
           outer; abstractly impossible, but we route via [Houter]
           rather than discharging via exfalso).
         - [InjLV #l_succ]: unmarked-pointer (Case B), with
           [γ_nm] fragment.
         - [InjRV #l_succ]: marked-pointer (Case A), with
           [γ_nm] fragment.
     - [Hdel_lb]: [◯MN i_iter_lb] from [γ_del]; combined with the
       no_O-iter witness, lifts "[del_pref ≥ i_iter]" to each
       inv-open.

     The lemma takes [outer_v #() : expr] as the literal expression to
     invoke when we hit "outer #()" inside the walk body.  The
     [Houter] hypothesis is the WP for [outer_v #()] with the same
     post-walk continuation that the lemma's outer WP uses. *)

  Lemma op_spec_deq_walk
    `{!heapGS Σ} (γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w : gname)
    (l head tail : loc)
    (head_val_outer p_iter : loc)
    (τ_h_opt : option positive) (v_h : val)
    (τ_iter_opt : option positive) (v_iter : val)
    (τ : positive) (rng_init : nat)
    (i_iter_lb : nat)
    (next_loaded : val)
    (extra_no_O : gset positive)
    (outer_v : val)
    (Φ : val → iProp Σ) :
    inv Nbq (bq_inv_body γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w head tail l) -∗
    trace_inv l (I_lang_bq) -∗
    own γ (◯ {[τ := Excl {| op_info_kind := OpDeq [] rng_init;
                            op_info_node := None;
                            op_info_linked := false |}]}) -∗
    (* Outer head's persistent γ_nm fragment. *)
    own γ_nm (◯ {[head_val_outer := to_agree
                ((τ_h_opt, v_h) : leibnizO node_info)]}) -∗
    (* Current iter's persistent γ_nm fragment. *)
    own γ_nm (◯ {[p_iter := to_agree
                ((τ_iter_opt, v_iter) : leibnizO node_info)]}) -∗
    (* Outer head's no_O fragment.  Equals [{[τ_h]}] when τ_h_opt =
       Some τ_h, [∅] when τ_h_opt = None. *)
    own γ_no_O (◯ extra_no_O) -∗
    ⌜extra_no_O = match τ_h_opt with
                  | Some t => {[t]}
                  | None => ∅
                  end⌝ -∗
    (* "p_iter ∉ absq_O" witness. *)
    ((⌜p_iter = head_val_outer⌝) ∨
     (∃ τ_iter, ⌜τ_iter_opt = Some τ_iter⌝ ∗
                 own γ_no_O (◯ ({[τ_iter]} : gsetUR positive)))) -∗
    own γ_del (◯MN i_iter_lb) -∗
    (* [next_loaded] characterisation: 3 shapes (Case C / [InjLV #()]
       is unreachable because Case A's (false, None) sub-case fires
       LIN-DEQ2 inline at the load's inv-open, then operationally
       wp_pures through the walk recursion + match dispatch into NONE
       without invoking the walk lemma's IH).  Cases:
         - [InjRV #()]: marked-null (Case D — operationally calls
           outer; abstractly impossible, routed via Houter).
         - [InjLV #l_succ]: unmarked-pointer (Case B), with γ_nm.
         - [InjRV #l_succ]: marked-pointer (Case A), with γ_nm and
           γ_no_O for [τ_succ] (sticky removal). *)
    ( ⌜next_loaded = InjRV #()⌝
    ∨ (∃ (τ_succ : positive) (l_succ : loc) (v_succ : val),
         ⌜next_loaded = InjLV #l_succ⌝ ∗
         own γ_nm (◯ {[l_succ := to_agree
                       ((Some τ_succ, v_succ) : leibnizO node_info)]}))
    ∨ (∃ (τ_succ : positive) (l_succ : loc) (v_succ : val),
         ⌜next_loaded = InjRV #l_succ⌝ ∗
         own γ_nm (◯ {[l_succ := to_agree
                       ((Some τ_succ, v_succ) : leibnizO node_info)]}) ∗
         own γ_no_O (◯ ({[τ_succ]} : gsetUR positive)))) -∗
    (* Outer Löb hypothesis: invoking [outer_v #()] re-establishes the
       full outer-loop WP with the post-walk trace_emit
       continuation. *)
    ▷ (own γ (◯ {[τ := Excl {| op_info_kind := OpDeq [] rng_init;
                                op_info_node := None;
                                op_info_linked := false |}]}) -∗
       (∀ v : val, True -∗ Φ v) -∗
       WP outer_v #()
       {{ deq_walk_cont l τ Φ }}) -∗
    (∀ v : val, True -∗ Φ v) -∗
    WP (rec: "walk" "iter" "next" :=
          match: "next" with
            InjL "p" =>
              if: "p" = #() then NONE
              else
                let: "v" := !"p" in
                if: CAS ("iter" +ₗ #1) "next" (InjR "p") then
                  CAS #head #head_val_outer "p" ;;
                  SOME "v"
                else
                  outer_v #()
          | InjR "p" =>
              if: "p" = #() then outer_v #()
              else
                let: "next2" := !("p" +ₗ #1) in
                "walk" "p" "next2"
          end)%V #p_iter next_loaded
    {{ deq_walk_cont l τ Φ }}.
  Proof.
    iIntros "#Hinv #Htrace_inv Hfrag #Hhead_frag_outer #Hiter_frag #Hno_O_outer
             %Hextra_no_O Hno_O_iter Hdel_lb Hnext Houter HΦ".
    (* Revert the iter-changing hypotheses so the iLöb IH is
       universally quantified over them. *)
    iRevert (p_iter τ_iter_opt v_iter i_iter_lb next_loaded)
            "Hiter_frag Hno_O_iter Hdel_lb Hnext Hfrag HΦ Houter".
    iLöb as "IH_walk".
    iIntros (p_iter τ_iter_opt v_iter i_iter_lb next_loaded).
    iIntros "#Hiter_frag Hno_O_iter Hdel_lb Hnext Hfrag HΦ Houter".
    wp_pures.
    (* Dispatch on next_loaded's structure via [Hnext]. *)
    iDestruct "Hnext" as "[%H_D | [(%τ_succ & %l_succ & %v_succ
                          & %H_B & #Hl_succ_frag) |
                          (%τ_succ & %l_succ & %v_succ
                          & %H_A & #Hl_succ_frag & #Hno_O_τ_succ_in)]]".
    - (* Case D: next_loaded = InjRV #() — abstractly impossible,
         operationally calls outer #().  Route via [Houter]. *)
      subst next_loaded.
      wp_pures.
      iApply ("Houter" with "Hfrag HΦ").
    - (* Case B: next_loaded = InjLV #l_succ — mark CAS / LIN-DEQ1.
         Steps:
           1. wp_pures past [if l_succ = #()] (false, l_succ is a loc).
           2. Load !l_succ (the value cell): open inv, find l_succ via
              Hl_succ_frag, extract value cell, wp_load, close inv.
           3. Mark CAS at iter.next: open inv, find iter at i_iter_n via
              Hiter_frag, dispatch on (mark_at, succ_at) at i_iter_n.
              Sub-cases:
              - (true, Some): CAS fails (iter already marked).  Close
                inv, outer recurse via Houter.
              - (true, None): impossible (clause 2 contradiction).
              - (false, Some l_succ'): if l_succ' = l_succ, CAS
                succeeds → LIN-DEQ1 firing + post-LIN-DEQ1 head CAS +
                trace_emit.  Else CAS fails (different successor),
                close inv, outer recurse.
              - (false, None): CAS fails (iter.next is null).  Close
                inv, outer recurse. *)
      subst next_loaded.
      wp_pures.
      (* Step 2: load !l_succ. *)
      wp_bind (! _)%E.
      iInv Nbq as (nodes_a del_pref_a head_val_a tail_val_a dummy_loc_a
                   ts_a s_a ls_a op_map_a node_map_a dq_map_a
                   no_O_set_a witness_map_a)
        "(>Hhead_a & >Htail_a & Hchain_a & >Htrace_a & >Hauth_op_a
          & >Hauth_nm_a & Hfrag_nm_a & >Hauth_dq_a & Hfrag_dq_a
          & >Hauth_del_a & >Hauth_calls_a & >Hauth_no_O_a & >Hauth_ls_a
          & >Hauth_w_a & Hfrag_w_a & >%Hsteps_a & >%Hts_eq_a & >%Hsim_a
          & >%Hdummy_a & >%Hnvi_a & >%Hdqi_a & >%Hno_O_inv_a & >%Hcoi_a
          & >%Hwit_a)".
      iDestruct (own_valid_2 with "Hauth_nm_a Hl_succ_frag") as %Hagree_a.
      apply auth_both_valid_discrete in Hagree_a as [Hincl_a _].
      apply singleton_included_l in Hincl_a as (av_a & Hav_lookup_a & Hav_incl_a).
      rewrite /to_nodemap lookup_fmap in Hav_lookup_a.
      apply fmap_Some_equiv in Hav_lookup_a as (info_a & Hnm_l_succ_a & Hav_eq_a).
      rewrite Hav_eq_a in Hav_incl_a. rewrite Some_included in Hav_incl_a.
      assert ((Some τ_succ, v_succ) = info_a :> leibnizO node_info)
        as Hinfo_a_eq.
      { destruct Hav_incl_a as [Heq|Hin].
        - by apply (inj to_agree), leibniz_equiv in Heq.
        - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
      rewrite -Hinfo_a_eq in Hnm_l_succ_a.
      clear Hav_eq_a Hav_incl_a Hinfo_a_eq info_a.
      pose proof Hsim_a as (_ & _ & _ & _ & Hnm_dom_a & _ & _ & _ & _ & _
                          & _ & _ & _ & _ & Hnm_chain_a & Hsome_at_pos_a).
      destruct (Hnm_dom_a _ _ _ Hnm_l_succ_a) as (i_succ_a & Hi_succ_a_lookup).
      iDestruct (bq_chain_lookup_acc _ del_pref_a i_succ_a l_succ
                   (Some τ_succ) v_succ Hi_succ_a_lookup with "Hchain_a")
        as "[Hv_a [Hn_a HW_a]]".
      simpl. wp_load.
      iDestruct ("HW_a" with "[$Hv_a $Hn_a]") as "Hchain_a".
      iModIntro.
      iSplitL "Hhead_a Htail_a Hchain_a Htrace_a Hauth_op_a Hauth_nm_a
               Hfrag_nm_a Hauth_dq_a Hfrag_dq_a Hauth_del_a Hauth_calls_a
               Hauth_no_O_a Hauth_ls_a Hauth_w_a Hfrag_w_a".
      { iNext. iExists nodes_a, del_pref_a, head_val_a, tail_val_a,
          dummy_loc_a, ts_a, s_a, ls_a, op_map_a, node_map_a, dq_map_a,
          no_O_set_a, witness_map_a.
        iFrame. iPureIntro. split_and!; auto.
        - apply Hno_O_inv_a.
        - apply Hno_O_inv_a. }
      wp_pures.
      (* Step 3: mark CAS at iter.next.  Open inv, find iter at i_iter_b. *)
      wp_bind (CmpXchg _ _ _).
      iInv Nbq as (nodes_b del_pref_b head_val_b tail_val_b dummy_loc_b
                   ts_b s_b ls_b op_map_b node_map_b dq_map_b
                   no_O_set_b witness_map_b)
        "(>Hhead_b & >Htail_b & Hchain_b & >Htrace_b & >Hauth_op_b
          & >Hauth_nm_b & Hfrag_nm_b & >Hauth_dq_b & Hfrag_dq_b
          & >Hauth_del_b & >Hauth_calls_b & >Hauth_no_O_b & >Hauth_ls_b
          & >Hauth_w_b & Hfrag_w_b & >%Hsteps_b & >%Hts_eq_b & >%Hsim_b
          & >%Hdummy_b & >%Hnvi_b & >%Hdqi_b & >%Hno_O_inv_b & >%Hcoi_b
          & >%Hwit_b)".
      (* Find iter (= p_iter) at i_iter_b. *)
      iDestruct (own_valid_2 with "Hauth_nm_b Hiter_frag") as %Hagree_b.
      apply auth_both_valid_discrete in Hagree_b as [Hincl_b _].
      apply singleton_included_l in Hincl_b as (av_b & Hav_lookup_b & Hav_incl_b).
      rewrite /to_nodemap lookup_fmap in Hav_lookup_b.
      apply fmap_Some_equiv in Hav_lookup_b as (info_b & Hnm_iter_b & Hav_eq_b).
      rewrite Hav_eq_b in Hav_incl_b. rewrite Some_included in Hav_incl_b.
      assert ((τ_iter_opt, v_iter) = info_b :> leibnizO node_info)
        as Hinfo_b_eq.
      { destruct Hav_incl_b as [Heq|Hin].
        - by apply (inj to_agree), leibniz_equiv in Heq.
        - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
      rewrite -Hinfo_b_eq in Hnm_iter_b.
      clear Hav_eq_b Hav_incl_b Hinfo_b_eq info_b.
      pose proof Hsim_b as (Hlen_b & Hdel_b & Hcp_in_ts_b & Hdomsub_b
                          & Hnm_dom_b & Henq_clause_b & Hdeq_clause_b
                          & Hinj_b & Hcorr_b & Hlt_pos_b & _Htbd_b
                          & Hcomp_link_b & Htail_in_b & Hhead_in_b
                          & Hnm_chain_b & Hsome_at_pos_b).
      destruct (Hnm_dom_b _ _ _ Hnm_iter_b) as (i_iter_b & Hi_iter_b_lookup).
      (* Dispatch on (mark_at, succ_at) at i_iter_b. *)
      destruct (mark_at del_pref_b i_iter_b) eqn:Hmark_b;
      destruct (succ_at nodes_b i_iter_b) as [l_succ_b|] eqn:Hsucc_b.
      + (* (true, Some l_succ_b): iter.next is marked.  CAS fails
           (heap value is InjRV #l_succ_b, expected InjLV #l_succ). *)
        iDestruct (bq_chain_lookup_acc _ del_pref_b i_iter_b p_iter
                     τ_iter_opt v_iter Hi_iter_b_lookup with "Hchain_b")
          as "[Hv_b [Hn_b HW_b]]".
        iEval (rewrite Hmark_b Hsucc_b /next_value_of) in "Hn_b".
        wp_cmpxchg_fail.
        iDestruct ("HW_b" with "[Hv_b Hn_b]") as "Hchain_b".
        { rewrite Hmark_b Hsucc_b /next_value_of. iFrame. }
        iModIntro.
        iSplitL "Hhead_b Htail_b Hchain_b Htrace_b Hauth_op_b Hauth_nm_b
                 Hfrag_nm_b Hauth_dq_b Hfrag_dq_b Hauth_del_b Hauth_calls_b
                 Hauth_no_O_b Hauth_ls_b Hauth_w_b Hfrag_w_b".
        { iNext. iExists nodes_b, del_pref_b, head_val_b, tail_val_b,
            dummy_loc_b, ts_b, s_b, ls_b, op_map_b, node_map_b, dq_map_b,
            no_O_set_b, witness_map_b.
          iFrame. iPureIntro. split_and!; auto.
          - apply Hno_O_inv_b.
          - apply Hno_O_inv_b. }
        wp_pures.
        iApply ("Houter" with "Hfrag HΦ").
      + (* (true, None): iter.next is marked-null.  Impossible. *)
        exfalso.
        rewrite /mark_at in Hmark_b.
        apply bool_decide_eq_true in Hmark_b.
        rewrite /succ_at in Hsucc_b.
        destruct (nodes_b !! (i_iter_b + 1)%nat) eqn:Hnext_b; first discriminate.
        apply lookup_ge_None_1 in Hnext_b. lia.
      + (* (false, Some l_succ_b): unmarked-pointer.  CAS dispatch:
           - l_succ_b = l_succ: success, fire LIN-DEQ1.
           - l_succ_b ≠ l_succ: fail. *)
        destruct (decide (l_succ_b = l_succ)) as [->|Hne_succ].
        * (* CAS SUCCESS — LIN-DEQ1 firing.  Mirror the inline LIN-DEQ1
             in [refine_deq_cont.v] but with [head_val → p_iter],
             [Hhead_frag → Hiter_frag], [Hno_O_frag → Hno_O_iter +
             Hno_O_outer (case-split)]. *)
          iDestruct (bq_chain_split_at _ del_pref_b p_iter
                       τ_iter_opt v_iter i_iter_b Hi_iter_b_lookup
                       with "Hchain_b")
            as "(Hpref_b & Hv_b & Hn_b & Hsuf_b)".
          iEval (rewrite Hmark_b Hsucc_b /next_value_of) in "Hn_b".
          wp_cmpxchg_suc.
          (* Step 1: del_pref_b = i_iter_b. *)
          assert (del_pref_b ≤ i_iter_b)%nat as Hdel_le_i_iter_b.
          { rewrite /mark_at in Hmark_b.
            apply bool_decide_eq_false in Hmark_b. lia. }
          iAssert (⌜i_iter_b ≤ del_pref_b⌝)%I as %Hi_iter_b_le_del.
          { iDestruct "Hno_O_iter" as "[%Hhead_eq | (%τ_iter & %Hτ_iter_eq & #Hno_O_τ_iter)]".
            - (* Head case: p_iter = head_val_outer. *)
              destruct τ_iter_opt as [τ_iter|] eqn:Hτ_eq.
              + (* τ_h = Some τ_iter (via Hhead_eq + outer fragment). *)
                assert (1 ≤ i_iter_b)%nat as Hi_iter_b_pos.
                { destruct (decide (1 ≤ i_iter_b)%nat) as [|Hlt]; first done.
                  assert (i_iter_b = 0%nat) as -> by lia.
                  rewrite Hdummy_b in Hi_iter_b_lookup.
                  injection Hi_iter_b_lookup as _ Habs _. discriminate. }
                (* From Hhead_eq, p_iter = head_val_outer; so τ_iter_opt = τ_h_opt. *)
                subst p_iter.
                (* Derive (τ_h_opt, v_h) = (τ_iter_opt, v_iter) via Hiter_frag = Hhead_frag_outer. *)
                iAssert (⌜τ_h_opt = τ_iter_opt ∧ v_h = v_iter⌝)%I as %[-> ->].
                { iDestruct (own_valid_2 with "Hhead_frag_outer Hiter_frag")
                    as %Hag.
                  rewrite -auth_frag_op singleton_op in Hag.
                  apply auth_frag_valid_1 in Hag.
                  rewrite singleton_valid in Hag.
                  apply to_agree_op_inv_L in Hag.
                  iPureIntro. injection Hag as -> ->. done. }
                (* extra_no_O = {τ_h_real} where τ_h_opt = Some τ_h_real. *)
                rewrite Hτ_eq /= in Hextra_no_O.
                iDestruct (own_valid_2 with "Hauth_no_O_b Hno_O_outer")
                  as %Hno_O_both_b.
                apply auth_both_valid_discrete in Hno_O_both_b as [Hno_O_incl_b _].
                apply gset_included in Hno_O_incl_b.
                rewrite Hextra_no_O in Hno_O_incl_b.
                assert (τ_iter ∈ no_O_set_b) as Hτ_iter_in_no_O
                  by (clear -Hno_O_incl_b; set_solver).
                assert (τ_iter ∉ s_b.(absq_O)) as Hτ_iter_not_O
                  by (destruct Hno_O_inv_b as [_ Hdisj];
                      clear -Hdisj Hτ_iter_in_no_O; set_solver).
                destruct (Hcorr_b _ _ _ _ Hi_iter_b_pos Hi_iter_b_lookup)
                  as (_ & _ & Hin_iff).
                iPureIntro.
                destruct (decide (del_pref_b < i_iter_b)%nat) as [Hlt|]; last lia.
                exfalso. apply Hτ_iter_not_O. by apply Hin_iff.
              + (* τ_h_opt = None, head case: i_iter_b = 0 by Hdummy. *)
                assert (¬ (1 ≤ i_iter_b)%nat) as Hi_iter_b_zero.
                { intros Hge.
                  (* Hhead_eq says p_iter = head_val_outer, so τ_iter_opt = τ_h_opt = None. *)
                  destruct (Hsome_at_pos_b _ _ _ _ Hge Hi_iter_b_lookup)
                    as [τ' Habs]. discriminate. }
                iPureIntro. lia.
            - (* Walked case: τ_iter_opt = Some τ_iter ∗ ◯ {[τ_iter]}. *)
              subst τ_iter_opt.
              assert (1 ≤ i_iter_b)%nat as Hi_iter_b_pos.
              { destruct (decide (1 ≤ i_iter_b)%nat) as [|Hlt]; first done.
                assert (i_iter_b = 0%nat) as -> by lia.
                rewrite Hdummy_b in Hi_iter_b_lookup.
                injection Hi_iter_b_lookup as _ Habs _. discriminate. }
              iDestruct (own_valid_2 with "Hauth_no_O_b Hno_O_τ_iter")
                as %Hno_O_both_b.
              apply auth_both_valid_discrete in Hno_O_both_b as [Hno_O_incl_b _].
              apply gset_included in Hno_O_incl_b.
              assert (τ_iter ∈ no_O_set_b) as Hτ_iter_in_no_O
                by (clear -Hno_O_incl_b; set_solver).
              assert (τ_iter ∉ s_b.(absq_O)) as Hτ_iter_not_O
                by (destruct Hno_O_inv_b as [_ Hdisj];
                    clear -Hdisj Hτ_iter_in_no_O; set_solver).
              destruct (Hcorr_b _ _ _ _ Hi_iter_b_pos Hi_iter_b_lookup)
                as (_ & _ & Hin_iff).
              iPureIntro.
              destruct (decide (del_pref_b < i_iter_b)%nat) as [Hlt|]; last lia.
              exfalso. apply Hτ_iter_not_O. by apply Hin_iff. }
          assert (del_pref_b = i_iter_b) as Hdel_eq_i_iter_b by lia.
          (* Step 2: identify τ_succ at i_iter_b + 1 via succ_at + clause 16. *)
          rewrite /succ_at in Hsucc_b.
          destruct (nodes_b !! (i_iter_b + 1)%nat) as [[[lk_b τ_succ_b_opt] v_succ_b]|]
            eqn:Hnext_lookup_b; last discriminate.
          simpl in Hsucc_b. injection Hsucc_b as ->.
          assert (Hi_succ_b_pos : (1 ≤ i_iter_b + 1)%nat) by lia.
          destruct (Hsome_at_pos_b _ _ _ _ Hi_succ_b_pos Hnext_lookup_b)
            as [τ_e ->].
          (* Step 2b: reconcile (Some τ_e, v_succ_b) with Hl_succ_frag's (Some τ_succ, v_succ). *)
          pose proof (Hnm_chain_b _ _ _ _ Hnext_lookup_b) as Hnm_l_succ_b.
          iDestruct (own_valid_2 with "Hauth_nm_b Hl_succ_frag") as %Hagree_l_succ.
          apply auth_both_valid_discrete in Hagree_l_succ as [Hincl_l_succ _].
          apply singleton_included_l in Hincl_l_succ as (av_l & Hav_l_lookup & Hav_l_incl).
          rewrite /to_nodemap lookup_fmap in Hav_l_lookup.
          apply fmap_Some_equiv in Hav_l_lookup as (info_l & Hnm_l_succ_b_2 & Hav_l_eq).
          rewrite Hav_l_eq in Hav_l_incl. rewrite Some_included in Hav_l_incl.
          assert ((Some τ_succ, v_succ) = info_l :> leibnizO node_info) as Hinfo_l_eq.
          { destruct Hav_l_incl as [Heq|Hin].
            - by apply (inj to_agree), leibniz_equiv in Heq.
            - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
          rewrite -Hinfo_l_eq in Hnm_l_succ_b_2.
          rewrite Hnm_l_succ_b in Hnm_l_succ_b_2.
          injection Hnm_l_succ_b_2 as Hτ_eq Hv_eq.
          subst τ_e v_succ_b.
          (* Step 3: extract op_map info via Hfrag. *)
          iDestruct (own_valid_2 with "Hauth_op_b Hfrag") as %Hτ_both.
          apply auth_both_valid_discrete in Hτ_both as [Hτ_incl Hτ_valid].
          apply singleton_included_exclusive_l in Hτ_incl; [|apply _|done].
          rewrite lookup_fmap in Hτ_incl.
          apply leibniz_equiv in Hτ_incl.
          apply fmap_Some_1 in Hτ_incl as (info_τ & Hτ_in_op_b & Hinfo_τ).
          destruct info_τ as [kd_τ nd_τ lk_τ];
            injection Hinfo_τ as <- <- <-.
          destruct (Hdeq_clause_b _ _ _ _ _ Hτ_in_op_b) as (_ & Hcp_τ_R1_pre & _).
          specialize (Hcp_τ_R1_pre eq_refl).
          (* Step 4: γ_op update — set linked := true. *)
          set (new_τ_info := {| op_info_kind := OpDeq [] rng_init;
                                op_info_node := None;
                                op_info_linked := true |}).
          iMod (own_update_2 _ _ _
                  (● to_opmap (<[τ := new_τ_info]> op_map_b)
                     ⋅ ◯ {[τ := Excl new_τ_info]})
                  with "Hauth_op_b Hfrag") as "[Hauth_op_b Hfrag]".
          { apply auth_update.
            rewrite /to_opmap fmap_insert.
            apply: singleton_local_update.
            { rewrite lookup_fmap Hτ_in_op_b //. }
            by apply exclusive_local_update. }
          (* Step 5: τ_succ ∈ absq_min(O, lt) — minimality argument. *)
          assert (Hτ_succ_in_O : τ_succ ∈ s_b.(absq_O)).
          { destruct (Hcorr_b _ _ _ _ Hi_succ_b_pos Hnext_lookup_b)
              as (_ & _ & Hin_iff_succ).
            apply Hin_iff_succ. lia. }
          assert (Hτ_succ_min : τ_succ ∈ absq_min s_b.(absq_O) s_b.(absq_lt)).
          { rewrite /absq_min elem_of_filter. split; [|exact Hτ_succ_in_O].
            intros k Hk_in_O.
            intros Hkin_lt.
            destruct (Hlt_pos_b _ _ Hkin_lt)
              as (p_k & l_k & d_k & Hp_k_pos & Hp_k_lookup & Hp_imp).
            specialize (Hp_imp (i_iter_b + 1)%nat l_succ v_succ
                                Hi_succ_b_pos Hnext_lookup_b).
            assert (Hp_k_le_i : (p_k ≤ i_iter_b)%nat) by lia.
            destruct (Hcorr_b _ _ _ _ Hp_k_pos Hp_k_lookup)
              as (_ & _ & Hin_iff_k).
            apply Hin_iff_k in Hk_in_O. lia. }
          destruct (Hcorr_b _ _ _ _ Hi_succ_b_pos Hnext_lookup_b)
            as (_ & (f_succ_b & Hℓ_τ_succ_b) & _).
          (* Step 6: dq_map_b !! τ = None. *)
          assert (absq_wf valid_value s_b) as Hwf_b.
          { eapply absq_wf_steps; [exact Hsteps_b|apply absq_wf_init]. }
          assert (dq_map_b !! τ = None) as Hdq_τ_none.
          { destruct (dq_map_b !! τ) as [v_old|] eqn:Heq; last done.
            exfalso. pose proof (Hdqi_b _ _ Heq) as Hrv_τ.
            destruct (absq_wf_rv _ _ Hwf_b τ (mk_is_Some _ _ Hrv_τ))
              as [Hcp|Hcp]; rewrite Hcp_τ_R1_pre in Hcp; discriminate. }
          (* Step 7: γ_dq update — record SOMEV v_succ. *)
          iMod (own_update_2 _ _ _
                  (● to_dqmap (<[τ := SOMEV v_succ]> dq_map_b)
                     ⋅ ◯ to_dqmap (<[τ := SOMEV v_succ]> dq_map_b))
                  with "Hauth_dq_b Hfrag_dq_b") as "[Hauth_dq_b Hfrag_dq_b]".
          { apply auth_update.
            rewrite /to_dqmap !fmap_insert.
            apply: alloc_local_update; [|done].
            rewrite lookup_fmap Hdq_τ_none //. }
          iDestruct (own_mono _ _ (◯ {[τ := to_agree (SOMEV v_succ)]}) with "Hfrag_dq_b")
            as "#Hdq_τ_frag".
          { apply auth_frag_mono. rewrite /to_dqmap.
            apply singleton_included_l.
            exists (to_agree (SOMEV v_succ)). split.
            - rewrite lookup_fmap lookup_insert_eq //.
            - reflexivity. }
          (* Step 8: γ_ls append. *)
          iMod (own_update _ _
                  (●ML (ls_b ++ [(τ, ALinDeq (SOMEV v_succ))]
                         : list (leibnizO (positive * absq_action))))
                  with "Hauth_ls_b") as "Hauth_ls_b".
          { apply mono_list_update. by apply prefix_app_r. }
          (* Step 9: γ_del update — advance del_pref_b → i_iter_b + 1. *)
          iMod (own_update _ _ (●MN (i_iter_b + 1)%nat)
                  with "Hauth_del_b") as "Hauth_del_b".
          { apply mono_nat_update. lia. }
          (* Step 9b: γ_no_O update — record τ_succ. *)
          iMod (own_update _ _
                  (● (no_O_set_b ∪ {[τ_succ]} : gsetUR positive)
                     ⋅ ◯ (no_O_set_b ∪ {[τ_succ]} : gsetUR positive)
                    : authR (gsetUR positive))
                  with "Hauth_no_O_b") as "[Hauth_no_O_b #Hno_O_full_τ_succ]".
          { apply auth_update_alloc, gset_local_update.
            apply union_subseteq_l. }
          iAssert (own γ_no_O (◯ ({[τ_succ]} : gsetUR positive)))
            as "#Hno_O_τ_succ_frag".
          { iApply (own_mono with "Hno_O_full_τ_succ").
            apply auth_frag_mono. apply gset_included.
            apply union_subseteq_r. }
          iClear "Hno_O_full_τ_succ".
          (* Step 10: rebuild bq_chain at i_iter_b + 1. *)
          assert (Hsucc_b_eq : succ_at nodes_b i_iter_b = Some l_succ).
          { rewrite /succ_at Hnext_lookup_b //. }
          assert (Hmark_new : mark_at (i_iter_b + 1)%nat i_iter_b = true).
          { rewrite /mark_at. apply bool_decide_eq_true. lia. }
          assert (Hi_lookup_del : nodes_b !! del_pref_b = Some (p_iter, τ_iter_opt, v_iter)).
          { rewrite Hdel_eq_i_iter_b. exact Hi_iter_b_lookup. }
          iAssert (bq_chain nodes_b (i_iter_b + 1)%nat)
            with "[Hpref_b Hv_b Hn_b Hsuf_b]" as "Hchain_b'".
          { rewrite -Hdel_eq_i_iter_b.
            iApply (bq_chain_advance _ del_pref_b p_iter τ_iter_opt v_iter
                      Hi_lookup_del).
            iSplitL "Hpref_b".
            { rewrite Hdel_eq_i_iter_b. iFrame. }
            iSplitL "Hv_b"; first iFrame.
            iSplitL "Hn_b".
            { rewrite Hdel_eq_i_iter_b Hmark_new Hsucc_b_eq /next_value_of.
              iFrame. }
            rewrite Hdel_eq_i_iter_b. iFrame "Hsuf_b". }
          (* Step 11: close inv with LIN-DEQ1 successor state. *)
          destruct s_b as [O_b lt_b ℓ_b rv_b cp_b]; simpl in *.
          iModIntro.
          iSplitL "Hhead_b Htail_b Hchain_b' Htrace_b Hauth_op_b Hauth_nm_b
                   Hfrag_nm_b Hauth_dq_b Hfrag_dq_b Hauth_del_b Hauth_calls_b
                   Hauth_no_O_b Hauth_ls_b Hauth_w_b Hfrag_w_b".
          { iNext.
            iExists nodes_b, (i_iter_b + 1)%nat, head_val_b, tail_val_b,
              dummy_loc_b, ts_b,
              {| absq_O := O_b ∖ {[τ_succ]};
                 absq_lt := absq_remove lt_b τ_succ;
                 absq_l := ℓ_b;
                 absq_rv := <[τ := SOMEV v_succ]> rv_b;
                 absq_cp := <[τ := R2]> cp_b |},
              (ls_b ++ [(τ, ALinDeq (SOMEV v_succ))]),
              (<[τ := new_τ_info]> op_map_b), node_map_b,
              (<[τ := SOMEV v_succ]> dq_map_b),
              (no_O_set_b ∪ {[τ_succ]}), witness_map_b.
            iFrame "Hhead_b Htail_b Hchain_b' Htrace_b Hauth_op_b Hauth_nm_b
                    Hfrag_nm_b Hauth_dq_b Hfrag_dq_b Hauth_del_b Hauth_ls_b
                    Hauth_no_O_b Hauth_w_b Hfrag_w_b".
            assert (τ ∈ dom cp_b) as Hτ_in_cp_b
              by (apply elem_of_dom; eexists; exact Hcp_τ_R1_pre).
            rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre)).
            iFrame "Hauth_calls_b".
            iPureIntro. split_and!.
            - eapply lts_steps_app; [exact Hsteps_b|].
              eapply lts_steps_cons; [|apply lts_steps_nil].
              apply absq_step_lin_deq1 with (f := f_succ_b);
                [exact Hcp_τ_R1_pre|exact Hτ_succ_min|exact Hℓ_τ_succ_b].
            - rewrite Hts_eq_b /trace_of_absq_labels map_app /= filter_app.
              rewrite filter_cons_False; [by rewrite app_nil_r|].
              by compute.
            - split_and!; simpl.
              + exact Hlen_b.
              + apply lookup_lt_Some in Hnext_lookup_b. lia.
              + rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre)).
                exact Hcp_in_ts_b.
              + rewrite !dom_insert_L.
                clear -Hdomsub_b Hτ_in_cp_b. set_solver.
              + exact Hnm_dom_b.
              + intros τ' d' node' linked' Hop'.
                destruct (decide (τ' = τ)) as [->|Hne].
                { rewrite lookup_insert_eq in Hop'.
                  injection Hop' as Habs. discriminate. }
                rewrite lookup_insert_ne in Hop'; last done.
                destruct (Henq_clause_b _ _ _ _ Hop')
                  as (Hcp & Hℓ & Hpre & Hpost).
                split_and!.
                { rewrite lookup_insert_ne; [exact Hcp|done]. }
                { exact Hℓ. }
                { intros Hlinked.
                  destruct (decide (τ' = τ_succ)) as [->|Hne_τ_succ].
                  - exfalso.
                    pose proof (Hcoi_b _ _ _ _ Hi_succ_b_pos Hnext_lookup_b
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
                  destruct (decide (τ' = τ_succ)) as [->|Hne_τ_succ].
                  - pose proof (Hinj_b _ _ _ _ _ _ _ Hi_e_pos Hi_succ_b_pos
                                  Hi_e_lookup Hnext_lookup_b).
                    subst i_e.
                    rewrite elem_of_difference. split.
                    + intros [_ Habs]. exfalso. apply Habs.
                      apply elem_of_singleton. reflexivity.
                    + lia.
                  - rewrite elem_of_difference. split.
                    + intros [HinO _]. apply Hin_iff_e in HinO.
                      assert (i_e ≠ i_iter_b + 1)%nat as Hi_ne.
                      { intros ->. apply Hne_τ_succ.
                        rewrite Hnext_lookup_b in Hi_e_lookup. congruence. }
                      lia.
                    + intros Hlt.
                      assert (i_e ≠ i_iter_b + 1)%nat as Hi_ne by lia.
                      assert (del_pref_b < i_e)%nat by lia.
                      split.
                      * by apply Hin_iff_e.
                      * clear -Hne_τ_succ. set_solver. }
              + intros τ' obs' rng' node' linked' Hop'.
                destruct (decide (τ' = τ)) as [->|Hne].
                * rewrite lookup_insert_eq in Hop'.
                  injection Hop' as <- <- <- <-.
                  split_and!.
                  { reflexivity. }
                  { intros [=]. }
                  { intros _. rewrite lookup_insert_eq. split; first done.
                    exists (SOMEV v_succ). by rewrite lookup_insert_eq. }
                * rewrite lookup_insert_ne in Hop'; last done.
                  destruct (Hdeq_clause_b _ _ _ _ _ Hop') as (Hnone & Hpre & Hpost).
                  split_and!.
                  { exact Hnone. }
                  { intros Hb. rewrite lookup_insert_ne; [|done]. by apply Hpre. }
                  { intros Hb. destruct (Hpost Hb) as (Hcp_R2' & v_rv' & Hrv_v').
                    split.
                    - rewrite lookup_insert_ne; [exact Hcp_R2'|done].
                    - exists v_rv'. rewrite lookup_insert_ne; [exact Hrv_v'|done]. }
              + exact Hinj_b.
              + intros i l_i τ_i v_i Hi_pos Hi_lookup.
                destruct (Hcorr_b _ _ _ _ Hi_pos Hi_lookup)
                  as (Hnm_l & Hℓ_τ_i & Hin_iff).
                split_and!.
                * exact Hnm_l.
                * exact Hℓ_τ_i.
                * destruct (decide (τ_i = τ_succ)) as [->|Hne_τ].
                  -- pose proof (Hinj_b _ _ _ _ _ _ _ Hi_pos Hi_succ_b_pos
                                   Hi_lookup Hnext_lookup_b).
                     subst i.
                     rewrite elem_of_difference. split.
                     ++ intros [_ Habs]. exfalso. apply Habs.
                        apply elem_of_singleton. reflexivity.
                     ++ lia.
                  -- assert (i ≠ i_iter_b + 1)%nat as Hi_ne.
                     { intros ->. apply Hne_τ.
                       rewrite Hnext_lookup_b in Hi_lookup. congruence. }
                     rewrite elem_of_difference.
                     split.
                     ++ intros [HinO _]. apply Hin_iff in HinO. lia.
                     ++ intros Hlt.
                        assert (del_pref_b < i)%nat by lia.
                        split.
                        ** by apply Hin_iff.
                        ** clear -Hne_τ. set_solver.
              + intros k k_e Hkk.
                rewrite /absq_remove elem_of_filter /= in Hkk.
                destruct Hkk as [_ Hkk_lt].
                exact (Hlt_pos_b _ _ Hkk_lt).
              + done.
              + exact Hcomp_link_b.
              + exact Htail_in_b.
              + (* clause 14: head in marked prefix. *)
                destruct Hhead_in_b as (i_h_old & τ_h_old & v_h_old & Hi_h_le_old & Hhead_at_old).
                exists i_h_old, τ_h_old, v_h_old. split.
                * lia.
                * exact Hhead_at_old.
              + exact Hnm_chain_b.
              + exact Hsome_at_pos_b.
            - exact Hdummy_b.
            - exact Hnvi_b.
            - intros τ' v Hlk.
              destruct (decide (τ' = τ)) as [->|Hne].
              { rewrite lookup_insert_eq in Hlk. injection Hlk as <-.
                by rewrite lookup_insert_eq. }
              rewrite lookup_insert_ne in Hlk; last done.
              rewrite lookup_insert_ne; last done.
              by apply Hdqi_b.
            - simpl.
              destruct Hno_O_inv_b as [Hsub _].
              destruct Hwf_b as [Hwf_dom _].
              simpl in Hwf_dom.
              assert (τ_succ ∈ dom ℓ_b) as Hτ_succ_in_ℓ
                by (apply elem_of_dom; eexists; exact Hℓ_τ_succ_b).
              clear -Hsub Hwf_dom Hτ_succ_in_ℓ. set_solver.
            - simpl. destruct Hno_O_inv_b as [_ Hdisj].
              clear -Hdisj. set_solver.
            - intros i loc τ' v Hpos Hlk info Hop_lk.
              destruct (decide (τ' = τ)) as [->|Hne].
              + rewrite lookup_insert_eq in Hop_lk.
                injection Hop_lk as <-. reflexivity.
              + rewrite lookup_insert_ne in Hop_lk; [|done].
                exact (Hcoi_b _ _ _ _ Hpos Hlk _ Hop_lk).
            - destruct Hwit_b as [Hwit_dom Hwit_per].
              split.
              { simpl. clear -Hwit_dom. set_solver. }
              intros τ_w tail_loc snap Hwit_lookup.
              destruct (Hwit_per τ_w tail_loc snap Hwit_lookup)
                as (Hsub & Hlen_w & Hsucc_w & Hsnap_end & Hlt_in_w).
              split_and!; [exact Hsub|exact Hlen_w|exact Hsucc_w|exact Hsnap_end|].
              intros k Hkin.
              rewrite /absq_remove elem_of_filter /= in Hkin.
              destruct Hkin as [_ Hkin_lt].
              by apply Hlt_in_w. }
          (* Step 12: post-CAS head CAS [head head_val_outer l_succ]. *)
          wp_pures.
          wp_bind (CmpXchg _ _ _).
          iInv Nbq as (nodes_c del_pref_c head_val_c tail_val_c dummy_loc_c
                       ts_c s_c ls_c op_map_c node_map_c dq_map_c
                       no_O_set_c witness_map_c)
            "(>Hhead_c & >Htail_c & Hchain_c & >Htrace_c & >Hauth_op_c
              & >Hauth_nm_c & Hfrag_nm_c & >Hauth_dq_c & Hfrag_dq_c
              & >Hauth_del_c & >Hauth_calls_c & >Hauth_no_O_c & >Hauth_ls_c
              & >Hauth_w_c & Hfrag_w_c & >%Hsteps_c & >%Hts_eq_c & >%Hsim_c
              & >%Hdummy_c & >%Hnvi_c & >%Hdqi_c & >%Hno_O_inv_c & >%Hcoi_c
              & >%Hwit_c)".
          destruct (decide (head_val_c = head_val_outer)) as [Heq_h|Hne_h].
          ** (* Head CAS success: advance head_loc to l_succ. *)
             subst head_val_c.
             wp_cmpxchg_suc.
             iDestruct (own_valid_2 with "Hauth_nm_c Hl_succ_frag") as %Hagree_c.
             apply auth_both_valid_discrete in Hagree_c as [Hincl_c _].
             apply singleton_included_l in Hincl_c as (av_c & Hav_lookup_c & Hav_incl_c).
             rewrite /to_nodemap lookup_fmap in Hav_lookup_c.
             apply fmap_Some_equiv in Hav_lookup_c as (info_c & Hnm_c_l_succ & Hav_eq_c).
             rewrite Hav_eq_c in Hav_incl_c. rewrite Some_included in Hav_incl_c.
             assert ((Some τ_succ, v_succ) = info_c :> leibnizO node_info)
               as Hinfo_c_eq.
             { destruct Hav_incl_c as [Heq|Hin].
               - by apply (inj to_agree), leibniz_equiv in Heq.
               - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
             rewrite -Hinfo_c_eq in Hnm_c_l_succ.
             clear Hav_eq_c Hav_incl_c Hinfo_c_eq info_c.
             pose proof Hsim_c as (Hlen_c & Hdel_c & Hcp_in_ts_c & Hdomsub_c
                                  & Hnm_dom_c & Henq_clause_c & Hdeq_clause_c
                                  & Hinj_c & Hcorr_c & Hlt_pos_c & _Htbd_c
                                  & Hcomp_link_c & Htail_in_c & _ & Hnm_chain_c
                                  & Hsome_at_pos_c).
             destruct (Hnm_dom_c _ _ _ Hnm_c_l_succ) as (i_succ_c & Hi_succ_c_lookup).
             assert (1 ≤ i_succ_c)%nat as Hi_succ_c_pos.
             { destruct (decide (1 ≤ i_succ_c)%nat) as [|Hlt]; first done.
               assert (i_succ_c = 0%nat) as -> by lia.
               rewrite Hdummy_c in Hi_succ_c_lookup.
               injection Hi_succ_c_lookup as _ Habs _. discriminate. }
             iDestruct (own_valid_2 with "Hauth_no_O_c Hno_O_τ_succ_frag")
               as %Hno_O_c_both.
             apply auth_both_valid_discrete in Hno_O_c_both as [Hno_O_c_incl _].
             apply gset_included in Hno_O_c_incl.
             assert (τ_succ ∈ no_O_set_c) as Hτ_succ_in_no_O_c
               by (clear -Hno_O_c_incl; set_solver).
             assert (τ_succ ∉ s_c.(absq_O)) as Hτ_succ_not_O_c.
             { destruct Hno_O_inv_c as [_ Hdisj].
               clear -Hdisj Hτ_succ_in_no_O_c. set_solver. }
             destruct (Hcorr_c _ _ _ _ Hi_succ_c_pos Hi_succ_c_lookup)
               as (_ & _ & Hin_iff_c).
             assert (i_succ_c ≤ del_pref_c)%nat as Hi_succ_c_le_del.
             { destruct (decide (del_pref_c < i_succ_c)%nat) as [Hlt|]; last lia.
               exfalso. apply Hτ_succ_not_O_c. by apply Hin_iff_c. }
             iModIntro.
             iSplitL "Hhead_c Htail_c Hchain_c Htrace_c Hauth_op_c Hauth_nm_c
                      Hfrag_nm_c Hauth_dq_c Hfrag_dq_c Hauth_del_c Hauth_calls_c
                      Hauth_no_O_c Hauth_ls_c Hauth_w_c Hfrag_w_c".
             { iNext. iExists nodes_c, del_pref_c, l_succ, tail_val_c, dummy_loc_c,
                 ts_c, s_c, ls_c, op_map_c, node_map_c, dq_map_c, no_O_set_c, witness_map_c.
               iFrame. iPureIntro. split_and!.
               - exact Hsteps_c.
               - exact Hts_eq_c.
               - split_and!.
                 + exact Hlen_c.
                 + exact Hdel_c.
                 + exact Hcp_in_ts_c.
                 + exact Hdomsub_c.
                 + exact Hnm_dom_c.
                 + exact Henq_clause_c.
                 + exact Hdeq_clause_c.
                 + exact Hinj_c.
                 + exact Hcorr_c.
                 + exact Hlt_pos_c.
                 + exact _Htbd_c.
                 + exact Hcomp_link_c.
                 + exact Htail_in_c.
                 + exists i_succ_c, (Some τ_succ), v_succ.
                   split; [exact Hi_succ_c_le_del|exact Hi_succ_c_lookup].
                 + exact Hnm_chain_c.
                 + exact Hsome_at_pos_c.
               - exact Hdummy_c.
               - exact Hnvi_c.
               - exact Hdqi_c.
               - apply Hno_O_inv_c.
               - apply Hno_O_inv_c.
               - exact Hcoi_c.
               - exact Hwit_c. }
             wp_pures.
             unfold new_τ_info in *.
             rewrite /deq_walk_cont.
             iModIntro.
             wp_pures.
             iApply (op_spec_deq_trace_emit
                       γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                       l head tail τ rng_init (InjRV v_succ)
                       with "Hinv Htrace_inv Hfrag Hdq_τ_frag HΦ").
          ** (* Head CAS fail: head pointer changed.  Close inv. *)
             assert (#head_val_c ≠ #head_val_outer) as Hne_h_inj.
             { intros [=Habs]. by apply Hne_h. }
             wp_cmpxchg_fail.
             iModIntro.
             iSplitL "Hhead_c Htail_c Hchain_c Htrace_c Hauth_op_c Hauth_nm_c
                      Hfrag_nm_c Hauth_dq_c Hfrag_dq_c Hauth_del_c Hauth_calls_c
                      Hauth_no_O_c Hauth_ls_c Hauth_w_c Hfrag_w_c".
             { iNext. iExists nodes_c, del_pref_c, head_val_c, tail_val_c, dummy_loc_c,
                 ts_c, s_c, ls_c, op_map_c, node_map_c, dq_map_c, no_O_set_c, witness_map_c.
               iFrame. iPureIntro. split_and!; auto.
               - apply Hno_O_inv_c.
               - apply Hno_O_inv_c. }
             wp_pures.
             unfold new_τ_info in *.
             rewrite /deq_walk_cont.
             iModIntro.
             wp_pures.
             iApply (op_spec_deq_trace_emit
                       γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                       l head tail τ rng_init (InjRV v_succ)
                       with "Hinv Htrace_inv Hfrag Hdq_τ_frag HΦ").
        * (* CAS FAIL — different successor. *)
          iDestruct (bq_chain_lookup_acc _ del_pref_b i_iter_b p_iter
                       τ_iter_opt v_iter Hi_iter_b_lookup with "Hchain_b")
            as "[Hv_b [Hn_b HW_b]]".
          iEval (rewrite Hmark_b Hsucc_b /next_value_of) in "Hn_b".
          assert (InjLV #l_succ_b ≠ InjLV #l_succ) as Hne_inj.
          { intros [=Habs]. apply Hne_succ. exact Habs. }
          wp_cmpxchg_fail.
          iDestruct ("HW_b" with "[Hv_b Hn_b]") as "Hchain_b".
          { rewrite Hmark_b Hsucc_b /next_value_of. iFrame. }
          iModIntro.
          iSplitL "Hhead_b Htail_b Hchain_b Htrace_b Hauth_op_b Hauth_nm_b
                   Hfrag_nm_b Hauth_dq_b Hfrag_dq_b Hauth_del_b Hauth_calls_b
                   Hauth_no_O_b Hauth_ls_b Hauth_w_b Hfrag_w_b".
          { iNext. iExists nodes_b, del_pref_b, head_val_b, tail_val_b,
              dummy_loc_b, ts_b, s_b, ls_b, op_map_b, node_map_b, dq_map_b,
              no_O_set_b, witness_map_b.
            iFrame. iPureIntro. split_and!; auto.
            - apply Hno_O_inv_b.
            - apply Hno_O_inv_b. }
          wp_pures.
          iApply ("Houter" with "Hfrag HΦ").
      + (* (false, None): iter.next is unmarked-null.  CAS fails. *)
        iDestruct (bq_chain_lookup_acc _ del_pref_b i_iter_b p_iter
                     τ_iter_opt v_iter Hi_iter_b_lookup with "Hchain_b")
          as "[Hv_b [Hn_b HW_b]]".
        iEval (rewrite Hmark_b Hsucc_b /next_value_of) in "Hn_b".
        wp_cmpxchg_fail.
        iDestruct ("HW_b" with "[Hv_b Hn_b]") as "Hchain_b".
        { rewrite Hmark_b Hsucc_b /next_value_of. iFrame. }
        iModIntro.
        iSplitL "Hhead_b Htail_b Hchain_b Htrace_b Hauth_op_b Hauth_nm_b
                 Hfrag_nm_b Hauth_dq_b Hfrag_dq_b Hauth_del_b Hauth_calls_b
                 Hauth_no_O_b Hauth_ls_b Hauth_w_b Hfrag_w_b".
        { iNext. iExists nodes_b, del_pref_b, head_val_b, tail_val_b,
            dummy_loc_b, ts_b, s_b, ls_b, op_map_b, node_map_b, dq_map_b,
            no_O_set_b, witness_map_b.
          iFrame. iPureIntro. split_and!; auto.
          - apply Hno_O_inv_b.
          - apply Hno_O_inv_b. }
        wp_pures.
        iApply ("Houter" with "Hfrag HΦ").
    - (* Case A: next_loaded = InjRV #l_succ — recurse the walk.
         Steps:
           1. wp_pures past the [if l_succ = #()] (l_succ is a loc, ≠).
           2. wp_bind for [!(l_succ +ₗ 1)].
           3. Open inv at [chain_n], find l_succ at i_succ_n via Hl_succ_frag,
              extract value+next via [bq_chain_lookup_acc], wp_load.
           4. Determine new next_loaded = next_value_of (mark_at_n) (succ_at_n)
              at l_succ's position.  Case-split into (true,Some)/(false,Some)/
              (false,None); (true,None) is contradiction.
           5. Alloc γ_no_O for τ_succ, derive persistent fragment.
           6. Extract γ_del lb for i_succ_n.
           7. Close inv with no_O_set ∪ {τ_succ}.
           8. wp_pures.
           9. iApply IH_walk with new params. *)
      subst next_loaded.
      wp_pures.
      wp_bind (! _)%E.
      iInv Nbq as (nodes_n del_pref_n head_val_n tail_val_n dummy_loc_n
                   ts_n s_n ls_n op_map_n node_map_n dq_map_n
                   no_O_set_n witness_map_n)
        "(>Hhead_n & >Htail_n & Hchain_n & >Htrace_n & >Hauth_op_n
          & >Hauth_nm_n & Hfrag_nm_n & >Hauth_dq_n & Hfrag_dq_n
          & >Hauth_del_n & >Hauth_calls_n & >Hauth_no_O_n & >Hauth_ls_n
          & >Hauth_w_n & Hfrag_w_n & >%Hsteps_n & >%Hts_eq_n & >%Hsim_n
          & >%Hdummy_n & >%Hnvi_n & >%Hdqi_n & >%Hno_O_inv_n & >%Hcoi_n
          & >%Hwit_n)".
      (* Find l_succ in chain_n. *)
      iDestruct (own_valid_2 with "Hauth_nm_n Hl_succ_frag") as %Hagree_n.
      apply auth_both_valid_discrete in Hagree_n as [Hincl_n _].
      apply singleton_included_l in Hincl_n as (av_n & Hav_lookup_n & Hav_incl_n).
      rewrite /to_nodemap lookup_fmap in Hav_lookup_n.
      apply fmap_Some_equiv in Hav_lookup_n as (info_n & Hnm_l_succ_n & Hav_eq_n).
      rewrite Hav_eq_n in Hav_incl_n. rewrite Some_included in Hav_incl_n.
      assert ((Some τ_succ, v_succ) = info_n :> leibnizO node_info)
        as Hinfo_n_eq.
      { destruct Hav_incl_n as [Heq|Hin].
        - by apply (inj to_agree), leibniz_equiv in Heq.
        - rewrite to_agree_included in Hin. by apply leibniz_equiv. }
      rewrite -Hinfo_n_eq in Hnm_l_succ_n.
      clear Hav_eq_n Hav_incl_n Hinfo_n_eq info_n.
      pose proof Hsim_n as (Hlen_n & Hdel_n & Hcp_in_ts_n & Hdomsub_n
                          & Hnm_dom_n & Henq_clause_n & Hdeq_clause_n
                          & Hinj_n & Hcorr_n & Hlt_pos_n & _Htbd_n
                          & Hcomp_link_n & Htail_in_n & Hhead_in_n
                          & Hnm_chain_n & Hsome_at_pos_n).
      destruct (Hnm_dom_n _ _ _ Hnm_l_succ_n) as (i_succ_n & Hi_succ_n_lookup).
      (* Position 1+ since l_succ has Some τ_succ tag (clause 16 in reverse:
         dummy is at position 0 with None tag). *)
      assert (1 ≤ i_succ_n)%nat as Hi_succ_n_pos.
      { destruct (decide (1 ≤ i_succ_n)%nat) as [|Hlt]; first done.
        assert (i_succ_n = 0%nat) as -> by lia.
        rewrite Hdummy_n in Hi_succ_n_lookup.
        injection Hi_succ_n_lookup as _ Habs _. discriminate. }
      (* Extract l_succ's value+next cells from chain_n. *)
      iDestruct (bq_chain_lookup_acc _ del_pref_n i_succ_n l_succ
                   (Some τ_succ) v_succ Hi_succ_n_lookup with "Hchain_n")
        as "[Hv_n [Hn_n HW_n]]".
      simpl. wp_load.
      iDestruct ("HW_n" with "[$Hv_n $Hn_n]") as "Hchain_n".
      (* Derive [τ_succ ∉ O_n] from [Hno_O_τ_succ_in] + [no_O_inv]'s
         disjointness.  Then by clause 9, [del_pref_n ≥ i_succ_n]. *)
      iDestruct (own_valid_2 with "Hauth_no_O_n Hno_O_τ_succ_in")
        as %Hno_O_both_n.
      apply auth_both_valid_discrete in Hno_O_both_n as [Hno_O_incl_n _].
      apply gset_included in Hno_O_incl_n.
      assert (τ_succ ∈ no_O_set_n) as Hτ_succ_in_no_O
        by (clear -Hno_O_incl_n; set_solver).
      assert (τ_succ ∉ s_n.(absq_O)) as Hτ_succ_not_O.
      { destruct Hno_O_inv_n as [_ Hdisj].
        clear -Hdisj Hτ_succ_in_no_O. set_solver. }
      destruct (Hcorr_n _ _ _ _ Hi_succ_n_pos Hi_succ_n_lookup)
        as (_ & (f_τ_succ & Hℓ_τ_succ) & Hin_iff_τ_succ).
      assert (i_succ_n ≤ del_pref_n)%nat as Hdel_ge_i_succ.
      { destruct (decide (del_pref_n < i_succ_n)%nat) as [Hlt|]; last lia.
        exfalso. apply Hτ_succ_not_O. by apply Hin_iff_τ_succ. }
      (* Extract γ_del lb at i_succ_n. *)
      iEval (rewrite mono_nat_auth_lb_op) in "Hauth_del_n".
      iDestruct "Hauth_del_n" as "[Hauth_del_n #Hdel_lb_full_n]".
      iAssert (own γ_del (◯MN i_succ_n)) as "#Hdel_lb_succ_n".
      { iApply (own_mono with "Hdel_lb_full_n").
        apply mono_nat_lb_mono. lia. }
      (* Determine the loaded next2 value via case-split on
         (mark_at, succ_at) at i_succ_n. *)
      destruct (mark_at del_pref_n i_succ_n) eqn:Hmark_n;
      destruct (succ_at nodes_n i_succ_n) as [l_succ_succ|] eqn:Hsucc_n.
      + (* (true, Some l_succ_succ): l_succ.next is marked-pointer.
           next2 = InjRV #l_succ_succ.  Recurse with iter := l_succ.
           Need to alloc γ_no_O for τ_l_succ_succ to feed into the
           next walk iter's Case A disjunct. *)
        rewrite /succ_at in Hsucc_n.
        destruct (nodes_n !! (i_succ_n + 1)%nat) as [[[lk τ_l_opt] v_l]|]
          eqn:Hnext_lookup_n; last discriminate.
        simpl in Hsucc_n. injection Hsucc_n as ->.
        assert (Hi_l_pos : (1 ≤ i_succ_n + 1)%nat) by lia.
        destruct (Hsome_at_pos_n _ _ _ _ Hi_l_pos Hnext_lookup_n)
          as [τ_l_succ_succ ->].
        pose proof (Hnm_chain_n _ _ _ _ Hnext_lookup_n) as Hnm_l_succ_succ.
        iDestruct (own_mono _ _ (◯ {[l_succ_succ := to_agree
                    ((Some τ_l_succ_succ, v_l) : leibnizO node_info)]})
                    with "Hfrag_nm_n") as "#Hl_succ_succ_frag".
        { apply auth_frag_mono. rewrite /to_nodemap.
          apply (proj2 (singleton_included_l _ _ _)).
          exists (to_agree ((Some τ_l_succ_succ, v_l) : leibnizO node_info)).
          split.
          - rewrite lookup_fmap Hnm_l_succ_succ //=.
          - reflexivity. }
        (* mark_at = true → i_succ_n + 1 ≤ del_pref_n. *)
        rewrite /mark_at in Hmark_n.
        apply bool_decide_eq_true in Hmark_n.
        (* Alloc γ_no_O for τ_l_succ_succ.  τ_l_succ_succ ∈ dom cp ∖ O
           via clause 9 at i_succ_n + 1 with del_pref_n ≥ i_succ_n + 1. *)
        destruct (Hcorr_n _ _ _ _ Hi_l_pos Hnext_lookup_n)
          as (_ & (f_τ_l_succ_succ & Hℓ_τ_l_succ_succ) & Hin_iff_τ_l_succ_succ).
        assert (τ_l_succ_succ ∉ s_n.(absq_O)) as Hτ_l_succ_succ_not_O.
        { intros Habs. apply Hin_iff_τ_l_succ_succ in Habs. lia. }
        assert (τ_l_succ_succ ∈ dom s_n.(absq_cp)) as Hτ_l_succ_succ_in_cp.
        { destruct s_n as [O_n lt_n l_n rv_n cp_n]; simpl in *.
          pose proof (absq_wf_steps _ _ _ _ _ Hsteps_n (absq_wf_init _)) as Hwf.
          pose proof (absq_wf_dom _ _ Hwf) as Hwf_dom. simpl in Hwf_dom.
          assert (τ_l_succ_succ ∈ dom l_n) as Hin_l
            by (apply elem_of_dom; by exists (v_l, f_τ_l_succ_succ)).
          clear -Hwf_dom Hin_l. set_solver. }
        iMod (own_update _ _
                (● (no_O_set_n ∪ {[τ_l_succ_succ]} : gsetUR positive)
                   ⋅ ◯ (no_O_set_n ∪ {[τ_l_succ_succ]} : gsetUR positive)
                  : authR (gsetUR positive))
                with "Hauth_no_O_n") as "[Hauth_no_O_n #Hno_O_full_τ_l]".
        { apply auth_update_alloc, gset_local_update.
          apply union_subseteq_l. }
        iAssert (own γ_no_O (◯ ({[τ_l_succ_succ]} : gsetUR positive)))
          as "#Hno_O_τ_l_succ_succ_frag".
        { iApply (own_mono with "Hno_O_full_τ_l").
          apply auth_frag_mono. apply gset_included.
          apply union_subseteq_r. }
        iClear "Hno_O_full_τ_l".
        (* Close inv with no_O_set ∪ {τ_l_succ_succ}. *)
        iModIntro.
        iSplitL "Hhead_n Htail_n Hchain_n Htrace_n Hauth_op_n Hauth_nm_n
                 Hfrag_nm_n Hauth_dq_n Hfrag_dq_n Hauth_del_n Hauth_calls_n
                 Hauth_no_O_n Hauth_ls_n Hauth_w_n Hfrag_w_n".
        { iNext. iExists nodes_n, del_pref_n, head_val_n, tail_val_n,
            dummy_loc_n, ts_n, s_n, ls_n, op_map_n, node_map_n, dq_map_n,
            (no_O_set_n ∪ {[τ_l_succ_succ]}), witness_map_n.
          iFrame. iPureIntro. split_and!; auto.
          - destruct Hno_O_inv_n as [Hsub _].
            assert (τ_l_succ_succ ∈ dom s_n.(absq_cp) ∖ s_n.(absq_O))
              as Hτ_l_diff.
            { rewrite elem_of_difference. split; assumption. }
            clear -Hsub Hτ_l_diff. set_solver.
          - destruct Hno_O_inv_n as [_ Hdisj].
            clear -Hdisj Hτ_l_succ_succ_not_O. set_solver. }
        simpl.
        wp_pure _.
        wp_pure _.
        (* Recursive walk call: iter := l_succ, next := InjRV #l_succ_succ. *)
        iApply ("IH_walk" $! l_succ (Some τ_succ) v_succ i_succ_n
                          (InjRV #l_succ_succ) with
                "Hl_succ_frag [] Hdel_lb_succ_n [] Hfrag HΦ Houter").
        { iRight. iExists τ_succ. iSplit; first done.
          iApply "Hno_O_τ_succ_in". }
        { iRight. iRight.
          iExists τ_l_succ_succ, l_succ_succ, v_l. iSplit; first done.
          iSplit.
          - iApply "Hl_succ_succ_frag".
          - iApply "Hno_O_τ_l_succ_succ_frag". }
      + (* (true, None): l_succ.next is marked-null.  Impossible. *)
        exfalso.
        rewrite /mark_at in Hmark_n.
        apply bool_decide_eq_true in Hmark_n.
        rewrite /succ_at in Hsucc_n.
        destruct (nodes_n !! (i_succ_n + 1)%nat) eqn:Hnext_n; first discriminate.
        apply lookup_ge_None_1 in Hnext_n. lia.
      + (* (false, Some l_succ_succ): l_succ.next is unmarked-pointer.
           next2 = InjLV #l_succ_succ.  Recurse with iter := l_succ;
           the new Hnext uses the Case B disjunct (no γ_no_O for the
           successor). *)
        rewrite /succ_at in Hsucc_n.
        destruct (nodes_n !! (i_succ_n + 1)%nat) as [[[lk τ_l_opt] v_l]|]
          eqn:Hnext_lookup_n; last discriminate.
        simpl in Hsucc_n. injection Hsucc_n as ->.
        assert (Hi_l_pos : (1 ≤ i_succ_n + 1)%nat) by lia.
        destruct (Hsome_at_pos_n _ _ _ _ Hi_l_pos Hnext_lookup_n)
          as [τ_l_succ_succ ->].
        pose proof (Hnm_chain_n _ _ _ _ Hnext_lookup_n) as Hnm_l_succ_succ.
        iDestruct (own_mono _ _ (◯ {[l_succ_succ := to_agree
                    ((Some τ_l_succ_succ, v_l) : leibnizO node_info)]})
                    with "Hfrag_nm_n") as "#Hl_succ_succ_frag".
        { apply auth_frag_mono. rewrite /to_nodemap.
          apply (proj2 (singleton_included_l _ _ _)).
          exists (to_agree ((Some τ_l_succ_succ, v_l) : leibnizO node_info)).
          split.
          - rewrite lookup_fmap Hnm_l_succ_succ //=.
          - reflexivity. }
        (* Close inv unchanged. *)
        iModIntro.
        iSplitL "Hhead_n Htail_n Hchain_n Htrace_n Hauth_op_n Hauth_nm_n
                 Hfrag_nm_n Hauth_dq_n Hfrag_dq_n Hauth_del_n Hauth_calls_n
                 Hauth_no_O_n Hauth_ls_n Hauth_w_n Hfrag_w_n".
        { iNext. iExists nodes_n, del_pref_n, head_val_n, tail_val_n,
            dummy_loc_n, ts_n, s_n, ls_n, op_map_n, node_map_n, dq_map_n,
            no_O_set_n, witness_map_n.
          iFrame. iPureIntro. split_and!; auto.
          - apply Hno_O_inv_n.
          - apply Hno_O_inv_n. }
        simpl.
        wp_pure _.
        wp_pure _.
        iApply ("IH_walk" $! l_succ (Some τ_succ) v_succ i_succ_n
                          (InjLV #l_succ_succ) with
                "Hl_succ_frag [] Hdel_lb_succ_n [] Hfrag HΦ Houter").
        { iRight. iExists τ_succ. iSplit; first done.
          iApply "Hno_O_τ_succ_in". }
        { iRight. iLeft.
          iExists τ_l_succ_succ, l_succ_succ, v_l. iSplit; first done.
          iApply "Hl_succ_succ_frag". }
      + (* (false, None): l_succ.next is unmarked-null.  The queue
           ends at l_succ — fire LIN-DEQ2 inline at this inv-open,
           then wp_pures past the operational walk recursion (which
           dispatches to InjL p with p = #() → returns NONE), and
           hand off to op_spec_deq_trace_emit. *)
        (* Step 1: del_pref_n = i_succ_n.  Already have
           [i_succ_n ≤ del_pref_n] (Hdel_ge_i_succ).  From
           [Hmark_n = false]: [del_pref_n ≤ i_succ_n]. *)
        rewrite /mark_at in Hmark_n.
        apply bool_decide_eq_false in Hmark_n.
        assert (del_pref_n = i_succ_n) as Hdel_eq_i_succ by lia.
        (* Step 2: length nodes_n = i_succ_n + 1. *)
        rewrite /succ_at in Hsucc_n.
        destruct (nodes_n !! (i_succ_n + 1)%nat) eqn:Hnext_n;
          first discriminate.
        apply lookup_ge_None_1 in Hnext_n.
        pose proof (lookup_lt_Some _ _ _ Hi_succ_n_lookup) as Hlen_lower.
        assert (length nodes_n = (i_succ_n + 1)%nat) as Hlen_eq by lia.
        (* Step 3: extract op_map info via Hfrag (linked = false). *)
        iDestruct (own_valid_2 with "Hauth_op_n Hfrag") as %Hτ_both.
        apply auth_both_valid_discrete in Hτ_both as [Hτ_incl Hτ_valid].
        apply singleton_included_exclusive_l in Hτ_incl; [|apply _|done].
        rewrite lookup_fmap in Hτ_incl.
        apply leibniz_equiv in Hτ_incl.
        apply fmap_Some_1 in Hτ_incl as (info_τ & Hτ_in_op_n & Hinfo_τ).
        destruct info_τ as [kd nd lk]; injection Hinfo_τ as <- <- <-.
        destruct (Hdeq_clause_n _ _ _ _ _ Hτ_in_op_n) as (_ & Hcp_τ_R1_pre & _).
        specialize (Hcp_τ_R1_pre eq_refl).
        (* Step 4: γ_op update — set linked := true. *)
        set (new_τ_info := {| op_info_kind := OpDeq [] rng_init;
                              op_info_node := None;
                              op_info_linked := true |}).
        iMod (own_update_2 _ _ _
                (● to_opmap (<[τ := new_τ_info]> op_map_n)
                   ⋅ ◯ {[τ := Excl new_τ_info]})
                with "Hauth_op_n Hfrag") as "[Hauth_op_n Hfrag]".
        { apply auth_update.
          rewrite /to_opmap fmap_insert.
          apply: singleton_local_update.
          { rewrite lookup_fmap Hτ_in_op_n //. }
          by apply exclusive_local_update. }
        (* Step 5: dq_map_n !! τ = None. *)
        assert (absq_wf valid_value s_n) as Hwf_n.
        { eapply absq_wf_steps; [exact Hsteps_n|apply absq_wf_init]. }
        assert (dq_map_n !! τ = None) as Hdq_τ_none.
        { destruct (dq_map_n !! τ) as [v_old|] eqn:Heq; last done.
          exfalso. pose proof (Hdqi_n _ _ Heq) as Hrv_τ.
          destruct (absq_wf_rv _ _ Hwf_n τ (mk_is_Some _ _ Hrv_τ))
            as [Hcp|Hcp]; rewrite Hcp_τ_R1_pre in Hcp; discriminate. }
        (* Step 6: γ_dq update with NONEV. *)
        iMod (own_update_2 _ _ _
                (● to_dqmap (<[τ := NONEV]> dq_map_n)
                   ⋅ ◯ to_dqmap (<[τ := NONEV]> dq_map_n))
                with "Hauth_dq_n Hfrag_dq_n") as "[Hauth_dq_n Hfrag_dq_n]".
        { apply auth_update.
          rewrite /to_dqmap !fmap_insert.
          apply: alloc_local_update; [|done].
          rewrite lookup_fmap Hdq_τ_none //. }
        iDestruct (own_mono _ _ (◯ {[τ := to_agree NONEV]}) with "Hfrag_dq_n")
          as "#Hdq_τ_frag".
        { apply auth_frag_mono. rewrite /to_dqmap.
          apply singleton_included_l.
          exists (to_agree NONEV). split.
          - rewrite lookup_fmap lookup_insert_eq //.
          - reflexivity. }
        (* Step 7: γ_ls update — append [(τ, ALinDeq NONEV)]. *)
        iMod (own_update _ _
                (●ML (ls_n ++ [(τ, ALinDeq NONEV)]
                       : list (leibnizO (positive * absq_action))))
                with "Hauth_ls_n") as "Hauth_ls_n".
        { apply mono_list_update. by apply prefix_app_r. }
        (* Step 8: discharge LIN-DEQ2 premise (HallPend). *)
        assert (s_n.(absq_O) ⊆ dom s_n.(absq_l)) as HO_in_l.
        { eapply absq_steps_O_in_l; [exact Hsteps_n|]. simpl. clear; set_solver. }
        assert (∀ o, o ∈ s_n.(absq_O) → ∃ d, s_n.(absq_l) !! o = Some (d, PEND))
          as HallPend.
        { intros o Ho_O.
          destruct (proj1 (elem_of_dom _ _) (HO_in_l _ Ho_O)) as [[d f] Hℓ_o].
          destruct f as [|].
          - by exists d.
          - exfalso.
            destruct (Hcomp_link_n _ _ Hℓ_o) as (p & l_p & Hp_pos & Hp_lookup).
            destruct (Hcorr_n _ _ _ _ Hp_pos Hp_lookup) as (_ & _ & Hin_iff).
            apply Hin_iff in Ho_O.
            apply lookup_lt_Some in Hp_lookup. lia. }
        (* Step 9: build the LIN-DEQ2 successor state and close inv. *)
        destruct s_n as [O_n lt_n ℓ_n rv_n cp_n]; simpl in *.
        iModIntro.
        iSplitL "Hhead_n Htail_n Hchain_n Htrace_n Hauth_op_n Hauth_nm_n
                 Hfrag_nm_n Hauth_dq_n Hfrag_dq_n Hauth_del_n Hauth_calls_n
                 Hauth_no_O_n Hauth_ls_n Hauth_w_n Hfrag_w_n".
        { iNext.
          iExists nodes_n, del_pref_n, head_val_n, tail_val_n, dummy_loc_n, ts_n,
            {| absq_O := O_n; absq_lt := lt_n; absq_l := ℓ_n;
               absq_rv := <[τ := NONEV]> rv_n;
               absq_cp := <[τ := R2]> cp_n |},
            (ls_n ++ [(τ, ALinDeq NONEV)]),
            (<[τ := new_τ_info]> op_map_n), node_map_n,
            (<[τ := NONEV]> dq_map_n), no_O_set_n, witness_map_n.
          iFrame "Hhead_n Htail_n Hchain_n Htrace_n Hauth_op_n Hauth_nm_n
                  Hfrag_nm_n Hauth_dq_n Hfrag_dq_n Hauth_del_n Hauth_ls_n
                  Hauth_no_O_n Hauth_w_n Hfrag_w_n".
          assert (τ ∈ dom cp_n) as Hτ_in_cp_n
            by (apply elem_of_dom; eexists; exact Hcp_τ_R1_pre).
          rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre)).
          iFrame "Hauth_calls_n".
          iPureIntro. split_and!.
          - eapply lts_steps_app; [exact Hsteps_n|].
            eapply lts_steps_cons; [|apply lts_steps_nil].
            apply absq_step_lin_deq2; [done|exact Hcp_τ_R1_pre|exact HallPend].
          - rewrite Hts_eq_n /trace_of_absq_labels map_app /= filter_app.
            rewrite filter_cons_False; [by rewrite app_nil_r|].
            by compute.
          - split_and!; simpl.
            + exact Hlen_n.
            + exact Hdel_n.
            + rewrite (dom_insert_lookup_L _ _ _ (mk_is_Some _ _ Hcp_τ_R1_pre)).
              exact Hcp_in_ts_n.
            + rewrite !dom_insert_L.
              clear -Hdomsub_n Hτ_in_cp_n. set_solver.
            + exact Hnm_dom_n.
            + intros τ' d' node' linked' Hop'.
              destruct (decide (τ' = τ)) as [->|Hne].
              { rewrite lookup_insert_eq in Hop'.
                injection Hop' as Habs. discriminate. }
              rewrite lookup_insert_ne in Hop'; last done.
              destruct (Henq_clause_n _ _ _ _ Hop')
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
                destruct (Hdeq_clause_n _ _ _ _ _ Hop') as (Hnone & Hpre & Hpost).
                split_and!.
                { exact Hnone. }
                { intros Hb. rewrite lookup_insert_ne; [|done]. by apply Hpre. }
                { intros Hb. destruct (Hpost Hb) as (Hcp_R2' & v_rv' & Hrv_v').
                  split.
                  - rewrite lookup_insert_ne; [exact Hcp_R2'|done].
                  - exists v_rv'. rewrite lookup_insert_ne; [exact Hrv_v'|done]. }
            + exact Hinj_n.
            + exact Hcorr_n.
            + exact Hlt_pos_n.
            + done.
            + exact Hcomp_link_n.
            + exact Htail_in_n.
            + exact Hhead_in_n.
            + exact Hnm_chain_n.
            + exact Hsome_at_pos_n.
          - exact Hdummy_n.
          - exact Hnvi_n.
          - intros τ' v Hlk.
            destruct (decide (τ' = τ)) as [->|Hne].
            { rewrite lookup_insert_eq in Hlk. injection Hlk as <-.
              by rewrite lookup_insert_eq. }
            rewrite lookup_insert_ne in Hlk; last done.
            rewrite lookup_insert_ne; last done.
            by apply Hdqi_n.
          - apply Hno_O_inv_n.
          - apply Hno_O_inv_n.
          - intros i loc τ' v Hpos Hlk info Hop_lk.
            pose proof (Hcoi_n _ _ _ _ Hpos Hlk) as Hlinked.
            destruct (decide (τ' = τ)) as [->|Hne].
            + exfalso. specialize (Hlinked _ Hτ_in_op_n). discriminate.
            + rewrite lookup_insert_ne in Hop_lk; [|done].
              exact (Hlinked _ Hop_lk).
          - destruct Hwit_n as [Hwit_dom Hwit_per].
            split.
            { simpl. clear -Hwit_dom. set_solver. }
            intros τ_w tail_loc snap Hwit_lookup.
            exact (Hwit_per τ_w tail_loc snap Hwit_lookup). }
        (* Step 10: wp_pures past the operational walk recursion.
           [walk l_succ (InjLV #())] dispatches to InjL p with p = #()
           → returns NONE.  All pure steps. *)
        simpl.
        wp_pures.
        (* Step 11: trace_emit handoff with v_dq := NONEV. *)
        rewrite /deq_walk_cont.
        iModIntro.
        wp_pures.
        unfold new_τ_info in *.
        iApply (op_spec_deq_trace_emit
                  γ γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w
                  l head tail τ rng_init NONEV
                  with "Hinv Htrace_inv Hfrag Hdq_τ_frag HΦ").
  Qed.

End bq_skeleton_deq_walk.
