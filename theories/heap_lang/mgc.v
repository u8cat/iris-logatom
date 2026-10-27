From iris_logatom.lib Require Import list.
From iris.proofmode Require Import proofmode.
From iris_logatom.pure_logic Require Export state_set linear.
From iris_logatom.pure_logic Require Import encodable steps step_laws tactics not_stuck_restrict.
From iris.algebra Require Import agree.
From iris.base_logic Require Import invariants ghost_map.
From iris.program_logic Require Export atomic.
From iris_logatom.program_logic Require Import weakestpre.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import completeness fork_free.
From iris_logatom.heap_lang.lib Require Export list nondet_int_prealloc trace.

(* Call ≡ InjL, Ret ≡ InjR *)
Definition call_ret_wrapper (l : loc) (n : nat) : val := λ: "op" "obj" "req",
  let: "τ" := trace_fresh #l (InjL (#n, "req")) in
  let: "res" := "op" "obj" "req" in
  trace_emit #l "τ" (InjR "res");;
  "res".

Section impl.
  (* The location for the tracer must be allocated at meta-level because
    it must fresh wrt the final state. *)
  Context (tracer : loc).

  Definition concurrent_call (opid : nat) (request : val) (ops obj : expr) : expr :=
    Fork (call_ret_wrapper tracer opid (list_nth #opid ops) obj request;; #()).

  Fixpoint concurrent_calls calls (ops obj : expr) : expr :=
    match calls with
    | [] => trace_peak #tracer
    | (opid,request)::calls =>
      concurrent_call opid request ops obj;;
      concurrent_calls calls ops obj
    end.

  Definition extract_calls (ts : list (positive*trace)) :=
    omap (λ t, if t.2 is Call n v then Some (n, v) else None) ts.

  Definition mgc_of_trace ts : val := λ: "ops" "obj",
    concurrent_calls (extract_calls ts) "ops" "obj".

  Lemma concurrent_call_subst ts ops obj :
    subst "obj" obj (subst "ops" ops (concurrent_calls (extract_calls ts) "ops" "obj")) =
    concurrent_calls (extract_calls ts) ops obj.
  Proof.
    induction ts as [|[τ [req| |]] ts IH]; simpl;
      [| rewrite IH..]; done.
  Qed.
End impl.

Record mgc_repr {Σ : gFunctors} := {
  I_lang : list (positive*trace) → Prop;
  mgc_inv : ∀ `{!heapGS Σ}, loc → gname → val → iProp Σ;
  mgc_inv_persistent : ∀ `{!heapGS Σ} l γ x, Persistent (mgc_inv l γ x);
}.
Global Arguments mgc_repr Σ : clear implicits.
Global Existing Instance mgc_inv_persistent.

Section spec.
  Context `{!heapGS Σ, !traceG Σ}.
  Context (P_init : iProp Σ).
  Context (R : mgc_repr Σ) (s : stuckness).
  Context (valid_reqs : list (val → Prop)).
  Context (init : expr) (ops : list val).

  Definition init_spec_type_gen : Prop :=
    {{{ P_init }}}
      init @ s; ⊤
    {{{ γ obj, RET obj; (∀ l : loc, trace_is l ([] : list (positive*trace)) ={⊤}=∗ mgc_inv R l γ obj) }}}.

  Definition call_ret_wrapper_spec_type : Prop :=
    ∀ n γ l (obj req : val), default default_vr (valid_reqs!!n) req →
      {{{ trace_inv l (I_lang R) ∗ mgc_inv R l γ obj }}}
        call_ret_wrapper l n (ops!!!n : val) obj req @ s; ⊤
      {{{ v, RET v; True }}}.

  Lemma mgc_spec_gen tracer ts :
    Forall (λ x, if x.2 is Call n req then default default_vr (valid_reqs!!n) req else True) ts →
    init_spec_type_gen → call_ret_wrapper_spec_type →
    ⊢ inv_heap_inv -∗ trace_inv tracer (I_lang R) -∗ trace_is tracer ([] : list (positive*trace)) -∗
    P_init -∗
    WP mgc_of_trace tracer ts (encode_val ops) init @ s; ⊤ {{ v, ⌜∃ ts, v = encode_trace ts ∧ I_lang R ts⌝ }}.
  Proof.
    intros Hvalid_trace init_spec op_spec.
    iIntros "#Hhi #Hti Ht HP_init".
    wp_apply (init_spec with "HP_init") as (γ obj) "His_P_wand".
    iMod ("His_P_wand" with "[$]") as "#His_P".
    wp_pures. wp_rec. wp_pure. wp_lam.
    rewrite concurrent_call_subst.
    iInduction ts as [|[τ [opid req| |]] ts IH] "IH".
    - rewrite /mgc_of_trace /extract_calls omap_nil /concurrent_calls.
      iApply (wp_stuck_mono NotStuck); first done.
      wp_apply (trace_peak_spec with "Hti") as (ts) "%HI_lang".
      iPureIntro. by exists ts.
    - rewrite /mgc_of_trace /extract_calls (omap_cons_Some _ _ (opid,req)) //=.
      rewrite Forall_cons in Hvalid_trace.
      destruct Hvalid_trace as [Hvalid_req_hd Hvalid_trace].
      wp_apply wp_fork.
      + wp_apply list_nth_spec.
        wp_apply (op_spec with "[$Hti $His_P]"); first done.
        iIntros (v) "_". by wp_pures.
      + wp_pures. iApply "IH". done.
    - rewrite /mgc_of_trace /extract_calls omap_cons_None //.
      rewrite Forall_cons in Hvalid_trace.
      destruct Hvalid_trace as [_ Hvalid_trace].
      iApply "IH". done.
    - rewrite /mgc_of_trace /extract_calls omap_cons_None //.
      rewrite Forall_cons in Hvalid_trace.
      destruct Hvalid_trace as [_ Hvalid_trace].
      iApply "IH". done.
  Qed.
End spec.

Definition init_spec_type `{!heapGS Σ, !traceG Σ} := init_spec_type_gen True.
Definition mgc_spec `{!heapGS Σ, !traceG Σ} := mgc_spec_gen True.

Section adequacy.
  Context (ops : list val) (obj : val).
  Context (valid_requests : list (val → Prop)).

  Notation adv_step := (adv_step ops obj valid_requests).

  (* Simulated steps.
    Thread pool:
      main_thread::[op threads; ...]++other threads
      where other threads include threads used to generate nodet_bool, and threads
      forked by op threads.

    State:
      σ ⊎ {[ tracer = ts ]} ⊎ σ_ext
      where σ is the state in adv_steps, σ_ext is the state used to generate nodet_bool,
      and tracer is the location to store the trace. *)
  Section simulated.
    Context (tracer : loc).

    Definition trace_to_state (ts : list (positive*trace)) :=
      {| heap := {[tracer := Some (encode_trace ts);
                   (tracer +ₗ 1) := Some NONEV;
                   (tracer +ₗ 2) := Some #false]};
         used_proph_id := ∅ |}.

    Definition compose_state σ ts :=
      σ ∪ trace_to_state ts.

    Definition composable_state σ :=
      {[tracer; tracer +ₗ 1; tracer +ₗ 2]} ## dom σ.(heap).

    Definition simulatedOp_idle '(n, req) : expr :=
      call_ret_wrapper tracer n (list_nth #n (encode_val ops)) obj (req : val);; #().

    Definition simulatedOp_pending_ctx τ :=
      [AppRCtx (λ: "res", trace_emit #tracer #(Z.pos τ) (InjR "res");; "res"); AppRCtx (λ: <>, #())].

    Definition simulatedOp_done := Val #().

    Definition pending_to_simulated (op : pendingOp) : expr :=
      match op with
      | (τ, Some e) => fill (simulatedOp_pending_ctx τ) e
      | (_, None) => simulatedOp_done
      end.

    Lemma base_step_composable_state e σ κs e' σ' efs :
      base_step e σ κs e' σ' efs →
      composable_state σ' → composable_state σ.
    Proof.
      intros Hbase_step Htracer_σ'.
      apply base_step_heap_subdom in Hbase_step as Hdom_heap.
      rewrite /composable_state in Htracer_σ' |- *. set_solver.
    Qed.

    Lemma prim_step_composable_state e σ κs e' σ' efs :
      prim_step e σ κs e' σ' efs →
      composable_state σ' → composable_state σ.
    Proof.
      intros Hprim_step Htracer_σ'.
      apply prim_step_heap_subdom in Hprim_step as Hdom_heap.
      rewrite /composable_state in Htracer_σ' |- *. set_solver.
    Qed.

    Lemma step_composable_state t σ κs t' σ' :
      step (t, σ) κs (t', σ') →
      composable_state σ' → composable_state σ.
    Proof.
      intros Hstep Htracer_σ'.
      apply step_heap_subdom in Hstep as Hdom_heap.
      rewrite /composable_state in Htracer_σ' |- *. set_solver.
    Qed.

    Lemma erased_step_composable_state t σ t' σ' :
      erased_step (t, σ) (t', σ') →
      composable_state σ' → composable_state σ.
    Proof.
      intros Hstep Htracer_σ'.
      apply erased_step_heap_subdom in Hstep as Hdom_heap.
      rewrite /composable_state in Htracer_σ' |- *. set_solver.
    Qed.

    Lemma erased_nsteps_composable_state n t σ t' σ' :
      relations.nsteps erased_step n (t, σ) (t', σ') →
      composable_state σ' → composable_state σ.
    Proof.
      intros Hstep Htracer_σ'.
      apply erased_nsteps_heap_subdom in Hstep as Hdom_heap.
      rewrite /composable_state in Htracer_σ' |- *. set_solver.
    Qed.

    Lemma erased_steps_composable_state t σ t' σ' :
      rtc erased_step (t, σ) (t', σ') →
      composable_state σ' → composable_state σ.
    Proof.
      intros Hstep Htracer_σ'.
      apply erased_steps_heap_subdom in Hstep as Hdom_heap.
      rewrite /composable_state in Htracer_σ' |- *. set_solver.
    Qed.

    Lemma adv_steps_composable_state σ σ' pendingOp pendingOp' childThread childThread' ts :
      rtcL adv_step (Config pendingOp childThread σ) (Config pendingOp' childThread' σ') ts →
      composable_state σ' → composable_state σ.
    Proof.
      intros Hadv_steps Htracer_σ'.
      apply adv_steps_heap_subdom in Hadv_steps as Hdom_heap.
      rewrite /composable_state in Htracer_σ' |- *. set_solver.
    Qed.

    Local Lemma tracer_neq_1 : tracer +ₗ 1 ≠ tracer.
    Proof. destruct tracer. rewrite /Loc.add. intros HFalse. injection HFalse. lia. Qed.
    Local Lemma tracer_neq_2 : tracer +ₗ 2 ≠ tracer.
    Proof. destruct tracer. rewrite /Loc.add. intros HFalse. injection HFalse. lia. Qed.
    Local Lemma tracer_neq_12 : tracer +ₗ 2 ≠ tracer +ₗ 1.
    Proof. destruct tracer. rewrite /Loc.add. intros HFalse. injection HFalse. lia. Qed.

    Local Lemma dom_trace_to_state ts :
      dom (heap (trace_to_state ts)) = {[tracer; tracer+ₗ1; tracer+ₗ2]}.
    Proof.
      clear.
      rewrite /trace_to_state /=.
      rewrite dom_insert_L dom_insert_L dom_singleton_L. set_solver.
    Qed.

    Lemma compose_state_lookup_trace0 σ ts :
      {[ tracer; tracer+ₗ1; tracer+ₗ2 ]} ## dom (heap σ) →
      heap (compose_state σ ts) !! tracer = Some (Some (encode_trace ts)).
    Proof.
      intros Hfresh.
      rewrite /compose_state /union /state_union /=.
      apply lookup_union_Some_r.
      - apply map_disjoint_dom. rewrite dom_trace_to_state. done.
      - rewrite /trace_to_state /=. by apply lookup_insert_eq.
    Qed.

    Lemma compose_state_lookup_trace1 σ ts :
      {[ tracer; tracer+ₗ1; tracer+ₗ2 ]} ## dom (heap σ) →
      heap (compose_state σ ts) !! (tracer+ₗ1) = Some (Some NONEV).
    Proof.
      pose proof tracer_neq_1.
      intros Hfresh.
      rewrite /compose_state /union /state_union /=.
      apply lookup_union_Some_r.
      - apply map_disjoint_dom. rewrite dom_trace_to_state. done.
      - rewrite /trace_to_state /=.
        rewrite lookup_insert_ne //. by rewrite lookup_insert_eq.
    Qed.

    Lemma compose_state_lookup_trace2 σ ts :
      {[ tracer; tracer+ₗ1; tracer+ₗ2 ]} ## dom (heap σ) →
      heap (compose_state σ ts) !! (tracer+ₗ2) = Some (Some #false).
    Proof.
      pose proof tracer_neq_2. pose proof tracer_neq_12.
      intros Hfresh.
      rewrite /compose_state /union /state_union /=.
      apply lookup_union_Some_r.
      - apply map_disjoint_dom. rewrite dom_trace_to_state. done.
      - rewrite /trace_to_state /=.
        rewrite lookup_insert_ne //.
        rewrite lookup_insert_ne //.
        by rewrite lookup_singleton_eq.
    Qed.

    (* We have to reasoning [rtc erased_step] without a program logic because the adequacy
      theorem is not strong enough to prove the concrete form of child threads. *)

    (* mgc -->* [simulatedOp_idle]s, with the fixed background thread kept at index 1. *)
    Lemma simulate_create (calls : list (nat*val)) σ :
      rtc erased_step ([concurrent_calls tracer calls (encode_val ops) obj;
                        nondet_bool_prealloc_bg #(tracer +ₗ 2)], σ)
                      (trace_peak #tracer :: nondet_bool_prealloc_bg #(tracer +ₗ 2)
                                          :: (simulatedOp_idle <$> calls), σ).
    Proof.
      induction calls as [|[opid request] calls IH]; first reflexivity.
      change ((opid,request) :: calls) with ([(opid,request)] ++ calls).
      rewrite fmap_app.
      simpl.
      etrans; last first.
      { change ([trace_peak #tracer; nondet_bool_prealloc_bg #(tracer +ₗ 2);
                  simulatedOp_idle (opid,request)] ++ (simulatedOp_idle <$> calls))
          with ([trace_peak #tracer; nondet_bool_prealloc_bg #(tracer +ₗ 2)]
                  ++ [simulatedOp_idle (opid,request)] ++ (simulatedOp_idle <$> calls)).
        change ([concurrent_calls tracer calls (encode_val ops) obj;
                 nondet_bool_prealloc_bg #(tracer +ₗ 2);
                 simulatedOp_idle (opid,request)])
          with ([concurrent_calls tracer calls (encode_val ops) obj;
                 nondet_bool_prealloc_bg #(tracer +ₗ 2)]
                  ++ [simulatedOp_idle (opid,request)]).
        apply (erased_steps_app_r
                 [concurrent_calls tracer calls (encode_val ops) obj;
                  nondet_bool_prealloc_bg #(tracer +ₗ 2)] σ
                 [trace_peak #tracer; nondet_bool_prealloc_bg #(tracer +ₗ 2)]
                 (simulatedOp_idle <$> calls) σ
                 [simulatedOp_idle (opid,request)]); [reflexivity|exact IH]. }
      apply (rtc_l _ _ ([(#();;concurrent_calls tracer calls (encode_val ops) obj)%E;
                          nondet_bool_prealloc_bg #(tracer +ₗ 2);
                          simulatedOp_idle (opid,request)], σ)).
      - set (K:=[AppRCtx (λ: <>, concurrent_calls tracer calls (encode_val ops) obj)]).
        change (concurrent_call tracer opid request (encode_val ops) obj;;
                  concurrent_calls tracer calls (encode_val ops) obj)%E
          with (fill K (concurrent_call tracer opid request (encode_val ops) obj)).
        change (#();; concurrent_calls tracer calls (encode_val ops) obj)%E
          with (fill K #()).
        apply (fill_erased_step K _ σ _ σ [] _ [] _); first reflexivity.
        rewrite /concurrent_call.
        exists [].
        eapply (step_atomic _ _ _ _ _ [] [nondet_bool_prealloc_bg #(tracer +ₗ 2)]);
          [reflexivity..|].
        apply base_prim_step. constructor.
      - do 2 erased_steps_pure. simpl. reflexivity.
    Qed.

    (**********************************************************)
    (* Begin LLM-generated code. *)
    (* tool: Claude Code 2.1.77
       model: Claude Opus 4.6 with 1M context (claude-opus-4-6)
       parameters:
          effort = high
          context window = 1000000
          max output tokens = 128000 *)
    (* Lemma types in this block are written by human, and only proofs
      are LLM-generated. *)
    Local Lemma compose_state_state_init_heap l n v σ ts :
      composable_state (state_init_heap l n v σ) →
      compose_state (state_init_heap l n v σ) ts
        = state_init_heap l n v (compose_state σ ts).
    Proof.
      intros _.
      rewrite /compose_state /state_init_heap /state_upd_heap /trace_to_state.
      destruct σ as [h p].
      rewrite /union /state_union /=. f_equal.
      rewrite -!(assoc (∪)). done.
    Qed.

    Local Lemma compose_state_lookup_heap l σ ts :
      composable_state σ → is_Some (heap σ !! l) →
      heap (compose_state σ ts) !! l = heap σ !! l.
    Proof.
      intros _ Hv.
      rewrite /compose_state /union /state_union /=.
      destruct Hv as [v Hv].
      rewrite Hv. apply lookup_union_Some_l. done.
    Qed.

    Local Lemma compose_state_state_init_heap_fresh l n v σ ts :
      (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
      composable_state (state_init_heap l n v σ) →
      ∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap (compose_state σ ts) !! (l +ₗ i) = None.
    Proof.
      intros Hfresh Htracer i Hi0 Hin.
      assert (Hli_in : l +ₗ i ∈ dom (heap (state_init_heap l n v σ))).
      { simpl. rewrite dom_union_L.
        apply elem_of_union_l, elem_of_dom. eexists. apply heap_array_lookup.
        exists i, v. split_and!; [lia|done|done|].
        apply lookup_replicate. split; [done|lia]. }
      rewrite /compose_state /union /state_union /=.
      apply lookup_union_None. split.
      - by apply Hfresh.
      - apply not_elem_of_dom_1.
        rewrite /composable_state in Htracer.
        intros Hin'.
        rewrite -(dom_trace_to_state ts) in Htracer.
        by apply (Htracer (l +ₗ i)).
    Qed.

    Local Lemma compose_state_state_upd_heap l v σ ts :
      composable_state σ → is_Some (heap σ !! l) →
      compose_state (state_upd_heap <[l:=v]> σ) ts
        = state_upd_heap <[l:=v]> (compose_state σ ts).
    Proof.
      intros _ _.
      rewrite /compose_state /state_upd_heap /trace_to_state.
      destruct σ as [h p].
      rewrite /union /state_union /=. f_equal.
      rewrite insert_union_l. done.
    Qed.

    Local Lemma compose_state_state_upd_proph_id p σ ts :
      composable_state (state_upd_used_proph_id (union {[p]}) σ) →
      compose_state (state_upd_used_proph_id (union {[p]}) σ) ts
        = state_upd_used_proph_id (union {[p]}) (compose_state σ ts).
    Proof.
      intros _.
      rewrite /compose_state /state_upd_used_proph_id /trace_to_state.
      destruct σ.
      rewrite /union /state_union /=.
      f_equal.
      apply set_eq. intros x. rewrite !elem_of_union elem_of_empty. set_solver.
    Qed.

    Local Lemma compose_state_state_upd_proph_id_fresh p σ ts :
      composable_state (state_upd_used_proph_id (union {[p]}) σ) →
      p ∉ used_proph_id σ →
      p ∉ used_proph_id (compose_state σ ts).
    Proof.
      intros _ Hnotin.
      rewrite /compose_state /union /state_union /=.
      set_solver.
    Qed.
    (* End LLM-generated code. *)
    (**********************************************************)

    Local Lemma compose_state_used_proph_id_elemof p σ ts :
      p ∈ used_proph_id σ →
      p ∈ used_proph_id (compose_state σ ts).
    Proof. rewrite /compose_state /union /state_union /=. set_solver. Qed.

    (* idle --> pending.  The background thread sits at the head of the pool. *)
    Lemma simulate_call n τ req t1 t2 σ ts :
      τ ∉ ts.*1 →
      composable_state σ →
      rtc erased_step
        (nondet_bool_prealloc_bg #(tracer +ₗ 2) :: t1 ++ simulatedOp_idle (n,req) :: t2,
         compose_state σ ts)
        (nondet_bool_prealloc_bg #(tracer +ₗ 2) :: t1 ++
           fill (simulatedOp_pending_ctx τ) ((ops!!!n: val) obj req) :: t2,
         compose_state σ (ts ++ [(τ, Call n req)])).
    Proof.
      intros Hfresh Hcompose.
      pose proof tracer_neq_1. pose proof tracer_neq_2. pose proof tracer_neq_12.
      opose proof (erased_steps_trace_fresh τ (Call n req) (InjLV (#n,req)) tracer
        ts (compose_state σ ts) (decode_encode_val (Call n req)) Hfresh _ _ _)
        as Hprim_steps.
      { by apply compose_state_lookup_trace0. }
      { by apply compose_state_lookup_trace1. }
      { by apply compose_state_lookup_trace2. }
      rewrite /simulatedOp_idle /call_ret_wrapper /simulatedOp_pending_ctx.
      (* Step pure on the [simulatedOp_idle] thread, with the bg thread at the head. *)
      apply (erased_steps_cons_r_cons_nofork _ _ t1 t2).
      erased_steps_apply2 erased_steps_list_nth.
      repeat erased_steps_pure2.
      erased_steps_2apply Hprim_steps.
      repeat erased_steps_pure2.
      evar (σ' : state).
      replace (compose_state σ (ts ++ [(τ,Call n req)])) with ?σ';
        first apply reflexivity.
      clear σ'.
      rewrite /compose_state /trace_to_state.
      destruct σ as [h p]. rewrite /union /state_union /=. f_equal.
      rewrite insert_union_r; last first.
      { apply not_elem_of_dom_1.
        rewrite /composable_state in Hcompose. set_solver. }
      rewrite insert_insert_eq.
      rewrite encode_trace_snoc //.
    Qed.

    Lemma simulate_base_step e1 σ1 κs e2 σ2 efs ts :
      base_step e1 σ1 κs e2 σ2 efs →
      composable_state σ2 →
      base_step e1 (compose_state σ1 ts) κs e2 (compose_state σ2 ts) efs.
    Proof.
      intros Hbase_step Hcompose'.
      eapply base_step_composable_state in Hcompose' as Hcompose; last exact Hbase_step.
      induction Hbase_step; try solve [econstructor; eauto].
      - rewrite compose_state_state_init_heap //.
        econstructor; first done.
        by eapply compose_state_state_init_heap_fresh.
      - rewrite compose_state_state_upd_heap //.
        econstructor.
        rewrite compose_state_lookup_heap //.
      - econstructor.
        rewrite compose_state_lookup_heap //.
      - rewrite compose_state_state_upd_heap //.
        econstructor.
        rewrite compose_state_lookup_heap //.
      - rewrite compose_state_state_upd_heap //.
        econstructor.
        rewrite compose_state_lookup_heap //.
      - rename select bool into b.
        destruct b.
        + rewrite compose_state_state_upd_heap //.
          econstructor; auto.
          rewrite compose_state_lookup_heap //.
        + econstructor; auto.
          rewrite compose_state_lookup_heap //.
      - rewrite compose_state_state_upd_heap //.
        econstructor.
        rewrite compose_state_lookup_heap //.
      - rewrite compose_state_state_upd_proph_id //.
        econstructor.
        by apply compose_state_state_upd_proph_id_fresh.
      - econstructor; first by eauto.
        by apply compose_state_used_proph_id_elemof.
    Qed.

    Lemma simulate_prim_step e1 σ1 κs e2 σ2 efs ts :
      prim_step e1 σ1 κs e2 σ2 efs →
      composable_state σ2 →
      prim_step e1 (compose_state σ1 ts) κs e2 (compose_state σ2 ts) efs.
    Proof.
      intros [] ?. econstructor; [eassumption..|].
      by eapply simulate_base_step.
    Qed.

    Lemma simulate_step t1 σ1 κs t2 σ2 ts :
      step (t1, σ1) κs (t2, σ2) →
      composable_state σ2 →
      step (t1, (compose_state σ1 ts)) κs (t2, (compose_state σ2 ts)).
    Proof.
      intros [] ?. simplify_eq. econstructor; [reflexivity..|].
      by eapply simulate_prim_step.
    Qed.

    Lemma simulate_erased_step t1 σ1 t2 σ2 ts :
      erased_step (t1, σ1) (t2, σ2) →
      composable_state σ2 →
      erased_step (t1, (compose_state σ1 ts)) (t2, (compose_state σ2 ts)).
    Proof. intros [] ?. eexists. by eapply simulate_step. Qed.

    Lemma simulate_erased_nsteps n t1 σ1 t2 σ2 ts :
      relations.nsteps erased_step n (t1, σ1) (t2, σ2) →
      composable_state σ2 →
      relations.nsteps erased_step n (t1, (compose_state σ1 ts)) (t2, (compose_state σ2 ts)).
    Proof.
      revert t1 σ1 t2 σ2 ts.
      induction n as [|n IH] => t1 σ1 t2 σ2 ts Hnsteps Hcompose2;
        inversion Hnsteps; simplify_eq. { apply nsteps_O. }
      rename select (cfg _) into ρ.
      destruct ρ as [tm σm].
      eapply nsteps_l; last by apply IH.
      apply simulate_erased_step; first done.
      by eapply erased_nsteps_composable_state.
    Qed.

    Lemma simulate_erased_steps t1 σ1 t2 σ2 ts :
      rtc erased_step (t1, σ1) (t2, σ2) →
      composable_state σ2 →
      rtc erased_step (t1, (compose_state σ1 ts)) (t2, (compose_state σ2 ts)).
    Proof.
      intros [??]%rtc_nsteps_1 ?.
      eapply rtc_nsteps_2.
      by eapply simulate_erased_nsteps.
    Qed.

    (* step pending *)
    Lemma simulate_intermediate τ e1 σ1 κs e2 σ2 efs t1 t2 ts :
      prim_step e1 σ1 κs e2 σ2 efs →
      composable_state σ2 →
      rtc erased_step
        (nondet_bool_prealloc_bg #(tracer +ₗ 2) :: t1
          ++ fill (simulatedOp_pending_ctx τ) e1 :: t2, compose_state σ1 ts)
        (nondet_bool_prealloc_bg #(tracer +ₗ 2) :: t1
          ++ fill (simulatedOp_pending_ctx τ) e2 :: t2 ++ efs, compose_state σ2 ts).
    Proof.
      intros Hprim_step Hcompose.
      apply erased_steps_cons_l.
      apply rtc_once.
      exists κs. eapply step_atomic; [reflexivity..|].
      destruct Hprim_step as [K e1' e2' -> -> Hbase_step].
      apply fill_prim_step, fill_prim_step, base_prim_step.
      simpl in *.
      by apply simulate_base_step.
    Qed.

    (* step child *)
    Lemma simulate_child e1 σ1 κs e2 σ2 efs t1 t2 ts :
      prim_step e1 σ1 κs e2 σ2 efs →
      composable_state σ2 →
      rtc erased_step
        (nondet_bool_prealloc_bg #(tracer +ₗ 2) :: t1 ++ e1 :: t2, compose_state σ1 ts)
        (nondet_bool_prealloc_bg #(tracer +ₗ 2) :: t1 ++ e2 :: t2 ++ efs, compose_state σ2 ts).
    Proof.
      intros Hprim_step Hcompose.
      apply erased_steps_cons_l.
      apply rtc_once.
      exists κs. eapply step_atomic; [reflexivity..|].
      destruct Hprim_step as [K e1' e2' -> -> Hbase_step].
      apply fill_prim_step, base_prim_step.
      simpl in *.
      by apply simulate_base_step.
    Qed.

    (* pending -> done *)
    Lemma simulate_ret τ res t1 t2 σ ts :
      composable_state σ →
      rtc erased_step
        (nondet_bool_prealloc_bg #(tracer +ₗ 2) :: t1
          ++ fill (simulatedOp_pending_ctx τ) (Val res) :: t2, compose_state σ ts)
        (nondet_bool_prealloc_bg #(tracer +ₗ 2) :: t1
          ++ simulatedOp_done :: t2, compose_state σ (ts ++ [(τ, Ret res)])).
    Proof.
      intros Hcompose.
      apply erased_steps_cons_l.
      apply erased_steps_app_l, erased_steps_cons_r_nofork.
      simpl. repeat erased_steps_pure.
      erased_steps_apply (erased_steps_trace_emit (A:=trace)).
      { reflexivity. }
      { by apply compose_state_lookup_trace0. }
      { by apply compose_state_lookup_trace1. }
      repeat erased_steps_pure.
      rewrite /simulatedOp_done.
      evar (σ' : state).
      replace (compose_state σ (ts ++ [(τ,Ret res)])) with ?σ';
        first reflexivity.
      clear σ'.
      rewrite /compose_state /trace_to_state /(union (A:=state)) /state_union /=. f_equal.
      rewrite insert_union_r; last first.
      { apply not_elem_of_dom_1.
        rewrite /composable_state in Hcompose. set_solver. }
      f_equal. rewrite insert_insert_eq encode_trace_snoc //.
    Qed.

    (* Inductive step of [mgc_match_adv_steps].
      The pool's tail equals [childThread] directly: no [other_ts]
      indirection, no index list [M].  The fixed background thread sits
      at index 1, just after [trace_peak #tracer]. *)
    Lemma mgc_match_adv_steps_ind σ σ' pendingOp pendingOp' childThread childThread' ts0 ts :
      rtcL adv_step (Config pendingOp childThread σ) (Config pendingOp' childThread' σ') ts →
      (list_to_set pendingOp.*1 : gset positive) = list_to_set (ts0.*1) →
      composable_state σ' →
      rtc erased_step
        (trace_peak #tracer :: nondet_bool_prealloc_bg #(tracer +ₗ 2)
          :: (pending_to_simulated <$> pendingOp)
          ++ (simulatedOp_idle <$> extract_calls ts) ++ childThread,
         compose_state σ ts0)
        (trace_peak #tracer :: nondet_bool_prealloc_bg #(tracer +ₗ 2)
          :: (pending_to_simulated <$> pendingOp') ++ childThread',
         compose_state σ' (ts0 ++ ts)).
    Proof.
      intros Hadv_steps. revert ts0.
      remember (Config pendingOp childThread σ) as config0 eqn:Heq0.
      remember (Config pendingOp' childThread' σ') as config2 eqn:Heq2.
      replace pendingOp with (config0.(config_pendingOp)) by by subst.
      replace childThread with (config0.(config_childThread)) by by subst.
      replace σ with (config0.(config_state)) by by subst.
      replace σ' with (config2.(config_state)) by by subst.
      replace pendingOp' with (config2.(config_pendingOp)) by by subst.
      replace childThread' with (config2.(config_childThread)) by by subst.
      clear σ σ' pendingOp pendingOp' childThread childThread' Heq0 Heq2.
      induction Hadv_steps as [config|config0 config1 config2 ts1 ts2 Hadv_step Hadv_steps IH]
        => ts0 Hsame_tag Hcompose.
      { rewrite right_id_L. reflexivity. }
      destruct config2 as [pendingOp_final childThread_final σ_final].
      destruct Hadv_step as [
          n req τ π efs σ Hfreshτ Hvalid_req
        | τ π₁ π₂ efs e e' σ σ' κ ef Hprim_step
        | π efs1 efs2 e e' σ σ' κ ef Hprim_step
        | τ π₁ π₂ efs res σ ]; simpl in *.
      - (* call *)
        opose proof (simulate_call n τ req
          (pending_to_simulated <$> π) ((simulatedOp_idle <$> extract_calls ts2) ++ efs)
          σ ts0 _ _) as Hstep.
        { by rewrite -(not_elem_of_list_to_set (C:=gset positive)) -Hsame_tag not_elem_of_list_to_set. }
        { by eapply adv_steps_composable_state. }
        opose proof (IH (ts0++[(τ,Call n req)]) _ Hcompose) as Hsteps.
        { rewrite !fmap_app. rewrite !list_to_set_app_L. f_equal. done. }
        apply (erased_steps_cons_l (trace_peak #tracer)) in Hstep.
        rewrite fmap_app /= -!app_assoc /= in Hsteps.
        etrans; [exact Hstep|exact Hsteps].
      - (* intermediate *)
        opose proof (simulate_intermediate τ e σ κ e' σ' ef
          (pending_to_simulated <$> π₁) ((pending_to_simulated <$> π₂)
            ++ (simulatedOp_idle <$> extract_calls ts2) ++ efs) ts0
          Hprim_step _) as Hstep.
        { by eapply adv_steps_composable_state. }
        opose proof (IH ts0 _ Hcompose) as Hsteps.
        { rewrite -Hsame_tag !fmap_app !fmap_cons. reflexivity. }
        apply (erased_steps_cons_l (trace_peak #tracer)) in Hstep.
        simpl in Hstep.
        rewrite !fmap_app /= -!app_assoc /= in Hsteps |- *.
        rewrite -!app_assoc in Hstep.
        etrans; [exact Hstep|exact Hsteps].
      - (* child *)
        opose proof (simulate_child e σ κ e' σ' ef
          ((pending_to_simulated <$> π) ++ (simulatedOp_idle <$> extract_calls ts2) ++ efs1)
          efs2 ts0 Hprim_step _) as Hstep.
        { by eapply adv_steps_composable_state. }
        opose proof (IH ts0 Hsame_tag Hcompose) as Hsteps.
        apply (erased_steps_cons_l (trace_peak #tracer)) in Hstep.
        rewrite -!(app_assoc _ _ _) in Hstep.
        etrans; [exact Hstep|exact Hsteps].
      - (* return *)
        opose proof (simulate_ret τ res
          (pending_to_simulated <$> π₁) ((pending_to_simulated <$> π₂)
            ++ (simulatedOp_idle <$> extract_calls ts2) ++ efs)
          σ ts0 _) as Hstep.
        { by eapply adv_steps_composable_state. }
        opose proof (IH (ts0++[(τ,Ret res)]) _ Hcompose) as Hsteps.
        { rewrite (fmap_app fst ts0) list_to_set_app_L -Hsame_tag.
          rewrite !fmap_app !fmap_cons fmap_nil /= right_id_L.
          rewrite !list_to_set_app_L !list_to_set_cons.
          set_solver. }
        apply (erased_steps_cons_l (trace_peak #tracer)) in Hstep.
        rewrite !fmap_app /= -!app_assoc /= in Hsteps |- *.
        etrans; [exact Hstep|exact Hsteps].
    Qed.
  End simulated.

  Lemma mgc_match_adv_steps σ config' ts (tracer : loc) :
    {[tracer; tracer +ₗ 1; tracer +ₗ 2]} ## dom (config'.(config_state).(heap)) →
    rtcL adv_step (Config [] [] σ) config' ts →
    rtc erased_step
      ([mgc_of_trace tracer ts (encode_val ops) obj;
        nondet_bool_prealloc_bg #(tracer +ₗ 2)],
       compose_state tracer σ [])
      (Val (encode_trace ts) :: nondet_bool_prealloc_bg #(tracer +ₗ 2)
        :: (pending_to_simulated tracer <$> config'.(config_pendingOp))
        ++ config'.(config_childThread),
       compose_state tracer config'.(config_state) ts).
  Proof.
    intros Htracer_fresh Hadv_steps.
    destruct config' as [π_final child_final σ']; simpl in *.
    rewrite /mgc_of_trace.
    do 3 erased_steps_pure. rewrite concurrent_call_subst.
    etrans; [apply simulate_create|].
    opose proof (mgc_match_adv_steps_ind tracer σ σ' [] π_final [] child_final []
                  ts Hadv_steps eq_refl Htracer_fresh) as Hsteps.
    simpl in Hsteps.
    rewrite right_id_L /= in Hsteps.
    etrans; [exact Hsteps|].
    apply (erased_steps_cons_r_nofork).
    rewrite /trace_peak. erased_steps_pure.
    erased_steps_apply erased_step_load; last reflexivity.
    by apply compose_state_lookup_trace0.
  Qed.
End adequacy.

(*************** Begin LLM-generated code. ****************)
(*  Claude Opus 4.7 (1M context, xhigh effort, v2.1.111)  *)

Class adv_mgcG Σ := {
  #[local] adv_mgcG_meta      :: inG Σ (agreeR (prodO gnameO gnameO));
  #[local] adv_mgcG_pendingOp :: ghost_mapG Σ positive expr;
  #[local] adv_mgcG_child     :: ghost_mapG Σ nat expr;
}.
Definition adv_mgcΣ : gFunctors :=
  #[ GFunctor (agreeRF (prodO gnameO gnameO));
     ghost_mapΣ positive expr;
     ghost_mapΣ nat expr ].
Global Instance subG_adv_mgcG Σ : subG adv_mgcΣ Σ → adv_mgcG Σ.
Proof. solve_inG. Qed.

Section requisteness.
  Let Σ := #[heapΣ; traceΣ; adv_mgcΣ; completenessΣ heap_lang].
  Context (valid_reqs : list (val → Prop)).
  Context (init : expr) (ops : list val).
  Context (σ₀ : state).

  Definition I_adv ts :=
    ∃ obj efs σ config',
      rtc erased_step ([init],σ₀) (Val obj::efs,σ)
    ∧ rtcL (adv_step ops obj valid_reqs) (Config [] [] σ) config' ts.

  Definition advN := nroot .@ "iris_logatom.heap_lang.mgc.adv".

  (** Pair each child thread expression with its 0-based index. *)
  (* TODO: replace with list_to_imap *)
  Local Definition child_indexed (efs : list expr) : list (nat * expr) :=
    imap (λ i e, (i : nat, e)) efs.

  Local Lemma child_indexed_lookup_iff (efs : list expr) (i : nat) (e : expr) :
    (i, e) ∈ child_indexed efs ↔ efs !! i = Some e.
  Proof.
    rewrite /child_indexed.
    rewrite list_elem_of_lookup. split.
    - intros (j & Hj). rewrite list_lookup_imap in Hj.
      destruct (efs !! j) as [e'|] eqn:He'; cbn in Hj; last done.
      injection Hj as -> ->. done.
    - intros He. exists i. rewrite list_lookup_imap He //.
  Qed.

  Local Lemma child_indexed_fst_seq (efs : list expr) :
    (child_indexed efs).*1 = seq O (length efs).
  Proof.
    rewrite /child_indexed.
    revert efs.
    enough (∀ (start : nat) (efs : list expr),
              ((imap (λ i e, ((start + i)%nat : nat, e)) efs).*1 : list nat)
              = seq start (length efs)) as Haux.
    { intros efs. specialize (Haux O efs).
      rewrite /imap in Haux. rewrite /imap. apply Haux. }
    intros start efs. revert start.
    induction efs as [|e efs IH]; intros start; first done.
    rewrite imap_cons fmap_cons /=.
    rewrite Nat.add_0_r. f_equal.
    rewrite -(IH (Datatypes.S start)).
    apply f_equal. apply imap_ext.
    intros i e' _. apply pair_equal_spec. split; [lia|done].
  Qed.

  Local Lemma child_indexed_nodup (efs : list expr) :
    NoDup (child_indexed efs).*1.
  Proof. rewrite child_indexed_fst_seq. apply NoDup_seq. Qed.

  Local Lemma child_indexed_split (efs : list expr) (i : nat) (e : expr) :
    efs !! i = Some e →
    ∃ efs1 efs2, efs = efs1 ++ e :: efs2 ∧ length efs1 = i.
  Proof.
    intros He.
    exists (take i efs), (drop (Datatypes.S i) efs).
    split.
    - symmetry. by apply take_drop_middle.
    - rewrite length_take Nat.min_l //. apply Nat.lt_le_incl.
      by eapply lookup_lt_Some.
  Qed.

  Local Lemma child_indexed_app_imap (efs1 efs2 : list expr) :
    child_indexed (efs1 ++ efs2) =
    child_indexed efs1
    ++ imap (λ (i : nat) (e0 : expr), ((length efs1 + i)%nat : nat, e0)) efs2.
  Proof. rewrite /child_indexed imap_app //. Qed.

  Local Lemma child_indexed_keys_geq_length (n : nat) (efs2 : list expr) :
    ∀ (k : nat) (e0 : expr),
      (k, e0) ∈ imap (λ i e', ((Datatypes.S n + i)%nat : nat, e')) efs2 →
      k ≥ Datatypes.S n.
  Proof.
    intros k e0 Hin.
    rewrite list_elem_of_lookup in Hin.
    destruct Hin as (j & Hj). rewrite list_lookup_imap in Hj.
    destruct (efs2 !! j); cbn in Hj; last done.
    injection Hj as <- _. lia.
  Qed.

  Local Lemma child_indexed_replace_step efs1 e e' efs2 :
    <[length efs1 := e']>
      (list_to_map (child_indexed (efs1 ++ e :: efs2)) : gmap nat expr)
    = list_to_map (child_indexed (efs1 ++ e' :: efs2)).
  Proof.
    rewrite !child_indexed_app_imap.
    cbn [imap].
    rewrite Nat.add_0_r.
    rewrite !list_to_map_app.
    rewrite (list_to_map_cons _ _ e').
    rewrite (list_to_map_cons _ _ e).
    assert (Hl1 :
      (list_to_map (child_indexed efs1) : gmap nat expr) !! (length efs1) = None).
    { apply not_elem_of_list_to_map_1.
      rewrite child_indexed_fst_seq.
      rewrite elem_of_seq. lia. }
    assert (Hl2 :
      (list_to_map (imap (λ i e0, ((Datatypes.S (length efs1) + i)%nat : nat, e0)) efs2)
        : gmap nat expr) !! (length efs1) = None).
    { apply not_elem_of_list_to_map_1.
      intros Hin.
      rewrite list_elem_of_fmap in Hin.
      destruct Hin as ([k e0] & Heq & Hin').
      cbn in Heq. subst k.
      apply child_indexed_keys_geq_length in Hin'. lia. }
    rewrite insert_union_r // insert_insert_eq //.
  Qed.

  Local Lemma child_indexed_extend_step efs1 e' efs2 ef :
    list_to_map (child_indexed ((efs1 ++ e' :: efs2) ++ ef))
    = list_to_map (child_indexed (efs1 ++ e' :: efs2))
      ∪ (list_to_map (imap (λ i e0,
                             ((length (efs1 ++ e' :: efs2) + i)%nat : nat, e0)) ef)
         : gmap nat expr).
  Proof.
    rewrite child_indexed_app_imap.
    rewrite list_to_map_app //.
  Qed.

  Local Lemma nsteps_O_eq_helper {A} (R : relation A) (x y : A) :
    relations.nsteps R 0 x y → x = y.
  Proof. by inversion 1. Qed.

  (** Cancellation of [state] union from the left: from
      [σ ∪ σ_a = σ ∪ σ_b] with [σ ## σ_a] and [σ ## σ_b], conclude
      [σ_a = σ_b]. *)
  Local Lemma state_union_cancel_l (σ σ_a σ_b : state) :
    σ ## σ_a → σ ## σ_b → σ ∪ σ_a = σ ∪ σ_b → σ_a = σ_b.
  Proof.
    intros [Hh_a Hp_a] [Hh_b Hp_b] Heq.
    destruct σ as [h p], σ_a as [h_a p_a], σ_b as [h_b p_b].
    cbn in Hh_a, Hh_b, Hp_a, Hp_b.
    rewrite /union /state_union /= in Heq.
    injection Heq as Heq_h Heq_p.
    f_equal.
    - apply (map_union_cancel_l h_a h_b h);
        [by apply map_disjoint_sym|by apply map_disjoint_sym|exact Heq_h].
    - clear -Hp_a Hp_b Heq_p. set_solver.
  Qed.

  (** Reverse simulation, single step: a step on a [compose_state] in
      which the head expression is reducible at the [σ] component is
      mirrored by a step on [σ] alone, leaving the tracer cells
      untouched. *)
  Local Lemma erased_step_compose_uncompose
        (tracer : loc) (σ : state) (ts : list (positive*trace))
        (e1 e2 : expr) (σ_compose' : state) :
    composable_state tracer σ →
    reducible e1 σ →
    erased_step ([e1], compose_state tracer σ ts) ([e2], σ_compose') →
    ∃ σ', composable_state tracer σ' ∧
      σ_compose' = compose_state tracer σ' ts ∧
      erased_step ([e1], σ) ([e2], σ').
  Proof.
    intros Hcomp Hred [κ Hstep].
    destruct Hstep as [eA σA eA' σA' efs t1V t2V Heq1 Heq2 Hprim_step].
    injection Heq1 as Heq1_t Heq1_s.
    injection Heq2 as Heq2_t Heq2_s.
    subst σA σA'.
    destruct t1V as [|? ?]; last first.
    { cbn [app] in Heq1_t. injection Heq1_t as <- Hbad.
      apply (f_equal length) in Hbad.
      rewrite length_app length_cons /= in Hbad. lia. }
    cbn [app] in Heq1_t, Heq2_t.
    injection Heq1_t as <- ->.
    cbn [app] in Heq2_t.
    injection Heq2_t as <- Hefs.
    symmetry in Hefs. apply app_eq_nil in Hefs as [-> ->].
    (* Now [Hprim_step : prim_step e1 (compose_state tracer σ ts) κ e2 σ_compose' []] *)
    assert (Hsubstate : σ ⊆ compose_state tracer σ ts).
    { rewrite /compose_state. split; cbn.
      - apply map_union_subseteq_l.
      - set_solver. }
    edestruct (prim_step_subset e1 _ κ e2 σ_compose' [] σ
                 Hsubstate Hred Hprim_step)
      as (σ_ext & σ' & Hd1 & Hd2 & Heq_compose & Heq_compose' & Hprim_step').
    assert (Hcomp_disj : σ ## trace_to_state tracer ts).
    { rewrite /composable_state in Hcomp.
      split; cbn.
      - apply map_disjoint_dom. rewrite dom_trace_to_state. set_solver.
      - rewrite /trace_to_state /=. set_solver. }
    assert (σ_ext = trace_to_state tracer ts) as ->.
    { apply (state_union_cancel_l σ); [done|done|].
      rewrite -Heq_compose. reflexivity. }
    exists σ'. split_and!.
    - rewrite /composable_state.
      destruct Hd2 as [Hd2_h _]. cbn in Hd2_h.
      apply map_disjoint_dom in Hd2_h.
      rewrite dom_trace_to_state in Hd2_h. set_solver.
    - exact Heq_compose'.
    - exists κ.
      apply (step_atomic e1 σ e2 σ' [] [] []); [done|done|exact Hprim_step'].
  Qed.

  (** [nsteps] form of reverse simulation: takes adequacy at both σ
      (used for σ-side reducibility) and at [compose σ ts] (used for
      no-fork to bound the intermediate thread pool to length 1). *)
  Local Lemma erased_nsteps_compose_uncompose
        (tracer : loc) (n : nat) (e1 : expr) (σ : state)
        (ts : list (positive*trace))
        (e2 : expr) (σ_compose' : state) :
    composable_state tracer σ →
    adequate NotStuck e1 σ (λ _ _, True) →
    sequential e1 σ →
    adequate NotStuck e1 (compose_state tracer σ ts) (λ _ _, True) →
    sequential e1 (compose_state tracer σ ts) →
    relations.nsteps erased_step n
      ([e1], compose_state tracer σ ts) ([e2], σ_compose') →
    ∃ σ', composable_state tracer σ' ∧
      σ_compose' = compose_state tracer σ' ts ∧
      relations.nsteps erased_step n ([e1], σ) ([e2], σ').
  Proof.
    revert e1 σ e2 σ_compose'.
    induction n as [|n IH]; intros e1 σ e2 σ_compose'
                                   Hcomp Hadq_σ Hseq_σ Hadq_c Hseq_c Hns.
    - apply nsteps_O_eq_helper in Hns.
      pose proof (f_equal fst Hns) as Hcfg_t. cbn in Hcfg_t.
      pose proof (f_equal snd Hns) as Hcfg_s. cbn in Hcfg_s.
      clear Hns.
      injection Hcfg_t as <-.
      exists σ. split_and!; [done|by symmetry|apply nsteps_O].
    - inversion Hns. simplify_eq.
      rename select (cfg _) into ρmid.
      destruct ρmid as [t_mid σ_mid_compose].
      rename select (erased_step _ _) into Hstep.
      rename select (relations.nsteps erased_step _ _ _) into Hns_rest.
      assert (Ht_mid_len : length t_mid = 1).
      { eapply Hseq_c.
        eapply rtc_l; first exact Hstep. apply rtc_refl. }
      destruct t_mid as [|e_mid [|? ?]]; cbn in Ht_mid_len; try lia.
      assert (Hred_e1 : reducible e1 σ).
      { assert (Hin : e1 ∈ [e1]) by (apply elem_of_cons; by left).
        pose proof (adequate_not_stuck _ _ _ _ Hadq_σ [e1] σ e1
                     eq_refl (rtc_refl _ _) Hin)
          as [Hisval|Hr]; last exact Hr.
        exfalso.
        destruct Hstep as [κ Hstep].
        destruct Hstep as [eA σA eA' σA' efs t1V t2V Heq1 Heq2 Hprim_step].
        injection Heq1 as Heq1_t _.
        destruct t1V as [|? ?]; cbn [app] in Heq1_t.
        - injection Heq1_t as <- _.
          apply val_stuck in Hprim_step.
          destruct Hisval as [v Hv]. by rewrite Hv in Hprim_step.
        - injection Heq1_t as <- Hbad.
          apply (f_equal length) in Hbad.
          rewrite length_app length_cons /= in Hbad. lia. }
      pose proof Hstep as Hstep_compose.
      apply (erased_step_compose_uncompose _ _ _ _ _ _ Hcomp Hred_e1)
        in Hstep as (σ_mid & Hcomp_mid & Hcompose_eq & Hstep_σ).
      pose proof (adequate_erased_step _ _ _ _ _ _ _ Hstep_σ Hadq_σ)
        as Hadq_σ_mid.
      pose proof (sequential_erased_step _ _ _ _ Hstep_σ Hseq_σ)
        as Hseq_σ_mid.
      assert (Hadq_c_mid : adequate NotStuck e_mid
                            (compose_state tracer σ_mid ts)
                            (λ _ _, True)).
      { rewrite -Hcompose_eq.
        eapply adequate_erased_step; eassumption. }
      assert (Hseq_c_mid : sequential e_mid (compose_state tracer σ_mid ts)).
      { rewrite -Hcompose_eq.
        eapply sequential_erased_step; eassumption. }
      rewrite Hcompose_eq in Hns_rest.
      apply (IH e_mid σ_mid e2 σ_compose' Hcomp_mid
               Hadq_σ_mid Hseq_σ_mid Hadq_c_mid Hseq_c_mid)
        in Hns_rest as (σ' & Hcomp' & -> & Hns').
      exists σ'. split_and!; [done|done|].
      eapply nsteps_l; eassumption.
  Qed.

  (** [rtc] form of reverse simulation, derived from the [nsteps] version. *)
  Local Lemma erased_steps_compose_uncompose
        (tracer : loc) (e1 : expr) (σ : state)
        (ts : list (positive*trace))
        (e2 : expr) (σ_compose' : state) :
    composable_state tracer σ →
    adequate NotStuck e1 σ (λ _ _, True) →
    sequential e1 σ →
    adequate NotStuck e1 (compose_state tracer σ ts) (λ _ _, True) →
    sequential e1 (compose_state tracer σ ts) →
    rtc erased_step
      ([e1], compose_state tracer σ ts) ([e2], σ_compose') →
    ∃ σ', composable_state tracer σ' ∧
      σ_compose' = compose_state tracer σ' ts ∧
      rtc erased_step ([e1], σ) ([e2], σ').
  Proof.
    intros Hcomp Hadq_σ Hseq_σ Hadq_c Hseq_c Hsteps.
    apply rtc_nsteps_1 in Hsteps as [n Hns].
    apply (erased_nsteps_compose_uncompose tracer n) in Hns
      as (σ' & ? & ? & Hns'); [|done|done|done|done|done].
    exists σ'. split_and!; [done|done|].
    by eapply rtc_nsteps_2.
  Qed.

  Section inv.
    Context `{!heapGS Σ}.

    (** Adversarial invariant. The [own_state config'.(config_state)] is
        the "shadow run" tracker that evolves alongside the global Iris
        state via [own_state_update] each time the program takes a
        [prim_step], in lockstep with [config']'s [adv_step] transition.
        The rtc-fact carries the σ₀-relative run of [init]; this can be
        established because [Hadq_init] is universal in σ (in particular
        true for σ := σ₀), and [adequate_strengthen_reach] enriches
        the postcondition with the rtc-witness. *)
    Definition adv_inv_content (γ : gname) (obj : val) (tracer : loc) : iProp Σ :=
      ∃ (γ_pending γ_child : gname)
        (efs : list expr) (σ : state)
        (config' : configuration) (ts : list (positive*trace)),
        own γ (to_agree (γ_pending, γ_child)) ∗
        trace_is tracer ts ∗
        own_state config'.(config_state) ∗
        ⌜rtc erased_step ([init], σ₀) (Val obj :: efs, σ)⌝ ∗
        ⌜rtcL (adv_step ops obj valid_reqs) (Config [] [] σ) config' ts⌝ ∗
        ghost_map_auth γ_pending 1
          (list_to_map (pendingOp_active config'.(config_pendingOp)) : gmap positive expr) ∗
        ghost_map_auth γ_child 1
          (list_to_map (child_indexed config'.(config_childThread)) : gmap nat expr).

    Definition adv_inv (tracer : loc) (γ : gname) (obj : val) : iProp Σ :=
      inv advN (adv_inv_content γ obj tracer).
  End inv.

  Local Definition adv_repr : mgc_repr Σ := {|
    I_lang := I_adv;
    mgc_inv := @adv_inv;
  |}.

  (** Tag-set inclusion: any τ in [config_pendingOp]'s tag list is also
      in the trace's tag list. Proved by induction on [rtcL adv_step]. *)
  Local Lemma adv_step_pendingOp_tag_in_trace obj π efs σ π' efs' σ' ts :
    adv_step ops obj valid_reqs (Config π efs σ) (Config π' efs' σ') ts →
    list_to_set π'.*1 ⊆@{gset positive} list_to_set π.*1 ∪ list_to_set ts.*1.
  Proof.
    intros Hstep. inversion Hstep; subst; clear Hstep; cbn;
      rewrite ?fmap_app ?fmap_cons ?fmap_nil; cbn;
      rewrite ?list_to_set_app_L ?list_to_set_cons ?list_to_set_nil; set_solver.
  Qed.

  Local Lemma adv_steps_pendingOp_tag_in_trace
        obj (config0 config' : configuration) ts :
    rtcL (adv_step ops obj valid_reqs) config0 config' ts →
    list_to_set config'.(config_pendingOp).*1 ⊆@{gset positive}
      list_to_set config0.(config_pendingOp).*1 ∪ list_to_set ts.*1.
  Proof.
    intros Hsteps. induction Hsteps as [c|c0 c1 c2 ts1 ts2 Hstep _ IH].
    - cbn. set_solver.
    - destruct c0 as [π0 efs0 σ0], c1 as [π1 efs1 σ1]. cbn in *.
      apply adv_step_pendingOp_tag_in_trace in Hstep.
      rewrite fmap_app list_to_set_app_L. set_solver.
  Qed.

  Local Lemma pendingOp_active_subset_pi (π : list pendingOp) :
    list_to_set (pendingOp_active π).*1 ⊆@{gset positive} list_to_set π.*1.
  Proof.
    induction π as [|[τ [e|]] π IH]; first done.
    - rewrite pendingOp_active_cons_Some !fmap_cons !list_to_set_cons.
      set_solver.
    - rewrite pendingOp_active_cons_None !fmap_cons !list_to_set_cons.
      set_solver.
  Qed.

  (** NoDup of the tags in [pendingOp_active] follows from NoDup of all tags. *)
  Local Lemma pendingOp_active_nodup (π : list pendingOp) :
    NoDup π.*1 → NoDup (pendingOp_active π).*1.
  Proof.
    induction π as [|[τ [e|]] π IH]; intros Hnd; first done.
    - rewrite pendingOp_active_cons_Some !fmap_cons !NoDup_cons.
      rewrite fmap_cons NoDup_cons in Hnd. destruct Hnd as [Hτ Hnd].
      split.
      + intros Hin. apply Hτ.
        apply (elem_of_list_to_set (C := gset positive)).
        eapply elem_of_weaken; first by apply elem_of_list_to_set, Hin.
        apply pendingOp_active_subset_pi.
      + by apply IH.
    - rewrite pendingOp_active_cons_None.
      rewrite fmap_cons NoDup_cons in Hnd. destruct Hnd as [_ Hnd].
      by apply IH.
  Qed.

  (** [adv_step] preserves [NoDup] of pending-op tags. *)
  Local Lemma adv_step_nodup obj config0 config1 ts :
    adv_step ops obj valid_reqs config0 config1 ts →
    NoDup (config0.(config_pendingOp)).*1 →
    NoDup (config1.(config_pendingOp)).*1.
  Proof.
    intros Hstep Hnd. inversion Hstep; subst; cbn in *.
    - rewrite fmap_app fmap_cons fmap_nil /=.
      apply NoDup_app. split_and!; auto.
      + intros x Hx Hin. apply list_elem_of_singleton in Hin. subst x.
        rename select (_ ∉ _) into Hfresh. contradiction.
      + apply NoDup_singleton.
    - rewrite !fmap_app !fmap_cons /= in Hnd |- *. exact Hnd.
    - exact Hnd.
    - rewrite !fmap_app !fmap_cons /= in Hnd |- *. exact Hnd.
  Qed.

  Local Lemma adv_steps_nodup obj config0 config' ts :
    rtcL (adv_step ops obj valid_reqs) config0 config' ts →
    NoDup config0.(config_pendingOp).*1 →
    NoDup config'.(config_pendingOp).*1.
  Proof.
    induction 1 as [c|c0 c1 c2 ts1 ts2 Hstep _ IH]; intros Hnd; first done.
    apply IH. by eapply adv_step_nodup.
  Qed.

  Section spec_proof.
    Context `{!heapGS Σ}.
    Implicit Types (γ γ_pending γ_child : gname) (obj req : val) (tracer : loc).

    (** [init_spec_type] for [adv_repr], proved using [hoare_compleness_nofork]
        with [own_state ∅] (free via [own_state_empty]) and [Hadq_init] at σ := ∅.
        After [init] returns, we allocate the ghost names and the invariant. *)
    Local Lemma adv_init_spec :
      to_val init = None →
      (∀ σ, adequate NotStuck init σ (λ _ _, True)) →
      (∀ σ, sequential init σ) →
      init_spec_type_gen (own_state σ₀) adv_repr MaybeStuck init.
    Proof.
      iIntros (Hinit_nv Hadq_init Hseq_init Φ) "HS◯ HΦ".
      (* Allocate the ghost names up front, while the goal is still a
         WP (which supports fupd). *)
      iMod (ghost_map_alloc_empty (V:=expr) (K:=positive)) as (γ_pending) "Hp●".
      iMod (ghost_map_alloc_empty (V:=expr) (K:=nat)) as (γ_child) "Hc●".
      iMod (own_alloc (to_agree (γ_pending, γ_child))) as (γ) "#Hmeta"; first done.
      iApply (wp_stuck_mono NotStuck); first done.
      (* Strengthen [Hadq_init] at σ := σ₀ so its postcondition exposes
         the [rtc erased_step ([init], σ₀) ...] witness, then lift
         to a WP via [hoare_completeness_nofork]. *)
      pose (Q := λ (v : val) (σ_post : state),
        ∃ efs, rtc erased_step ([init], σ₀) (Val v :: efs, σ_post)).
      wp_apply (hoare_completeness_nofork init σ₀ Q with "[HS◯]").
      { done. }
      { eapply adequate_weaken;
            last apply (adequate_strengthen_reach _ _ _ _ (Hadq_init σ₀)).
          intros v σ_post [_ (efs & Hrtc)]. by exists efs. }
      { apply (Hseq_init σ₀). }
      { by iDestruct "HS◯" as "$". }
      iIntros (obj σ_post) "[Hown_state %Hrtc_existsσ]".
      iApply ("HΦ" $! γ obj).
      iIntros (l) "Hti".
      destruct Hrtc_existsσ as (efs & Hrtc_σ_init).
      iApply (inv_alloc advN _ (adv_inv_content γ obj l) with "[-]").
      iNext.
      iExists γ_pending, γ_child, efs, σ_post, (Config [] [] σ_post), [].
      cbn [config_state config_pendingOp config_childThread
           pendingOp_active child_indexed list_to_map fmap].
      iFrame "Hmeta Hti Hown_state".
      iSplit; first done.
      iSplit; first by iPureIntro; apply rtcL_refl.
      iFrame "Hp● Hc●".
    Qed.

    (** Convert a [big_sepM] over an indexed list back to a [big_sepL] over
        the original list. *)
    Local Lemma big_sepM_imap_to_sepL_offset
        `{!ghost_mapG Σ nat expr}
        (γ : gname) (start : nat) (l : list expr) :
      ([∗ map] k ↦ v ∈
          (list_to_map (imap (λ j ef, ((start + j)%nat : nat, ef)) l)
            : gmap nat expr),
        k ↪[γ] v) ⊢
      [∗ list] j ↦ ef ∈ l, (start + j)%nat ↪[γ] ef.
    Proof.
      revert start.
      induction l as [|ef rest IH]; intros start.
      - simpl. rewrite big_sepM_empty //.
      - cbn [imap].
        rewrite list_to_map_cons.
        rewrite Nat.add_0_r.
        rewrite big_sepM_insert; last first.
        { apply not_elem_of_list_to_map_1.
          rewrite fmap_imap.
          rewrite list_elem_of_lookup.
          intros (k & Hk). rewrite list_lookup_imap in Hk.
          destruct (rest !! k); cbn in Hk; last done.
          injection Hk as Hk_eq. lia. }
        cbn [big_opL].
        iIntros "[Hef Hrest]".
        rewrite Nat.add_0_r. iFrame "Hef".
        assert (Heq : imap ((λ j ef, ((start + j)%nat : nat, ef)) ∘ Datatypes.S) rest
                   = imap (λ j ef, ((Datatypes.S start + j)%nat : nat, ef)) rest).
        { apply imap_ext. intros k v _.
          cbn. apply pair_equal_spec. split; [lia|done]. }
        rewrite Heq. clear Heq.
        iDestruct (IH (Datatypes.S start) with "Hrest") as "Hrest".
        iApply (big_sepL_impl with "Hrest").
        iIntros "!>" (k v _) "H".
        replace (start + Datatypes.S k)%nat with (Datatypes.S start + k)%nat by lia.
        done.
    Qed.

    (** Disjoint-domain fact: the [γ_child] auth before allocating fresh
        entries (keyed [0..length child_old-1]) is disjoint from the new
        entries (keyed [length child_old..]). *)
    Local Lemma child_indexed_disjoint_new (child_old efs' : list expr) :
      (list_to_map (imap (λ i e0, ((length child_old + i)%nat : nat, e0)) efs')
        : gmap nat expr)
      ##ₘ
      list_to_map (child_indexed child_old).
    Proof.
      apply map_disjoint_dom.
      intros k Hk_new Hk_old.
      apply elem_of_dom in Hk_new as [e_new Hk_new].
      apply elem_of_dom in Hk_old as [e_old Hk_old].
      apply elem_of_list_to_map_2, list_elem_of_lookup in Hk_new
        as (j & Hj). rewrite list_lookup_imap in Hj.
      destruct (efs' !! j) eqn:Hj'; cbn in Hj; last done.
      injection Hj as Heq _.
      apply elem_of_list_to_map_2, child_indexed_lookup_iff in Hk_old.
      apply lookup_lt_Some in Hk_old. lia.
    Qed.

    (** Forked-thread WP: a child thread tracked by the invariant satisfies
        [WP e @ MaybeStuck; ⊤ {{ _, True }}]. Proved by Löb induction on [e]:
        at each non-value step, open the invariant, advance one [prim_step]
        of [e], replay it as [adv_step_child], update [γ_child], and
        allocate fresh [γ_child] receipts for forked threads via
        [ghost_map_insert_big]. *)
    Local Lemma wp_adv_child :
      (∀ σ, adequate NotStuck init σ (λ _ _, True)) →
      (∀ σ, sequential init σ) →
      (∀ obj' σ_init σ config' ts,
        rtc erased_step ([init], σ_init) ([Val obj'], σ) →
        rtcL (adv_step ops obj' valid_reqs) (Config [] [] σ) config' ts →
        config_not_stuck config') →
      ∀ γ γ_pending γ_child obj l (i : nat) e,
        adv_inv l γ obj -∗
        own γ (to_agree (γ_pending, γ_child)) -∗
        i ↪[γ_child] e -∗
        WP e @ NotStuck; ⊤ {{ _, True }}.
    Proof.
      iIntros (Hadq_init Hseq_init Hadq_op γ γ_pending γ_child obj l i e)
        "#Hinv #Hmeta Hi_child".
      iLöb as "IH" forall (i e).
      destruct (to_val e) as [v|] eqn:Hv.
      { rewrite -(of_to_val e v) //. iApply wp_value. done. }
      iApply wp_inv_open_maybe.
      iInv "Hinv" as ">Hadv" "Hclose".
      iDestruct "Hadv" as (γ_pending' γ_child' efs σ config' ts)
        "(#Hmeta' & Htrace & Hown_state & %Hrtc & %Hadv_steps & Hp● & Hc●)".
      iCombine "Hmeta Hmeta'" gives %Hagree%to_agree_op_inv_L.
      injection Hagree as <- <-. iClear "Hmeta'".
      destruct config' as [π_now child_old σ_now].
      cbn [config_state config_pendingOp config_childThread] in *.
      iDestruct (ghost_map_lookup with "Hc● Hi_child") as %Hi_lookup.
      apply elem_of_list_to_map_2, child_indexed_lookup_iff in Hi_lookup.
      pose proof Hi_lookup as Hi_lookup'.
      apply child_indexed_split in Hi_lookup' as (efs1 & efs2 & Heq_child & Hlen_efs1).
      assert (Hefs_nil : efs = []).
      { opose proof (Hseq_init σ₀ _ _ Hrtc) as Hlen.
        cbn in Hlen. destruct efs; first done. cbn in Hlen. lia. }
      subst efs. subst child_old.
      pose proof (Hadq_op obj σ₀ σ
                    (Config π_now (efs1 ++ e :: efs2) σ_now) ts Hrtc Hadv_steps)
        as [_ Hns_children].
      cbn in Hns_children.
      rewrite Forall_app Forall_cons in Hns_children.
      destruct Hns_children as (_ & Hns_e & _).
      assert (He_red : reducible e σ_now).
      { destruct Hns_e as [Hisval|Hr]; last exact Hr.
        exfalso. destruct Hisval as [w Hw']. by rewrite Hw' in Hv. }
      iMod (lang_completeness with "[Hown_state]") as "H".
      { exact He_red. } { iFrame "Hown_state". }
      iModIntro. iDestruct "H" as "[H | H]".
      - (* first redex is atomic *)
        iLeft. iDestruct "H" as (K e1 ? Heq Hnotval Hatomic) "H". subst e.
        iExists K, e1. do 3 (iSplit; first done). iApply "H".
        iNext. iIntros "_" (κ v2 σ2 efs' Hbase).
        eapply fill_step in Hbase as Hprim_step.
        iMod (ghost_map_update (K (Val v2)) with "Hc● Hi_child") as "[Hc● Hi_child]".
        rewrite -Hlen_efs1.
        rewrite child_indexed_replace_step.
        pose (new_map :=
          (list_to_map
            (imap (λ j ef, ((length (efs1 ++ K (Val v2) :: efs2) + j)%nat : nat, ef)) efs')
           : gmap nat expr)).
        iMod (ghost_map_insert_big new_map with "Hc●") as "[Hc● Hnew]".
        { rewrite /new_map. apply child_indexed_disjoint_new. }
        iModIntro. iSplitR "Hnew"; last first.
        { rewrite /new_map.
          iDestruct (big_sepM_imap_to_sepL_offset _ _ _ with "Hnew") as "Hnew".
          iApply (big_sepL_impl with "Hnew").
          iIntros "!>" (k v _) "H". iApply ("IH" with "H"). }
        iIntros "Hown_state".
        iMod ("Hclose" with "[Htrace Hown_state Hp● Hc●]") as "_".
        { iNext. iExists γ_pending, γ_child, [], σ,
                         (Config π_now (efs1 ++ K (Val v2) :: efs2 ++ efs') σ2),
                         ts.
          cbn [config_state config_pendingOp config_childThread].
          iFrame "Hmeta Htrace Hown_state Hp●".
          iSplit; first done.
          iSplit.
          { iPureIntro. rewrite -(right_id_L [] (++) ts).
            eapply rtcL_r; first exact Hadv_steps.
            by eapply adv_step_child. }
          replace (efs1 ++ K (Val v2) :: efs2 ++ efs')
            with ((efs1 ++ K (Val v2) :: efs2) ++ efs')
            by (rewrite -app_assoc //).
          rewrite child_indexed_extend_step.
          rewrite map_union_comm; first iFrame.
          rewrite /new_map. apply child_indexed_disjoint_new. }
        iModIntro.
        iApply ("IH" $! (length efs1) (K (Val v2)) with "Hi_child").
      - (* first redex is not atomic *)
        iRight. iDestruct "H" as "[Hown_state H]".
        iMod ("Hclose" with "[Htrace Hown_state Hp● Hc●]") as "_".
        { iNext. iExists γ_pending, γ_child, [], σ,
                         (Config π_now (efs1 ++ e :: efs2) σ_now), ts.
          cbn [config_state config_pendingOp config_childThread].
          iFrame "Hmeta Htrace Hown_state Hp● Hc●".
          iSplit; first done. iPureIntro. exact Hadv_steps. }
        iModIntro. iApply "H".
        iNext. iIntros "_" (e2 efs_new) "Hstep".
        iInv "Hinv" as ">Hadv" "Hclose".
        iDestruct "Hadv" as (γ_pending'' γ_child'' efs'' σ2i config'' ts2)
          "(#Hmeta'' & Htrace & Hown_state & %Hrtc2 & %Hadv_steps2 & Hp● & Hc●)".
        iCombine "Hmeta Hmeta''" gives %Hagree2%to_agree_op_inv_L.
        injection Hagree2 as <- <-. iClear "Hmeta''".
        destruct config'' as [π_now2 child_old2 σ_now2].
        cbn [config_state config_pendingOp config_childThread] in *.
        iDestruct (ghost_map_lookup with "Hc● Hi_child") as %Hi_lookup2.
        apply elem_of_list_to_map_2, child_indexed_lookup_iff in Hi_lookup2.
        pose proof Hi_lookup2 as Hi_lookup2'.
        apply child_indexed_split in Hi_lookup2'
          as (efs1b & efs2b & Heq_child2 & Hlen_efs1b).
        assert (Hefs_nil2 : efs'' = []).
        { opose proof (Hseq_init σ₀ _ _ Hrtc2) as Hlen.
          cbn in Hlen. destruct efs''; first done. cbn in Hlen. lia. }
        subst efs''. subst child_old2.
        iMod ("Hstep" with "Hown_state") as (κ2 σ_new) "[%Hprim_step Hown_state]".
        iMod (ghost_map_update e2 with "Hc● Hi_child") as "[Hc● Hi_child]".
        rewrite -Hlen_efs1b.
        rewrite child_indexed_replace_step.
        pose (new_map :=
          (list_to_map
            (imap (λ j ef, ((length (efs1b ++ e2 :: efs2b) + j)%nat : nat, ef)) efs_new)
           : gmap nat expr)).
        iMod (ghost_map_insert_big new_map with "Hc●") as "[Hc● Hnew]".
        { rewrite /new_map. apply child_indexed_disjoint_new. }
        iMod ("Hclose" with "[Htrace Hown_state Hp● Hc●]") as "_".
        { iNext. iExists γ_pending, γ_child, [], σ2i,
                         (Config π_now2 (efs1b ++ e2 :: efs2b ++ efs_new) σ_new),
                         ts2.
          cbn [config_state config_pendingOp config_childThread].
          iFrame "Hmeta Htrace Hown_state Hp●".
          iSplit; first done.
          iSplit.
          { iPureIntro. rewrite -(right_id_L [] (++) ts2).
            eapply rtcL_r; first exact Hadv_steps2.
            by eapply adv_step_child. }
          replace (efs1b ++ e2 :: efs2b ++ efs_new)
            with ((efs1b ++ e2 :: efs2b) ++ efs_new)
            by (rewrite -app_assoc //).
          rewrite child_indexed_extend_step.
          rewrite map_union_comm; first iFrame.
          rewrite /new_map. apply child_indexed_disjoint_new. }
        iModIntro. iSplitL "Hi_child".
        { iApply ("IH" $! (length efs1b) e2 with "Hi_child"). }
        rewrite /new_map.
        iDestruct (big_sepM_imap_to_sepL_offset _ _ _ with "Hnew") as "Hnew".
        iApply (big_sepL_impl with "Hnew").
        iIntros "!>" (k v _) "H". iApply ("IH" with "H").
    Qed.

    (** [call_ret_wrapper_spec_type] for [adv_repr].

        Phase 1 — [trace_fresh #l (InjL (#n, req))]: at the linearization point,
        open [adv_inv γ obj l] to access [trace_is l ts] and the abstract
        [config']. Pick a fresh [τ ∉ ts.*1] and use [adv_step_call] (with
        [Hvalid_req req]) to extend [rtcL adv_step] to [ts ++ [(τ, Call n req)]],
        producing the new pending op [(τ, Some (ops!!!n obj req))].
        Allocate [τ ↪[γ_pending] (ops!!!n obj req)] and re-close.

        Phase 2 — [ops!!!n obj req]: a Löb induction (in [wp_phase2]) over the
        expression. At each WP prim-step, open [adv_inv], derive
        reducibility from [Hadq_op]+[config_not_stuck], take the step via
        [prim_step_subset]+[prim_step_state_update], replay as
        [adv_step_intermediate], update [γ_pending]'s entry from
        [(τ, Some e)] to [(τ, Some e')], and allocate fresh [γ_child]
        receipts for forked threads via [ghost_map_insert_big]. Forked
        threads are discharged with [wp_adv_child] using the new receipts.

        Phase 3 — [trace_emit #l #τ (InjR v)]: invokes [trace_emit_spec],
        whose linearization point opens [adv_inv]; replay [adv_step_return]
        to update the trace and turn the pending entry into [None]; delete
        the [γ_pending] receipt; re-close. *)
    Local Lemma adv_call_ret_wrapper_spec :
      (∀ σ, adequate NotStuck init σ (λ _ _, True)) →
      (∀ σ, sequential init σ) →
      (∀ obj' σ_init σ config' ts,
        rtc erased_step ([init], σ_init) ([Val obj'], σ) →
        rtcL (adv_step ops obj' valid_reqs) (Config [] [] σ) config' ts →
        config_not_stuck config') →
      call_ret_wrapper_spec_type adv_repr MaybeStuck valid_reqs ops.
    Proof.
      iIntros (Hadq_init Hseq_init Hadq_op n γ l obj req Hvalid_req Φ).
      iIntros "[#Hti #Hinv] HΦ".
      iApply (wp_stuck_mono NotStuck MaybeStuck); first done.
      rewrite /call_ret_wrapper. wp_pures.
      wp_bind (trace_fresh _ _).
      awp_apply (trace_fresh_spec _ (Call n req) (InjLV (#n,req)) I_adv with "Hti").
      { exact (decode_encode_val (Call n req)). }
      rewrite /atomic_acc /=.
      iInv "Hinv" as ">Hadv" "Hclose".
      iDestruct "Hadv" as (γ_pending γ_child efs σ config' ts)
        "(#Hmeta_in & Htrace & Hown_state & %Hrtc & %Hadv_steps & Hp● & Hc●)".
      destruct config' as [π_old child_old σ_old].
      cbn [config_state config_pendingOp config_childThread] in *.
      rewrite /atomic_acc /=.
      iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose_mask".
      (* Helper: any fresh tag from the trace is also fresh from [π_old].
         Used in both the AU's pure obligation and the commit branch. *)
      assert (Htag_in_ts : ∀ τ, τ ∈ π_old.*1 → τ ∈ ts.*1).
      { intros τ' Hin_π.
        opose proof (adv_steps_pendingOp_tag_in_trace _ _ _ _ Hadv_steps) as Hsub.
        cbn in Hsub.
        apply (elem_of_list_to_set (C := gset positive)).
        apply (elem_of_list_to_set (C := gset positive)) in Hin_π.
        clear -Hsub Hin_π. set_solver. }
      iFrame "Htrace". iSplit.
      { (* Verify [I_adv (ts ++ [(τ, Call n req)])] for any fresh τ. *)
        iPureIntro. intros τ Hfresh.
        rewrite /I_adv.
        exists obj, efs, σ,
          (Config (π_old ++ [(τ, Some ((ops!!!n: val) obj req))]) child_old σ_old).
        split; first exact Hrtc.
        eapply rtcL_r; first exact Hadv_steps.
        apply adv_step_call; last exact Hvalid_req.
        intros Hin_π. by apply Hfresh, Htag_in_ts. }
      iSplit.
      { (* Abort branch *)
        iIntros "[Htrace _]". iMod "Hclose_mask" as "_".
        iMod ("Hclose" with "[-HΦ]") as "_"; last done.
        iNext. iExists γ_pending, γ_child, efs, σ, (Config π_old child_old σ_old),
                ts.
        iFrame "Hmeta_in Htrace Hown_state Hp● Hc●". by iSplit. }
      (* Commit branch *)
      iIntros (τ) "[Htrace_new %Hfresh]". iMod "Hclose_mask" as "_".
      assert (Hτ_notin_πold : τ ∉ π_old.*1).
      { intros Hin. by apply Hfresh, Htag_in_ts. }
      (* Allocate the pending-op ghost map fragment for the new τ. *)
      iMod (ghost_map_insert τ ((ops!!!n: val) obj req) with "Hp●") as "[Hp● Hτ_pending]".
      { by apply not_elem_of_list_to_map_1, not_elem_of_pendingOp_active_fmap. }
      iMod ("Hclose" with "[Htrace_new Hown_state Hp● Hc●]") as "_".
      { iNext.
        iExists γ_pending, γ_child, efs, σ,
                (Config (π_old ++ [(τ, Some ((ops!!!n: val) obj req))]) child_old σ_old),
                (ts ++ [(τ, Call n req)]).
        cbn [config_state config_pendingOp config_childThread].
        iFrame "Hmeta_in Htrace_new Hown_state".
        iSplit; first done.
        iSplit.
        { iPureIntro. eapply rtcL_r; first exact Hadv_steps.
          apply adv_step_call; last exact Hvalid_req. exact Hτ_notin_πold. }
        rewrite pendingOp_active_snoc_Some list_to_map_snoc;
          last by apply not_elem_of_pendingOp_active_fmap.
        iFrame. }
      iModIntro.
      wp_pures.
      (* Phase 2 — [op obj req]: Löb-induct over [e]. At each non-value step,
         open the invariant, advance one [prim_step], replay as
         [adv_step_intermediate], update [γ_pending]'s entry from
         [(τ, Some e)] to [(τ, Some e')], allocate fresh [γ_child] receipts
         for forked threads, and continue. *)
      wp_bind ((ops!!!n: val) _ _).
      remember ((ops!!!n: val) obj req) as e0 eqn:He0.
      clear He0.
      iAssert (∀ e, τ ↪[γ_pending] e -∗
                WP e @ NotStuck; ⊤ {{ v, τ ↪[γ_pending] (Val v) }})%I as "wp_phase2".
      { iIntros (e). iIntros "Hτ_pending".
        iLöb as "IH" forall (e).
        destruct (to_val e) as [v|] eqn:Hv.
        { rewrite -(of_to_val e v) //. iApply wp_value. iFrame. }
        iApply wp_inv_open_maybe.
        iInv "Hinv" as ">Hadv" "Hclose".
        iDestruct "Hadv" as
          (γ_pending' γ_child' efs' σ' config' ts')
          "(#Hmeta_in' & Htrace & Hown_state & %Hrtc' & %Hadv_steps' & Hp● & Hc●)".
        iCombine "Hmeta_in Hmeta_in'" gives %Hagree%to_agree_op_inv_L.
        injection Hagree as <- <-. iClear "Hmeta_in'".
        destruct config' as [π_now child_now σ_now].
        cbn [config_state config_pendingOp config_childThread] in *.
        iCombine "Hp● Hτ_pending" gives %Hτ_lookup.
        apply elem_of_list_to_map_2, elem_of_pendingOp_active_split in Hτ_lookup
          as (π1 & π2 & ->).
        assert (Hefs_nil : efs' = []).
        { opose proof (Hseq_init σ₀ _ _ Hrtc')
            as Hlen. cbn in Hlen.
          destruct efs'; first done. cbn in Hlen. lia. }
        subst efs'.
        pose proof (Hadq_op obj σ₀ σ'
                      (Config (π1 ++ (τ, Some e) :: π2) child_now σ_now) ts'
                      Hrtc' Hadv_steps') as [Hns_pending _].
        cbn in Hns_pending.
        rewrite Forall_app Forall_cons in Hns_pending.
        destruct Hns_pending as (_ & Hns_e & _). cbn in Hns_e.
        assert (He_red : reducible e σ_now).
        { destruct Hns_e as [Hisval|Hr]; last exact Hr.
          exfalso. destruct Hisval as [w Hw']. by rewrite Hw' in Hv. }
        iMod (lang_completeness with "[Hown_state]") as "H".
        { exact He_red. } { iFrame "Hown_state". }
        iModIntro. iDestruct "H" as "[H | H]".
        + (* first redex is atomic *)
          iLeft. iDestruct "H" as (K e1 ? Heq Hnotval Hatomic) "H". subst e.
          iExists K, e1. do 3 (iSplit; first done). iApply "H".
          iNext. iIntros "_" (κ v2 σ2 efs_new Hbase).
          eapply fill_step in Hbase as Hprim_step.
          iMod (ghost_map_update (K (Val v2)) with "Hp● Hτ_pending")
            as "[Hp● Hτ_pending]".
          (* Derive NoDup of pendingOp tags via adv_steps_nodup. *)
          assert (Hnd_now : NoDup (π1 ++ (τ, Some (K e1)) :: π2).*1).
          { eapply (adv_steps_nodup obj _ (Config _ _ _)); first exact Hadv_steps'.
            cbn. apply NoDup_nil_2. }
          assert (Hτ_notin_π1 : τ ∉ (pendingOp_active π1).*1).
          { intros Hin.
            rewrite fmap_app fmap_cons NoDup_app in Hnd_now.
            destruct Hnd_now as (_ & Hdisj & _).
            eapply (Hdisj τ); last by left.
            apply (elem_of_list_to_set (C := gset positive)) in Hin.
            rewrite -(elem_of_list_to_set (C := gset positive)).
            eapply elem_of_weaken; first exact Hin.
            apply pendingOp_active_subset_pi. }
          assert (Hτ_notin_π2 : τ ∉ (pendingOp_active π2).*1).
          { rewrite fmap_app fmap_cons NoDup_app in Hnd_now.
            destruct Hnd_now as (_ & _ & Hnd_τπ2).
            rewrite NoDup_cons in Hnd_τπ2. destruct Hnd_τπ2 as [Hτπ2 _].
            intros Hin. apply Hτπ2.
            apply (elem_of_list_to_set (C := gset positive)) in Hin.
            apply (elem_of_list_to_set (C := gset positive)).
            eapply elem_of_weaken; first exact Hin.
            apply pendingOp_active_subset_pi. }
          replace (<[τ:=K (Val v2)]>
                    (list_to_map (pendingOp_active (π1 ++ (τ, Some (K e1)) :: π2))
                      : gmap positive expr))
            with (list_to_map (pendingOp_active (π1 ++ (τ, Some (K (Val v2))) :: π2))
                    : gmap positive expr); last first.
          { rewrite !pendingOp_active_app !pendingOp_active_cons_Some
                    !list_to_map_app !list_to_map_cons.
            rewrite insert_union_r;
              last by apply not_elem_of_list_to_map_1.
            rewrite insert_insert_eq //. }
          (* Allocate fresh γ_child for new forks *)
          pose (new_map := (list_to_map
            (imap (λ j ef, ((length child_now + j)%nat : nat, ef)) efs_new)
              : gmap nat expr)).
          iMod (ghost_map_insert_big new_map with "Hc●") as "[Hc● Hnew]".
          { rewrite /new_map. apply child_indexed_disjoint_new. }
          iModIntro. iSplitR "Hnew"; last first.
          { rewrite /new_map.
            iDestruct (big_sepM_imap_to_sepL_offset _ _ _ with "Hnew") as "Hnew".
            iApply (big_sepL_impl with "Hnew").
            iIntros "!>" (k v _) "H".
            iApply (wp_adv_child Hadq_init Hseq_init Hadq_op with "Hinv Hmeta_in H"). }
          iIntros "Hown_state".
          iMod ("Hclose" with "[Htrace Hown_state Hp● Hc●]") as "_".
          { iNext. iExists γ_pending, γ_child, [], σ',
                           (Config (π1 ++ (τ, Some (K (Val v2))) :: π2)
                                   (child_now ++ efs_new) σ2),
                           ts'.
            cbn [config_state config_pendingOp config_childThread].
            iFrame "Hmeta_in Htrace Hown_state Hp●".
            iSplit; first done.
            iSplit.
            { iPureIntro. rewrite -(right_id_L [] (++) ts').
              eapply rtcL_r; first exact Hadv_steps'.
              by eapply adv_step_intermediate. }
            rewrite child_indexed_app_imap.
            rewrite list_to_map_app.
            rewrite map_union_comm; first iFrame.
            rewrite /new_map. apply child_indexed_disjoint_new. }
          iModIntro.
          iApply ("IH" with "Hτ_pending").
        + (* first redex is not atomic *)
          iRight. iDestruct "H" as "[Hown_state H]".
          iMod ("Hclose" with "[Htrace Hown_state Hp● Hc●]") as "_".
          { iNext. iExists γ_pending, γ_child, [], σ',
                           (Config (π1 ++ (τ, Some e) :: π2) child_now σ_now), ts'.
            cbn [config_state config_pendingOp config_childThread].
            iFrame "Hmeta_in Htrace Hown_state Hp● Hc●".
            iSplit; first done. iPureIntro. exact Hadv_steps'. }
          iModIntro. iApply "H".
          iNext. iIntros "_" (e2 efs_new) "Hstep".
          iInv "Hinv" as ">Hadv" "Hclose".
          iDestruct "Hadv" as
            (γ_pending'' γ_child'' efs'' σ2i config'' ts2)
            "(#Hmeta_in'' & Htrace & Hown_state & %Hrtc2 & %Hadv_steps2 & Hp● & Hc●)".
          iCombine "Hmeta_in Hmeta_in''" gives %Hagree2%to_agree_op_inv_L.
          injection Hagree2 as <- <-. iClear "Hmeta_in''".
          destruct config'' as [π_now2 child_now2 σ_now2].
          cbn [config_state config_pendingOp config_childThread] in *.
          iCombine "Hp● Hτ_pending" gives %Hτ_lookup2.
          apply elem_of_list_to_map_2, elem_of_pendingOp_active_split in Hτ_lookup2
            as (π1b & π2b & ->).
          assert (Hefs_nil2 : efs'' = []).
          { opose proof (Hseq_init σ₀ _ _ Hrtc2) as Hlen. cbn in Hlen.
            destruct efs''; first done. cbn in Hlen. lia. }
          subst efs''.
          iMod ("Hstep" with "Hown_state") as (κ2 σ_new) "[%Hprim_step Hown_state]".
          iMod (ghost_map_update e2 with "Hp● Hτ_pending")
            as "[Hp● Hτ_pending]".
          (* Derive NoDup of pendingOp tags via adv_steps_nodup. *)
          assert (Hnd_now : NoDup (π1b ++ (τ, Some e) :: π2b).*1).
          { eapply (adv_steps_nodup obj _ (Config _ _ _)); first exact Hadv_steps2.
            cbn. apply NoDup_nil_2. }
          assert (Hτ_notin_π1 : τ ∉ (pendingOp_active π1b).*1).
          { intros Hin.
            rewrite fmap_app fmap_cons NoDup_app in Hnd_now.
            destruct Hnd_now as (_ & Hdisj & _).
            eapply (Hdisj τ); last by left.
            apply (elem_of_list_to_set (C := gset positive)) in Hin.
            rewrite -(elem_of_list_to_set (C := gset positive)).
            eapply elem_of_weaken; first exact Hin.
            apply pendingOp_active_subset_pi. }
          assert (Hτ_notin_π2 : τ ∉ (pendingOp_active π2b).*1).
          { rewrite fmap_app fmap_cons NoDup_app in Hnd_now.
            destruct Hnd_now as (_ & _ & Hnd_τπ2).
            rewrite NoDup_cons in Hnd_τπ2. destruct Hnd_τπ2 as [Hτπ2 _].
            intros Hin. apply Hτπ2.
            apply (elem_of_list_to_set (C := gset positive)) in Hin.
            apply (elem_of_list_to_set (C := gset positive)).
            eapply elem_of_weaken; first exact Hin.
            apply pendingOp_active_subset_pi. }
          replace (<[τ:=e2]>
                    (list_to_map (pendingOp_active (π1b ++ (τ, Some e) :: π2b))
                      : gmap positive expr))
            with (list_to_map (pendingOp_active (π1b ++ (τ, Some e2) :: π2b))
                    : gmap positive expr); last first.
          { rewrite !pendingOp_active_app !pendingOp_active_cons_Some
                    !list_to_map_app !list_to_map_cons.
            rewrite insert_union_r;
              last by apply not_elem_of_list_to_map_1.
            rewrite insert_insert_eq //. }
          (* Allocate fresh γ_child for new forks *)
          pose (new_map := (list_to_map
            (imap (λ j ef, ((length child_now2 + j)%nat : nat, ef)) efs_new)
              : gmap nat expr)).
          iMod (ghost_map_insert_big new_map with "Hc●") as "[Hc● Hnew]".
          { rewrite /new_map. apply child_indexed_disjoint_new. }
          iMod ("Hclose" with "[Htrace Hown_state Hp● Hc●]") as "_".
          { iNext. iExists γ_pending, γ_child, [], σ2i,
                           (Config (π1b ++ (τ, Some e2) :: π2b)
                                   (child_now2 ++ efs_new) σ_new),
                           ts2.
            cbn [config_state config_pendingOp config_childThread].
            iFrame "Hmeta_in Htrace Hown_state Hp●".
            iSplit; first done.
            iSplit.
            { iPureIntro. rewrite -(right_id_L [] (++) ts2).
              eapply rtcL_r; first exact Hadv_steps2.
              by eapply adv_step_intermediate. }
            rewrite child_indexed_app_imap.
            rewrite list_to_map_app.
            rewrite map_union_comm; first iFrame.
            rewrite /new_map. apply child_indexed_disjoint_new. }
          iModIntro. iSplitL "Hτ_pending".
          { iApply ("IH" with "Hτ_pending"). }
          rewrite /new_map.
          iDestruct (big_sepM_imap_to_sepL_offset _ _ _ with "Hnew") as "Hnew".
          iApply (big_sepL_impl with "Hnew").
          iIntros "!>" (k v _) "H".
          iApply (wp_adv_child Hadq_init Hseq_init Hadq_op with "Hinv Hmeta_in H"). }
      iSpecialize ("wp_phase2" $! e0 with "Hτ_pending").
      iApply (wp_wand with "wp_phase2"). iIntros (v) "Hτ_pending".
      wp_pures.
      (* Phase 3 — [trace_emit]: at the linearization point, open the invariant,
         replay as [adv_step_return], delete [τ ↪[γ_pending] (Val v)]. *)
      wp_bind (trace_emit _ _ _).
      awp_apply (trace_emit_spec _ τ (Ret v) (InjRV v) I_adv with "Hti").
      { reflexivity. }
      rewrite /atomic_acc /=.
      iInv "Hinv" as ">Hadv" "Hclose".
      iDestruct "Hadv" as
        (γ_pending' γ_child' efs' σ' config' ts')
        "(#Hmeta_in' & Htrace & Hown_state & %Hrtc' & %Hadv_steps' & Hp● & Hc●)".
      iCombine "Hmeta_in Hmeta_in'" gives %Hagree%to_agree_op_inv_L.
      injection Hagree as <- <-. iClear "Hmeta_in'".
      destruct config' as [π_now child_now σ_now].
      cbn [config_state config_pendingOp config_childThread] in *.
      iCombine "Hp● Hτ_pending" gives %Hτ_lookup.
      apply elem_of_list_to_map_2, elem_of_pendingOp_active_split in Hτ_lookup
        as (π1 & π2 & ->).
      iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose_mask".
      iFrame "Htrace". iSplit.
      { iPureIntro.
        red. exists obj, efs', σ',
          (Config (π1 ++ (τ, None) :: π2) child_now σ_now).
        split; first exact Hrtc'.
        eapply rtcL_r; first exact Hadv_steps'.
        apply adv_step_return. }
      iSplit.
      { (* Abort branch — for [trace_emit_spec] this never fires (it's
           a non-AU; only the "commit" branch matters). But the
           [atomic_acc] shape still requires us to provide it. *)
        iIntros "[Htrace _]". iMod "Hclose_mask" as "_".
        iMod ("Hclose" with "[-HΦ Hτ_pending]") as "_"; last by iFrame.
        iNext. iExists γ_pending, γ_child, efs', σ',
          (Config (π1 ++ (τ, Some (Val v)) :: π2) child_now σ_now),
          ts'.
        iFrame "Hmeta_in Htrace Hown_state Hp● Hc●". by iSplit. }
      (* Commit branch *)
      iIntros "Htrace_new". iMod "Hclose_mask" as "_".
      iMod (ghost_map_delete with "Hp● Hτ_pending") as "Hp●".
      (* Derive NoDup of pendingOp tags via adv_steps_nodup. *)
      assert (Hnd_now : NoDup (π1 ++ (τ, Some (Val v)) :: π2).*1).
      { eapply (adv_steps_nodup obj _ (Config _ _ _)); first exact Hadv_steps'.
        cbn. apply NoDup_nil_2. }
      assert (Hτ_notin_π1 : τ ∉ (pendingOp_active π1).*1).
      { intros Hin.
        rewrite fmap_app fmap_cons NoDup_app in Hnd_now.
        destruct Hnd_now as (_ & Hdisj & _).
        eapply (Hdisj τ); last by left.
        apply (elem_of_list_to_set (C := gset positive)) in Hin.
        rewrite -(elem_of_list_to_set (C := gset positive)).
        eapply elem_of_weaken; first exact Hin.
        apply pendingOp_active_subset_pi. }
      assert (Hτ_notin_π2 : τ ∉ (pendingOp_active π2).*1).
      { rewrite fmap_app fmap_cons NoDup_app in Hnd_now.
        destruct Hnd_now as (_ & _ & Hnd_τπ2).
        rewrite NoDup_cons in Hnd_τπ2. destruct Hnd_τπ2 as [Hτπ2 _].
        intros Hin. apply Hτπ2.
        apply (elem_of_list_to_set (C := gset positive)) in Hin.
        apply (elem_of_list_to_set (C := gset positive)).
        eapply elem_of_weaken; first exact Hin.
        apply pendingOp_active_subset_pi. }
      iMod ("Hclose" with "[Htrace_new Hown_state Hp● Hc●]") as "_".
      { iNext. iExists γ_pending, γ_child, efs', σ',
          (Config (π1 ++ (τ, None) :: π2) child_now σ_now),
          (ts' ++ [(τ, Ret v)]).
        cbn [config_state config_pendingOp config_childThread].
        iFrame "Hmeta_in Htrace_new Hown_state".
        iSplit; first done.
        iSplit.
        { iPureIntro. eapply rtcL_r; first exact Hadv_steps'.
          apply adv_step_return. }
        replace (list_to_map (pendingOp_active (π1 ++ (τ, None) :: π2))
                  : gmap positive expr)
          with (delete τ
                  (list_to_map (pendingOp_active (π1 ++ (τ, Some (Val v)) :: π2))
                    : gmap positive expr)); first iFrame.
        rewrite !pendingOp_active_app pendingOp_active_cons_Some
                pendingOp_active_cons_None.
        rewrite !list_to_map_app list_to_map_cons.
        rewrite delete_union delete_insert_eq.
        rewrite !delete_id //;
          by apply not_elem_of_list_to_map_1. }
      iModIntro. wp_pures. iModIntro. by iApply "HΦ".
    Qed.

  End spec_proof.

  (* The reachable forms of the background thread, used to characterize
     2-thread derivations where the second thread is bg. The four forms
     trace the loop A → B → C → D → A. Heap_lang evaluates the argument
     before the function in [App], so B steps via Store first, then C
     steps via Rec→RecV. The Store step keeps the heap unchanged because
     the cell at [l] already holds [#false]. *)
  Inductive bg_form (l : loc) : expr → Prop :=
  | bg_form_A : bg_form l (nondet_bool_prealloc_bg #l)
  | bg_form_B : bg_form l ((#l <- #false ;; nondet_bool_prealloc_bg #l)%E)
  | bg_form_C : bg_form l
      (App (Rec BAnon BAnon (nondet_bool_prealloc_bg #l)) (Val #()))%E
  | bg_form_D : bg_form l
      (App (Val (RecV BAnon BAnon (nondet_bool_prealloc_bg #l))) (Val #()))%E.

  Definition bg_form_initial l := bg_form_A l.

  (* A single erased_step of a [bg_form] thread, when the scratch cell
     already holds [#false], preserves the heap and remains in [bg_form]. *)
  (* Helper: invert a single [erased_step] from a 1-thread pool with no
     forks (final pool also length 1). Reduces to a [base_step] under
     some evaluation context. *)
  Local Lemma erased_step_1_inv (e e' : expr) σ σ' :
    erased_step ([e], σ) ([e'], σ') →
    ∃ κ K e_in e_in', e = fill K e_in ∧ e' = fill K e_in' ∧
      base_step e_in σ κ e_in' σ' [].
  Proof.
    intros [κ Hstep].
    destruct Hstep as [eA σA eA' σA' efs t1 t2 Heq1 Heq2 Hprim].
    injection Heq1 as Heq1_t Heq1_s. subst σA.
    injection Heq2 as Heq2_t Heq2_s. subst σA'.
    destruct t1 as [|? ?]; last first.
    { simpl in Heq1_t. injection Heq1_t as <- Hbad.
      apply (f_equal length) in Hbad.
      rewrite length_app /= in Hbad. lia. }
    simpl in Heq1_t, Heq2_t.
    injection Heq1_t as <- Heq_t_nil.
    symmetry in Heq_t_nil. subst t2.
    destruct efs as [|? ?]; last first.
    { simpl in Heq2_t. injection Heq2_t as <- Hbad.
      apply (f_equal length) in Hbad. simpl in Hbad. lia. }
    simpl in Heq2_t. injection Heq2_t as <-.
    destruct Hprim as [K e_in e_in' He He' Hbase].
    exists κ, K, e_in, e_in'. done.
  Qed.

  (* A no-fork [base_step] on a [Val] is impossible. *)
  Local Lemma base_step_not_val v σ κ e' σ' efs :
    base_step (Val v) σ κ e' σ' efs → False.
  Proof. inversion 1. Qed.

  (* Helper: turn a PureExec-1 step into a prim_step determinism statement. *)
  Local Lemma pure_step_unique (e_pure e_next e e' : expr) σ σ' efs κ :
    PureExec True 1 e_pure e_next →
    e_pure = e →
    prim_step e σ κ e' σ' efs →
    e' = e_next ∧ σ' = σ ∧ efs = [] ∧ κ = [].
  Proof.
    intros HPE Heq Hprim. subst e.
    specialize (HPE I).
    inversion HPE; subst.
    rename select (pure_step _ _) into Hone.
    rename select (relations.nsteps _ _ _ _) into Hns.
    inversion Hns; subst.
    destruct Hone as [_ Hdet].
    edestruct (Hdet σ κ e' σ' efs Hprim) as (-> & -> & -> & ->).
    done.
  Qed.

  Local Lemma bg_form_step (l : loc) (σ σ' : state) (e e' : expr) :
    bg_form l e →
    σ.(heap) !! l = Some (Some #false) →
    erased_step ([e], σ) ([e'], σ') →
    σ' = σ ∧ bg_form l e'.
  Proof.
    intros Hbg Hheap Hstep.
    apply erased_step_1_inv in Hstep
      as (κ & K & e_in & e_in' & He & He' & Hbase).
    (* Reassemble a [prim_step] from the fill-decomposition. *)
    assert (Hprim : prim_step e σ κ e' σ' []).
    { rewrite He He'. by econstructor. }
    clear He He' Hbase e_in e_in' K.
    destruct Hbg.
    - (* Form A → B: pure β step. *)
      rewrite /nondet_bool_prealloc_bg in Hprim.
      pose (Hpe := @pure_beta "f" "l"
        ("l" <- #false ;; "f" "l")%E
        (RecV "f" "l" ("l" <- #false ;; "f" "l")%E)
        (LitV (LitLoc l)) (AsRecV_recv _ _ _)).
      edestruct (pure_step_unique _ _ _ _ _ _ _ _ Hpe eq_refl Hprim)
        as (-> & -> & _ & _).
      split; first done. cbn. apply bg_form_B.
    - (* Form B → C: Store inside [AppRCtx (Rec _ _ _)]. The Store is a no-op
         on the heap because the cell already holds [#false]. *)
      change (#l <- #false ;; nondet_bool_prealloc_bg #l)%E
        with (fill [AppRCtx (Rec BAnon BAnon (nondet_bool_prealloc_bg #l))]
                   (#l <- #false)%E) in Hprim.
      assert (Hto_val_None : to_val (#l <- #false)%E = None) by reflexivity.
      apply (fill_step_inv _ _ _ _ _ _ Hto_val_None) in Hprim
        as (e2_inner & Heq_e' & Hprim_store).
      (* [Hprim_store] is a [prim_step] on [#l <- #false]; invert it to get
         the [StoreS] base_step. *)
      simpl in *.
      apply (atomic (a:=StronglyAtomic)) in Hprim_store as He2_inner_val.
      destruct He2_inner_val as [v2_inner Hsome].
      rewrite -(of_to_val _ _ Hsome) in Heq_e', Hprim_store.
      apply (prim_step_to_val_is_base_step) in Hprim_store as Hbase_store.
      clear Hprim_store.
      inversion Hbase_store.
      simplify_eq.
      split.
      + destruct σ as [h p]. rewrite /state_upd_heap /=. f_equal.
        by rewrite insert_id.
      + cbn. apply bg_form_C.
    - (* Form C → D: Rec→RecV inside [AppLCtx (Val #())]. *)
      assert (Hpe :
        PureExec True 1
          (App (Rec BAnon BAnon (nondet_bool_prealloc_bg #l)) (Val #()))
          (App (Val (RecV BAnon BAnon (nondet_bool_prealloc_bg #l))) (Val #()))).
      { intros _.
        apply (pure_step_nsteps_ctx (fill [AppLCtx (LitV LitUnit)])).
        apply (pure_recc BAnon BAnon _ I). }
      edestruct (pure_step_unique _ _ _ _ _ _ _ _ Hpe eq_refl Hprim)
        as (-> & -> & _ & _).
      split; first done. cbn. apply bg_form_D.
    - (* Form D → A: pure β step. *)
      pose (Hpe := @pure_beta BAnon BAnon (nondet_bool_prealloc_bg #l)
        (RecV BAnon BAnon (nondet_bool_prealloc_bg #l))
        (LitV LitUnit) (AsRecV_recv _ _ _)).
      edestruct (pure_step_unique _ _ _ _ _ _ _ _ Hpe eq_refl Hprim)
        as (-> & -> & _ & _).
      split; first done. cbn. apply bg_form_A.
  Qed.

  (* 2-thread reverse simulation: given a 2-thread derivation in
     [compose_state] whose head thread terminates to a value, extract a
     σ-level reduction of the head thread. The second thread is the
     fixed background thread, which preserves the composed state across
     all its (looped) steps. *)
  Local Lemma erased_steps_compose_uncompose_init_terminates
        (tracer : loc) (e_init e_bg : expr) (σ : state)
        (ts : list (positive*trace))
        (v_init : val) (t2 : list expr) (σ_compose' : state) :
    composable_state tracer σ →
    adequate NotStuck e_init σ (λ _ _, True) →
    sequential e_init σ →
    adequate NotStuck e_init (compose_state tracer σ ts) (λ _ _, True) →
    sequential e_init (compose_state tracer σ ts) →
    bg_form (tracer +ₗ 2) e_bg →
    rtc erased_step ([e_init; e_bg], compose_state tracer σ ts)
                    (Val v_init :: t2, σ_compose') →
    ∃ σ_init, rtc erased_step ([e_init], σ) ([Val v_init], σ_init).
  Proof.
    intros Hcomp Hadq_σ Hseq_σ Hadq_c Hseq_c Hbg [n Hns]%rtc_nsteps_1.
    revert e_init e_bg σ t2 σ_compose'
           Hcomp Hadq_σ Hseq_σ Hadq_c Hseq_c Hbg Hns.
    induction n as [|n IH];
      intros e_init e_bg σ t2 σ_compose'
             Hcomp Hadq_σ Hseq_σ Hadq_c Hseq_c Hbg Hns.
    { apply nsteps_O_eq_helper in Hns.
      pose proof (f_equal fst Hns) as Hcfg_t. simpl in Hcfg_t.
      injection Hcfg_t as Hcfg_h _.
      exists σ. rewrite -Hcfg_h. apply rtc_refl. }
    inversion Hns. simplify_eq.
    rename select (cfg _) into ρmid.
    destruct ρmid as [t_mid σ_mid_compose].
    rename select (erased_step _ _) into Hstep.
    rename select (relations.nsteps erased_step _ _ _) into Hns_rest.
    (* Pool length at intermediate: ≥ 2 (monotonic from initial pool). *)
    pose proof (erased_step_grow _ _ _ _ Hstep) as Hlen_ge.
    cbn in Hlen_ge.
    (* We need [t_mid] to have exactly the form [m1 :: m2 :: rest]. *)
    destruct t_mid as [|m1 [|m2 t_mid_rest]];
      [simpl in Hlen_ge; lia|simpl in Hlen_ge; lia|].
    (* Case-analyze on which thread (init or bg) stepped. Since neither
       forks, the step doesn't add new threads and [t_mid_rest = []].
       Rather than prove that upfront, we case on the structural form of
       [Hstep] directly. *)
    destruct Hstep as [κ Hstep_inner].
    destruct Hstep_inner as [eA σA eA' σA' efs t_pre t_post Heq1 Heq2 Hprim].
    injection Heq1 as Heq1_t ?. subst σA.
    injection Heq2 as Heq2_t ?. subst σA'.
    destruct t_pre as [|? [|? ?]]; cbn in Heq1_t.
    - (* [t_pre = []]: [eA = e_init], so init stepped. *)
      injection Heq1_t as <- <-.
      cbn in Heq2_t. injection Heq2_t as <- Heq2_rest.
      (* From [adequate] at σ, init doesn't fork: [efs = []]. *)
      assert (Hred_init : reducible e_init σ).
      { opose proof (adequate_not_stuck _ _ _ _ Hadq_σ [e_init] σ e_init
                    eq_refl (rtc_refl _ _))
          as [Hisval|Hr]; [set_solver| |exact Hr].
        exfalso. destruct Hisval as [v_init0 Hv].
        apply val_stuck in Hprim. by rewrite Hv in Hprim. }
      (* From [sequential] at compose_state, init doesn't fork at compose_state. *)
      assert (Hefs_nil : efs = []).
      { assert (Hreach :
          rtc erased_step ([e_init], compose_state tracer σ ts)
                          (m1 :: efs, σ_mid_compose)).
        { eapply rtc_l; last apply rtc_refl. exists κ.
          eapply (step_atomic e_init _ m1 _ efs [] []);
            [reflexivity..|exact Hprim]. }
        pose proof (Hseq_c _ _ Hreach) as Hlen.
        cbn in Hlen.
        destruct efs as [|? ?]; [reflexivity|cbn in Hlen; lia]. }
      subst efs. cbn in Heq2_rest. subst t_mid_rest.
      (* Construct a 1-thread step and use the 1-thread uncompose. *)
      assert (Hstep_compose : erased_step ([e_init], compose_state tracer σ ts)
                                          ([m1], σ_mid_compose)).
      { exists κ.
        eapply (step_atomic e_init _ m1 _ [] [] []);
          [reflexivity..|exact Hprim]. }
      pose proof Hstep_compose as Hstep_compose_copy.
      apply (erased_step_compose_uncompose tracer σ ts _ _ _ Hcomp Hred_init)
        in Hstep_compose as (σ_mid_σ & Hcomp_mid & Hcompose_eq & Hstep_σ).
      pose proof (adequate_erased_step _ _ _ _ _ _ _ Hstep_σ Hadq_σ)
        as Hadq_σ_mid.
      pose proof (sequential_erased_step _ _ _ _ Hstep_σ Hseq_σ)
        as Hseq_σ_mid.
      assert (Hadq_c_mid : adequate NotStuck m1
                            (compose_state tracer σ_mid_σ ts) (λ _ _, True)).
      { rewrite -Hcompose_eq.
        eapply adequate_erased_step; [exact Hstep_compose_copy|exact Hadq_c]. }
      assert (Hseq_c_mid : sequential m1 (compose_state tracer σ_mid_σ ts)).
      { rewrite -Hcompose_eq.
        eapply sequential_erased_step; [exact Hstep_compose_copy|exact Hseq_c]. }
      rewrite Hcompose_eq in Hns_rest.
      subst m2.
      destruct (IH m1 e_bg σ_mid_σ t2 σ_compose'
                  Hcomp_mid Hadq_σ_mid Hseq_σ_mid Hadq_c_mid Hseq_c_mid
                  Hbg Hns_rest)
        as (σ_post & Hrest).
      exists σ_post. eapply rtc_l; eassumption.
    - (* [t_pre = [?]]: [eA = e_bg], so bg stepped. *)
      (* From [Heq1_t : [e_init; e_bg] = ?t_pre_head :: eA :: t_post]:
         ?t_pre_head = e_init, eA = e_bg, t_post = []. *)
      assert (Heq_lengths : length t_post = 0).
      { apply (f_equal length) in Heq1_t. cbn in Heq1_t. lia. }
      apply length_zero_iff_nil in Heq_lengths. subst t_post.
      cbn in Heq1_t. injection Heq1_t as <- <-.
      (* Now [Heq2_t : m1 :: m2 :: t_mid_rest = eA' :: efs]. *)
      (* By inspection of bg's [base_step]s (none are [ForkS]), [efs = []]. *)
      assert (Hefs_nil : efs = []).
      { clear -Hprim Hbg.
        destruct Hbg.
        (* Use fork_free_prim_step *)
        - destruct (fork_free_prim_step _ _ _ _ _ _ Hprim
                    ltac:(vm_compute; reflexivity)) as [_ ->]. done.
        - destruct (fork_free_prim_step _ _ _ _ _ _ Hprim
                    ltac:(vm_compute; reflexivity)) as [_ ->]. done.
        - destruct (fork_free_prim_step _ _ _ _ _ _ Hprim
                    ltac:(vm_compute; reflexivity)) as [_ ->]. done.
        - destruct (fork_free_prim_step _ _ _ _ _ _ Hprim
                    ltac:(vm_compute; reflexivity)) as [_ ->]. done. }
      subst efs.
      assert (Hlen_eq : length t_mid_rest = 0).
      { apply (f_equal length) in Heq2_t. cbn in Heq2_t. lia. }
      apply length_zero_iff_nil in Hlen_eq. subst t_mid_rest.
      cbn in Heq2_t. injection Heq2_t as <- <-.
      assert (Hcell_false :
        (compose_state tracer σ ts).(heap) !! (tracer +ₗ 2) = Some (Some #false))
        by by apply compose_state_lookup_trace2.
      assert (Hbg_step : erased_step ([e_bg], compose_state tracer σ ts)
                                     ([m2], σ_mid_compose)).
      { exists κ.
        eapply (step_atomic e_bg _ m2 _ [] [] []);
          [reflexivity..|exact Hprim]. }
      pose proof (bg_form_step _ _ _ _ _ Hbg Hcell_false Hbg_step)
        as [Heq_σ Hbg'].
      rewrite Heq_σ in Hns_rest.
      apply (IH m1 m2 σ t2 σ_compose'
              Hcomp Hadq_σ Hseq_σ Hadq_c Hseq_c Hbg' Hns_rest).
    - (* [t_pre = [_; _; ...]]: impossible. *)
      exfalso. apply (f_equal length) in Heq1_t. cbn in Heq1_t.
      rewrite length_app in Heq1_t. cbn in Heq1_t. lia.
  Qed.

  Lemma adv_match_mgc_steps ts₀ (tracer : loc) v other_ts' σ' :
    to_val init = None →
    (∀ σ, sequential init σ) →
    (∀ σ, adequate NotStuck init σ (λ _ _, True)) →
    (∀ obj σ₀ σ config' ts,
      rtc erased_step ([init], σ₀) ([Val obj], σ) →
      rtcL (adv_step ops obj valid_reqs) (Config [] [] σ) config' ts →
      config_not_stuck config') →
    Forall (λ x, if x.2 is Call n req then default default_vr (valid_reqs!!n) req else True) ts₀ →
    {[tracer; tracer +ₗ 1; tracer +ₗ 2]} ## dom (σ₀.(heap)) →
    rtc erased_step ([mgc_of_trace tracer ts₀ (encode_val ops) init;
                      nondet_bool_prealloc_bg #(tracer +ₗ 2)],
                      (compose_state tracer σ₀ []))
                    (Val v::other_ts', σ') →
    ∃ ts, v = encode_trace ts ∧ ∃ obj efs σ config',
        rtc erased_step ([init],σ₀) (Val obj::efs,σ)
      ∧ rtcL (adv_step ops obj valid_reqs) (Config [] [] σ) config' ts.
  Proof.
    intros Hinit_nv Hseq_init Hadq_init Hadq_op Hvalid_req Hfresh Hsteps.
    set (φ := λ v, ∃ ts, v = encode_trace ts ∧ I_adv ts).
    opose proof (trace_adequacy (Σ:=Σ) tracer
        (mgc_of_trace tracer ts₀ (encode_val ops) init)%E
        (compose_state tracer σ₀ []) MaybeStuck I_adv φ
        _ (* I [] *) _ (* ... -∗ WP ... *)
        v other_ts' σ' false
        _ _ _ Hsteps) as [(ts & Heqv & Hadv) _].
    1: {
      (* [I_adv []]: from [Hsteps] we extract that [init] terminates
         from [compose_state σ₀ []] (via the 2-thread [bind_inv]); the
         2-thread reverse-simulation lemma then gives termination from σ₀. *)
      change (mgc_of_trace tracer ts₀ (encode_val ops) init)%E
        with (fill [AppRCtx (mgc_of_trace tracer ts₀ (encode_val ops))] init) in Hsteps.
      apply (erased_steps_bind_inv_two _ _ _ _ v _ _) in Hsteps
        as (v_init & t2_init & σ_mid & Hsteps_init & _).
      assert (Hcomp_σ₀ : composable_state tracer σ₀) by exact Hfresh.
      pose proof (erased_steps_compose_uncompose_init_terminates tracer init
                    (nondet_bool_prealloc_bg #(tracer +ₗ 2))
                    σ₀ [] v_init t2_init σ_mid
                    Hcomp_σ₀ (Hadq_init _) (Hseq_init _)
                    (Hadq_init _) (Hseq_init _)
                    (bg_form_initial _) Hsteps_init)
        as (σ_post & Hinit_σ₀).
      red.
      exists v_init, [], σ_post, (Config [] [] σ_post).
      split; [exact Hinit_σ₀ | apply rtcL_refl]. }
    { iIntros (?) "Hhi Hti Ht Hls Hps".
      iApply (mgc_spec_gen (own_state σ₀) adv_repr MaybeStuck valid_reqs
              init ops tracer ts₀ Hvalid_req
              (adv_init_spec Hinit_nv Hadq_init Hseq_init)
              (adv_call_ret_wrapper_spec Hadq_init Hseq_init Hadq_op)
            with "Hhi Hti Ht").
      rewrite /compose_state /trace_to_state /=.
      rewrite map_union_comm; last (apply map_disjoint_dom; set_solver).
      rewrite -!insert_union_l left_id_L !delete_insert_id; first last;
        [apply not_elem_of_dom_1; rewrite ?dom_insert_L..|].
      { rewrite !not_elem_of_union !not_elem_of_singleton. split_and!.
        - symmetry; apply tracer_neq_1.
        - symmetry; apply tracer_neq_2.
        - set_solver. }
      { rewrite !not_elem_of_union !not_elem_of_singleton. split_and!.
        - symmetry; apply tracer_neq_12.
        - set_solver. }
      { set_solver. }
      rewrite right_id_L.
      iFrame. }
    { by apply compose_state_lookup_trace0. }
    { by apply compose_state_lookup_trace1. }
    { by apply compose_state_lookup_trace2. }
    exists ts. split; first done.
    exact Hadv.
  Qed.
End requisteness.
(**************** End LLM-generated code. *****************)

Section free.
  Context `{!heapGpreS Σ, !traceG Σ}.
  Context (R : mgc_repr Σ).
  Context (valid_reqs : list (val → Prop)).
  Context (init : expr) (ops : list val).

  (* Per-thread [not_stuck] in the composed state, at the granularity of
    the wrapped thread pool. The pool has the shape
    [Val (encode_trace ts) :: nondet_bool_prealloc_bg #(tracer +ₗ 2)
      :: efs ++ (pending_to_simulated tracer <$> config'.pendingOp)
      ++ config'.childThread],
    where [efs] carries any forks from [init], the background thread
    appears at index 1, pending ops appear as [pending_to_simulated]-
    wrapped expressions, and each child thread sits at its source-level
    position. *)
  Lemma bdgjst_free_pool σ₀ obj efs σ config' ts (tracer : loc) :
    {[tracer; tracer+ₗ1; tracer+ₗ2]} ## dom (heap (config_state config')) →
    (∀ `(!heapGS Σ), init_spec_type R NotStuck init) →
    (∀ `(!heapGS Σ), call_ret_wrapper_spec_type R NotStuck valid_reqs ops) →
    I_lang R [] →
    rtc erased_step ([init],σ₀) (Val obj::efs,σ) →
    rtcL (adv_step ops obj valid_reqs) (Config [] [] σ) config' ts →
    I_lang R ts ∧
    ∀ e2, e2 ∈ Val (encode_trace ts) ::
                nondet_bool_prealloc_bg #(tracer +ₗ 2) ::
                efs ++
                (pending_to_simulated tracer <$> config'.(config_pendingOp)) ++
                config'.(config_childThread) →
      not_stuck e2 (compose_state tracer (config_state config') ts).
  Proof.
    intros Htracer_disj' init_spec op_spec HIinit Hinit_steps Hop_steps.
    assert (Htracer_disj: {[tracer; tracer+ₗ1; tracer+ₗ2]} ## dom (heap σ)).
    { pose proof (Hsubdom := adv_steps_heap_subdom _ _ _ _ _ _ Hop_steps).
      simpl in Hsubdom. set_solver. }
    assert (Htracer_disj₀ : {[tracer; tracer+ₗ1; tracer+ₗ2]} ## dom (heap σ₀)).
    { pose proof (Hsubdom := erased_steps_heap_subdom _ _ _ _ Hinit_steps).
      set_solver. }

    pose proof (mgc_match_adv_steps ops obj valid_reqs σ config' ts tracer
                 Htracer_disj' Hop_steps)
      as Hop_steps'.

    opose proof (simulate_erased_steps tracer _ _ _ _ [] Hinit_steps _)
      as Hinit_steps'.
    { exact Htracer_disj. }

    opose proof (trace_adequacy tracer (mgc_of_trace tracer ts (encode_val ops) init)
      (compose_state tracer σ₀ []) NotStuck
      (I_lang R) (λ v, ∃ ts0, v = encode_trace ts0 ∧ I_lang R ts0)
      HIinit _ (encode_trace ts)
      (nondet_bool_prealloc_bg #(tracer +ₗ 2)
        :: efs ++ (pending_to_simulated tracer <$> config'.(config_pendingOp))
                   ++ config'.(config_childThread))
      (compose_state tracer (config_state config') ts) false _ _ _ _)
      as [(ts' & Heq & HI_lang) Hns].
    { iIntros (?) "??? _ _". iApply (mgc_spec with "[$] [$] [$]"); [| |done..].
      - by eapply adv_steps_trace_valid_req.
      - by apply init_spec. }
    { by (eapply (compose_state_lookup_trace0)). }
    { by (eapply (compose_state_lookup_trace1)). }
    { by (eapply (compose_state_lookup_trace2)). }
    { (* Source-level init steps lifted to compose_state, then the
         wrapper steps, with the bg thread sitting at index 1. *)
      apply (erased_steps_app_r [init] _ [Val obj] _ _
               [nondet_bool_prealloc_bg #(tracer +ₗ 2)] eq_refl) in Hinit_steps'.
      simpl in Hinit_steps'.
      assert (Hwrapped :
        rtc erased_step
          ([mgc_of_trace tracer ts (encode_val ops) init;
            nondet_bool_prealloc_bg #(tracer +ₗ 2)], compose_state tracer σ₀ [])
          (mgc_of_trace tracer ts (encode_val ops) (Val obj)
            :: nondet_bool_prealloc_bg #(tracer +ₗ 2) :: efs, compose_state tracer σ [])).
      { apply (fill_erased_steps [AppRCtx _] _ _ _ _ [] _ [] _ eq_refl).
        simpl. exact Hinit_steps'. }
      etrans; [exact Hwrapped|].
      apply (erased_steps_app_r
              [mgc_of_trace tracer ts (encode_val ops) obj; nondet_bool_prealloc_bg #(tracer +ₗ 2)] _
              [Val (encode_trace ts); nondet_bool_prealloc_bg #(tracer +ₗ 2)] _ _ efs
              eq_refl) in Hop_steps'.
      simpl in Hop_steps'.
      exact Hop_steps'. }

    apply (inj encode_trace) in Heq as <-.
    split; first done.
    intros ?. by apply Hns.
  Qed.

  Local Lemma not_stuck_fill (K : list ectx_item) (e : expr) σ :
    not_stuck (fill K e) σ → not_stuck e σ.
  Proof.
    intros [[v Hv]|Hr].
    - apply to_val_fill_some in Hv as [-> ->]. left. by exists v.
    - destruct (to_val e) as [v|] eqn:Hv; first by left; exists v.
      right. by eapply (reducible_fill_inv (K := fill K)).
  Qed.

  (* [config_not_stuck]-shaped Foralls over [config'.pendingOp] and
    [config'.childThread], in the composed state. Each pending op's
    [simulatedOp_pending_ctx] wrapper is stripped via [not_stuck_fill];
    each child thread sits directly in the pool's tail. *)
  Lemma bdgjst_free_composed σ₀ obj efs σ config' ts (tracer : loc) :
    {[tracer; tracer+ₗ1; tracer+ₗ2]} ## dom (heap (config_state config')) →
    (∀ `(!heapGS Σ), init_spec_type R NotStuck init) →
    (∀ `(!heapGS Σ), call_ret_wrapper_spec_type R NotStuck valid_reqs ops) →
    I_lang R [] →
    rtc erased_step ([init],σ₀) (Val obj::efs,σ) →
    rtcL (adv_step ops obj valid_reqs) (Config [] [] σ) config' ts →
    I_lang R ts ∧
    let composed := compose_state tracer (config_state config') ts in
    Forall (λ '(_, oe), match oe with Some e => not_stuck e composed | None => True end)
           config'.(config_pendingOp) ∧
    Forall (λ e, not_stuck e composed) config'.(config_childThread).
  Proof.
    intros Htracer_disj Hinit_spec Hop_spec HIinit Hinit_steps Hop_steps.
    pose proof (bdgjst_free_pool σ₀ obj efs σ config' ts tracer
                  Htracer_disj Hinit_spec Hop_spec HIinit Hinit_steps Hop_steps)
      as [HI_lang Hns].
    split; first done.
    set (composed := compose_state tracer (config_state config') ts).
    split.
    - apply Forall_forall. intros [τ [e|]] Hin; last done.
      assert (Hns_wrapped : not_stuck (fill (simulatedOp_pending_ctx tracer τ) e) composed).
      { apply Hns.
        rewrite elem_of_cons. right.
        rewrite elem_of_cons. right.
        rewrite !elem_of_app. right; left.
        by apply (list_elem_of_fmap_2 (pending_to_simulated tracer) _ (τ, Some e)). }
      by apply not_stuck_fill in Hns_wrapped.
    - apply Forall_forall. intros e_child Hin_child.
      apply Hns.
      rewrite elem_of_cons. right.
      rewrite elem_of_cons. right.
      rewrite !elem_of_app. by right; right.
  Qed.

  Local Lemma heap_array_3 (l : loc) (v1 v2 v3 : val) :
    heap_array l [v1; v2; v3] =
    {[l := Some v1; l +ₗ 1 := Some v2; l +ₗ 2 := Some v3]}.
  Proof.
    simpl.
    rewrite (Loc.add_assoc l 1 1) /=.
    rewrite right_id_L.
    rewrite -!insert_union_singleton_l.
    reflexivity.
  Qed.

  Local Lemma compose_state_is_σ_ext (tracer : loc) σ ts :
    composable_state tracer σ →
    compose_state tracer σ ts =
    σ_ext tracer [encode_trace ts; NONEV; #false] σ.
  Proof.
    intros Hcomp.
    rewrite /compose_state /trace_to_state heap_array_3.
    rewrite /(union (A:=state)) /state_union /state_upd_heap /=.
    f_equal.
    - apply map_union_comm, map_disjoint_dom.
      rewrite /composable_state in Hcomp.
      rewrite dom_insert_L dom_insert_L dom_singleton_L. set_solver.
    - apply right_id_L, _.
  Qed.

  (* An end-to-end result in the style of Birkedal et al.'s Free
    Theorem (2021), phrased in terms of most adversarial steps.

    If [init] and [ops] satisfy the trace-indexed call-return specifications
    for the representation [R], then for any adversarial run ending at
    [config'], the source-level trace is in [I_lang R] and every source
    thread of [config'] is [not_stuck] at [config_state config']. The proof
    invokes the composed-state variant at every fresh tracer location and
    frames out the three trace cells via [not_stuck_heap_restrict]. *)
  Theorem bdgjst_free σ₀ obj efs σ config' ts :
    (∀ `(!heapGS Σ), init_spec_type R NotStuck init) →
    (∀ `(!heapGS Σ), call_ret_wrapper_spec_type R NotStuck valid_reqs ops) →
    I_lang R [] →
    rtc erased_step ([init],σ₀) (Val obj::efs,σ) →
    rtcL (adv_step ops obj valid_reqs) (Config [] [] σ) config' ts →
    config_not_stuck config' ∧ I_lang R ts.
  Proof.
    intros Hinit_spec Hop_spec HIinit Hinit_steps Hop_steps.
    set (tracer0 := Loc.fresh (dom (heap (config_state config')))).
    assert (Htracer0_disj: {[tracer0; tracer0+ₗ1; tracer0+ₗ2]} ## dom (heap (config_state config'))).
    { rewrite !disjoint_union_l !disjoint_singleton_l. split_and!.
      - rewrite -(Loc.add_0 tracer0). eapply Loc.fresh_fresh. lia.
      - eapply Loc.fresh_fresh. lia.
      - eapply Loc.fresh_fresh. lia. }
    pose proof (bdgjst_free_composed σ₀ obj efs σ config' ts tracer0
                 Htracer0_disj Hinit_spec Hop_spec HIinit Hinit_steps Hop_steps)
      as [HI_lang _].
    split; last done.
    assert (Haux : ∀ (l : loc),
              (∀ i : nat, i < 3 → l +ₗ i ∉ dom (config_state config').(heap)) →
              ∃ ws, length ws = 3 ∧
                    Forall (λ '(_, oe), match oe with
                                        | Some e => not_stuck e (σ_ext l ws (config_state config'))
                                        | None => True end)
                           config'.(config_pendingOp) ∧
                    Forall (λ e, not_stuck e (σ_ext l ws (config_state config')))
                           config'.(config_childThread)).
    { intros l Hl_fresh.
      pose proof (Hl_fresh 0 ltac:(lia)) as H0.
      pose proof (Hl_fresh 1 ltac:(lia)) as H1.
      pose proof (Hl_fresh 2 ltac:(lia)) as H2.
      change (l +ₗ 0%nat) with (l +ₗ 0%Z) in H0.
      change (l +ₗ 1%nat) with (l +ₗ 1%Z) in H1.
      change (l +ₗ 2%nat) with (l +ₗ 2%Z) in H2.
      rewrite Loc.add_0 in H0.
      assert (Hdisj_l : {[l; l+ₗ1; l+ₗ2]} ## dom (heap (config_state config'))).
      { set_solver. }
      pose proof (bdgjst_free_composed σ₀ obj efs σ config' ts l
                   Hdisj_l Hinit_spec Hop_spec HIinit Hinit_steps Hop_steps)
        as [_ (Hpending & Hchild)].
      exists [encode_trace ts; NONEV; #false].
      rewrite -(compose_state_is_σ_ext l (config_state config') ts);
        last exact Hdisj_l.
      split_and!; [reflexivity|exact Hpending|exact Hchild]. }
    split.
    - apply Forall_forall. intros [τ [e|]] Hin_pending; last done.
      apply (not_stuck_heap_restrict _ _ 3).
      intros l Hl_fresh.
      destruct (Haux l Hl_fresh) as (ws & Hws_len & Hpending & _).
      exists ws. split; first done.
      rewrite Forall_forall in Hpending.
      by specialize (Hpending _ Hin_pending).
    - apply Forall_forall. intros e_child Hin_child.
      apply (not_stuck_heap_restrict _ _ 3).
      intros l Hl_fresh.
      destruct (Haux l Hl_fresh) as (ws & Hws_len & _ & Hchild).
      exists ws. split; first done.
      rewrite Forall_forall in Hchild.
      by apply Hchild.
  Qed.
End free.
