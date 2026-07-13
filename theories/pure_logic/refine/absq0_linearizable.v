(* absq0_linearizable.v: bridge from "a Call/Ret trace refines AbsQ₀ / AbsQ"
  to [trace_linearizable] in the sense of [linear.v].

  This is the refine technique's headline result, stated in the same
  trace-level style as the other techniques ([metaconfig], [aspect]):
  a Call/Ret trace [ts] is declared linearizable iff it can be extended
  with [Lin] events so the extended trace is per-tag [Call → Lin → Ret]
  and the [Lin] projection is a valid sequential execution of a chosen
  [model] (this is exactly [trace_linearizable]). The generic lift from
  [trace_linearizable] to the library-level [library_linearizable] is
  handled uniformly elsewhere (see [program_logic/atomic_sound.v], which
  plugs [I_lang := trace_linearizable] into the [mgc] bridge), so it is
  not repeated here.

  This file plugs in the queue model [queue_model] from
  [pure_logic/models/bag_like.v] (parameterized by a [valid_value]
  predicate) and delivers two trace-level theorems:
  - [refines_absq0_trace_linearizable]: any Call/Ret trace that is the
    projection of a reachable AbsQ₀ execution (i.e., refines AbsQ₀ at the
    C∪R level) is [trace_linearizable];
  - [refines_absq_trace_linearizable]: any Call/Ret trace refining AbsQ at
    the C∪R level is [trace_linearizable], by chaining the above with the
    AbsQ ⊑ AbsQ₀ backward simulation from [absq_refines_absq0.v]. *)

From iris_logatom.pure_logic Require Import linear.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
  backward_simulation.
From iris.heap_lang Require Import notation.
From stdpp Require Import list gmap.

(** Per-label translation from AbsQ₀ action labels to [linear.v] trace
  events. Requests/responses use [bag_like.v]'s [encode_request] /
  [encode_response]: enqueue of [d] is [SOMEV d] and dequeue is [NONEV]
  on the request side; on the response side, dequeue results are
  already option-encoded ([SOMEV d] for non-empty, [NONEV] for empty)
  by [absq_step] / [absq0_step]. *)
Definition trace_of_absq_label (la : positive * absq_action)
  : positive * trace :=
  match la with
  | (τ, ACallEnq d) => (τ, Call (encode_request (Push d)))
  | (τ, ACallDeq)   => (τ, Call (encode_request Pop))
  | (τ, ARetEnq)    => (τ, Ret #())
  | (τ, ARetDeq v)  => (τ, Ret v)
  | (τ, ALinEnq d)  => (τ, Lin (encode_request (Push d)) #())
  | (τ, ALinDeq v)  => (τ, Lin (encode_request Pop) v)
  end.

Definition trace_of_absq_labels
  : list (positive * absq_action) → list (positive * trace) :=
  map trace_of_absq_label.

Lemma trace_of_absq_label_fst la : (trace_of_absq_label la).1 = la.1.
Proof. destruct la as [? []]; reflexivity. Qed.

(** Snoc-inversion for [absq0_steps] (i.e., [lts_steps absq0_step]):
  every [ls ++ [l]]-trace decomposes into a prefix trace and a final
  step. Used by the reverse induction in [absq0_steps_invariant]. *)
Lemma absq0_steps_snoc_inv rme valid_value s0 s2 ls l :
  absq0_steps rme valid_value s0 (ls ++ [l]) s2 →
  ∃ s1, absq0_steps rme valid_value s0 ls s1 ∧ absq0_step rme valid_value s1 l s2.
Proof.
  revert s0 s2. induction ls as [|l0 ls IH]; intros s0 s2 Hs; simpl in *.
  - inversion Hs as [|? s1 ? ? ? Hstep Hrest]; subst.
    inversion Hrest; subst. exists s0. split; [constructor|done].
  - inversion Hs as [|? s1 ? ? ? Hstep Hrest]; subst.
    apply IH in Hrest as (s_mid & Hrest' & Hlast_step).
    exists s_mid. split; [|done]. by econstructor.
Qed.

(** Per-tag invariant: for every tag [τ], the [τ]-filtered events of
  the induced trace are determined exactly by the AbsQ₀ state via
  [cp0(τ)]. Each control-point maps to a specific prefix of the
  [Call → Lin → Ret] sequence, with input/return values read from
  [in0]/[rv0]. Requests/responses follow [bag_like.queue_model]'s
  encoding. *)
Definition per_tag_invariant (u : absq0_state) (τ : positive)
    (ts' : list (positive * trace)) : Prop :=
  match u.(absq0_cp) !! τ with
  | None =>
      filter (λ t, t.1 = τ) ts' = []
  | Some A1 =>
      ∃ d, u.(absq0_in) !! τ = Some d ∧
           filter (λ t, t.1 = τ) ts' = [(τ, Call (encode_request (Push d)))]
  | Some A =>
      ∃ d, u.(absq0_in) !! τ = Some d ∧
           filter (λ t, t.1 = τ) ts' =
             [(τ, Call (encode_request (Push d)));
              (τ, Lin (encode_request (Push d)) #())]
  | Some A2 =>
      ∃ d, u.(absq0_in) !! τ = Some d ∧
           filter (λ t, t.1 = τ) ts' =
             [(τ, Call (encode_request (Push d)));
              (τ, Lin (encode_request (Push d)) #());
              (τ, Ret #())]
  | Some R1 =>
      filter (λ t, t.1 = τ) ts' = [(τ, Call (encode_request Pop))]
  | Some R2 =>
      ∃ v, u.(absq0_rv) !! τ = Some v ∧
           filter (λ t, t.1 = τ) ts' =
             [(τ, Call (encode_request Pop));
              (τ, Lin (encode_request Pop) v)]
  | Some R3 =>
      ∃ v, u.(absq0_rv) !! τ = Some v ∧
           filter (λ t, t.1 = τ) ts' =
             [(τ, Call (encode_request Pop));
              (τ, Lin (encode_request Pop) v);
              (τ, Ret v)]
  end.

Lemma per_tag_invariant_to_per_tag_linearized u ts' :
  (∀ τ, per_tag_invariant u τ ts') →
  per_tag_linearized ts'.
Proof.
  intros H τ. specialize (H τ). rewrite /per_tag_invariant in H.
  destruct (absq0_cp u !! τ) as [c|] eqn:Hcp.
  - destruct c.
    + destruct H as (d & _ & Hf). exists (encode_request (Push d)), #().
      rewrite Hf. apply prefix_cons, prefix_nil.
    + destruct H as (d & _ & Hf). exists (encode_request (Push d)), #().
      rewrite Hf. apply prefix_cons, prefix_cons, prefix_nil.
    + destruct H as (d & _ & Hf). exists (encode_request (Push d)), #().
      rewrite Hf. done.
    + exists (encode_request Pop), #(). rewrite H. apply prefix_cons, prefix_nil.
    + destruct H as (v & _ & Hf). exists (encode_request Pop), v.
      rewrite Hf. apply prefix_cons, prefix_cons, prefix_nil.
    + destruct H as (v & _ & Hf). exists (encode_request Pop), v.
      rewrite Hf. done.
  - exists #(), #(). rewrite H. apply prefix_nil.
Qed.

(** The filter for tag τ, when appending a new event whose tag is τ₀ ≠ τ,
  is unchanged. Used repeatedly in the τ ≠ l.1 side of every step case. *)
Local Lemma filter_tag_app_ne (τ τ₀ : positive) te (ts' : list (positive * trace)) :
  te.1 = τ₀ → τ ≠ τ₀ →
  filter (λ t, t.1 = τ) (ts' ++ [te]) = filter (λ t, t.1 = τ) ts'.
Proof.
  intros Hte Hne. rewrite filter_app filter_cons_False.
  - by rewrite filter_nil right_id_L.
  - rewrite Hte. exact (λ H, Hne (eq_sym H)).
Qed.

Local Lemma filter_tag_app_eq (τ : positive) te (ts' : list (positive * trace)) :
  te.1 = τ →
  filter (λ t, t.1 = τ) (ts' ++ [te]) = filter (λ t, t.1 = τ) ts' ++ [te].
Proof.
  intros Hte. rewrite filter_app filter_cons_True; [|done].
  by rewrite filter_nil.
Qed.

Local Lemma not_is_lin_Call v : ¬ is_lin (Call v).
Proof. compute. tauto. Qed.

Local Lemma not_is_lin_Ret v : ¬ is_lin (Ret v).
Proof. compute. tauto. Qed.

Local Lemma is_lin_Lin v v' : is_lin (Lin v v').
Proof. compute. trivial. Qed.

Local Lemma filter_is_lin_app_nonlin (ts' : list (positive * trace)) te :
  ¬ is_lin te.2 →
  filter (is_lin ∘ snd) (ts' ++ [te]) = filter (is_lin ∘ snd) ts'.
Proof.
  intros Hne. rewrite filter_app filter_cons_False.
  - by rewrite filter_nil right_id_L.
  - exact Hne.
Qed.

Local Lemma filter_is_lin_app_lin (ts' : list (positive * trace)) te :
  is_lin te.2 →
  filter (is_lin ∘ snd) (ts' ++ [te]) = filter (is_lin ∘ snd) ts' ++ [te].
Proof.
  intros Hlin. rewrite filter_app filter_cons_True; [|exact Hlin].
  by rewrite filter_nil.
Qed.

(** One-step preservation of [per_tag_invariant] for tags NOT touched
  by the step. All AbsQ₀ steps modify at most one tag (the label's
  tag), leaving [cp0]/[in0]/[rv0] for every other tag unchanged. *)
Local Lemma per_tag_invariant_step_unrelated rme valid_value u0 u1 l ts' τ :
  absq0_step rme valid_value u0 l u1 →
  τ ≠ l.1 →
  per_tag_invariant u0 τ ts' →
  per_tag_invariant u1 τ (ts' ++ [trace_of_absq_label l]).
Proof.
  intros Hstep Hne HIH.
  assert ((trace_of_absq_label l).1 = l.1) as Hfst
    by apply trace_of_absq_label_fst.
  assert (filter (λ t, t.1 = τ) (ts' ++ [trace_of_absq_label l])
          = filter (λ t, t.1 = τ) ts') as Hfilt.
  { eapply filter_tag_app_ne; [rewrite Hfst; reflexivity|done]. }
  rewrite /per_tag_invariant Hfilt.
  (* Every step only inserts at l.1 ≠ τ in cp0/in0/rv0. *)
  assert (u1.(absq0_cp) !! τ = u0.(absq0_cp) !! τ
          ∧ u1.(absq0_in) !! τ = u0.(absq0_in) !! τ
          ∧ u1.(absq0_rv) !! τ = u0.(absq0_rv) !! τ) as (-> & Hin & Hrv).
  { inversion Hstep; subst; simpl in Hne |- *; split_and!;
      try done; by rewrite lookup_insert_ne. }
  rewrite /per_tag_invariant in HIH.
  destruct (absq0_cp u0 !! τ) as [c|]; [destruct c|]; auto.
  - destruct HIH as (d & ? & ?). exists d. by rewrite Hin.
  - destruct HIH as (d & ? & ?). exists d. by rewrite Hin.
  - destruct HIH as (d & ? & ?). exists d. by rewrite Hin.
  - destruct HIH as (v & ? & ?). exists v. by rewrite Hrv.
  - destruct HIH as (v & ? & ?). exists v. by rewrite Hrv.
Qed.

(** The main induction: both invariants hold after every reachable
  AbsQ₀ execution. Proved by reverse induction on [ls], using
  [absq0_steps_snoc_inv] to decompose. *)
Lemma absq0_steps_invariant rme valid_value ls u :
  absq0_steps rme valid_value absq0_init ls u →
  (∀ τ, per_tag_invariant u τ (trace_of_absq_labels ls)) ∧
  linearized_sound (M := queue_model rme valid_value)
    (filter (is_lin ∘ snd) (trace_of_absq_labels ls))
    [] u.(absq0_seq).*2.
Proof.
  revert u. induction ls as [|l ls IH] using rev_ind; intros u Hs.
  - (* Base: ls = [], u = absq0_init. *)
    inversion Hs; subst. rewrite /trace_of_absq_labels /=.
    split.
    + intros τ. rewrite /per_tag_invariant /absq0_init /= lookup_empty.
      by rewrite filter_nil.
    + rewrite filter_nil /absq0_init /=. apply linearized_sound_nil.
  - (* Inductive: ls ++ [l]. *)
    apply absq0_steps_snoc_inv in Hs as (u' & Hpre & Hstep).
    destruct (IH u' Hpre) as [IH_tag IH_lin].
    rewrite /trace_of_absq_labels map_app.
    inversion Hstep as
      [σ0 in0 rv0 cp0 k0 d Hfresh Hd_ub
      |σ0 in0 rv0 cp0 k0 d Hcp_A1 Hin_k Hd_ub_lin
      |σ0 in0 rv0 cp0 k0 Hcp_A
      |σ0 in0 rv0 cp0 k0 Hfresh
      |σ0 σtl in0 rv0 cp0 k0 k_e d Hcp_R1 Hσ_split
      |in0 rv0 cp0 k0 Hrme_guard Hcp_R1
      |σ0 in0 rv0 cp0 k0 v Hcp_R2 Hrv_k];
      subst l u' u; simpl in *.
    { (* CALL-ENQ: l = (k0, ACallEnq d). *)
      apply not_elem_of_dom in Hfresh as Hcp0_none.
      split.
      - intros τ. destruct (decide (τ = k0)) as [->|Hne]; last first.
        { eapply (per_tag_invariant_step_unrelated
                   rme valid_value _ _ (k0, ACallEnq d)); [|done|exact (IH_tag τ)].
          by apply absq0_step_call_enq. }
        specialize (IH_tag k0).
        rewrite /per_tag_invariant /= lookup_insert_eq.
        rewrite /per_tag_invariant Hcp0_none in IH_tag.
        exists d. split; [by rewrite lookup_insert_eq|].
        rewrite filter_tag_app_eq /=; last done.
        by rewrite IH_tag.
      - rewrite filter_is_lin_app_nonlin;
          [exact IH_lin|apply not_is_lin_Call]. }
    { (* LIN-ENQ: l = (k0, ALinEnq d). [Hin_k] and [Hd_ub_lin] come
         directly from [absq0_step_lin_enq]. The [σ ++ [(k_0, d)]]
         post-state matches [queue_model]'s [Push] case
         [s2 = s1 ++ [d]]. *)
      split.
      - intros τ. destruct (decide (τ = k0)) as [->|Hne]; last first.
        { eapply (per_tag_invariant_step_unrelated
                   rme valid_value _ _ (k0, ALinEnq d)); [|done|exact (IH_tag τ)].
          by apply absq0_step_lin_enq. }
        specialize (IH_tag k0).
        rewrite /per_tag_invariant /= lookup_insert_eq.
        rewrite /per_tag_invariant Hcp_A1 in IH_tag.
        destruct IH_tag as (d' & Hind' & Hfilt).
        rewrite Hin_k in Hind'. injection Hind' as <-.
        exists d. split; [done|].
        rewrite filter_tag_app_eq /=; last done.
        by rewrite Hfilt.
      - rewrite filter_is_lin_app_lin; [|apply is_lin_Lin].
        rewrite fmap_app /=.
        eapply linearized_sound_snoc; [exact IH_lin| |].
        + left. exists d. split; [exact Hd_ub_lin|done].
        + exists (Push d). done. }
    { (* RET-ENQ: l = (k0, ARetEnq). *)
      split.
      - intros τ. destruct (decide (τ = k0)) as [->|Hne]; last first.
        { eapply (per_tag_invariant_step_unrelated
                   rme valid_value _ _ (k0, ARetEnq)); [|done|exact (IH_tag τ)].
          by apply absq0_step_ret_enq. }
        specialize (IH_tag k0).
        rewrite /per_tag_invariant /= lookup_insert_eq.
        rewrite /per_tag_invariant Hcp_A in IH_tag.
        destruct IH_tag as (d & Hin & Hfilt).
        exists d. split; [done|].
        rewrite filter_tag_app_eq /=; last done.
        by rewrite Hfilt.
      - rewrite filter_is_lin_app_nonlin;
          [exact IH_lin|apply not_is_lin_Ret]. }
    { (* CALL-DEQ: l = (k0, ACallDeq). *)
      apply not_elem_of_dom in Hfresh as Hcp0_none.
      split.
      - intros τ. destruct (decide (τ = k0)) as [->|Hne]; last first.
        { eapply (per_tag_invariant_step_unrelated
                   rme valid_value _ _ (k0, ACallDeq)); [|done|exact (IH_tag τ)].
          by apply absq0_step_call_deq. }
        specialize (IH_tag k0).
        rewrite /per_tag_invariant /= lookup_insert_eq.
        rewrite /per_tag_invariant Hcp0_none in IH_tag.
        rewrite filter_tag_app_eq /=; last done.
        by rewrite IH_tag.
      - rewrite filter_is_lin_app_nonlin;
          [exact IH_lin|apply not_is_lin_Call]. }
    { (* LIN-DEQ1: l = (k0, ALinDeq (SOMEV d)), σ0 = (k_e, d) :: σtl
         (head=oldest). The pre-state [σ0.*2 = d :: σtl.*2] matches
         [queue_model]'s [Pop] non-empty case. *)
      split.
      - intros τ. destruct (decide (τ = k0)) as [->|Hne]; last first.
        { eapply (per_tag_invariant_step_unrelated
                   rme valid_value _ _ (k0, ALinDeq (SOMEV d))); [|done|exact (IH_tag τ)].
          by eapply (absq0_step_lin_deq1 _ _ _ _ _ _ _ _ _ d). }
        specialize (IH_tag k0).
        rewrite /per_tag_invariant /= lookup_insert_eq.
        rewrite /per_tag_invariant Hcp_R1 in IH_tag.
        exists (SOMEV d). split; [by rewrite lookup_insert_eq|].
        rewrite filter_tag_app_eq /=; last done.
        by rewrite IH_tag.
      - rewrite filter_is_lin_app_lin; [|apply is_lin_Lin].
        eapply (linearized_sound_snoc _ _ _ _ (encode_request Pop) (SOMEV d));
          [exact IH_lin| |].
        + right. done.
        + exists Pop. split; first done.
          rewrite Hσ_split fmap_cons /=. done. }
    { (* LIN-DEQ2: l = (k0, ALinDeq NONEV), σ0 = []. *)
      split.
      - intros τ. destruct (decide (τ = k0)) as [->|Hne]; last first.
        { eapply (per_tag_invariant_step_unrelated
                   rme valid_value _ _ (k0, ALinDeq NONEV)); [|done|exact (IH_tag τ)].
          by apply absq0_step_lin_deq2. }
        specialize (IH_tag k0).
        rewrite /per_tag_invariant /= lookup_insert_eq.
        rewrite /per_tag_invariant Hcp_R1 in IH_tag.
        exists NONEV. split; [by rewrite lookup_insert_eq|].
        rewrite filter_tag_app_eq /=; last done.
        by rewrite IH_tag.
      - rewrite filter_is_lin_app_lin; [|apply is_lin_Lin].
        eapply (linearized_sound_snoc _ _ _ _ (encode_request Pop) NONEV);
          [exact IH_lin| |].
        + right. done.
        + simpl. exists Pop. split; first done.
          destruct rme; [done|exact Hrme_guard]. }
    { (* RET-DEQ: l = (k0, ARetDeq v). *)
      split.
      - intros τ. destruct (decide (τ = k0)) as [->|Hne]; last first.
        { eapply (per_tag_invariant_step_unrelated
                   rme valid_value _ _ (k0, ARetDeq v)); [|done|exact (IH_tag τ)].
          by apply absq0_step_ret_deq. }
        specialize (IH_tag k0).
        rewrite /per_tag_invariant /= lookup_insert_eq.
        rewrite /per_tag_invariant Hcp_R2 in IH_tag.
        destruct IH_tag as (v' & Hrv' & Hfilt).
        rewrite Hrv_k in Hrv'. injection Hrv' as <-.
        exists v. split; [done|].
        rewrite filter_tag_app_eq /=; last done.
        by rewrite Hfilt.
      - rewrite filter_is_lin_app_nonlin;
          [exact IH_lin|apply not_is_lin_Ret]. }
Qed.

(** Key helper: any reachable AbsQ₀ execution induces a trace
  witnessing [trace_linearizable]. *)
Lemma absq0_steps_trace_helper rme valid_value ls u :
  absq0_steps rme valid_value absq0_init ls u →
  per_tag_linearized (trace_of_absq_labels ls) ∧
  linearized_sound (M := queue_model rme valid_value)
    (filter (is_lin ∘ snd) (trace_of_absq_labels ls))
    [] u.(absq0_seq).*2.
Proof.
  intros Hs. destruct (absq0_steps_invariant rme _ _ _ Hs) as [Htag Hlin].
  split; [|done]. by eapply per_tag_invariant_to_per_tag_linearized.
Qed.

(** [call_valid] is downward-closed under filtering. *)
Local Lemma call_valid_filter `{M : model} (P : positive * trace → Prop)
    `{!∀ x, Decision (P x)} ts :
  call_valid ts → call_valid (filter P ts).
Proof.
  rewrite /call_valid !Forall_forall. intros Hcv x Hx.
  apply list_elem_of_filter in Hx as [_ Hin]. by apply Hcv.
Qed.

(** Every [Call] event of a reachable AbsQ₀ execution carries a valid
  request: [ACallEnq d] steps record [valid_value d] (left disjunct of
  [valid_bag_request]) and [ACallDeq] steps produce [encode_request Pop]
  (right disjunct). Hence the induced trace is [call_valid] — the only
  ingredient of [trace_linearizable] that the old library-level proof
  obtained from [adv_steps]. *)
Lemma absq0_steps_call_valid rme valid_value ls u :
  absq0_steps rme valid_value absq0_init ls u →
  call_valid (M := queue_model rme valid_value) (trace_of_absq_labels ls).
Proof.
  revert u. induction ls as [|l ls IH] using rev_ind; intros u Hs.
  - constructor.
  - apply absq0_steps_snoc_inv in Hs as (u' & Hpre & Hstep).
    rewrite /trace_of_absq_labels map_app /call_valid Forall_app.
    split; [by eapply IH|]. rewrite Forall_singleton.
    inversion Hstep; subst; simpl; try done.
    + (* CALL-ENQ: valid_value d *)
      rewrite /valid_request /= /valid_bag_request. left. eauto.
    + (* CALL-DEQ *)
      rewrite /valid_request /= /valid_bag_request. by right.
Qed.

(** The trace-level refinement hypothesis: the Call/Ret trace [ts] is the
  projection of some reachable AbsQ₀ execution (i.e., [ts] refines AbsQ₀
  at the C∪R level). This is the refine analogue of [metaconfig]'s
  [I_metaconfig] / [aspect]'s [I_queue] invariant on [ts]. Under AbsQ₀'s
  strengthened [absq0_step_lin_enq] rule, reachable executions
  automatically have [ALinEnq d] events with [d = in0(τ) ≠ empty], so
  no separate faithfulness condition is needed. *)
Definition trace_refines_absq0 (rme : response_mayempty)
  (valid_value : val → Prop) (ts : list (positive * trace)) : Prop :=
  ∃ u ls,
    absq0_steps rme valid_value absq0_init ls u ∧
    ts = filter (not ∘ is_lin ∘ snd) (trace_of_absq_labels ls).

(** Main result: a Call/Ret trace refining AbsQ₀ at the C∪R projection
  level is [trace_linearizable] in the [linear.v] sense. *)
Theorem refines_absq0_trace_linearizable rme valid_value ts :
  trace_refines_absq0 rme valid_value ts →
  trace_linearizable (M := queue_model rme valid_value) ts.
Proof.
  intros (u & ls & Hls & Hts_eq). split.
  - rewrite Hts_eq. apply call_valid_filter. by eapply absq0_steps_call_valid.
  - exists (trace_of_absq_labels ls).
    destruct (absq0_steps_trace_helper rme _ _ _ Hls) as [Hptl Hls_sound].
    split_and!; [exact Hts_eq | exact Hptl | by eexists].
Qed.

(* ========================================== *)
(* Chaining through AbsQ: [trace_refines_absq → trace_linearizable]. *)

(** Picks out the Call/Ret labels (= C ∪ R) among [absq_action]s; a
  strict subset of [is_observable] (which also keeps [ALinDeq]). *)
Definition is_call_or_ret_action (x : positive * absq_action) : Prop :=
  match x.2 with
  | ACallEnq _ | ACallDeq | ARetEnq | ARetDeq _ => True
  | _ => False
  end.

Global Instance is_call_or_ret_action_dec x : Decision (is_call_or_ret_action x).
Proof. rewrite /is_call_or_ret_action. destruct x.2; apply _. Defined.

Lemma is_call_or_ret_action_observable x :
  is_call_or_ret_action x → is_observable x.
Proof. rewrite /is_call_or_ret_action /is_observable. by destruct x.2. Qed.

(** The [Lin]-free projection of [trace_of_absq_labels ls] factors
  through the [Call/Ret] filter on the underlying AbsQ₀ labels. *)
Lemma filter_lin_trace_of_absq_labels ls :
  filter (not ∘ is_lin ∘ snd) (trace_of_absq_labels ls)
  = trace_of_absq_labels (filter is_call_or_ret_action ls).
Proof.
  induction ls as [|l ls IH].
  { by rewrite /trace_of_absq_labels !filter_nil. }
  rewrite /trace_of_absq_labels map_cons.
  destruct l as [τ []].
  - rewrite filter_cons_True; last by apply not_is_lin_Call.
    rewrite filter_cons_True; last done.
    simpl. by f_equal.
  - rewrite filter_cons_True; last by apply not_is_lin_Call.
    rewrite filter_cons_True; last done.
    simpl. by f_equal.
  - rewrite filter_cons_True; last by apply not_is_lin_Ret.
    rewrite filter_cons_True; last done.
    simpl. by f_equal.
  - rewrite filter_cons_True; last by apply not_is_lin_Ret.
    rewrite filter_cons_True; last done.
    simpl. by f_equal.
  - rewrite filter_cons_False;
      last (intros HH; apply HH; apply is_lin_Lin).
    rewrite filter_cons_False; last by intros []. exact IH.
  - rewrite filter_cons_False;
      last (intros HH; apply HH; apply is_lin_Lin).
    rewrite filter_cons_False; last by intros []. exact IH.
Qed.

(** The [is_observable] projection (from the paper / [absq_refines_absq0])
  retains enough information to determine the [Call/Ret] projection. *)
Lemma filter_call_or_ret_via_observable (ls : list (positive * absq_action)) :
  filter is_call_or_ret_action ls
  = filter is_call_or_ret_action (filter is_observable ls).
Proof.
  symmetry. apply list_filter_filter_l.
  apply is_call_or_ret_action_observable.
Qed.

(** The trace-level refinement hypothesis for AbsQ. Same shape as
  [trace_refines_absq0] but with AbsQ traces. *)
Definition trace_refines_absq (rme : response_mayempty)
  (valid_value : val → Prop) (ts : list (positive * trace)) : Prop :=
  ∃ s ls,
    absq_steps rme valid_value absq_init ls s ∧
    ts = filter (not ∘ is_lin ∘ snd) (trace_of_absq_labels ls).

(** Chained result: a Call/Ret trace refining AbsQ at the C∪R projection
  level is [trace_linearizable]. Combines with [absq_refines_absq0] to
  factor through AbsQ₀. *)
Theorem refines_absq_trace_linearizable rme valid_value ts :
  trace_refines_absq rme valid_value ts →
  trace_linearizable (M := queue_model rme valid_value) ts.
Proof.
  intros (s & ls_absq & Habsq & Hts_eq).
  apply refines_absq0_trace_linearizable.
  (* Run [absq_refines_absq0] on the AbsQ trace to get an AbsQ₀ trace
     with matching [is_observable] projection. *)
  destruct (absq_refines_absq0 rme valid_value _ _ Habsq)
    as (ls_absq0 & u & Habsq0 & Hproj).
  exists u, ls_absq0. split; [exact Habsq0|].
  (* Equate Call/Ret projections by factoring through [is_observable]. *)
  rewrite Hts_eq !filter_lin_trace_of_absq_labels. f_equal.
  rewrite (filter_call_or_ret_via_observable ls_absq).
  rewrite (filter_call_or_ret_via_observable ls_absq0).
  rewrite /project_labels in Hproj. by rewrite Hproj.
Qed.
