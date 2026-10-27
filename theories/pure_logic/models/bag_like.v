From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic Require Export linear.
From iris.heap_lang Require Export notation.

(* Shared interface for bag-like containers. *)

Definition Push : nat := 0.
Definition Pop : nat := 1.

Inductive response :=
  | IsEmpty : response
  | NonEmpty : val → response.

Inductive response_mayempty := MayEmpty | NeverEmpty.

Definition encode_response r : val :=
  match r with
  | IsEmpty => NONEV
  | NonEmpty v => SOMEV v
  end.

Global Instance encode_response_inj : Inj (=) (=) encode_response.
Proof.
  intros r1 r2 Henc.
  destruct r1, r2; simpl in Henc.
  - done.
  - discriminate Henc.
  - discriminate Henc.
  - by injection Henc as ->.
Qed.

Definition bag_model (rme : response_mayempty) (valid_value: val → Prop) : model := {|
  S := gmultiset val;
  s_init := ∅;
  valid_requests := [valid_value; λ v, v=#()];
  request_responses := [
    λ s1 v1 s2 v2, s2 = {[+ v1 +]} ⊎ s1 ∧ v2 = #();
    λ s1 v1 s2 v2, (if rme then s1 = ∅ ∧ s2 = ∅ ∧ v2 = encode_response IsEmpty else False)
                  ∨ ∃ v, v ∈ s1 ∧ s2 = s1∖{[+ v +]} ∧ v2 = encode_response (NonEmpty v)
  ];
|}.

Definition queue_model (rme : response_mayempty) (valid_value: val → Prop) : model := {|
  S := list val;
  s_init := [];
  valid_requests := [valid_value; λ v, v=#()];
  request_responses := [
    λ s1 v1 s2 v2, s2 = s1 ++ [v1] ∧ v2 = #();
    λ s1 v1 s2 v2,
      match s1 with
      | [] => (if rme then s2 = [] ∧ v2 = encode_response IsEmpty else False)
      | v::s1' => s2 = s1' ∧ v2 = encode_response (NonEmpty v)
      end
  ];
|}.

Definition stack_model (rme : response_mayempty) (valid_value: val → Prop) : model := {|
  S := list val;
  s_init := [];
  valid_requests := [valid_value; λ v, v=#()];
  request_responses := [
    λ s1 v1 s2 v2, s2 = v1::s1 ∧ v2 = #();
    λ s1 v1 s2 v2,
      match s1 with
      | [] => (if rme then s2 = [] ∧ v2 = encode_response IsEmpty else False)
      | v::s1' => s2 = s1' ∧ v2 = encode_response (NonEmpty v)
      end
  ];
|}.

(* LLM-generated: the requests are decidable if the valid values are *)
Local Lemma bag_like_valid_requests_decide (valid_value : val → Prop)
    `{!∀ v, Decision (valid_value v)} n v :
  default default_vr ([valid_value; λ v, v = #()] !! n) v ∨
  ¬ default default_vr ([valid_value; λ v, v = #()] !! n) v.
Proof.
  destruct n as [|[|n]]; simpl.
  - destruct (decide (valid_value v)); auto.
  - destruct (decide (v = #())); auto.
  - right. intros [].
Qed.

Global Instance bag_model_decidable rme valid_value `{!∀ v, Decision (valid_value v)} :
  ModelDecidable (bag_model rme valid_value).
Proof. intros n v. by apply bag_like_valid_requests_decide. Qed.

Global Instance queue_model_decidable rme valid_value `{!∀ v, Decision (valid_value v)} :
  ModelDecidable (queue_model rme valid_value).
Proof. intros n v. by apply bag_like_valid_requests_decide. Qed.

Global Instance stack_model_decidable rme valid_value `{!∀ v, Decision (valid_value v)} :
  ModelDecidable (stack_model rme valid_value).
Proof. intros n v. by apply bag_like_valid_requests_decide. Qed.

Definition is_call_push t := ∃ v, t = Call Push v.
Definition is_call_pop t := t = Call Pop #().
Definition is_ret_push t := t = Ret #().
Definition is_ret_pop t := ∃ r, t = Ret (encode_response r).
Definition is_ret_pop_val t := ∃ v, t = Ret (encode_response (NonEmpty v)).
Definition is_ret_pop_emp t := t = Ret (encode_response IsEmpty).

Definition per_tag_wellformed_bag (rme : response_mayempty) (valid_value: val → Prop) (ts : list (positive*trace)) :=
  ∀ τ, let ts_τ := (filter (λ x, x.1 = τ)) ts in
      (∃ v, valid_value v ∧ ts_τ `prefix_of` [(τ,Call Push v); (τ,Ret #())])
    ∨ (∃ r, (if rme then True else r ≠ IsEmpty) ∧ ts_τ `prefix_of` [(τ,Call 1 #()); (τ,Ret (encode_response r))]).

Global Instance is_call_push_decide t : Decision (is_call_push t).
Proof.
  destruct t as [r| |]; [|by right; intros [??]..].
  destruct r; try by right; intros [??].
  left. eexists _. done.
Defined.

Global Instance is_call_pop_decide t : Decision (is_call_pop t).
Proof. solve_decision. Defined.

Global Instance is_ret_push_decide t : Decision (is_ret_push t).
Proof. solve_decision. Defined.

Global Instance is_ret_pop_decide t : Decision (is_ret_pop t).
Proof.
  destruct t as [| |r]; [by right; intros [??]..|].
  destruct r; try by right; intros [res ?]; destruct res.
  - rename select val into r.
    destruct r; try by right; intros [res ?]; destruct res.
    rename select base_lit into l.
    destruct l; try by right; intros [r ?]; destruct r.
    left. exists IsEmpty. done.
  - left. eexists (NonEmpty _). done.
Defined.

Global Instance is_ret_pop_val_decide t : Decision (is_ret_pop_val t).
Proof.
  destruct t as [| |r]; [by right; intros [??]..|].
  destruct r; try by right; intros [??].
  left. eexists _. done.
Defined.

Global Instance is_ret_pop_emp_decide t : Decision (is_ret_pop_emp t).
Proof. solve_decision. Defined.

Section relations.
  Context (ts : list (positive*trace)).

  (* the set of push operations of a trace *)
  Definition push_of_trace : list positive :=
    (filter (is_call_push ∘ snd) ts).*1.

  Definition pop_of_trace : list positive :=
    (filter (is_call_pop ∘ snd) ts).*1.

  (* the set of pop operations that returns NonEmpty of a trace *)
  Definition pop_val_of_trace : list positive :=
    (filter (is_ret_pop_val ∘ snd) ts).*1.

  Definition pop_emp_of_trace : list positive :=
    (filter (is_ret_pop_emp ∘ snd) ts).*1.

  Lemma push_or_pop_of_trace rme valid_value τ :
    per_tag_wellformed_bag rme valid_value ts →
    τ ∈ events_of_trace ts →
    τ ∈ push_of_trace ∨ τ ∈ pop_of_trace.
  Proof.
    intros Hper_tag_wf ([τ' v₀] & Heq & Hin)%elem_of_list_to_set%list_elem_of_fmap_1.
    simpl in Heq. subst τ'.
    assert (Hin': (τ,v₀) ∈ filter (λ x, x.1 = τ) ts).
    { apply list_elem_of_filter. split; done. }
    destruct (filter (λ x, x.1 = τ) ts) as [|x xs] eqn:Heq; first set_solver.
    clear v₀ Hin Hin'.
    destruct (Hper_tag_wf τ) as [(v & _ & Hprefix) | (r & _ & Hprefix)];
      rewrite Heq in Hprefix;
      apply prefix_cons_inv_1 in Hprefix; subst x.
    - left.
      assert (Hin: (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts).
      { rewrite Heq. set_solver. }
      apply list_elem_of_filter_1 in Hin.
      eapply (list_elem_of_fmap_2 fst _ (τ,_)).
      apply list_elem_of_filter_2; last exact Hin.
      compute_done.
    - right.
      assert (Hin: (τ, Call Pop #()) ∈ filter (λ x, x.1 = τ) ts).
      { rewrite Heq. set_solver. }
      apply list_elem_of_filter_1 in Hin.
      eapply (list_elem_of_fmap_2 fst _ (τ,_)).
      apply list_elem_of_filter_2; last exact Hin.
      compute_done.
  Qed.

  Lemma per_tag_wellformed_bag_wellformed rme valid_value :
    per_tag_wellformed_bag rme valid_value ts → per_tag_wellformed ts.
  Proof.
    intros H τ.
    destruct (H τ) as [(v & _ & Hprefix) | (r & _ & Hprefix)]; by eexists _,_,_.
  Qed.

  (* Reusable Lemma generated by LLM. *)
  (**********************************************************)
  (* Begin LLM-generated code. *)
  (* tool: Claude Code 2.1.91
      model: Claude Opus 4.6 (claude-opus-4-6)
      parameters:
        effort = high
        context window = 1000000
        max output tokens = 128000 *)
  Lemma push_tag_in_trace τ :
    τ ∈ push_of_trace → ∃ v, (τ, Call Push v) ∈ ts.
  Proof.
    rewrite /push_of_trace.
    intros Hin.
    apply list_elem_of_fmap_1 in Hin as ([τ' ev] & Heq & Hin).
    simpl in Heq. subst τ'.
    apply list_elem_of_filter in Hin as [Hpush Hin].
    simpl in Hpush. destruct Hpush as [v ->].
    exists v. exact Hin.
  Qed.

  Lemma pop_tag_in_trace τ :
    τ ∈ pop_of_trace →
    (τ, Call 1 #()) ∈ ts.
  Proof.
    rewrite /pop_of_trace.
    intros Hin.
    apply list_elem_of_fmap_1 in Hin as ([τ' ev] & Heq & Hin).
    simpl in Heq. subst τ'.
    apply list_elem_of_filter in Hin as [Hpop Hin].
    simpl in Hpop. rewrite Hpop in Hin. exact Hin.
  Qed.

  Lemma push_xor_pop_of_trace rme valid_value τ :
    per_tag_wellformed_bag rme valid_value ts →
    τ ∈ push_of_trace → τ ∈ pop_of_trace →
    False.
  Proof.
    intros Hwf Hpush Hpop.
    apply push_tag_in_trace in Hpush as [v Hpush].
    apply pop_tag_in_trace in Hpop.
    assert (Hin_push : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts).
    { apply list_elem_of_filter. done. }
    assert (Hin_pop : (τ, Call 1 #()) ∈ filter (λ x, x.1 = τ) ts).
    { apply list_elem_of_filter. done. }
    destruct (Hwf τ) as [(w & _ & Hpfx)|(r & _ & Hpfx)].
    - assert (Hin_pop' := Hin_pop).
      eapply elem_of_prefix in Hin_pop'; last exact Hpfx.
      apply elem_of_cons in Hin_pop' as [Habs|Hin_pop'].
      + injection Habs as Habs. discriminate.
      + apply elem_of_cons in Hin_pop' as [Habs|Hin_pop']; last by set_solver.
        discriminate.
    - assert (Hin_push' := Hin_push).
      eapply elem_of_prefix in Hin_push'; last exact Hpfx.
      apply elem_of_cons in Hin_push' as [Habs|Hin_push'].
      + injection Habs as Habs. discriminate.
      + apply elem_of_cons in Hin_push' as [Habs|Hin_push']; last by set_solver.
        discriminate.
  Qed.
  (* End LLM-generated code. *)
  (**********************************************************)
End relations.

Lemma per_tag_wellformed_bag_nil rme valid_value :
  per_tag_wellformed_bag rme valid_value [].
Proof.
  intros τ. right. exists (NonEmpty #()).
  split.
  - destruct rme; [done|discriminate].
  - rewrite filter_nil. apply prefix_nil.
Qed.

Lemma per_tag_wellformed_bag_snoc_call_push rme valid_value ts τ v :
  per_tag_wellformed_bag rme valid_value ts → τ ∉ ts.*1 → valid_value v →
  per_tag_wellformed_bag rme valid_value (ts++[(τ,Call Push v)]).
Proof.
  intros Hwf Hfresh Hvv τ' ts_τ'. subst ts_τ'.
  destruct (decide (τ' = τ)) as [-> | Hne].
  - left. exists v.
    split; first done.
    rewrite filter_app (filter_False_nil _ ts); last first.
    { apply Forall_forall. intros [τ' ?] Hin%(list_elem_of_fmap_2 fst) <-.
      done. }
    rewrite left_id_L filter_cons_True // filter_nil.
    exists [(τ, Ret #())]. reflexivity.
  - destruct (Hwf τ') as [[v' Hprefix] | (r & Hr_ne & Hprefix)].
    + left. exists v'.
      rewrite filter_app filter_cons_False // filter_nil right_id_L.
      apply Hprefix.
    + right. exists r. split; first exact Hr_ne.
      rewrite filter_app filter_cons_False // filter_nil right_id_L.
      apply Hprefix.
Qed.

Lemma per_tag_wellformed_bag_snoc_call_pop rme valid_value ts τ :
  per_tag_wellformed_bag rme valid_value ts → τ ∉ ts.*1 →
  per_tag_wellformed_bag rme valid_value (ts++[(τ,Call Pop #())]).
Proof.
  intros Hwf Hfresh τ' ts_τ'. subst ts_τ'.
  destruct (decide (τ' = τ)) as [-> | Hne].
  - right. exists (NonEmpty #()).
    split; first by (destruct rme; [done|discriminate]).
    rewrite filter_app (filter_False_nil _ ts); last first.
    { apply Forall_forall. intros [τ' ?] Hin%(list_elem_of_fmap_2 fst) <-.
      done. }
    rewrite left_id_L filter_cons_True // filter_nil.
    exists [(τ, Ret (encode_response (NonEmpty #())))]. reflexivity.
  - destruct (Hwf τ') as [[v' Hprefix] | (r & Hr_ne & Hprefix)].
    + left. exists v'.
      rewrite filter_app filter_cons_False // filter_nil right_id_L.
      apply Hprefix.
    + right. exists r. split; first exact Hr_ne.
      rewrite filter_app filter_cons_False // filter_nil right_id_L.
      apply Hprefix.
Qed.

Lemma per_tag_wellformed_bag_snoc_ret_push rme valid_value ts τ v :
  per_tag_wellformed_bag rme valid_value ts →
  filter (λ x, x.1 = τ) ts = [(τ,Call Push v)] →
  valid_value v →
  per_tag_wellformed_bag rme valid_value (ts++[(τ,Ret #())]).
Proof.
  intros Hwf Hfilter Hvv τ' ts_τ'. subst ts_τ'.
  destruct (decide (τ' = τ)) as [-> | Hne].
  - left. exists v.
    split; first done.
    rewrite filter_app Hfilter.
    by rewrite filter_cons_True //.
  - destruct (Hwf τ') as [[v' Hprefix] | (r & Hr_ne & Hprefix)].
    + left. exists v'.
      rewrite filter_app filter_cons_False // filter_nil right_id_L.
      apply Hprefix.
    + right. exists r. split; first exact Hr_ne.
      rewrite filter_app filter_cons_False // filter_nil right_id_L.
      apply Hprefix.
Qed.

Lemma per_tag_wellformed_bag_snoc_ret_pop rme valid_value ts τ r :
  per_tag_wellformed_bag rme valid_value ts →
  filter (λ x, x.1 = τ) ts = [(τ,Call Pop #())] →
  (if rme then True else r ≠ IsEmpty) →
  per_tag_wellformed_bag rme valid_value (ts++[(τ,Ret (encode_response r))]).
Proof.
  intros Hwf Hfilter Hr_ne τ' ts_τ'. subst ts_τ'.
  destruct (decide (τ' = τ)) as [-> | Hne].
  - right. exists r. split; first exact Hr_ne.
    rewrite filter_app Hfilter.
    by rewrite filter_cons_True //.
  - destruct (Hwf τ') as [[v' Hprefix] | (r' & Hr'_ne & Hprefix)].
    + left. exists v'.
      rewrite filter_app filter_cons_False // filter_nil right_id_L.
      apply Hprefix.
    + right. exists r'. split; first exact Hr'_ne.
      rewrite filter_app filter_cons_False // filter_nil right_id_L.
      apply Hprefix.
Qed.

(**********************************************************)
(* Begin LLM-generated code. *)
(* tool: Claude Code 2.1.91
    model: Claude Opus 4.6 (claude-opus-4-6)
    parameters:
      effort = high
      context window = 1000000
      max output tokens = 128000 *)
Lemma per_tag_wellformed_bag_valid_push_value rme valid_value ts τ v :
  per_tag_wellformed_bag rme valid_value ts →
  (τ, Call Push v) ∈ ts →
  valid_value v.
Proof.
  intros Hwf Hin.
  assert (Hin_f : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts).
  { apply list_elem_of_filter. done. }
  destruct (Hwf τ) as [(v' & Hv'_valid & Hpfx)|(r' & _ & Hpfx)].
  - eapply elem_of_prefix in Hin_f; last exact Hpfx.
    apply elem_of_cons in Hin_f as [Heq|Hin_cons].
    + assert (v = v') as ->; last done.
      injection Heq as Heq. by simplify_eq.
    + apply elem_of_cons in Hin_cons as [Heq|Hempty]; last set_solver.
      discriminate.
  - exfalso.
    eapply elem_of_prefix in Hin_f; last exact Hpfx.
    apply elem_of_cons in Hin_f as [Heq|Hin_cons].
    + injection Heq as Heq. discriminate.
    + apply elem_of_cons in Hin_cons as [Heq|Hempty]; last set_solver.
      injection Heq as Heq. discriminate.
Qed.

Lemma trace_linearizable_per_tag_wellformed_bag rme valid_value ts :
  trace_linearizable (M:=(bag_model rme valid_value)) ts → per_tag_wellformed_bag rme valid_value ts.
Proof.
  intros (Hcv & ts' & Hfilt & Hptl & s_end & Hls) τ.
  destruct (Hptl τ) as (n & v & v' & Hpfx).
  (* The filter on ts is a prefix of [(τ,Call n v); (τ,Ret v')] *)
  assert (Hpfx_ts : filter (λ x, x.1 = τ) ts `prefix_of` [(τ,Call n v); (τ,Ret v')]).
  { rewrite Hfilt list_filter_comm.
    apply (prefix_filter (not ∘ is_lin ∘ snd)) in Hpfx.
    rewrite filter_cons_True in Hpfx; [|compute_done].
    rewrite filter_cons_False in Hpfx; [|compute_done].
    rewrite filter_cons_True in Hpfx; [|compute_done].
    rewrite filter_nil in Hpfx. done. }
  destruct (filter (λ x, x.1 = τ) ts) as [|[p1 t1] rest'] eqn:Heq.
  { right. exists (NonEmpty #()).
    split; first by (destruct rme; [done|discriminate]).
    apply prefix_nil. }
  (* First element is (τ, Call v) *)
  assert (H1 := prefix_cons_inv_1 _ _ _ _ Hpfx_ts).
  injection H1 as -> ->.
  (* v is a valid bag request *)
  rewrite /call_valid Forall_forall in Hcv.
  assert (Hin : (τ, Call n v) ∈ ts).
  { assert (H : (τ, Call n v) ∈ filter (λ x, x.1 = τ) ts)
      by (rewrite Heq; set_solver).
    by apply list_elem_of_filter in H as [_ ?]. }
  (* Refold [v] as [encode_request r] for some [r ∈ {Push w, Pop}].
     The [valid_value w] precondition is propagated into the [left]
     conclusion below. *)
  specialize (Hcv _ Hin).
  destruct n as [|[|n]]; simpl in Hcv; last contradict Hcv.
  + (* n = Push. *)
    destruct rest' as [|[p2 t2] rest].
    { left. exists v. split; first exact Hcv.
      apply prefix_cons, prefix_nil. }
    (* Second element is (τ, Ret v') *)
    assert (Hpfx2 := prefix_cons_inv_2 _ _ _ _ Hpfx_ts).
    assert (H2 := prefix_cons_inv_1 _ _ _ _ Hpfx2).
    injection H2 as -> ->.
    assert (Hnil : rest = []).
    { apply prefix_nil_inv, (prefix_cons_inv_2 _ _ _ _ Hpfx2). }
    subst rest.
    (* Show that the filter on ts' is the full 3-element list *)
    assert (Hret_in : (τ, Ret v') ∈ filter (λ t, t.1 = τ) ts').
    { apply list_elem_of_filter. split; first done.
      assert (H : (τ, Ret v') ∈ ts).
      { assert (H' : (τ, Ret v') ∈ filter (λ x, x.1 = τ) ts)
          by (rewrite Heq; set_solver).
        by apply list_elem_of_filter in H' as [_ ?]. }
      rewrite Hfilt in H. by apply list_elem_of_filter in H as [_ ?]. }
    assert (Hfilt_eq : filter (λ t, t.1 = τ) ts' =
      [(τ, Call Push v); (τ, Lin Push v v'); (τ, Ret v')]).
    { apply prefix_length_eq; first exact Hpfx. simpl.
      destruct (list_elem_of_lookup_1 _ _ Hret_in) as [i Hi].
      pose proof (prefix_lookup_Some _ _ _ _ Hi Hpfx) as Hi'.
      destruct i as [|[|[|i]]]; simpl in Hi'; try by simplify_eq.
      apply lookup_lt_Some in Hi. lia. }
    (* Extract Lin event from filter *)
    assert (Hlin_in : (τ, Lin Push v v') ∈ filter (is_lin ∘ snd) ts').
    { apply list_elem_of_filter. split; first done.
      assert (H : (τ, Lin Push v v') ∈ filter (λ t, t.1 = τ) ts')
        by (rewrite Hfilt_eq; set_solver).
      by apply list_elem_of_filter in H as [_ ?]. }
    (* Extract request_response from [rtcL model_step] *)
    destruct (list_elem_of_split _ _ Hlin_in) as (l1 & l2 & Heq_lin).
    rewrite Heq_lin in Hls.
    apply rtcL_app_inv in Hls as (s_mid & _ & Hls_tail).
    apply rtcL_cons_inv in Hls_tail as (s_next & [_ Hrr]%model_step_inv & _).
    simpl in Hrr. destruct Hrr as [-> ->].
    left. exists v. split; first exact Hcv. reflexivity.
  + (* n = Pop. *)
    subst v.
    destruct rest' as [|[p2 t2] rest].
    { right. exists (NonEmpty #()).
      split; first by (destruct rme; [done|discriminate]).
      apply prefix_cons, prefix_nil. }
    assert (Hpfx2 := prefix_cons_inv_2 _ _ _ _ Hpfx_ts).
    assert (H2 := prefix_cons_inv_1 _ _ _ _ Hpfx2).
    injection H2 as -> ->.
    assert (Hnil : rest = []).
    { apply prefix_nil_inv, (prefix_cons_inv_2 _ _ _ _ Hpfx2). }
    subst rest.
    assert (Hret_in : (τ, Ret v') ∈ filter (λ t, t.1 = τ) ts').
    { apply list_elem_of_filter. split; first done.
      assert (H : (τ, Ret v') ∈ ts).
      { assert (H' : (τ, Ret v') ∈ filter (λ x, x.1 = τ) ts)
          by (rewrite Heq; set_solver).
        by apply list_elem_of_filter in H' as [_ ?]. }
      rewrite Hfilt in H. by apply list_elem_of_filter in H as [_ ?]. }
    assert (Hfilt_eq : filter (λ t, t.1 = τ) ts' =
      [(τ, Call Pop #()); (τ, Lin Pop #() v'); (τ, Ret v')]).
    { apply prefix_length_eq; first exact Hpfx. simpl.
      destruct (list_elem_of_lookup_1 _ _ Hret_in) as [i Hi].
      pose proof (prefix_lookup_Some _ _ _ _ Hi Hpfx) as Hi'.
      destruct i as [|[|[|i]]]; simpl in Hi'; try by simplify_eq.
      apply lookup_lt_Some in Hi. lia. }
    assert (Hlin_in : (τ, Lin Pop #() v') ∈ filter (is_lin ∘ snd) ts').
    { apply list_elem_of_filter. split; first done.
      assert (H : (τ, Lin Pop #() v') ∈ filter (λ t, t.1 = τ) ts')
        by (rewrite Hfilt_eq; set_solver).
      by apply list_elem_of_filter in H as [_ ?]. }
    destruct (list_elem_of_split _ _ Hlin_in) as (l1 & l2 & Heq_lin).
    rewrite Heq_lin in Hls.
    apply rtcL_app_inv in Hls as (s_mid & _ & Hls_tail).
    apply rtcL_cons_inv in Hls_tail as (s_next & [_ Hrr]%model_step_inv & _).
    simpl in Hrr.
    destruct Hrr as [Hempty | (w & _ & _ & ->)].
    * destruct rme; [|done]. destruct Hempty as (_ & _ & ->).
      right. exists IsEmpty. split; [done|reflexivity].
    * right. exists (NonEmpty w).
      split; first by (destruct rme; [done|discriminate]).
      reflexivity.
Qed.
(* End LLM-generated code. *)
(**********************************************************)
