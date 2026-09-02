From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Export bag.base.

Definition order_correct_matched ts (m : list (positive*positive)) :=
  ∀ e1 e2 d1 d2, (pre_of_trace ts) e1 e2 → (e1,d1) ∈ m → (e2, d2) ∈ m →
                ¬ (pre_of_trace ts) d2 d1.

Definition order_correct_unmatched ts (m : list (positive*positive)) :=
  ∀ e1 e2, (pre_of_trace ts) e1 e2 → e1 ∈ push_of_trace ts → e2 ∈ m.*1 → e1 ∈ m.*1.

Definition I_queue_pre ts m :=
    valid_match ts m
  ∧ per_tag_pop_empty_sound ts m
  ∧ order_correct_matched ts m
  ∧ order_correct_unmatched ts m.

Definition I_queue ts := ∃ m, I_queue_pre ts m.

Lemma order_correct_matched_nil : order_correct_matched [] [].
Proof. intros ???? _ HFalse. set_solver. Qed.

Lemma order_correct_unmatched_nil : order_correct_unmatched [] [].
Proof. intros ???? HFalse. set_solver. Qed.

(**********************************************************)
(* Begin LLM-generated code. *)
(* claude-opus-4-7[1m], max effort Claude Code 2.1.111 *)

(*** Local helper lemmas. ***)

(* If τ has no Ret event in ts, then pre_of_trace ts τ _ is False
   (the ret_of_tag lookup fails). *)
Local Lemma pre_of_trace_no_ret_l (ts0 : list (positive * trace)) τ1 τ2 :
  τ1 ∉ (filter (is_ret ∘ snd) ts0).*1 →
  ¬ pre_of_trace ts0 τ1 τ2.
Proof.
  intros Hno_ret Hpre.
  rewrite /pre_of_trace in Hpre.
  destruct (ret_of_tag ts0 τ1) as [[i [τ' ev]]|] eqn:Hret;
    simpl in Hpre; [|done].
  apply Hno_ret.
  rewrite /ret_of_tag in Hret.
  apply list_find_Some in Hret as (Hlookup & [Htag His_ret] & _).
  simpl in Htag. subst τ'.
  apply (list_elem_of_fmap_2 fst _ (τ1, ev)).
  apply list_elem_of_filter_2; [exact His_ret|].
  by apply list_elem_of_lookup_2 in Hlookup.
Qed.

(* push_of_trace under append: 3 cases (Call Push, Call Pop, Ret). *)
Local Lemma push_of_trace_app_call_push (ts0 : list (positive * trace)) τ_new v :
  push_of_trace (ts0 ++ [(τ_new, Call Push v)]) =
    push_of_trace ts0 ++ [τ_new].
Proof.
  rewrite /push_of_trace filter_app fmap_app.
  rewrite filter_cons_True; last by exists v.
  by rewrite filter_nil.
Qed.

Local Lemma push_of_trace_app_call_pop (ts0 : list (positive * trace)) τ_new :
  push_of_trace (ts0 ++ [(τ_new, Call Pop #())]) = push_of_trace ts0.
Proof.
  rewrite /push_of_trace filter_app fmap_app.
  rewrite filter_cons_False; last by intros [? Habs]; discriminate.
  rewrite filter_nil /= right_id_L //.
Qed.

Local Lemma push_of_trace_app_ret (ts0 : list (positive * trace)) τ_new ev :
  push_of_trace (ts0 ++ [(τ_new, Ret ev)]) = push_of_trace ts0.
Proof.
  rewrite /push_of_trace filter_app fmap_app.
  rewrite filter_cons_False; last by intros [? Habs]; discriminate.
  rewrite filter_nil /= right_id_L //.
Qed.

(*** Main lemmas: order_correct_matched under various extensions. ***)

(* For the four ts-extension matched lemmas (snoc_call_push, snoc_call_pop,
   snoc_ret_push, snoc_ret_pop_empty, snoc_ret_pop_val), the proof is:
   from valid_match, e_2 has Call Push and d_1 has Call Pop in ts. So
   pre_of_trace_app_inv lifts Hpre to pre(ts) form. Hocm gives ¬ pre(ts) d_2 d_1.
   bag.pre_of_trace_app_not (with d_1 having Call) re-extends. *)

Lemma order_correct_matched_snoc_call_push ts m τ v:
  valid_match ts m →
  order_correct_matched ts m → τ ∉ ts.*1 →
  order_correct_matched (ts++[(τ,Call Push v)]) m.
Proof.
  intros Hvm Hocm Hfresh e1 e2 d1 d2 Hpre Hin1 Hin2.
  destruct (valid_match_call_push _ _ _ _ Hvm Hin2) as [v2 Hcall_e2].
  pose proof (valid_match_call_pop _ _ _ _ Hvm Hin1) as Hcall_d1.
  assert (Hex_e2 : ∃ nc v', (e2, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_e2).
  assert (Hex_d1 : ∃ nc v', (d1, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_d1).
  apply (pre_of_trace_app_inv _ _ _ _ Hex_e2) in Hpre.
  pose proof (Hocm _ _ _ _ Hpre Hin1 Hin2) as Hnot_pre_ts.
  by apply (not_pre_of_trace_app _ _ _ _ Hex_d1).
Qed.

Lemma order_correct_matched_snoc_call_pop ts m τ:
  valid_match ts m →
  order_correct_matched ts m → τ ∉ ts.*1 →
  order_correct_matched (ts++[(τ,Call Pop #())]) m.
Proof.
  intros Hvm Hocm Hfresh e1 e2 d1 d2 Hpre Hin1 Hin2.
  destruct (valid_match_call_push _ _ _ _ Hvm Hin2) as [v2 Hcall_e2].
  pose proof (valid_match_call_pop _ _ _ _ Hvm Hin1) as Hcall_d1.
  assert (Hex_e2 : ∃ nc v', (e2, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_e2).
  assert (Hex_d1 : ∃ nc v', (d1, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_d1).
  apply (pre_of_trace_app_inv _ _ _ _ Hex_e2) in Hpre.
  pose proof (Hocm _ _ _ _ Hpre Hin1 Hin2) as Hnot_pre_ts.
  by apply (not_pre_of_trace_app _ _ _ _ Hex_d1).
Qed.

Lemma order_correct_matched_snoc_ret_push ts m τ v:
  valid_match ts m →
  order_correct_matched ts m → filter (λ x, x.1 = τ) ts = [(τ,Call Push v)] →
  order_correct_matched (ts++[(τ,Ret #())]) m.
Proof.
  intros Hvm Hocm Hfilter e1 e2 d1 d2 Hpre Hin1 Hin2.
  destruct (valid_match_call_push _ _ _ _ Hvm Hin2) as [v2 Hcall_e2].
  pose proof (valid_match_call_pop _ _ _ _ Hvm Hin1) as Hcall_d1.
  assert (Hex_e2 : ∃ nc v', (e2, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_e2).
  assert (Hex_d1 : ∃ nc v', (d1, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_d1).
  apply (pre_of_trace_app_inv _ _ _ _ Hex_e2) in Hpre.
  pose proof (Hocm _ _ _ _ Hpre Hin1 Hin2) as Hnot_pre_ts.
  by apply (not_pre_of_trace_app _ _ _ _ Hex_d1).
Qed.

Lemma order_correct_matched_snoc_ret_pop_empty ts m τ :
  valid_match ts m →
  order_correct_matched ts m → filter (λ x, x.1 = τ) ts = [(τ,Call Pop #())] →
  order_correct_matched (ts++[(τ, Ret (encode_response IsEmpty))]) m.
Proof.
  intros Hvm Hocm Hfilter e1 e2 d1 d2 Hpre Hin1 Hin2.
  destruct (valid_match_call_push _ _ _ _ Hvm Hin2) as [v2 Hcall_e2].
  pose proof (valid_match_call_pop _ _ _ _ Hvm Hin1) as Hcall_d1.
  assert (Hex_e2 : ∃ nc v', (e2, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_e2).
  assert (Hex_d1 : ∃ nc v', (d1, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_d1).
  apply (pre_of_trace_app_inv _ _ _ _ Hex_e2) in Hpre.
  pose proof (Hocm _ _ _ _ Hpre Hin1 Hin2) as Hnot_pre_ts.
  by apply (not_pre_of_trace_app _ _ _ _ Hex_d1).
Qed.

Lemma order_correct_matched_snoc_ret_pop_val ts m τ1 τ2 v :
  valid_match ts m →
  order_correct_matched ts m →
  (τ1, τ2) ∈ m →
  filter (λ x, x.1 = τ2) ts = [(τ2, Call Pop #())] →
  order_correct_matched (ts ++ [(τ2, Ret (encode_response (NonEmpty v)))]) m.
Proof.
  intros Hvm Hocm Hin Hfilter e1 e2 d1 d2 Hpre Hin1 Hin2.
  destruct (valid_match_call_push _ _ _ _ Hvm Hin2) as [v2 Hcall_e2].
  pose proof (valid_match_call_pop _ _ _ _ Hvm Hin1) as Hcall_d1.
  assert (Hex_e2 : ∃ nc v', (e2, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_e2).
  assert (Hex_d1 : ∃ nc v', (d1, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_d1).
  apply (pre_of_trace_app_inv _ _ _ _ Hex_e2) in Hpre.
  pose proof (Hocm _ _ _ _ Hpre Hin1 Hin2) as Hnot_pre_ts.
  by apply (not_pre_of_trace_app _ _ _ _ Hex_d1).
Qed.

(* This lemma additionally requires τ1 ∉ m.*1 and (τ1, Call Push v) ∈ ts.
   Without the former, a counterexample exists where τ1 already appears in
   m.*1 (e.g., as (τ1, d') ∈ m); a new pair (τ1, τ2) then can fail
   order_correct_matched even though all stated hypotheses hold. The Call
   Push hypothesis is used (with Hocum) to derive contradiction in case 3.
   Both additional hypotheses are available at call sites of this lemma
   (e.g., I_queue_pre_snoc_match passes them via Hτ1_nm and Hcall_push). *)
Lemma order_correct_matched_snoc_match ts m τ1 τ2 v :
  order_correct_matched ts m →
  order_correct_unmatched ts m →
  τ1 ∉ m.*1 →
  (τ1, Call Push v) ∈ ts →
  τ2 ∉ (filter (is_ret ∘ snd) ts).*1 →
  order_correct_matched ts (m ++ [(τ1, τ2)]).
Proof.
  intros Hocm Hocu Hτ1_nm Hcall_τ1 Hτ2_no_ret e1 e2 d1 d2 Hpre Hin1 Hin2.
  apply elem_of_app in Hin1 as [Hin1m | Hin1_new].
  - apply elem_of_app in Hin2 as [Hin2m | Hin2_new].
    + by apply (Hocm _ _ _ _ Hpre Hin1m Hin2m).
    + apply list_elem_of_singleton in Hin2_new. injection Hin2_new as -> ->.
      by apply pre_of_trace_no_ret_l.
  - apply list_elem_of_singleton in Hin1_new. injection Hin1_new as -> ->.
    apply elem_of_app in Hin2 as [Hin2m | Hin2_new].
    + exfalso. apply Hτ1_nm.
      assert (Hpush_τ1 : τ1 ∈ push_of_trace ts).
      { apply (list_elem_of_fmap_2 fst _ (τ1, Call Push v)).
        apply list_elem_of_filter_2; [by exists v|exact Hcall_τ1]. }
      assert (He2_inm : e2 ∈ m.*1) by (by apply (list_elem_of_fmap_2 fst _ (e2, d2))).
      exact (Hocu _ _ Hpre Hpush_τ1 He2_inm).
    + apply list_elem_of_singleton in Hin2_new. injection Hin2_new as -> ->.
      by apply pre_of_trace_no_ret_l.
Qed.

(*** order_correct_unmatched lemmas ***)

Lemma order_correct_unmatched_snoc_call_push ts m τ v:
  valid_match ts m →
  order_correct_unmatched ts m → τ ∉ ts.*1 →
  order_correct_unmatched (ts++[(τ,Call Push v)]) m.
Proof.
  intros Hvm Hocu Hfresh e1 e2 Hpre Hpush_ext Hin2.
  apply list_elem_of_fmap_1 in Hin2 as ([e2' d2'] & Heq & Hin2_pair).
  simpl in Heq. subst e2'.
  destruct (valid_match_call_push _ _ _ _ Hvm Hin2_pair) as [v2 Hcall_e2].
  assert (Hex_e2 : ∃ nc v', (e2, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_e2).
  apply (pre_of_trace_app_inv _ _ _ _ Hex_e2) in Hpre.
  rewrite push_of_trace_app_call_push elem_of_app list_elem_of_singleton in Hpush_ext.
  destruct Hpush_ext as [Hpush_ts | He1_eq_τ].
  - exact (Hocu _ _ Hpre Hpush_ts (list_elem_of_fmap_2 fst _ (e2, d2') Hin2_pair)).
  - subst e1. exfalso. apply Hfresh.
    rewrite /pre_of_trace in Hpre.
    destruct (ret_of_tag ts τ) as [[i [τ' ev]]|] eqn:Hret;
      simpl in Hpre; [|done].
    rewrite /ret_of_tag in Hret. apply list_find_Some in Hret as (Hlookup & [Htag _] & _).
    simpl in Htag. subst τ'.
    apply (list_elem_of_fmap_2 fst _ (τ, ev)).
    by apply list_elem_of_lookup_2 in Hlookup.
Qed.

Lemma order_correct_unmatched_snoc_call_pop ts m τ:
  valid_match ts m →
  order_correct_unmatched ts m → τ ∉ ts.*1 →
  order_correct_unmatched (ts++[(τ,Call Pop #())]) m.
Proof.
  intros Hvm Hocu Hfresh e1 e2 Hpre Hpush_ext Hin2.
  apply list_elem_of_fmap_1 in Hin2 as ([e2' d2'] & Heq & Hin2_pair).
  simpl in Heq. subst e2'.
  destruct (valid_match_call_push _ _ _ _ Hvm Hin2_pair) as [v2 Hcall_e2].
  assert (Hex_e2 : ∃ nc v', (e2, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_e2).
  apply (pre_of_trace_app_inv _ _ _ _ Hex_e2) in Hpre.
  rewrite push_of_trace_app_call_pop in Hpush_ext.
  exact (Hocu _ _ Hpre Hpush_ext (list_elem_of_fmap_2 fst _ (e2, d2') Hin2_pair)).
Qed.

Lemma order_correct_unmatched_snoc_ret_push ts m τ v :
  valid_match ts m →
  order_correct_unmatched ts m → filter (λ x, x.1 = τ) ts = [(τ,Call Push v)] →
  order_correct_unmatched (ts++[(τ, Ret #())]) m.
Proof.
  intros Hvm Hocu Hfilter e1 e2 Hpre Hpush_ext Hin2.
  apply list_elem_of_fmap_1 in Hin2 as ([e2' d2'] & Heq & Hin2_pair).
  simpl in Heq. subst e2'.
  destruct (valid_match_call_push _ _ _ _ Hvm Hin2_pair) as [v2 Hcall_e2].
  assert (Hex_e2 : ∃ nc v', (e2, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_e2).
  apply (pre_of_trace_app_inv _ _ _ _ Hex_e2) in Hpre.
  rewrite push_of_trace_app_ret in Hpush_ext.
  exact (Hocu _ _ Hpre Hpush_ext (list_elem_of_fmap_2 fst _ (e2, d2') Hin2_pair)).
Qed.

Lemma order_correct_unmatched_snoc_ret_pop_val ts m τ v :
  valid_match ts m →
  order_correct_unmatched ts m → filter (λ x, x.1 = τ) ts = [(τ,Call Pop #())] →
  order_correct_unmatched (ts++[(τ, Ret (encode_response (NonEmpty v)))]) m.
Proof.
  intros Hvm Hocu Hfilter e1 e2 Hpre Hpush_ext Hin2.
  apply list_elem_of_fmap_1 in Hin2 as ([e2' d2'] & Heq & Hin2_pair).
  simpl in Heq. subst e2'.
  destruct (valid_match_call_push _ _ _ _ Hvm Hin2_pair) as [v2 Hcall_e2].
  assert (Hex_e2 : ∃ nc v', (e2, Call nc v') ∈ ts) by (do 2 eexists; exact Hcall_e2).
  apply (pre_of_trace_app_inv _ _ _ _ Hex_e2) in Hpre.
  rewrite push_of_trace_app_ret in Hpush_ext.
  exact (Hocu _ _ Hpre Hpush_ext (list_elem_of_fmap_2 fst _ (e2, d2') Hin2_pair)).
Qed.

Lemma order_correct_unmatched_snoc_match ts m τ1 τ2 :
  order_correct_unmatched ts m →
  τ1 ∉ m.*1 →
  (∀ τ1', pre_of_trace ts τ1' τ1 → τ1' ∈ push_of_trace ts → τ1' ∈ m.*1) →
  order_correct_unmatched ts (m++[(τ1, τ2)]).
Proof.
  intros Hocu Hτ1_nm Hpre_τ1 e1 e2 Hpre Hpush Hin2.
  rewrite fmap_app /= elem_of_app list_elem_of_singleton in Hin2.
  rewrite fmap_app /= elem_of_app list_elem_of_singleton.
  destruct Hin2 as [Hin2m | ->].
  - left. exact (Hocu _ _ Hpre Hpush Hin2m).
  - left. exact (Hpre_τ1 _ Hpre Hpush).
Qed.
(* End LLM-generated code. *)
(**********************************************************)

Lemma I_queue_pre_nil : I_queue_pre [] [].
Proof.
  split_and!.
  - apply valid_match_nil.
  - apply per_tag_pop_empty_sound_nil.
  - apply order_correct_matched_nil.
  - apply order_correct_unmatched_nil.
Qed.

Lemma I_queue_pre_snoc_ret_pop_val rme valid_value ts m τ1 τ2 v :
  per_tag_wellformed_bag rme valid_value ts →
  I_queue_pre ts m →
  (τ1, τ2) ∈ m →
  (τ1, Call Push v) ∈ ts →
  filter (λ x, x.1 = τ2) ts = [(τ2, Call Pop #())] →
  I_queue_pre (ts ++ [(τ2, Ret (encode_response (NonEmpty v)))]) m.
Proof.
  intros Hwf (Hvm & Hps & Hocm & Hocu) ???.
  rewrite /I_queue_pre. split_and!.
  - by eapply valid_match_snoc_ret_pop_val.
  - by eapply per_tag_pop_empty_sound_snoc_ret_pop_val.
  - by eapply order_correct_matched_snoc_ret_pop_val.
  - by eapply order_correct_unmatched_snoc_ret_pop_val.
Qed.

Lemma I_queue_pre_snoc_match ts m τ1 τ2 v :
  I_queue_pre ts m →
  τ1 ∉ m.*1 → τ2 ∉ m.*2 →
  τ2 ∉ (filter (is_ret ∘ snd) ts).*1 →
  (τ1, Call Push v) ∈ ts →
  (τ2, Call Pop #()) ∈ ts →
  (∀ τ1', pre_of_trace ts τ1' τ1 → τ1' ∈ push_of_trace ts → τ1' ∈ m.*1) →
  I_queue_pre ts (m++[(τ1, τ2)]).
Proof.
  intros (Hvm & Hps & Hocm & Hocu) ?? Hτ2_no_ret ???.
  rewrite /I_queue_pre. split_and!.
  - by eapply valid_match_snoc_match.
  - by eapply per_tag_pop_empty_sound_snoc_match.
  - by eapply order_correct_matched_snoc_match.
  - by eapply order_correct_unmatched_snoc_match.
Qed.

Lemma I_queue_nil : I_queue [].
Proof. exists []. apply I_queue_pre_nil. Qed.
