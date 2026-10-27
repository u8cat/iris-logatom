(* The trace <-> history binding for sets: a complete, closed trace that is linearizable
   with respect to the bag model is linearizable as a set history (bag/ext/conc_his_rel.v).
   Shared by the queue and stack theorems. *)
From stdpp Require Import finite.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.bag.ext Require Import conc_his_rel.
From iris_logatom.pure_logic.aspect.bag Require Import base linear_points binder.

Global Instance trace_pre_dec ts : RelDecision (trace_pre ts).
Proof. intros a b. unfold trace_pre. apply _. Qed.

Global Instance trace_prt_dec ts ts' : RelDecision (trace_prt ts ts').
Proof. intros a b. unfold trace_prt. apply _. Qed.

Global Instance trace_val_dec ts m : RelDecision (trace_val ts m).
Proof. intros a b. unfold trace_val. apply _. Qed.

Global Instance trace_empty_dec ts m a : Decision (trace_empty ts m a).
Proof. unfold trace_empty. apply _. Qed.

Section set_binder.
  Variables (rme : response_mayempty) (valid_value : val → Prop) (ts : list (positive * trace)) (m : list (positive*positive)).
  Hypothesis Hvalid : valid_match ts m.
  Hypothesis Hcomplete : per_tag_complete ts.
  Hypothesis Hclosed : closed_match ts m.

  Local Notation call_ret_le := (bag.binder.call_ret_le ts m Hvalid Hcomplete Hclosed).
  Local Notation trace_op := (bag.binder.trace_op ts).
  Local Notation trace_pre := (bag.binder.trace_pre ts).
  Local Notation trace_prt := (bag.binder.trace_prt ts).
  Local Notation trace_val := (bag.binder.trace_val ts m).
  Local Notation trace_empty := (bag.binder.trace_empty ts m).

  Lemma conc_history_trace_pre : ConcHistory trace_pre.
  Proof.
    constructor.
    - (* Transitive *)
      rewrite /trace_pre /pre_of_trace. intros [τ1 ?] [τ2 ?] [τ3 ?] Hpre12 Hpre23.
      simpl in *.
      destruct (ret_of_tag ts τ1) as [[ret1 ?]|] eqn:Hret1; last done.
      destruct (ret_of_tag ts τ2) as [[ret2 ?]|] eqn:Hret2; last done.
      destruct (call_of_tag ts τ2) as [[call2 ?]|] eqn:Hcall2; last done.
      destruct (call_of_tag ts τ3) as [[call3 ?]|] eqn:Hcall3; last done.
      simpl in *.
      pose proof (call_ret_le Hcall2 Hret2).
      lia.
    - (* Antisymmetric *)
      rewrite /trace_pre /pre_of_trace. intros [τ1 ?] [τ2 ?] Hpre12 Hpre21.
      exfalso.
      simpl in *.
      destruct (ret_of_tag ts τ1) as [[ret1 ?]|] eqn:Hret1; last done.
      destruct (ret_of_tag ts τ2) as [[ret2 ?]|] eqn:Hret2; last done.
      destruct (call_of_tag ts τ2) as [[call2 ?]|] eqn:Hcall2; last done.
      destruct (call_of_tag ts τ1) as [[call1 ?]|] eqn:Hcall1; last done.
      simpl in *.
      pose proof (call_ret_le Hcall1 Hret1).
      pose proof (call_ret_le Hcall2 Hret2).
      lia.
    - (* Irreflexive *)
      rewrite /trace_pre /pre_of_trace. intros [τ ?] Hpre.
      simpl in *.
      destruct (ret_of_tag ts τ) as [[ret ?]|] eqn:Hret; last done.
      destruct (call_of_tag ts τ) as [[call ?]|] eqn:Hcall; last done.
      simpl in *.
      pose proof (call_ret_le Hcall Hret).
      lia.
    - (* Abcd *)
      rewrite /trace_pre /pre_of_trace. intros [τ1 ?] [τ2 ?] [τ3 ?] [τ4 ?] Hpre12 Hpre34.
      simpl in *.
      destruct (ret_of_tag ts τ1) as [[ret1 ?]|] eqn:Hret1; last done.
      destruct (ret_of_tag ts τ3) as [[ret3 ?]|] eqn:Hret3; last done.
      destruct (call_of_tag ts τ2) as [[call2 ?]|] eqn:Hcall2; last done.
      destruct (call_of_tag ts τ4) as [[call4 ?]|] eqn:Hcall4; last done.
      simpl in *.
      lia.
  Qed.

  Lemma conc_history_trace_prt ts' :
    ConcHistory (trace_prt ts').
  Proof.
    constructor.
    - (* Transitive *)
      rewrite /trace_prt /prt_of_trace. intros [τ1 ?] [τ2 ?] [τ3 ?] Hpre12 Hpre23.
      simpl in *.
      destruct (lin_of_tag ts' τ1) as [[lin1 ?]|] eqn:Hlin1; last done.
      destruct (lin_of_tag ts' τ2) as [[lin2 ?]|] eqn:Hlin2; last done.
      destruct (lin_of_tag ts' τ3) as [[lin3 ?]|] eqn:Hlin3; last done.
      simpl in *.
      lia.
    - (* Antisymmetric *)
      rewrite /trace_prt /prt_of_trace. intros [τ1 ?] [τ2 ?] Hpre12 Hpre21.
      exfalso.
      simpl in *.
      destruct (lin_of_tag ts' τ1) as [[lin1 ?]|] eqn:Hlin1; last done.
      destruct (lin_of_tag ts' τ2) as [[lin2 ?]|] eqn:Hlin2; last done.
      simpl in *.
      lia.
    - (* Irreflexive *)
      rewrite /trace_prt /prt_of_trace. intros [τ ?] Hpre.
      simpl in *.
      destruct (lin_of_tag ts' τ) as [[lin ?]|] eqn:Hlin; last done.
      simpl in *.
      lia.
    - (* Abcd *)
      rewrite /trace_prt /prt_of_trace. intros [τ1 ?] [τ2 ?] [τ3 ?] [τ4 ?] Hpre12 Hpre34.
      simpl in *.
      destruct (lin_of_tag ts' τ1) as [[lin1 ?]|] eqn:Hlin1; last done.
      destruct (lin_of_tag ts' τ3) as [[lin3 ?]|] eqn:Hlin3; last done.
      destruct (lin_of_tag ts' τ2) as [[lin2 ?]|] eqn:Hlin2; last done.
      destruct (lin_of_tag ts' τ4) as [[lin4 ?]|] eqn:Hlin4; last done.
      simpl in *.
      lia.
  Qed.

  Local Lemma τ_in_filter_lin ts' τ :
    ts = filter (not ∘ is_lin ∘ snd) ts' →
    per_tag_linearized ts' →
    τ ∈ ts.*1 →
    τ ∈ (filter (is_lin ∘ snd) ts').*1.
  Proof.
    intros Hfilter Hper_tag_lin Hin.
    destruct (Hcomplete τ) as (nv&v&v'&[HFalse|Heq]).
    { exfalso.
      destruct (list_elem_of_fmap_1 fst ts τ Hin) as ([τ' t] & Heq & Hin').
      simpl in Heq. subst τ'. clear Hin.
      assert (Hin_filter_tag: (τ,t) ∈ filter (λ x, x.1 = τ) ts).
      { by rewrite list_elem_of_filter. }
      rewrite HFalse in Hin_filter_tag. set_solver. }
    (* rewrite Heq in Hin_filter_tag.
    rewrite !elem_of_cons elem_of_nil right_id in Hin_filter_tag. *)
    destruct (Hper_tag_lin τ) as (nv_&v_&v'_&[l Heq']).

    (* show that filter (not ∘ is_lin ∘ snd) l = nil *)
    rewrite Hfilter list_filter_comm in Heq.
    apply (f_equal (filter (not∘is_lin∘snd))) in Heq' as Heq''.
    rewrite filter_app Heq in Heq''.
    rewrite filter_cons_True in Heq''; last by simpl; auto.
    rewrite filter_cons_False in Heq''; last by simpl; auto.
    rewrite filter_cons_True in Heq''; last by simpl; auto.
    rewrite filter_nil in Heq''.
    rewrite -(right_id_L [] (++) [(τ, Call nv_ v_); (τ, Ret v'_)]) in Heq''.
    apply app_inj_1 in Heq'' as [Heq''1 Heq''2]; last done.
    injection  Heq''1 as -> -> ->.

    (* show that l = nil *)
    destruct l as [|x l _] using rev_ind; last first.
    { apply (f_equal last) in Heq'.
      rewrite assoc last_snoc /= in Heq'.
      injection Heq' as <-.
      rewrite filter_app in Heq''2.
      symmetry in Heq''2.
      apply app_nil_r_inv in Heq''2.
      rewrite filter_cons_True in Heq''2; last by simpl; auto.
      discriminate. }
    rewrite right_id_L in Heq'.

    (* now we know (τ,Lin nv v v') ∈ ts' *)
    assert (Hin': (τ,Lin nv v v') ∈ ts').
    { apply (list_elem_of_filter_1 (λ t, t.1 = τ)).
      rewrite -Heq'. set_solver. }
    change (τ) with (τ,Lin nv v v').1.
    apply list_elem_of_fmap_2.
    apply list_elem_of_filter_2; done.
  Qed.

  Lemma trichotomy_trace_prt ts' :
    ts = filter (not∘is_lin∘snd) ts' →
    per_tag_linearized ts' →
    Trichotomy (trace_prt ts').
  Proof.
    intros Hfilter Hper_tag_lin [τ1 H1] [τ2 H2].
    rewrite /trace_prt sig_eq_pi. simpl.
    rewrite /events_of_trace !elem_of_list_to_set in H1,H2.
    eapply τ_in_filter_lin in H1; [|eassumption..].
    eapply τ_in_filter_lin in H2; [|eassumption..].
    apply list_elem_of_fmap_1 in H1 as ([τ1' t1] & Heq & H1).
    simpl in Heq. subst τ1'.
    apply list_elem_of_fmap_1 in H2 as ([τ2' t2] & Heq & H2).
    simpl in Heq. subst τ2'.
    apply list_elem_of_filter in H1.
    destruct H1 as [Hlin1 H1].
    apply list_elem_of_filter in H2.
    destruct H2 as [Hlin2 H2].
    opose proof (list_find_exists_Some (λ x, x.1 = τ1 ∧ is_lin x.2) ts' _)
      as (i1 & [τ1' t1'] & Hlin_of_tag1).
    { exists (τ1,t1). split_and!; done. }
    rewrite -/(lin_of_tag ts' τ1) in Hlin_of_tag1.
    opose proof (list_find_exists_Some (λ x, x.1 = τ2 ∧ is_lin x.2) ts' _)
      as (i2 & [τ2' t2'] & Hlin_of_tag2).
    { exists (τ2,t2). split_and!; done. }
    rewrite -/(lin_of_tag ts' τ2) in Hlin_of_tag2.
    rewrite /prt_of_trace Hlin_of_tag1 Hlin_of_tag2 /=.
    assert (i1 < i2 ∨ i1 = i2 ∨ i2 < i1) as [? | [<- | ?] ] by lia; auto.
    right; left.
    apply list_find_Some in Hlin_of_tag1, Hlin_of_tag2.
    destruct Hlin_of_tag1 as (Hlookup1 & [Heq1 _] & _).
    destruct Hlin_of_tag2 as (Hlookup2 & [Heq2 _] & _).
    simplify_eq. done.
  Qed.

  Lemma push_once_trace_val : push_once trace_val.
  Proof.
    intros [ia ?] [ib ?] [ra ?] [i Hin1]%list_elem_of_lookup_1 [j Hin2]%list_elem_of_lookup_1.
    apply (inj proj1_sig).
    simpl. simpl in Hin1, Hin2.
    destruct Hvalid as (_ & [_ Hnodup] & _).
    apply (list_lookup_fmap_Some_2 snd) in Hin1 as Hinj1'.
    apply (list_lookup_fmap_Some_2 snd) in Hin2 as Hinj2'.
    opose proof (NoDup_lookup m.*2 i j ra Hnodup Hinj1' Hinj2') as <-.
    rewrite Hin1 in Hin2. injection Hin2. done.
  Qed.

  Lemma pop_once_trace_val : pop_once trace_val.
  Proof.
    intros [ia ?] [ra ?] [rb ?] [i Hin1]%list_elem_of_lookup_1 [j Hin2]%list_elem_of_lookup_1.
    apply (inj proj1_sig).
    simpl. simpl in Hin1, Hin2.
    destruct Hvalid as (_ & [Hnodup _] & _).
    apply (list_lookup_fmap_Some_2 fst) in Hin1 as Hinj1'.
    apply (list_lookup_fmap_Some_2 fst) in Hin2 as Hinj2'.
    opose proof (NoDup_lookup m.*1 i j ia Hnodup Hinj1' Hinj2') as <-.
    rewrite Hin1 in Hin2. injection Hin2. done.
  Qed.

  Lemma val_order_trace_val :
    val_order trace_val.
  Proof.
    intros [ia ?] [ra ?] Hin1 [[b ?] [Hin2 | Hin2]].
    - destruct (valid_match_call_push ts m _ _ Hvalid Hin1) as (x & Hia_call).
      pose proof (valid_match_call_pop ts m _ _ Hvalid Hin2) as Hia_ret.
      apply (list_elem_of_filter_2 (λ t, t.1 = ia)) in Hia_call; last done.
      apply (list_elem_of_filter_2 (λ t, t.1 = ia)) in Hia_ret; last done.
      destruct (Hcomplete ia) as (?&?&?&[Heq|Heq]).
      { rewrite Heq in Hia_call. set_solver. }
      rewrite Heq in Hia_call, Hia_ret.
      rewrite !elem_of_cons !elem_of_nil !right_id in Hia_call, Hia_ret.
      destruct Hia_call as [Hia_call|]; last discriminate.
      destruct Hia_ret as [Hia_ret|]; last discriminate.
      simplify_eq.
    - pose proof (valid_match_call_pop ts m _ _ Hvalid Hin1) as Hra_ret.
      destruct (valid_match_call_push ts m _ _ Hvalid Hin2) as (x & Hra_call).
      apply (list_elem_of_filter_2 (λ t, t.1 = ra)) in Hra_ret; last done.
      apply (list_elem_of_filter_2 (λ t, t.1 = ra)) in Hra_call; last done.
      destruct (Hcomplete ra) as (?&?&?&[Heq|Heq]).
      { rewrite Heq in Hra_call. set_solver. }
      rewrite Heq in Hra_call, Hra_ret.
      rewrite !elem_of_cons !elem_of_nil !right_id in Hra_call, Hra_ret.
      destruct Hra_call as [Hra_call|]; last discriminate.
      destruct Hra_ret as [Hra_ret|]; last discriminate.
      simplify_eq.
  Qed.

  Lemma all_popped_or_empty_trace_val_trace_empty :
    per_tag_wellformed_bag rme valid_value ts →
    all_popped_or_empty trace_val trace_empty.
  Proof.
    intros Hwf [ia Hia].
    destruct (decide (empty_of_trace_match ts m ia)) as [Hemp | Hnot_emp];
      [by left|right].
    destruct (decide (ia ∈ pop_of_trace ts)) as [Hpop | Hnot_pop].
    - (* ia is pop *)
      rewrite /empty_of_trace_match not_and_l in Hnot_emp.
      destruct Hnot_emp as [|Hia_in_m%dec_stable]; first done.
      destruct (list_elem_of_lookup_1 _ _ Hia_in_m) as [i Hlookup].
      apply lookup_lt_Some in Hlookup as Hi_lt.
      rewrite length_fmap in Hi_lt.
      destruct (lookup_lt_is_Some_2 m i Hi_lt) as [[τ1 τ2] Hlookup'].
      apply (list_lookup_fmap_Some_2 snd) in Hlookup' as Hlookup''.
      rewrite Hlookup in Hlookup''.
      injection Hlookup'' as ->. clear Hlookup.
      apply list_elem_of_lookup_2 in Hlookup' as Hin.
      assert (Hτ1: τ1 ∈ events_of_trace ts).
      { destruct (valid_match_call_push _ _ _ _ Hvalid Hin) as [? Hτ1_call].
        apply (list_elem_of_fmap_2 fst) in Hτ1_call.
        by apply elem_of_list_to_set. }
      eexists (τ1 ↾ Hτ1). right. done.
    - (* ia is push *)
      opose proof (push_or_pop_of_trace ts _ _ ia Hwf Hia) as [Hpush |]; last done.
      destruct Hclosed as [Hpush_subset _].
      assert (Hia_in_m: ia ∈ m.*1) by set_solver.
      destruct (list_elem_of_lookup_1 _ _ Hia_in_m) as [i Hlookup].
      apply lookup_lt_Some in Hlookup as Hi_lt.
      rewrite length_fmap in Hi_lt.
      destruct (lookup_lt_is_Some_2 m i Hi_lt) as [[τ1 τ2] Hlookup'].
      apply (list_lookup_fmap_Some_2 fst) in Hlookup' as Hlookup''.
      rewrite Hlookup in Hlookup''.
      injection Hlookup'' as ->. clear Hlookup.
      apply list_elem_of_lookup_2 in Hlookup' as Hin.
      assert (Hτ2: τ2 ∈ events_of_trace ts).
      { pose proof (valid_match_call_pop _ _ _ _ Hvalid Hin) as Hτ2_ret.
        apply (list_elem_of_fmap_2 fst) in Hτ2_ret.
        by apply elem_of_list_to_set. }
      eexists (τ2 ↾ Hτ2). left. done.
  Qed.

  Lemma empty_then_not_val_trace_val_trace_empty :
    empty_then_not_val trace_val trace_empty.
  Proof.
    intros [ia Hia] [Hia_pop Hia_notin_m].
    split; last by intros [[??] ?%(list_elem_of_fmap_2 snd)].
    intros [[b Hb] Hb_in_m].
    (* ia is pop because of [Hia_pop] *)
    destruct (list_elem_of_fmap_1 fst _ ia Hia_pop) as ([ia' t] & Heq & Hia_pop').
    simpl in Heq. subst ia'.
    apply (list_elem_of_filter_2 (λ x, x.1 = ia)) in Hia_pop'; last done.

    (* However, ia is push because of [Hb_in_m] *)
    destruct (valid_match_call_push _ _ _ _ Hvalid Hb_in_m) as [v Hia_call].
    apply (list_elem_of_filter_2 (λ x, x.1 = ia)) in Hia_call; last done.
    destruct (Hcomplete ia) as (?&?&?&[Heq|Heq]).
    { rewrite Heq in Hia_call. set_solver. }
    rewrite Heq !elem_of_cons elem_of_nil right_id in Hia_call.
    destruct Hia_call as [Hia_call|]; last discriminate.
    injection Hia_call as <-.
    apply (f_equal (filter (is_call_pop ∘ snd))) in Heq.
    do 2 rewrite filter_cons_False // in Heq.
    rewrite filter_nil in Heq.

    rewrite list_filter_comm in Heq.
    rewrite Heq in Hia_pop'.
    set_solver.
  Qed.


  (**********************************************************)
  (* Begin LLM-generated code. *)
  (* tool: Claude Code 2.1.91
     model: Claude Opus 4.6 (claude-opus-4-6)
     parameters:
        effort = high
        context window = 1000000
        max output tokens = 128000 *)
  (* Public lemma types in this block are written by human. Only proofs
    and private lemmas are LLM-generated. *)

  (* per_tag_linearized → NoDup of Lin-filter tags *)
  Local Lemma per_tag_linearized_NoDup_lin_tags ts'₀ :
    per_tag_linearized ts'₀ →
    NoDup (filter (is_lin ∘ snd) ts'₀).*1.
  Proof.
    clear.
    intros Hptl.
    rewrite NoDup_alt. intros i j τ' Hi Hj.
    apply list_lookup_fmap_Some_1 in Hi as ([τ_i ev_i] & Heq_i & Hfi). simpl in Heq_i. subst τ_i.
    apply list_lookup_fmap_Some_1 in Hj as ([τ_j ev_j] & Heq_j & Hfj). simpl in Heq_j. subst τ_j.
    pose proof (list_filter_lookup_pred _ _ _ _ Hfi) as Hlin_i.
    pose proof (list_filter_lookup_pred _ _ _ _ Hfj) as Hlin_j.
    pose proof (list_filter_lookup_orig _ _ _ _ Hfi) as Hin_i.
    pose proof (list_filter_lookup_orig _ _ _ _ Hfj) as Hin_j.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ')) in Hin_i; last done.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ')) in Hin_j; last done.
    destruct (Hptl τ') as (nw & w & w' & Hprefix).
    pose proof (elem_of_prefix _ _ _ Hin_i Hprefix) as H1.
    pose proof (elem_of_prefix _ _ _ Hin_j Hprefix) as H2.
    rewrite !elem_of_cons !elem_of_nil !right_id in H1, H2.
    (* Both must be the Lin element — Call and Ret fail is_lin *)
    assert (Heq_i : ev_i = Lin nw w w').
    { destruct H1 as [H1|[H1|H1]]; apply (f_equal snd) in H1; simpl in H1; subst;
        try done; simpl in Hlin_i; done. }
    assert (Heq_j : ev_j = Lin nw w w').
    { destruct H2 as [H2|[H2|H2]]; apply (f_equal snd) in H2; simpl in H2; subst;
        try done; simpl in Hlin_j; done. }
    subst ev_i ev_j.
    eapply (filter_NoDup_at (is_lin ∘ snd) ts'₀ _ i j Hfi Hfj Hlin_i).
    intros i' j' Hi' Hj'.
    assert (Hi'_filt : (τ', Lin nw w w') ∈ filter (λ x, x.1 = τ') ts'₀).
    { apply list_elem_of_filter_2; [done|]. eapply list_elem_of_lookup_2. exact Hi'. }
    assert (Hj'_filt : (τ', Lin nw w w') ∈ filter (λ x, x.1 = τ') ts'₀).
    { apply list_elem_of_filter_2; [done|]. eapply list_elem_of_lookup_2. exact Hj'. }
    eapply (filter_at_most_once (λ x, x.1 = τ') ts'₀ (τ', Lin nw w w') eq_refl).
    + intros k1 k2 Hk1 Hk2.
      pose proof (prefix_lookup_Some _ _ k1 _ Hk1 Hprefix) as Hk1'.
      pose proof (prefix_lookup_Some _ _ k2 _ Hk2 Hprefix) as Hk2'.
      destruct k1 as [|[|[|]]]; simpl in Hk1'; try discriminate;
      destruct k2 as [|[|[|]]]; simpl in Hk2'; try discriminate;
      done.
    + exact Hi'.
    + exact Hj'.
  Qed.

  (* Basic list fact: per_tag_linearized + sublist ordering → lin_of_tag ordering.
     Each tag has at most one Lin event (per_tag_linearized). The sublist [τ_a;τ_b]
     of filter.*1 means τ_a's Lin comes before τ_b's Lin in ts'. list_find returns
     the unique position, so lin(τ_a) < lin(τ_b). *)
  Local Lemma sublist_lin_order ts'₀ τ_a τ_b :
    per_tag_linearized ts'₀ →
    NoDup (filter (is_lin ∘ snd) ts'₀).*1 →
    [τ_a; τ_b] `sublist_of` (filter (is_lin ∘ snd) ts'₀).*1 →
    ∃ pa xa pb xb,
      lin_of_tag ts'₀ τ_a = Some (pa, xa) ∧
      lin_of_tag ts'₀ τ_b = Some (pb, xb) ∧
      pa < pb.
  Proof.
    clear.
    intros Hptl Hnd Hsub.
    assert (Ha_in : τ_a ∈ (filter (is_lin ∘ snd) ts'₀).*1).
    { eapply elem_of_sublist; [|exact Hsub]. set_solver. }
    assert (Hb_in : τ_b ∈ (filter (is_lin ∘ snd) ts'₀).*1).
    { eapply elem_of_sublist; [|exact Hsub]. set_solver. }
    apply list_elem_of_fmap_1 in Ha_in as ([τ_a' ev_a] & Heq_a & Hin_a).
    simpl in Heq_a. subst τ_a'.
    apply list_elem_of_filter in Hin_a as [Hlin_a Hin_a_ts].
    apply list_elem_of_fmap_1 in Hb_in as ([τ_b' ev_b] & Heq_b & Hin_b).
    simpl in Heq_b. subst τ_b'.
    apply list_elem_of_filter in Hin_b as [Hlin_b Hin_b_ts].
    assert (Hfind_a := list_find_elem_of (λ t, t.1 = τ_a ∧ is_lin t.2) ts'₀ (τ_a, ev_a)
      Hin_a_ts (conj eq_refl Hlin_a)).
    assert (Hfind_b := list_find_elem_of (λ t, t.1 = τ_b ∧ is_lin t.2) ts'₀ (τ_b, ev_b)
      Hin_b_ts (conj eq_refl Hlin_b)).
    rewrite /lin_of_tag.
    destruct (list_find _ ts'₀) as [[pa xa]|] eqn:Hla; last by destruct Hfind_a.
    destruct (list_find (λ t, t.1 = τ_b ∧ is_lin t.2) ts'₀) as [[pb xb]|] eqn:Hlb;
      last by destruct Hfind_b.
    exists pa, xa, pb, xb. split_and!; [done|done|].
    pose proof Hla as Hla_orig. pose proof Hlb as Hlb_orig.
    apply list_find_Some in Hla as (Hlookup_a & [Htag_a Hlin_xa] & Hmin_a).
    apply list_find_Some in Hlb as (Hlookup_b & [Htag_b Hlin_xb] & Hmin_b).
    simpl in Htag_a, Htag_b.
    destruct (decide (pa < pb)); first lia. exfalso.
    destruct (decide (pa = pb)) as [->|Hne_pos].
    - (* pa = pb → xa = xb → τ_a = τ_b → [τ_a;τ_a] sublist of NoDup → False *)
      rewrite Hlookup_a in Hlookup_b. injection Hlookup_b as <-. subst.
      pose proof (sublist_NoDup _ _ Hnd Hsub) as Hnd_sub.
      apply NoDup_cons in Hnd_sub as [Habs _]. apply Habs. set_solver.
    - (* pb < pa *)
      assert (Hlt : pb < pa) by lia.
      pose proof (take_drop_middle _ _ _ Hlookup_b) as Hts_split.
      assert (Hxa_in_drop : xa ∈ drop (Datatypes.S pb) ts'₀).
      { eapply list_elem_of_lookup_2. rewrite lookup_drop.
        replace (Datatypes.S pb + (pa - Datatypes.S pb)) with pa by lia. exact Hlookup_a. }
      (* In filter.*1: τ_b is before τ_a (from ts'₀ positions). *)
      assert (Htb_before_ta :
        ∃ l_before l_after,
          (filter (is_lin ∘ snd) ts'₀).*1 = l_before ++ [τ_b] ++ l_after ∧ τ_a ∈ l_after).
      { eexists (filter (is_lin ∘ snd) (take pb ts'₀)).*1,
               (filter (is_lin ∘ snd) (drop (Datatypes.S pb) ts'₀)).*1.
        split.
        - apply (f_equal (λ l, (filter (is_lin ∘ snd) l).*1)) in Hts_split.
          rewrite !filter_app !fmap_app in Hts_split.
          rewrite (filter_cons_True (is_lin ∘ snd)) in Hts_split; last exact Hlin_xb.
          rewrite fmap_cons /= Htag_b in Hts_split. symmetry. exact Hts_split.
        - rewrite -Htag_a. apply (list_elem_of_fmap_2 fst).
          apply list_elem_of_filter_2; [exact Hlin_xa|exact Hxa_in_drop]. }
      destruct Htb_before_ta as (l_before & l_after & Hfilt_eq & Hta_in_after).
      rewrite Hfilt_eq in Hnd, Hsub.
      assert (Htb_notin_after : τ_b ∉ l_after).
      { intros Hin_la. rewrite /app in Hnd.
        apply NoDup_app in Hnd as (_ & Hdisj & Hnd_rest).
        apply NoDup_cons in Hnd_rest as [Habs _]. exact (Habs Hin_la). }
      apply Htb_notin_after.
      apply sublist_cons_l in Hsub as (k1 & k2 & Hk_eq & Hsub_tb).
      apply singleton_sublist_l in Hsub_tb.
      assert (Htb_notin_before : τ_b ∉ l_before).
      { apply NoDup_app in Hnd as (_ & Hdisj & _).
        intros Hin_lb. apply (Hdisj τ_b Hin_lb). set_solver. }
      assert (Htb_notin_k1 : τ_b ∉ k1).
      { assert (Hnd' : NoDup (k1 ++ τ_a :: k2)) by (rewrite -Hk_eq; exact Hnd).
        apply NoDup_app in Hnd' as (_ & Hdisj & _).
        intros Hin. apply (Hdisj τ_b Hin). set_solver. }
      assert (Htb_ne_ta : τ_b ≠ τ_a).
      { intros <-. apply Hne_pos. rewrite Hla_orig in Hlb_orig. by injection Hlb_orig. }
      apply list_elem_of_lookup_1 in Hsub_tb as [i_tb Hi_tb].
      assert (Hi_tb_list : (l_before ++ [τ_b] ++ l_after) !! (length k1 + 1 + i_tb) = Some τ_b).
      { rewrite Hk_eq lookup_app_r; last lia.
        replace (length k1 + 1 + i_tb - length k1) with (Datatypes.S i_tb) by lia.
        simpl. exact Hi_tb. }
      (* τ_b also at position |l_before| *)
      assert (Hi_tb_orig : (l_before ++ [τ_b] ++ l_after) !! (length l_before) = Some τ_b).
      { rewrite lookup_app_r; last lia. replace (length l_before - length l_before) with 0 by lia. done. }
      (* NoDup: these positions are equal *)
      assert (Hpos_eq : length k1 + 1 + i_tb = length l_before).
      { eapply NoDup_lookup; [exact Hnd|exact Hi_tb_list|exact Hi_tb_orig]. }
      (* τ_a at position |k1| in the list *)
      assert (Hi_ta_list : (l_before ++ [τ_b] ++ l_after) !! (length k1) = Some τ_a).
      { rewrite Hk_eq lookup_app_r; last lia.
        replace (length k1 - length k1) with 0 by lia. done. }
      (* |k1| < |l_before| (from Hpos_eq: |k1|+1+i_tb = |l_before| and i_tb ≥ 0) *)
      assert (Hk1_lt : length k1 < length l_before) by lia.
      (* τ_a at position |k1| < |l_before| → τ_a ∈ l_before *)
      rewrite lookup_app_l in Hi_ta_list; last lia.
      assert (Hta_in_before : τ_a ∈ l_before).
      { eapply list_elem_of_lookup_2. exact Hi_ta_list. }
      (* τ_a ∈ l_before ∧ τ_a ∈ l_after → NoDup contradiction *)
      apply NoDup_app in Hnd as (_ & Hdisj & _).
      exfalso. apply (Hdisj τ_a Hta_in_before). set_solver.
  Qed.

  (* Pigeonhole: injective map from NoDup list of same length is surjective *)
  Local Lemma pigeonhole (f : positive → positive)
    (la lb : list positive) :
    (∀ a, a ∈ la → f a ∈ lb) →
    (∀ a1 a2, a1 ∈ la → a2 ∈ la → f a1 = f a2 → a1 = a2) →
    NoDup la → NoDup lb →
    length la = length lb →
    ∀ b, b ∈ lb → ∃ a, a ∈ la ∧ f a = b.
  Proof.
    clear.
    intros Hmap Hinj Hnda Hndb Hlen b Hb.
    assert (Hnd_fa : NoDup (f <$> la)).
    { apply NoDup_fmap_2_strong; [|exact Hnda].
      intros x y Hx Hy. exact (Hinj x y Hx Hy). }
    assert (Hsub : f <$> la ⊆+ lb).
    { apply NoDup_submseteq; [exact Hnd_fa|].
      intros x. rewrite list_elem_of_fmap. intros (a & -> & Ha). exact (Hmap a Ha). }
    assert (Hperm : f <$> la ≡ₚ lb).
    { apply submseteq_length_Permutation; [exact Hsub|]. rewrite length_fmap. lia. }
    rewrite -Hperm in Hb.
    apply list_elem_of_fmap_1 in Hb as (a & -> & Ha). eauto.
  Qed.

  (* If [a; b] sublist of L1 ++ L2, NoDup, and b ∈ L1, then a ∈ L1. *)
  Local Lemma sublist_pair_in_prefix {A : Type} `{EqDecision A}
    (a b : A) (L1 L2 : list A) :
    [a; b] `sublist_of` (L1 ++ L2) →
    NoDup (L1 ++ L2) →
    b ∈ L1 →
    a ∈ L1.
  Proof.
    clear.
    intros Hsub Hnd Hb.
    apply sublist_cons_l in Hsub as (la & la' & Heq & Hb_la').
    apply singleton_sublist_l in Hb_la'.
    rewrite Heq in Hnd.
    apply NoDup_app in Hnd as (Hnd_la & Hdisj_la & Hnd_rest).
    (* b ∈ la → b ∉ a :: la' by Hdisj_la. But b ∈ la'. So b ∉ la. *)
    assert (Hb_not_la : b ∉ la).
    { intro Habs. apply (Hdisj_la b Habs). rewrite elem_of_cons. right. exact Hb_la'. }
    (* L1 = take (length L1) (la ++ a :: la') *)
    assert (HL1_eq : L1 = take (length L1) (la ++ a :: la')).
    { rewrite <- Heq. symmetry. apply take_app_length. }
    destruct (Nat.le_gt_cases (length L1) (length la)) as [Hle|Hgt].
    - (* |L1| ≤ |la|: L1 ⊆ la. b ∈ L1 → b ∈ la → contradiction *)
      exfalso. apply Hb_not_la.
      rewrite HL1_eq take_app_le in Hb; last lia.
      apply list_elem_of_lookup_1 in Hb as [i Hi].
      apply lookup_take_Some in Hi as [Hi _].
      eapply list_elem_of_lookup_2. exact Hi.
    - (* |L1| > |la|: a ∈ L1 *)
      rewrite HL1_eq take_app.
      rewrite take_ge; last lia.
      destruct (length L1 - length la) as [|k] eqn:Hk; first lia.
      simpl. apply elem_of_app. right. left.
  Qed.

  (* Counting functions for Lin events in bag_model *)
  Local Definition bag_pop_ne_vals (lts : list (positive * trace)) : list val :=
    omap (λ '(_, ev), match ev with Lin 1 _ (InjRV v) => Some v | _ => None end) lts.
  Local Definition bag_push_vals (lts : list (positive * trace)) : list val :=
    omap (λ '(_, ev), match ev with Lin 0 v (LitV LitUnit) => Some v | _ => None end) lts.

  Local Lemma bag_pop_ne_vals_app l1 l2 :
    bag_pop_ne_vals (l1 ++ l2) = bag_pop_ne_vals l1 ++ bag_pop_ne_vals l2.
  Proof. clear. apply omap_app. Qed.
  Local Lemma bag_push_vals_app l1 l2 :
    bag_push_vals (l1 ++ l2) = bag_push_vals l1 ++ bag_push_vals l2.
  Proof. clear. apply omap_app. Qed.
  Local Lemma bag_push_vals_push τ w :
    bag_push_vals [(τ, Lin Push w #())] = [w].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_pop_ne_vals_push τ w :
    bag_pop_ne_vals [(τ, Lin Push w #())] = [].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_push_vals_pop_empty τ :
    bag_push_vals [(τ, Lin Pop #() NONEV)] = [].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_pop_ne_vals_pop_empty τ :
    bag_pop_ne_vals [(τ, Lin Pop #() NONEV)] = [].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_push_vals_pop_ne τ w :
    bag_push_vals [(τ, Lin Pop #() (SOMEV w))] = [].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_pop_ne_vals_pop_ne τ v w :
    bag_pop_ne_vals [(τ, Lin Pop v (SOMEV w))] = [w].
  Proof. clear. reflexivity. Qed.

  (* Size balance for [rtcL model_step] on the bag model:
     size s' + #pops = size s + #pushes. *)
  Local Lemma model_steps_bag_size_balance
    (s0 s' : gmultiset val) (lts : list (positive * trace)) :
    rtcL (model_step (M:=bag_model rme valid_value)) s0 s' lts →
    size s' + length (bag_pop_ne_vals lts) = size s0 + length (bag_push_vals lts).
  Proof.
    clear.
    revert s' lts. apply rtcL_ind_r.
    - simpl. lia.
    - intros ?? ts ? Hls [s s' nn τ v v' Hvr Hrr] IH.
      change (@linear.S (bag_model rme valid_value)) with (gmultiset val) in *.
      destruct nn as [|[|nn]]; last by (simpl in Hvr; destruct Hvr).
      + (* Push v *)
        destruct Hrr as [-> ->].
        rewrite bag_pop_ne_vals_app bag_push_vals_app
                bag_pop_ne_vals_push bag_push_vals_push !length_app length_cons length_nil.
        rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
      + (* Pop *)
        simpl in Hvr. subst v.
        destruct Hrr as [Hempty|(w & Hw_in & -> & ->)].
        * (* Pop IsEmpty *)
          destruct rme; [|done]. destruct Hempty as (Hs & -> & ->).
          rewrite bag_pop_ne_vals_app bag_push_vals_app
                  bag_pop_ne_vals_pop_empty bag_push_vals_pop_empty !length_app length_nil.
          subst s. lia.
        * (* Pop NonEmpty w *)
          rewrite bag_pop_ne_vals_app bag_push_vals_app
                  bag_pop_ne_vals_pop_ne bag_push_vals_pop_ne !length_app length_cons length_nil.
          rewrite gmultiset_size_difference; last by apply gmultiset_singleton_subseteq_l.
          rewrite gmultiset_size_singleton.
          assert (1 ≤ size s).
          { rewrite -(gmultiset_size_singleton w). apply gmultiset_subseteq_size.
            by apply gmultiset_singleton_subseteq_l. }
          lia.
  Qed.


  Local Lemma push_tags_count_le (l : list (positive * trace))
    (tags : list positive) :
    NoDup l.*1 → NoDup tags →
    (∀ τ, τ ∈ tags → ∃ v, (τ, Lin Push v (LitV LitUnit)) ∈ l) →
    length tags ≤ length (bag_push_vals l).
  Proof.
    clear. revert tags. induction l as [|[τ0 ev0] rest IH]; intros tags Hnd_l Hnd_tags Htags.
    - (* l = []: tags must be empty *)
      destruct tags as [|tag tags]; [simpl; lia|].
      exfalso. destruct (Htags tag) as [? Habs]; [set_solver|set_solver].
    - apply NoDup_cons in Hnd_l as [Hnotin Hnd_rest].
      rewrite (_ : (τ0, ev0) :: rest = [(τ0, ev0)] ++ rest) // bag_push_vals_app length_app.
      destruct (decide (τ0 ∈ tags)) as [Hτ0_in|Hτ0_nin].
      + (* τ0 ∈ tags *)
        destruct (Htags _ Hτ0_in) as [v0 Hv0].
        apply elem_of_cons in Hv0 as [[= Hev0]|Hv0].
        * (* Head is the push event for τ0 *)
          subst ev0.
          rewrite bag_push_vals_push length_cons length_nil.
          apply list_elem_of_split in Hτ0_in as (tags1 & tags2 & ->).
          rewrite length_app /=.
          assert (Hle : length (tags1 ++ tags2) ≤ length (bag_push_vals rest)).
          { apply IH; [done| |].
            - pose proof Hnd_tags as HH0.
              apply NoDup_app in HH0 as (H1 & Hdisj & H2).
              apply NoDup_cons in H2 as [_ H2].
              apply NoDup_app; split; [done|split; [|done]].
              intros x Hx1 Hx2. apply (Hdisj x Hx1). right. exact Hx2.
            - intros τ' Hτ'. apply elem_of_app in Hτ' as [Hτ'|Hτ'].
              + destruct (Htags τ') as [v' Hv']; [apply elem_of_app; left; exact Hτ'|].
                apply elem_of_cons in Hv' as [Hv'|Hv']; [|eauto].
                exfalso. pose proof Hnd_tags as HH.
                apply NoDup_app in HH as (_ & Hdisj' & _).
                injection Hv' as <- _. apply (Hdisj' τ' Hτ'). set_solver.
              + destruct (Htags τ') as [v' Hv']; [apply elem_of_app; right; right; exact Hτ'|].
                apply elem_of_cons in Hv' as [Hv'|Hv']; [|eauto].
                exfalso. pose proof Hnd_tags as HH.
                apply NoDup_app in HH as (_ & _ & Hnd2').
                apply NoDup_cons in Hnd2' as [Hnin _]. injection Hv' as <- _. exact (Hnin Hτ'). }
          rewrite length_app in Hle. lia.
        * (* Push event for τ0 is in rest, not head *)
          assert (Hle : length tags ≤ length (bag_push_vals rest)).
          { apply IH; [done|done|].
            intros τ Hτ. destruct (Htags τ Hτ) as [v' Hv'].
            apply elem_of_cons in Hv' as [[= -> _]|Hv']; [|eauto].
            exfalso. apply Hnotin.
            exact (list_elem_of_fmap_2 fst _ _ Hv0). }
          lia.
      + (* τ0 ∉ tags *)
        assert (Hle : length tags ≤ length (bag_push_vals rest)).
        { apply IH; [done|done|].
          intros τ Hτ. destruct (Htags τ Hτ) as [v' Hv'].
          apply elem_of_cons in Hv' as [[= -> _]|Hv']; [|eauto].
          exfalso. exact (Hτ0_nin Hτ). }
        lia.
  Qed.

  (* Symmetric lemma for pop-ne tags *)
  Local Lemma pop_ne_tags_count_le (l : list (positive * trace))
    (tags : list positive) :
    NoDup l.*1 → NoDup tags →
    (∀ τ, τ ∈ tags → ∃ w, (τ, Lin Pop #() (SOMEV w)) ∈ l) →
    length tags ≤ length (bag_pop_ne_vals l).
  Proof.
    clear. revert tags. induction l as [|[τ0 ev0] rest IH]; intros tags Hnd_l Hnd_tags Htags.
    - destruct tags as [|tag tags]; [simpl; lia|].
      exfalso. destruct (Htags tag) as [? Habs]; [set_solver|set_solver].
    - apply NoDup_cons in Hnd_l as [Hnotin Hnd_rest].
      rewrite (_ : (τ0, ev0) :: rest = [(τ0, ev0)] ++ rest) // bag_pop_ne_vals_app length_app.
      destruct (decide (τ0 ∈ tags)) as [Hτ0_in|Hτ0_nin].
      + destruct (Htags _ Hτ0_in) as [w0 Hv0].
        apply elem_of_cons in Hv0 as [[= Hev0]|Hv0].
        * subst ev0.
          rewrite bag_pop_ne_vals_pop_ne length_cons length_nil.
          apply list_elem_of_split in Hτ0_in as (tags1 & tags2 & ->).
          rewrite length_app /=.
          assert (Hle : length (tags1 ++ tags2) ≤ length (bag_pop_ne_vals rest)).
          { apply IH; [done| |].
            - pose proof Hnd_tags as HH0.
              apply NoDup_app in HH0 as (H1 & Hdisj & H2).
              apply NoDup_cons in H2 as [_ H2].
              apply NoDup_app; split; [done|split; [|done]].
              intros x Hx1 Hx2. apply (Hdisj x Hx1). right. exact Hx2.
            - intros τ' Hτ'. apply elem_of_app in Hτ' as [Hτ'|Hτ'].
              + destruct (Htags τ') as [w' Hv']; [apply elem_of_app; left; exact Hτ'|].
                apply elem_of_cons in Hv' as [Hv'|Hv']; [|eauto].
                exfalso. pose proof Hnd_tags as HH.
                apply NoDup_app in HH as (_ & Hdisj' & _).
                injection Hv' as <- _. apply (Hdisj' τ' Hτ'). set_solver.
              + destruct (Htags τ') as [w' Hv']; [apply elem_of_app; right; right; exact Hτ'|].
                apply elem_of_cons in Hv' as [Hv'|Hv']; [|eauto].
                exfalso. pose proof Hnd_tags as HH.
                apply NoDup_app in HH as (_ & _ & Hnd2').
                apply NoDup_cons in Hnd2' as [Hnin _]. injection Hv' as <- _. exact (Hnin Hτ'). }
          rewrite length_app in Hle. lia.
        * assert (Hle : length tags ≤ length (bag_pop_ne_vals rest)).
          { apply IH; [done|done|].
            intros τ Hτ. destruct (Htags τ Hτ) as [w' Hv'].
            apply elem_of_cons in Hv' as [[= -> _]|Hv']; [|eauto].
            exfalso. apply Hnotin.
            exact (list_elem_of_fmap_2 fst _ _ Hv0). }
          lia.
      + assert (Hle : length tags ≤ length (bag_pop_ne_vals rest)).
        { apply IH; [done|done|].
          intros τ Hτ. destruct (Htags τ Hτ) as [w' Hv'].
          apply elem_of_cons in Hv' as [[= -> _]|Hv']; [|eauto].
          exfalso. exact (Hτ0_nin Hτ). }
        lia.
  Qed.

  (* Reverse direction: |bag_pop_ne_vals l| ≤ |tags| when every pop-ne tag is in tags *)
  Local Lemma bag_pop_ne_count_le (l : list (positive * trace))
    (tags : list positive) :
    NoDup l.*1 → NoDup tags →
    (∀ τ v w, (τ, Lin Pop v (InjRV w)) ∈ l → τ ∈ tags) →
    length (bag_pop_ne_vals l) ≤ length tags.
  Proof.
    clear. revert tags. induction l as [|[τ0 ev0] rest IH]; intros tags Hnd_l Hnd_tags Htags.
    - simpl. lia.
    - rewrite fmap_cons in Hnd_l.
      apply NoDup_cons in Hnd_l as [Hnotin Hnd_rest].
      rewrite (_ : (τ0, ev0) :: rest = [(τ0, ev0)] ++ rest) // bag_pop_ne_vals_app length_app.
      assert (Hrest_le : ∀ ev, (∀ τ' v' w', (τ', Lin Pop v' (SOMEV w')) ∈ rest → τ' ∈ tags) →
                bag_pop_ne_vals [(τ0, ev)] = [] →
                length (bag_pop_ne_vals rest) ≤ length tags →
                length (bag_pop_ne_vals [(τ0, ev)]) + length (bag_pop_ne_vals rest) ≤ length tags).
      { intros ev' ? ->. simpl. lia. }
      destruct ev0 as [nv_c v_c|nvr vr vr'|v_r].
      { apply Hrest_le.
        - intros ????.
          eapply Htags, elem_of_cons.
          right. eassumption.
        - reflexivity.
        - apply IH; [done..|].
          intros ????.
          eapply Htags, elem_of_cons.
          right. eassumption. }
      2: { apply Hrest_le.
        - intros ????.
          eapply Htags, elem_of_cons.
          right. eassumption.
        - reflexivity.
        - apply IH; [done..|].
          intros ????.
          eapply Htags, elem_of_cons.
          right. eassumption. }
      (* Lin case *)
      destruct nvr as [|[|nvr]]; destruct vr';
        try (rewrite /bag_pop_ne_vals /=; rewrite /bag_pop_ne_vals in IH;
             apply (IH tags); auto; intros τ' v' w' Hin'; eapply Htags; right; exact Hin').
      (* Only Pop × InjRV survives *)
      rewrite bag_pop_ne_vals_pop_ne length_cons length_nil.
      (* change (bag_pop_ne_vals [(τ0, Lin (InjLV v0) (InjRV v1))]) with [v1]. *)
      (* rewrite length_cons length_nil. *)
      assert (Hτ0_in : τ0 ∈ tags).
      { eapply Htags. by left. }
      apply list_elem_of_split in Hτ0_in as (tags1 & tags2 & ->).
      rewrite length_app /=.
      assert (Hle : length (bag_pop_ne_vals rest) ≤ length (tags1 ++ tags2)).
      { apply IH; [done| |].
        - apply NoDup_app in Hnd_tags as (H1 & Hdisj & H2).
          apply NoDup_cons in H2 as [_ H2].
          apply NoDup_app; split; [done|split; [|done]].
          intros x Hx1 Hx2. apply (Hdisj x Hx1). right. exact Hx2.
        - intros τ' v' w' Hin'. apply elem_of_app.
          assert (Hτ'_in : τ' ∈ tags1 ++ τ0 :: tags2).
          { eapply Htags. right. exact Hin'. }
          apply elem_of_app in Hτ'_in as [?|Hτ'_in]; [left; done|].
          apply elem_of_cons in Hτ'_in as [->|?]; [|right; done].
          exfalso. apply Hnotin.
          exact (list_elem_of_fmap_2 fst _ _ Hin'). }
      rewrite length_app in Hle. lia.
  Qed.

  (* A matched pair (τ1,τ2) does not cross a pop-empty τ3 in the Lin trace.
     Proof: if [τ1;τ3;τ2] were a sublist, then τ1 pushed a value before τ3,
     τ3 sees empty bag, but τ1's value hasn't been popped (τ2 is after τ3).
     By [rtcL model_step], the bag at τ3 is non-empty. Contradiction with Pop IsEmpty. *)
  Local Lemma trace_prt_no_cross_match ts' :
    per_tag_wellformed_bag rme valid_value ts →
    ts = filter (not ∘ is_lin ∘ snd) ts' →
    per_tag_linearized ts' →
    NoDup (filter (is_lin ∘ snd) ts').*1 →
    (∃ s', rtcL (model_step (M:=bag_model rme valid_value)) s_init s' (filter (is_lin ∘ snd) ts')) →
    (∀ τ1 τ2, (τ1,τ2) ∈ m → [τ1;τ2] `sublist_of` (filter (is_lin ∘ snd) ts').*1) →
    ∀ τ1 τ2 τ3, (τ1,τ2) ∈ m → τ3 ∈ pop_emp_of_trace ts →
      [τ1;τ2;τ3] `sublist_of` (filter (is_lin ∘ snd) ts').*1
    ∨ [τ3;τ1;τ2] `sublist_of` (filter (is_lin ∘ snd) ts').*1.
  Proof.
    intros Hwf Hfilt Hptl Hnd [s_end Hls] Hval_sub τ1 τ2 τ3 Hin_m Hτ3_pop_emp.
    pose proof Hτ3_pop_emp as Hτ3_pop_emp_orig.
    pose proof Hfilt as Hfilt_orig.
    set lts := filter (is_lin ∘ snd) ts'.
    pose proof (Hval_sub _ _ Hin_m) as Hsub12.
    (* Step 1: τ3 ∈ lts.*1. τ3 ∈ pop_emp_of_trace ts → τ3 has Ret IsEmpty in ts → τ3 ∈ ts.*1. *)
    assert (Hτ3_in_lts : τ3 ∈ lts.*1).
    { apply (τ_in_filter_lin ts' τ3 Hfilt Hptl).
      rewrite /pop_emp_of_trace in Hτ3_pop_emp.
      apply list_elem_of_fmap_1 in Hτ3_pop_emp as ([τ3' ev3] & Heq3 & Hin3).
      simpl in Heq3. subst τ3'.
      apply list_elem_of_filter in Hin3 as [_ Hin3].
      apply (list_elem_of_fmap_2 fst _ (τ3, ev3)). exact Hin3. }
    (* Step 2: Get positions. Use sublist_cons_l on [τ1;τ2] and NoDup to get ordered positions. *)
    (* Use sublist_cons_l to decompose lts.*1 at τ1 and τ2 *)
    apply sublist_cons_l in Hsub12 as (k_before1 & k_after1 & Heq1 & Hsub2_rest).
    apply singleton_sublist_l in Hsub2_rest.
    (* lts.*1 = k_before1 ++ τ1 :: k_after1, τ2 ∈ k_after1 *)
    (* τ3 ∈ lts.*1. By NoDup: τ3 ≠ τ1 and τ3 ≠ τ2 (τ3 is pop-empty, τ1 is push, τ2 is non-empty pop).
       τ3 ∈ k_before1 ∨ τ3 = τ1 ∨ τ3 ∈ k_after1. Since τ3 ≠ τ1: τ3 ∈ k_before1 ∨ τ3 ∈ k_after1. *)
    (* Further decompose k_after1 at τ2: *)
    destruct (list_elem_of_split _ _ Hsub2_rest) as (k_between & k_after2 & Hk_after1_eq).
    (* k_after1 = k_between ++ τ2 :: k_after2 *)
    (* τ3 is in k_before1, k_between, or k_after2 (not τ1 or τ2 by NoDup) *)
    assert (Hτ3_ne_τ1 : τ3 ≠ τ1).
    { intros <-.
      (* τ1 ∈ push_of_trace (from valid_match). τ3 ∈ pop_of_trace (from Hwf + pop_emp).
         push_xor_pop_of_trace gives False. *)
      assert (Hτ3_push : τ3 ∈ push_of_trace ts).
      { destruct Hvalid as (_ & _ & Hforall). rewrite Forall_forall in Hforall.
        destruct (Hforall _ Hin_m) as (_ & _ & v & Hpush_call & _).
        apply (list_elem_of_fmap_2 fst _ (τ3, Call Push v)).
        apply list_elem_of_filter_2; [simpl; eexists; done|exact Hpush_call]. }
      eapply push_xor_pop_of_trace; [exact Hwf|exact Hτ3_push|].
      (* Show τ3 ∈ pop_of_trace ts. τ3 has Ret IsEmpty ∈ ts (from pop_emp_of_trace).
         By Hwf: τ3 can't be push pattern (push Ret = #() ≠ NONEV = IsEmpty).
         So τ3 is pop pattern → has Call Pop → τ3 ∈ pop_of_trace. *)
      rewrite /pop_emp_of_trace in Hτ3_pop_emp.
      apply list_elem_of_fmap_1 in Hτ3_pop_emp as ([τ3' ev3] & Heq3 & Hin3).
      simpl in Heq3. subst τ3'.
      apply list_elem_of_filter in Hin3 as [Hev3 Hin3].
      rewrite /is_ret_pop_emp /= in Hev3. subst ev3.
      destruct (Hwf τ3) as [(w & _ & Hpfx)|(r & _ & Hpfx)].
      - (* push pattern: Ret IsEmpty impossible *)
        exfalso.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ3)) in Hin3; last done.
        pose proof (elem_of_prefix _ _ _ Hin3 Hpfx) as Hp.
        rewrite !elem_of_cons elem_of_nil in Hp.
        destruct Hp as [Hp|[Hp|[]]]; apply (f_equal snd) in Hp; simpl in Hp; discriminate.
      - (* pop pattern: prefix has Call Pop at head → (τ3, Call Pop) ∈ filter ⊆ ts *)
        apply (list_elem_of_fmap_2 fst _ (τ3, Call Pop #())).
        apply list_elem_of_filter_2; [done|].
        (* (τ3, Call Pop) ∈ ts: it's the head of filter(tag=τ3) ts, which is a prefix of [(Call Pop);...] *)
        apply (list_elem_of_filter_2 (λ x, x.1 = τ3)) in Hin3; last done.
        (* filter(tag=τ3) ts is non-empty (contains Hin3). Its head = (τ3, Call Pop) from prefix. *)
        destruct (filter (λ x, x.1 = τ3) ts) as [|hd rest] eqn:Hfilt_eq; first set_solver.
        apply prefix_cons_inv_1 in Hpfx. subst hd.
        apply (list_elem_of_filter_1 (λ x, x.1 = τ3)). rewrite Hfilt_eq. set_solver. }
    assert (Hτ3_ne_τ2 : τ3 ≠ τ2).
    { intros <-.
      (* τ2 ∈ m.*2. From valid_match, τ2 has either (Ret NonEmpty v) or no Ret.
         But τ3 = τ2 means (τ2, Ret IsEmpty) ∈ ts.
         Case 1: (τ2, Ret NonEmpty v) ∈ ts AND (τ2, Ret IsEmpty) ∈ ts.
           By per_tag_complete: only one Ret. encode_response (NonEmpty v) ≠ encode_response IsEmpty.
         Case 2: τ2 ∉ ret_tags. But (τ2, Ret IsEmpty) ∈ ts → τ2 ∈ ret_tags. Contradiction. *)
      destruct Hvalid as (_ & _ & Hforall).
      rewrite Forall_forall in Hforall.
      destruct (Hforall _ Hin_m) as (_ & _ & v & _ & [Hret_ne|Hno_ret]).
      - (* (τ2, Ret NonEmpty v) ∈ ts and (τ2, Ret IsEmpty) ∈ ts. Same tag, 2 Rets. *)
        rewrite /pop_emp_of_trace in Hτ3_pop_emp.
        apply list_elem_of_fmap_1 in Hτ3_pop_emp as ([τ3' ev3] & Heq3 & Hin3).
        simpl in Heq3. subst τ3'.
        apply list_elem_of_filter in Hin3 as [Heq_ev Hin3]. rewrite /is_ret_pop_emp /= in Heq_ev.
        rewrite Heq_ev in Hin3.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ3)) in Hin3; last done.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ3)) in Hret_ne; last done.
        destruct (Hcomplete τ3) as (nvc & vc & vc' & [Heq_c|Heq_c]).
        + rewrite Heq_c in Hin3. set_solver.
        + rewrite Heq_c in Hin3, Hret_ne.
          (* Two Rets for same tag in a 2-element filter → both at position 1 → equal *)
          (* But one is Ret IsEmpty and other is Ret NonEmpty v → discriminate *)
          apply elem_of_cons in Hin3 as [Hin3|Hin3];
            [apply (f_equal snd) in Hin3; simpl in Hin3; discriminate|].
          apply elem_of_cons in Hin3 as [Hin3|Hin3]; last set_solver.
          apply elem_of_cons in Hret_ne as [Hret_ne|Hret_ne];
            [apply (f_equal snd) in Hret_ne; simpl in Hret_ne; discriminate|].
          apply elem_of_cons in Hret_ne as [Hret_ne|Hret_ne]; last set_solver.
          apply (f_equal snd) in Hin3. apply (f_equal snd) in Hret_ne. simpl in *.
          rewrite -Hin3 in Hret_ne. discriminate.
      - (* τ2 has no Ret but τ3 = τ2 has Ret IsEmpty → contradiction *)
        apply Hno_ret.
        rewrite /pop_emp_of_trace in Hτ3_pop_emp.
        apply list_elem_of_fmap_1 in Hτ3_pop_emp as ([τ3' ev3] & Heq3 & Hin3).
        simpl in Heq3. subst τ3'.
        apply list_elem_of_filter in Hin3 as [Heq_ev Hin3]. rewrite /is_ret_pop_emp /= in Heq_ev.
        rewrite Heq_ev in Hin3.
        apply (list_elem_of_fmap_2 fst _ (τ3, Ret (encode_response IsEmpty))).
        apply list_elem_of_filter_2; [simpl; eexists; done|exact Hin3]. }
    rewrite Heq1 Hk_after1_eq in Hτ3_in_lts.
    apply elem_of_app in Hτ3_in_lts as [Hτ3_before|Hτ3_rest].
    { (* τ3 ∈ k_before1 → τ3 before τ1 before τ2 → [τ3;τ1;τ2] sublist *)
      right. rewrite Heq1 Hk_after1_eq.
      (* lts.*1 = k_before1 ++ τ1 :: k_between ++ τ2 :: k_after2 *)
      (* τ3 ∈ k_before1. Need [τ3; τ1; τ2] sublist of this. *)
      destruct (list_elem_of_split _ _ Hτ3_before) as (kb1 & kb2 & Hkb_eq).
      apply sublist_cons_l. exists kb1, (kb2 ++ τ1 :: k_between ++ τ2 :: k_after2).
      rewrite Hkb_eq. split; [by rewrite -!assoc|].
      apply sublist_cons_l. exists kb2, (k_between ++ τ2 :: k_after2).
      split; [done|].
      apply singleton_sublist_l. apply elem_of_app. right. set_solver. }
    apply elem_of_cons in Hτ3_rest as [->|Hτ3_rest]; first done.
    apply elem_of_app in Hτ3_rest as [Hτ3_between|Hτ3_rest].
    { (* τ3 ∈ k_between → τ1 < τ3 < τ2 in lts → cross-match → contradiction *)
      exfalso.
      (* First, find τ3's Lin event in lts *)
      destruct (list_elem_of_split _ _ Hτ3_between) as (kb1 & kb2 & Hkb_eq).
      (* τ3 is at a specific position in lts. Get its Lin event. *)
      assert (Hτ3_in_lts' : τ3 ∈ lts.*1).
      { rewrite Heq1. apply elem_of_app. right. apply elem_of_cons. right.
        rewrite Hk_after1_eq. apply elem_of_app. left. rewrite Hkb_eq.
        apply elem_of_app. right. set_solver. }
      apply list_elem_of_fmap_1 in Hτ3_in_lts' as ([τ3_tag ev_τ3] & Heq_τ3 & Hin_lts_τ3).
      simpl in Heq_τ3. subst τ3_tag.
      apply list_elem_of_filter in Hin_lts_τ3 as [Hlin_ev_τ3 Hin_ts'_τ3].
      (* ev_τ3 is a Lin event for τ3. Split lts at this element. *)
      assert (Hτ3_in_lts_elem : (τ3, ev_τ3) ∈ lts).
      { apply list_elem_of_filter_2; [exact Hlin_ev_τ3|exact Hin_ts'_τ3]. }
      destruct (list_elem_of_split _ _ Hτ3_in_lts_elem)
        as (lts_before & lts_after & Hlts_split).
      (* Split [rtcL model_step] at τ3 *)
      rewrite /lts in Hlts_split. rewrite Hlts_split in Hls.
      destruct ev_τ3 as [|nv_req v_req v_resp|]; simpl in Hlin_ev_τ3; try done.
      apply rtcL_app_inv in Hls as (s_mid & Hls_before & Hls_rest).
      apply rtcL_cons_inv in Hls_rest as (s_after_τ3 & [_ Hrr]%model_step_inv & _).
      assert (Hv_resp : v_resp = encode_response IsEmpty).
      { destruct (Hptl τ3) as (nw & w & w' & Hprefix).
        rewrite /pop_emp_of_trace in Hτ3_pop_emp_orig.
        apply list_elem_of_fmap_1 in Hτ3_pop_emp_orig as ([τ3' ev'] & Heq' & Hin').
        simpl in Heq'. subst τ3'.
        apply list_elem_of_filter in Hin' as [Hev' Hin']. rewrite /is_ret_pop_emp /= in Hev'. rewrite Hev' in Hin'.
        assert (Hin_ts' : (τ3, Ret (encode_response IsEmpty)) ∈ ts').
        { rewrite Hfilt_orig in Hin'.
          apply list_elem_of_filter in Hin' as [_ Hin_ts']. exact Hin_ts'. }
        apply (list_elem_of_filter_2 (λ x, x.1 = τ3)) in Hin_ts'; last done.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ3)) in Hin_ts'_τ3; last done.
        assert (Hw' : w' = encode_response IsEmpty).
        { pose proof (elem_of_prefix _ _ _ Hin_ts' Hprefix) as H1.
          rewrite !elem_of_cons elem_of_nil in H1.
          destruct H1 as [H1|[H1|[H1|[]]]];
            apply (f_equal snd) in H1; simpl in H1;
            first [discriminate H1 | injection H1; done]. }
        assert (Hvresp_eq : v_resp = w').
        { pose proof (elem_of_prefix _ _ _ Hin_ts'_τ3 Hprefix) as H2.
          rewrite !elem_of_cons elem_of_nil in H2.
          destruct H2 as [H2|[H2|[H2|[]]]];
            apply (f_equal snd) in H2; simpl in H2;
            first [discriminate H2 | injection H2; intros <-; done | injection H2; intros _ <-; done]. }
        congruence. }
      assert (Hs_mid_empty : s_mid = ∅).
      { destruct nv_req as [|[|nv_req]]; simpl in Hrr; last done.
        - destruct Hrr as [_ Habs]. rewrite Hv_resp in Habs. discriminate.
        - destruct Hrr as [Hempty|(v' & _ & _ & Habs)].
          + destruct rme; [|done]. destruct Hempty as (Hs & _ & _). exact Hs.
          + rewrite Hv_resp in Habs. discriminate. }
      (* Step 1: τ1 ∈ lts_before.*1 via NoDup_split_unique *)
      assert (Hlts_fmap : lts.*1 = lts_before.*1 ++ τ3 :: lts_after.*1).
      { rewrite /lts Hlts_split fmap_app /=. done. }
      assert (Hbig_eq : lts.*1 = (k_before1 ++ τ1 :: kb1) ++ τ3 :: kb2 ++ τ2 :: k_after2).
      { rewrite Heq1 Hk_after1_eq Hkb_eq. by rewrite -!assoc. }
      assert (Hτ3_notin_prefix : τ3 ∉ k_before1 ++ τ1 :: kb1).
      { pose proof Hnd as Hnd'. rewrite Hbig_eq in Hnd'.
        apply NoDup_app in Hnd' as (_ & Hdisj & _).
        intro H. apply (Hdisj _ H). left. }
      assert (Hτ3_notin_before : τ3 ∉ lts_before.*1).
      { pose proof Hnd as Hnd'. rewrite Hlts_fmap in Hnd'.
        apply NoDup_app in Hnd' as (_ & Hdisj & _).
        intro H. apply (Hdisj _ H). left. }
      assert (Hbefore_eq : lts_before.*1 = k_before1 ++ τ1 :: kb1).
      { exact (NoDup_split_unique _ _ _ _ _ _ Hnd Hlts_fmap Hbig_eq
                Hτ3_notin_before Hτ3_notin_prefix). }
      assert (Hτ1_in_before : τ1 ∈ lts_before.*1).
      { rewrite Hbefore_eq. apply elem_of_app. right. left. }
      (* Step 2: τ2 ∈ lts_after.*1 *)
      assert (Hτ2_in_after : τ2 ∈ lts_after.*1).
      { assert (Hafter_eq : lts_after.*1 = kb2 ++ τ2 :: k_after2).
        { assert (Htmp : lts_before.*1 ++ τ3 :: lts_after.*1 =
                         lts_before.*1 ++ τ3 :: kb2 ++ τ2 :: k_after2).
          { rewrite -Hlts_fmap Hbig_eq Hbefore_eq. done. }
          by apply app_inv_head, (inj (cons τ3)) in Htmp. }
        rewrite Hafter_eq. apply elem_of_app. right. left. }
      (* Step 3: τ2 ∉ lts_before.*1 *)
      assert (Hτ2_notin_before : τ2 ∉ lts_before.*1).
      { rewrite Hlts_fmap in Hnd. apply NoDup_app in Hnd as (_ & Hdisj & _).
        intro H. apply (Hdisj _ H). right. exact Hτ2_in_after. }
      (* Step 4: counting — #pushes = #pops in lts_before *)
      assert (Hcount : length (bag_push_vals lts_before) = length (bag_pop_ne_vals lts_before)).
      { assert (Hbal := model_steps_bag_size_balance _ _ _ Hls_before).
        change (@linear.S (bag_model rme valid_value)) with (gmultiset val) in Hbal.
        rewrite Hs_mid_empty gmultiset_size_empty in Hbal.
        assert (Hsz0 : size (@s_init (bag_model rme valid_value)) = 0).
        { change (@s_init (bag_model rme valid_value)) with (∅ : gmultiset val).
          apply gmultiset_size_empty. }
        lia. }
      (* Step 5: Contradiction via counting + strict subset. *)
      assert (Hnd_m1 : NoDup m.*1) by (destruct Hvalid as (_ & (? & _) & _); done).
      set (m_before := filter (λ p : positive * positive, p.2 ∈ lts_before.*1) m).
      assert (Hmb1_in : ∀ τ, τ ∈ m_before.*1 → τ ∈ lts_before.*1).
      { intros τ Hτ. apply list_elem_of_fmap_1 in Hτ as ([τ' τ''] & Heq_τ & Hin_mb).
        simpl in Heq_τ. subst τ'. apply list_elem_of_filter in Hin_mb as [Hτ''_in Hin_m'].
        (* (τ, τ'') ∈ m, τ'' ∈ lts_before.*1. By sublist_pair_in_prefix: τ ∈ lts_before.*1 *)
        apply (sublist_pair_in_prefix τ τ'' lts_before.*1 (τ3 :: lts_after.*1)).
        - rewrite -Hlts_fmap. exact (Hval_sub _ _ Hin_m').
        - rewrite -Hlts_fmap. exact Hnd.
        - exact Hτ''_in. }
      assert (Hτ1_notin_mb1 : τ1 ∉ m_before.*1).
      { intro H. apply list_elem_of_fmap_1 in H as ([τ1' τ''] & Heq_τ & Hin_mb).
        simpl in Heq_τ. subst τ1'.
        apply list_elem_of_filter in Hin_mb as [Hτ''_in Hin_m'].
        (* (τ1, τ'') ∈ m and (τ1, τ2) ∈ m. NoDup m.*1 → τ'' = τ2. *)
        assert (τ'' = τ2).
        { apply list_elem_of_lookup_1 in Hin_m' as [i Hi].
          apply list_elem_of_lookup_1 in Hin_m as [j Hj].
          assert (Hi' : m.*1 !! i = Some τ1) by (rewrite list_lookup_fmap Hi; done).
          assert (Hj' : m.*1 !! j = Some τ1) by (rewrite list_lookup_fmap Hj; done).
          assert (i = j) by (eapply NoDup_lookup; eassumption).
          subst j. rewrite Hi in Hj. by injection Hj. }
        subst τ''. exact (Hτ2_notin_before Hτ''_in). }
      assert (Hnd_mb1 : NoDup m_before.*1).
      { (* NoDup (filter P m).*1 from NoDup m.*1 *)
        apply NoDup_fmap_1 in Hnd_m1.
        apply NoDup_fmap_2_strong, NoDup_filter, Hnd_m1.
        clear -Hvalid. subst m_before.
        intros [τ1 τ2] [τ1' τ2'] Hin1 Hin2 Heq.
        simpl in Heq. subst τ1'.
        apply list_elem_of_filter_1 in Hin1,Hin2.
        apply list_elem_of_lookup_1 in Hin1 as [i Hlookup1].
        apply list_elem_of_lookup_1 in Hin2 as [j Hlookup2].
        destruct Hvalid as (_ & [Hnodup _] & _).
        destruct (decide (i = j)) as [<- | Hi_ne_j];
          last destruct (decide (i < j)) as [Hi_lt_j | Hi_gt_j].
        - rewrite Hlookup2 in Hlookup1. injection Hlookup1 as ->. done.
        - exfalso.
          pose proof (Heq_m := take_drop_middle _ _ _ Hlookup2).
          rewrite -(lookup_take_lt _ j) in Hlookup1; last lia.
          destruct (list_elem_of_split_length _ _ _ Hlookup1) as (l1 & l2 & Heq & _).
          rewrite Heq in Heq_m.
          rewrite -assoc -app_comm_cons in Heq_m.
          apply (f_equal (fmap fst)) in Heq_m.
          rewrite fmap_app fmap_cons fmap_app fmap_cons /= in Heq_m.
          rewrite -Heq_m in Hnodup.
          apply NoDup_app in Hnodup as (_ & _ & Hnodup).
          apply NoDup_cons in Hnodup as (Hnot_in & _).
          apply Hnot_in.
          set_solver.
        - exfalso.
          pose proof (Heq_m := take_drop_middle _ _ _ Hlookup1).
          rewrite -(lookup_take_lt _ i) in Hlookup2; last lia.
          destruct (list_elem_of_split_length _ _ _ Hlookup2) as (l1 & l2 & Heq & _).
          rewrite Heq in Heq_m.
          rewrite -assoc -app_comm_cons in Heq_m.
          apply (f_equal (fmap fst)) in Heq_m.
          rewrite fmap_app fmap_cons fmap_app fmap_cons /= in Heq_m.
          rewrite -Heq_m in Hnodup.
          apply NoDup_app in Hnodup as (_ & _ & Hnodup).
          apply NoDup_cons in Hnodup as (Hnot_in & _).
          apply Hnot_in.
          set_solver. }
      assert (Hnd_before : NoDup lts_before.*1).
      { pose proof Hnd as Hnd'. rewrite Hlts_fmap in Hnd'.
        by apply NoDup_app in Hnd' as (? & _ & _). }
      (* m_before.*1 ⊆+ lts_before.*1 *)
      assert (Hsub_mb : m_before.*1 ⊆+ lts_before.*1).
      { apply NoDup_submseteq; [exact Hnd_mb1|exact Hmb1_in]. }
      (* Key facts for the counting contradiction *)
      (* Every pop-ne tag in lts_before is in m.*2 and hence in m_before.*2 *)
      (* Helper: for a Lin event in lts, derive the Ret in ts with matching value *)
      assert (Hlin_ret : ∀ τ0 nvr vr vr', (τ0, Lin nvr vr vr') ∈ lts →
                (τ0, Ret vr') ∈ ts).
      { intros τ0 nvr vr vr' Hin_lts0.
        apply list_elem_of_filter in Hin_lts0 as [_ Hin_ts'0].
        destruct (Hptl τ0) as (nw0 & w0 & w0' & Hprefix0).
        apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hin_ts'0 as Hfilt0; last done.
        pose proof (elem_of_prefix _ _ _ Hfilt0 Hprefix0) as Hmem.
        rewrite !elem_of_cons elem_of_nil in Hmem.
        destruct Hmem as [Hmem|[Hmem|[Hmem|[]]]];
          apply (f_equal snd) in Hmem; simpl in Hmem; try discriminate.
        injection Hmem as Heq_nw0 Heq_w0 Heq_w0'. subst nw0 w0 w0'.
        assert (Hcall_ts0 : (τ0, Call nvr vr) ∈ ts).
        { assert (Hlin_filt : (τ0, Lin nvr vr vr') ∈ filter (λ x, x.1 = τ0) ts').
          { apply list_elem_of_filter_2; done. }
          set (ft := filter (λ x : positive * trace, x.1 = τ0) ts') in *.
          destruct ft as [|c1 rest_f] eqn:Hf.
          { set_solver. }
          assert (Hc1 : c1 = (τ0, Call nvr vr)).
          { exact (prefix_cons_inv_1 _ _ _ _ Hprefix0). }
          rewrite Hfilt_orig. apply list_elem_of_filter_2; [compute_done|].
          apply (list_elem_of_filter_1 (λ x, x.1 = τ0)). subst ft c1. rewrite Hf. clear. set_solver. }
        destruct (Hcomplete τ0) as (nvc & vc & vc' & [Heq_c|Heq_c]).
        - exfalso. apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hcall_ts0; last done.
          rewrite Heq_c in Hcall_ts0. clear -Hcall_ts0. set_solver.
        - assert (Hvc' : vc' = vr').
          { rewrite Hfilt_orig list_filter_comm in Heq_c.
            pose proof (prefix_filter (not ∘ is_lin ∘ snd) _ _ Hprefix0) as Hpfx.
            rewrite filter_cons_True in Hpfx; last compute_done.
            rewrite filter_cons_False in Hpfx; last compute_done.
            rewrite filter_cons_True in Hpfx; last compute_done.
            rewrite filter_nil in Hpfx. rewrite Heq_c in Hpfx.
            apply prefix_cons_inv_2 in Hpfx.
            apply prefix_cons_inv_1 in Hpfx. by injection Hpfx. }
          subst vc'. apply (list_elem_of_filter_1 (λ x, x.1 = τ0)).
          rewrite Heq_c. clear. set_solver. }
      (* Every pop-ne tag in lts_before is in m_before.*2 *)
      assert (Hpop_ne_in_mb2 : ∀ τ' w, (τ', Lin Pop #() (SOMEV w)) ∈ lts_before →
                                         τ' ∈ m_before.*2).
      { intros τ' w Hin_before0.
        assert (Hin_lts0 : (τ', Lin Pop #() (SOMEV w)) ∈ lts).
        { rewrite /lts Hlts_split. apply elem_of_app. left. exact Hin_before0. }
        assert (Hret : (τ', Ret (SOMEV w)) ∈ ts).
        { exact (Hlin_ret _ _ _ _ Hin_lts0). }
        assert (Hτ'_m2 : τ' ∈ m.*2).
        { destruct Hvalid as (Hpvt_sub & _). apply Hpvt_sub.
          apply (list_elem_of_fmap_2 fst _ (τ', Ret (SOMEV w))).
          apply list_elem_of_filter_2; [|exact Hret].
          rewrite /is_ret_pop_val. eexists. done. }
        apply list_elem_of_fmap_1 in Hτ'_m2 as ([τ_push τ_pop'] & Heq_τ & Hin_m0).
        simpl in Heq_τ. subst τ_pop'.
        apply (list_elem_of_fmap_2 snd _ (τ_push, τ')).
        apply list_elem_of_filter_2; [|exact Hin_m0].
        simpl. apply (list_elem_of_fmap_2 fst _ (τ', Lin Pop #() (SOMEV w))).
        exact Hin_before0. }
      (* NoDup m_before.*2 — same pattern as Hnd_mb1 *)
      assert (Hnd_m2 : NoDup m.*2) by (destruct Hvalid as (_ & (_ & ?) & _); done).
      assert (Hnd_mb2 : NoDup m_before.*2).
      { apply NoDup_fmap_1 in Hnd_m2.
        apply NoDup_fmap_2_strong, NoDup_filter, Hnd_m2.
        clear -Hvalid. subst m_before.
        intros [a1 b1] [a2 b2] Hin1 Hin2 Heq. simpl in Heq. subst b2.
        apply list_elem_of_filter_1 in Hin1,Hin2.
        apply list_elem_of_lookup_1 in Hin1 as [i Hlookup1].
        apply list_elem_of_lookup_1 in Hin2 as [j Hlookup2].
        destruct Hvalid as (_ & [_ Hnodup] & _).
        destruct (decide (i = j)) as [<- | Hi_ne_j];
          last destruct (decide (i < j)) as [Hi_lt_j | Hi_gt_j].
        - rewrite Hlookup2 in Hlookup1. injection Hlookup1 as ->. done.
        - exfalso. pose proof (Heq_m := take_drop_middle _ _ _ Hlookup2).
          rewrite -(lookup_take_lt _ j) in Hlookup1; last lia.
          destruct (list_elem_of_split_length _ _ _ Hlookup1) as (l1 & l2 & Heq & _).
          rewrite Heq -assoc -app_comm_cons in Heq_m.
          apply (f_equal (fmap snd)) in Heq_m.
          rewrite fmap_app fmap_cons fmap_app fmap_cons /= in Heq_m.
          rewrite -Heq_m in Hnodup. apply NoDup_app in Hnodup as (_ & _ & Hnodup).
          apply NoDup_cons in Hnodup as (Hnot_in & _). apply Hnot_in. set_solver.
        - exfalso. pose proof (Heq_m := take_drop_middle _ _ _ Hlookup1).
          rewrite -(lookup_take_lt _ i) in Hlookup2; last lia.
          destruct (list_elem_of_split_length _ _ _ Hlookup2) as (l1 & l2 & Heq & _).
          rewrite Heq -assoc -app_comm_cons in Heq_m.
          apply (f_equal (fmap snd)) in Heq_m.
          rewrite fmap_app fmap_cons fmap_app fmap_cons /= in Heq_m.
          rewrite -Heq_m in Hnodup. apply NoDup_app in Hnodup as (_ & _ & Hnodup).
          apply NoDup_cons in Hnodup as (Hnot_in & _). apply Hnot_in. set_solver. }
      (* Helper: omap tag extraction from push/pop-ne events *)
      (* For (τ, Lin (InjRV v) #()) ∈ l, τ ∈ bag_push_vals l *)
      assert (Hpush_in_vals : ∀ l τ0 v0,
        (τ0, Lin Push v0 (LitV LitUnit)) ∈ l → v0 ∈ bag_push_vals l).
      { clear. intros l τ0 v0. induction l as [|[τ' ev'] rest IH]; first set_solver.
        rewrite elem_of_cons. intros [Heq|Hin].
        - injection Heq as <- <-. unfold bag_push_vals. simpl.
          apply elem_of_cons. left. done.
        - specialize (IH Hin).
          change ((τ',ev')::rest) with ([(τ',ev')]++rest).
          rewrite /bag_push_vals omap_app.
          rewrite /bag_push_vals in IH.
          set_solver. }
      (* For (τ, Lin (InjLV _) (InjRV w)) ∈ l, w ∈ bag_pop_ne_vals l *)
      assert (Hpop_in_vals : ∀ l τ0 v0 w0,
        (τ0, Lin Pop v0 (InjRV w0)) ∈ l → w0 ∈ bag_pop_ne_vals l).
      { clear. intros l τ0 v0 w0. induction l as [|[τ' ev'] rest IH]; first set_solver.
        rewrite elem_of_cons. intros [Heq|Hin].
        - injection Heq as <- <-. unfold bag_pop_ne_vals. simpl.
          apply elem_of_cons. left. done.
        - specialize (IH Hin).
          change ((τ',ev')::rest) with ([(τ',ev')]++rest).
          rewrite /bag_pop_ne_vals omap_app.
          rewrite /bag_pop_ne_vals in IH.
          set_solver. }
      (* Hlower: |bag_pop_ne_vals lts_before| ≤ |m_before| *)
      (* Every pop-ne event adds to bag_pop_ne_vals and its tag is in m_before.*2.
         Since NoDup m_before.*2 and the tags are distinct: |pop-ne events| ≤ |m_before|. *)
      assert (Hlower : length (bag_pop_ne_vals lts_before) ≤ length m_before).
      { rewrite -(length_fmap snd m_before).
        apply (bag_pop_ne_count_le lts_before m_before.*2).
        - exact Hnd_before.
        - exact Hnd_mb2.
        - intros τ0 v0 w0 Hin0.
          assert (v0 = #()) as ->.
          { clear -Hin0 Hls_before.
            apply model_steps_valid_request in Hls_before.
            rewrite Forall_forall in Hls_before.
            exact (Hls_before _ Hin0). }
          exact (Hpop_ne_in_mb2 τ0 w0 Hin0). }
      (* Hupper: 1 + |m_before| ≤ |bag_push_vals lts_before| *)
      (* Each matched push and τ1 contribute a distinct value to bag_push_vals *)
      assert (Hupper : 1 + length m_before ≤ length (bag_push_vals lts_before)).
      { (* Show each τ ∈ m_before.*1 has push Lin event, extract its value *)
        assert (Hmb1_val : ∀ τ0, τ0 ∈ m_before.*1 →
                  ∃ v0, v0 ∈ bag_push_vals lts_before ∧
                        (τ0, Lin Push v0 #()) ∈ lts_before).
        { intros τ0 Hτ0.
          assert (Hτ0_in : τ0 ∈ lts_before.*1) by exact (Hmb1_in τ0 Hτ0).
          apply list_elem_of_fmap_1 in Hτ0 as ([τ0' τ''] & Heqτ0 & Hin_mb0).
          simpl in Heqτ0. subst τ0'.
          apply list_elem_of_filter in Hin_mb0 as [_ Hin_m0].
          destruct (valid_match_call_push ts m τ0 τ'' Hvalid Hin_m0) as [v0 Hcall].
          apply list_elem_of_fmap_1 in Hτ0_in as ([τ0'' ev0] & Heqτ0' & Hin0).
          simpl in Heqτ0'. subst τ0''.
          assert (Hin_lts0 : (τ0, ev0) ∈ lts).
          { rewrite /lts Hlts_split. apply elem_of_app. left. exact Hin0. }
          pose proof Hin_lts0 as Hin_lts0'.
          apply list_elem_of_filter in Hin_lts0 as [Hlin0 Hin_ts'00].
          destruct ev0 as [|nvr00 vr00 vr00'|]; simpl in Hlin0; try done.
          assert (Hret0 := Hlin_ret τ0 nvr00 vr00 vr00' Hin_lts0').
          destruct (Hwf τ0) as [(vw & _ & Hpfx_push)|(vw & _ & Hpfx_pop)].
          - apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hcall; last done.
            apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hret0; last done.
            pose proof (elem_of_prefix _ _ _ Hcall Hpfx_push) as Hm1.
            pose proof (elem_of_prefix _ _ _ Hret0 Hpfx_push) as Hm2.
            rewrite !elem_of_cons !elem_of_nil !right_id in Hm1, Hm2.
            destruct Hm1 as [Hm1|Hm1];
              [|apply (f_equal snd) in Hm1; simpl in Hm1; discriminate].
            destruct Hm2 as [Hm2|Hm2];
              try (apply (f_equal snd) in Hm2; simpl in Hm2; discriminate).
            (* Derive nvr00 = Push and vr00 = vw from two prefix constraints *)
            assert (Hvr : nvr00 = Push ∧ vr00 = vw).
            { (* the Call of τ0 fixes the head of the per_tag_linearized prefix *)
              destruct (Hptl τ0) as (nw0c & w0c & w0c' & Hpfx0c).
              assert (Hcall_ts' : (τ0, Call Push v0) ∈ ts').
              { apply list_elem_of_filter_1 in Hcall. rewrite Hfilt_orig in Hcall.
                exact (list_elem_of_filter_1 _ _ _ Hcall). }
              apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hcall_ts'; last done.
              pose proof (elem_of_prefix _ _ _ Hcall_ts' Hpfx0c) as Hpos.
              rewrite !elem_of_cons elem_of_nil in Hpos.
              destruct Hpos as [Hpos|[Hpos|[Hpos|[]]]];
                try (apply (f_equal snd) in Hpos; simpl in Hpos; discriminate).
              apply (f_equal snd) in Hpos. simpl in Hpos. injection Hpos as <- <-.
              (* Now the Lin of the prefix is [Lin Push v0 w0c'] *)
              assert (Hlin_in : (τ0, Lin nvr00 vr00 vr00') ∈ filter (λ x, x.1 = τ0) ts').
              { apply list_elem_of_filter_2; [done|exact Hin_ts'00]. }
              pose proof (elem_of_prefix _ _ _ Hlin_in Hpfx0c) as Hpos2.
              rewrite !elem_of_cons elem_of_nil in Hpos2.
              destruct Hpos2 as [Hpos2|[Hpos2|[Hpos2|[]]]];
                try (apply (f_equal snd) in Hpos2; simpl in Hpos2; discriminate).
              apply (f_equal snd) in Hpos2. simpl in Hpos2.
              injection Hpos2 as -> -> _.
              assert (Hvr_eq2 : v0 = vw).
              { apply (f_equal snd) in Hm1. simpl in Hm1. injection Hm1; done. }
              split; [done|exact Hvr_eq2]. }
            assert (Hvr_eq3 : vr00' = #()).
            { apply (f_equal snd) in Hm2. simpl in Hm2. injection Hm2; done. }
            destruct Hvr as [-> ->]. subst vr00'.
            exists vw. split; [exact (Hpush_in_vals _ _ _ Hin0)|exact Hin0].
          - exfalso.
            apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hcall; last done.
            pose proof (elem_of_prefix _ _ _ Hcall Hpfx_pop) as Hm1.
            rewrite !elem_of_cons elem_of_nil right_id in Hm1.
            destruct Hm1 as [Hm1|Hm1];
              apply (f_equal snd) in Hm1; simpl in Hm1; discriminate. }
        (* τ1 also has a push value in bag_push_vals *)
        assert (Hτ1_val : ∃ v0, v0 ∈ bag_push_vals lts_before ∧
                                 (τ1, Lin Push v0 #()) ∈ lts_before).
        { destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [v0 Hcall].
          apply list_elem_of_fmap_1 in Hτ1_in_before as ([τ1'' ev0] & Heqτ1 & Hin0).
          simpl in Heqτ1. subst τ1''.
          assert (Hin_lts0 : (τ1, ev0) ∈ lts).
          { rewrite /lts Hlts_split. apply elem_of_app. left. exact Hin0. }
          pose proof Hin_lts0 as Hin_lts0'.
          apply list_elem_of_filter in Hin_lts0 as [Hlin0 Hin_ts'01].
          destruct ev0 as [|nvr01 vr01 vr01'|]; simpl in Hlin0; try done.
          assert (Hret0 := Hlin_ret τ1 nvr01 vr01 vr01' Hin_lts0').
          destruct (Hwf τ1) as [(vw & _ & Hpfx_push)|(vw & _ & Hpfx_pop)].
          - apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall; last done.
            apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hret0; last done.
            pose proof (elem_of_prefix _ _ _ Hcall Hpfx_push) as Hm1.
            pose proof (elem_of_prefix _ _ _ Hret0 Hpfx_push) as Hm2.
            rewrite !elem_of_cons !elem_of_nil !right_id in Hm1, Hm2.
            destruct Hm1 as [Hm1|Hm1];
              [|apply (f_equal snd) in Hm1; simpl in Hm1; discriminate].
            destruct Hm2 as [Hm2|Hm2];
              try (apply (f_equal snd) in Hm2; simpl in Hm2; discriminate).
            assert (Hvr : nvr01 = Push ∧ vr01 = vw).
            { destruct (Hptl τ1) as (nw0c & w0c & w0c' & Hpfx0c).
              assert (Hcall_ts' : (τ1, Call Push v0) ∈ ts').
              { apply list_elem_of_filter_1 in Hcall. rewrite Hfilt_orig in Hcall.
                exact (list_elem_of_filter_1 _ _ _ Hcall). }
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_ts'; last done.
              pose proof (elem_of_prefix _ _ _ Hcall_ts' Hpfx0c) as Hpos.
              rewrite !elem_of_cons elem_of_nil in Hpos.
              destruct Hpos as [Hpos|[Hpos|[Hpos|[]]]];
                try (apply (f_equal snd) in Hpos; simpl in Hpos; discriminate).
              apply (f_equal snd) in Hpos. simpl in Hpos. injection Hpos as <- <-.
              assert (Hlin_in : (τ1, Lin nvr01 vr01 vr01') ∈ filter (λ x, x.1 = τ1) ts').
              { apply list_elem_of_filter_2; [done|exact Hin_ts'01]. }
              pose proof (elem_of_prefix _ _ _ Hlin_in Hpfx0c) as Hpos2.
              rewrite !elem_of_cons elem_of_nil in Hpos2.
              destruct Hpos2 as [Hpos2|[Hpos2|[Hpos2|[]]]];
                try (apply (f_equal snd) in Hpos2; simpl in Hpos2; discriminate).
              apply (f_equal snd) in Hpos2. simpl in Hpos2.
              injection Hpos2 as -> -> _.
              assert (Hvr_eq2 : v0 = vw) by (apply (f_equal snd) in Hm1; simpl in Hm1; injection Hm1; done).
              split; [done|exact Hvr_eq2]. }
            assert (Hvr' : vr01' = #()) by (apply (f_equal snd) in Hm2; simpl in Hm2; injection Hm2; done).
            destruct Hvr as [-> ->]. subst vr01'.
            exists vw. split; [exact (Hpush_in_vals _ _ _ Hin0)|exact Hin0].
          - exfalso.
            apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall; last done.
            pose proof (elem_of_prefix _ _ _ Hcall Hpfx_pop) as Hm1.
            rewrite !elem_of_cons elem_of_nil right_id in Hm1.
            destruct Hm1 as [Hm1|Hm1];
              apply (f_equal snd) in Hm1; simpl in Hm1; discriminate. }
        (* Use push_tags_count_le with τ1 :: m_before.*1 *)
        assert (Hlen_eq : 1 + length m_before = length (τ1 :: m_before.*1)).
        { simpl. rewrite length_fmap. lia. }
        rewrite Hlen_eq.
        apply (push_tags_count_le lts_before (τ1 :: m_before.*1)).
        - exact Hnd_before.
        - constructor; [exact Hτ1_notin_mb1|exact Hnd_mb1].
        - intros τ0 Hτ0. rewrite elem_of_cons in Hτ0.
          destruct Hτ0 as [->|Hτ0].
          + destruct Hτ1_val as [v0 [_ Hv0_ev]]. eauto.
          + destruct (Hmb1_val _ Hτ0) as [v0 [_ Hv0_ev]]. eauto. }
      lia. }
    apply elem_of_cons in Hτ3_rest as [->|Hτ3_after]; first done.
    { (* τ3 ∈ k_after2 → τ1 before τ2 before τ3 → [τ1;τ2;τ3] sublist *)
      left. apply sublist_cons_l. exists k_before1, (k_between ++ τ2 :: k_after2).
      rewrite Heq1 Hk_after1_eq. split; [done|].
      apply sublist_cons_l. eexists _, _. split; [done|].
      apply singleton_sublist_l. exact Hτ3_after. }
  Qed.

  (* Helper: extract prt ordering from a 3-element sublist *)
  Local Lemma sublist3_prt ts'₀ τ_a τ_b τ_c :
    per_tag_linearized ts'₀ →
    NoDup (filter (is_lin ∘ snd) ts'₀).*1 →
    [τ_a; τ_b; τ_c] `sublist_of` (filter (is_lin ∘ snd) ts'₀).*1 →
    prt_of_trace ts'₀ τ_a τ_b ∧ prt_of_trace ts'₀ τ_b τ_c ∧ prt_of_trace ts'₀ τ_a τ_c.
  Proof.
    clear.
    intros Hptl Hnd Hsub.
    (* Extract 2-element sublists from the 3-element one *)
    (* [a;b;c] = [a;b] ++ [c]. By sublist_app_l: split into k1++k2 with [a;b] sub k1, [c] sub k2.
       [a;b] sub k1 sub full → [a;b] sub full. Similarly [b;c] and [a;c]. *)
    apply sublist_cons_l in Hsub as (k1_a & k2_a & Heq_a & Hsub_bc_rest).
    apply sublist_cons_l in Hsub_bc_rest as (k1_b & k2_b & Heq_b & Hsub_c_rest).
    apply singleton_sublist_l in Hsub_c_rest.
    assert (Hsub_ab : [τ_a; τ_b] `sublist_of` (filter (is_lin ∘ snd) ts'₀).*1).
    { apply sublist_cons_l. exists k1_a, (k1_b ++ τ_b :: k2_b).
      rewrite Heq_a Heq_b. split; [done|].
      apply singleton_sublist_l. apply elem_of_app. right. set_solver. }
    assert (Hsub_bc : [τ_b; τ_c] `sublist_of` (filter (is_lin ∘ snd) ts'₀).*1).
    { apply sublist_cons_l. exists (k1_a ++ τ_a :: k1_b), k2_b.
      rewrite Heq_a Heq_b. split; [by rewrite -assoc|].
      apply singleton_sublist_l. exact Hsub_c_rest. }
    assert (Hsub_ac : [τ_a; τ_c] `sublist_of` (filter (is_lin ∘ snd) ts'₀).*1).
    { apply sublist_cons_l. exists k1_a, (k1_b ++ τ_b :: k2_b).
      rewrite Heq_a Heq_b. split; [done|].
      apply singleton_sublist_l. apply elem_of_app. right. set_solver. }
    destruct (sublist_lin_order _ _ _ Hptl Hnd Hsub_ab) as (pa&xa&pb&xb&Ha&Hb&Hlt_ab).
    destruct (sublist_lin_order _ _ _ Hptl Hnd Hsub_bc) as (pb'&xb'&pc&xc&Hb'&Hc&Hlt_bc).
    destruct (sublist_lin_order _ _ _ Hptl Hnd Hsub_ac) as (pa'&xa'&pc'&xc'&Ha'&Hc'&Hlt_ac).
    (* Unify duplicate results *)
    rewrite Ha in Ha'. injection Ha' as <- <-.
    rewrite Hb in Hb'. injection Hb' as <- <-.
    rewrite Hc in Hc'. injection Hc' as <- <-.
    (* prt_of_trace uses lin_of_tag which is list_find. Rewrite directly. *)
    unfold prt_of_trace, lin_of_tag in *.
    rewrite Ha Hb Hc /=.
    split_and!; lia.
  Qed.

  Lemma trace_pre_prt_subrelation ts' :
    ts = filter (not ∘ is_lin ∘ snd) ts' →
    per_tag_linearized ts' →
    subrelation trace_pre (trace_prt ts').
  Proof.
    intros Hfilter Hptl [τ1 Hτ1_in] [τ2 Hτ2_in].
    rewrite /trace_pre /trace_prt /pre_of_trace /prt_of_trace /=.
    intros Hpre.
    destruct (ret_of_tag ts τ1) as [[ret1 p_ret]|] eqn:Hret1; last done.
    destruct (call_of_tag ts τ2) as [[call2 p_call]|] eqn:Hcall2; last done.
    simpl in Hpre.
    rewrite /events_of_trace !elem_of_list_to_set in Hτ1_in, Hτ2_in.
    pose proof (τ_in_filter_lin ts' τ1 Hfilter Hptl Hτ1_in) as Hτ1_lin.
    pose proof (τ_in_filter_lin ts' τ2 Hfilter Hptl Hτ2_in) as Hτ2_lin.
    apply list_elem_of_fmap_1 in Hτ1_lin as ([τ1a t1a] & Heq1a & Hin1a).
    simpl in Heq1a. subst τ1a.
    apply list_elem_of_fmap_1 in Hτ2_lin as ([τ2a t2a] & Heq2a & Hin2a).
    simpl in Heq2a. subst τ2a.
    apply list_elem_of_filter in Hin1a as [Hlin_t1a Hin1a_ts'].
    apply list_elem_of_filter in Hin2a as [Hlin_t2a Hin2a_ts'].
    opose proof (list_find_exists_Some (λ x, x.1 = τ1 ∧ is_lin x.2) ts' _)
      as (lin1 & [τ1b lt1] & Hlin_tag1).
    { exists (τ1, t1a). split_and!; done. }
    rewrite -/(lin_of_tag ts' τ1) in Hlin_tag1.
    opose proof (list_find_exists_Some (λ x, x.1 = τ2 ∧ is_lin x.2) ts' _)
      as (lin2 & [τ2b lt2] & Hlin_tag2).
    { exists (τ2, t2a). split_and!; done. }
    rewrite -/(lin_of_tag ts' τ2) in Hlin_tag2.
    rewrite /prt_of_trace Hlin_tag1 Hlin_tag2 /=.
    (* Goal: lin1 < lin2. Proof by contradiction. *)
    destruct (decide (lin1 < lin2)) as [Hlt_done|Hnlt]; first lia.
    exfalso.
    assert (Hle : lin2 ≤ lin1) by lia.
    (* Extract list_find_Some facts *)
    apply list_find_Some in Hlin_tag1 as (Hlt1_lookup & [Hlt1_tag Hlt1_islin] & Hlt1_min).
    simpl in Hlt1_tag. subst τ1b.
    apply list_find_Some in Hlin_tag2 as (Hlt2_lookup & [Hlt2_tag Hlt2_islin] & Hlt2_min).
    simpl in Hlt2_tag. subst τ2b.
    apply list_find_Some in Hret1 as (Hret1_lookup & [Hret1_tag Hret1_isret] & _).
    simpl in Hret1_tag.
    apply list_find_Some in Hcall2 as (Hcall2_lookup & [Hcall2_tag Hcall2_iscall] & _).
    simpl in Hcall2_tag.
    (* Per_tag_linearized for τ1, τ2 *)
    destruct (Hptl τ1) as (nv1 & v1 & v1' & Hptl_τ1).
    destruct (Hptl τ2) as (nv2 & v2 & v2' & Hptl_τ2).
    (* Determine p_ret = (τ1, Ret v1') *)
    assert (Hp_ret_in_ts' : p_ret ∈ ts').
    { rewrite Hfilter in Hret1_lookup.
      exact (list_filter_lookup_orig _ _ _ _ Hret1_lookup). }
    assert (Hp_ret_eq : p_ret = (τ1, Ret v1')).
    { assert (Hp_ret_filt : p_ret ∈ filter (λ t, t.1 = τ1) ts').
      { apply list_elem_of_filter_2; [exact Hret1_tag|exact Hp_ret_in_ts']. }
      pose proof (elem_of_prefix _ _ _ Hp_ret_filt Hptl_τ1) as Hcases.
      rewrite !elem_of_cons elem_of_nil right_id in Hcases.
      destruct Hcases as [Hcase|[Hcase|Hcase]]; [| |exact Hcase];
        exfalso; subst p_ret; simpl in Hret1_isret; done. }
    (* Determine p_call = (τ2, Call nv2 v2) *)
    assert (Hp_call_in_ts' : p_call ∈ ts').
    { rewrite Hfilter in Hcall2_lookup.
      exact (list_filter_lookup_orig _ _ _ _ Hcall2_lookup). }
    assert (Hp_call_eq : p_call = (τ2, Call nv2 v2)).
    { assert (Hp_call_filt : p_call ∈ filter (λ t, t.1 = τ2) ts').
      { apply list_elem_of_filter_2; [exact Hcall2_tag|exact Hp_call_in_ts']. }
      pose proof (elem_of_prefix _ _ _ Hp_call_filt Hptl_τ2) as Hcases.
      rewrite !elem_of_cons elem_of_nil in Hcases.
      destruct Hcases as [Hcase|[Hcase|[Hcase|]]]; [exact Hcase| | |done];
        exfalso; subst p_call; simpl in Hcall2_iscall; done. }
    (* === Step A: ret1 ≥ length(filter P (take lin1 ts')) === *)
    (* Decompose ts' at lin1 *)
    pose proof (take_drop_middle ts' lin1 (τ1, lt1) Hlt1_lookup) as Hts'_decomp1.
    (* ts splits as filter P (take lin1 ts') ++ filter P (drop (Datatypes.S lin1) ts') *)
    assert (Hts_decomp1 : ts = filter (not ∘ is_lin ∘ snd) (take lin1 ts') ++
                                filter (not ∘ is_lin ∘ snd) (drop (Datatypes.S lin1) ts')).
    { rewrite Hfilter -{1}Hts'_decomp1 filter_app filter_cons_False //.
      simpl. tauto. }
    set A1 := filter (not ∘ is_lin ∘ snd) (take lin1 ts').
    (* p_ret is not in A1 (no Ret-with-tag-τ1 before lin1) *)
    assert (Hret1_ge : ret1 ≥ length A1).
    { destruct (decide (ret1 < length A1)) as [Habs|Hge]; last lia. exfalso.
      assert (Hp_ret_in_A1 : p_ret ∈ A1).
      { eapply list_elem_of_lookup_2.
        rewrite Hts_decomp1 lookup_app_l in Hret1_lookup; [exact Hret1_lookup|exact Habs]. }
      (* p_ret ∈ take lin1 ts' *)
      assert (Hp_ret_in_take : p_ret ∈ take lin1 ts').
      { eapply list_elem_of_filter_1. exact Hp_ret_in_A1. }
      (* p_ret ∈ filter(tag=τ1)(take lin1 ts') *)
      assert (Hp_ret_in_tag_filt : p_ret ∈ filter (λ t, t.1 = τ1) (take lin1 ts')).
      { apply list_elem_of_filter_2; [exact Hret1_tag|exact Hp_ret_in_take]. }
      (* filter(tag=τ1)(take lin1 ts') is prefix of [Call; Lin; Ret] *)
      assert (Hpfx : filter (λ t, t.1 = τ1) (take lin1 ts') `prefix_of`
                      [(τ1, Call nv1 v1); (τ1, Lin nv1 v1 v1'); (τ1, Ret v1')]).
      { etrans; [|exact Hptl_τ1].
        apply prefix_filter. exists (drop lin1 ts'). symmetry. apply take_drop. }
      (* p_ret = (τ1, Ret v1') is in this prefix, so prefix must be the full list.
         Then Lin ∈ take lin1 ts', contradicting Hlt1_min. *)
      rewrite Hp_ret_eq in Hp_ret_in_tag_filt.
      destruct Hpfx as [sfx Hsfx].
      destruct (filter (λ t, t.1 = τ1) (take lin1 ts')) as [|a1 [|a2 [|a3 rest]]] eqn:Hfilt_eq;
        simpl in Hsfx.
      - set_solver.
      - injection Hsfx as <- _.
        rewrite elem_of_cons elem_of_nil in Hp_ret_in_tag_filt.
        destruct Hp_ret_in_tag_filt as [Heq_abs|[]]. discriminate.
      - injection Hsfx as <- <- _.
        rewrite !elem_of_cons elem_of_nil in Hp_ret_in_tag_filt.
        destruct Hp_ret_in_tag_filt as [Heq_abs|[Heq_abs|[]]]; discriminate.
      - injection Hsfx as <- <- <- Hsfx_rest.
        destruct rest; [|simpl in Hsfx_rest; discriminate].
        (* Lin ∈ take lin1 ts' → contradiction *)
        assert (Hlin_in_take : (τ1, Lin nv1 v1 v1') ∈ take lin1 ts').
        { apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). rewrite Hfilt_eq. set_solver. }
        apply list_elem_of_lookup_1 in Hlin_in_take as [k Hk_take].
        assert (Hk_lt : k < lin1).
        { apply lookup_lt_Some in Hk_take. rewrite length_take in Hk_take.
          apply lookup_lt_Some in Hlt1_lookup. lia. }
        assert (Hk_ts' : ts' !! k = Some (τ1, Lin nv1 v1 v1')).
        { apply lookup_take_Some in Hk_take. tauto. }
        apply (Hlt1_min k (τ1, Lin nv1 v1 v1') Hk_ts' Hk_lt).
        split; [done|simpl; done]. }
    (* === Step B: call2 < length(filter P (take lin2 ts')) === *)
    (* Decompose ts' at lin2 *)
    pose proof (take_drop_middle ts' lin2 (τ2, lt2) Hlt2_lookup) as Hts'_decomp2.
    assert (Hts_decomp2 : ts = filter (not ∘ is_lin ∘ snd) (take lin2 ts') ++
                                filter (not ∘ is_lin ∘ snd) (drop (Datatypes.S lin2) ts')).
    { rewrite Hfilter -{1}Hts'_decomp2 filter_app filter_cons_False //.
      simpl. tauto. }
    set A2 := filter (not ∘ is_lin ∘ snd) (take lin2 ts').
    (* p_call = (τ2, Call nv2 v2) ∈ take lin2 ts' *)
    (* First, decompose filter(tag=τ2) ts' using the split at lin2 *)
    assert (Hfilt_τ2_decomp : filter (λ t, t.1 = τ2) ts' =
              filter (λ t, t.1 = τ2) (take lin2 ts') ++
              (τ2, lt2) :: filter (λ t, t.1 = τ2) (drop (Datatypes.S lin2) ts')).
    { rewrite -{1}Hts'_decomp2 filter_app filter_cons_True //. }
    (* filter(tag=τ2)(take lin2 ts') has no Lin (Hlt2_min) *)
    assert (Hno_lin_before : ∀ z, z ∈ filter (λ t, t.1 = τ2) (take lin2 ts') → ¬ is_lin z.2).
    { intros z Hz_in Hz_lin.
      apply list_elem_of_filter in Hz_in as [Hz_tag Hz_in_take].
      apply list_elem_of_lookup_1 in Hz_in_take as [k Hk_lookup].
      assert (Hk_lt : k < lin2).
      { apply lookup_lt_Some in Hk_lookup. rewrite length_take in Hk_lookup.
        apply lookup_lt_Some in Hlt2_lookup. lia. }
      assert (Hk_ts' : ts' !! k = Some z).
      { apply lookup_take_Some in Hk_lookup. tauto. }
      apply (Hlt2_min k z Hk_ts' Hk_lt).
      split; [exact Hz_tag|exact Hz_lin]. }
    (* The tag-τ2 filter before lin2 must be [(τ2, Call nv2 v2)] (not []) *)
    assert (Hfilt_τ2_before : filter (λ t, t.1 = τ2) (take lin2 ts') = [(τ2, Call nv2 v2)]).
    { pose proof Hptl_τ2 as Hpfx2. rewrite Hfilt_τ2_decomp in Hpfx2.
      destruct (filter (λ t, t.1 = τ2) (take lin2 ts')) as [|hd [|hd2 rest]] eqn:Hfilt2_eq.
      - (* []. Then (τ2,lt2)::... is prefix of [Call;Lin;Ret]. lt2=Call. But is_lin lt2. *)
        exfalso. destruct Hpfx2 as [sfx Hsfx]. simpl in Hsfx.
        injection Hsfx as Hlt2_eq Hsfx_rest. subst lt2. simpl in Hlt2_islin. done.
      - (* [hd]. hd::(τ2,lt2)::... prefix of [Call;Lin;Ret]. hd=Call. *)
        destruct Hpfx2 as [sfx Hsfx]. simpl in Hsfx.
        injection Hsfx as Hhd_eq Hsfx_rest. subst hd. done.
      - (* [hd;hd2;rest]. hd=Call, hd2=Lin. But Hno_lin_before says no Lin. *)
        exfalso. destruct Hpfx2 as [sfx Hsfx]. simpl in Hsfx.
        injection Hsfx as Hhd_eq Hhd2_eq Hsfx_rest. subst hd hd2.
        apply (Hno_lin_before (τ2, Lin nv2 v2 v2')); [set_solver|simpl; done]. }
    (* (τ2, Call nv2 v2) ∈ take lin2 ts' *)
    assert (Hcall_in_take : (τ2, Call nv2 v2) ∈ take lin2 ts').
    { apply (list_elem_of_filter_1 (λ x, x.1 = τ2)).
      rewrite Hfilt_τ2_before. apply elem_of_cons. left. done. }
    (* p_call ∉ drop (Datatypes.S lin2) ts' *)
    assert (Hp_call_notin_drop : p_call ∉ drop (Datatypes.S lin2) ts').
    { rewrite Hp_call_eq. intros Habs_in.
      assert (Hcall_in_fa : (τ2, Call nv2 v2) ∈ filter (λ t, t.1 = τ2) (drop (Datatypes.S lin2) ts')).
      { apply list_elem_of_filter_2; [done|exact Habs_in]. }
      (* From the decomposition, filter(tag=τ2)(drop) is part of the prefix *)
      pose proof Hptl_τ2 as Hpfx_full.
      rewrite Hfilt_τ2_decomp Hfilt_τ2_before in Hpfx_full.
      destruct Hpfx_full as [sfx Hsfx]. simpl in Hsfx.
      injection Hsfx as Hlt2_eq Hsfx_rest.
      (* filter(tag=τ2)(drop) ++ sfx = [(τ2, Ret v2')] *)
      destruct (filter (λ t, t.1 = τ2) (drop (Datatypes.S lin2) ts')) as [|fa_hd fa_tl].
      - set_solver.
      - simpl in Hsfx_rest. injection Hsfx_rest as Hfa_hd_eq Hsfx_rest2.
        subst fa_hd.
        rewrite elem_of_cons in Hcall_in_fa.
        destruct Hcall_in_fa as [Habs_eq|Hcall_in_tl]; first discriminate.
        destruct fa_tl; [set_solver|simpl in Hsfx_rest2; discriminate]. }
    (* call2 < length A2 *)
    assert (Hcall2_lt : call2 < length A2).
    { destruct (decide (call2 < length A2)) as [|Hge]; first done. exfalso.
      apply Hp_call_notin_drop.
      eapply list_elem_of_filter_1.
      eapply list_elem_of_lookup_2.
      rewrite Hts_decomp2 lookup_app_r in Hcall2_lookup; [exact Hcall2_lookup|fold A2; lia]. }
    (* === Step C: length A2 ≤ length A1 (from lin2 ≤ lin1) === *)
    assert (Hlen_le : length A2 ≤ length A1).
    { unfold A1, A2.
      assert (Htake_pfx : take lin2 ts' `prefix_of` take lin1 ts').
      { exists (drop lin2 (take lin1 ts')).
        pose proof (take_drop lin2 (take lin1 ts')) as Htd.
        rewrite take_take Nat.min_l in Htd; [|lia].
        symmetry. exact Htd. }
      destruct (prefix_filter (not ∘ is_lin ∘ snd) _ _ Htake_pfx) as [sfx Hsfx].
      rewrite Hsfx length_app. lia. }
    (* Contradiction: call2 < length A2 ≤ length A1 ≤ ret1, so call2 < ret1.
       But Hpre says ret1 < call2. *)
    lia.
  Qed.

  Lemma trace_prt_correct_empty ts' :
    per_tag_wellformed_bag rme valid_value ts →
    ts = filter (not ∘ is_lin ∘ snd) ts' →
    per_tag_linearized ts' →
    (∃ s', rtcL (model_step (M:=bag_model rme valid_value)) s_init s' (filter (is_lin ∘ snd) ts')) →
    (∀ τ1 τ2, (τ1,τ2) ∈ m → [τ1;τ2] `sublist_of` (filter (is_lin ∘ snd) ts').*1) →
    correct_empty (trace_prt ts') trace_val trace_empty.
  Proof.
    intros Hwf Hfilt Hptl [s_end Hls] Hval_sub.
    pose proof (per_tag_linearized_NoDup_lin_tags _ Hptl) as Hnd.
    intros [a Ha] Hempty [ib Hib] [rb Hrb] Hval.
    rewrite /trace_empty /trace_val /trace_prt /= in Hempty, Hval |- *.
    (* a is pop-empty: a ∈ pop_of_trace ts ∧ a ∉ m.*2 *)
    destruct Hempty as [Ha_pop Ha_notin_m].
    (* Need: a ∈ pop_emp_of_trace ts. From closed_match + per_tag_complete:
       a is a pop, not matched. By closed_match, unmatched pops return IsEmpty
       or are unfinished. By per_tag_complete, a has a Ret. So a returns IsEmpty. *)
    assert (Ha_pop_emp : a ∈ pop_emp_of_trace ts).
    { destruct Hclosed as [_ Hclosed_pop].
      rewrite Forall_forall in Hclosed_pop.
      destruct (Hclosed_pop a Ha_pop) as [Habs|[Hret|Hunfinished]].
      - exfalso. exact (Ha_notin_m Habs).
      - rewrite /pop_emp_of_trace. apply (list_elem_of_fmap_2 fst _ (a, Ret (encode_response IsEmpty))).
        apply list_elem_of_filter_2; [done|exact Hret].
      - exfalso. apply Hunfinished.
        (* a has a Ret by per_tag_complete *)
        destruct (Hcomplete a) as (nv & v & v' & [Heq|Heq]).
        + (* filter = []: a ∈ pop_of_trace means (a, Call Pop) ∈ ts, but filter(tag=a) = []. *)
          exfalso. rewrite /pop_of_trace in Ha_pop.
          apply list_elem_of_fmap_1 in Ha_pop as ([a' ev'] & Heq_a & Hin).
          simpl in Heq_a. subst a'.
          apply list_elem_of_filter in Hin as [_ Hin].
          apply (list_elem_of_filter_2 (λ x, x.1 = a)) in Hin; last done.
          rewrite Heq in Hin. set_solver.
        + apply (list_elem_of_fmap_2 fst _ (a, Ret v')).
          apply list_elem_of_filter_2; [done|].
          apply (list_elem_of_filter_1 (λ x, x.1 = a)).
          rewrite Heq. set_solver. }
    destruct (trace_prt_no_cross_match ts' Hwf Hfilt Hptl Hnd (ex_intro _ _ Hls) Hval_sub
      ib rb a Hval Ha_pop_emp) as [Hcase1|Hcase2].
    - (* [ib;rb;a] sublist → prt ib a ∧ prt rb a *)
      destruct (sublist3_prt _ _ _ _ Hptl Hnd Hcase1) as (Hprt_ib_rb & Hprt_rb_a & Hprt_ib_a).
      left. split; [exact Hprt_ib_a|exact Hprt_rb_a].
    - (* [a;ib;rb] sublist → prt a ib ∧ prt a rb *)
      destruct (sublist3_prt _ _ _ _ Hptl Hnd Hcase2) as (Hprt_a_ib & Hprt_ib_rb & Hprt_a_rb).
      right. split; [exact Hprt_a_ib|exact Hprt_a_rb].
  Qed.

  Lemma val_then_not_pr_trace_prt_trace_val ts' :
    per_tag_linearized ts' →
    (∀ τ1 τ2, (τ1,τ2) ∈ m → [τ1;τ2] `sublist_of` (filter (is_lin ∘ snd) ts').*1) →
    val_then_not_pr (trace_prt ts') trace_val.
  Proof.
    intros Hptl Hsub [ia Hia] [ra Hra] Hval Hprt.
    rewrite /trace_val /= in Hval.
    rewrite /trace_prt /prt_of_trace /= in Hprt.
    destruct (sublist_lin_order ts' ia ra Hptl (per_tag_linearized_NoDup_lin_tags _ Hptl) (Hsub _ _ Hval))
      as (pa & xa & pb & xb & Hlin_a & Hlin_b & Hlt_ab).
    rewrite Hlin_b in Hprt. simpl in Hprt.
    rewrite Hlin_a in Hprt. simpl in Hprt.
    lia.
  Qed.

  (* End LLM-generated code. *)
  (**********************************************************)

  Lemma trace_linearizable_bag__linearizable_set :
    per_tag_wellformed_bag rme valid_value ts →
    per_tag_pop_empty_sound ts m →
    linearizable_set trace_pre trace_val trace_empty.
  Proof.
    intros Hwf Hempty_sound.
    destruct (trace_linearizable_bag_destruct rme valid_value ts m Hvalid Hcomplete Hclosed Hwf Hempty_sound)
      as (ts' & Hfilter & Hper_tag_lin & Hmsteps & Hval_then_not_pr).
    split; first by eapply conc_history_trace_pre.
    exists (trace_prt ts'), _.
    split; first by eapply trace_pre_prt_subrelation.
    split; last by eapply trace_prt_correct_empty.
    split; last by eapply trichotomy_trace_prt.
    constructor.
    - by eapply conc_history_trace_prt.
    - exists (enum trace_op). split; [apply NoDup_enum|intros x _; apply elem_of_enum].
    - by apply push_once_trace_val.
    - by apply pop_once_trace_val.
    - by apply val_order_trace_val.
    - by apply all_popped_or_empty_trace_val_trace_empty.
    - by apply empty_then_not_val_trace_val_trace_empty.
    - by apply val_then_not_pr_trace_prt_trace_val.
  Qed.
End set_binder.
