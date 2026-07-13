From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.models Require Export bag_like.
From iris_logatom.pure_logic.aspect.bag Require Import base.

Section proof.
  Variables (rme : response_mayempty) (valid_value : val → Prop) (ts : list (positive * trace)) (m : list (positive*positive)).
  Hypothesis Hvalid : valid_match ts m.
  Hypothesis Hcomplete : per_tag_complete ts.
  Hypothesis Hclosed : closed_match ts m.

  (* The bag only consists of values whose push has finished but whose pop
    has not started yet. *)
  Definition state_of_trace n : gmultiset val :=
    let pushes := (filter (λ '(τ1,τ2), τ1 ∈ (filter (is_ret∘snd) (take n ts)).*1
      ∧ τ2 ∉ (filter (is_call∘snd) (take n ts)).*1) m).*1 in
    let values := omap (λ x,
      if bool_decide (x.1 ∈ pushes) then
        if x.2 is Call (SOMEV v) then
          Some v
        else None
      else None) ts in
    list_to_set_disj values.

  (*************** Begin LLM-generated code. ****************)
  (* Claude Opus 4.6 (1M context, high effort, v2.1.91) *)

  (* Helper: a tag whose Call is at position n has no events at all in ts'_head *)
  Local Lemma call_at_n_no_events n₀ τ₀ v₀ ts'_head₀ :
    per_tag_wellformed_bag rme valid_value ts →
    ts !! n₀ = Some (τ₀, Call v₀) →
    take n₀ ts = filter (not ∘ is_lin ∘ snd) ts'_head₀ →
    per_tag_linearized ts'_head₀ →
    filter (λ x, x.1 = τ₀) ts'_head₀ = [].
  Proof.
    intros Hwf₀ Hlookup₀ Hfilter₀ Hper_tag₀.
    destruct (filter (λ x, x.1 = τ₀) ts'_head₀) as [|hd rest] eqn:Hfilt_eq; [done|].
    exfalso.
    destruct (Hper_tag₀ τ₀) as (w & w' & Hprefix₀).
    rewrite Hfilt_eq in Hprefix₀.
    pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as Hhd_eq. subst hd.
    assert (Hcall_in_take : (τ₀, Call w) ∈ take n₀ ts).
    { rewrite Hfilter₀. apply list_elem_of_filter_2; first by simpl; auto.
      apply (list_elem_of_filter_1 (λ x, x.1 = τ₀)).
      rewrite Hfilt_eq. set_solver. }
    apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hcall_in_take; last done.
    pose proof (take_drop_middle _ _ _ Hlookup₀) as Hts_split.
    apply (f_equal (filter (λ x, x.1 = τ₀))) in Hts_split as Hfilt_split.
    rewrite !filter_app filter_cons_True // in Hfilt_split.
    destruct (Hcomplete τ₀) as (vc & vc' & [Heq_c | Heq_c]); rewrite Heq_c in Hfilt_split.
    - destruct (filter (λ x, x.1 = τ₀) (take n₀ ts)); discriminate.
    - destruct (filter (λ x, x.1 = τ₀) (take n₀ ts)) as [|a_take rest_take]; first set_solver.
      simpl in Hfilt_split.
      destruct rest_take as [|b_take rest_take'].
      + injection Hfilt_split as _ Habs _. discriminate.
      + injection Hfilt_split as _ _ Hfilt_rest.
        apply (f_equal length) in Hfilt_rest. rewrite length_app /= in Hfilt_rest. lia.
  Qed.

  (* If ts!!n = (τ,ev) with P ev, and per_tag_complete gives at most one P-element per tag,
     then τ ∉ (filter (P∘snd) (take n ts)).*1. *)
  Local Lemma tag_at_n_not_in_take_tags n₀ τ₀ ev₀
    (P : trace → Prop) `{!∀ x, Decision (P x)} :
    ts !! n₀ = Some (τ₀, ev₀) → P ev₀ →
    (∀ ev', (τ₀, ev') ∈ ts → P ev' → ev' = ev₀) →
    τ₀ ∉ (filter (P ∘ snd) (take n₀ ts)).*1.
  Proof.
    intros Hlookup HP Huniq Hin.
    apply list_elem_of_fmap_1 in Hin as ([τ' ev'] & Heq_tag & Hin_filt).
    simpl in Heq_tag. subst τ'.
    apply list_elem_of_filter in Hin_filt as [HP' Hin_take].
    simpl in HP'.
    apply list_elem_of_lookup_1 in Hin_take as [j Hj].
    assert (Hj_lt : j < n₀).
    { apply lookup_lt_Some in Hj.
      rewrite length_take_le in Hj; last by (apply lookup_lt_Some in Hlookup; lia). lia. }
    rewrite lookup_take_lt in Hj; last lia.
    (* ts!!j = (τ₀,ev') and ts!!n₀ = (τ₀,ev₀). Both have P. By Huniq: ev' = ev₀. *)
    pose proof (Huniq ev' (list_elem_of_lookup_2 _ _ _ Hj) HP') as ->.
    (* Same element at positions j and n₀ with j < n₀. *)
    destruct (Hcomplete τ₀) as (vc & vc' & [Heq_c|Heq_c]).
    - (* filter = []: (τ₀,ev₀) ∈ ts but not in tag-filter → contradiction *)
      assert (Hin : (τ₀, ev₀) ∈ filter (λ x, x.1 = τ₀) ts).
      { apply list_elem_of_filter_2; [done|]. eapply list_elem_of_lookup_2. exact Hlookup. }
      rewrite Heq_c in Hin. set_solver.
    - (* filter = [(Call vc); (Ret vc')]. *)
      pose proof (take_drop_middle _ _ _ Hlookup) as Hts_split.
      apply (f_equal (filter (λ x, x.1 = τ₀))) in Hts_split.
      rewrite !filter_app filter_cons_True // in Hts_split.
      assert (Hj_in : (τ₀, ev₀) ∈ filter (λ x, x.1 = τ₀) (take n₀ ts)).
      { apply list_elem_of_filter_2; [done|]. eapply list_elem_of_lookup_2.
        rewrite lookup_take_lt; [exact Hj|lia]. }
      rewrite Heq_c in Hts_split.
      destruct (filter (λ x, x.1 = τ₀) (take n₀ ts)) as [|a rest] eqn:Hfilt_take.
      { set_solver. }
      (* a :: rest ++ (τ₀,ev₀) :: ... = [(Call vc); (Ret vc')] *)
      simpl in Hts_split. injection Hts_split as Ha Hrest.
      destruct rest as [|b rest'].
      + simpl in Hrest. injection Hrest as Hev₀ _.
        simplify_eq. set_solver.
      + apply (f_equal length) in Hrest. rewrite length_app /= in Hrest. lia.
  Qed.

  Local Lemma call_at_n_not_in_call_tags n₀ τ₀ :
    ts !! n₀ = Some (τ₀, Call (encode_request Pop)) →
    τ₀ ∉ (filter (is_call ∘ snd) (take n₀ ts)).*1.
  Proof.
    intros Hlookup.
    eapply tag_at_n_not_in_take_tags; [exact Hlookup|simpl; auto|].
    intros ev' Hin_ts HP'.
    destruct (Hcomplete τ₀) as (vc & vc' & [Heq_c|Heq_c]).
    - apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_ts; [rewrite Heq_c in Hin_ts; set_solver|done].
    - apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_ts; last done.
      rewrite Heq_c in Hin_ts.
      apply elem_of_cons in Hin_ts as [Heq_call|Hin_ts].
      + (* (τ₀,ev') = (τ₀, Call vc). Also ts!!n₀ = (τ₀, Call Pop) ∈ filter.
           Call Pop = Call vc (both are the unique Call entry). *)
        apply (f_equal snd) in Heq_call. simpl in Heq_call. subst ev'.
        assert (Hlookup_in : (τ₀, Call (encode_request Pop)) ∈ filter (λ x, x.1 = τ₀) ts).
        { apply list_elem_of_filter_2; [done|]. eapply list_elem_of_lookup_2. exact Hlookup. }
        rewrite Heq_c in Hlookup_in.
        apply elem_of_cons in Hlookup_in as [Heq|Hlookup_in].
        * apply (f_equal snd) in Heq. simpl in Heq. done.
        * apply elem_of_cons in Hlookup_in as [Heq|Hlookup_in]; [|set_solver].
          apply (f_equal snd) in Heq. simpl in Heq. discriminate.
      + apply elem_of_cons in Hin_ts as [Heq_ret|Hin_ts]; [|set_solver].
        apply (f_equal snd) in Heq_ret. simpl in Heq_ret. rewrite Heq_ret in HP'.
        simpl in HP'. done.
  Qed.

    (* Helper: a tag whose Call is at position n has no events in ts'_head,
     so it can't be linearized. *)
  Local Lemma call_at_n_not_linearized n₀ τ₀ v₀ ts'_head₀ :
    per_tag_wellformed_bag rme valid_value ts →
    ts !! n₀ = Some (τ₀, Call v₀) →
    take n₀ ts = filter (not ∘ is_lin ∘ snd) ts'_head₀ →
    per_tag_linearized ts'_head₀ →
    τ₀ ∉ (filter (is_lin ∘ snd) ts'_head₀).*1.
  Proof.
    intros Hwf₀ Hlookup₀ Hfilter₀ Hper_tag₀ Hin_lin.
    apply list_elem_of_fmap_1 in Hin_lin as ([τ₀' ev_lin] & Heq_tag & Hin_filt).
    simpl in Heq_tag. subst τ₀'.
    apply list_elem_of_filter in Hin_filt as [Hlin_ev Hin_head].
    apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_head; last done.
    destruct (Hper_tag₀ τ₀) as (w & w' & Hprefix₀).
    destruct (filter (λ x, x.1 = τ₀) ts'_head₀) as [|hd rest] eqn:Hfilt_eq.
    { set_solver. }
    pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as Hhd_eq. subst hd.
    assert (Hcall_in_take : (τ₀, Call w) ∈ take n₀ ts).
    { rewrite Hfilter₀. apply list_elem_of_filter_2; first by simpl; auto.
      apply (list_elem_of_filter_1 (λ x, x.1 = τ₀)). rewrite Hfilt_eq. set_solver. }
    pose proof (take_drop_middle _ _ _ Hlookup₀) as Hts_split.
    apply (f_equal (filter (λ x, x.1 = τ₀))) in Hts_split as Hfilt_split.
    rewrite !filter_app filter_cons_True // in Hfilt_split.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hcall_in_take; last done.
    destruct (Hcomplete τ₀) as (vc & vc' & [Heq_c | Heq_c]); rewrite Heq_c in Hfilt_split.
    - destruct (filter (λ x, x.1 = τ₀) (take n₀ ts)); discriminate.
    - destruct (filter (λ x, x.1 = τ₀) (take n₀ ts)) as [|a_take rest_take].
      { set_solver. }
      simpl in Hfilt_split.
      destruct rest_take as [|b_take rest_take'].
      + simpl in Hfilt_split. injection Hfilt_split as _ Habs _.
        discriminate.
      + injection Hfilt_split as _ _ Hfilt_rest.
        apply (f_equal length) in Hfilt_rest.
        rewrite length_app /= in Hfilt_rest. lia.
  Qed.

  Local Lemma ret_at_n_not_in_ret_tags n₀ τ₀ :
    ts !! n₀ = Some (τ₀, Ret #()) →
    τ₀ ∉ (filter (is_ret ∘ snd) (take n₀ ts)).*1.
  Proof.
    intros Hlookup.
    eapply tag_at_n_not_in_take_tags; [exact Hlookup|simpl; auto|].
    intros ev' Hin_ts HP'.
    destruct (Hcomplete τ₀) as (vc & vc' & [Heq_c|Heq_c]).
    - apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_ts; [rewrite Heq_c in Hin_ts; set_solver|done].
    - apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_ts; last done.
      rewrite Heq_c in Hin_ts.
      apply elem_of_cons in Hin_ts as [Heq_call|Hin_ts].
      + apply (f_equal snd) in Heq_call. simpl in Heq_call. rewrite Heq_call in HP'.
        simpl in HP'. done.
      + apply elem_of_cons in Hin_ts as [Heq_ret|Hin_ts]; [|set_solver].
        apply (f_equal snd) in Heq_ret. simpl in Heq_ret. subst ev'.
        assert (Hlookup_in : (τ₀, Ret #()) ∈ filter (λ x, x.1 = τ₀) ts).
        { apply list_elem_of_filter_2; [done|]. eapply list_elem_of_lookup_2. exact Hlookup. }
        rewrite Heq_c in Hlookup_in.
        apply elem_of_cons in Hlookup_in as [Heq|Hlookup_in].
        * apply (f_equal snd) in Heq. simpl in Heq. discriminate.
        * apply elem_of_cons in Hlookup_in as [Heq|Hlookup_in]; [|set_solver].
          apply (f_equal snd) in Heq. simpl in Heq. done.
  Qed.

  (* Helper: state_of_trace is determined by the filter on m *)
  Local Lemma state_of_trace_filter_irrel n₁ n₂ :
    (filter (λ '(τ1₀, τ2₀),
      τ1₀ ∈ (filter (is_ret ∘ snd) (take n₁ ts)).*1 ∧
      τ2₀ ∉ (filter (is_call ∘ snd) (take n₁ ts)).*1) m) =
    (filter (λ '(τ1₀, τ2₀),
      τ1₀ ∈ (filter (is_ret ∘ snd) (take n₂ ts)).*1 ∧
      τ2₀ ∉ (filter (is_call ∘ snd) (take n₂ ts)).*1) m) →
    state_of_trace n₁ = state_of_trace n₂.
  Proof. intros Hfilt_eq. unfold state_of_trace. rewrite Hfilt_eq. done. Qed.

  (* Helper: pop tags in m differ from push-Call tags *)
  Local Lemma pop_tag_ne_call_push n₀ τ₀ v₀ τ1₀ τ2₀ :
    ts !! n₀ = Some (τ₀, Call (encode_request (Push v₀))) →
    (τ1₀, τ2₀) ∈ m → τ2₀ ≠ τ₀.
  Proof.
    intros Hlookup₀ Hin₀ <-. (* τ₀ replaced by τ2₀ *)
    pose proof (valid_match_call_pop ts m τ1₀ τ2₀ Hvalid Hin₀) as Hpop.
    apply list_elem_of_lookup_2 in Hlookup₀ as Hpush.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ2₀)) in Hpop; last done.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ2₀)) in Hpush; last done.
    destruct (Hcomplete τ2₀) as (w & w' & [Heq|Heq]); rewrite Heq in Hpop; first set_solver.
    rewrite Heq in Hpush.
    apply elem_of_cons in Hpop as [Hp|Hpop].
    + apply elem_of_cons in Hpush as [Hq|Hpush].
      * apply (f_equal snd) in Hp, Hq. simpl in Hp, Hq.
        injection Hp as Hp. injection Hq as Hq. subst. discriminate.
      * apply elem_of_cons in Hpush as [Hq|Hpush]; last set_solver.
        apply (f_equal snd) in Hq. simpl in Hq. discriminate.
    + apply elem_of_cons in Hpop as [Hp|Hpop]; last set_solver.
      apply (f_equal snd) in Hp. simpl in Hp. discriminate.
  Qed.

  (* Helper: push tags in m differ from Ret-response tags *)
  Local Lemma push_tag_ne_ret_resp n₀ τ₀ r₀ τ1₀ τ2₀ :
    per_tag_wellformed_bag rme valid_value ts →
    ts !! n₀ = Some (τ₀, Ret (encode_response r₀)) →
    (τ1₀, τ2₀) ∈ m → τ1₀ ≠ τ₀.
  Proof.
    intros Hwf₀ Hlookup₀ Hin₀ <-.
    destruct (valid_match_call_push ts m τ1₀ τ2₀ Hvalid Hin₀) as [w Hpush].
    apply list_elem_of_lookup_2 in Hlookup₀ as Hret.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ1₀)) in Hpush; last done.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ1₀)) in Hret; last done.
    destruct (Hwf₀ τ1₀) as [(w' & _ & Hpfx)|(r' & _ & Hpfx)].
    - pose proof (elem_of_prefix _ _ _ Hret Hpfx) as Hin'.
      rewrite !elem_of_cons elem_of_nil in Hin'.
      destruct Hin' as [Hp|[Hp|[]]]; apply (f_equal snd) in Hp; simpl in Hp; first discriminate.
      destruct r₀; discriminate.
    - pose proof (elem_of_prefix _ _ _ Hpush Hpfx) as Hin'.
      rewrite !elem_of_cons elem_of_nil in Hin'.
      destruct Hin' as [Hp|[Hp|[]]]; apply (f_equal snd) in Hp; simpl in Hp; discriminate.
  Qed.

  (* Helper: NoDup m.*1 implies same-τ1 pairs are equal *)
  Local Lemma NoDup_m_fst_eq τ1₀ τ2₀ τ2₁ :
    (τ1₀, τ2₀) ∈ m → (τ1₀, τ2₁) ∈ m → τ2₀ = τ2₁.
  Proof.
    intros Hin₀ Hin₁.
    destruct Hvalid as (_ & [Hnd _] & _).
    apply list_elem_of_lookup_1 in Hin₀ as [i Hi].
    apply list_elem_of_lookup_1 in Hin₁ as [j Hj].
    assert (Hi' : m.*1 !! i = Some τ1₀) by (rewrite list_lookup_fmap Hi; done).
    assert (Hj' : m.*1 !! j = Some τ1₀) by (rewrite list_lookup_fmap Hj; done).
    pose proof (NoDup_lookup _ _ _ _ Hnd Hi' Hj') as Heq_ij. subst j.
    rewrite Hi in Hj. by injection Hj.
  Qed.

  (* Helper: NoDup m.*2 implies same-τ2 pairs are equal *)
  Local Lemma NoDup_m_snd_eq τ1₀ τ1₁ τ2₀ :
    (τ1₀, τ2₀) ∈ m → (τ1₁, τ2₀) ∈ m → τ1₀ = τ1₁.
  Proof.
    intros Hin₀ Hin₁.
    destruct Hvalid as (_ & [_ Hnd] & _).
    apply list_elem_of_lookup_1 in Hin₀ as [i Hi].
    apply list_elem_of_lookup_1 in Hin₁ as [j Hj].
    assert (Hi' : m.*2 !! i = Some τ2₀) by (rewrite list_lookup_fmap Hi; done).
    assert (Hj' : m.*2 !! j = Some τ2₀) by (rewrite list_lookup_fmap Hj; done).
    pose proof (NoDup_lookup _ _ _ _ Hnd Hi' Hj') as Heq_ij. subst j.
    rewrite Hi in Hj. by injection Hj.
  Qed.

  (* Basic list fact 2: Adding τ2 to call_tags excludes the unique (τ1,τ2) pair,
     giving pushes with τ1 filtered out. *)
  (* Helper: filter (≠ x) l = l when x ∉ l *)
  Local Lemma filter_ne_id {A} `{!EqDecision A} (x : A) (l : list A) :
    x ∉ l → filter (λ y, y ≠ x) l = l.
  Proof.
    induction l as [|a l' IH]; first done.
    intros Hnotin. rewrite not_elem_of_cons in Hnotin. destruct Hnotin as [Hne Hnotin].
    rewrite filter_cons_True; last done. f_equal. by apply IH.
  Qed.

  (* Helper: two omaps that agree pointwise produce the same result *)
  Local Lemma omap_ext_in {A B} (f g : A → option B) (l : list A) :
    (∀ x, x ∈ l → f x = g x) → omap f l = omap g l.
  Proof.
    clear.
    induction l as [|a l' IH]; first done.
    intros Hfg. simpl. rewrite Hfg; last set_solver.
    destruct (g a); [f_equal|]; apply IH; intros; apply Hfg; set_solver.
  Qed.

  (* Helper: the omap for state_of_trace can be split at (τ1, Call Push v) *)
  Local Lemma state_of_trace_omap_split (pushes : list positive) τ₀ v₀ :
    τ₀ ∈ pushes →
    (τ₀, Call (encode_request (Push v₀))) ∈ ts →
    ∃ l1 l2,
      omap (λ x, if bool_decide (x.1 ∈ pushes)
        then if x.2 is Call (SOMEV v) then Some v else None else None) ts
      = l1 ++ [v₀] ++ l2
    ∧ omap (λ x, if bool_decide (x.1 ∈ filter (λ τ, τ ≠ τ₀) pushes)
        then if x.2 is Call (SOMEV v) then Some v else None else None) ts
      = l1 ++ l2.
  Proof.
    intros Hin_pushes Hin_ts.
    (* Split ts at (τ₀, Call Push v₀) *)
    destruct (list_elem_of_split _ _ Hin_ts) as (ts1 & ts2 & Hts_eq).
    set f_with := (λ x : positive * trace, if bool_decide (x.1 ∈ pushes)
      then if x.2 is Call (SOMEV v) then Some v else None else None).
    set f_without := (λ x : positive * trace, if bool_decide (x.1 ∈ filter (λ τ, τ ≠ τ₀) pushes)
      then if x.2 is Call (SOMEV v) then Some v else None else None).
    exists (omap f_without ts1), (omap f_without ts2).
    rewrite Hts_eq !omap_app /=.
    (* For the middle element: f_with gives Some v₀, f_without gives None *)
    assert (Hf_mid_with : f_with (τ₀, Call (encode_request (Push v₀))) = Some v₀).
    { rewrite /f_with /=. rewrite bool_decide_eq_true_2; last done. done. }
    assert (Hf_mid_without : f_without (τ₀, Call (encode_request (Push v₀))) = None).
    { rewrite /f_without /=. rewrite bool_decide_eq_false_2; first done.
      rewrite list_elem_of_filter. intros [Habs _]. done. }
    rewrite Hf_mid_with Hf_mid_without /=.
    assert (Hext : ∀ l, l ⊆ ts1 ++ ts2 → omap f_with l = omap f_without l).
    { intros l Hsub. apply omap_ext_in. intros [τ' ev'] Hin'. rewrite /f_with /f_without /=.
    destruct (decide (τ' = τ₀)) as [->|Hne].
    - rewrite bool_decide_eq_true_2; last done.
      rewrite bool_decide_eq_false_2; last by (rewrite list_elem_of_filter; tauto).
      destruct ev' as [v_ev|v_ev v_ev'|v_ev]; try done.
      (* ev' = Call v_ev. Show v_ev ≠ SOMEV _ *)
      exfalso.
      assert (Hin_ts' : (τ₀, Call v_ev) ∈ ts).
      { rewrite Hts_eq. pose proof (Hsub _ Hin') as Hin_sub.
        apply elem_of_app in Hin_sub as [?|?]; apply elem_of_app; [left; done|right; right; done]. }
      apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_ts'; last done.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_ts as Hin_ts_filt; last done.
      destruct (Hcomplete τ₀) as (vc & vc' & [Heq_c|Heq_c]).
      { rewrite Heq_c in Hin_ts'. set_solver. }
      rewrite Heq_c in Hin_ts', Hin_ts_filt.
      apply (f_equal (filter (λ x, x.1 = τ₀))) in Hts_eq.
      rewrite !filter_app filter_cons_True // in Hts_eq.
      rewrite Heq_c in Hts_eq.
      pose proof Hts_eq as Hts_eq_struct.
      apply (f_equal length) in Hts_eq. rewrite !length_app /= in Hts_eq.
      pose proof (Hsub _ Hin') as Hin_sub.
      apply elem_of_app in Hin_sub as [Hin_x|Hin_x].
      all: apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_x; last done.
      + (* (τ₀, Call v_ev) ∈ filter(tag=τ₀)(ts1). *)
        destruct (filter (λ x, x.1 = τ₀) ts1) as [|x1 rest1] eqn:Hfilt1; first set_solver.
        assert (Hrest1_nil : rest1 = []) by (destruct rest1; [done|simpl in Hts_eq; lia]).
        subst rest1. simpl in Hts_eq_struct.
        apply (f_equal (λ l, hd_error (drop 1 l))) in Hts_eq_struct. simpl in Hts_eq_struct.
        destruct (filter (λ x, x.1 = τ₀) ts2); simpl in Hts_eq_struct; discriminate.
      + (* (τ₀, Call v_ev) ∈ filter(tag=τ₀)(ts2) *)
        destruct (filter (λ x, x.1 = τ₀) ts1) as [|x1 rest1].
        * simpl in Hts_eq_struct.
          apply (f_equal (λ l, hd_error (drop 1 l))) in Hts_eq_struct.
          simpl in Hts_eq_struct.
          destruct (filter (λ x, x.1 = τ₀) ts2) as [|x2 rest2]; first set_solver.
          destruct rest2 as [|x3 rest3].
          -- (* filter ts2 = [x2]. *)
             injection Hts_eq_struct as Hx2_eq.
             rewrite -Hx2_eq in Hin_x.
             apply elem_of_cons in Hin_x as [Habs|Hin_x]; [|set_solver].
             apply (f_equal snd) in Habs. simpl in Habs. discriminate.
          -- simpl in Hts_eq_struct. discriminate.
        * apply list_elem_of_lookup_1 in Hin_x as [kx Hkx].
          apply lookup_lt_Some in Hkx.
          destruct rest1; simpl in Hts_eq; lia.
    - (* τ' ≠ τ₀: membership conditions equivalent *)
      assert (Hmem_eq : τ' ∈ pushes ↔ τ' ∈ filter (λ τ, τ ≠ τ₀) pushes).
      { rewrite list_elem_of_filter. tauto. }
      destruct (decide (τ' ∈ pushes)) as [Hin_p|Hnotin_p].
      + rewrite !bool_decide_eq_true_2; [done|apply Hmem_eq; done|done].
      + rewrite !bool_decide_eq_false_2; [done|intros Habs; apply Hnotin_p; apply Hmem_eq; done|done]. }
    split; [|done].
    rewrite -(Hext ts1 ltac:(set_solver)) -(Hext ts2 ltac:(set_solver)). done.
  Qed.

  Local Lemma filter_add_call_removes_push (ret_tags call_tags : list positive) τ1₀ τ2₀ :
    NoDup m.*2 →
    (τ1₀, τ2₀) ∈ m →
    τ1₀ ∈ ret_tags → τ2₀ ∉ call_tags →
    (filter (λ '(a, b), a ∈ ret_tags ∧ b ∉ call_tags ++ [τ2₀]) m).*1 =
    filter (λ τ, τ ≠ τ1₀) (filter (λ '(a, b), a ∈ ret_tags ∧ b ∉ call_tags) m).*1.
  Proof.
    assert (Hnd1 : NoDup m.*1) by (destruct Hvalid as (_ & [? _] & _); done).
    clear ts Hvalid Hcomplete Hclosed.
    revert τ1₀ τ2₀ ret_tags call_tags Hnd1.
    induction m as [|[a b] m' IH]; intros τ1₀ τ2₀ ret_tags call_tags Hnd1 Hnd2 Hin Hret Hcall.
    { set_solver. }
    rewrite fmap_cons in Hnd1. apply NoDup_cons in Hnd1 as [Ha_notin1 Hnd1'].
    rewrite fmap_cons in Hnd2. apply NoDup_cons in Hnd2 as [Hb_notin2 Hnd2'].
    apply elem_of_cons in Hin as [Heq|Hin'].
    - (* Head = (τ1₀, τ2₀). After injection, a=τ1₀ and b=τ2₀ or vice versa.
         Use subst to keep the pair-variable names. *)
      assert (Heq_a : a = τ1₀) by congruence.
      assert (Heq_b : b = τ2₀) by congruence.
      subst a b.
      rewrite filter_cons_False; last by (simpl; intros [_ Habs]; apply Habs; set_solver).
      rewrite filter_cons_True; last by (simpl; done).
      rewrite fmap_cons /= filter_cons_False; last by (intros Habs; apply Habs).
      assert (Htail_eq : (filter (λ '(a0, b0), a0 ∈ ret_tags ∧ b0 ∉ call_tags ++ [τ2₀]) m').*1 =
                         (filter (λ '(a0, b0), a0 ∈ ret_tags ∧ b0 ∉ call_tags) m').*1).
      { f_equal. apply list_filter_ext. intros [a' b'] Hin'. simpl.
        assert (Hb'_ne : b' ≠ τ2₀).
        { intros ->. apply Hb_notin2. apply (list_elem_of_fmap_2 snd _ (a', τ2₀)). exact Hin'. }
        split; intros [Ha' Hb']; (split; [exact Ha'|]).
        - intros Hin_ct. apply Hb'. set_solver.
        - intros Hin_ct. apply Hb'. apply elem_of_app in Hin_ct as [?|Hin_ct]; [done|].
          apply elem_of_cons in Hin_ct as [->|Hin_ct]; [done|set_solver]. }
      rewrite Htail_eq.
      rewrite filter_ne_id; first done.
      intros Hin_filt. apply Ha_notin1.
      apply list_elem_of_fmap_1 in Hin_filt as ([a' b'] & Heq_a & Hin_filt').
      simpl in Heq_a. subst a'.
      apply list_elem_of_filter in Hin_filt' as [_ Hin_m'].
      apply (list_elem_of_fmap_2 fst _ (τ1₀, b')). exact Hin_m'.
    - (* Head ≠ (τ1₀, τ2₀), (τ1₀, τ2₀) ∈ m' *)
      assert (Hb_ne : b ≠ τ2₀).
      { intros ->. apply Hb_notin2. apply (list_elem_of_fmap_2 snd _ (τ1₀, τ2₀)). exact Hin'. }
      assert (Ha_ne : a ≠ τ1₀).
      { intros ->. apply Ha_notin1. apply (list_elem_of_fmap_2 fst _ (τ1₀, τ2₀)). exact Hin'. }
      (* b ≠ τ2₀ means the ++ [τ2₀] doesn't affect (a,b) *)
      destruct (decide (a ∈ ret_tags ∧ b ∉ call_tags)) as [[Ha Hb]|Hneg].
      + (* (a,b) passes both filters *)
        rewrite filter_cons_True; last first.
        {simpl. split; [exact Ha|]. intros Hin_ct.
          apply elem_of_app in Hin_ct as [Hin_ct|Hin_ct]; [exact (Hb Hin_ct)|].
          apply elem_of_cons in Hin_ct as [->|]; [done|set_solver]. }
        rewrite filter_cons_True; last by done.
        rewrite !fmap_cons /= filter_cons_True; last done.
        f_equal. apply IH; done.
      + (* (a,b) fails both filters *)
        rewrite filter_cons_False; last by (simpl; intros [Ha Hb]; apply Hneg; split; [exact Ha|];
          intros Habs; apply Hb; set_solver).
        rewrite filter_cons_False; last by done.
        apply IH; done.
  Qed.

  (* Helper: adding a tag to pushes adds its value to the omap result.
     new_pushes is any list with membership = {τ₀} ∪ pushes. *)
  Local Lemma state_of_trace_omap_add (new_pushes pushes : list positive) τ₀ v₀ :
    τ₀ ∉ pushes →
    (∀ τ, τ ∈ new_pushes ↔ τ = τ₀ ∨ τ ∈ pushes) →
    (τ₀, Call (encode_request (Push v₀))) ∈ ts →
    ∃ l1 l2,
      omap (λ x, if bool_decide (x.1 ∈ new_pushes)
        then if x.2 is Call (SOMEV v) then Some v else None else None) ts
      = l1 ++ [v₀] ++ l2
    ∧ omap (λ x, if bool_decide (x.1 ∈ pushes)
        then if x.2 is Call (SOMEV v) then Some v else None else None) ts
      = l1 ++ l2.
  Proof.
    intros Hnotin_pushes Hmem Hin_ts.
    destruct (list_elem_of_split _ _ Hin_ts) as (ts1 & ts2 & Hts_eq).
    set f_new := (λ x : positive * trace, if bool_decide (x.1 ∈ new_pushes)
      then if x.2 is Call (SOMEV v) then Some v else None else None).
    set f_old := (λ x : positive * trace, if bool_decide (x.1 ∈ pushes)
      then if x.2 is Call (SOMEV v) then Some v else None else None).
    exists (omap f_old ts1), (omap f_old ts2).
    rewrite Hts_eq !omap_app /=.
    assert (Hf_mid_new : f_new (τ₀, Call (encode_request (Push v₀))) = Some v₀).
    { rewrite /f_new /=. rewrite bool_decide_eq_true_2; [done|]. apply Hmem. left. done. }
    assert (Hf_mid_old : f_old (τ₀, Call (encode_request (Push v₀))) = None).
    { rewrite /f_old /=. rewrite bool_decide_eq_false_2; [done|exact Hnotin_pushes]. }
    rewrite Hf_mid_new Hf_mid_old /=.
    (* f_new and f_old agree on ts1 and ts2 (same argument as omap_split) *)
    assert (Hext : ∀ l, l ⊆ ts1 ++ ts2 → omap f_new l = omap f_old l).
    { intros l Hsub. apply omap_ext_in. intros [τ' ev'] Hin'. rewrite /f_new /f_old /=.
      destruct (decide (τ' = τ₀)) as [->|Hne].
      - (* τ' = τ₀: ev' ≠ Call SOMEV _ by per_tag_complete *)
        rewrite bool_decide_eq_true_2; last by (apply Hmem; left; done).
        rewrite bool_decide_eq_false_2; last done.
        (* Show ev' ≠ Call (SOMEV _) using same argument as omap_split *)
        destruct ev' as [v_ev|v_ev v_ev'|v_ev]; try done.
        exfalso.
        apply (f_equal (filter (λ x, x.1 = τ₀))) in Hts_eq.
        rewrite !filter_app filter_cons_True // in Hts_eq.
        destruct (Hcomplete τ₀) as (vc & vc' & [Heq_c|Heq_c]).
        { apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_ts; [rewrite Heq_c in Hin_ts; set_solver|done]. }
        rewrite Heq_c in Hts_eq.
        pose proof Hts_eq as Hts_eq_struct.
        apply (f_equal length) in Hts_eq. rewrite !length_app /= in Hts_eq.
        pose proof (Hsub _ Hin') as Hin_sub.
        apply elem_of_app in Hin_sub as [Hin_x|Hin_x].
        all: apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_x; last done.
        + destruct (filter (λ x, x.1 = τ₀) ts1) as [|x1 rest1]; first set_solver.
          assert (rest1 = []) by (destruct rest1; [done|simpl in Hts_eq; lia]). subst.
          simpl in Hts_eq_struct.
          apply (f_equal (λ l, hd_error (drop 1 l))) in Hts_eq_struct. simpl in Hts_eq_struct.
          destruct (filter (λ x, x.1 = τ₀) ts2); simpl in Hts_eq_struct; discriminate.
        + destruct (filter (λ x, x.1 = τ₀) ts1) as [|x1 rest1].
          * simpl in Hts_eq_struct.
            apply (f_equal (λ l, hd_error (drop 1 l))) in Hts_eq_struct. simpl in Hts_eq_struct.
            destruct (filter (λ x, x.1 = τ₀) ts2) as [|x2 rest2]; first set_solver.
            destruct rest2 as [|x3 rest3].
            -- injection Hts_eq_struct as Hx2_eq. rewrite -Hx2_eq in Hin_x.
               apply elem_of_cons in Hin_x as [Habs|Hin_x]; [discriminate|set_solver].
            -- simpl in Hts_eq_struct. discriminate.
          * apply list_elem_of_lookup_1 in Hin_x as [kx Hkx].
            apply lookup_lt_Some in Hkx. destruct rest1; simpl in Hts_eq; lia.
      - (* τ' ≠ τ₀: membership conditions equivalent *)
        assert (Hmem_eq : τ' ∈ new_pushes ↔ τ' ∈ pushes).
        { rewrite Hmem. split; [intros [->|?]; [done|done]|intros; right; done]. }
        destruct (decide (τ' ∈ pushes)) as [Hin_p|Hnotin_p].
        + rewrite !bool_decide_eq_true_2 //. apply Hmem_eq. done.
        + rewrite !bool_decide_eq_false_2 //. intros Habs. apply Hnotin_p. apply Hmem_eq. done. }
    split; [|done].
    rewrite -(Hext ts1 ltac:(set_solver)) -(Hext ts2 ltac:(set_solver)). done.
  Qed.

  (* Adding τ1₀ to ret_tags: membership equivalence (exact list equality is false in general) *)
  Local Lemma filter_add_ret_adds_push_elem (ret_tags call_tags : list positive) τ1₀ τ2₀ :
    NoDup m.*1 →
    (τ1₀, τ2₀) ∈ m →
    τ1₀ ∉ ret_tags → τ2₀ ∉ call_tags →
    ∀ τ, τ ∈ (filter (λ '(a, b), a ∈ ret_tags ++ [τ1₀] ∧ b ∉ call_tags) m).*1 ↔
         τ = τ1₀ ∨ τ ∈ (filter (λ '(a, b), a ∈ ret_tags ∧ b ∉ call_tags) m).*1.
  Proof.
    assert (Hnd2 : NoDup m.*2) by (destruct Hvalid as (_ & [_ ?] & _); done).
    clear ts Hvalid Hcomplete Hclosed.
    revert τ1₀ τ2₀ ret_tags call_tags Hnd2.
    induction m as [|[a b] m' IH]; intros τ1₀ τ2₀ ret_tags call_tags Hnd2 Hnd1 Hin Hret Hcall τ.
    { set_solver. }
    rewrite fmap_cons in Hnd1. apply NoDup_cons in Hnd1 as [Ha_notin1 Hnd1'].
    rewrite fmap_cons in Hnd2. apply NoDup_cons in Hnd2 as [Hb_notin2 Hnd2'].
    apply elem_of_cons in Hin as [Heq|Hin'].
    - (* Head = (τ1₀, τ2₀) *)
      assert (Heq_a : a = τ1₀) by congruence.
      assert (Heq_b : b = τ2₀) by congruence. subst a b.
      rewrite filter_cons_True; last by (simpl; split; [set_solver|exact Hcall]).
      rewrite filter_cons_False; last by (simpl; intros [Habs _]; exact (Hret Habs)).
      rewrite fmap_cons /=.
      assert (Htail_eq : filter (λ '(a0, b0), a0 ∈ ret_tags ++ [τ1₀] ∧ b0 ∉ call_tags) m' =
                         filter (λ '(a0, b0), a0 ∈ ret_tags ∧ b0 ∉ call_tags) m').
      { apply list_filter_ext. intros [a' b'] Hin'. simpl.
        assert (Ha'_ne : a' ≠ τ1₀).
        { intros ->. apply Ha_notin1. apply (list_elem_of_fmap_2 fst _ (τ1₀, b')). exact Hin'. }
        split; intros [Ha Hb]; (split; [|exact Hb]).
        - apply elem_of_app in Ha as [Ha|Ha]; [exact Ha|].
          apply elem_of_cons in Ha as [->|Ha]; [done|set_solver].
        - set_solver. }
      rewrite Htail_eq. set_solver.
    - (* Head ≠ (τ1₀, τ2₀), (τ1₀, τ2₀) ∈ m' *)
      assert (Ha_ne : a ≠ τ1₀).
      { intros ->. apply Ha_notin1. apply (list_elem_of_fmap_2 fst _ (τ1₀, τ2₀)). exact Hin'. }
      destruct (decide (a ∈ ret_tags ∧ b ∉ call_tags)) as [[Ha Hb]|Hneg].
      + rewrite filter_cons_True; last by (simpl; split; [set_solver|exact Hb]).
        rewrite filter_cons_True; last by done.
        rewrite !fmap_cons /=.
        pose proof (IH τ1₀ τ2₀ ret_tags call_tags Hnd2' Hnd1' Hin' Hret Hcall) as HIH.
        split; intros Hin_τ.
        * apply elem_of_cons in Hin_τ as [->|Hin_τ]; [right; set_solver|].
          apply HIH in Hin_τ. destruct Hin_τ as [->|Hin_τ]; [left; done|right; set_solver].
        * destruct Hin_τ as [->|Hin_τ].
          -- right. apply HIH. left. done.
          -- apply elem_of_cons in Hin_τ as [->|Hin_τ]; [left; done|].
             right. apply HIH. right. done.
      + rewrite filter_cons_False; last by (simpl; intros [Ha Hb]; apply Hneg; split;
          [apply elem_of_app in Ha as [?|Ha]; [done|]; apply elem_of_cons in Ha as [->|]; [done|set_solver]
          |exact Hb]).
        rewrite filter_cons_False; last by done.
        eapply IH; done.
  Qed.

  Lemma state_of_trace_call_push n τ v :
    ts !! n = Some (τ,Call (encode_request (Push v))) →
    state_of_trace (1+n) = state_of_trace n.
  Proof.
    intros Hlookup.
    apply state_of_trace_filter_irrel.
    rewrite (take_S_r _ _ _ Hlookup) !filter_app.
    rewrite (filter_cons_False (is_ret∘snd)); last by simpl; auto.
    rewrite (filter_cons_True (is_call∘snd)); last by (simpl; eexists; done).
    rewrite !filter_nil !right_id !fmap_app /=.
    apply list_filter_ext. intros [τ1₀ τ2₀] Hin_m₀. simpl.
    rewrite elem_of_app elem_of_cons elem_of_nil.
    split; intros [H1 H2]; (split; [exact H1|]).
    - intros Hin. apply H2. left. exact Hin.
    - intros [Hin|[->|[]]]; [exact (H2 Hin)|].
      exact (pop_tag_ne_call_push n τ v τ1₀ τ Hlookup Hin_m₀ eq_refl).
  Qed.

  Lemma state_of_trace_ret_pop n τ r :
    per_tag_wellformed_bag rme valid_value ts →
    ts !! n = Some (τ,Ret (encode_response r)) →
    state_of_trace (1+n) = state_of_trace n.
  Proof.
    intros Hwf Hlookup.
    apply state_of_trace_filter_irrel.
    rewrite (take_S_r _ _ _ Hlookup) !filter_app.
    rewrite (filter_cons_True (is_ret∘snd)); last by (simpl; eexists; done).
    rewrite (filter_cons_False (is_call∘snd)); last by simpl; auto.
    rewrite !filter_nil !right_id !fmap_app /=.
    apply list_filter_ext. intros [τ1₀ τ2₀] Hin_m₀. simpl.
    rewrite elem_of_app elem_of_cons elem_of_nil.
    split; intros [H1 H2]; (split; [|exact H2]).
    - destruct H1 as [H1|[->|[]]]; [exact H1|].
      exfalso. exact (push_tag_ne_ret_resp n τ r τ τ2₀ Hwf Hlookup Hin_m₀ eq_refl).
    - left. exact H1.
  Qed.

  Lemma state_of_trace_call_pop_overlap n τ1 τ2 :
    (τ1,τ2) ∈ m →
    τ1 ∉ (filter (is_ret∘snd) (take n ts)).*1 →
    ts !! n = Some (τ2,Call (encode_request Pop)) →
    state_of_trace (1+n) = state_of_trace n.
  Proof.
    intros Hin_m Hτ1_no_ret Hlookup.
    apply state_of_trace_filter_irrel.
    rewrite (take_S_r _ _ _ Hlookup) !filter_app.
    rewrite (filter_cons_False (is_ret∘snd)); last by simpl; auto.
    rewrite (filter_cons_True (is_call∘snd)); last by simpl; auto.
    rewrite !filter_nil !right_id !fmap_app /=.
    apply list_filter_ext. intros [τ1₀ τ2₀] Hin_m₀. simpl.
    rewrite elem_of_app elem_of_cons elem_of_nil.
    split; intros [H1 H2]; (split; [exact H1|]).
    - intros Hin. apply H2. left. exact Hin.
    - intros [Hin|[->|[]]]; [exact (H2 Hin)|].
      pose proof (NoDup_m_snd_eq τ1₀ τ1 τ2 Hin_m₀ Hin_m) as <-.
      exact (Hτ1_no_ret H1).
  Qed.

   Lemma state_of_trace_call_pop_nonoverlap n τ1 τ2 v :
    (τ1,τ2) ∈ m →
    (τ1,Call (encode_request (Push v))) ∈ ts →
    τ1 ∈ (filter (is_ret∘snd) (take n ts)).*1 →
    ts !! n = Some (τ2,Call (encode_request Pop)) →
    state_of_trace (1+n) = state_of_trace n ∖ {[+ v +]}.
  Proof.
    intros Hin_m Hpush_in Hτ1_ret Hlookup.
    unfold state_of_trace.
    rewrite (take_S_r _ _ _ Hlookup) !filter_app.
    rewrite (filter_cons_False (is_ret∘snd)); last by simpl; auto.
    rewrite (filter_cons_True (is_call∘snd)); last by simpl; auto.
    rewrite !filter_nil !right_id !fmap_app /=.
    pose proof (call_at_n_not_in_call_tags n τ2 Hlookup) as Hτ2_notin_call.
    assert (Hτ1_in : τ1 ∈ (filter (λ '(τ1₀, τ2₀),
      τ1₀ ∈ (filter (is_ret ∘ snd) (take n ts)).*1 ∧
      τ2₀ ∉ (filter (is_call ∘ snd) (take n ts)).*1) m).*1).
    { apply (list_elem_of_fmap_2 fst _ (τ1,τ2)).
      apply list_elem_of_filter_2; [|exact Hin_m]. simpl. split; [exact Hτ1_ret|exact Hτ2_notin_call]. }
    destruct Hvalid as (_ & [_ Hnd2] & _).
    pose proof (filter_add_call_removes_push
      (filter (is_ret ∘ snd) (take n ts)).*1
      (filter (is_call ∘ snd) (take n ts)).*1
      τ1 τ2 Hnd2 Hin_m Hτ1_ret Hτ2_notin_call) as Hfilter_eq.
    rewrite Hfilter_eq.
    destruct (state_of_trace_omap_split _ τ1 v Hτ1_in Hpush_in)
      as (l1 & l2 & Homap_old & Homap_new).
    rewrite Homap_old Homap_new.
    rewrite !list_to_set_disj_app /=.
    clear.
    multiset_solver.
  Qed.

  Lemma state_of_trace_ret_push_overlap n τ1 τ2 :
    (τ1,τ2) ∈ m →
    τ2 ∈ (filter (is_call∘snd) (take n ts)).*1 →
    ts !! n = Some (τ1, Ret #()) →
    state_of_trace (1+n) = state_of_trace n.
  Proof.
    intros Hin_m Hτ2_called Hlookup.
    apply state_of_trace_filter_irrel.
    rewrite (take_S_r _ _ _ Hlookup) !filter_app.
    rewrite (filter_cons_True (is_ret∘snd)); last by simpl; auto.
    rewrite (filter_cons_False (is_call∘snd)); last by simpl; auto.
    rewrite !filter_nil !right_id !fmap_app /=.
    apply list_filter_ext. intros [τ1₀ τ2₀] Hin_m₀. simpl.
    rewrite elem_of_app elem_of_cons elem_of_nil.
    split; intros [H1 H2]; (split; [|exact H2]).
    - destruct H1 as [H1|[->|[]]]; [exact H1|].
      exfalso. apply H2.
      pose proof (NoDup_m_fst_eq τ1 τ2₀ τ2 Hin_m₀ Hin_m) as <-.
      exact Hτ2_called.
    - left. exact H1.
  Qed.

  Lemma state_of_trace_ret_push_nonoverlap n τ1 τ2 v :
    (τ1,τ2) ∈ m →
    (τ1,Call (encode_request (Push v))) ∈ ts →
    τ2 ∉ (filter (is_call∘snd) (take n ts)).*1 →
    ts !! n = Some (τ1, Ret #()) →
    state_of_trace (1+n) = {[+ v +]} ⊎ state_of_trace n.
  Proof.
    intros Hin_m Hpush_in Hτ2_no_call Hlookup.
    unfold state_of_trace.
    rewrite (take_S_r _ _ _ Hlookup) !filter_app.
    rewrite (filter_cons_True (is_ret∘snd)); last by simpl; auto.
    rewrite (filter_cons_False (is_call∘snd)); last by simpl; auto.
    rewrite !filter_nil !right_id !fmap_app /=.
    (* The change: τ1 is added to ret_tags.
       This adds pair (τ1,τ2) to pushes (since τ2 ∉ call_tags by hypothesis).
       Adding τ1 to pushes adds v to the multiset. *)
    (* The new pushes = old pushes ∪ {τ1}. Use state_of_trace_push_add. *)
    (* τ1's Ret is at position n, so τ1 ∉ ret_tags(take n ts) *)
    assert (Hτ1_notin_ret : τ1 ∉ (filter (is_ret ∘ snd) (take n ts)).*1).
    { eapply ret_at_n_not_in_ret_tags. exact Hlookup. }
    assert (Hτ1_notin : τ1 ∉ (filter (λ '(τ1₀, τ2₀),
      τ1₀ ∈ (filter (is_ret ∘ snd) (take n ts)).*1 ∧
      τ2₀ ∉ (filter (is_call ∘ snd) (take n ts)).*1) m).*1).
    { intros Hin. apply list_elem_of_fmap_1 in Hin as ([a b] & Heq & Hin_filt).
      simpl in Heq. subst a.
      apply list_elem_of_filter in Hin_filt as [[Hret _] _]. exact (Hτ1_notin_ret Hret). }
    destruct Hvalid as (_ & [Hnd1 _] & _).
    pose proof (filter_add_ret_adds_push_elem
      (filter (is_ret ∘ snd) (take n ts)).*1
      (filter (is_call ∘ snd) (take n ts)).*1
      τ1 τ2 Hnd1 Hin_m Hτ1_notin_ret Hτ2_no_call) as Hfilter_mem.
    destruct (state_of_trace_omap_add
      (filter (λ '(τ1₀, τ2₀),
        τ1₀ ∈ (filter (is_ret ∘ snd) (take n ts)).*1 ++ [τ1] ∧
        τ2₀ ∉ (filter (is_call ∘ snd) (take n ts)).*1) m).*1
      (filter (λ '(τ1₀, τ2₀),
        τ1₀ ∈ (filter (is_ret ∘ snd) (take n ts)).*1 ∧
        τ2₀ ∉ (filter (is_call ∘ snd) (take n ts)).*1) m).*1
      τ1 v Hτ1_notin Hfilter_mem Hpush_in)
      as (l1 & l2 & Homap_new & Homap_old).
    rewrite Homap_new Homap_old.
    rewrite !list_to_set_disj_app /=.
    clear.
    multiset_solver.
  Qed.

  Lemma state_of_trace_call_pop_empty n τ :
    τ ∉ m.*2 →
    ts !! n = Some (τ, Call (encode_request Pop)) →
    state_of_trace (1+n) = state_of_trace n.
  Proof.
    intros Hnotin_m2 Hlookup.
    apply state_of_trace_filter_irrel.
    rewrite (take_S_r _ _ _ Hlookup) !filter_app.
    rewrite (filter_cons_False (is_ret∘snd)); last by simpl; auto.
    rewrite (filter_cons_True (is_call∘snd)); last by (simpl; eexists; done).
    rewrite !filter_nil !right_id !fmap_app /=.
    apply list_filter_ext. intros [τ1₀ τ2₀] Hin_m₀. simpl.
    rewrite elem_of_app elem_of_cons elem_of_nil.
    split; intros [H1 H2]; (split; [exact H1|]).
    - intros Hin. apply H2. left. exact Hin.
    - intros [Hin|[->|[]]]; [exact (H2 Hin)|].
      exfalso. apply Hnotin_m2.
      exact (list_elem_of_fmap_2 snd _ _ Hin_m₀).
  Qed.

  (* Helper: if a tag has Call at position j and Ret at position n,
     and per_tag_wellformed holds, then j < n (Call before Ret). *)
  Local Lemma call_pos_lt_ret_pos τ0 j n ev_call ev_ret :
    per_tag_wellformed_bag rme valid_value ts →
    ts !! j = Some (τ0, Call ev_call) →
    ts !! n = Some (τ0, Ret ev_ret) →
    j < n.
  Proof.
    intros Hwf0 Hj Hn.
    assert (j ≠ n) by (intros ->; rewrite Hn in Hj; discriminate).
    assert (j < length ts) by (eapply lookup_lt_Some; eauto).
    destruct (decide (j < n)); [lia|exfalso].
    (* j > n: Ret at n before Call at j. filter starts with Call (from prefix). Contradiction. *)
    destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf0 τ0) as (vc & vc' & Hpfx).
    rewrite -(take_drop n ts) filter_app in Hpfx.
    destruct (filter (λ x, x.1 = τ0) (take n ts)) as [|htk rtk] eqn:Hftk.
    - (* filter(take) = []: filter starts from drop. drop starts with Ret at n. *)
      rewrite left_id in Hpfx.
      pose proof (drop_S _ _ _ Hn) as Hdrop_eq.
      rewrite Hdrop_eq filter_cons_True // in Hpfx.
      apply prefix_cons_inv_1 in Hpfx. discriminate.
    - (* filter(take) ≠ []: Call in take AND Call at j in drop. Two Calls. *)
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as Hhtk. subst htk.
      assert (Hcall_take : (τ0, Call vc) ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ0) (take n ts))).
      { apply list_elem_of_filter_2; [done|]. rewrite Hftk. clear. set_solver. }
      assert (Hcall_drop : (τ0, Call ev_call) ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ0) (drop n ts))).
      { apply list_elem_of_filter_2; [done|]. apply list_elem_of_filter_2; [done|].
        replace j with (n + (j - n)) in Hj by lia. rewrite -lookup_drop in Hj.
        exact (list_elem_of_lookup_2 _ _ _ Hj). }
      apply (prefix_filter (is_call ∘ snd)) in Hpfx.
      apply prefix_length in Hpfx. rewrite filter_app length_app in Hpfx.
      enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ0) (take n ts)))) by
        (enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ0) (drop n ts))));
         [simpl in Hpfx; lia|];
         destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ0) (drop n ts)));
         [clear -Hcall_drop; set_solver|simpl; lia]).
      destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ0) (take n ts)));
        [clear -Hcall_take; set_solver|simpl; lia].
  Qed.

  (* Helper: a pop-IsEmpty tag with events cannot be in m.*2 *)
  Local Lemma pop_empty_not_in_m τ0 :
    per_tag_complete ts →
    valid_match ts m →
    per_tag_wellformed_bag rme valid_value ts →
    (τ0, Call (encode_request Pop)) ∈ ts →
    filter (λ x, x.1 = τ0) ts `prefix_of`
      [(τ0, Call (encode_request Pop)); (τ0, Ret (encode_response IsEmpty))] →
    τ0 ∉ m.*2.
  Proof.
    intros Hcomp Hval Hwf0 Hin_call Hpfx Hin_m2.
    apply list_elem_of_fmap_1 in Hin_m2 as ([τ1₀ τ2₀] & Heqτ & Hin_m₀).
    simpl in Heqτ. subst τ2₀.
    destruct Hval as (_ & _ & Hforall).
    rewrite Forall_forall in Hforall.
    destruct (Hforall _ Hin_m₀) as (_ & _ & v_m & _ & [Hret_m | Hno_ret]).
    - (* (τ0, Ret (NonEmpty v_m)) ∈ ts. But τ0's Ret is IsEmpty. *)
      apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hret_m; last done.
      pose proof (elem_of_prefix _ _ _ Hret_m Hpfx) as Hin'.
      rewrite !elem_of_cons elem_of_nil right_id in Hin'.
      destruct Hin' as [Hin'|Hin']; apply (f_equal snd) in Hin'; simpl in Hin'; discriminate.
    - (* τ0 ∉ ret_tags(ts). But from per_tag_complete, τ0 has Ret IsEmpty. *)
      apply Hno_ret.
      destruct (Hcomp τ0) as (vc & vc' & [Heq_c | Heq_c]).
      { (* filter = []: but τ0 has Call ∈ ts. *)
        apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hin_call; last done.
        rewrite Heq_c in Hin_call. clear -Hin_call. set_solver. }
      (* filter = [(Call vc); (Ret vc')]. Ret vc' ∈ ts. *)
      apply (list_elem_of_fmap_2 fst _ (τ0, Ret vc')).
      apply list_elem_of_filter_2; [done|].
      apply (list_elem_of_filter_1 (λ x, x.1 = τ0)). rewrite Heq_c. clear. set_solver.
  Qed.

  (* Helper: for matched (τ1, τ2), τ1's Call at j and τ2's Ret at n give j ≤ n
     via ¬ pre_of_trace. Uses per_tag_complete + per_tag_wellformed. *)
  Local Lemma matched_push_call_le_pop_ret τ1₀ τ2₀ j n ev_call ev_ret :
    per_tag_complete ts →
    valid_match ts m →
    per_tag_wellformed_bag rme valid_value ts →
    (τ1₀, τ2₀) ∈ m →
    ts !! j = Some (τ1₀, Call ev_call) →
    ts !! n = Some (τ2₀, Ret ev_ret) →
    j ≤ n.
  Proof.
    intros Hcomp Hval Hwf0 Hin_m0 Hj Hn.
    destruct (decide (j ≤ n)); [lia|exfalso].
    assert (Hj_gt_n : n < j) by lia.
    destruct Hval as (_ & _ & Hforall).
    rewrite Forall_forall in Hforall.
    destruct (Hforall _ Hin_m0) as (Hno_pre & _).
    apply Hno_pre. clear Hno_pre Hforall.
    rewrite /pre_of_trace.
    (* Show call_of_tag ts τ1₀ and ret_of_tag ts τ2₀ exist, with ret < call. *)
    assert (Hret_ex : ∃ n' ev_ret', ret_of_tag ts τ2₀ = Some (n', (τ2₀, Ret ev_ret')) ∧ n' ≤ n).
    { rewrite /ret_of_tag.
      pose proof (list_elem_of_lookup_2 _ _ _ Hn) as Hin_n.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ2₀ ∧ is_ret x.2)) in Hin_n as Hin_filt.
      2: { simpl. done. }
      destruct (ret_of_tag ts τ2₀) as [[n' [τ' ev']]|] eqn:Hfind.
      2: { rewrite /ret_of_tag in Hfind. apply list_find_None in Hfind.
           rewrite Forall_forall in Hfind.
           exfalso. exact (Hfind _ (list_elem_of_lookup_2 _ _ _ Hn) (conj eq_refl I)). }
      pose proof Hfind as Hfind'.
      rewrite /ret_of_tag list_find_Some /= in Hfind'.
      destruct Hfind' as (Hn' & [Heq_τ' His_ret'] & _). subst τ'.
      destruct ev' as [| |v_ret']; [by simpl in His_ret'..|].
      eexists _, _. split; [exact Hfind|].
      destruct (decide (n' ≤ n)); [lia|exfalso].
      (* n' > n: two Ret events for τ2₀. Contradiction with per_tag_wellformed. *)
      destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf0 τ2₀) as (vc_τ & vc_τ' & Hpfx_τ).
      apply (prefix_filter (is_ret∘snd)) in Hpfx_τ.
      rewrite filter_cons_False in Hpfx_τ; last by simpl; auto.
      rewrite filter_cons_True in Hpfx_τ; last by simpl; auto.
      rewrite filter_nil in Hpfx_τ.
      rewrite /ret_of_tag list_find_Some /= in Hfind.
      destruct Hfind as (_ & _ & Hmin_ret).
      exfalso. eapply Hmin_ret; [exact Hn|lia|]. simpl. done. }
    (* call_of_tag ts τ1₀: finds first Call for τ1₀. *)
    assert (Hcall_ex : ∃ j' ev_call', call_of_tag ts τ1₀ = Some (j', (τ1₀, Call ev_call'))).
    { destruct (call_of_tag ts τ1₀) as [[j' [τ' ev']]|] eqn:Hfind.
      2: { rewrite /call_of_tag in Hfind. apply list_find_None in Hfind.
           rewrite Forall_forall in Hfind.
           exfalso. exact (Hfind _ (list_elem_of_lookup_2 _ _ _ Hj) (conj eq_refl I)). }
      pose proof Hfind as Hfind'.
      rewrite /call_of_tag list_find_Some /= in Hfind'.
      destruct Hfind' as (Hj' & [Heq_τ' His_call'] & _). subst τ'.
      destruct ev' as [v_call'| |]; [exists j', v_call'; done|by simpl in His_call'..]. }
    destruct Hret_ex as (n' & ev_ret' & Hret & Hn'_le_n).
    destruct Hcall_ex as (j' & ev_call' & Hcall).
    rewrite Hret Hcall /=.
    (* Need: n' < j'. We know n' ≤ n < j. And j' ≤ j (first match ≤ any match). *)
    (* j' ≤ j: from list_find finding the FIRST match. *)
    assert (Hj'_le_j : j' ≤ j).
    { rewrite /call_of_tag list_find_Some in Hcall.
      destruct Hcall as (Hj'_lookup & _ & Hmin).
      destruct (decide (j' ≤ j)); [lia|].
      assert (j < j') by lia.
      exfalso. eapply Hmin; [exact Hj|lia|]. simpl. done. }
    (* j' = j: unique Call position for τ1₀ *)
    assert (Hj'_eq : j' = j).
    { destruct (decide (j' = j)); [lia|exfalso].
      assert (j' < j) by lia.
      (* Two Call positions for τ1₀ (j' and j). Contradiction via take/drop. *)
      destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf0 τ1₀) as (vc_u & vc_u' & Hpfx_u).
      apply (prefix_filter (is_call∘snd)) in Hpfx_u.
      rewrite filter_cons_True in Hpfx_u; last done.
      rewrite filter_cons_False in Hpfx_u; last by simpl; auto.
      rewrite filter_nil in Hpfx_u.
      rewrite /call_of_tag list_find_Some /= in Hcall.
      destruct Hcall as (Hj'_lookup & _ & _).
      rewrite -(take_drop j ts) !filter_app in Hpfx_u.
      apply prefix_length in Hpfx_u. rewrite !length_app length_cons length_nil in Hpfx_u.
      assert (Hin_take : (τ1₀, Call ev_call') ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ1₀) (take j ts))).
      { apply list_elem_of_filter_2; [done|]. apply list_elem_of_filter_2; [done|].
        eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hj'_lookup|lia]. }
      assert (Hin_drop : (τ1₀, Call ev_call) ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ1₀) (drop j ts))).
      { apply list_elem_of_filter_2; [done|]. apply list_elem_of_filter_2; [done|].
        replace j with (j + 0) in Hj by lia. rewrite -lookup_drop in Hj.
        exact (list_elem_of_lookup_2 _ _ _ Hj). }
      enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ1₀) (take j ts)))).
      { enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ1₀) (drop j ts))));
        [lia|]; destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ1₀) (drop j ts)));
        [clear -Hin_drop; set_solver|simpl; lia]. }
      destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ1₀) (take j ts)));
        [clear -Hin_take; set_solver|simpl; lia]. }
    lia.
  Qed.

  (* If state_of_trace n ≠ ∅, there exists a push-pop pair in m
     whose push has Ret'd in take n ts and whose pop has not been Called in take n ts. *)
  Local Lemma state_of_trace_nonempty_witness n₀ :
    state_of_trace n₀ ≠ ∅ →
    ∃ τ1₀ τ2₀, (τ1₀,τ2₀) ∈ m
      ∧ τ1₀ ∈ (filter (is_ret∘snd) (take n₀ ts)).*1
      ∧ τ2₀ ∉ (filter (is_call∘snd) (take n₀ ts)).*1.
  Proof.
    intros Hne.
    apply gmultiset_choose in Hne as [v₀ Hv₀].
    rewrite /state_of_trace elem_of_list_to_set_disj in Hv₀.
    apply list_elem_of_omap in Hv₀ as ([τ₀ ev₀] & Hin_ts & Hsome).
    simpl in Hsome.
    case_bool_decide as Hin_pushes; last by destruct ev₀; discriminate.
    apply list_elem_of_fmap_1 in Hin_pushes as ([τ1₀ τ2₀] & Heq_τ & Hin_filt).
    simpl in Heq_τ. subst τ₀.
    apply list_elem_of_filter in Hin_filt as [[Hret Hcall] Hin_m₀].
    exists τ1₀, τ2₀. done.
  Qed.

  (* If τ1 is a finished push (matched to τ2 in m, where τ2 is the call at position n,
     and τ1 has no future activity in drop n ts), then τ1's Ret is in take n ts. *)
  Local Lemma matched_finished_push_ret_in_take τ1 τ2 n :
    per_tag_complete ts →
    valid_match ts m →
    per_tag_wellformed_bag rme valid_value ts →
    (τ1, τ2) ∈ m →
    τ1 ≠ τ2 →
    τ1 ∉ trace_pendingOp (drop n ts) →
    τ1 ∉ (filter (is_call ∘ snd) (drop n ts)).*1 →
    ts !! n = Some (τ2, Call (encode_request Pop)) →
    τ1 ∈ (filter (is_ret ∘ snd) (take n ts)).*1.
  Proof.
    intros Hcomp Hval Hwf0 Hin_m Hne_τ Hnot_pending Hfinished Hlookup.
    destruct (Hcomp τ1) as (vc1 & vc1' & [Hfilt_empty | Hfilt_eq]).
    { destruct (valid_match_call_push ts m τ1 τ2 Hval Hin_m) as [vp Hcp].
      apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcp; last done.
      rewrite Hfilt_empty in Hcp. clear -Hcp. set_solver. }
    apply (list_elem_of_fmap_2 fst _ (τ1, Ret vc1')).
    apply list_elem_of_filter_2; [done|].
    assert (Hret_in : (τ1, Ret vc1') ∈ ts).
    { apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). rewrite Hfilt_eq. clear. set_solver. }
    apply list_elem_of_lookup_1 in Hret_in as [k_ret Hk_ret].
    assert (k_ret < n).
    { assert (k_ret ≠ n) by (intros ->; rewrite Hlookup in Hk_ret; simplify_eq).
      assert (k_ret < length ts) by (eapply lookup_lt_Some; eauto).
      destruct (decide (k_ret < n)); [lia|exfalso].
      assert (k_ret > n) by lia.
      apply Hnot_pending.
      pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
      apply filter_tag_trace_pendingOp.
      rewrite filter_cons_False; last by (simpl; auto).
      rewrite -filter_tag_trace_pendingOp.
      apply filter_tag_trace_pendingOp.
      assert (Hret_in_drop : (τ1, Ret vc1') ∈ drop (Datatypes.S n) ts).
      { replace k_ret with (Datatypes.S n + (k_ret - Datatypes.S n)) in Hk_ret by lia.
        rewrite -lookup_drop in Hk_ret. exact (list_elem_of_lookup_2 _ _ _ Hk_ret). }
      apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hret_in_drop; last done.
      destruct (filter (λ x, x.1 = τ1) (drop (Datatypes.S n) ts)) as [|[τ1_d ev_d] rest_d] eqn:Hfilt_d.
      { clear -Hret_in_drop Hfilt_d. set_solver. }
      assert (Hτ1_d_eq : τ1_d = τ1).
      { pose proof (list_elem_of_here (τ1_d, ev_d) rest_d) as Hin_hd.
        rewrite -Hfilt_d in Hin_hd.
        apply list_elem_of_filter in Hin_hd as [Htag _]. simpl in Htag. done. }
      subst τ1_d.
      destruct ev_d as [v_d| |].
      - exfalso. apply Hfinished.
        apply (list_elem_of_fmap_2 fst _ (τ1, Call v_d)).
        apply list_elem_of_filter_2; [done|].
        assert (Hcall_in_filt : (τ1, Call v_d) ∈ filter (λ x, x.1 = τ1) (drop (Datatypes.S n) ts)).
        { rewrite Hfilt_d. clear. set_solver. }
        apply list_elem_of_filter in Hcall_in_filt as [_ Hcall_in_ds].
        pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq2. rewrite Hdrop_eq2.
        clear -Hcall_in_ds. set_solver.
      - apply trace_pendingOp_lin_elem_of.
      - apply trace_pendingOp_ret_elem_of. }
    eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hk_ret|lia].
  Qed.

  (* If (τ1,τ2) ∈ m matches a Pop with NonEmpty v_pop result, then the push value
     for τ1 equals v_pop (per_tag_wellformed gives unique Call values). *)
  Local Lemma matched_push_value_eq_pop_value τ1 τ2 vp v_pop :
    per_tag_complete ts →
    valid_match ts m →
    per_tag_wellformed_bag rme valid_value ts →
    (τ1, τ2) ∈ m →
    (τ1, Call (encode_request (Push vp))) ∈ ts →
    filter (λ x, x.1 = τ2) ts `prefix_of`
      [(τ2, Call (encode_request Pop)); (τ2, Ret (encode_response (NonEmpty v_pop)))] →
    vp = v_pop.
  Proof.
    intros Hcomp Hval Hwf0 Hin_m Hcp Hprefix.
    pose proof Hval as Hval'.
    destruct Hval' as (_ & _ & Hforall_vm).
    rewrite Forall_forall in Hforall_vm.
    destruct (Hforall_vm _ Hin_m) as (_ & _ & v_match & Hcall_match & [Hret_match | Hno_ret]).
    - apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hret_match; last done.
      pose proof (elem_of_prefix _ _ _ Hret_match Hprefix) as Hin_pfx.
      rewrite !elem_of_cons elem_of_nil right_id in Hin_pfx.
      destruct Hin_pfx as [Hin_pfx|Hin_pfx].
      { apply (f_equal snd) in Hin_pfx. simpl in Hin_pfx. discriminate. }
      assert (Hvm_eq : v_match = v_pop) by (simplify_eq; done).
      subst v_match.
      destruct (Hwf0 τ1) as [(vc1 & _ & Hpfx_τ1) | (vc1 & _ & Hpfx_τ1)].
      + apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcp; last done.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_match; last done.
        pose proof (elem_of_prefix _ _ _ Hcp Hpfx_τ1) as Hin1.
        pose proof (elem_of_prefix _ _ _ Hcall_match Hpfx_τ1) as Hin2.
        rewrite !elem_of_cons !elem_of_nil in Hin1, Hin2.
        destruct Hin1 as [Hin1|[Hin1|[]]]; destruct Hin2 as [Hin2|[Hin2|[]]];
          try (apply (f_equal snd) in Hin1; by simpl in Hin1);
          try (apply (f_equal snd) in Hin2; by simpl in Hin2).
        simplify_eq. done.
      + exfalso.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcp; last done.
        pose proof (elem_of_prefix _ _ _ Hcp Hpfx_τ1) as Hin1.
        rewrite !elem_of_cons !elem_of_nil in Hin1.
        destruct Hin1 as [Hin1|[Hin1|[]]]; apply (f_equal snd) in Hin1; by simpl in Hin1.
    - exfalso. apply Hno_ret.
      destruct (Hcomp τ2) as (vc2 & vc2' & [Hfilt_empty2|Hfilt_eq2]).
      { pose proof (valid_match_call_pop ts m τ1 τ2 Hval Hin_m) as Hcp2.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hcp2; last done.
        rewrite Hfilt_empty2 in Hcp2. clear -Hcp2. set_solver. }
      apply (list_elem_of_fmap_2 fst _ (τ2, Ret vc2')).
      apply list_elem_of_filter_2; [simpl; eexists; done|].
      apply (list_elem_of_filter_1 (λ x, x.1 = τ2)). rewrite Hfilt_eq2. clear. set_solver.
  Qed.

  (* If τ1's push has finished and τ2's pop has been called, the push value is in the
     state at position n. *)
  Local Lemma matched_push_value_in_state_of_trace τ1 τ2 v_pop n :
    valid_match ts m →
    (τ1, τ2) ∈ m →
    (τ1, Call (encode_request (Push v_pop))) ∈ ts →
    τ1 ∈ (filter (is_ret ∘ snd) (take n ts)).*1 →
    ts !! n = Some (τ2, Call (encode_request Pop)) →
    v_pop ∈ state_of_trace n.
  Proof.
    intros Hval Hin_m Hcp Hτ1_ret Hlookup.
    rewrite /state_of_trace elem_of_list_to_set_disj.
    pose proof (call_at_n_not_in_call_tags n τ2 Hlookup) as Hτ2_notin_call.
    assert (Hτ1_in_pushes : τ1 ∈ (filter (λ '(τ1₀, τ2₀),
      τ1₀ ∈ (filter (is_ret ∘ snd) (take n ts)).*1 ∧
      τ2₀ ∉ (filter (is_call ∘ snd) (take n ts)).*1) m).*1).
    { apply (list_elem_of_fmap_2 fst _ (τ1,τ2)).
      apply list_elem_of_filter_2; [|exact Hin_m]. simpl.
      split; [exact Hτ1_ret|exact Hτ2_notin_call]. }
    destruct (state_of_trace_omap_split _ τ1 v_pop Hτ1_in_pushes Hcp) as (l1 & l2 & Homap & _).
    rewrite Homap. clear. set_solver.
  Qed.

  (* Helper for Hpop_lin_consistent: when the new ts'_head is extended with a list
     of events containing no Lin events, the property is preserved from the old part. *)
  Local Lemma pop_lin_consistent_extend_no_lin
    (P : positive → val → val → Prop)
    (ts'_head_old added : list (positive * trace)) :
    Forall (λ x, ¬ is_lin (snd x)) added →
    (∀ τ v v', τ ∈ pop_of_trace ts → (τ, Lin v v') ∈ ts'_head_old → P τ v v') →
    ∀ τ v v', τ ∈ pop_of_trace ts → (τ, Lin v v') ∈ ts'_head_old ++ added → P τ v v'.
  Proof.
    intros Hno_lin Hold τ v v' Hpop Hin.
    apply elem_of_app in Hin as [Hin_old|Hin_new].
    - exact (Hold τ v v' Hpop Hin_old).
    - exfalso.
      rewrite Forall_forall in Hno_lin.
      pose proof (Hno_lin _ Hin_new) as Hnl. simpl in Hnl. by apply Hnl.
  Qed.

  (* If (τ_push, τ_pop) ∈ m, then τ_push is in push_of_trace ts. *)
  Local Lemma matched_push_in_push_of_trace τ_push τ_pop :
    (τ_push, τ_pop) ∈ m → τ_push ∈ push_of_trace ts.
  Proof.
    intros Hin_m. destruct (valid_match_call_push ts m _ _ Hvalid Hin_m) as [vp Hcp].
    apply (list_elem_of_fmap_2 fst _ (τ_push, Call (encode_request (Push vp)))).
    apply list_elem_of_filter_2; [eexists; done|exact Hcp].
  Qed.

  (* If (τ_push, τ_pop) ∈ m, then τ_pop is in pop_of_trace ts. *)
  Local Lemma matched_pop_in_pop_of_trace τ_push τ_pop :
    (τ_push, τ_pop) ∈ m → τ_pop ∈ pop_of_trace ts.
  Proof.
    intros Hin_m.
    apply (list_elem_of_fmap_2 fst _ (τ_pop, Call (encode_request Pop))).
    apply list_elem_of_filter_2; [done|exact (valid_match_call_pop _ _ _ _ Hvalid Hin_m)].
  Qed.

  (* If (τ_push, τ) ∈ m, then τ_push ≠ a tag known to be a pop. *)
  Local Lemma matched_push_xor_pop τ_push τ_pop τ :
    per_tag_wellformed_bag rme valid_value ts →
    (τ_push, τ_pop) ∈ m →
    τ ∈ pop_of_trace ts →
    τ ≠ τ_push.
  Proof.
    intros Hwf0 Hin_m Hτ_pop ->.
    eapply push_xor_pop_of_trace;
      [exact Hwf0|exact (matched_push_in_push_of_trace _ _ Hin_m)|exact Hτ_pop].
  Qed.

  (* If τ ∈ ts as Call event with tag τ, then τ ∈ pop_of_trace if event is Call Pop. *)
  Local Lemma in_pop_of_trace_from_call_pop τ :
    (τ, Call (encode_request Pop)) ∈ ts → τ ∈ pop_of_trace ts.
  Proof.
    intros Hin.
    apply (list_elem_of_fmap_2 fst _ (τ, Call (encode_request Pop))).
    apply list_elem_of_filter_2; [done|exact Hin].
  Qed.

  (* Specialized helper: extend Hpop_lin_consistent with one Call event. *)
  Local Lemma pop_lin_consistent_extend_call
    (P : positive → val → val → Prop)
    ts'_head_old τ_call v_call :
    (∀ τ v v', τ ∈ pop_of_trace ts → (τ, Lin v v') ∈ ts'_head_old → P τ v v') →
    ∀ τ v v', τ ∈ pop_of_trace ts → (τ, Lin v v') ∈ ts'_head_old ++ [(τ_call, Call v_call)] → P τ v v'.
  Proof.
    intros Hold τ v v' Hpop Hin.
    apply elem_of_app in Hin as [Hin_old|Hin_new].
    - exact (Hold τ v v' Hpop Hin_old).
    - rewrite elem_of_cons elem_of_nil in Hin_new.
      destruct Hin_new as [Habs|[]]. discriminate.
  Qed.

  (* Specialized helper: extend Hpop_lin_consistent with one Ret event. *)
  Local Lemma pop_lin_consistent_extend_ret
    (P : positive → val → val → Prop)
    ts'_head_old τ_ret v_ret :
    (∀ τ v v', τ ∈ pop_of_trace ts → (τ, Lin v v') ∈ ts'_head_old → P τ v v') →
    ∀ τ v v', τ ∈ pop_of_trace ts → (τ, Lin v v') ∈ ts'_head_old ++ [(τ_ret, Ret v_ret)] → P τ v v'.
  Proof.
    intros Hold τ v v' Hpop Hin.
    apply elem_of_app in Hin as [Hin_old|Hin_new].
    - exact (Hold τ v v' Hpop Hin_old).
    - rewrite elem_of_cons elem_of_nil in Hin_new.
      destruct Hin_new as [Habs|[]]. discriminate.
  Qed.
  (**************** End LLM-generated code. *****************)

  (* The induction condition.
    - ts[0..n] has been processed
    - s is the current state
    - ts[n..] is the trace in the future
    - ts'_head is a linearization of the processed trace

    The general principle is to linearize push as late as possible and
    linearize pop as early as possible. This ensures the bag contains the
    least possible amount of elements so that pop(∅) can always succeed.
    *)
  Lemma trace_linearizable_bag_destruct_ind n :
    per_tag_wellformed_bag rme valid_value ts →
    per_tag_pop_empty_sound ts m →
    ∃ ts'_head s, (* The next 3 lines are about processed trace *)
      let ts'_head_lin := (filter (is_lin ∘ snd) ts'_head) in
      take n ts = filter (not ∘ is_lin ∘ snd) ts'_head
    ∧ per_tag_linearized ts'_head
    ∧ linearized_sound (M:=bag_model rme valid_value) ts'_head_lin s_init s
      (* conclusion *)
    ∧ (∀ τ1 τ2, (τ1,τ2) ∈ m → τ2 ∈ ts'_head_lin.*1 → [τ1;τ2] `sublist_of` ts'_head_lin.*1)
      (* state *)
    ∧ s = state_of_trace n
      (* No pending pop(∅) can ever linearize *)
    ∧ (∀ τ, τ ∈ (trace_pendingOp (drop n ts)) ∧ τ ∉ ts'_head_lin.*1 →
          τ ∈ pop_emp_of_trace ts →
          ∃ icall, ts !! icall = Some (τ, Call (encode_request Pop)) ∧
                   ∀ i, icall ≤ i < n → ∃ τ1 τ2, (τ1,τ2) ∈ m ∧ push_pop_covers ts τ1 τ2 i)
      (* If a pending push has linearized, its pop must also have linearized *)
    ∧ (∀ τ1, τ1 ∈ (trace_pendingOp (drop n ts)) ∧ τ1 ∈ ts'_head_lin.*1 →
          τ1 ∈ push_of_trace ts →
          ∃ τ2, (τ1,τ2) ∈ m ∧ τ2 ∈ ts'_head_lin.*1)
       (* If both push and pop are called, the pop must be both linearized *)
    ∧ (∀ τ1 τ2, (τ1,τ2) ∈ m →
      τ1 ∈ (filter (is_call ∘ snd) (take n ts)).*1 →
      τ2 ∈ (filter (is_call ∘ snd) (take n ts)).*1 →
      τ2 ∈ ts'_head_lin.*1)
      (* The linearization of Pop is consistent with m *)
    ∧ (∀ τ2 v v', τ2 ∈ pop_of_trace ts → (τ2,Lin v v') ∈ ts'_head →
      if bool_decide (τ2 ∈ m.*2)
        then (∃ τ1 v_pop, (τ1,τ2) ∈ m ∧ (τ1, Call (encode_request (Push v_pop))) ∈ ts ∧ v' = encode_response (NonEmpty v_pop))
        else v' = encode_response IsEmpty).
  Proof.
  (* Part of this proof is LLM-generated using the same configuration:
      tool: Claude Code 2.1.91
      model: Claude Opus 4.6 (claude-opus-4-6)
      parameters:
        effort = high
        context window = 1000000
        max output tokens = 128000 *)
    intros Hwf Hbag_sound. induction n as [|n IH].
    { (* Base case: no trace was processed *)
      exists [], ∅. rewrite !take_0 !drop_0 filter_nil.
      split_and!.
      - done.
      - apply per_tag_linearized_nil.
      - apply linearized_sound_nil.
      - intros ??? Hfalse. exfalso. set_solver.
      - rewrite /state_of_trace !filter_nil.
        rewrite filter_False_nil; last first.
        { apply Forall_forall => x _ HFalse.
          destruct x, HFalse.
          set_solver. }
        clear.
        induction ts as [|t ts' IH]; first  by rewrite omap_nil.
        rewrite omap_cons_None; first done.
        rewrite bool_decide_eq_false_2; first done.
        set_solver.
      - rewrite per_tag_wellformed_trace_pendingOp_empty;
          last by apply per_tag_complete_per_tag_wellformed.
        intros ? [HFalse _]. exfalso. set_solver.
      - rewrite per_tag_wellformed_trace_pendingOp_empty;
          last by apply per_tag_complete_per_tag_wellformed.
        intros ? [HFalse _]. exfalso. set_solver.
      - simpl.
        intros ??? HFalse. exfalso. set_solver.
      - intros ??? ? HFalse. exfalso. set_solver. }
    destruct IH as (ts'_head & s &
      Hfilter & Hper_tag_lin & Hlin_sound
      & Hval_then_not_pr & Hstate_of_trace & Hempty_aeap & Hpush_alap & Hpop_aeap & Hpop_lin_consistent).
    destruct (decide (n < length ts)) as [Hn_lt | Hn_ge]; last first.
    { (* Another trivial case: the whole trace has been processed *)
      exists ts'_head, s.
      split_and!; try assumption.
      - rewrite !take_ge; last lia.
        rewrite !take_ge in Hfilter; last lia.
        assumption.
      - rewrite /state_of_trace take_ge; last lia.
        rewrite /state_of_trace take_ge in Hstate_of_trace; last lia.
        assumption.
      - rewrite drop_ge; last lia.
        intros ? [HFalse _]. exfalso.
        simpl in HFalse.
        set_solver.
      - rewrite drop_ge; last lia.
        intros ? [HFalse _]. exfalso.
        simpl in HFalse.
        set_solver.
      - rewrite !take_ge; last lia.
        rewrite !take_ge in Hpop_aeap; last lia.
        assumption. }
    rewrite -lookup_lt_is_Some in Hn_lt.
    destruct Hn_lt as [[τ [v|v v'|v']] Hlookup].
    2: { exfalso.
      apply list_elem_of_lookup_2 in Hlookup as Hin.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin; last done.
      destruct (Hcomplete τ) as (?&?&[Heq | Heq]); rewrite Heq in Hin.
      - set_solver.
      - rewrite !elem_of_cons elem_of_nil right_id in Hin.
        destruct Hin; discriminate. }
    - (* the next event is Call *)
      apply list_elem_of_lookup_2 in Hlookup as Hin.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin as Hin_filter_tag; last done.
      destruct (Hwf τ) as [(v_push & _ & Hprefix)|(rsel & Hr_ne & Hprefix)];
        [|destruct rsel as [|v_pop]].
      + (* Call Push *)
        rename τ into τ1.
        pose proof (Hin':= elem_of_prefix _ _ _ Hin_filter_tag Hprefix).
        rewrite !elem_of_cons elem_of_nil right_id in Hin'.
        destruct Hin' as [Heq | HFalse]; last discriminate HFalse.
        injection Heq as Heq.
        subst v.
        assert (Hτ1_in_m: τ1 ∈ m.*1).
        { destruct Hclosed as [Hclosed_push _].
          eapply list_elem_of_weaken; last exact Hclosed_push.
          rewrite /push_of_trace.
          eapply (list_elem_of_fmap_2 fst _ (τ1,_)).
          apply list_elem_of_filter_2; last exact Hin.
          eexists. done. }
        apply list_elem_of_fmap_1 in Hτ1_in_m.
        destruct Hτ1_in_m as ([τ1' τ2] & Heqτ1 & Hin_m).
        simpl in Heqτ1. subst τ1'.
        opose proof (valid_match_ne _ _ _ _ _ Hvalid Hin_m) as Hτ1_ne_τ2.
        { apply per_tag_complete_per_tag_wellformed, Hcomplete. }
        destruct (decide (τ2 ∈ trace_pendingOp (drop n ts))) as [Hτ2_started | Hτ2_not_started].
        * (* If the matched Pop has started, linearize both operations immediately *)
          exists (ts'_head ++ [(τ1,Call (encode_request (Push v_push)));
            (τ1,Lin (encode_request (Push v_push)) #());
            (τ2,Lin (encode_request Pop) (encode_response (NonEmpty v_push)))]), s.
          intros ts'_head_lin. split_and!.
          --(* Hfilter *)
            rewrite filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil.
            rewrite (take_S_r _ _ _ Hlookup).
            f_equal. done.
          --(* Hper_tag_lin *)
            intro τ₀.
            pose proof (Hper_tag_lin' := Hper_tag_lin).
            specialize (Hper_tag_lin' τ₀) as (v₀ & v₀' & Hprefix₀).
            rewrite filter_app.
            destruct (decide (τ₀ = τ1)) as [-> | Hτ₀_ne_τ1];
            last destruct (decide (τ₀ = τ2)) as [-> | Hτ₀_ne_τ2].
            ++exists (encode_request (Push v_push)), #().
              do 2 rewrite filter_cons_True //.
              rewrite filter_cons_False //.
              rewrite filter_nil.
              (* This is equivalent to assert (filter (λ x, x.1 = τ1) ts'_head = []) *)
              destruct (filter (λ x, x.1 = τ1) ts'_head) as [|t l] eqn:Heq; last first.
              { exfalso. (* ts cannot have two (τ1,Call) *)
                apply prefix_cons_inv_1 in Hprefix₀. subst t.
                assert (Hτ1_called: (τ1, Call v₀) ∈ take n ts).
                { rewrite Hfilter.
                  apply (list_elem_of_filter_2); first by auto.
                  apply (list_elem_of_filter_1 (λ x, x.1 = τ1)).
                  rewrite Heq. set_solver. }
                pose proof (Hts_eq := (take_drop n ts)).
                destruct (list_elem_of_split _ _ Hτ1_called) as (l1 & l2 & Hts_head_eq).
                rewrite Hts_head_eq in Hts_eq.
                replace n with (n+0) in Hlookup by lia.
                rewrite -lookup_drop in Hlookup.
                destruct (list_elem_of_split_length _ _ _ Hlookup) as (l3 & l4 & Hts_tail_eq & ->%eq_comm%nil_length_inv).
                rewrite left_id in Hts_tail_eq.
                rewrite Hts_tail_eq in Hts_eq.
                rewrite -assoc in Hts_eq.
                apply (f_equal (filter (λ x, x.1 = τ1))) in Hts_eq.
                rewrite !filter_app !filter_cons_True // in Hts_eq.
                destruct (Hcomplete τ1) as (? & ? & [Heq1 | Heq1]); rewrite Heq1 in Hts_eq.
                - apply (f_equal length) in Hts_eq.
                  rewrite !length_app length_cons length_nil in Hts_eq.
                  lia.
                - apply (f_equal (filter (is_call∘snd))) in Hts_eq.
                  rewrite !filter_app in Hts_eq.
                  do 3 rewrite filter_cons_True // in Hts_eq.
                  rewrite filter_cons_False in Hts_eq; last by simpl; auto.
                  rewrite filter_nil in Hts_eq.
                  apply (f_equal length) in Hts_eq.
                  rewrite !length_app !length_cons length_nil in Hts_eq.
                  lia. }
              rewrite left_id.
              eexists. reflexivity.
            ++exists (encode_request Pop), (encode_response (NonEmpty v_push)).
              do 2 rewrite filter_cons_False //.
              rewrite filter_cons_True //.
              rewrite filter_nil.
              assert (filter (λ x, x.1 = τ2) ts'_head = [(τ2, Call (encode_request Pop))]) as ->.
              { (* τ2 was called because of Hτ2_started
                   τ2 did not linearize because of Hval_then_not_pr  *)
                (*************** Begin LLM-generated code. ****************)
                (* The prefix is non-empty: τ2 was called before step n *)
                assert (Hτ2_call_in : (τ2, Call (encode_request Pop)) ∈ ts'_head).
                { assert (Hcall_pop := valid_match_call_pop _ _ _ _ Hvalid Hin_m).
                  (* (τ2, Call Pop) ∈ ts. Need it in take n ts. *)
                  assert (Hcall_in_take : (τ2, Call (encode_request Pop)) ∈ take n ts).
                  { (*clear -Hcall_pop Hτ2_started.*)
                    apply list_elem_of_lookup_1 in Hcall_pop as [j Hj].
                    assert (j < length ts) by (eapply lookup_lt_Some; eauto).
                    destruct (decide (j < n)) as [Hjn|Hjn].
                    - eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hj|lia].
                    - exfalso.
                      replace j with (n+(j-n)) in Hj by lia.
                      rewrite -lookup_drop in Hj.
                      destruct (list_elem_of_split_length _ _ _ Hj) as (l1 & l2 & Hdrop_eq & Hlen).
                      rewrite Hdrop_eq in Hτ2_started.
                      contradict Hτ2_started.
                      apply trace_pendingOp_call_middle_elem_of.
                      rewrite -Hdrop_eq.
                      eapply per_tag_partial_wellformed_suffix; first apply suffix_drop.
                      apply per_tag_wellformed_per_tag_partial_wellformed.
                      apply per_tag_complete_per_tag_wellformed.
                      done. }
                  rewrite Hfilter in Hcall_in_take.
                  exact (list_elem_of_filter_1 _ _ _ Hcall_in_take). }
                (* τ2 NOT linearized: if τ2 ∈ ts'_head_lin.*1, then by Hval_then_not_pr,
                   [τ1; τ2] sublist. But τ1 ∉ ts'_head_lin.*1 (call_at_n_no_events). *)
                assert (Hτ2_not_lin : τ2 ∉ (filter (is_lin ∘ snd) ts'_head).*1).
                { intro Habs.
                  assert (Hτ1_no_events := call_at_n_no_events n τ1 _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin).
                  assert (Hsub := Hval_then_not_pr τ1 τ2 Hin_m Habs).
                  (* [τ1; τ2] sublist of ts'_head_lin.*1. But τ1 ∉ ts'_head_lin.*1. *)
                  apply sublist_cons_l in Hsub as (la & la' & Heq_sub & _).
                  assert (Hτ1_in : τ1 ∈ (filter (is_lin ∘ snd) ts'_head).*1).
                  { rewrite Heq_sub. apply elem_of_app. right. left. }
                  apply list_elem_of_fmap_1 in Hτ1_in as ([τ1' ev1] & Heq1 & Hin1).
                  simpl in Heq1. subst τ1'.
                  apply list_elem_of_filter in Hin1 as [Hlin1 Hin1'].
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hin1'; last done.
                  rewrite Hτ1_no_events in Hin1'. set_solver. }
                destruct (filter (λ x, x.1 = τ2) ts'_head) as [|hd [|hd2 rest2]] eqn:Hfilt2.
                - (* Empty: contradicts τ2 Call in ts'_head *)
                  exfalso. apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hτ2_call_in; last done.
                  rewrite Hfilt2 in Hτ2_call_in. clear -Hτ2_call_in. set_solver.
                - (* Singleton: hd = (τ2, Call Pop) *)
                  f_equal.
                  apply prefix_cons_inv_1 in Hprefix₀. rewrite Hprefix₀.
                  assert (Hcall_pop := valid_match_call_pop _ _ _ _ Hvalid Hin_m).
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hcall_pop; last done.
                  destruct (Hwf τ2) as [(vp & _ & Hpfx2)|(rp & _ & Hpfx2)].
                  + (* push pattern: Call (SOMEV vp). But τ2 is a pop, not a push. *)
                    pose proof (elem_of_prefix _ _ _ Hcall_pop Hpfx2) as Hm.
                    rewrite !elem_of_cons elem_of_nil right_id in Hm.
                    destruct Hm as [Hm|Hm]; apply (f_equal snd) in Hm; simpl in Hm; discriminate.
                  + (* pop pattern *)
                    subst hd.
                    assert (Hhd_in_filt : (τ2, Call v₀) ∈ filter (λ x, x.1 = τ2) ts).
                    { apply list_elem_of_filter_2; first done.
                      assert (Hin_ts'_head : (τ2, Call v₀) ∈ ts'_head).
                      { apply (list_elem_of_filter_1 (λ x, x.1 = τ2)). rewrite Hfilt2. clear. set_solver. }
                      assert (Hnot_lin : (not ∘ is_lin ∘ snd) (τ2, Call v₀)).
                      { simpl. auto. }
                      eapply (elem_of_prefix (take n _)); last apply prefix_take.
                      rewrite Hfilter. apply list_elem_of_filter_2; [exact Hnot_lin|exact Hin_ts'_head]. }
                    pose proof (elem_of_prefix _ _ _ Hhd_in_filt Hpfx2) as Hpos.
                    rewrite !elem_of_cons elem_of_nil right_id in Hpos.
                    destruct Hpos as [Hpos|Hpos]; [exact Hpos|].
                    exfalso. discriminate Hpos.
                - (* Two or more: prefix has ≥ 2 elements, meaning Lin exists → contradiction *)
                  exfalso.
                  apply prefix_cons_inv_2 in Hprefix₀.
                  apply prefix_cons_inv_1 in Hprefix₀ as ->.
                  (* hd2 = (τ2, Lin w2 w2') → τ2 linearized → contradiction with Hτ2_not_lin *)
                  apply Hτ2_not_lin.
                  apply (list_elem_of_fmap_2 fst _ (τ2, Lin v₀ v₀')).
                  apply list_elem_of_filter_2; first by simpl.
                  apply (list_elem_of_filter_1 (λ x, x.1 = τ2)).
                  rewrite Hfilt2. clear. set_solver.
                (**************** End LLM-generated code. *****************)}
              eexists. reflexivity.
            ++exists v₀, v₀'.
              do 3 rewrite filter_cons_False //.
              rewrite filter_nil right_id.
              assumption.
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            eapply linearized_sound_app; first eassumption.
            eapply linearized_sound_cons; first by (left; exists v_push;
              split; [eapply per_tag_wellformed_bag_valid_push_value; eauto|reflexivity]).
            { eexists. split; first reflexivity.
              split; reflexivity. }
            eapply (linearized_sound_cons _ s); first by (right; reflexivity).
            { eexists. split; first reflexivity.
              right. eexists v_push.
              split_and!.
              - set_solver.
              - clear. multiset_solver.
              - reflexivity. }
            apply linearized_sound_nil.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            (*************** Begin LLM-generated code. ****************)
            rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_cons_True in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_cons_True in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil fmap_app in Hτ2_bounded₀ |- *.
            simpl in Hτ2_bounded₀ |- *. (*rewrite right_id_L in Hτ2_bounded₀ |- *.*)
            rewrite elem_of_app in Hτ2_bounded₀.
            destruct Hτ2_bounded₀ as [Hτ2_old | Hτ2_new].
            { apply sublist_inserts_r. eapply Hval_then_not_pr; eassumption. }
            rewrite !elem_of_cons elem_of_nil in Hτ2_new.
            destruct Hτ2_new as [-> | [-> | []]].
            ++ (* τ2₀ = τ1: (τ1₀,τ1) ∈ m means τ1 is a pop. But τ1 is a push. *)
              exfalso.
              pose proof (valid_match_call_pop ts m _ _ Hvalid Hin_m₀) as Hτ1_pop.
              (* τ1 was called as Push, but valid_match says it's called as Pop *)
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hτ1_pop; last done.
              apply list_elem_of_lookup_2 in Hlookup as Hin_ts.
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hin_ts; last done.
              destruct (Hcomplete τ1) as (vc & vc' & [Heq_c | Heq_c]).
              { rewrite Heq_c in Hin_ts. clear -Hin_ts. set_solver. }
              rewrite Heq_c in Hin_ts, Hτ1_pop.
              rewrite !elem_of_cons !elem_of_nil !right_id in Hin_ts, Hτ1_pop.
              destruct Hin_ts as [Hin_ts | Hin_ts]; [|discriminate].
              destruct Hτ1_pop as [Hτ1_pop | Hτ1_pop]; [|discriminate].
              injection Hin_ts as <-. injection Hτ1_pop as Heq_call.
              discriminate.
            ++ (* τ2₀ = τ2: [τ1₀;τ2] sublist *)
              assert (Heq_τ1: τ1₀ = τ1).
              { by eapply valid_match_inj_call. }
              subst τ1₀.
              apply sublist_inserts_l. reflexivity.
            (**************** End LLM-generated code. *****************)
          --(* Hstate_of_trace *)
            by rewrite (state_of_trace_call_push n τ1 v_push Hlookup).
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            (*************** Begin LLM-generated code. ****************)
            rewrite /ts'_head_lin filter_app in Hτ₀_not_lin.
            rewrite filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_not_lin. simpl in Hτ₀_not_lin.
            assert (Hτ₀_not_lin_old : τ₀ ∉ (filter (is_lin ∘ snd) ts'_head).*1) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_ne_τ1 : τ₀ ≠ τ1) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_ne_τ2 : τ₀ ≠ τ2) by (clear -Hτ₀_not_lin; set_solver).
            (* τ₀ ∈ trace_pendingOp (drop (S n) ts). Derive τ₀ ∈ trace_pendingOp (drop n ts). *)
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ1 (encode_request (Push v_push))
                                   (drop (Datatypes.S n) ts)).
              clear -Hsubset Hτ₀_pending Hτ₀_ne_τ1 Hτ₀_ne_τ2.
              set_solver. }
            destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin_old) Hτ₀_pop_emp)
              as (icall & Hicall_lookup & Hicall_covers).
            exists icall. split; first assumption.
            intros i Hi.
            destruct (decide (i = n)) as [-> | Hne].
            ++ (* Position n is a Call Push. Same argument as in the not-started case. *)
              assert (Hn_gt_icall : icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. injection Hicall_lookup as _ Habs.
                discriminate. }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              exists τ1c, τ2c.
              rewrite /push_pop_covers in Hcover |- *.
              destruct (ret_of_tag ts τ1c) as [[iret ?]|]; [|done].
              destruct (call_of_tag ts τ2c) as [[icall_c [? t_c]]|] eqn:Hicall_c; [|done].
              simpl in Hcover |- *.
              split; first done.
              cut (icall_c ≠ n); first lia.
              intros ->.
              rewrite /call_of_tag list_find_Some /= in Hicall_c.
              destruct Hicall_c as (Hlookup' & [-> His_call] & _).
              destruct t_c as [v_c | |]; [|apply His_call..].
              opose proof (valid_match_lookup_call_pop _ _ _ _ _ _ _ Hvalid Hinm Hlookup') as ->.
              { by eapply per_tag_wellformed_bag_wellformed. }
              rewrite Hlookup' in Hlookup. discriminate Hlookup.
            ++ apply Hicall_covers. lia.
            (**************** End LLM-generated code. *****************)
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            (*************** Begin LLM-generated code. ****************)
            (* ts'_head_lin.*1 = old ++ [τ1; τ2]. τ₀ ∈ ts'_head_lin.*1. *)
            rewrite /ts'_head_lin filter_app in Hτ₀_lin.
            rewrite filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_lin. simpl in Hτ₀_lin.
            apply elem_of_app in Hτ₀_lin as [Hτ₀_lin_old | Hτ₀_lin_new].
            ++(* τ₀ was already linearized before step n *)
              assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
              { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
                assert (Hsubset := trace_pendingOp_call τ1 (encode_request (Push v_push))
                                     (drop (Datatypes.S n) ts)).
                assert (Hne: τ₀ ≠ τ1).
                { intros <-.
                  exact (call_at_n_not_linearized n τ₀ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin Hτ₀_lin_old). }
                clear -Hsubset Hne Hτ₀_pending.
                set_solver. }
              destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin_old) Hτ₀_push)
                as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
              exists τ2_0. split; first assumption.
              rewrite /ts'_head_lin filter_app.
              rewrite filter_cons_False; last by simpl; auto.
              rewrite filter_cons_True; last by simpl; auto.
              rewrite filter_cons_True; last by simpl; auto.
              rewrite filter_nil fmap_app. simpl. clear -Hτ2_0_lin. set_solver.
            ++(* τ₀ was just linearized: τ₀ ∈ [τ1; τ2] *)
              rewrite !elem_of_cons elem_of_nil right_id in Hτ₀_lin_new.
              destruct Hτ₀_lin_new as [-> | ->].
              **(* τ₀ = τ1: matched pop is τ2, which we just linearized *)
                exists τ2. split; first assumption.
                rewrite /ts'_head_lin filter_app.
                rewrite filter_cons_False; last by simpl; auto.
                rewrite filter_cons_True; last by simpl; auto.
                rewrite filter_cons_True; last by simpl; auto.
                rewrite filter_nil fmap_app. simpl. clear. set_solver.
              **(* τ₀ = τ2: but τ2 is a pop, not a push. Contradiction. *)
                exfalso.
                eapply push_xor_pop_of_trace; [exact Hwf|exact Hτ₀_push|].
                rewrite /pop_of_trace.
                apply (list_elem_of_fmap_2 fst _ (τ2, Call (encode_request Pop))).
                apply list_elem_of_filter_2; [simpl; done|].
                exact (valid_match_call_pop _ _ _ _ Hvalid Hin_m).
            (**************** End LLM-generated code. *****************)
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ1₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ2₀_called.
            simpl in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app
              filter_cons_False; [|by simpl; auto].
            rewrite filter_cons_True; [|by simpl; auto].
            rewrite filter_cons_True; [|by simpl; auto].
            rewrite filter_nil fmap_app /=.
            apply elem_of_app in Hτ1₀_called as [Hτ1₀_old | Hτ1₀_new];
            apply elem_of_app in Hτ2₀_called as [Hτ2₀_old | Hτ2₀_new].
            ++ apply elem_of_app. left. exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_old Hτ2₀_old).
            ++ (* τ2₀ = τ1: push as pop — contradiction *)
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [->|[]].
               exfalso. exact (push_xor_pop_of_trace ts _ _ _ Hwf
                 (matched_push_in_push_of_trace _ _ Hin_m)
                 (matched_pop_in_pop_of_trace _ _ Hin_m₀)).
            ++ (* τ1₀ = τ1: (τ1, τ2₀) ∈ m → τ2₀ = τ2 → τ2 just linearized *)
               rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               assert (τ2₀ = τ2) by (by eapply valid_match_inj_ret). subst τ2₀.
               apply elem_of_app. right. clear. set_solver.
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [Heq2|[]].
               exfalso. subst. refine (valid_match_ne _ _ _ _ _ Hvalid Hin_m₀ eq_refl).
               apply per_tag_complete_per_tag_wellformed, Hcomplete.
          --(* Hpop_lin_consistent *)
            (*************** Begin LLM-generated code. ****************)
            intros τ₀ v₀_c v₀'_c Hτ₀_pop Hin_lin.
            apply elem_of_app in Hin_lin as [Hlin_old | Hlin_new].
            { exact (Hpop_lin_consistent _ _ _ Hτ₀_pop Hlin_old). }
            rewrite !elem_of_cons elem_of_nil in Hlin_new.
            destruct Hlin_new as [Habs | [Habs | [Heq_lin | []]]].
            ++ (* (τ1,Call Push) — not a Lin *) discriminate.
            ++ (* (τ1,Lin Push #()) — τ₀ = τ1 is a push, not a pop *)
               exfalso.
               apply (f_equal fst) in Habs. simpl in Habs. subst τ₀.
               exact (push_xor_pop_of_trace ts _ _ _ Hwf
                 (matched_push_in_push_of_trace _ _ Hin_m) Hτ₀_pop).
            ++ (* (τ2,Lin Pop (NonEmpty v_push)) — τ₀ = τ2, matched, NonEmpty *)
               injection Heq_lin as -> _ ->.
               rewrite bool_decide_eq_true_2; last by (apply (list_elem_of_fmap_2 snd _ (τ1,τ2)); exact Hin_m).
               exists τ1, v_push. split_and!; [exact Hin_m| |done].
               apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). exact Hin_filter_tag.
            (**************** End LLM-generated code. *****************)
        * (* If the matched Pop hasn't started, don't linearize *)
          exists (ts'_head ++ [(τ1,Call (encode_request (Push v_push)))]), s.
          intros ts'_head_lin. split_and!.
          (*************** Begin LLM-generated code. ****************)
          --(* Hfilter *)
            rewrite filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            rewrite (take_S_r _ _ _ Hlookup).
            f_equal. done.
          --(* Hper_tag_lin *)
            intro τ₀.
            specialize (Hper_tag_lin τ₀) as (v₀ & v₀' & Hprefix₀).
            rewrite filter_app.
            destruct (decide (τ₀ = τ1)) as [-> | Hτ₀_ne_τ1].
            ++exists (encode_request (Push v_push)), #().
              rewrite filter_cons_True //.
              rewrite filter_nil.
              (* filter for τ1 in ts'_head is [] because Call Push at n is the first event for τ1 *)
              destruct (filter (λ x, x.1 = τ1) ts'_head) as [|t l] eqn:Heq; last first.
              { exfalso.
                apply prefix_cons_inv_1 in Hprefix₀. subst t.
                assert (Hτ1_called: (τ1, Call v₀) ∈ take n ts).
                { rewrite Hfilter.
                  apply (list_elem_of_filter_2); first by auto.
                  apply (list_elem_of_filter_1 (λ x, x.1 = τ1)).
                  rewrite Heq. set_solver. }
                pose proof (Hts_eq := (take_drop n ts)).
                destruct (list_elem_of_split _ _ Hτ1_called) as (l1 & l2 & Hts_head_eq).
                rewrite Hts_head_eq in Hts_eq.
                replace n with (n+0) in Hlookup by lia.
                rewrite -lookup_drop in Hlookup.
                destruct (list_elem_of_split_length _ _ _ Hlookup)
                  as (l3 & l4 & Hts_tail_eq & ->%eq_comm%nil_length_inv).
                rewrite left_id in Hts_tail_eq.
                rewrite Hts_tail_eq in Hts_eq.
                rewrite -assoc in Hts_eq.
                apply (f_equal (filter (λ x, x.1 = τ1))) in Hts_eq.
                rewrite !filter_app !filter_cons_True // in Hts_eq.
                destruct (Hcomplete τ1) as (? & ? & [Heq1 | Heq1]); rewrite Heq1 in Hts_eq.
                - apply (f_equal length) in Hts_eq.
                  rewrite !length_app length_cons length_nil in Hts_eq.
                  lia.
                - apply (f_equal (filter (is_call∘snd))) in Hts_eq.
                  rewrite !filter_app in Hts_eq.
                  do 3 rewrite filter_cons_True // in Hts_eq.
                  rewrite filter_cons_False in Hts_eq; last by simpl; auto.
                  rewrite filter_nil in Hts_eq.
                  apply (f_equal length) in Hts_eq.
                  rewrite !length_app !length_cons length_nil in Hts_eq.
                  lia. }
              rewrite left_id.
              eexists. reflexivity.
            ++exists v₀, v₀'.
              rewrite filter_cons_False; last by simpl; auto.
              rewrite filter_nil right_id. assumption.
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            assumption.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil right_id in Hτ2_bounded₀ |- *.
            eapply Hval_then_not_pr; eassumption.
          --(* Hstate_of_trace *)
            by rewrite (state_of_trace_call_push n τ1 v_push Hlookup).
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_nil right_id in Hτ₀_not_lin.
            assert (Hτ₀_pending_old: τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
              rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ1 (encode_request (Push v_push))
                                   (drop (Datatypes.S n) ts)).
              assert (Hne_τ₀ : τ₀ ≠ τ1). {
                intros <-.
                rewrite /pop_emp_of_trace in Hτ₀_pop_emp.
                apply list_elem_of_fmap_1 in Hτ₀_pop_emp as ([τ₀' ev_emp] & Heq_tag & Hin_emp).
                simpl in Heq_tag. subst τ₀'.
                apply list_elem_of_filter in Hin_emp as [Heq_ev Hin_emp].
                rewrite /is_ret_pop_emp /= in Heq_ev. subst ev_emp.
                apply list_elem_of_lookup_2 in Hlookup as Hin_push.
                apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_emp; last done.
                apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin_push; last done.
                destruct (Hwf τ₀) as [(w & _ & Hpfx)|(r & _ & Hpfx)];
                  [pose proof (elem_of_prefix _ _ _ Hin_emp Hpfx) as Hp
                  |pose proof (elem_of_prefix _ _ _ Hin_push Hpfx) as Hp];
                  rewrite !elem_of_cons elem_of_nil right_id in Hp;
                  destruct Hp as [Hp|Hp]; apply (f_equal snd) in Hp; simpl in Hp; discriminate.
              }
              set_solver. }
            destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin) Hτ₀_pop_emp)
              as (icall & Hicall_lookup & Hicall_covers).
            exists icall. split; first assumption.
            intros i Hi.
            destruct (decide (i = n)) as [-> | Hne].
            ++ (* Position n is a Call Push. The pair covering n-1 also covers n
                  because the event at n is not a pop Call. *)
              assert (Hn_gt_icall: icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. injection Hicall_lookup as _ Habs.
                discriminate. }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              exists τ1c, τ2c.
              rewrite /push_pop_covers in Hcover |- *.
              destruct (ret_of_tag ts τ1c) as [[iret ?]|]; [|done].
              destruct (call_of_tag ts τ2c) as [[icall_c [? t_c]]|] eqn:Hicall_c; [|done].
              simpl in Hcover |- *.
              (* icall_c > n because ts[n] = Call Push, not a tag matching τ2c *)
              split; first done.
              cut (icall_c ≠ n); first lia.
              intros ->.
              rewrite /call_of_tag list_find_Some /= in Hicall_c.
              destruct Hicall_c as (Hlookup' & [-> His_call] & _).
              destruct t_c as [v_c | |]; [|apply His_call..].
              opose proof (valid_match_lookup_call_pop _ _ _ _ _ _ _ Hvalid Hinm Hlookup') as ->.
              { by eapply per_tag_wellformed_bag_wellformed. }
              rewrite Hlookup' in Hlookup. discriminate Hlookup.
            ++apply Hicall_covers. lia.
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil right_id in Hτ₀_lin.
            assert (Hτ₀_pending_old: τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
              rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ1 (encode_request (Push v_push))
                                   (drop (Datatypes.S n) ts)).
              assert (Hne_τ₀ : τ₀ ≠ τ1). {
                intros <-.
                exact (call_at_n_not_linearized n τ₀ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin Hτ₀_lin).
              }
              clear -Hsubset Hτ₀_pending Hne_τ₀. set_solver. }
            destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin) Hτ₀_push)
              as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
            exists τ2_0. split; first assumption.
            rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            exact Hτ2_0_lin.
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ1₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ2₀_called.
            simpl in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            apply elem_of_app in Hτ1₀_called as [Hτ1₀_old | Hτ1₀_new];
            apply elem_of_app in Hτ2₀_called as [Hτ2₀_old | Hτ2₀_new].
            ++ exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_old Hτ2₀_old).
            ++ (* τ2₀ = τ1: push as pop — contradiction *)
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [->|[]].
               exfalso.
               assert (Hτ1_push : τ1 ∈ push_of_trace ts).
               { destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcp].
                 apply (list_elem_of_fmap_2 fst _ (τ1, Call (encode_request (Push vp)))).
                 apply list_elem_of_filter_2; [eexists; done|exact Hcp]. }
               assert (Hτ1_pop : τ1 ∈ pop_of_trace ts).
               { apply (list_elem_of_fmap_2 fst _ (τ1, Call (encode_request Pop))).
                 apply list_elem_of_filter_2; [done|exact (valid_match_call_pop ts m _ _ Hvalid Hin_m₀)]. }
               exact (push_xor_pop_of_trace ts _ _ _ Hwf Hτ1_push Hτ1_pop).
            ++ (* τ1₀ = τ1, τ2₀ old: (τ1, τ2₀) ∈ m → τ2₀ = τ2 → τ2 ∈ call_tags(take n). *)
               (* τ1₀ = τ1 → τ2₀ = τ2 *)
               rewrite elem_of_cons elem_of_nil in Hτ1₀_new.
               destruct Hτ1₀_new as [->|[]].
               assert (Heq_τ2₀ : τ2₀ = τ2).
               { exact (valid_match_inj_ret ts m _ _ _ Hvalid Hin_m₀ Hin_m). }
               subst τ2₀.
               (* From per_tag_complete: τ2 has both Call and Ret. *)
               destruct (Hcomplete τ2) as (vc_τ2 & vc_τ2' & [Hfilt_empty | Hfilt_eq]).
               { (* filter = []: τ2 has no events. But valid_match gives Call Pop ∈ ts. *)
                 pose proof (valid_match_call_pop ts m τ1 τ2 Hvalid Hin_m) as Hcp2.
                 apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hcp2; last done.
                 rewrite Hfilt_empty in Hcp2. clear -Hcp2. set_solver. }
               (* filter = [(Call vc_τ2); (Ret vc_τ2')]. τ2 has Ret at some position. *)
               assert (Hτ2_ret_in : (τ2, Ret vc_τ2') ∈ ts).
               { apply (list_elem_of_filter_1 (λ x, x.1 = τ2)). rewrite Hfilt_eq. clear. set_solver. }
               apply list_elem_of_lookup_1 in Hτ2_ret_in as [k2 Hk2].
               (* From matched_push_call_le_pop_ret: n ≤ k2 *)
               assert (Hk2_ge_n : n ≤ k2).
               { exact (matched_push_call_le_pop_ret _ _ _ _ _ _ Hcomplete Hvalid Hwf Hin_m Hlookup Hk2). }
               (* k2 ≥ n: Ret at position k2 ∈ drop n ts. τ2 is pending. *)
               exfalso.
               assert (k2 ≠ n).
               { intros ->. rewrite Hlookup in Hk2. simplify_eq. }
               assert (Hk2_gt_n : k2 > n) by lia.
               assert (Hτ2_pending : τ2 ∈ trace_pendingOp (drop n ts)).
               { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
                 apply filter_tag_trace_pendingOp.
                 destruct (decide (τ2 = τ1)) as [Heq_τ|Hne_τ].
                 { subst τ2. exfalso. exact (Hτ1_ne_τ2 eq_refl). }
                 rewrite filter_cons_False; last by simpl; auto.
                 rewrite -filter_tag_trace_pendingOp.
                 apply filter_tag_trace_pendingOp.
                 assert (Hret_in_drop : (τ2, Ret vc_τ2') ∈ drop (Datatypes.S n) ts).
                 { replace k2 with (Datatypes.S n + (k2 - Datatypes.S n)) in Hk2 by lia.
                   rewrite -lookup_drop in Hk2. exact (list_elem_of_lookup_2 _ _ _ Hk2). }
                 apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hret_in_drop; last done.
                 destruct (filter (λ x, x.1 = τ2) (drop (Datatypes.S n) ts)) as [|[τ2' ev2'] rest_filt] eqn:Hfilt_τ2.
                 { clear -Hret_in_drop. set_solver. }
                 (* First element is (τ2', ev2'). τ2' = τ2 from filter. *)
                 assert (Hτ2'_eq : τ2' = τ2).
                 { assert (Hhd_in : (τ2', ev2') ∈ filter (λ x, x.1 = τ2) (drop (Datatypes.S n) ts)).
                   { rewrite Hfilt_τ2. clear. set_solver. }
                   apply list_elem_of_filter in Hhd_in as [Hhd_tag _].
                   simpl in Hhd_tag. done. }
                 subst τ2'.
                 (* ev2' is NOT a Call for τ2 (since τ2's Call is in take, not in drop (S n)). *)
                 destruct ev2' as [v_c| |]; last first.
                 - (* Ret: use trace_pendingOp_ret_elem_of *)
                   apply trace_pendingOp_ret_elem_of.
                 - (* Lin: use trace_pendingOp_lin_elem_of *)
                   apply trace_pendingOp_lin_elem_of.
                 - (* Call: impossible — τ2's Call is in take n ts, not in drop (S n). *)
                   exfalso.
                   assert (Hcall_vc_drop : (τ2, Call v_c) ∈ drop (Datatypes.S n) ts).
                   { apply (list_elem_of_filter_1 (λ x, x.1 = τ2)). rewrite Hfilt_τ2. clear. set_solver. }
                   apply list_elem_of_fmap_1 in Hτ2₀_old as ([τ2'' ev2''] & Heq_τ2'' & Hin_take).
                   simpl in Heq_τ2''. subst τ2''.
                   apply list_elem_of_filter in Hin_take as [Hcall_ev2 Hin_take].
                   destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ2) as (vc_u & vc_u' & Hpfx_u).
                   apply (prefix_filter (is_call∘snd)) in Hpfx_u.
                   rewrite filter_cons_True in Hpfx_u; last done.
                   rewrite filter_cons_False in Hpfx_u; last by simpl; auto.
                   rewrite filter_nil in Hpfx_u.
                   rewrite -(take_drop (Datatypes.S n) ts) !filter_app in Hpfx_u.
                   apply prefix_length in Hpfx_u. rewrite !length_app length_cons length_nil in Hpfx_u.
                   assert (Hcall_take : (τ2, ev2'') ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (take (Datatypes.S n) ts))).
                   { apply list_elem_of_filter_2; [exact Hcall_ev2|]. apply list_elem_of_filter_2; [done|].
                     apply list_elem_of_lookup_1 in Hin_take as [i_take Hi_take].
                     apply lookup_take_Some in Hi_take as [Hi_take Hilt].
                     eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hi_take|lia]. }
                   assert (Hcall_drop : (τ2, Call v_c) ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (drop (Datatypes.S n) ts))).
                   { apply list_elem_of_filter_2; [done|]. apply list_elem_of_filter_2; [done|exact Hcall_vc_drop]. }
                   enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (take (Datatypes.S n) ts)))).
                   { enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (drop (Datatypes.S n) ts))));
                     [lia|]; destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (drop (Datatypes.S n) ts)));
                     [clear -Hcall_drop; set_solver|simpl; lia]. }
                   destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (take (Datatypes.S n) ts)));
                     [clear -Hcall_take; set_solver|simpl; lia]. }
               exact (Hτ2_not_started Hτ2_pending).
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [<-|[]].
               exfalso. refine (valid_match_ne _ _ _ _ _ Hvalid Hin_m₀ eq_refl).
               apply per_tag_complete_per_tag_wellformed, Hcomplete.
          --(* Hpop_lin_consistent *)
            exact (pop_lin_consistent_extend_call _ _ _ _ Hpop_lin_consistent).
          (**************** End LLM-generated code. *****************)
      + (* Call Pop IsEmpty *)
        pose proof (Hin':= elem_of_prefix _ _ _ Hin_filter_tag Hprefix).
        rewrite !elem_of_cons elem_of_nil right_id in Hin'.
        destruct Hin' as [Heq | HFalse]; last discriminate HFalse.
        injection Heq as Heq.
        subst v.
        destruct (decide (s = ∅)) as [Hs_is_empty | Hs_not_empty].
        * (* If the current state is already empty, linearize immediately *)
          exists (ts'_head ++ [(τ,Call (encode_request Pop));
            (τ,Lin (encode_request Pop) (encode_response IsEmpty))]), s.
          intros ts'_head_lin. split_and!.
          (*************** Begin LLM-generated code. ****************)
          --(* Hfilter *)
            rewrite filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil.
            rewrite (take_S_r _ _ _ Hlookup).
            f_equal. done.
          --(* Hper_tag_lin *)
            intro τ₀.
            destruct (Hper_tag_lin τ₀) as (v₀ & v₀' & Hprefix₀).
            rewrite filter_app.
            destruct (decide (τ₀ = τ)) as [-> | Hne].
            ++exists (encode_request Pop), (encode_response IsEmpty).
              rewrite filter_cons_True // filter_cons_True // filter_nil.
              rewrite (call_at_n_no_events n τ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin) left_id.
              eexists. reflexivity.
            ++exists v₀, v₀'.
              rewrite filter_cons_False; [|simpl; auto].
              rewrite filter_cons_False; [|simpl; auto].
              rewrite filter_nil right_id. assumption.
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            eapply linearized_sound_app; first eassumption.
            eapply (linearized_sound_cons _ s); first by (right; reflexivity).
            { eexists. split; first reflexivity.
              left. destruct rme; [split_and!; done|exfalso; by apply Hr_ne]. }
            apply linearized_sound_nil.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_cons_True in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil fmap_app in Hτ2_bounded₀ |- *. simpl in Hτ2_bounded₀ |- *.
            rewrite elem_of_app in Hτ2_bounded₀.
            destruct Hτ2_bounded₀ as [Hold | Hnew].
            { apply sublist_inserts_r. eapply Hval_then_not_pr; eassumption. }
            rewrite elem_of_cons elem_of_nil in Hnew. destruct Hnew as [-> | []].
            exfalso.
            destruct Hvalid as (_ & _ & Hptv).
            rewrite Forall_forall in Hptv.
            destruct (Hptv _ Hin_m₀) as (_ & _ & vp & _ & [Hret | Hno_ret]).
            ++ apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hret; last done.
               pose proof (elem_of_prefix _ _ _ Hret Hprefix) as Hret'.
               rewrite !elem_of_cons elem_of_nil right_id in Hret'.
               destruct Hret' as [Habs | Habs]; apply (f_equal snd) in Habs;
                 simpl in Habs; discriminate.
            ++ apply Hno_ret.
               destruct (Hcomplete τ) as (vc & vc' & [Heq_c | Heq_c]).
               ** rewrite Heq_c in Hin_filter_tag. clear -Hin_filter_tag. set_solver.
               ** apply (list_elem_of_fmap_2 fst _ (τ, Ret vc')).
                  apply list_elem_of_filter_2; first by (simpl; eexists; done).
                  apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
                  rewrite Heq_c. set_solver.
          --(* Hstate_of_trace *)
            assert (Hτ_notin_m2 : τ ∉ m.*2).
            { intro Habs. apply list_elem_of_fmap_1 in Habs as ([τ1₀ τ₀'] & Heqτ & Hin_m₀).
              simpl in Heqτ. subst τ₀'.
              destruct Hvalid as (_ & _ & Hptv). rewrite Forall_forall in Hptv.
              destruct (Hptv _ Hin_m₀) as (_ & _ & vp & _ & [Hret | Hno_ret]).
              - apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hret; last done.
                pose proof (elem_of_prefix _ _ _ Hret Hprefix) as Hret'.
                rewrite !elem_of_cons elem_of_nil right_id in Hret'.
                destruct Hret' as [Habs' | Habs']; apply (f_equal snd) in Habs';
                  simpl in Habs'; discriminate.
              - apply Hno_ret.
                destruct (Hcomplete τ) as (vc & vc' & [Heq_c | Heq_c]).
                + rewrite Heq_c in Hin_filter_tag. clear -Hin_filter_tag. set_solver.
                + apply (list_elem_of_fmap_2 fst _ (τ, Ret vc')).
                  apply list_elem_of_filter_2; first by (simpl; eexists; done).
                  apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
                  rewrite Heq_c. set_solver. }
            by rewrite Hstate_of_trace (state_of_trace_call_pop_empty n τ Hτ_notin_m2 Hlookup).
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            (* ts'_head_lin.*1 = old ++ [τ]. τ₀ ∉ ts'_head_lin.*1 ⇒ τ₀ ∉ old ∧ τ₀ ≠ τ. *)
            rewrite /ts'_head_lin filter_app in Hτ₀_not_lin.
            rewrite filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_not_lin. simpl in Hτ₀_not_lin.
            assert (Hτ₀_not_lin_old : τ₀ ∉ (filter (is_lin ∘ snd) ts'_head).*1) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_ne_τ : τ₀ ≠ τ) by (clear -Hτ₀_not_lin; set_solver).
            (* τ₀ ∈ trace_pendingOp (drop (S n) ts) ⇒ τ₀ ∈ trace_pendingOp (drop n ts) *)
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ (encode_request Pop)
                                   (drop (Datatypes.S n) ts)).
              clear -Hsubset Hτ₀_pending Hτ₀_ne_τ.
              set_solver. }
            destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin_old) Hτ₀_pop_emp)
              as (icall & Hicall_lookup & Hicall_covers).
            exists icall. split; first assumption.
            intros i Hi.
            destruct (decide (i = n)) as [-> | Hne].
            ++ (* Position n is Call Pop IsEmpty. The pair covering n-1 also covers n. *)
              assert (Hn_gt_icall : icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. injection Hicall_lookup as Habs.
                exfalso. rewrite /pop_emp_of_trace in Hτ₀_pop_emp.
                apply list_elem_of_fmap_1 in Hτ₀_pop_emp as ([? ?] & ? & ?).
                done. }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              exists τ1c, τ2c. split; [exact Hinm|].
              rewrite /push_pop_covers in Hcover |- *.
              destruct (ret_of_tag ts τ1c) as [[iret ?]|]; [|done].
              destruct (call_of_tag ts τ2c) as [[icall_c [? t_c]]|] eqn:Hicall_c; [|done].
              simpl in Hcover |- *.
              split; first lia.
              cut (icall_c ≠ n); first lia.
              intros ->.
              (* τ2c = τ from call_of_tag at position n. But (τ1c,τ2c) ∈ m ⇒ τ2c ∈ m.*2.
                 And τ ∉ m.*2 (pop-empty). Contradiction. *)
              rewrite /call_of_tag list_find_Some /= in Hicall_c.
              destruct Hicall_c as (Hlookup' & [-> _] & _).
              rewrite Hlookup' in Hlookup. injection Hlookup as ->.
              (* Now τ2c is renamed to τ. (τ1c,τ) ∈ m ⇒ τ ∈ m.*2.
                 But τ ∉ m.*2 (pop-empty). Contradiction. *)
              destruct Hvalid as (_ & _ & Hptv). rewrite Forall_forall in Hptv.
              destruct (Hptv _ Hinm) as (_ & _ & vp & _ & [Hret | Hno_ret]).
              ** apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hret; last done.
                 pose proof (elem_of_prefix _ _ _ Hret Hprefix) as Hret'.
                 rewrite !elem_of_cons elem_of_nil right_id in Hret'.
                 destruct Hret' as [Habs | Habs]; apply (f_equal snd) in Habs;
                   simpl in Habs; discriminate.
              ** apply Hno_ret.
                 destruct (Hcomplete τ) as (vc & vc' & [Heq_c | Heq_c]).
                 --- rewrite Heq_c in Hin_filter_tag. clear -Hin_filter_tag. set_solver.
                 --- apply (list_elem_of_fmap_2 fst _ (τ, Ret vc')).
                     apply list_elem_of_filter_2; first by (simpl; eexists; done).
                     apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
                     rewrite Heq_c. set_solver.
            ++ apply Hicall_covers. lia.
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            (* ts'_head_lin.*1 = old ++ [τ]. τ₀ ∈ old or τ₀ = τ. *)
            rewrite /ts'_head_lin filter_app in Hτ₀_lin.
            rewrite filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_lin. simpl in Hτ₀_lin.
            apply elem_of_app in Hτ₀_lin as [Hτ₀_lin_old | Hτ₀_lin_new].
            ++ (* τ₀ was already linearized before step n *)
              assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
              { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
                assert (Hsubset := trace_pendingOp_call τ (encode_request Pop)
                                     (drop (Datatypes.S n) ts)).
                assert (Hne_τ₀ : τ₀ ≠ τ).
                { intros <-.
                  exact (call_at_n_not_linearized n τ₀ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin Hτ₀_lin_old). }
                clear -Hsubset Hτ₀_pending Hne_τ₀. set_solver. }
              destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin_old) Hτ₀_push)
                as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
              exists τ2_0. split; first assumption.
              rewrite /ts'_head_lin filter_app.
              rewrite filter_cons_False; last by simpl; auto.
              rewrite filter_cons_True; last by simpl; auto.
              rewrite filter_nil fmap_app. simpl. set_solver.
            ++ (* τ₀ = τ: but τ is a pop, not a push. Contradiction. *)
              rewrite elem_of_cons elem_of_nil in Hτ₀_lin_new.
              destruct Hτ₀_lin_new as [-> | []].
              exfalso.
              eapply push_xor_pop_of_trace; [exact Hwf|exact Hτ₀_push|].
              rewrite /pop_of_trace.
              apply (list_elem_of_fmap_2 fst _ (τ, Call (encode_request Pop))).
              apply list_elem_of_filter_2; [done|exact Hin].
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ1₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ2₀_called.
            simpl in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app filter_cons_False; [|by simpl; auto].
            rewrite filter_cons_True; [|by simpl; auto].
            rewrite filter_nil fmap_app /=.
            apply elem_of_app in Hτ1₀_called as [Hτ1₀_old | Hτ1₀_new];
            apply elem_of_app in Hτ2₀_called as [Hτ2₀_old | Hτ2₀_new].
            ++ apply elem_of_app. left. exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_old Hτ2₀_old).
            ++ (* τ2₀ = τ: pop-empty ∉ m.*2. *)
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [->|[]].
               exfalso.
               assert (Hτ_not_m2 : τ ∉ m.*2) by (eapply pop_empty_not_in_m; eauto).
               apply Hτ_not_m2. exact (list_elem_of_fmap_2 snd _ _ Hin_m₀).
            ++ (* τ1₀ = τ: push_xor_pop *)
               rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               exfalso. exact (push_xor_pop_of_trace ts _ _ _ Hwf
                 (matched_push_in_push_of_trace _ _ Hin_m₀)
                 (in_pop_of_trace_from_call_pop _ Hin)).
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [<-|[]].
               exfalso. refine (valid_match_ne _ _ _ _ _ Hvalid Hin_m₀ eq_refl).
               apply per_tag_complete_per_tag_wellformed, Hcomplete.
          --(* Hpop_lin_consistent *)
            intros τ₀ v₀_c v₀'_c Hτ₀_pop Hin_lin.
            apply elem_of_app in Hin_lin as [Hlin_old | Hlin_new].
            { exact (Hpop_lin_consistent _ _ _ Hτ₀_pop Hlin_old). }
            rewrite !elem_of_cons elem_of_nil in Hlin_new.
            destruct Hlin_new as [Habs | [Heq_lin | []]].
            ++ discriminate.
            ++ injection Heq_lin as -> _ ->.
               rewrite bool_decide_eq_false_2; [done|].
               eapply pop_empty_not_in_m; eauto.
          (**************** End LLM-generated code. *****************)
        * (* If the current state is not empty, don't linearize *)
          exists (ts'_head ++ [(τ,Call (encode_request Pop))]), s.
          intros ts'_head_lin. split_and!.
          (*************** Begin LLM-generated code. ****************)
          --(* Hfilter *)
            rewrite filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            rewrite (take_S_r _ _ _ Hlookup).
            f_equal. done.
          --(* Hper_tag_lin *)
            intro τ₀0.
            destruct (Hper_tag_lin τ₀0) as (v₀0 & v₀0' & Hprefix₀0).
            rewrite filter_app.
            destruct (decide (τ₀0 = τ)) as [-> | Hne0]; last first.
            { exists v₀0, v₀0'.
              rewrite filter_cons_False; [|simpl; auto].
              rewrite filter_nil right_id. assumption. }
            exists (encode_request Pop), (encode_response IsEmpty).
            rewrite filter_cons_True // filter_nil.
            rewrite (call_at_n_no_events n τ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin) left_id.
            eexists. reflexivity.
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            assumption.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil right_id in Hτ2_bounded₀ |- *.
            eapply Hval_then_not_pr; eassumption.
          --(* Hstate_of_trace *)
            rewrite Hstate_of_trace.
            apply state_of_trace_filter_irrel.
            rewrite (take_S_r _ _ _ Hlookup) !filter_app.
            rewrite (filter_cons_False (is_ret∘snd)); last by simpl; auto.
            rewrite (filter_cons_True (is_call∘snd)); last by simpl; auto.
            rewrite !filter_nil !right_id !fmap_app /=.
            apply list_filter_ext. intros [τ1₀ τ2₀] Hin_m₀. simpl.
            rewrite elem_of_app elem_of_cons elem_of_nil.
            split; intros [Hm_fst Hm_snd]; (split; [exact Hm_fst|]).
            ++ intros [Hin0|[->|[]]]; [exact (Hm_snd Hin0)|].
               (* τ2₀ = τ but (τ1₀, τ) ∈ m contradicts τ being pop-empty *)
               exfalso.
               destruct Hvalid as (_ & _ & Hptv).
               rewrite Forall_forall in Hptv.
               destruct (Hptv _ Hin_m₀) as (_ & _ & vp & _ & [Hret | Hno_ret]).
               ** apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hret; last done.
                  pose proof (elem_of_prefix _ _ _ Hret Hprefix) as Hret'.
                  rewrite !elem_of_cons elem_of_nil right_id in Hret'.
                  destruct Hret' as [Habs | Habs]; apply (f_equal snd) in Habs;
                    simpl in Habs; discriminate.
               ** apply Hno_ret.
                  destruct (Hcomplete τ) as (vc & vc' & [Heq_c | Heq_c]).
                  --- rewrite Heq_c in Hin_filter_tag. clear -Hin_filter_tag. set_solver.
                  --- apply (list_elem_of_fmap_2 fst _ (τ, Ret vc')).
                      apply list_elem_of_filter_2; first by (simpl; eexists; done).
                      apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
                      rewrite Heq_c. set_solver.
            ++ intros Hin0. apply Hm_snd. left. exact Hin0.
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_nil right_id in Hτ₀_not_lin.
            (* τ ∉ m.*2 because τ is a pop-empty tag *)
            assert (Hτ_not_in_m2 : τ ∉ m.*2).
            { intros Hin_m2.
              apply list_elem_of_fmap_1 in Hin_m2 as ([τ1₀' τ2₀'] & Heq_τ & Hin_m₀').
              simpl in Heq_τ. subst τ2₀'.
              destruct Hvalid as (_ & _ & Hptv).
              rewrite Forall_forall in Hptv.
              destruct (Hptv _ Hin_m₀') as (_ & _ & vp & _ & [Hret | Hno_ret]).
              - apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hret; last done.
                pose proof (elem_of_prefix _ _ _ Hret Hprefix) as Hret'.
                rewrite !elem_of_cons elem_of_nil right_id in Hret'.
                destruct Hret' as [Habs | Habs]; apply (f_equal snd) in Habs;
                  simpl in Habs; discriminate.
              - apply Hno_ret.
                destruct (Hcomplete τ) as (vc & vc' & [Heq_c | Heq_c]).
                + rewrite Heq_c in Hin_filter_tag. clear -Hin_filter_tag. set_solver.
                + apply (list_elem_of_fmap_2 fst _ (τ, Ret vc')).
                  apply list_elem_of_filter_2; first by (simpl; eexists; done).
                  apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
                  rewrite Heq_c. set_solver. }
            (* Position n is covered because state is not empty *)
            assert (Hcovers_n : ∃ τ1c τ2c, (τ1c,τ2c) ∈ m ∧ push_pop_covers ts τ1c τ2c n).
            { rewrite Hstate_of_trace in Hs_not_empty.
              unfold state_of_trace in Hs_not_empty.
              (* The filtered m must be non-empty *)
              destruct (filter (λ '(τ1₀, τ2₀),
                τ1₀ ∈ (filter (is_ret ∘ snd) (take n ts)).*1 ∧
                τ2₀ ∉ (filter (is_call ∘ snd) (take n ts)).*1) m)
                as [|[τ1c τ2c] rest] eqn:Hfilt; last first.
              - (* Non-empty: extract the pair *)
                assert (Hin_m_c : (τ1c, τ2c) ∈ m ∧
                  τ1c ∈ (filter (is_ret ∘ snd) (take n ts)).*1 ∧
                  τ2c ∉ (filter (is_call ∘ snd) (take n ts)).*1).
                { assert (Helem : (τ1c, τ2c) ∈ (τ1c, τ2c) :: rest) by (clear; set_solver).
                  rewrite -Hfilt in Helem.
                  apply list_elem_of_filter in Helem as [[??] ?]. split; [|split]; done. }
                destruct Hin_m_c as (Hin_m_c & Hτ1c_ret & Hτ2c_no_call).
                (* ret_of_tag τ1c ≤ some position < n *)
                apply list_elem_of_fmap_1 in Hτ1c_ret as ([τ1c' ev_ret] & Heq_tag & Hin_ret).
                simpl in Heq_tag. subst τ1c'.
                apply list_elem_of_filter in Hin_ret as [His_ret Hin_take].
                apply list_elem_of_lookup_1 in Hin_take as [i_ret Hi_ret].
                assert (Hi_ret_lt : i_ret < n).
                { apply lookup_lt_Some in Hi_ret.
                  rewrite length_take_le in Hi_ret; last by (apply lookup_lt_Some in Hlookup; lia). lia. }
                assert (Hin_ts_ret : ts !! i_ret = Some (τ1c, ev_ret)).
                { apply lookup_take_Some in Hi_ret. destruct Hi_ret. done. }
                (* call_of_tag τ2c > n *)
                pose proof (valid_match_call_pop ts m _ _ Hvalid Hin_m_c) as Hτ2c_call.
                apply list_elem_of_lookup_1 in Hτ2c_call as [i_call Hi_call].
                assert (Hi_call_ge : i_call ≥ n).
                { destruct (decide (i_call < n)) as [Hlt | ?]; last lia.
                  exfalso. apply Hτ2c_no_call.
                  apply (list_elem_of_fmap_2 fst _ (τ2c, Call (encode_request Pop))).
                  apply list_elem_of_filter_2; first by (simpl; auto).
                  eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hi_call | lia]. }
                assert (Hi_call_gt : i_call > n).
                { destruct (decide (i_call = n)) as [Heq_n | ?]; last lia.
                  subst i_call. rewrite Hlookup in Hi_call.
                  injection Hi_call as <-.
                  exfalso. apply Hτ_not_in_m2.
                  apply (list_elem_of_fmap_2 snd _ (τ1c, τ)). exact Hin_m_c. }
                exists τ1c, τ2c. split; first done.
                rewrite /push_pop_covers.
                (* Get ret_of_tag and call_of_tag *)
                destruct (ret_of_tag_destruct ts τ1c) as [(ir & vr & Hret_eq & Hir_lookup)|Hret_none].
                ++ rewrite Hret_eq /=.
                   destruct (call_of_tag_destruct ts τ2c) as [(ic & vc & Hcall_eq & Hic_lookup)|Hcall_none].
                   ** rewrite Hcall_eq /=.
                      (* ir ≤ i_ret < n < i_call, and ic ≤ i_call *)
                      (* Also ir is the FIRST ret, so ir ≤ i_ret *)
                      assert (Hir_le : ir ≤ i_ret).
                      { rewrite /ret_of_tag in Hret_eq.
                        apply list_find_Some in Hret_eq as (? & ? & Hmin).
                        destruct (decide (ir ≤ i_ret)); [lia|].
                        exfalso. eapply (Hmin i_ret _ Hin_ts_ret); [lia | split; [done | exact His_ret]]. }
                      assert (Hic_gt : n < ic).
                      { (* ic = call_of_tag ts τ2c. No Call for τ2c in take n ts, so ic ≥ n.
                           And τ2c ≠ τ, so ic ≠ n, thus ic > n. *)
                        assert (Hic_ge : ic ≥ n).
                        { destruct (decide (ic < n)) as [Hlt | ?]; last lia.
                          exfalso. apply Hτ2c_no_call.
                          apply (list_elem_of_fmap_2 fst _ (τ2c, Call vc)).
                          apply list_elem_of_filter_2; first by (simpl; auto).
                          eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hic_lookup | lia]. }
                        destruct (decide (ic = n)) as [Heq_n | ?]; last lia.
                        subst ic.
                        rewrite Hlookup in Hic_lookup.
                        injection Hic_lookup as <- _.
                        exfalso. apply Hτ_not_in_m2.
                        apply (list_elem_of_fmap_2 snd _ (τ1c, τ)). exact Hin_m_c. }
                      lia.
                   ** exfalso. rewrite /call_of_tag in Hcall_none.
                      apply list_find_None in Hcall_none.
                      rewrite Forall_forall in Hcall_none.
                      apply (Hcall_none (τ2c, Call (encode_request Pop))).
                      { eapply list_elem_of_lookup_2. exact Hi_call. }
                      split; [done | simpl; auto].
                ++ exfalso. rewrite /ret_of_tag in Hret_none.
                   apply list_find_None in Hret_none.
                   rewrite Forall_forall in Hret_none.
                   apply (Hret_none (τ1c, ev_ret)).
                   { eapply list_elem_of_lookup_2. exact Hin_ts_ret. }
                   split; [done | exact His_ret].
              - (* Filtered m is empty ⟹ state is empty ⟹ contradiction *)
                exfalso.
                assert (Hstate_empty : state_of_trace n = ∅).
                { unfold state_of_trace. rewrite Hfilt.
                  simpl fmap.
                  clear.
                  induction ts as [|[τ' t'] ts' IH]; first by rewrite omap_nil.
                  rewrite omap_cons_None; first exact IH.
                  rewrite bool_decide_eq_false_2; first done.
                  set_solver. }
                unfold state_of_trace in Hstate_empty. rewrite Hfilt in Hstate_empty.
                simpl fmap in Hstate_empty.
                exact (Hs_not_empty Hstate_empty). }
            (* Now handle both cases *)
            destruct (decide (τ₀ = τ)) as [-> | Hne_τ₀_τ].
            ++ (* τ₀ = τ: the tag was just called at position n *)
               exists n. split; first exact Hlookup.
               intros i Hi. assert (i = n) by lia. subst i.
               exact Hcovers_n.
            ++ (* τ₀ ≠ τ: use IH *)
               assert (Hτ₀_pending_old: τ₀ ∈ trace_pendingOp (drop n ts)).
               { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
                 rewrite Hdrop_eq.
                 assert (Hsubset := trace_pendingOp_call τ (encode_request Pop)
                                      (drop (Datatypes.S n) ts)).
                 clear -Hsubset Hτ₀_pending Hne_τ₀_τ.
                 set_solver. }
               destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin) Hτ₀_pop_emp)
                 as (icall & Hicall_lookup & Hicall_covers).
               exists icall. split; first assumption.
               intros i Hi.
               destruct (decide (i = n)) as [-> | Hne_i_n].
               ** exact Hcovers_n.
               ** apply Hicall_covers. lia.
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil right_id in Hτ₀_lin.
            assert (Hτ₀_pending_old: τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
              rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ (encode_request Pop)
                                   (drop (Datatypes.S n) ts)).
              assert (Hne_τ₀ : τ₀ ≠ τ). {
                intros <-.
                exact (call_at_n_not_linearized n τ₀ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin Hτ₀_lin).
              }
              clear -Hsubset Hτ₀_pending Hne_τ₀. set_solver. }
            destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin) Hτ₀_push)
              as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
            exists τ2_0. split; first assumption.
            rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            exact Hτ2_0_lin.
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ1₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ2₀_called.
            simpl in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            apply elem_of_app in Hτ1₀_called as [Hτ1₀_old | Hτ1₀_new];
            apply elem_of_app in Hτ2₀_called as [Hτ2₀_old | Hτ2₀_new].
            ++ exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_old Hτ2₀_old).
            ++ rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [->|[]].
               exfalso.
               assert (Hτ_not_m2 : τ ∉ m.*2) by (eapply pop_empty_not_in_m; eauto).
               apply Hτ_not_m2. exact (list_elem_of_fmap_2 snd _ _ Hin_m₀).
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               exfalso. exact (push_xor_pop_of_trace ts _ _ _ Hwf
                 (matched_push_in_push_of_trace _ _ Hin_m₀)
                 (in_pop_of_trace_from_call_pop _ Hin)).
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [<-|[]].
               exfalso. refine (valid_match_ne _ _ _ _ _ Hvalid Hin_m₀ eq_refl).
               apply per_tag_complete_per_tag_wellformed, Hcomplete.
          --(* Hpop_lin_consistent *)
            apply (pop_lin_consistent_extend_call _ _ _ _ Hpop_lin_consistent).
          (**************** End LLM-generated code. *****************)
      + (* Call Pop NonEmpty *)
        rename τ into τ2.
        pose proof (Hin':= elem_of_prefix _ _ _ Hin_filter_tag Hprefix).
        rewrite !elem_of_cons elem_of_nil right_id in Hin'.
        destruct Hin' as [Heq | HFalse]; last discriminate HFalse.
        injection Heq as Heq.
        subst v.
        assert (Hτ2_in_m: τ2 ∈ m.*2).
        { destruct Hclosed as [_ Hclosed_pop].
          rewrite Forall_forall in Hclosed_pop.
          opose proof (Hclosed_pop τ2 _) as [?|[HFalse | HFalse]].
          { eapply (list_elem_of_fmap_2 fst _ (τ2,_)).
            eapply list_elem_of_filter_2; last exact Hin.
            done. }
          - assumption.
          - exfalso.
            apply (list_elem_of_filter_2 (λ x, x.1=τ2)) in HFalse; last done.
            pose proof (elem_of_prefix _ _ _ HFalse Hprefix) as HFalse'.
            rewrite !elem_of_cons elem_of_nil right_id in HFalse'.
            destruct HFalse'; discriminate.
          - contradict HFalse.
            destruct (Hcomplete τ2) as (v&v'&[Heq|Heq]).
            + rewrite Heq in Hin_filter_tag. clear -Hin_filter_tag. set_solver.
            + apply (list_elem_of_fmap_2 fst _ (τ2,Ret v')).
              apply list_elem_of_filter_2; first done.
              apply (list_elem_of_filter_1 (λ x, x.1=τ2)).
              rewrite Heq.
              set_solver. }
        apply list_elem_of_fmap_1 in Hτ2_in_m.
        destruct Hτ2_in_m as ([τ1 τ2'] & Heqτ2 & Hin_m).
        simpl in Heqτ2. subst τ2'.
        opose proof (valid_match_ne _ _ _ _ _ Hvalid Hin_m) as Hτ1_ne_τ2.
        { apply per_tag_complete_per_tag_wellformed, Hcomplete. }
        destruct (decide (τ1 ∈ trace_pendingOp (drop n ts))) as [Hτ1_pending | Hτ1_not_pending];
        last destruct (decide (τ1 ∈ (filter (is_call∘snd) (drop n ts)).*1)) as [Hτ1_not_started | Hτ1_finished];
        last destruct (decide (s∖{[+ v_pop +]} = ∅)) as [Hemp_after_pop|Hnot_emp_after_pop].
        * (* If the matched Push is pending, linearize both operations *)
          exists (ts'_head ++ [(τ2,Call (encode_request Pop));
            (τ1,Lin (encode_request (Push v_pop)) #());
            (τ2,Lin (encode_request Pop) (encode_response (NonEmpty v_pop)))]), s.
          intros ts'_head_lin. split_and!.
          (*************** Begin LLM-generated code. ****************)
          --(* Hfilter *)
            rewrite filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil.
            rewrite (take_S_r _ _ _ Hlookup).
            f_equal. done.
          --(* Hper_tag_lin *)
            intro τ₀.
            pose proof (Hper_tag_lin' := Hper_tag_lin).
            specialize (Hper_tag_lin' τ₀) as (v₀ & v₀' & Hprefix₀).
            rewrite filter_app.
            destruct (decide (τ₀ = τ2)) as [-> | Hτ₀_ne_τ2];
            last destruct (decide (τ₀ = τ1)) as [-> | Hτ₀_ne_τ1].
            ++exists (encode_request Pop), (encode_response (NonEmpty v_pop)).
              rewrite filter_cons_True // filter_cons_False // filter_cons_True //.
              rewrite filter_nil.
              rewrite (call_at_n_no_events n τ2 _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin) left_id.
              eexists. reflexivity.
            ++exists (encode_request (Push v_pop)), #().
              rewrite filter_cons_False; [|simpl; auto].
              rewrite filter_cons_True // filter_cons_False; [|simpl; auto].
              rewrite filter_nil.
              assert (filter (λ x, x.1 = τ1) ts'_head = [(τ1, Call (encode_request (Push v_pop)))]) as ->.
              { (* τ1 is pending: it was called before. Same argument as in Call Push case. *)
                destruct (filter (λ x, x.1 = τ1) ts'_head) as [|hd [|hd2 rest2]] eqn:Hfilt1.
                - (* Empty: τ1 has no events. *)
                  exfalso.
                  destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcall_push].
                  apply list_elem_of_lookup_1 in Hcall_push as [j Hj].
                  assert (j ≠ n).
                  { intros ->. rewrite Hlookup in Hj. discriminate. }
                  assert (j < length ts) by (eapply lookup_lt_Some; eauto).
                  destruct (decide (j < n)) as [Hjn|Hjn].
                  -- assert (Hin_take : (τ1, Call (encode_request (Push vp))) ∈ take n ts).
                     { eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hj|lia]. }
                     rewrite Hfilter in Hin_take.
                     apply list_elem_of_filter in Hin_take as [_ Hin_head].
                     apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hin_head; last done.
                     rewrite Hfilt1 in Hin_head. clear -Hin_head. set_solver.
                  --replace j with (n + (j - n)) in Hj by lia.
                    rewrite -lookup_drop in Hj.
                    destruct (list_elem_of_split_length _ _ _ Hj) as (l1 & l2 & Heq_drop_n_ts & _).
                    rewrite Heq_drop_n_ts in Hτ1_pending.
                    contradict Hτ1_pending.
                    apply trace_pendingOp_call_middle_elem_of.
                    rewrite -Heq_drop_n_ts.
                    eapply per_tag_partial_wellformed_suffix; first apply suffix_drop.
                    apply per_tag_wellformed_per_tag_partial_wellformed.
                    by eapply per_tag_wellformed_bag_wellformed.
                - (* Singleton [hd]: Good. Show hd = (τ1, Call Push). *)
                  apply prefix_cons_inv_1 in Hprefix₀ as ->. f_equal.
                  assert (Hcall_push := valid_match_call_push _ _ _ _ Hvalid Hin_m).
                  destruct Hcall_push as [vp Hcp].
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcp as Hcp_filt; last done.
                  assert (Hcv_in_ts : (τ1, Call v₀) ∈ ts).
                  { assert (Hin_head : (τ1, Call v₀) ∈ ts'_head).
                    { apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). rewrite Hfilt1. set_solver. }
                    assert (Hcv_in_take : (τ1, Call v₀) ∈ take n ts).
                    { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; by auto|exact Hin_head]. }
                    apply list_elem_of_lookup in Hcv_in_take as [i Hi].
                    eapply list_elem_of_lookup_2.
                    apply lookup_take_Some in Hi as [Hi _]. exact Hi. }
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcv_in_ts as Hcv_filt; last done.
                  destruct (Hwf τ1) as [(vw & _ & Hpfx1)|(rw & _ & Hpfx1)].
                  **destruct (filter (λ x, x.1 = τ1) ts) as [|c1 rest'] eqn:Hfts;
                      [clear -Hcv_filt; set_solver|].
                    apply prefix_cons_inv_1 in Hpfx1 as Hc1. subst c1.
                    pose proof (elem_of_prefix _ _ _ Hcv_filt Hpfx1) as Hpos.
                    rewrite !elem_of_cons elem_of_nil right_id in Hpos.
                    destruct Hpos as [Hpos|Hpos]; last discriminate Hpos.
                    simplify_eq.
                    destruct Hvalid as (_ & _ & Hper_match_valid).
                    rewrite Forall_forall in Hper_match_valid.
                    destruct (Hper_match_valid _ Hin_m) as (_ & _ & v_match & Hcall_match & [Hret_match | Hno_ret]).
                    ---(* τ1 pushed v_match, τ2 returned NonEmpty v_match.
                        vw = v_match from per_tag_wellformed (one Call per tag).
                        v_pop = v_match from τ2's Ret matching. *)
                      assert (Hvw : vw = v_match).
                      { apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_match; last done.
                        rewrite Hfts in Hcall_match.
                        apply elem_of_cons in Hcall_match as [Hcall_match | Hcall_match].
                        - by injection Hcall_match.
                        - exfalso.
                          apply prefix_cons_inv_2 in Hpfx1.
                          pose proof (elem_of_prefix _ _ _ Hcall_match Hpfx1) as Hp.
                          rewrite elem_of_cons elem_of_nil in Hp.
                          destruct Hp as [Hp|[]].
                          apply (f_equal snd) in Hp. simpl in Hp. discriminate. }
                      assert (Hvpop : v_pop = v_match).
                      { apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hret_match; last done.
                        pose proof (elem_of_prefix _ _ _ Hret_match Hprefix) as Hp.
                        rewrite !elem_of_cons elem_of_nil right_id in Hp.
                        destruct Hp as [Hp|Hp]; [|by injection Hp].
                        exfalso. apply (f_equal snd) in Hp. simpl in Hp. discriminate. }
                      simplify_eq. reflexivity.
                    ---(* τ2 has not returned. But from Hprefix (pop pattern), τ2 has a Ret.
                        Contradiction. *)
                      exfalso. apply Hno_ret.
                      apply (list_elem_of_fmap_2 fst _ (τ2, Ret (encode_response (NonEmpty v_pop)))).
                      apply list_elem_of_filter_2; [simpl; eexists; done|].
                      (* (τ2, Ret NonEmpty v_pop) ∈ ts from Hprefix + Hcomplete *)
                      destruct (Hcomplete τ2) as (vc & vc' & [Heq_c2 | Heq_c2]).
                      { rewrite Heq_c2 in Hin_filter_tag. clear -Hin_filter_tag. set_solver. }
                      apply (list_elem_of_filter_1 (λ x, x.1 = τ2)).
                      rewrite Heq_c2 in Hprefix.
                      apply prefix_cons_inv_2, prefix_cons_inv_1 in Hprefix.
                      rewrite Heq_c2 Hprefix. apply elem_of_cons. right. left.
                  **(* pop pattern: τ1 called Pop. But τ1 ∈ m.*1, so τ1 is a push. *)
                    exfalso.
                    pose proof (elem_of_prefix _ _ _ Hcp_filt Hpfx1) as Hm.
                    rewrite !elem_of_cons elem_of_nil right_id in Hm.
                    destruct Hm as [Hm|Hm]; apply (f_equal snd) in Hm; simpl in Hm; discriminate.
                - (* Two or more: Lin exists ⇒ τ1 linearized.
                    But τ1 is pending ⇒ by Hpush_alap, τ2 also linearized.
                    But τ2 just called (call_at_n_no_events ⇒ τ2 has no events). Contradiction. *)
                  exfalso.
                  apply prefix_cons_inv_2 in Hprefix₀.
                  apply prefix_cons_inv_1 in Hprefix₀ as ->. (* hd2 = (τ1, Lin v₀ v₀') *)
                  assert (Hτ1_lin_old : τ1 ∈ (filter (is_lin ∘ snd) ts'_head).*1).
                  { apply (list_elem_of_fmap_2 fst _ (τ1, Lin v₀ v₀')).
                    apply list_elem_of_filter_2; [done|].
                    apply (list_elem_of_filter_1 (λ x, x.1 = τ1)).
                    rewrite Hfilt1. set_solver. }
                  assert (Hτ1_push_of : τ1 ∈ push_of_trace ts).
                  { destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcp].
                    apply (list_elem_of_fmap_2 fst _ (τ1, Call (encode_request (Push vp)))).
                    apply list_elem_of_filter_2; [eexists; done|exact Hcp]. }
                  destruct (Hpush_alap τ1 (conj Hτ1_pending Hτ1_lin_old) Hτ1_push_of)
                    as (τ2' & Hin_m' & Hτ2'_lin).
                  (* τ2' = τ2 from NoDup m.*1 *)
                  assert (τ2' = τ2).
                  { by eapply valid_match_inj_ret. }
                  subst τ2'.
                  (* τ2 linearized in old ts'_head. But call_at_n_no_events says
                     filter(tag=τ2) ts'_head = []. So τ2 has no events ⇒ not linearized. *)
                  pose proof (call_at_n_no_events n τ2 _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin) as Hτ2_none.
                  apply (list_elem_of_fmap_1) in Hτ2'_lin as ([? ev'] & [= <-] & Hin').
                  apply list_elem_of_filter in Hin' as [_ Hin'].
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hin'; last done.
                  rewrite Hτ2_none in Hin'. clear -Hin'. set_solver. }
              eexists. reflexivity.
            ++exists v₀, v₀'.
              do 3 rewrite filter_cons_False //.
              rewrite filter_nil right_id. assumption.
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            eapply linearized_sound_app; first eassumption.
            eapply linearized_sound_cons.
            { (* valid_request (encode_request (Push v_pop)) — derive
                 valid_value v_pop from Hwf and the matching Push call. *)
              left. exists v_pop. split; last reflexivity.
              destruct (Hcomplete τ2) as (v & v' & [HFalse|Hfilter_eq]).
              { apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hin; last done.
                rewrite HFalse in Hin.
                clear -Hin. set_solver. }
              rewrite Hfilter_eq in Hprefix.
              apply prefix_cons_inv_2, prefix_cons_inv_1 in Hprefix.
              injection Hprefix as ->.
              destruct Hvalid as (_ & _ & Hper_match_valid).
              rewrite Forall_forall in Hper_match_valid.
              destruct (Hper_match_valid _ Hin_m) as (_ & _ & vc & Hτ1_in & [Hτ2_in | Hτ2_notin]).
              - enough (vc = v_pop).
                { subst vc. eapply per_tag_wellformed_bag_valid_push_value; eassumption. }
                apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hτ2_in; last done.
                rewrite Hfilter_eq !elem_of_cons elem_of_nil right_id in Hτ2_in.
                destruct Hτ2_in as [HFalse | Heq].
                + discriminate HFalse.
                + injection Heq. done.
              - contradict Hτ2_notin.
                eapply (list_elem_of_fmap_2 fst _ (τ2,_)).
                apply (list_elem_of_filter_1 (λ x, x.1 = τ2)).
                rewrite list_filter_comm Hfilter_eq.
                rewrite filter_cons_False; last by simpl; auto.
                rewrite filter_cons_True; last by simpl; auto.
                rewrite filter_nil.
                apply list_elem_of_singleton.
                reflexivity. }
            { eexists. split; first reflexivity.
              split; reflexivity. }
            eapply (linearized_sound_cons _ s); first by (right; reflexivity).
            { eexists. split; first reflexivity.
              right. eexists v_pop.
              split_and!.
              - set_solver.
              - clear. multiset_solver.
              - reflexivity. }
            apply linearized_sound_nil.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_cons_True in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_cons_True in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil fmap_app in Hτ2_bounded₀ |- *.
            simpl in Hτ2_bounded₀ |- *.
            rewrite elem_of_app in Hτ2_bounded₀.
            destruct Hτ2_bounded₀ as [Hτ2_old | Hτ2_new].
            { apply sublist_inserts_r. eapply Hval_then_not_pr; eassumption. }
            rewrite !elem_of_cons elem_of_nil in Hτ2_new.
            destruct Hτ2_new as [-> | [-> | []]].
            ++ (* τ2₀ = τ1: (τ1₀,τ1) ∈ m means τ1 is a pop. But τ1 is a push. *)
              exfalso.
              pose proof (valid_match_call_pop ts m _ _ Hvalid Hin_m₀) as Hτ1_pop.
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hτ1_pop; last done.
              destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hτ1_push].
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hτ1_push; last done.
              destruct (Hcomplete τ1) as (vc & vc' & [Heq_c | Heq_c]).
              { rewrite Heq_c in Hτ1_push. clear -Hτ1_push. set_solver. }
              rewrite Heq_c in Hτ1_push, Hτ1_pop.
              rewrite !elem_of_cons !elem_of_nil !right_id in Hτ1_push, Hτ1_pop.
              destruct Hτ1_push as [Hτ1_push | Hτ1_push]; [|discriminate].
              destruct Hτ1_pop as [Hτ1_pop | Hτ1_pop]; [|discriminate].
              injection Hτ1_push as <-. injection Hτ1_pop as Heq_call.
              discriminate.
            ++ (* τ2₀ = τ2: Show τ1₀ = τ1 from NoDup m.*2, then [τ1;τ2] sublist *)
              assert (Heq_τ1: τ1₀ = τ1).
              { destruct Hvalid as (_ & [_ Hnodup2] & _).
                apply list_elem_of_lookup_1 in Hin_m₀ as [i₀ Hi₀].
                apply list_elem_of_lookup_1 in Hin_m as [i Hi].
                assert (Hi₀' : m.*2 !! i₀ = Some τ2) by (rewrite list_lookup_fmap Hi₀; done).
                assert (Hi' : m.*2 !! i = Some τ2) by (rewrite list_lookup_fmap Hi; done).
                assert (Heq_i : i₀ = i) by (eapply NoDup_lookup; eassumption).
                subst i₀. rewrite Hi₀ in Hi. injection Hi as ->. done. }
              subst τ1₀.
              apply sublist_inserts_l. reflexivity.
          --(* Hstate_of_trace *)
            rewrite Hstate_of_trace.
            assert (Hτ1_no_ret : τ1 ∉ (filter (is_ret∘snd) (take n ts)).*1).
            { (* τ1 ∉ ret_tags(take n ts): τ1 is pending in drop n ts. *)
            intro Habs. apply list_elem_of_fmap_1 in Habs as ([τ1' ev1] & Heq1 & Hin1).
            simpl in Heq1. subst τ1'.
            apply (list_elem_of_filter) in Hin1 as [His_ret Hin1].
            destruct ev1 as [| |v1]; [by simpl in His_ret..|].
            opose proof (elem_of_trace_pendingOp_inv_ret _ _ _ Hτ1_pending) as [v2 Hin2].
            { eapply per_tag_partial_wellformed_suffix; first apply suffix_drop.
              apply per_tag_wellformed_per_tag_partial_wellformed.
              by eapply per_tag_wellformed_bag_wellformed. }
            destruct (list_elem_of_split _ _ Hin1) as (l1 & l2 & Heq1).
            destruct (list_elem_of_split _ _ Hin2) as (l3 & l4 & Heq2).
            pose proof (take_drop n ts) as Heq.
            rewrite Heq1 Heq2 in Heq.
            destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (?&?&Hprefix').
            apply (f_equal (filter (λ x, x.1 = τ1))) in Heq.
            rewrite -Heq in Hprefix'. clear -Hprefix'.
            rewrite !filter_app !filter_cons_True // in Hprefix'.
            assert (Heq: filter (λ x : positive * trace, x.1 = τ1) l1 = []).
            { apply nil_length_inv.
              apply prefix_length in Hprefix'.
              rewrite !length_app !length_cons length_nil in Hprefix'.
              lia. }
            rewrite Heq left_id -app_comm_cons in Hprefix'.
            apply prefix_cons_inv_1 in Hprefix'.
            discriminate. }
            symmetry. exact (state_of_trace_call_pop_overlap n τ1 τ2 Hin_m Hτ1_no_ret Hlookup).
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            rewrite /ts'_head_lin filter_app in Hτ₀_not_lin.
            rewrite filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_not_lin. simpl in Hτ₀_not_lin.
            assert (Hτ₀_not_lin_old : τ₀ ∉ (filter (is_lin ∘ snd) ts'_head).*1) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_ne_τ1 : τ₀ ≠ τ1) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_ne_τ2 : τ₀ ≠ τ2) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ2 (encode_request Pop)
                                   (drop (Datatypes.S n) ts)).
              clear -Hsubset Hτ₀_pending Hτ₀_ne_τ2.
              set_solver. }
            destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin_old) Hτ₀_pop_emp)
              as (icall & Hicall_lookup & Hicall_covers).
            exists icall. split; first assumption.
            intros i Hi.
            destruct (decide (i = n)) as [-> | Hne_i].
            ++assert (Hn_gt_icall : icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. injection Hicall_lookup as ->.
                exfalso. exact (Hτ₀_ne_τ2 eq_refl). }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              exists τ1c, τ2c. split; [exact Hinm|].
              rewrite /push_pop_covers in Hcover |- *.
              destruct (ret_of_tag ts τ1c) as [[iret_c [? tret]]|] eqn:Hiret; [|done].
              destruct (call_of_tag ts τ2c) as [[icall_c [? tcall]]|] eqn:Hicall; [|done].
              simpl in Hcover |- *.
              cut (icall_c ≠ n); first lia.
              intros ->.
              rewrite /call_of_tag list_find_Some /= in Hicall.
              destruct Hicall as (Hlookup_call & [-> His_call] & _).
              rewrite Hlookup in Hlookup_call. injection Hlookup_call as <- <-.
              assert (τ1c = τ1) as ->.
              { by eapply valid_match_inj_call. }
              rewrite /call_of_tag list_find_Some /= in Hiret.
              destruct Hiret as (Hlookup_ret & [-> His_ret] & _).
              destruct tret as [| |vr]; [apply His_ret..|].
              rewrite -(lookup_take_lt _ n) in Hlookup_ret; last lia.
              opose proof (elem_of_trace_pendingOp_inv_ret _ _ _ Hτ1_pending) as [v2 Hin2].
              { eapply per_tag_partial_wellformed_suffix; first apply suffix_drop.
                apply per_tag_wellformed_per_tag_partial_wellformed.
                by eapply per_tag_wellformed_bag_wellformed. }
              pose proof (take_drop n ts) as Heq_ts.
              destruct (list_elem_of_split_length _ _ _ Hlookup_ret) as (l1 & l2 & Heq1 & _).
              destruct (list_elem_of_split _ _ Hin2) as (l3 & l4 & Heq2).
              rewrite Heq1 Heq2 in Heq_ts.
              destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (?&?&Hprefix').
              apply (f_equal (filter (λ x, x.1 = τ1))) in Heq_ts.
              rewrite -Heq_ts !filter_app !filter_cons_True // in Hprefix'.
              assert (filter (λ x, x.1 = τ1) l1 = []) as Hrw.
              { apply nil_length_inv.
                apply prefix_length in Hprefix'.
                rewrite !length_app !length_cons length_nil in Hprefix'.
                lia. }
              rewrite Hrw left_id_L -app_comm_cons in Hprefix'.
              apply prefix_cons_inv_1 in Hprefix'.
              discriminate Hprefix'.
            ++ apply Hicall_covers. lia.
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            rewrite /ts'_head_lin filter_app in Hτ₀_lin.
            rewrite filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_lin. simpl in Hτ₀_lin.
            apply elem_of_app in Hτ₀_lin as [Hτ₀_lin_old | Hτ₀_lin_new].
            ++ (* τ₀ was already linearized *)
              assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
              { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
                assert (Hsubset := trace_pendingOp_call τ2 (encode_request Pop)
                                     (drop (Datatypes.S n) ts)).
                assert (Hne_τ₀ : τ₀ ≠ τ2).
                { intros <-.
                  exact (call_at_n_not_linearized n τ₀ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin Hτ₀_lin_old). }
                clear -Hsubset Hτ₀_pending Hne_τ₀. set_solver. }
              destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin_old) Hτ₀_push)
                as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
              exists τ2_0. split; first assumption.
              rewrite /ts'_head_lin filter_app.
              rewrite filter_cons_False; last by simpl; auto.
              rewrite filter_cons_True; last by simpl; auto.
              rewrite filter_cons_True; last by simpl; auto.
              rewrite filter_nil fmap_app. simpl. set_solver.
            ++ (* τ₀ ∈ [τ1; τ2] *)
              rewrite !elem_of_cons elem_of_nil right_id in Hτ₀_lin_new.
              destruct Hτ₀_lin_new as [-> | ->].
              ** (* τ₀ = τ1: matched pop is τ2, which we just linearized *)
                exists τ2. split; first assumption.
                rewrite /ts'_head_lin filter_app.
                rewrite filter_cons_False; last by simpl; auto.
                rewrite filter_cons_True; last by simpl; auto.
                rewrite filter_cons_True; last by simpl; auto.
                rewrite filter_nil fmap_app. simpl. set_solver.
              ** (* τ₀ = τ2: pop, not push. Contradiction. *)
                exfalso.
                eapply push_xor_pop_of_trace; [exact Hwf|exact Hτ₀_push|].
                rewrite /pop_of_trace.
                apply (list_elem_of_fmap_2 fst _ (τ2, Call (encode_request Pop))).
                apply list_elem_of_filter_2; [done|exact Hin].
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ1₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ2₀_called.
            simpl in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app
              filter_cons_False; [|by simpl; auto].
            rewrite filter_cons_True; [|by simpl; auto].
            rewrite filter_cons_True; [|by simpl; auto].
            rewrite filter_nil fmap_app /=.
            apply elem_of_app in Hτ1₀_called as [Hτ1₀_old | Hτ1₀_new];
            apply elem_of_app in Hτ2₀_called as [Hτ2₀_old | Hτ2₀_new].
            ++ apply elem_of_app. left. exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_old Hτ2₀_old).
            ++ (* τ2₀ = τ2: just linearized → τ2 ∈ new lin_tags *)
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [->|[]].
               apply elem_of_app. right. clear -Hτ1_ne_τ2. set_solver.
            ++ (* τ1₀ = τ2: push_xor_pop *)
               rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               exfalso. exact (push_xor_pop_of_trace ts _ _ _ Hwf
                 (matched_push_in_push_of_trace _ _ Hin_m₀)
                 (in_pop_of_trace_from_call_pop _ Hin)).
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [<-|[]].
               exfalso. refine (valid_match_ne _ _ _ _ _ Hvalid Hin_m₀ eq_refl).
               apply per_tag_complete_per_tag_wellformed, Hcomplete.
          --(* Hpop_lin_consistent *)
            intros τ₀ v₀_c v₀'_c Hτ₀_pop Hin_lin.
            apply elem_of_app in Hin_lin as [Hlin_old | Hlin_new].
            { exact (Hpop_lin_consistent _ _ _ Hτ₀_pop Hlin_old). }
            rewrite !elem_of_cons elem_of_nil in Hlin_new.
            destruct Hlin_new as [Habs | [Habs | [Heq_lin | []]]].
            ++ discriminate.
            ++ (* (τ1,Lin Push) — τ₀ = τ1 is push, not pop *)
               exfalso.
               apply (f_equal fst) in Habs. simpl in Habs. subst τ₀.
               exact (push_xor_pop_of_trace ts _ _ _ Hwf
                 (matched_push_in_push_of_trace _ _ Hin_m) Hτ₀_pop).
            ++ (* (τ2,Lin Pop NonEmpty) — τ₀ = τ2, matched *)
               injection Heq_lin as -> _ ->.
               rewrite bool_decide_eq_true_2; last by (apply (list_elem_of_fmap_2 snd _ (τ1,τ2)); exact Hin_m).
               exists τ1, v_pop. split_and!; [exact Hin_m| |done].
               destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcp].
               (* vp = v_pop: from valid_match Forall + per_tag_wellformed uniqueness *)
               enough (vp = v_pop) as -> by exact Hcp.
               destruct Hvalid as (_ & _ & Hforall_vm). rewrite Forall_forall in Hforall_vm.
               destruct (Hforall_vm _ Hin_m) as (_ & _ & v_m & Hcall_m & [Hret_m | Hno_ret]).
               ** apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hret_m; last done.
                  pose proof (elem_of_prefix _ _ _ Hret_m Hprefix) as Hin_pfx.
                  rewrite !elem_of_cons elem_of_nil right_id in Hin_pfx.
                  destruct Hin_pfx as [Hin_pfx|Hin_pfx]; [discriminate|].
                  assert (Hvm_eq : v_m = v_pop) by (simplify_eq; done). subst v_m.
                  destruct (Hwf τ1) as [(vc1 & _ & Hpfx_τ1) | (vc1 & _ & Hpfx_τ1)].
                  --- apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcp; last done.
                      apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_m; last done.
                      pose proof (elem_of_prefix _ _ _ Hcp Hpfx_τ1) as Hin1.
                      pose proof (elem_of_prefix _ _ _ Hcall_m Hpfx_τ1) as Hin2.
                      rewrite !elem_of_cons !elem_of_nil in Hin1, Hin2.
                      destruct Hin1 as [Hin1|[Hin1|[]]]; destruct Hin2 as [Hin2|[Hin2|[]]];
                        try (apply (f_equal snd) in Hin1; by simpl in Hin1);
                        try (apply (f_equal snd) in Hin2; by simpl in Hin2).
                      simplify_eq. done.
                  --- exfalso.
                      apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcp; last done.
                      pose proof (elem_of_prefix _ _ _ Hcp Hpfx_τ1) as Hin1.
                      rewrite !elem_of_cons !elem_of_nil in Hin1.
                      destruct Hin1 as [Hin1|[Hin1|[]]]; apply (f_equal snd) in Hin1; by simpl in Hin1.
               ** exfalso. apply Hno_ret.
                  destruct (Hcomplete τ2) as (vc2 & vc2' & [Hfilt_empty2|Hfilt_eq2]).
                  { pose proof (valid_match_call_pop ts m τ1 τ2 Hvalid Hin_m) as Hcp2.
                    apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hcp2; last done.
                    rewrite Hfilt_empty2 in Hcp2. clear -Hcp2. set_solver. }
                  apply (list_elem_of_fmap_2 fst _ (τ2, Ret vc2')).
                  apply list_elem_of_filter_2; [simpl; eexists; done|].
                  apply (list_elem_of_filter_1 (λ x, x.1 = τ2)). rewrite Hfilt_eq2. clear. set_solver.
          (**************** End LLM-generated code. *****************)
        * (* If the matched Push hasn't started, linearize nothing *)
          exists (ts'_head ++ [(τ2,Call (encode_request Pop))]), s.
          intros ts'_head_lin. split_and!.
          (*************** Begin LLM-generated code. ****************)
          --(* Hfilter *)
            rewrite filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            rewrite (take_S_r _ _ _ Hlookup).
            f_equal. done.
          --(* Hper_tag_lin *)
            intro τ₀0.
            destruct (Hper_tag_lin τ₀0) as (v₀0 & v₀0' & Hprefix₀0).
            rewrite filter_app.
            destruct (decide (τ₀0 = τ2)) as [-> | Hne0]; last first.
            { exists v₀0, v₀0'.
              rewrite filter_cons_False; [|simpl; auto].
              rewrite filter_nil right_id. assumption. }
            exists (encode_request Pop), (encode_response (NonEmpty v_pop)).
            rewrite filter_cons_True // filter_nil.
            rewrite (call_at_n_no_events n τ2 _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin) left_id.
            eexists. reflexivity.
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            assumption.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil right_id in Hτ2_bounded₀ |- *.
            eapply Hval_then_not_pr; eassumption.
          --(* Hstate_of_trace *)
            rewrite Hstate_of_trace.
            assert (Hτ1_no_ret : τ1 ∉ (filter (is_ret∘snd) (take n ts)).*1).
            { (* τ1 not started: filter(tag=τ1)(take n ts) = []. *)
              intro Habs.
              apply list_elem_of_fmap_1 in Habs as ([τ1' ev1] & Heq1 & Hin1).
              simpl in Heq1. subst τ1'.
              apply list_elem_of_filter in Hin1 as [His_ret Hin1].
              destruct ev1 as [| |v1]; [by simpl in His_ret..|].
              (* (τ1, Ret v1) ∈ take n ts. τ1's Call is in drop n ts. *)
              apply list_elem_of_fmap_1 in Hτ1_not_started as ([τ1'' ev_c] & Heq_c & Hin_c).
              simpl in Heq_c. subst τ1''.
              apply list_elem_of_filter in Hin_c as [His_call Hin_c].
              destruct ev_c as [v_call| |]; [|by simpl in His_call..].
              (* (τ1, Call v_call) ∈ drop n ts *)
              destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (vc & vc' & Hprefix_τ1).
              rewrite -(take_drop n ts) filter_app in Hprefix_τ1.
              assert (Hin1_f : (τ1, Ret v1) ∈ filter (λ x, x.1 = τ1) (take n ts)).
              { apply list_elem_of_filter_2; [done|exact Hin1]. }
              assert (Hin_c_f : (τ1, Call v_call) ∈ filter (λ x, x.1 = τ1) (drop n ts)).
              { apply list_elem_of_filter_2; [done|exact Hin_c]. }
              destruct (filter (λ x, x.1 = τ1) (take n ts)) as [|hd tl] eqn:Hfilt_take.
              { clear -Hin1_f. set_solver. }
              apply prefix_cons_inv_1 in Hprefix_τ1 as Hhd_eq.
              subst hd.
              apply prefix_cons_inv_2 in Hprefix_τ1.
              apply prefix_length in Hprefix_τ1.
              rewrite length_app length_cons length_nil in Hprefix_τ1.
              assert (1 ≤ length (filter (λ x, x.1 = τ1) (drop n ts))).
              { enough (filter (λ x, x.1 = τ1) (drop n ts) ≠ []) as Hne.
                { destruct (filter (λ x, x.1 = τ1) (drop n ts)); [congruence|simpl; lia]. }
                intros Hemp. rewrite Hemp in Hin_c_f. clear -Hin_c_f. set_solver. }
              assert (tl = []) by (apply nil_length_inv; lia). subst tl.
              rewrite elem_of_cons elem_of_nil in Hin1_f.
              destruct Hin1_f as [Habs2|[]]. discriminate. }
            symmetry. exact (state_of_trace_call_pop_overlap n τ1 τ2 Hin_m Hτ1_no_ret Hlookup).
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            rewrite /ts'_head_lin filter_app in Hτ₀_not_lin.
            rewrite filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_nil right_id in Hτ₀_not_lin.
            assert (Hτ₀_ne_τ2 : τ₀ ≠ τ2).
            { intro Heq_τ₀_τ2. subst τ₀.
              rewrite /pop_emp_of_trace in Hτ₀_pop_emp.
              apply list_elem_of_fmap_1 in Hτ₀_pop_emp as ([τ₀' ev₀] & Heq₀ & Hin_emp).
              simpl in Heq₀. subst τ₀'.
              apply list_elem_of_filter in Hin_emp as [Heq_ev Hin_ts].
              rewrite /is_ret_pop_emp /= in Heq_ev. subst ev₀.
              apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hin_ts; last done.
              pose proof (elem_of_prefix _ _ _ Hin_ts Hprefix) as Hin'.
              rewrite !elem_of_cons elem_of_nil right_id in Hin'.
              destruct Hin' as [Hin'|Hin']; apply (f_equal snd) in Hin'; simpl in Hin'; discriminate. }
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ2 (encode_request Pop)
                                   (drop (Datatypes.S n) ts)).
              clear -Hsubset Hτ₀_pending Hτ₀_ne_τ2.
              set_solver. }
            destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin) Hτ₀_pop_emp)
              as (icall & Hicall_lookup & Hicall_covers).
            exists icall. split; first assumption.
            intros i Hi.
            destruct (decide (i = n)) as [-> | Hne_i].
            ++ assert (Hn_gt_icall : icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. injection Hicall_lookup as ->.
                exfalso. exact (Hτ₀_ne_τ2 eq_refl). }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              exists τ1c, τ2c. split; [exact Hinm|].
              rewrite /push_pop_covers in Hcover |- *.
              destruct (ret_of_tag ts τ1c) as [[iret_c [? tret]]|] eqn:Hiret; [|done].
              destruct (call_of_tag ts τ2c) as [[icall_c [? tcall]]|] eqn:Hicall; [|done].
              simpl in Hcover |- *.
              split; first lia.
              cut (icall_c ≠ n); first lia.
              intros ->.
              rewrite /call_of_tag list_find_Some /= in Hicall.
              destruct Hicall as (Hlookup_call & [-> _] & _).
              rewrite Hlookup in Hlookup_call. injection Hlookup_call as <- <-.
              assert (τ1c = τ1) as -> by (by eapply valid_match_inj_call).
              (* τ1's Ret at iret_c < n-1. But τ1 not started (Call ≥ n). Ret-duplication. *)
              rewrite /ret_of_tag list_find_Some /= in Hiret.
              destruct Hiret as (Hlookup_ret & [-> His_ret] & _).
              destruct tret as [| |vr]; [exact His_ret..|].
              (* Ret vr at iret_c ≤ n-1. τ1's Call is in drop n ts (not started).
                 Contradiction: Ret in take, Call in drop violates per_tag_wellformed prefix. *)
              rewrite -(lookup_take_lt _ n) in Hlookup_ret; last lia.
              assert (Hin_ret_f : (τ1, Ret vr) ∈ filter (λ x, x.1 = τ1) (take n ts)).
              { apply list_elem_of_filter_2; [done|exact (list_elem_of_lookup_2 _ _ _ Hlookup_ret)]. }
              apply list_elem_of_fmap_1 in Hτ1_not_started as ([τ1'' ev_c] & Heq_c & Hin_c).
              simpl in Heq_c. subst τ1''.
              apply list_elem_of_filter in Hin_c as [His_call_c Hin_c].
              destruct ev_c as [v_call| |]; [|by simpl in His_call_c..].
              assert (Hin_call_f : (τ1, Call v_call) ∈ filter (λ x, x.1 = τ1) (drop n ts)).
              { apply list_elem_of_filter_2; [done|exact Hin_c]. }
              destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (vc & vc' & Hprefix_τ1).
              rewrite -(take_drop n ts) filter_app in Hprefix_τ1.
              destruct (filter (λ x, x.1 = τ1) (take n ts)) as [|hd tl] eqn:Hfilt_take.
              { clear -Hin_ret_f. set_solver. }
              apply prefix_cons_inv_1 in Hprefix_τ1 as Hhd_eq. subst hd.
              apply prefix_cons_inv_2 in Hprefix_τ1.
              apply prefix_length in Hprefix_τ1.
              rewrite length_app length_cons length_nil in Hprefix_τ1.
              assert (1 ≤ length (filter (λ x, x.1 = τ1) (drop n ts))).
              { enough (filter (λ x, x.1 = τ1) (drop n ts) ≠ []) as Hne.
                { destruct (filter (λ x, x.1 = τ1) (drop n ts)); [congruence|simpl; lia]. }
                intros Hemp. rewrite Hemp in Hin_call_f. clear -Hin_call_f. set_solver. }
              assert (tl = []) by (apply nil_length_inv; lia). subst tl.
              rewrite elem_of_cons elem_of_nil in Hin_ret_f.
              destruct Hin_ret_f as [Habs2|[]]. discriminate.
            ++ apply Hicall_covers. lia.
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            rewrite /ts'_head_lin filter_app in Hτ₀_lin.
            rewrite filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil right_id in Hτ₀_lin.
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ2 (encode_request Pop)
                                   (drop (Datatypes.S n) ts)).
              assert (Hne_τ₀ : τ₀ ≠ τ2).
              { intros <-.
                exact (call_at_n_not_linearized n τ₀ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin Hτ₀_lin). }
              clear -Hsubset Hτ₀_pending Hne_τ₀. set_solver. }
            destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin) Hτ₀_push)
              as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
            exists τ2_0. split; first assumption.
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            exact Hτ2_0_lin.
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ1₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ2₀_called.
            simpl in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            apply elem_of_app in Hτ1₀_called as [Hτ1₀_old | Hτ1₀_new];
            apply elem_of_app in Hτ2₀_called as [Hτ2₀_old | Hτ2₀_new].
            ++ exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_old Hτ2₀_old).
            ++ (* τ2₀ = τ2: need τ1₀ ∈ call_tags(take n). (τ1₀, τ2) ∈ m → τ1₀ = τ1.
                 τ1 not started: τ1 ∉ call_tags(take n). Contradiction. *)
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [->|[]].
               assert (Heq_τ1₀ : τ1₀ = τ1) by (by eapply valid_match_inj_call).
               subst τ1₀.
               exfalso.
               (* τ1 ∈ call_tags(take n) AND τ1 ∈ call_tags(drop n). Two Calls → contradiction. *)
               apply list_elem_of_fmap_1 in Hτ1₀_old as ([τ1' ev_take] & Heq_τ1' & Hin_take).
               simpl in Heq_τ1'. subst τ1'.
               apply list_elem_of_filter in Hin_take as [Hcall_take Hin_take].
               apply list_elem_of_fmap_1 in Hτ1_not_started as ([τ1'' ev_drop] & Heq_τ1'' & Hin_drop).
               simpl in Heq_τ1''. subst τ1''.
               apply list_elem_of_filter in Hin_drop as [Hcall_drop Hin_drop].
               destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (vc_u & vc_u' & Hpfx_u).
               apply (prefix_filter (is_call∘snd)) in Hpfx_u.
               rewrite filter_cons_True in Hpfx_u; last done.
               rewrite filter_cons_False in Hpfx_u; last by simpl; auto.
               rewrite filter_nil in Hpfx_u.
               rewrite -(take_drop n ts) !filter_app in Hpfx_u.
               apply prefix_length in Hpfx_u. rewrite !length_app length_cons length_nil in Hpfx_u.
               assert (Hct : (τ1, ev_take) ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ1) (take n ts))).
               { apply list_elem_of_filter_2; [exact Hcall_take|].
                 apply list_elem_of_filter_2; [done|exact Hin_take]. }
               assert (Hcd : (τ1, ev_drop) ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ1) (drop n ts))).
               { apply list_elem_of_filter_2; [exact Hcall_drop|].
                 apply list_elem_of_filter_2; [done|exact Hin_drop]. }
               enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ1) (take n ts)))).
               { enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ1) (drop n ts))));
                 [lia|]; destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ1) (drop n ts)));
                 [clear -Hcd; set_solver|simpl; lia]. }
               destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ1) (take n ts)));
                 [clear -Hct; set_solver|simpl; lia].
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               exfalso. exact (push_xor_pop_of_trace ts _ _ _ Hwf
                 (matched_push_in_push_of_trace _ _ Hin_m₀)
                 (in_pop_of_trace_from_call_pop _ Hin)).
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [<-|[]].
               exfalso. refine (valid_match_ne _ _ _ _ _ Hvalid Hin_m₀ eq_refl).
               apply per_tag_complete_per_tag_wellformed, Hcomplete.
          --(* Hpop_lin_consistent *)
            apply (pop_lin_consistent_extend_call _ _ _ _ Hpop_lin_consistent).
          (**************** End LLM-generated code. *****************)
        * (* If the matched Push has finished and the new state is empty,
          linearize the pop and all pending pop(empty)'s *)
          pose (pending_pop_emptys := filter (λ τ,
            τ ∈ trace_pendingOp (drop n ts) ∧ τ ∉ (filter (is_lin ∘ snd) ts'_head).*1)
            (pop_emp_of_trace ts)).
          exists (ts'_head ++ [(τ2,Call (encode_request Pop));
            (τ2,Lin (encode_request Pop) (encode_response (NonEmpty v_pop)))]
            ++ ((λ τ, (τ, Lin (encode_request Pop) (encode_response IsEmpty))) <$> pending_pop_emptys)).
          exists ∅.
          (*************** Begin LLM-generated code. ****************)
          (* Derive shared facts before split_and! using extracted helpers *)
          assert (Hτ1_ret : τ1 ∈ (filter (is_ret∘snd) (take n ts)).*1)
            by (eapply matched_finished_push_ret_in_take; eauto).
          destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcp].
          assert (Hvp_eq : vp = v_pop)
            by (eapply matched_push_value_eq_pop_value; eauto).
          subst vp.
          assert (Hvpop_in_s : v_pop ∈ s).
          { rewrite Hstate_of_trace.
            eapply matched_push_value_in_state_of_trace; eauto. }
          (* pending_pop_emptys are pop tags with IsEmpty prefix *)
          assert (Hppe_pop : ∀ τ₀, τ₀ ∈ pending_pop_emptys → τ₀ ∈ pop_of_trace ts).
          { intros τ₀ Hin_ppe. rewrite /pending_pop_emptys in Hin_ppe.
            apply list_elem_of_filter in Hin_ppe as [_ Hin_ppe].
            rewrite /pop_emp_of_trace in Hin_ppe.
            apply list_elem_of_fmap_1 in Hin_ppe as ([τ₀' ev₀] & Heq₀ & Hin₀).
            simpl in Heq₀. subst τ₀'.
            apply list_elem_of_filter in Hin₀ as [His_emp Hin₀].
            (* ev₀ = Ret IsEmpty. From per_tag_wellformed_bag: τ₀ is a pop. *)
            apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin₀; last done.
            destruct (Hwf τ₀) as [(vp₀ & _ & Hpfx₀)|(vp₀ & _ & Hpfx₀)].
            - (* push prefix — contradicts Ret IsEmpty event *)
              exfalso.
              rewrite /is_ret_pop_emp in His_emp. subst.
              pose proof (elem_of_prefix _ _ _ Hin₀ Hpfx₀) as Hin_pfx₀.
              rewrite !elem_of_cons !elem_of_nil right_id in Hin_pfx₀.
              destruct Hin_pfx₀ as [Hin_pfx₀|Hin_pfx₀]; simplify_eq.
            - (* pop prefix — get Call Pop from filter(tag=τ₀)(ts) via prefix *)
              apply (list_elem_of_fmap_2 fst _ (τ₀, Call (encode_request Pop))).
              apply list_elem_of_filter_2; [done|].
              apply (list_elem_of_filter_1 (λ x, x.1 = τ₀)).
              pose proof (elem_of_prefix _ _ _ Hin₀ Hpfx₀) as Hret_in_pfx.
              rewrite !elem_of_cons !elem_of_nil right_id in Hret_in_pfx.
              destruct Hret_in_pfx as [Habs|_]; first by simplify_eq.
              (* filter ≥ 2 elements: contains both Call and Ret *)
              destruct (filter (λ x, x.1 = τ₀) ts) as [|hd0 [|hd1 rest0]] eqn:Hfilt_eq0.
              + clear -Hin₀ Hfilt_eq0. set_solver.
              + exfalso. rewrite elem_of_cons elem_of_nil in Hin₀.
                pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx₀) as ->.
                destruct Hin₀ as [Habs|[]]. by simplify_eq.
              + pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx₀) as ->. clear. set_solver. }
          assert (Hppe_not_m2 : ∀ τ₀, τ₀ ∈ pending_pop_emptys → τ₀ ∉ m.*2).
          { intros τ₀ Hin_ppe. rewrite /pending_pop_emptys in Hin_ppe.
            apply list_elem_of_filter in Hin_ppe as [_ Hin_ppe].
            rewrite /pop_emp_of_trace in Hin_ppe.
            apply list_elem_of_fmap_1 in Hin_ppe as ([τ₀' ev₀] & Heq₀ & Hin₀).
            simpl in Heq₀. subst τ₀'.
            apply list_elem_of_filter in Hin₀ as [His_emp Hin₀].
            simpl in His_emp. rewrite /is_ret_pop_emp in His_emp. subst.
            apply (list_elem_of_filter_2 (λ x, x.1 = τ₀)) in Hin₀; last done.
            destruct (Hwf τ₀) as [(vp₀ & _ & Hpfx₀)|(vp₀ & _ & Hpfx₀)].
            - exfalso.
              pose proof (elem_of_prefix _ _ _ Hin₀ Hpfx₀) as Hin_pfx₀.
              rewrite !elem_of_cons !elem_of_nil right_id in Hin_pfx₀.
              destruct Hin_pfx₀ as [Hin_pfx₀|Hin_pfx₀]; by simplify_eq.
            - assert (Hvp₀ : vp₀ = IsEmpty).
              { pose proof (elem_of_prefix _ _ _ Hin₀ Hpfx₀) as Hin_pfx₀.
                rewrite !elem_of_cons !elem_of_nil right_id in Hin_pfx₀.
                destruct Hin_pfx₀ as [Hin_pfx₀|Hin_pfx₀]; first by simplify_eq.
                revert Hin_pfx₀. intros [= Habs].
                change (encode_response IsEmpty = encode_response vp₀) in Habs.
                by apply (inj encode_response) in Habs. }
              subst vp₀.
              eapply pop_empty_not_in_m; [exact Hcomplete|exact Hvalid|exact Hwf| |exact Hpfx₀].
              apply (list_elem_of_filter_1 (λ x, x.1 = τ₀)).
              (* (τ₀, Call Pop) ∈ filter(tag=τ₀)(ts): filter has ≥ 1 element from Hin₀,
                 and prefix starts with Call Pop *)
              destruct (filter (λ x, x.1 = τ₀) ts) as [|hd0 rest0].
              { clear -Hin₀. set_solver. }
              pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx₀) as ->. clear. set_solver. }
          (* Shared: filter(is_lin)(fmap pending) = fmap pending *)
          assert (Hfilt_ppe_id : filter (is_lin ∘ snd)
            ((λ τ, (τ, Lin (encode_request Pop) (encode_response IsEmpty))) <$> pending_pop_emptys)
            = (λ τ, (τ, Lin (encode_request Pop) (encode_response IsEmpty))) <$> pending_pop_emptys).
          { clear. induction pending_pop_emptys as [|h t IH]; first done.
            rewrite !fmap_cons filter_cons_True; [|done]. by f_equal. }
          intros ts'_head_lin. split_and!.
          --(* Hfilter *)
            rewrite filter_app filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil.
            rewrite -Hfilter.
            rewrite filter_False_nil; last first.
            { rewrite Forall_fmap. apply Forall_forall.
              intros x _. simpl. auto. }
            rewrite right_id.
            rewrite (take_S_r _ _ _ Hlookup).
            by f_equal.
          --(* Hper_tag_lin *)
            intro τ₀0.
            destruct (Hper_tag_lin τ₀0) as (v₀0 & v₀0' & Hprefix₀0).
            rewrite filter_app filter_app.
            destruct (decide (τ₀0 = τ2)) as [-> | Hne0].
            { (* τ₀0 = τ2 *)
              exists (encode_request Pop), (encode_response (NonEmpty v_pop)).
              do 2 rewrite filter_cons_True //. rewrite filter_nil.
              rewrite (call_at_n_no_events n τ2 _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin) left_id.
              (* τ2 ∉ pending_pop_emptys *)
              (* filter(tag=τ2)(fmap pending) = [] because τ2 ∉ pending *)
              rewrite filter_False_nil; last first.
              { rewrite Forall_fmap. apply Forall_forall.
                intros τ_p Hin_p. simpl. intros Heq_p. subst τ_p.
                eapply (Hppe_not_m2 _ Hin_p).
                exact (list_elem_of_fmap_2 snd _ _ Hin_m). }
              rewrite right_id.
              eexists. reflexivity. }
            (* τ₀0 ≠ τ2 *)
            rewrite filter_cons_False; [|simpl; congruence].
            rewrite filter_cons_False; [|simpl; congruence].
            rewrite filter_nil.
            destruct (decide (τ₀0 ∈ pending_pop_emptys)) as [Hin_ppe|Hnotin_ppe].
            { (* τ₀0 ∈ pending_pop_emptys: old filter = [(τ₀0, Call Pop)], adds Lin *)
              exists (encode_request Pop), (encode_response IsEmpty).
              (* old filter: τ₀0 is pending in drop n, not linearized. *)
              assert (Hτ₀0_pop := Hppe_pop _ Hin_ppe).
              assert (Hτ₀0_call_in : (τ₀0, Call (encode_request Pop)) ∈ ts'_head).
              { rewrite /pending_pop_emptys in Hin_ppe.
                apply list_elem_of_filter in Hin_ppe as [[Hpending Hnot_lin] Hin_emp].
                rewrite /pop_of_trace in Hτ₀0_pop.
                apply list_elem_of_fmap_1 in Hτ₀0_pop as ([τ₀0' ev₀0] & Heq₀0 & Hin₀0).
                simpl in Heq₀0. subst τ₀0'.
                apply list_elem_of_filter in Hin₀0 as [His_call Hin₀0].
                simpl in His_call. rewrite /is_call_pop in His_call. subst ev₀0.
                (* (τ₀0, Call Pop) ∈ ts. Need it in take n ts. *)
                apply list_elem_of_lookup_1 in Hin₀0 as [j Hj].
                assert (j < n).
                { assert (j < length ts) by (eapply lookup_lt_Some; eauto).
                  assert (j ≠ n).
                  { intros ->. rewrite Hlookup in Hj. simplify_eq. }
                  destruct (decide (j < n)); [lia|exfalso].
                  assert (j > n) by lia.
                  (* j > n: Call Pop at j in drop n ts. *)
                  pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq in Hpending.
                  apply filter_tag_trace_pendingOp in Hpending.
                  rewrite filter_cons_False in Hpending; last by (simpl; congruence).
                  rewrite -filter_tag_trace_pendingOp in Hpending.
                  (* τ₀0 pending in drop (S n) ts. But Call at j > n (hence j ≥ S n). *)
                  assert (Hj_drop : drop (Datatypes.S n) ts !! (j - Datatypes.S n) = Some (τ₀0, Call (encode_request Pop))).
                  { rewrite lookup_drop. replace (Datatypes.S n + (j - Datatypes.S n)) with j by lia. exact Hj. }
                  destruct (list_elem_of_split_length _ _ _ Hj_drop) as (l1_d & l2_d & Hdrop_split & Hl1_len).
                  rewrite Hdrop_split in Hpending.
                  eapply trace_pendingOp_call_middle_elem_of; [|exact Hpending].
                  eapply per_tag_partial_wellformed_suffix; first by (rewrite -Hdrop_split; apply suffix_drop).
                  apply per_tag_wellformed_per_tag_partial_wellformed.
                  apply per_tag_complete_per_tag_wellformed. done. }
                assert (Hin_take : (τ₀0, Call (encode_request Pop)) ∈ take n ts).
                { eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hj|lia]. }
                rewrite Hfilter in Hin_take.
                apply list_elem_of_filter in Hin_take as [_ ?]. done. }
              assert (Hτ₀0_not_lin : τ₀0 ∉ (filter (is_lin ∘ snd) ts'_head).*1).
              { rewrite /pending_pop_emptys in Hin_ppe.
                apply list_elem_of_filter in Hin_ppe as [[_ Hnot_lin] _]. exact Hnot_lin. }
              (* filter(tag=τ₀0)(ts'_head) = [(τ₀0, Call Pop)] *)
              assert (Hfilt_eq : filter (λ x, x.1 = τ₀0) ts'_head = [(τ₀0, Call (encode_request Pop))]).
              { apply (list_elem_of_filter_2 (λ x, x.1 = τ₀0)) in Hτ₀0_call_in as Hτ₀0_in_filt; last done.
                destruct (filter (λ x, x.1 = τ₀0) ts'_head) as [|hd [|hd2 rest2]] eqn:Hf.
                - exfalso. clear -Hτ₀0_in_filt. set_solver.
                - f_equal. apply prefix_cons_inv_1 in Hprefix₀0.
                  rewrite Hprefix₀0.
                  assert (Hcv : (τ₀0, Call v₀0) ∈ ts'_head).
                  { apply (list_elem_of_filter_1 (λ x, x.1 = τ₀0)). rewrite Hf. rewrite Hprefix₀0. clear. set_solver. }
                  assert (Hcv_in_ts : (τ₀0, Call v₀0) ∈ ts).
                  { assert (Hin_take : (τ₀0, Call v₀0) ∈ take n ts).
                    { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; by auto|exact Hcv]. }
                    eapply elem_of_prefix; last apply prefix_take. exact Hin_take. }
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ₀0)) in Hcv_in_ts; last done.
                  destruct (Hwf τ₀0) as [(vp₀ & _ & Hpfx₀)|(vp₀ & _ & Hpfx₀)].
                  + exfalso.
                    (* (τ₀0, Call v₀0) ∈ push prefix for τ₀0 → v₀0 = Push vp₀.
                       But τ₀0 has Call Pop → Call Pop ∈ push prefix → discriminate. *)
                    assert (Hcall_pop_in_ts : (τ₀0, Call (encode_request Pop)) ∈ filter (λ x, x.1 = τ₀0) ts).
                    { apply list_elem_of_filter_2; [done|].
                      assert (Hin_take : (τ₀0, Call (encode_request Pop)) ∈ take n ts).
                      { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; by auto|exact Hτ₀0_call_in]. }
                      eapply elem_of_prefix; last apply prefix_take. exact Hin_take. }
                    pose proof (elem_of_prefix _ _ _ Hcall_pop_in_ts Hpfx₀) as Hin_pfx₀'.
                    rewrite !elem_of_cons !elem_of_nil right_id in Hin_pfx₀'.
                    destruct Hin_pfx₀' as [Hin_pfx₀'|Hin_pfx₀']; apply (f_equal snd) in Hin_pfx₀';
                      simpl in Hin_pfx₀'; discriminate.
                  + pose proof (elem_of_prefix _ _ _ Hcv_in_ts Hpfx₀) as Hin_pfx₀.
                    rewrite !elem_of_cons !elem_of_nil right_id in Hin_pfx₀.
                    destruct Hin_pfx₀ as [Hin_pfx₀|Hin_pfx₀]; last by
                      (apply (f_equal snd) in Hin_pfx₀; simpl in Hin_pfx₀; discriminate).
                    by simplify_eq.
                - (* ≥ 2 elements: second must be Lin → contradicts Hτ₀0_not_lin *)
                  exfalso. apply Hτ₀0_not_lin.
                  apply prefix_cons_inv_2 in Hprefix₀0.
                  pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀0) as ->.
                  apply (list_elem_of_fmap_2 fst _ (τ₀0, Lin v₀0 v₀0')).
                  apply list_elem_of_filter_2; [done|].
                  apply (list_elem_of_filter_1 (λ x, x.1 = τ₀0)). rewrite Hf. clear. set_solver. }
              rewrite Hfilt_eq.
              (* fmap filter for τ₀0 in pending *)
              assert (Hfilt_fmap_ppe :
                filter (λ x, x.1 = τ₀0)
                  ((λ τ, (τ, Lin (encode_request Pop) (encode_response IsEmpty))) <$> pending_pop_emptys)
                  = [(τ₀0, Lin (encode_request Pop) (encode_response IsEmpty))]).
              { (* τ₀0 appears exactly once in pending_pop_emptys *)
                assert (Hppe_once : filter (λ τ, τ = τ₀0) pending_pop_emptys = [τ₀0]).
                { (* NoDup pending_pop_emptys from per_tag_wellformed *)
                  assert (Hnodup_pop_emp : NoDup (pop_emp_of_trace ts)).
                  { rewrite /pop_emp_of_trace. apply NoDup_fmap_fst.
                    - intros τ_a ev_a ev_b Hin_a Hin_b.
                      apply list_elem_of_filter in Hin_a as [Ha_emp Hin_a].
                      apply list_elem_of_filter in Hin_b as [Hb_emp Hin_b].
                      destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ_a) as (vc_a & vc_a' & Hpfx_a).
                      apply (list_elem_of_filter_2 (λ x, x.1 = τ_a)) in Hin_a; last done.
                      apply (list_elem_of_filter_2 (λ x, x.1 = τ_a)) in Hin_b; last done.
                      pose proof (elem_of_prefix _ _ _ Hin_a Hpfx_a) as Hin_pfx_a.
                      pose proof (elem_of_prefix _ _ _ Hin_b Hpfx_a) as Hin_pfx_b.
                      rewrite !elem_of_cons !elem_of_nil !right_id in Hin_pfx_a, Hin_pfx_b.
                      destruct Hin_pfx_a as [Hin_pfx_a|Hin_pfx_a]; destruct Hin_pfx_b as [Hin_pfx_b|Hin_pfx_b];
                        simplify_eq. done.
                    - apply NoDup_filter. exact (per_tag_complete_NoDup _ Hcomplete). }
                  assert (Hnodup_ppe : NoDup pending_pop_emptys).
                  { subst pending_pop_emptys. apply NoDup_filter. exact Hnodup_pop_emp. }
                  (* From NoDup + membership: filter(= τ₀0) = [τ₀0] *)
                  clear -Hnodup_ppe Hin_ppe.
                  induction pending_pop_emptys as [|h tl IH].
                  - exfalso. clear -Hin_ppe. set_solver.
                  - apply NoDup_cons in Hnodup_ppe as [Hnotin_tl Hnodup_tl].
                    destruct (decide (h = τ₀0)) as [->|Hne].
                    + rewrite filter_cons_True; last done. f_equal.
                      apply filter_False_nil. apply Forall_forall.
                      intros τ_q Hin_q Heq_q. subst τ_q. exact (Hnotin_tl Hin_q).
                    + rewrite filter_cons_False; last done.
                      apply IH; last done.
                      rewrite elem_of_cons in Hin_ppe. destruct Hin_ppe as [->|]; [congruence|done]. }
                (* Convert filter on fmap to fmap of filter *)
                clear -Hin_ppe Hppe_once.
                induction pending_pop_emptys as [|h tl IH].
                - exfalso. clear -Hin_ppe. set_solver.
                - rewrite fmap_cons.
                  destruct (decide (h = τ₀0)) as [->|Hne].
                  + rewrite filter_cons_True; [|done]. f_equal.
                    rewrite filter_cons_True in Hppe_once; last done.
                    injection Hppe_once as Hppe_once.
                    rewrite filter_False_nil; [done|]. rewrite Forall_fmap. apply Forall_forall.
                    intros τ_q Hin_q. simpl. intros Heq_q. subst τ_q.
                    assert (Htmp : τ₀0 ∈ filter (λ τ : positive, τ = τ₀0) tl).
                    { apply list_elem_of_filter_2; [done|exact Hin_q]. }
                    rewrite Hppe_once in Htmp. clear -Htmp. set_solver.
                  + rewrite filter_cons_False; [|simpl; congruence].
                    rewrite filter_cons_False in Hppe_once; last done.
                    apply IH; last exact Hppe_once.
                    rewrite elem_of_cons in Hin_ppe. destruct Hin_ppe as [->|]; [congruence|done]. }
              rewrite Hfilt_fmap_ppe /=.
              eexists. reflexivity. }
            (* τ₀0 ∉ pending_pop_emptys: no new events *)
            exists v₀0, v₀0'.
            assert (Hfilt_fmap_none : filter (λ x, x.1 = τ₀0)
              ((λ τ, (τ, Lin (encode_request Pop) (encode_response IsEmpty))) <$> pending_pop_emptys) = []).
            { rewrite filter_False_nil; [done|]. rewrite Forall_fmap. apply Forall_forall.
              intros τ_p Hin_p. simpl. intros <-. exact (Hnotin_ppe Hin_p). }
            rewrite Hfilt_fmap_none right_id. assumption.
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            eapply linearized_sound_app; first eassumption.
            eapply (linearized_sound_cons _ ∅); first by (right; reflexivity).
            { eexists. split; first reflexivity.
              right. eexists v_pop.
              split_and!; [exact Hvpop_in_s|rewrite Hemp_after_pop; done|done]. }
            (* Now linearize all pending pop(∅)s from state ∅ *)
            assert (Hfilt_id : filter (is_lin ∘ snd)
              ((λ τ, (τ, Lin (encode_request Pop) (encode_response IsEmpty))) <$> pending_pop_emptys)
              = (λ τ, (τ, Lin (encode_request Pop) (encode_response IsEmpty))) <$> pending_pop_emptys).
            { clear. induction pending_pop_emptys as [|h t IH]; first done.
              rewrite !fmap_cons filter_cons_True; [|done]. by f_equal. }
            rewrite Hfilt_id.
            assert (Hppe_const : ∀ τ_pe, τ_pe ∈ pending_pop_emptys → if rme then True else False).
            { intros τ_pe Hin_pe.
              rewrite /pending_pop_emptys in Hin_pe.
              apply list_elem_of_filter in Hin_pe as [_ Hin_pe].
              rewrite /pop_emp_of_trace in Hin_pe.
              apply list_elem_of_fmap_1 in Hin_pe as ([τ_pe' ev_pe] & Heq_pe & Hin_pe').
              simpl in Heq_pe. subst τ_pe'.
              apply list_elem_of_filter in Hin_pe' as [His_emp Hin_ts'].
              rewrite /is_ret_pop_emp /= in His_emp. subst ev_pe.
              destruct rme; first done.
              apply (list_elem_of_filter_2 (λ x, x.1 = τ_pe)) in Hin_ts'; last done.
              destruct (Hwf τ_pe) as [(? & _ & Hpfx)|(r_pe & Hr_ne_pe & Hpfx)].
              - pose proof (elem_of_prefix _ _ _ Hin_ts' Hpfx) as Hin_pfx.
                rewrite !elem_of_cons elem_of_nil right_id in Hin_pfx.
                destruct Hin_pfx as [Hin_pfx|Hin_pfx]; apply (f_equal snd) in Hin_pfx; simpl in Hin_pfx; discriminate.
              - pose proof (elem_of_prefix _ _ _ Hin_ts' Hpfx) as Hin_pfx.
                rewrite !elem_of_cons elem_of_nil right_id in Hin_pfx.
                destruct Hin_pfx as [Hin_pfx|Hin_pfx]; apply (f_equal snd) in Hin_pfx; simpl in Hin_pfx;
                  [discriminate|]. injection Hin_pfx as Hr_eq.
                assert (r_pe = IsEmpty) as ->.
                { destruct r_pe; simpl in Hr_eq; [done|discriminate]. }
                by apply Hr_ne_pe. }
            revert Hppe_const.
            generalize pending_pop_emptys.
            clear -rme. intros l Hl.
            induction l as [|τ_pe_hd rest IH].
            { rewrite fmap_nil. apply linearized_sound_nil. }
            rewrite fmap_cons.
            eapply linearized_sound_cons.
            ++ right. reflexivity.
            ++ eexists. split; first reflexivity.
               left. destruct rme; first done.
               exfalso.
               assert (Hin_τ_pe_hd : τ_pe_hd ∈ τ_pe_hd :: rest)
                 by (apply elem_of_cons; left; reflexivity).
               pose proof (Hl τ_pe_hd Hin_τ_pe_hd) as Hfalse. done.
            ++ apply IH. intros τ Hτ. apply (Hl τ). apply elem_of_cons. right. exact Hτ.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            rewrite /ts'_head_lin filter_app filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_cons_True in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil Hfilt_ppe_id !fmap_app /= in Hτ2_bounded₀ |- *.
            rewrite -list_fmap_compose /= list_fmap_id in Hτ2_bounded₀ |- *.
            (* τ2₀ ∈ old_lin ++ [τ2] ++ pending. Three cases. *)
            assert (Hτ2₀_cases : τ2₀ ∈ (filter (is_lin ∘ snd) ts'_head).*1 ∨ τ2₀ = τ2 ∨ τ2₀ ∈ pending_pop_emptys).
            { clear -Hτ2_bounded₀. set_solver. }
            destruct Hτ2₀_cases as [Hτ2_old | [-> | Hτ2_ppe]].
            ++ (* τ2₀ in old lin tags *)
               apply sublist_inserts_r.
               eapply Hval_then_not_pr; eassumption.
            ++ (* τ2₀ = τ2: need [τ1₀;τ2] sublist. τ1₀ = τ1 by NoDup m.*2. *)
               assert (Heq_τ1: τ1₀ = τ1) by (by eapply valid_match_inj_call). subst τ1₀.
               (* τ1 must be linearized in old ts'_head (same argument as "not empty" case) *)
               assert (Hτ1_lin : τ1 ∈ (filter (is_lin ∘ snd) ts'_head).*1).
               { destruct (Hper_tag_lin τ1) as (v₁_a & v₁_b & Hprefix₁_a).
                 assert (Hcall_in_take : ∃ vc, (τ1, Call vc) ∈ take n ts).
                 { destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp' Hcp'].
                   apply list_elem_of_lookup_1 in Hcp' as [j_p Hj_p].
                   assert (j_p < n).
                   { assert (j_p < length ts) by (eapply lookup_lt_Some; eauto).
                     assert (j_p ≠ n) by (intros ->; rewrite Hlookup in Hj_p; discriminate).
                     destruct (decide (j_p < n)); [lia|].
                     exfalso. apply Hτ1_finished.
                     apply (list_elem_of_fmap_2 fst _ (τ1, Call (encode_request (Push vp')))).
                     apply list_elem_of_filter_2; [done|].
                     apply (list_elem_of_lookup_2 _ (j_p - n)).
                     rewrite lookup_drop. replace (n + (j_p - n)) with j_p by lia. exact Hj_p. }
                   eexists. eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hj_p|lia]. }
                 assert (Hret_in_take : ∃ vr, (τ1, Ret vr) ∈ take n ts).
                 { apply list_elem_of_fmap_1 in Hτ1_ret as ([τ1' ev1] & Heq1 & Hin1).
                   simpl in Heq1. subst τ1'.
                   apply list_elem_of_filter in Hin1 as [Hret1 Hin1'].
                   destruct ev1 as [|v1' v1''|]; try by destruct Hret1.
                   eexists. exact Hin1'. }
                 destruct Hcall_in_take as [vc Hcall_in].
                 destruct Hret_in_take as [vr Hret_in].
                 assert (Hcall_in_head : (τ1, Call vc) ∈ ts'_head).
                 { rewrite Hfilter in Hcall_in. apply list_elem_of_filter in Hcall_in as [_ ?]. done. }
                 assert (Hret_in_head : (τ1, Ret vr) ∈ ts'_head).
                 { rewrite Hfilter in Hret_in. apply list_elem_of_filter in Hret_in as [_ ?]. done. }
                 apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_in_head; last done.
                 apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hret_in_head; last done.
                 assert (Hlen_filt : 2 ≤ length (filter (λ x, x.1 = τ1) ts'_head)).
                 { destruct (filter (λ x, x.1 = τ1) ts'_head) as [|a1 rest1].
                   - exfalso. clear -Hcall_in_head. set_solver.
                   - destruct rest1 as [|a2 rest2].
                     + exfalso.
                       assert (Htmp : (τ1, Call vc) = (τ1, Ret vr) → False).
                       { intros Habs. apply (f_equal snd) in Habs. simpl in Habs. discriminate. }
                       clear -Hcall_in_head Hret_in_head Htmp. set_solver.
                     + simpl. lia. }
                 destruct (filter (λ x, x.1 = τ1) ts'_head) as [|b1 [|b2 rest2']] eqn:Hfilt_eq.
                 - simpl in Hlen_filt. lia.
                 - simpl in Hlen_filt. lia.
                 - simpl in Hprefix₁_a.
                   apply prefix_cons_inv_2 in Hprefix₁_a.
                   pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₁_a) as Heq_lin.
                   apply (list_elem_of_fmap_2 fst _ (τ1, Lin v₁_a v₁_b)).
                   apply list_elem_of_filter_2; [done|].
                   apply (list_elem_of_filter_1 (λ x, x.1 = τ1)).
                   rewrite Hfilt_eq Heq_lin. clear. set_solver. }
               destruct (list_elem_of_split _ _ Hτ1_lin) as (la & la' & Hlin_eq).
               apply sublist_cons_l.
               exists la, (la' ++ [τ2] ++ pending_pop_emptys).
               split.
               ** rewrite Hlin_eq -assoc /=. reflexivity.
               ** apply sublist_inserts_l. constructor. apply sublist_nil_l.
            ++ (* τ2₀ ∈ pending_pop_emptys: τ2₀ is pop(∅), not in m.*2 *)
               exfalso. apply (Hppe_not_m2 _ Hτ2_ppe).
               exact (list_elem_of_fmap_2 snd _ _ Hin_m₀).
          --(* Hstate_of_trace *)
            symmetry.
            rewrite (state_of_trace_call_pop_nonoverlap n τ1 τ2 v_pop Hin_m Hcp Hτ1_ret Hlookup).
            rewrite -Hstate_of_trace. exact Hemp_after_pop.
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            exfalso. apply Hτ₀_not_lin.
            (* τ₀ is pending, pop(∅). So τ₀ ∈ pending_pop_emptys (or already linearized). *)
            (* First show τ₀ ∈ pending_pop_emptys *)
            assert (Hτ₀_ne_τ2 : τ₀ ≠ τ2).
            { intros <-. apply Hτ₀_not_lin.
              rewrite /ts'_head_lin filter_app filter_app.
              rewrite filter_cons_False; last by simpl; auto.
              rewrite filter_cons_True; last by simpl; auto.
              rewrite filter_nil Hfilt_ppe_id !fmap_app /=.
              clear. set_solver. }
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ2 (encode_request Pop)
                                   (drop (Datatypes.S n) ts)).
              clear -Hsubset Hτ₀_pending Hτ₀_ne_τ2. set_solver. }
            assert (Hτ₀_not_lin_old : τ₀ ∉ (filter (is_lin ∘ snd) ts'_head).*1).
            { rewrite /ts'_head_lin filter_app filter_app in Hτ₀_not_lin.
              rewrite filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
              rewrite filter_cons_True in Hτ₀_not_lin; last by simpl; auto.
              rewrite filter_nil Hfilt_ppe_id !fmap_app /= in Hτ₀_not_lin.
              rewrite -list_fmap_compose /= list_fmap_id in Hτ₀_not_lin.
              clear -Hτ₀_not_lin. set_solver. }
            (* τ₀ ∈ pending_pop_emptys by definition *)
            assert (Hτ₀_ppe : τ₀ ∈ pending_pop_emptys).
            { rewrite /pending_pop_emptys.
              apply list_elem_of_filter_2; [split; [exact Hτ₀_pending_old|exact Hτ₀_not_lin_old]|exact Hτ₀_pop_emp]. }
            (* Now τ₀ is linearized via the fmap *)
            rewrite /ts'_head_lin filter_app filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil Hfilt_ppe_id !fmap_app /=.
            rewrite -list_fmap_compose /= list_fmap_id.
            clear -Hτ₀_ppe. set_solver.
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            rewrite /ts'_head_lin filter_app filter_app in Hτ₀_lin.
            rewrite filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil Hfilt_ppe_id !fmap_app /= in Hτ₀_lin.
            rewrite -list_fmap_compose /= list_fmap_id in Hτ₀_lin.
            assert (Hτ₀_lin_old : τ₀ ∈ (filter (is_lin ∘ snd) ts'_head).*1).
            { (* τ₀ is a push, so it's not τ2 (pop) and not in pending_pop_emptys (pop-empty).
                 Hence τ₀ must be in old lin tags. *)
              assert (Hτ₀_ne_τ2 : τ₀ ≠ τ2).
              { intros ->. eapply push_xor_pop_of_trace; [exact Hwf|exact Hτ₀_push|].
                apply (list_elem_of_fmap_2 fst _ (τ2, Call (encode_request Pop))).
                apply list_elem_of_filter_2; [done|exact Hin]. }
              assert (Hτ₀_notin_ppe : τ₀ ∉ pending_pop_emptys).
              { intros Hin_ppe.
                eapply push_xor_pop_of_trace; [exact Hwf|exact Hτ₀_push|exact (Hppe_pop _ Hin_ppe)]. }
              clear -Hτ₀_lin Hτ₀_ne_τ2 Hτ₀_notin_ppe. set_solver. }
            ++ assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
                { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
                  assert (Hsubset := trace_pendingOp_call τ2 (encode_request Pop)
                                       (drop (Datatypes.S n) ts)).
                  assert (Hne_τ₀ : τ₀ ≠ τ2).
                  { intros <-.
                    exact (call_at_n_not_linearized n τ₀ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin Hτ₀_lin_old). }
                  clear -Hsubset Hτ₀_pending Hne_τ₀. set_solver. }
                destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin_old) Hτ₀_push)
                  as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
                exists τ2_0. split; first assumption.
                rewrite /ts'_head_lin filter_app filter_app.
                rewrite filter_cons_False; last by simpl; auto.
                rewrite filter_cons_True; last by simpl; auto.
                rewrite filter_nil Hfilt_ppe_id !fmap_app /=. clear -Hτ2_0_lin. set_solver.
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ1₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ2₀_called.
            simpl in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app filter_app
              filter_cons_False; [|by simpl; auto].
            rewrite filter_cons_True; [|by simpl; auto].
            rewrite filter_nil Hfilt_ppe_id !fmap_app /=
              -list_fmap_compose /= list_fmap_id.
            apply elem_of_app in Hτ1₀_called as [Hτ1₀_old | Hτ1₀_new];
            apply elem_of_app in Hτ2₀_called as [Hτ2₀_old | Hτ2₀_new].
            ++ (* Both old: use IH *)
               clear -Hpop_aeap Hin_m₀ Hτ1₀_old Hτ2₀_old. set_solver.
            ++ rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [->|[]].
               clear -Hτ1_ne_τ2. set_solver.
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               exfalso. exact (push_xor_pop_of_trace ts _ _ _ Hwf
                 (matched_push_in_push_of_trace _ _ Hin_m₀)
                 (in_pop_of_trace_from_call_pop _ Hin)).
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [<-|[]].
               exfalso. refine (valid_match_ne _ _ _ _ _ Hvalid Hin_m₀ eq_refl).
               apply per_tag_complete_per_tag_wellformed, Hcomplete.
          --(* Hpop_lin_consistent *)
            intros τ₀ v₀_c v₀'_c Hτ₀_pop Hin_lin.
            apply elem_of_app in Hin_lin as [Hlin_old | Hlin_new].
            { exact (Hpop_lin_consistent _ _ _ Hτ₀_pop Hlin_old). }
            apply elem_of_app in Hlin_new as [Hlin_mid | Hlin_ppe].
            { rewrite !elem_of_cons elem_of_nil in Hlin_mid.
              destruct Hlin_mid as [Habs | [Heq_lin | []]].
              - discriminate.
              - injection Heq_lin as -> _ ->.
                rewrite bool_decide_eq_true_2; last by (apply (list_elem_of_fmap_2 snd _ (τ1,τ2)); exact Hin_m).
                exists τ1, v_pop. split_and!; [exact Hin_m|exact Hcp|done]. }
            (* Lin in pending_pop_emptys suffix *)
            apply list_elem_of_fmap_1 in Hlin_ppe as [τ_ppe [Heq_ppe Hin_ppe]].
            injection Heq_ppe as -> _ ->.
            rewrite bool_decide_eq_false_2; [done|exact (Hppe_not_m2 _ Hin_ppe)].
          (**************** End LLM-generated code. *****************)
        * (* If the matched Push has finished and the new state is not empty,
          only linearize the pop *)
          exists (ts'_head ++ [(τ2,Call (encode_request Pop));
            (τ2,Lin (encode_request Pop) (encode_response (NonEmpty v_pop)))]).
          exists (s∖{[+ v_pop +]}).
          (*************** Begin LLM-generated code. ****************)
          (* Derive shared facts before split_and! using extracted helpers *)
          assert (Hτ1_ret : τ1 ∈ (filter (is_ret∘snd) (take n ts)).*1)
            by (eapply matched_finished_push_ret_in_take; eauto).
          destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcp].
          assert (Hvp_eq : vp = v_pop)
            by (eapply matched_push_value_eq_pop_value; eauto).
          subst vp.
          assert (Hvpop_in_s : v_pop ∈ s).
          { rewrite Hstate_of_trace.
            eapply matched_push_value_in_state_of_trace; eauto. }
          intros ts'_head_lin. split_and!.
          --(* Hfilter *)
            rewrite filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil.
            rewrite (take_S_r _ _ _ Hlookup).
            f_equal. done.
          --(* Hper_tag_lin *)
            intro τ₀0.
            destruct (Hper_tag_lin τ₀0) as (v₀0 & v₀0' & Hprefix₀0).
            rewrite filter_app.
            destruct (decide (τ₀0 = τ2)) as [-> | Hne0]; last first.
            { exists v₀0, v₀0'.
              rewrite filter_cons_False; [|simpl; congruence].
              rewrite filter_cons_False; [|simpl; congruence].
              rewrite filter_nil right_id. assumption. }
            exists (encode_request Pop), (encode_response (NonEmpty v_pop)).
            do 2 rewrite filter_cons_True //. rewrite filter_nil.
            rewrite (call_at_n_no_events n τ2 _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin) left_id.
            eexists. reflexivity.
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            eapply linearized_sound_app; first eassumption.
            eapply (linearized_sound_cons _ (s∖{[+ v_pop +]})); first by (right; reflexivity).
            { eexists. split; first reflexivity.
              right. eexists v_pop.
              split_and!; [exact Hvpop_in_s|reflexivity..]. }
            apply linearized_sound_nil.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_cons_True in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil fmap_app in Hτ2_bounded₀ |- *. simpl in Hτ2_bounded₀ |- *.
            rewrite elem_of_app in Hτ2_bounded₀.
            destruct Hτ2_bounded₀ as [Hτ2_old | Hτ2_new].
            { apply sublist_inserts_r. eapply Hval_then_not_pr; eassumption. }
            rewrite !elem_of_cons elem_of_nil in Hτ2_new. destruct Hτ2_new as [-> | []].
            (* τ2₀ = τ2: need [τ1₀;τ2] sublist. τ1₀ = τ1 by NoDup m.*2. *)
            assert (Heq_τ1: τ1₀ = τ1) by (by eapply valid_match_inj_call). subst τ1₀.
            (* τ1 must be linearized in old ts'_head because τ1 finished before n:
               filter(tag=τ1)(ts'_head) = [(Call); (Lin); (Ret)] by Hper_tag_lin + Hfilter *)
            assert (Hτ1_lin : τ1 ∈ (filter (is_lin ∘ snd) ts'_head).*1).
            { destruct (Hper_tag_lin τ1) as (v₁ & v₁' & Hprefix₁).
              (* filter(tag=τ1)(take n ts) has both Call and Ret *)
              assert (Hcall_in_take : ∃ vc, (τ1, Call vc) ∈ take n ts).
              { destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp' Hcp'].
                apply list_elem_of_lookup_1 in Hcp' as [j Hj].
                assert (j < n).
                { assert (j < length ts) by (eapply lookup_lt_Some; eauto).
                  assert (j ≠ n) by (intros ->; rewrite Hlookup in Hj; discriminate).
                  destruct (decide (j < n)); [lia|].
                  exfalso. apply Hτ1_finished.
                  apply (list_elem_of_fmap_2 fst _ (τ1, Call (encode_request (Push vp')))).
                  apply list_elem_of_filter_2; [done|].
                  apply (list_elem_of_lookup_2 _ (j - n)).
                  rewrite lookup_drop. replace (n + (j - n)) with j by lia. exact Hj. }
                eexists. eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hj|lia]. }
              assert (Hret_in_take : ∃ vr, (τ1, Ret vr) ∈ take n ts).
              { apply list_elem_of_fmap_1 in Hτ1_ret as ([τ1' ev1] & Heq1 & Hin1).
                simpl in Heq1. subst τ1'.
                apply list_elem_of_filter in Hin1 as [Hret1 Hin1'].
                destruct ev1 as [|v1 v1'|]; try by destruct Hret1.
                eexists. exact Hin1'. }
              destruct Hcall_in_take as [vc Hcall_in].
              destruct Hret_in_take as [vr Hret_in].
              (* These are in ts'_head via Hfilter *)
              assert (Hcall_in_head : (τ1, Call vc) ∈ ts'_head).
              { rewrite Hfilter in Hcall_in. apply list_elem_of_filter in Hcall_in as [_ ?]. done. }
              assert (Hret_in_head : (τ1, Ret vr) ∈ ts'_head).
              { rewrite Hfilter in Hret_in. apply list_elem_of_filter in Hret_in as [_ ?]. done. }
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_in_head; last done.
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hret_in_head; last done.
              (* filter(tag=τ1)(ts'_head) has ≥ 2 elements (Call and Ret). *)
              apply prefix_length in Hprefix₁ as Hlen_pfx.
              assert (Hlen_filt : 2 ≤ length (filter (λ x, x.1 = τ1) ts'_head)).
              { destruct (filter (λ x, x.1 = τ1) ts'_head) as [|a1 rest1].
                - exfalso. clear -Hcall_in_head. set_solver.
                - destruct rest1 as [|a2 rest2].
                  + exfalso.
                    assert (Hin1 : (τ1, Call vc) ∈ [a1]) by exact Hcall_in_head.
                    assert (Hin2 : (τ1, Ret vr) ∈ [a1]) by exact Hret_in_head.
                    assert (Htmp : (τ1, Call vc) = (τ1, Ret vr) → False).
                    { intros Habs. apply (f_equal snd) in Habs. simpl in Habs. discriminate. }
                    clear -Hcall_in_head Hret_in_head Htmp. set_solver.
                  + simpl. lia. }
              destruct (Hper_tag_lin τ1) as (v₁_a & v₁_b & Hprefix₁_a).
              destruct (filter (λ x, x.1 = τ1) ts'_head) as [|b1 [|b2 rest2']] eqn:Hfilt_eq.
              - simpl in Hlen_filt. lia.
              - simpl in Hlen_filt. lia.
              - simpl in Hprefix₁_a.
                apply prefix_cons_inv_2 in Hprefix₁_a.
                pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₁_a) as Heq_lin.
                apply (list_elem_of_fmap_2 fst _ (τ1, Lin v₁_a v₁_b)).
                apply list_elem_of_filter_2; [done|].
                apply (list_elem_of_filter_1 (λ x, x.1 = τ1)).
                rewrite Hfilt_eq Heq_lin. clear. set_solver. }
            (* [τ1;τ2] sublist of old_lin_tags ++ [τ2] *)
            destruct (list_elem_of_split _ _ Hτ1_lin) as (la & la' & Hlin_eq).
            apply sublist_cons_l.
            exists la, (la' ++ [τ2]).
            split.
            ++ by rewrite Hlin_eq -assoc.
            ++ apply sublist_inserts_l. reflexivity.
          --(* Hstate_of_trace *)
            rewrite Hstate_of_trace.
            symmetry. exact (state_of_trace_call_pop_nonoverlap n τ1 τ2 v_pop Hin_m Hcp Hτ1_ret Hlookup).
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            rewrite /ts'_head_lin filter_app in Hτ₀_not_lin.
            rewrite filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_not_lin. simpl in Hτ₀_not_lin.
            assert (Hτ₀_not_lin_old : τ₀ ∉ (filter (is_lin ∘ snd) ts'_head).*1) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_ne_τ2 : τ₀ ≠ τ2) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              assert (Hsubset := trace_pendingOp_call τ2 (encode_request Pop)
                                   (drop (Datatypes.S n) ts)).
              clear -Hsubset Hτ₀_pending Hτ₀_ne_τ2. set_solver. }
            destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin_old) Hτ₀_pop_emp)
              as (icall & Hicall_lookup & Hicall_covers).
            exists icall. split; first assumption.
            intros i Hi.
            destruct (decide (i = n)) as [-> | Hne_i].
            ++ assert (Hn_gt_icall : icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. injection Hicall_lookup as ->.
                exfalso. exact (Hτ₀_ne_τ2 eq_refl). }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              (* Position n is a Call Pop for τ2. *)
              assert (Hstate_Sn : state_of_trace (Datatypes.S n) ≠ ∅).
              { rewrite (state_of_trace_call_pop_nonoverlap n τ1 τ2 v_pop Hin_m Hcp Hτ1_ret Hlookup).
                rewrite -Hstate_of_trace. exact Hnot_emp_after_pop. }
              destruct (state_of_trace_nonempty_witness (Datatypes.S n) Hstate_Sn)
                as (τ1w & τ2w & Hin_mw & Hτ1w_ret & Hτ2w_nocall).
              exists τ1w, τ2w. split; [exact Hin_mw|].
              rewrite /push_pop_covers.
              (* ret_of_tag τ1w < n: τ1w has Ret in take (S n) ts, so first Ret ≤ n.
                 Position n is (τ2, Call Pop), not a Ret for τ1w, so first Ret < n. *)
              destruct (ret_of_tag ts τ1w) as [[iret_w [τ_rw ev_rw]]|] eqn:Hret_w.
              ** destruct (call_of_tag ts τ2w) as [[icall_w [τ_cw ev_cw]]|] eqn:Hcall_w.
                 --- simpl. split.
                     +++ (* iret_w < n *)
                         rewrite /ret_of_tag list_find_Some /= in Hret_w.
                         destruct Hret_w as (Hlookup_rw & [Htag_rw Hret_rw] & Hmin_rw).
                         (* τ1w has Ret in take (S n) ts *)
                         apply list_elem_of_fmap_1 in Hτ1w_ret as ([τ_r ev_r] & Heq_r & Hin_r).
                         simpl in Heq_r. subst τ_r.
                         apply list_elem_of_filter in Hin_r as [His_r Hin_r].
                         apply list_elem_of_lookup_1 in Hin_r as [j_r Hj_r].
                         apply lookup_take_Some in Hj_r as [Hj_r Hj_r_lt].
                         assert (iret_w ≤ j_r).
                         { destruct (decide (iret_w ≤ j_r)); [lia|exfalso].
                           exact (Hmin_rw j_r (τ1w, ev_r) Hj_r ltac:(lia) (conj eq_refl His_r)). }
                         (* iret_w ≤ j_r < S n, so iret_w ≤ n. But position n is Call, not Ret for τ1w. *)
                         assert (iret_w ≠ n).
                         { intros Heq_n. subst iret_w.
                           rewrite Hlookup in Hlookup_rw. simplify_eq. }
                         lia.
                     +++ (* n < icall_w *)
                         rewrite /call_of_tag list_find_Some /= in Hcall_w.
                         destruct Hcall_w as (Hlookup_cw & [Htag_cw Hcall_cw] & Hmin_cw).
                         (* τ2w has no Call in take (S n) ts, so icall_w ≥ S n, i.e., > n *)
                         destruct (decide (n < icall_w)); [lia|exfalso].
                         assert (icall_w ≤ n) by lia.
                         apply Hτ2w_nocall. subst τ_cw.
                         apply (list_elem_of_fmap_2 fst _ (τ2w, ev_cw)).
                         apply list_elem_of_filter_2; [exact Hcall_cw|].
                         eapply list_elem_of_lookup_2.
                         rewrite lookup_take_lt; [exact Hlookup_cw|lia].
                 --- (* call_of_tag τ2w = None: contradiction, τ2w has a Call Pop from valid_match *)
                     exfalso.
                     pose proof (valid_match_call_pop ts m τ1w τ2w Hvalid Hin_mw) as Hcall_pop_w.
                     apply list_elem_of_lookup_1 in Hcall_pop_w as [j_c Hj_c].
                     rewrite /call_of_tag list_find_None Forall_forall in Hcall_w.
                     apply (Hcall_w (τ2w, Call (encode_request Pop))).
                     { exact (list_elem_of_lookup_2 _ _ _ Hj_c). }
                     simpl. done.
              ** (* ret_of_tag τ1w = None: contradiction, τ1w has Ret in take (S n) ts *)
                 exfalso.
                 apply list_elem_of_fmap_1 in Hτ1w_ret as ([τ_r ev_r] & Heq_r & Hin_r).
                 simpl in Heq_r. subst τ_r.
                 apply list_elem_of_filter in Hin_r as [His_r Hin_r].
                 apply list_elem_of_lookup_1 in Hin_r as [j_r Hj_r].
                 apply lookup_take_Some in Hj_r as [Hj_r _].
                 rewrite /ret_of_tag list_find_None Forall_forall in Hret_w.
                 apply (Hret_w (τ1w, ev_r) (list_elem_of_lookup_2 _ _ _ Hj_r)).
                 simpl. done.
            ++ apply Hicall_covers. lia.
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            rewrite /ts'_head_lin filter_app in Hτ₀_lin.
            rewrite filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_cons_True in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_lin. simpl in Hτ₀_lin.
            apply elem_of_app in Hτ₀_lin as [Hτ₀_lin_old | Hτ₀_lin_new].
            ++ assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
              { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
                assert (Hsubset := trace_pendingOp_call τ2 (encode_request Pop)
                                     (drop (Datatypes.S n) ts)).
                assert (Hne_τ₀ : τ₀ ≠ τ2).
                { intros <-.
                  exact (call_at_n_not_linearized n τ₀ _ ts'_head Hwf Hlookup Hfilter Hper_tag_lin Hτ₀_lin_old). }
                clear -Hsubset Hτ₀_pending Hne_τ₀.
                set_solver. }
              destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin_old) Hτ₀_push)
                as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
              exists τ2_0. split; first assumption.
              rewrite /ts'_head_lin filter_app.
              rewrite filter_cons_False; last by simpl; auto.
              rewrite filter_cons_True; last by simpl; auto.
              rewrite filter_nil fmap_app. simpl. clear -Hτ2_0_lin. set_solver.
            ++ rewrite !elem_of_cons elem_of_nil in Hτ₀_lin_new.
              destruct Hτ₀_lin_new as [-> | []].
              exfalso.
              eapply push_xor_pop_of_trace; [exact Hwf|exact Hτ₀_push|].
              rewrite /pop_of_trace.
              apply (list_elem_of_fmap_2 fst _ (τ2, Call (encode_request Pop))).
              apply list_elem_of_filter_2; [done|exact Hin].
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ1₀_called.
            rewrite (take_S_r _ _ _ Hlookup) filter_app fmap_app
              filter_cons_True // filter_nil in Hτ2₀_called.
            simpl in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app
              filter_cons_False; [|by simpl; auto].
            rewrite filter_cons_True; [|by simpl; auto].
            rewrite filter_nil fmap_app /=.
            apply elem_of_app in Hτ1₀_called as [Hτ1₀_old | Hτ1₀_new];
            apply elem_of_app in Hτ2₀_called as [Hτ2₀_old | Hτ2₀_new].
            ++ apply elem_of_app. left. exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_old Hτ2₀_old).
            ++ rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [->|[]].
               (* τ2₀ = τ2: τ2 just linearized → τ2 ∈ new lin_tags *)
               apply elem_of_app. right. clear -Hτ1_ne_τ2. set_solver.
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               exfalso. exact (push_xor_pop_of_trace ts _ _ _ Hwf
                 (matched_push_in_push_of_trace _ _ Hin_m₀)
                 (in_pop_of_trace_from_call_pop _ Hin)).
            ++ rewrite elem_of_cons elem_of_nil in Hτ1₀_new. destruct Hτ1₀_new as [->|[]].
               rewrite elem_of_cons elem_of_nil in Hτ2₀_new. destruct Hτ2₀_new as [<-|[]].
               exfalso. refine (valid_match_ne _ _ _ _ _ Hvalid Hin_m₀ eq_refl).
               apply per_tag_complete_per_tag_wellformed, Hcomplete.
          --(* Hpop_lin_consistent *)
            intros τ₀ v₀_c v₀'_c Hτ₀_pop Hin_lin.
            apply elem_of_app in Hin_lin as [Hlin_old | Hlin_new].
            { exact (Hpop_lin_consistent _ _ _ Hτ₀_pop Hlin_old). }
            rewrite !elem_of_cons elem_of_nil in Hlin_new.
            destruct Hlin_new as [Habs | [Heq_lin | []]].
            ++ discriminate.
            ++ injection Heq_lin as -> _ ->.
               rewrite bool_decide_eq_true_2; last by (apply (list_elem_of_fmap_2 snd _ (τ1,τ2)); exact Hin_m).
               exists τ1, v_pop. split_and!; [exact Hin_m|exact Hcp|done].
          (**************** End LLM-generated code. *****************)
    - (* the next event is Ret *)
      apply list_elem_of_lookup_2 in Hlookup as Hin.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin as Hin_filter_tag; last done.
      destruct (Hwf τ) as [(v_push & Hvv & Hprefix)|(rsel & Hr_ne & Hprefix)];
        [|destruct rsel as [|v_pop]].
      + (* Ret Push *)
        rename τ into τ1.
        pose proof (Hin':= elem_of_prefix _ _ _ Hin_filter_tag Hprefix).
        rewrite !elem_of_cons elem_of_nil right_id in Hin'.
        destruct Hin' as [HFalse | Heq]; first discriminate HFalse.
        injection Heq as Heq.
        subst v'.
        assert (Hτ1_in_m: τ1 ∈ m.*1).
        { destruct Hclosed as [Hclosed_push _].
          eapply list_elem_of_weaken; last exact Hclosed_push.
          rewrite /push_of_trace.
          apply (list_elem_of_fmap_2 fst _ (τ1,Call (encode_request (Push v_push)))).
          apply list_elem_of_filter_2.
          - eexists. done.
          - (*************** Begin LLM-generated code. ****************)
            apply (list_elem_of_filter_1 (λ x, x.1 = τ1)).
            destruct (filter (λ x, x.1 = τ1) ts) as [|a l] eqn:Hfilt.
            { exfalso. set_solver. }
            pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix) as Ha. subst a.
            set_solver.
            (**************** End LLM-generated code. *****************)  }
        apply list_elem_of_fmap_1 in Hτ1_in_m.
        destruct Hτ1_in_m as ([τ1' τ2] & Heqτ1 & Hin_m).
        simpl in Heqτ1. subst τ1'.
        opose proof (valid_match_ne _ _ _ _ _ Hvalid Hin_m) as Hτ1_ne_τ2.
        { apply per_tag_complete_per_tag_wellformed, Hcomplete. }
        destruct (decide ((τ2,Call (encode_request Pop)) ∈ drop n ts)) as [Hτ2_not_started|Hτ2_started].
        * (* The matched Pop hasn't started -- linearize τ1 here *)
          exists (ts'_head ++ [(τ1,Lin (encode_request (Push v_push)) #());
            (τ1,Ret #())]), ({[+ v_push +]} ⊎ s).
          intros ts'_head_lin. split_and!.
          (*************** Begin LLM-generated code. ****************)
          --(* Hfilter *)
            rewrite filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            rewrite (take_S_r _ _ _ Hlookup).
            f_equal. done.
          --(* Hper_tag_lin *)
            intro τ₀.
            pose proof (Hper_tag_lin' := Hper_tag_lin).
            specialize (Hper_tag_lin' τ₀) as (v₀ & v₀' & Hprefix₀).
            rewrite filter_app.
            destruct (decide (τ₀ = τ1)) as [-> | Hne]; last first.
            { exists v₀, v₀'.
              rewrite filter_cons_False; [|simpl; congruence].
              rewrite filter_cons_False; [|simpl; congruence].
              rewrite filter_nil right_id. assumption. }
            exists (encode_request (Push v_push)), #().
            do 2 rewrite filter_cons_True //. rewrite filter_nil.
            assert (filter (λ x, x.1 = τ1) ts'_head = [(τ1, Call (encode_request (Push v_push)))]) as ->.
            { destruct (filter (λ x, x.1 = τ1) ts'_head) as [|hd [|hd2 rest2]] eqn:Hfilt1.
              - (* Empty: τ1's Call must be in ts'_head *)
                exfalso.
                destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcall_push].
                apply list_elem_of_lookup_1 in Hcall_push as [j Hj].
                destruct (decide (j < n)) as [Hjn|Hjn].
                + (* j < n: Call in take n ts, hence in ts'_head. filter ≠ []. *)
                  assert (Hin_take : (τ1, Call (encode_request (Push vp))) ∈ take n ts).
                  { eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hj|lia]. }
                  rewrite Hfilter in Hin_take.
                  apply list_elem_of_filter in Hin_take as [_ Hin_head].
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hin_head; last done.
                  rewrite Hfilt1 in Hin_head.
                  clear -Hin_head.
                  set_solver.
                + (* j ≥ n: Call after Ret. filter(drop) starts with Ret, not Call. Contradicts prefix. *)
                  assert (j ≠ n) by (intros ->; rewrite Hlookup in Hj; discriminate).
                  assert (Hj_gt : j > n) by lia.
                  destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (vc & vc' & Hpfx).
                  rewrite -(take_drop n ts) filter_app Hfilter list_filter_comm Hfilt1 left_id in Hpfx.
                  pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
                  rewrite Hdrop_eq filter_cons_True // in Hpfx.
                  apply prefix_cons_inv_1 in Hpfx. discriminate.
              - (* Singleton: hd = Call v₀. Show v₀ = Push v_push. *)
                apply prefix_cons_inv_1 in Hprefix₀ as ->. f_equal.
                assert (Hcv_in_ts : (τ1, Call v₀) ∈ ts).
                { assert (Hin_head : (τ1, Call v₀) ∈ ts'_head).
                  { apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). rewrite Hfilt1. clear. set_solver. }
                  assert (Hcv_in_take : (τ1, Call v₀) ∈ take n ts).
                  { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; by auto|exact Hin_head]. }
                  apply list_elem_of_lookup_1 in Hcv_in_take as [i Hi].
                  apply lookup_take_Some in Hi as [Hi _].
                  exact (list_elem_of_lookup_2 _ _ _ Hi). }
                apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcv_in_ts; last done.
                pose proof (elem_of_prefix _ _ _ Hcv_in_ts Hprefix) as Hin_pfx.
                rewrite !elem_of_cons elem_of_nil right_id in Hin_pfx.
                destruct Hin_pfx as [Hin_pfx|Hin_pfx]; [by injection Hin_pfx|].
                apply (f_equal snd) in Hin_pfx. simpl in Hin_pfx. discriminate.
              - (* Two or more: τ1 linearized → Hpush_alap → τ2 linearized → contradiction *)
                exfalso.
                apply prefix_cons_inv_2 in Hprefix₀.
                pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as ->. (* hd2 = Lin *)
                assert (Hτ1_lin_old : τ1 ∈ (filter (is_lin ∘ snd) ts'_head).*1).
                { apply (list_elem_of_fmap_2 fst _ (τ1, Lin v₀ v₀')).
                  apply list_elem_of_filter_2; [done|].
                  apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). rewrite Hfilt1. clear. set_solver. }
                assert (Hτ1_push_of : τ1 ∈ push_of_trace ts).
                { destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcp].
                  apply (list_elem_of_fmap_2 fst _ (τ1, Call (encode_request (Push vp)))).
                  apply list_elem_of_filter_2; [eexists; done|exact Hcp]. }
                assert (Hτ1_pending : τ1 ∈ trace_pendingOp (drop n ts)).
                { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
                  apply filter_tag_trace_pendingOp.
                  rewrite filter_cons_True //. apply trace_pendingOp_ret_elem_of. }
                destruct (Hpush_alap τ1 (conj Hτ1_pending Hτ1_lin_old) Hτ1_push_of)
                  as (τ2' & Hin_m' & Hτ2'_lin).
                assert (τ2' = τ2) by (by eapply valid_match_inj_ret). subst τ2'.
                (* τ2 linearized but has no events in ts'_head *)
                pose proof (Hper_tag_lin τ2) as (v₂ & v₂' & Hprefix₂).
                assert (Hτ2_no_ev : filter (λ x, x.1 = τ2) ts'_head = []).
                { destruct (filter (λ x, x.1 = τ2) ts'_head) as [|c cs] eqn:Hft2; [done|].
                  exfalso.
                  pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₂) as Hc_eq. subst c.
                  assert (Hτ2_t: (τ2, Call v₂) ∈ filter (not ∘ is_lin ∘ snd) ts'_head).
                  { apply list_elem_of_filter_2; [simpl; auto|].
                    apply (list_elem_of_filter_1 (λ x, x.1 = τ2)). rewrite Hft2. clear. set_solver. }
                  rewrite -Hfilter in Hτ2_t.
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hτ2_t; last done.
                  apply (list_elem_of_filter_2 (is_call∘snd)) in Hτ2_t; last done.
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hτ2_not_started as Hτ2_d; last done.
                  apply (list_elem_of_filter_2 (is_call∘snd)) in Hτ2_d; last done.
                  destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ2) as (vc3 & vc3' & Hpfx3).
                  rewrite -(take_drop n ts) filter_app in Hpfx3.
                  apply (prefix_filter (is_call∘snd)) in Hpfx3.
                  apply prefix_length in Hpfx3.
                  rewrite filter_app length_app in Hpfx3.
                  enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (take n ts)))).
                  { enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (drop n ts)))) by
                    (simpl in Hpfx3; lia).
                    destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (drop n ts))).
                    - clear -Hτ2_d. set_solver.
                    - simpl. lia. }
                  destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ2) (take n ts))).
                  - clear -Hτ2_t. set_solver.
                  - simpl. lia. }
                apply (list_elem_of_fmap_1) in Hτ2'_lin as ([? ev'] & [= <-] & Hin').
                apply list_elem_of_filter in Hin' as [_ Hin'].
                apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hin'; last done.
                rewrite Hτ2_no_ev in Hin'. clear -Hin'. set_solver. }
            eexists. reflexivity.
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil.
            eapply linearized_sound_app; first eassumption.
            eapply linearized_sound_cons.
            { left. exists v_push. split; [assumption|reflexivity]. }
            { eexists. split; first reflexivity.
              split; reflexivity. }
            apply linearized_sound_nil.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_True in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil fmap_app in Hτ2_bounded₀ |- *.
            simpl in Hτ2_bounded₀ |- *.
            rewrite elem_of_app in Hτ2_bounded₀.
            destruct Hτ2_bounded₀ as [Hτ2_old | Hτ2_new].
            { apply sublist_inserts_r. eapply Hval_then_not_pr; eassumption. }
            rewrite !elem_of_cons elem_of_nil in Hτ2_new.
            destruct Hτ2_new as [-> | []].
            (* τ2₀ = τ1: τ1 is push but (τ1₀, τ1) ∈ m means τ1 is pop too. *)
            exfalso. exact (push_xor_pop_of_trace ts _ _ _ Hwf
              (matched_push_in_push_of_trace _ _ Hin_m)
              (matched_pop_in_pop_of_trace _ _ Hin_m₀)).
          --(* Hstate_of_trace *)
            rewrite Hstate_of_trace.
            destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcp].
            assert (vp = v_push).
            { apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcp; last done.
              pose proof (elem_of_prefix _ _ _ Hcp Hprefix) as Hin'.
              rewrite !elem_of_cons elem_of_nil right_id in Hin'.
              destruct Hin' as [Hin'|Hin']; [by injection Hin'|discriminate]. }
            subst vp.
            assert (Hτ2_not_in_call_take : τ2 ∉ (filter (is_call∘snd) (take n ts)).*1).
            { intro Habs.
              destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ2) as (vc & vc' & Hprefix_τ2).
              apply list_elem_of_fmap_1 in Habs as ([τ2' ev2] & Heq2 & Hin2).
              simpl in Heq2. subst τ2'.
              apply list_elem_of_filter in Hin2 as [_ Hin2].
              apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hin2 as Hin2_f; last done.
              apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hτ2_not_started as Hτ2_f; last done.
              rewrite -(take_drop n ts) filter_app in Hprefix_τ2.
              destruct (filter (λ x, x.1 = τ2) (take n ts)) as [|hd_t tl_t].
              { set_solver. }
              destruct (filter (λ x, x.1 = τ2) (drop n ts)) as [|hd_d tl_d].
              { set_solver. }
              pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix_τ2) as ->. (* hd_t = (τ2, Call vc) *)
              apply prefix_cons_inv_2 in Hprefix_τ2.
              destruct tl_t as [|? ?]; last first.
              { exfalso. apply prefix_length in Hprefix_τ2.
                revert Hprefix_τ2. rewrite /= length_app /=. lia. }
              simpl in Hprefix_τ2.
              pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix_τ2) as ->. (* hd_d = (τ2, Ret vc') *)
              apply prefix_cons_inv_2 in Hprefix_τ2.
              apply prefix_nil_inv in Hprefix_τ2. subst tl_d.
              rewrite elem_of_cons elem_of_nil in Hτ2_f.
              destruct Hτ2_f as [Hτ2_f|[]].
              apply (f_equal snd) in Hτ2_f. simpl in Hτ2_f. discriminate. }
            symmetry. exact (state_of_trace_ret_push_nonoverlap n τ1 τ2 v_push Hin_m Hcp Hτ2_not_in_call_take Hlookup).
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            rewrite /ts'_head_lin filter_app in Hτ₀_not_lin.
            rewrite filter_cons_True in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_not_lin. simpl in Hτ₀_not_lin.
            assert (Hτ₀_not_lin_old : τ₀ ∉ (filter (is_lin ∘ snd) ts'_head).*1) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_ne_τ1 : τ₀ ≠ τ1) by (clear -Hτ₀_not_lin; set_solver).
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              apply filter_tag_trace_pendingOp.
              destruct (decide (τ₀ = τ1)) as [-> | Hne].
              - exfalso. exact (Hτ₀_ne_τ1 eq_refl).
              - rewrite filter_cons_False //.
                rewrite -filter_tag_trace_pendingOp. assumption. }
            destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin_old) Hτ₀_pop_emp)
              as (icall & Hicall_lookup & Hicall_covers).
            exists icall. split; first assumption.
            intros i Hi.
            destruct (decide (i = n)) as [-> | Hne_i].
            ++ assert (Hn_gt_icall : icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. discriminate. }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              exists τ1c, τ2c. split; [exact Hinm|].
              rewrite /push_pop_covers in Hcover |- *.
              destruct (ret_of_tag ts τ1c) as [[iret_c [? tret]]|] eqn:Hiret; [|done].
              destruct (call_of_tag ts τ2c) as [[icall_c [? tcall]]|] eqn:Hicall_eq; [|done].
              simpl in Hcover |- *.
              split; first lia.
              cut (icall_c ≠ n); first lia.
              intros ->.
              rewrite /call_of_tag list_find_Some /= in Hicall_eq.
              destruct Hicall_eq as (Hlookup_call & [-> His_call] & _).
              rewrite Hlookup in Hlookup_call. injection Hlookup_call as <- <-.
              (* Position n is Ret, but call_of_tag found a Call. Contradiction. *)
              by simpl in His_call.
            ++ apply Hicall_covers. lia.
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            rewrite /ts'_head_lin filter_app in Hτ₀_lin.
            rewrite filter_cons_True in Hτ₀_lin; last by simpl; auto.
            rewrite filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil fmap_app in Hτ₀_lin. simpl in Hτ₀_lin.
            apply elem_of_app in Hτ₀_lin as [Hτ₀_lin_old | Hτ₀_lin_new].
            ++ (* Old: use IH *)
              assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
              { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
                apply filter_tag_trace_pendingOp.
                destruct (decide (τ₀ = τ1)) as [-> | Hne].
                - rewrite filter_cons_True //.
                  apply trace_pendingOp_ret_elem_of.
                - rewrite filter_cons_False //.
                  rewrite -filter_tag_trace_pendingOp. assumption. }
              destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin_old) Hτ₀_push)
                as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
              exists τ2_0. split; first assumption.
              rewrite /ts'_head_lin filter_app.
              rewrite filter_cons_True; last by simpl; auto.
              rewrite filter_cons_False; last by simpl; auto.
              rewrite filter_nil fmap_app. simpl. set_solver.
            ++ (* New: τ₀ = τ1 *)
              rewrite !elem_of_cons elem_of_nil in Hτ₀_lin_new.
              destruct Hτ₀_lin_new as [-> | []].
              (* τ₀ = τ1: but τ1 just Ret'd at position n, so τ1 ∉ trace_pendingOp(drop (S n) ts).
                 τ1's Ret at position n makes τ1 complete, not pending. *)
              exfalso.
              assert (Hfilt_empty : filter (λ x, x.1 = τ1) (drop (Datatypes.S n) ts) = []).
              { pose proof (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (vc & vc' & Hprefix_τ1).
                assert (Hret_take : (τ1, Ret #()) ∈ filter (λ x, x.1 = τ1) (take (Datatypes.S n) ts)).
                { apply list_elem_of_filter_2; [done|].
                  eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hlookup|lia]. }
                pose proof (Hprefix_τ1' := Hprefix_τ1).
                rewrite -(take_drop (Datatypes.S n) ts) filter_app in Hprefix_τ1'.
                destruct (filter (λ x, x.1 = τ1) (take (Datatypes.S n) ts)) as [|a [|b rest]] eqn:Hft.
                - exfalso. clear -Hret_take. set_solver.
                - exfalso.
                  pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix_τ1') as Heq_a. subst a.
                  rewrite elem_of_cons elem_of_nil in Hret_take.
                  destruct Hret_take as [Habs|[]]. discriminate.
                - apply nil_length_inv.
                  apply prefix_length in Hprefix_τ1'.
                  revert Hprefix_τ1'. rewrite /= length_app /=. lia. }
              apply filter_tag_trace_pendingOp in Hτ₀_pending.
              assert (Heq_f : filter (λ t : positive * trace, t.1 = τ1) (drop (Datatypes.S n) ts) = []).
              { exact Hfilt_empty. }
              rewrite Heq_f /trace_pendingOp /= in Hτ₀_pending. clear -Hτ₀_pending. set_solver.
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) !filter_app !fmap_app in Hτ1₀_called, Hτ2₀_called.
            rewrite filter_cons_False in Hτ1₀_called; last by simpl; auto.
            rewrite filter_cons_False in Hτ2₀_called; last by simpl; auto.
            rewrite filter_nil fmap_nil right_id in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil fmap_app /=.
            apply elem_of_app. left.
            exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_called Hτ2₀_called).
          --(* Hpop_lin_consistent *)
            intros τ₀ v₀_c v₀'_c Hτ₀_pop Hin_lin.
            apply elem_of_app in Hin_lin as [Hlin_old | Hlin_new].
            { exact (Hpop_lin_consistent _ _ _ Hτ₀_pop Hlin_old). }
            rewrite !elem_of_cons elem_of_nil in Hlin_new.
            destruct Hlin_new as [Heq_lin | [Habs | []]]; [|discriminate].
            (* τ₀ = τ1 but τ1 is push and τ₀ is pop *)
            exfalso.
            apply (f_equal fst) in Heq_lin. simpl in Heq_lin. subst τ₀.
            exact (push_xor_pop_of_trace ts _ _ _ Hwf
              (matched_push_in_push_of_trace _ _ Hin_m) Hτ₀_pop).
          (**************** End LLM-generated code. *****************)
        * (* The matched Pop has started -- τ2 must have been linearized before,
            so don't linearize anything *)
          exists (ts'_head ++ [(τ1,Ret #())]), s.
          intros ts'_head_lin. split_and!.
          (*************** Begin LLM-generated code. ****************)
          --(* Hfilter *)
            rewrite filter_app.
            rewrite filter_cons_True; last by simpl; auto.
            rewrite filter_nil.
            rewrite (take_S_r _ _ _ Hlookup).
            f_equal. done.
          --(* Hper_tag_lin *)
            intro τ₀.
            destruct (Hper_tag_lin τ₀) as (v₀ & v₀' & Hprefix₀).
            rewrite filter_app.
            destruct (decide (τ₀ = τ1)) as [-> | Hne]; last first.
            { exists v₀, v₀'.
              rewrite filter_cons_False; [|simpl; congruence].
              rewrite filter_nil right_id. assumption. }
            exists (encode_request (Push v_push)), #().
            rewrite filter_cons_True // filter_nil.
            destruct (filter (λ x, x.1 = τ1) ts'_head) as [|hd [|hd2 [|hd3 rest3]]] eqn:Hfilt1.
            { exfalso.
              destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcall_push].
              apply list_elem_of_lookup_1 in Hcall_push as [j Hj].
              destruct (decide (j < n)) as [Hjn|Hjn].
              - assert (Hin_take_vp : (τ1, Call (encode_request (Push vp))) ∈ take n ts).
                { eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hj|lia]. }
                rewrite Hfilter in Hin_take_vp.
                apply list_elem_of_filter in Hin_take_vp as [_ Hin_head].
                apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hin_head; last done.
                rewrite Hfilt1 in Hin_head.
                clear -Hin_head. set_solver.
              - assert (j ≠ n) by (intros ->; rewrite Hlookup in Hj; discriminate).
                destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (vc & vc' & Hpfx).
                rewrite -(take_drop n ts) filter_app Hfilter list_filter_comm Hfilt1 left_id in Hpfx.
                pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
                rewrite Hdrop_eq filter_cons_True // in Hpfx.
                apply prefix_cons_inv_1 in Hpfx. discriminate. }
            { (* Singleton: τ1 NOT linearized. Use Hpop_aeap to derive contradiction. *)
              exfalso.
              (* Determine hd = (τ1, Call v₀) *)
              pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as Hhd_eq.
              (* τ1 ∈ call_tags(take n ts) *)
              assert (Hτ1_called : τ1 ∈ (filter (is_call ∘ snd) (take n ts)).*1).
              { apply (list_elem_of_fmap_2 fst _ (τ1, Call v₀)).
                apply list_elem_of_filter_2; [done|].
                assert (Hin_head : (τ1, Call v₀) ∈ ts'_head).
                { apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). rewrite Hfilt1 Hhd_eq. clear. set_solver. }
                assert (Hin_take_v₀ : (τ1, Call v₀) ∈ take n ts).
                { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; by auto|exact Hin_head]. }
                exact Hin_take_v₀. }
              (* τ2 ∈ call_tags(take n ts) *)
              assert (Hτ2_called : τ2 ∈ (filter (is_call ∘ snd) (take n ts)).*1).
              { apply (list_elem_of_fmap_2 fst _ (τ2, Call (encode_request Pop))).
                apply list_elem_of_filter_2; [done|].
                pose proof (valid_match_call_pop ts m τ1 τ2 Hvalid Hin_m) as Hcp.
                rewrite -(take_drop n ts) in Hcp. apply elem_of_app in Hcp as [Hcp_take|Hcp_drop]; [done|].
                exfalso. exact (Hτ2_started Hcp_drop). }
              pose proof (Hpop_aeap _ _ Hin_m Hτ1_called Hτ2_called) as Hτ2_lin.
              pose proof (Hval_then_not_pr _ _ Hin_m Hτ2_lin) as Hsublist.
              assert (Hτ1_lin : τ1 ∈ (filter (is_lin ∘ snd) ts'_head).*1).
              { eapply elem_of_sublist; [|exact Hsublist]. clear. set_solver. }
              (* τ1 has Lin in ts'_head → Lin ∈ filter(tag=τ1)(ts'_head) = [hd]. *)
              apply list_elem_of_fmap_1 in Hτ1_lin as ([τ1' ev_lin] & Heq_τ1' & Hin_lin).
              simpl in Heq_τ1'. subst τ1'.
              apply list_elem_of_filter in Hin_lin as [His_lin Hin_lin].
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hin_lin; last done.
              (* Hin_lin : (τ1, ev_lin) ∈ filter(tag=τ1)(ts'_head) = [hd] = [(τ1, Call v₀)] *)
              subst hd.
              rewrite Hfilt1 elem_of_cons elem_of_nil in Hin_lin.
              destruct Hin_lin as [Hin_lin|[]].
              injection Hin_lin as Hin_lin. subst ev_lin.
              by simpl in His_lin. }
            { apply prefix_cons_inv_1 in Hprefix₀ as ?. subst hd.
              apply prefix_cons_inv_2 in Hprefix₀.
              pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as ->.
              assert (Hcv_in_ts : (τ1, Call v₀) ∈ ts).
              { assert (Hin_head' : (τ1, Call v₀) ∈ ts'_head).
                { apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). rewrite Hfilt1. clear. set_solver. }
                assert (Hin_take' : (τ1, Call v₀) ∈ take n ts).
                { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; by auto|exact Hin_head']. }
                apply list_elem_of_lookup_1 in Hin_take' as [i Hi].
                apply lookup_take_Some in Hi as [Hi _].
                exact (list_elem_of_lookup_2 _ _ _ Hi). }
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcv_in_ts; last done.
              pose proof (elem_of_prefix _ _ _ Hcv_in_ts Hprefix) as Hin_pfx.
              rewrite !elem_of_cons elem_of_nil right_id in Hin_pfx.
              destruct Hin_pfx as [Hin_pfx|Hin_pfx]; last discriminate Hin_pfx.
              injection Hin_pfx as ->.
              enough (v₀' = #()) by (subst v₀'; exists []; reflexivity).
              assert ((τ1, Lin (InjRV v_push) v₀') ∈ filter (is_lin ∘ snd) ts'_head)
                as (l1 & l2 & Heq_τ1_lin)%list_elem_of_split.
              { apply list_elem_of_filter_2; first by simpl.
                apply (list_elem_of_filter_1 (λ x, x.1=τ1)).
                rewrite Hfilt1. clear. set_solver. }
              rewrite Heq_τ1_lin in Hlin_sound.
              apply linearized_sound_app_inv in Hlin_sound as (? & _ & Hlin_sound).
              apply linearized_sound_cons_inv in Hlin_sound as (? & ? & Hrr & _).
              destruct Hrr as ([v_push'|] & Henc & Hrr); last discriminate Henc.
              destruct Hrr as [_ ?].
              assumption. }
            { (* 3+ elements: Ret ∈ ts'_head but only 1 Ret for τ1, at position n ∉ take n ts. *)
              exfalso.
              (* hd3 = (τ1, Ret v₀') from prefix. It's non-Lin, so in take n ts. *)
              apply prefix_cons_inv_2, prefix_cons_inv_2 in Hprefix₀.
              pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as Hhd3.
              assert (Hret_take : (τ1, Ret v₀') ∈ take n ts).
              { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; auto|].
                apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). rewrite Hfilt1 Hhd3. clear. set_solver. }
              (* Also Ret at position n in drop n ts. Two Rets ⇒ length contradiction. *)
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hret_take as Hrt_f; last done.
              apply (list_elem_of_filter_2 (is_ret∘snd)) in Hrt_f; last done.
              assert (Hrn_f : (τ1, Ret #()) ∈ filter (λ x, x.1 = τ1) (drop n ts)).
              { apply list_elem_of_filter_2; [done|].
                pose proof (drop_S _ _ _ Hlookup) as ->. clear. set_solver. }
              apply (list_elem_of_filter_2 (is_ret∘snd)) in Hrn_f; last done.
              destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (vc & vc' & Hpfx).
              apply (prefix_filter (is_ret∘snd)) in Hpfx.
              rewrite -(take_drop n ts) !filter_app in Hpfx.
              apply prefix_length in Hpfx. rewrite length_app in Hpfx.
              enough (1 ≤ length (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ1) (take n ts)))).
              { enough (1 ≤ length (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ1) (drop n ts)))) by
                (simpl in Hpfx; lia).
                destruct (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ1) (drop n ts))).
                - clear -Hrn_f. set_solver.
                - simpl. lia. }
              destruct (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ1) (take n ts))).
              - clear -Hrt_f. set_solver.
              - simpl. lia. }
          --(* Hlin_sound *)
            rewrite /ts'_head_lin filter_app.
            rewrite filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            assumption.
          --(* Hval_then_not_pr *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
            rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
            rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
            rewrite filter_nil right_id in Hτ2_bounded₀ |- *.
            eapply Hval_then_not_pr; eassumption.
          --(* Hstate_of_trace *)
            rewrite Hstate_of_trace.
            assert (Hτ2_in_call_take : τ2 ∈ (filter (is_call∘snd) (take n ts)).*1).
            { apply (list_elem_of_fmap_2 fst _ (τ2, Call (encode_request Pop))).
              apply list_elem_of_filter_2; [done|].
              pose proof (valid_match_call_pop ts m τ1 τ2 Hvalid Hin_m) as Hcp.
              rewrite -(take_drop n ts) in Hcp. apply elem_of_app in Hcp as [?|?]; [done|].
              exfalso. by apply Hτ2_started. }
            symmetry. exact (state_of_trace_ret_push_overlap n τ1 τ2 Hin_m Hτ2_in_call_take Hlookup).
          --(* Hempty_as early as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
            rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
            rewrite filter_nil right_id in Hτ₀_not_lin.
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              apply filter_tag_trace_pendingOp.
              destruct (decide (τ₀ = τ1)) as [-> | Hne].
              - rewrite filter_cons_True //. apply trace_pendingOp_ret_elem_of.
              - rewrite filter_cons_False //.
                rewrite -filter_tag_trace_pendingOp. assumption. }
            destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin) Hτ₀_pop_emp)
              as (icall & Hicall_lookup & Hicall_covers).
            exists icall. split; first assumption.
            intros i Hi.
            destruct (decide (i = n)) as [-> | Hne_i].
            ++ assert (Hn_gt_icall : icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. discriminate. }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              exists τ1c, τ2c. split; [exact Hinm|].
              rewrite /push_pop_covers in Hcover |- *.
              destruct (ret_of_tag ts τ1c) as [[iret_c [? tret]]|] eqn:Hiret; [|done].
              destruct (call_of_tag ts τ2c) as [[icall_c [? tcall]]|] eqn:Hicall_eq; [|done].
              simpl in Hcover |- *.
              split; first lia.
              cut (icall_c ≠ n); first lia.
              intros ->.
              rewrite /call_of_tag list_find_Some /= in Hicall_eq.
              destruct Hicall_eq as (Hlookup_call & [-> His_call] & _).
              rewrite Hlookup in Hlookup_call. injection Hlookup_call as <- <-.
              by simpl in His_call.
            ++ apply Hicall_covers. lia.
          --(* Hpush_as late as possible *)
            intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
            rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_lin; last by simpl; auto.
            rewrite filter_nil right_id in Hτ₀_lin.
            assert (Hτ₀_pending_old : τ₀ ∈ trace_pendingOp (drop n ts)).
            { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
              apply filter_tag_trace_pendingOp.
              destruct (decide (τ₀ = τ1)) as [-> | Hne].
              - rewrite filter_cons_True //. apply trace_pendingOp_ret_elem_of.
              - rewrite filter_cons_False //.
                rewrite -filter_tag_trace_pendingOp. assumption. }
            destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin) Hτ₀_push)
              as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
            exists τ2_0. split; first assumption.
            rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id. exact Hτ2_0_lin.
          --(* Hpop as early as possible *)
            intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
            rewrite (take_S_r _ _ _ Hlookup) !filter_app !fmap_app in Hτ1₀_called, Hτ2₀_called.
            rewrite filter_cons_False in Hτ1₀_called; last by simpl; auto.
            rewrite filter_cons_False in Hτ2₀_called; last by simpl; auto.
            rewrite filter_nil fmap_nil right_id in Hτ1₀_called, Hτ2₀_called.
            rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
            rewrite filter_nil right_id.
            exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_called Hτ2₀_called).
          --(* Hpop_lin_consistent *)
            apply (pop_lin_consistent_extend_ret _ _ _ _ Hpop_lin_consistent).
          (**************** End LLM-generated code. *****************)
      + (* Ret Pop IsEmpty
        It must have been linearized before, otherwise, [Hbag_sound] won't hold *)
        exists (ts'_head ++ [(τ,Ret (encode_response IsEmpty))]), s.
        intros ts'_head_lin. split_and!.
        (*************** Begin LLM-generated code. ****************)
        * (* Hfilter *)
          rewrite filter_app.
          rewrite filter_cons_True; last by simpl; auto.
          rewrite filter_nil.
          rewrite (take_S_r _ _ _ Hlookup).
          f_equal; first done.
          destruct (filter (λ x : positive * trace, x.1 = τ) ts) as [|x xs]; first (exfalso; set_solver).
          apply prefix_cons_inv_1 in Hprefix as Heq1. subst x.
          apply prefix_cons_inv_2 in Hprefix.
          rewrite elem_of_cons in Hin_filter_tag.
          destruct Hin_filter_tag as [|Hin_filter_tag]; first discriminate.
          destruct xs as [|x xs]; first (exfalso; set_solver).
          apply prefix_cons_inv_2 in Hprefix as Heq2. apply prefix_nil_inv in Heq2. subst xs.
          apply prefix_cons_inv_1 in Hprefix. subst x.
          set_solver.
        * (* Hper_tag_lin *)intro τ₀.
          specialize (Hper_tag_lin τ₀) as (v₀ & v₀' & Hprefix₀).
          rewrite filter_app.
          destruct (decide (τ₀ = τ)) as [-> | Hτ₀_ne_τ].
          -- assert (Hv'_eq : v' = encode_response IsEmpty).
             { pose proof (elem_of_prefix _ _ _ Hin_filter_tag Hprefix) as Hin'.
               rewrite !elem_of_cons elem_of_nil right_id in Hin'.
               destruct Hin' as [Hin'|Hin']; [discriminate|by injection Hin']. }
             subst v'.
             exists (encode_request Pop), (encode_response IsEmpty).
             rewrite filter_cons_True //.
             rewrite filter_nil.
             destruct (filter (λ x, x.1 = τ) ts'_head) as [|hd [|hd2 [|hd3 rest3]]] eqn:Hfilt1.
             { exfalso.
               destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ) as (vc & vc' & Hpfx_τ).
               rewrite -(take_drop n ts) filter_app Hfilter list_filter_comm Hfilt1 left_id in Hpfx_τ.
               pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
               rewrite Hdrop_eq filter_cons_True // in Hpfx_τ.
               apply prefix_cons_inv_1 in Hpfx_τ. discriminate. }
             { (* Singleton: τ not linearized. Use Hbag_sound + Hempty_aeap. *)
               exfalso.
               (* τ is pending in drop n ts and not linearized *)
               assert (Hτ_pending : τ ∈ trace_pendingOp (drop n ts)).
               { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq. rewrite Hdrop_eq.
                 apply filter_tag_trace_pendingOp.
                 rewrite filter_cons_True //. apply trace_pendingOp_ret_elem_of. }
               assert (Hτ_not_lin : τ ∉ (filter (is_lin ∘ snd) ts'_head).*1).
               { intro Habs. apply list_elem_of_fmap_1 in Habs as ([? ev'] & [= <-] & Hin_lin).
                 apply list_elem_of_filter in Hin_lin as [His_lin Hin_lin].
                 apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin_lin; last done.
                 pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as Hhd_eq. subst hd.
                 rewrite Hfilt1 elem_of_cons elem_of_nil in Hin_lin.
                 destruct Hin_lin as [Hin_lin|[]].
                 injection Hin_lin as Hin_lin. subst ev'.
                 by simpl in His_lin. }
               assert (Hτ_pop_emp : τ ∈ pop_emp_of_trace ts).
               { apply (list_elem_of_fmap_2 fst _ (τ, Ret (encode_response IsEmpty))).
                 apply list_elem_of_filter_2; [done|exact (list_elem_of_lookup_2 _ _ _ Hlookup)]. }
               (* From Hempty_aeap IH: coverage for icall ≤ i < n *)
               destruct (Hempty_aeap τ (conj Hτ_pending Hτ_not_lin) Hτ_pop_emp)
                 as (icall & Hicall_lookup & Hicall_covers).
               (* From Hbag_sound: uncovered position in icall..n *)
               destruct (Hbag_sound τ Hτ_pop_emp) as (icall' & iret & i_unc & Hicall' & Hiret & [Hbnd_lo Hbnd_hi] & Hno_cover & _).
               (* icall = icall': unique Call position. Both are Call Pop for τ. *)
               assert (icall = icall').
               { destruct (decide (icall = icall')); [lia|].
                 exfalso.
                 (* Two Calls for τ at different positions. Contradiction with per_tag_wellformed. *)
                 destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ) as (vc_u & vc_u' & Hpfx_u).
                 apply (prefix_filter (is_call∘snd)) in Hpfx_u.
                 rewrite filter_cons_True in Hpfx_u; last done.
                 rewrite filter_cons_False in Hpfx_u; last by simpl; auto.
                 rewrite filter_nil in Hpfx_u.
                 (* Split at max(icall,icall'). One Call in take, one in drop. *)
                 set (split_pos := max icall icall').
                 pose proof (list_elem_of_lookup_2 _ _ _ Hicall_lookup) as Hin_c1.
                 pose proof (list_elem_of_lookup_2 _ _ _ Hicall') as Hin_c2.
                 rewrite -(take_drop split_pos ts) !filter_app in Hpfx_u.
                 apply prefix_length in Hpfx_u. rewrite !length_app length_cons length_nil in Hpfx_u.
                 assert (Hin_take : (τ, Call (encode_request Pop)) ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ) (take split_pos ts))).
                 { apply list_elem_of_filter_2; [done|]. apply list_elem_of_filter_2; [done|].
                   destruct (decide (icall < icall')).
                   - eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hicall_lookup|]. subst split_pos. lia.
                   - eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hicall'|]. subst split_pos. lia. }
                 assert (Hin_drop : (τ, Call (encode_request Pop)) ∈ filter (is_call ∘ snd) (filter (λ x, x.1 = τ) (drop split_pos ts))).
                 { apply list_elem_of_filter_2; [done|]. apply list_elem_of_filter_2; [done|].
                   destruct (decide (icall < icall')).
                   - replace icall' with (split_pos + (icall' - split_pos)) in Hicall' by (subst split_pos; lia).
                     rewrite -lookup_drop in Hicall'. exact (list_elem_of_lookup_2 _ _ _ Hicall').
                   - replace icall with (split_pos + (icall - split_pos)) in Hicall_lookup by (subst split_pos; lia).
                     rewrite -lookup_drop in Hicall_lookup. exact (list_elem_of_lookup_2 _ _ _ Hicall_lookup). }
                 enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ) (take split_pos ts)))).
                 { enough (1 ≤ length (filter (is_call ∘ snd) (filter (λ x, x.1 = τ) (drop split_pos ts))));
                   [lia|]; destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ) (drop split_pos ts)));
                   [clear -Hin_drop; set_solver|simpl; lia]. }
                 destruct (filter (is_call ∘ snd) (filter (λ x, x.1 = τ) (take split_pos ts)));
                   [clear -Hin_take; set_solver|simpl; lia]. }
               subst icall'.
               (* iret = n (τ's Ret at position n) *)
               assert (iret = n).
               { destruct (decide (iret = n)); [lia|exfalso].
                 (* Two Rets at different positions. Same take/drop argument. *)
                 destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ) as (vc_r & vc_r' & Hpfx_r).
                 apply (prefix_filter (is_ret∘snd)) in Hpfx_r.
                 rewrite filter_cons_False in Hpfx_r; last by simpl; auto.
                 rewrite filter_cons_True in Hpfx_r; last by simpl; auto.
                 rewrite filter_nil in Hpfx_r.
                 set (split_r := max iret n).
                 rewrite -(take_drop split_r ts) !filter_app in Hpfx_r.
                 apply prefix_length in Hpfx_r. rewrite !length_app length_cons length_nil in Hpfx_r.
                 assert (Hrt1 : (τ, Ret (encode_response IsEmpty)) ∈ filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (take split_r ts))).
                 { apply list_elem_of_filter_2; [done|]. apply list_elem_of_filter_2; [done|].
                   destruct (decide (iret < n)).
                   - eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hiret|subst split_r; lia].
                   - eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hlookup|subst split_r; lia]. }
                 assert (Hrt2 : (τ, Ret (encode_response IsEmpty)) ∈ filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (drop split_r ts))).
                 { apply list_elem_of_filter_2; [done|]. apply list_elem_of_filter_2; [done|].
                   destruct (decide (iret < n)).
                   - replace n with (split_r + (n - split_r)) in Hlookup by (subst split_r; lia).
                     rewrite -lookup_drop in Hlookup. exact (list_elem_of_lookup_2 _ _ _ Hlookup).
                   - replace iret with (split_r + (iret - split_r)) in Hiret by (subst split_r; lia).
                     rewrite -lookup_drop in Hiret. exact (list_elem_of_lookup_2 _ _ _ Hiret). }
                 enough (1 ≤ length (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (take split_r ts)))).
                 { enough (1 ≤ length (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (drop split_r ts))));
                   [lia|]; destruct (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (drop split_r ts)));
                   [clear -Hrt2; set_solver|simpl; lia]. }
                 destruct (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (take split_r ts)));
                   [clear -Hrt1; set_solver|simpl; lia]. }
               subst iret.
               (* i_unc in icall..n. From Hempty_aeap: all icall ≤ j < n are covered. *)
               assert (i_unc = n).
               { destruct (decide (i_unc < n)).
                 - destruct (Hicall_covers i_unc ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
                   exfalso. exact (Hno_cover τ1c τ2c Hinm Hcover).
                 - lia. }
               subst i_unc.
               (* No push_pop_covers at n. But from the Hempty_aeap proof for step n+1,
                  we showed coverage at n using icall_c ≠ n. Re-derive: *)
               assert (icall < n).
               { exact (call_pos_lt_ret_pos _ _ _ _ _ Hwf Hicall_lookup Hlookup). }
               destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm_c & Hcover_c).
               rewrite /push_pop_covers in Hcover_c.
               destruct (ret_of_tag ts τ1c) as [[iret_c [? tret_c]]|] eqn:Hiret_c; [|done].
               destruct (call_of_tag ts τ2c) as [[icall_c [? tcall_c]]|] eqn:Hicall_c; [|done].
               simpl in Hcover_c.
               (* push_pop_covers at n-1: iret_c ≤ n-1 and n-1 ≤ icall_c. *)
               assert (icall_c ≠ n).
               { intros ->.
                 rewrite /call_of_tag list_find_Some /= in Hicall_c.
                 destruct Hicall_c as (Hlookup_call & [-> His_call] & _).
                 rewrite Hlookup in Hlookup_call. injection Hlookup_call as <- <-.
                 by simpl in His_call. }
               (* icall_c ≥ n (from n-1 ≤ icall_c and icall_c ≠ n): icall_c > n.
                  So push_pop_covers at n: iret_c ≤ n ≤ icall_c. *)
               apply (Hno_cover τ1c τ2c Hinm_c).
               rewrite /push_pop_covers Hiret_c Hicall_c /=. lia. }
             { destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ) as (vc & vc' & Hpfx_τ).
               apply prefix_cons_inv_1 in Hprefix₀ as ?. subst hd.
               apply prefix_cons_inv_2 in Hprefix₀.
               pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as ->.
               assert (Hcv_in_ts : (τ, Call v₀) ∈ ts).
               { assert (Hin_head' : (τ, Call v₀) ∈ ts'_head).
                 { apply (list_elem_of_filter_1 (λ x, x.1 = τ)). rewrite Hfilt1. clear. set_solver. }
                 assert (Hin_take' : (τ, Call v₀) ∈ take n ts).
                 { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; by auto|exact Hin_head']. }
                 apply list_elem_of_lookup_1 in Hin_take' as [i Hi].
                 apply lookup_take_Some in Hi as [Hi _].
                 exact (list_elem_of_lookup_2 _ _ _ Hi). }
               apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hcv_in_ts; last done.
               pose proof (elem_of_prefix _ _ _ Hcv_in_ts Hprefix) as Hin_pfx.
               rewrite !elem_of_cons elem_of_nil right_id in Hin_pfx.
               destruct Hin_pfx as [Hin_pfx|Hin_pfx]; last discriminate Hin_pfx.
               injection Hin_pfx as ->.
               enough (v₀' = encode_response IsEmpty) by (subst v₀'; exists []; reflexivity).
               assert (Hlin_in : (τ, Lin (encode_request Pop) v₀') ∈ ts'_head).
               { apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
                 rewrite Hfilt1. clear. set_solver. }
               assert (Hτ_pop_ret : τ ∈ pop_of_trace ts).
               { apply (list_elem_of_fmap_2 fst _ (τ, Call (encode_request Pop))).
                 apply list_elem_of_filter_2; [done|].
                 apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
                 destruct (filter (λ x, x.1 = τ) ts) as [|x_filt xs_filt] eqn:Hfilt_empty.
                 { exfalso. apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin; last done.
                   rewrite Hfilt_empty in Hin. clear -Hin. set_solver. }
                 pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix) as ->. clear. set_solver. }
               pose proof (Hpop_lin_consistent _ _ _ Hτ_pop_ret Hlin_in) as Hcons.
               assert (Hτ_not_m2 : τ ∉ m.*2).
               { eapply pop_empty_not_in_m; [exact Hcomplete|exact Hvalid|exact Hwf| |exact Hprefix].
                 apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
                 destruct (filter (λ x, x.1 = τ) ts) as [|x_filt xs_filt] eqn:Hfilt_e.
                 { exfalso. apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin; last done.
                   rewrite Hfilt_e in Hin. clear -Hin. set_solver. }
                 pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix) as ->. clear. set_solver. }
               rewrite bool_decide_eq_false_2 in Hcons; [exact Hcons|exact Hτ_not_m2]. }
             { exfalso.
               apply prefix_cons_inv_2, prefix_cons_inv_2 in Hprefix₀.
               pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as Hhd3.
               assert (Hret_take : (τ, Ret v₀') ∈ take n ts).
               { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; auto|].
                 apply (list_elem_of_filter_1 (λ x, x.1 = τ)). rewrite Hfilt1 Hhd3. clear. set_solver. }
               apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hret_take as Hrt_f; last done.
               apply (list_elem_of_filter_2 (is_ret∘snd)) in Hrt_f; last done.
               assert (Hrn_f : (τ, Ret (encode_response IsEmpty)) ∈ filter (λ x, x.1 = τ) (drop n ts)).
               { apply list_elem_of_filter_2; [done|].
                 pose proof (drop_S _ _ _ Hlookup) as ->. clear. set_solver. }
               apply (list_elem_of_filter_2 (is_ret∘snd)) in Hrn_f; last done.
               destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ) as (vc & vc' & Hpfx).
               apply (prefix_filter (is_ret∘snd)) in Hpfx.
               rewrite -(take_drop n ts) !filter_app in Hpfx.
               apply prefix_length in Hpfx. rewrite length_app in Hpfx.
               enough (1 ≤ length (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (take n ts)))).
               { enough (1 ≤ length (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (drop n ts)))) by
                 (simpl in Hpfx; lia).
                 destruct (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (drop n ts))).
                 - clear -Hrn_f. set_solver.
                 - simpl. lia. }
               destruct (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ) (take n ts))).
               - clear -Hrt_f. set_solver.
               - simpl. lia. }
          -- exists v₀, v₀'.
             rewrite filter_cons_False; last by simpl; auto.
             rewrite filter_nil right_id. assumption.
        * (* Hlin_sound *)
          rewrite /ts'_head_lin filter_app.
          rewrite filter_cons_False; last by simpl; auto.
          rewrite filter_nil right_id.
          assumption.
        * (* Hval_then_not_pr *)
          intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
          rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
          rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
          rewrite filter_nil right_id in Hτ2_bounded₀ |- *.
          eapply Hval_then_not_pr; eassumption.
        * (* Hstate_of_trace *)
          assert (Hv'_eq: v' = encode_response IsEmpty).
          { pose proof (Hin' := elem_of_prefix _ _ _ Hin_filter_tag Hprefix).
            rewrite !elem_of_cons elem_of_nil right_id in Hin'.
            destruct Hin' as [HFalse | Heq]; first discriminate HFalse.
            by injection Heq. }
          subst v'.
          by rewrite (state_of_trace_ret_pop n τ (IsEmpty) Hwf Hlookup).
        * (* Hempty_as early as possible *)
          assert (Hv'_eq: v' = encode_response IsEmpty).
          { pose proof (Hin' := elem_of_prefix _ _ _ Hin_filter_tag Hprefix).
            rewrite !elem_of_cons elem_of_nil right_id in Hin'.
            destruct Hin' as [HFalse | Heq]; first discriminate HFalse.
            by injection Heq. }
          subst v'.
          intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
          rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
          rewrite filter_nil right_id in Hτ₀_not_lin.
          assert (Hτ₀_pending_old: τ₀ ∈ trace_pendingOp (drop n ts)).
          { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
            rewrite Hdrop_eq.
            apply filter_tag_trace_pendingOp.
            destruct (decide (τ₀ = τ)) as [-> | Hne].
            - rewrite filter_cons_True //.
              apply trace_pendingOp_ret_elem_of.
            - rewrite filter_cons_False //.
              rewrite -filter_tag_trace_pendingOp.
              assumption. }
          destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin) Hτ₀_pop_emp)
            as (icall & Hicall_lookup & Hicall_covers).
          exists icall. split; first assumption.
          intros i Hi.
          destruct (decide (i = n)) as [-> | Hne].
          -- assert (Hn_gt_icall : icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. discriminate. }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              exists τ1c, τ2c. split; [exact Hinm|].
              rewrite /push_pop_covers in Hcover |- *.
              destruct (ret_of_tag ts τ1c) as [[iret_c [? tret]]|] eqn:Hiret; [|done].
              destruct (call_of_tag ts τ2c) as [[icall_c [? tcall]]|] eqn:Hicall_eq; [|done].
              simpl in Hcover |- *.
              split; first lia.
              cut (icall_c ≠ n); first lia.
              intros ->.
              rewrite /call_of_tag list_find_Some /= in Hicall_eq.
              destruct Hicall_eq as (Hlookup_call & [-> His_call] & _).
              rewrite Hlookup in Hlookup_call. injection Hlookup_call as <- <-.
              by simpl in His_call.
          -- apply Hicall_covers. lia.
        * (* Hpush_as late as possible *)
          assert (Hv'_eq: v' = encode_response IsEmpty).
          { pose proof (Hin' := elem_of_prefix _ _ _ Hin_filter_tag Hprefix).
            rewrite !elem_of_cons elem_of_nil right_id in Hin'.
            destruct Hin' as [HFalse | Heq]; first discriminate HFalse.
            by injection Heq. }
          subst v'.
          intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
          rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_lin; last by simpl; auto.
          rewrite filter_nil right_id in Hτ₀_lin.
          assert (Hτ₀_pending_old: τ₀ ∈ trace_pendingOp (drop n ts)).
          { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
            rewrite Hdrop_eq.
            apply filter_tag_trace_pendingOp.
            destruct (decide (τ₀ = τ)) as [-> | Hne].
            - rewrite filter_cons_True //.
              apply trace_pendingOp_ret_elem_of.
            - rewrite filter_cons_False //.
              rewrite -filter_tag_trace_pendingOp.
              assumption. }
          destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin) Hτ₀_push)
            as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
          exists τ2_0. split; first assumption.
          rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
          rewrite filter_nil right_id.
          exact Hτ2_0_lin.
        * (* Hpop as early as possible *)
          intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
          rewrite (take_S_r _ _ _ Hlookup) !filter_app !fmap_app in Hτ1₀_called, Hτ2₀_called.
          rewrite filter_cons_False in Hτ1₀_called; last by simpl; auto.
          rewrite filter_cons_False in Hτ2₀_called; last by simpl; auto.
          rewrite filter_nil fmap_nil right_id in Hτ1₀_called, Hτ2₀_called.
          rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
          rewrite filter_nil right_id.
          exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_called Hτ2₀_called).
        * (* Hpop_lin_consistent *)
          intros τ₀ v₀_c v₀'_c Hτ₀_pop Hin_lin.
          apply elem_of_app in Hin_lin as [Hlin_old | Hlin_new].
          { exact (Hpop_lin_consistent _ _ _ Hτ₀_pop Hlin_old). }
          rewrite elem_of_cons elem_of_nil in Hlin_new.
          destruct Hlin_new as [Habs|[]]. discriminate.
        (**************** End LLM-generated code. *****************)
      + (* Ret Pop NonEmpty *)
        rename τ into τ2.
        pose proof (Hin':= elem_of_prefix _ _ _ Hin_filter_tag Hprefix).
        rewrite !elem_of_cons elem_of_nil right_id in Hin'.
        destruct Hin' as [HFalse | Heq]; first discriminate HFalse.
        injection Heq as Heq.
        subst v'.
        assert (Hτ2_in_m: τ2 ∈ m.*2).
        { destruct Hclosed as [_ Hclosed_pop].
          rewrite Forall_forall in Hclosed_pop.
          opose proof (Hclosed_pop τ2 _) as [?|[HFalse | HFalse]].
          { apply (list_elem_of_fmap_2 fst _ (τ2,Call (encode_request Pop))).
            eapply list_elem_of_filter_2.
            - done.
            - (*************** Begin LLM-generated code. ****************)
              apply (list_elem_of_filter_1 (λ x, x.1 = τ2)).
              destruct (filter (λ x, x.1 = τ2) ts) as [|a l] eqn:Hfilt.
              { exfalso. set_solver. }
              pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix) as Ha. subst a.
              set_solver.
              (**************** End LLM-generated code. *****************) }
          - assumption.
          - exfalso.
            apply (list_elem_of_filter_2 (λ x, x.1=τ2)) in HFalse; last done.
            pose proof (elem_of_prefix _ _ _ HFalse Hprefix) as HFalse'.
            rewrite !elem_of_cons elem_of_nil right_id in HFalse'.
            destruct HFalse'; discriminate.
          - contradict HFalse.
            destruct (Hcomplete τ2) as (v&v'&[Heq|Heq]).
            + rewrite Heq in Hin_filter_tag. clear -Hin_filter_tag. set_solver.
            + apply (list_elem_of_fmap_2 fst _ (τ2,Ret v')).
              apply list_elem_of_filter_2; first done.
              apply (list_elem_of_filter_1 (λ x, x.1=τ2)).
              rewrite Heq.
              set_solver. }
        apply list_elem_of_fmap_1 in Hτ2_in_m.
        destruct Hτ2_in_m as ([τ1 τ2'] & Heqτ2 & Hin_m).
        simpl in Heqτ2. subst τ2'.
        opose proof (valid_match_ne _ _ _ _ _ Hvalid Hin_m) as Hτ1_ne_τ2.
        { apply per_tag_complete_per_tag_wellformed, Hcomplete. }
        exists (ts'_head ++ [(τ2,Ret (encode_response (NonEmpty v_pop)))]), s.
        intros ts'_head_lin. split_and!.
        (*************** Begin LLM-generated code. ****************)
        * (* Hfilter *)
          rewrite filter_app.
          rewrite filter_cons_True; last by simpl; auto.
          rewrite filter_nil.
          rewrite (take_S_r _ _ _ Hlookup).
          f_equal. done.
        * (* Hper_tag_lin *)
          intro τ₀.
          specialize (Hper_tag_lin τ₀) as (v₀ & v₀' & Hprefix₀).
          rewrite filter_app.
          destruct (decide (τ₀ = τ2)) as [-> | Hτ₀_ne_τ2].
          --
             exists (encode_request Pop), (encode_response (NonEmpty v_pop)).
             rewrite filter_cons_True //.
             rewrite filter_nil.
             destruct (filter (λ x, x.1 = τ2) ts'_head) as [|hd [|hd2 [|hd3 rest3]]] eqn:Hfilt1.
             { exfalso.
               destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ2) as (vc & vc' & Hpfx_τ2).
               rewrite -(take_drop n ts) filter_app Hfilter list_filter_comm Hfilt1 left_id in Hpfx_τ2.
               pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
               rewrite Hdrop_eq filter_cons_True // in Hpfx_τ2.
               apply prefix_cons_inv_1 in Hpfx_τ2. discriminate. }
             { (* Singleton: τ2 NOT linearized. Use Hpop_aeap to derive contradiction. *)
               exfalso.
               (* τ1 ∈ call_tags(take n ts): from valid_match, τ1 has Call Push ∈ ts.
                  The Call must be before n (since per_tag_wellformed: Call before Ret). *)
               assert (Hτ1_called : τ1 ∈ (filter (is_call ∘ snd) (take n ts)).*1).
               { destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [vp Hcp].
                 apply (list_elem_of_fmap_2 fst _ (τ1, Call (encode_request (Push vp)))).
                 apply list_elem_of_filter_2; [done|].
                 (* Call Push ∈ ts. Position < n because Ret at n and per_tag_wellformed says Call first. *)
                 apply list_elem_of_lookup_1 in Hcp as [j Hj].
                 assert (j < n).
                 { assert (j ≠ n) by (intros ->; rewrite Hlookup in Hj; discriminate).
                   assert (j < length ts) by (eapply lookup_lt_Some; eauto).
                   destruct (decide (j < n)); [lia|exfalso].
                   (* j > n: τ1's Call Push at j, τ2's Ret NonEmpty at n. Use filter order. *)
                   destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ1) as (vc & vc' & Hpfx_τ1).
                   rewrite -(take_drop n ts) filter_app in Hpfx_τ1.
                   pose proof (matched_push_call_le_pop_ret _ _ _ _ _ _ Hcomplete Hvalid Hwf Hin_m Hj Hlookup). lia. }
                 eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hj|lia]. }
               (* τ2 ∈ call_tags(take n ts): τ2's Call Pop is in take n ts (before Ret at n) *)
               assert (Hτ2_called : τ2 ∈ (filter (is_call ∘ snd) (take n ts)).*1).
               { apply (list_elem_of_fmap_2 fst _ (τ2, Call (encode_request Pop))).
                 apply list_elem_of_filter_2; [done|].
                 pose proof (valid_match_call_pop ts m τ1 τ2 Hvalid Hin_m) as Hcp2.
                 apply list_elem_of_lookup_1 in Hcp2 as [k Hk].
                 assert (k < n).
                 { exact (call_pos_lt_ret_pos _ _ _ _ _ Hwf Hk Hlookup). }
                 eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hk|lia]. }
               (* By Hpop_aeap: τ2 ∈ lin_tags(ts'_head) *)
               pose proof (Hpop_aeap _ _ Hin_m Hτ1_called Hτ2_called) as Hτ2_lin.
               (* τ2 ∈ lin_tags means Lin event for τ2 in ts'_head *)
               apply list_elem_of_fmap_1 in Hτ2_lin as ([τ2' ev_lin] & Heq_τ2' & Hin_lin).
               simpl in Heq_τ2'. subst τ2'.
               apply list_elem_of_filter in Hin_lin as [His_lin Hin_lin].
               apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hin_lin; last done.
               pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as Hhd_eq. subst hd.
               rewrite Hfilt1 elem_of_cons elem_of_nil in Hin_lin.
               destruct Hin_lin as [Hin_lin|[]].
               injection Hin_lin as Hin_lin. subst ev_lin.
               by simpl in His_lin. }
             { apply prefix_cons_inv_1 in Hprefix₀ as ?. subst hd.
               apply prefix_cons_inv_2 in Hprefix₀.
               pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as ->.
               assert (Hcv_in_ts : (τ2, Call v₀) ∈ ts).
               { assert (Hin_head' : (τ2, Call v₀) ∈ ts'_head).
                 { apply (list_elem_of_filter_1 (λ x, x.1 = τ2)). rewrite Hfilt1. clear. set_solver. }
                 assert (Hin_take' : (τ2, Call v₀) ∈ take n ts).
                 { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; by auto|exact Hin_head']. }
                 apply list_elem_of_lookup_1 in Hin_take' as [i Hi].
                 apply lookup_take_Some in Hi as [Hi _].
                 exact (list_elem_of_lookup_2 _ _ _ Hi). }
               apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hcv_in_ts; last done.
               pose proof (elem_of_prefix _ _ _ Hcv_in_ts Hprefix) as Hin_pfx.
               rewrite !elem_of_cons elem_of_nil right_id in Hin_pfx.
               destruct Hin_pfx as [Hin_pfx|Hin_pfx]; last discriminate Hin_pfx.
               injection Hin_pfx as ->.
               enough (v₀' = encode_response (NonEmpty v_pop)) by (subst v₀'; exists []; reflexivity).
               assert (Hlin_in : (τ2, Lin (encode_request Pop) v₀') ∈ ts'_head).
               { apply (list_elem_of_filter_1 (λ x, x.1 = τ2)).
                 rewrite Hfilt1. clear. set_solver. }
               assert (Hτ2_pop : τ2 ∈ pop_of_trace ts).
               { apply (list_elem_of_fmap_2 fst _ (τ2, Call (encode_request Pop))).
                 apply list_elem_of_filter_2; [done|].
                 apply (list_elem_of_filter_1 (λ x, x.1 = τ2)).
                 destruct (filter (λ x, x.1 = τ2) ts) as [|x xs] eqn:Hfilt_empty.
                 { exfalso. clear -Hin_filter_tag Hfilt_empty. set_solver. }
                 pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix) as ->. clear. set_solver. }
               pose proof (Hpop_lin_consistent _ _ _ Hτ2_pop Hlin_in) as Hcons.
               assert (Hτ2_m2 : τ2 ∈ m.*2).
               { apply (list_elem_of_fmap_2 snd _ (τ1, τ2)). exact Hin_m. }
               rewrite bool_decide_eq_true_2 in Hcons; last exact Hτ2_m2.
               destruct Hcons as (τ1' & v_pop' & Hin_m' & Hcall_push' & Hv_eq).
               subst v₀'.
               (* v_pop' = v_pop: τ1' matched to τ2, so τ1' = τ1 (by NoDup m.*2).
                  Then (τ1, Call (Push v_pop')) ∈ ts. Per_tag_wellformed for τ1 says
                  the push value is unique, so v_pop' = v_pop. *)
               assert (Hτ1'_eq : τ1' = τ1) by (by eapply valid_match_inj_call). subst τ1'.
               f_equal.
               (* Both (τ1, Call (Push v_pop')) and v_pop is the Ret value of τ2.
                  From valid_match: push value = pop return value. So v_pop' = v_pop. *)
               destruct (Hwf τ1) as [(vc1 & _ & Hpfx_τ1) | (vc1 & _ & Hpfx_τ1)].
               ** apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_push'; last done.
                  pose proof (elem_of_prefix _ _ _ Hcall_push' Hpfx_τ1) as Hin1.
                  rewrite !elem_of_cons !elem_of_nil in Hin1.
                  destruct Hin1 as [Hin1|[Hin1|[]]]; last by (apply (f_equal snd) in Hin1; simpl in Hin1).
                  revert Hin1. intros [= ->].
                  (* vc1 = v_pop: from valid_match, push and pop values match *)
                  destruct Hvalid as (_ & _ & Hforall_vm). rewrite Forall_forall in Hforall_vm.
                  destruct (Hforall_vm _ Hin_m) as (_ & _ & v_m & Hcall_m & [Hret_m | Hno_ret]).
                  --- apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_m; last done.
                      pose proof (elem_of_prefix _ _ _ Hcall_m Hpfx_τ1) as Hin2.
                      rewrite !elem_of_cons !elem_of_nil in Hin2.
                      destruct Hin2 as [Hin2|[Hin2|[]]]; last by (apply (f_equal snd) in Hin2; simpl in Hin2).
                      revert Hin2. intros [= ->].
                      apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hret_m; last done.
                      pose proof (elem_of_prefix _ _ _ Hret_m Hprefix) as Hin3.
                      rewrite !elem_of_cons !elem_of_nil right_id in Hin3.
                      destruct Hin3 as [Hin3|Hin3]; first discriminate.
                      by simplify_eq.
                  --- exfalso. apply Hno_ret.
                      destruct (Hcomplete τ2) as (vc2 & vc2' & [Hfilt_empty2|Hfilt_eq2]).
                      { pose proof (valid_match_call_pop ts m τ1 τ2 Hvalid Hin_m) as Hcp2.
                        apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hcp2; last done.
                        rewrite Hfilt_empty2 in Hcp2. clear -Hcp2. set_solver. }
                      apply (list_elem_of_fmap_2 fst _ (τ2, Ret vc2')).
                      apply list_elem_of_filter_2; [simpl; eexists; done|].
                      apply (list_elem_of_filter_1 (λ x, x.1 = τ2)). rewrite Hfilt_eq2. clear. set_solver.
               ** exfalso.
                  apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_push'; last done.
                  pose proof (elem_of_prefix _ _ _ Hcall_push' Hpfx_τ1) as Hin1.
                  rewrite !elem_of_cons !elem_of_nil in Hin1.
                  destruct Hin1 as [Hin1|[Hin1|[]]]; apply (f_equal snd) in Hin1; by simpl in Hin1. }
             { exfalso.
               apply prefix_cons_inv_2, prefix_cons_inv_2 in Hprefix₀.
               pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix₀) as Hhd3.
               assert (Hret_take : (τ2, Ret v₀') ∈ take n ts).
               { rewrite Hfilter. apply list_elem_of_filter_2; [simpl; auto|].
                 apply (list_elem_of_filter_1 (λ x, x.1 = τ2)). rewrite Hfilt1 Hhd3. clear. set_solver. }
               apply (list_elem_of_filter_2 (λ x, x.1 = τ2)) in Hret_take as Hrt_f; last done.
               apply (list_elem_of_filter_2 (is_ret∘snd)) in Hrt_f; last done.
               assert (Hrn_f : (τ2, Ret (encode_response (NonEmpty v_pop))) ∈ filter (λ x, x.1 = τ2) (drop n ts)).
               { apply list_elem_of_filter_2; [done|].
                 pose proof (drop_S _ _ _ Hlookup) as ->. clear. set_solver. }
               apply (list_elem_of_filter_2 (is_ret∘snd)) in Hrn_f; last done.
               destruct (per_tag_wellformed_bag_wellformed _ _ _ Hwf τ2) as (vc & vc' & Hpfx).
               apply (prefix_filter (is_ret∘snd)) in Hpfx.
               rewrite -(take_drop n ts) !filter_app in Hpfx.
               apply prefix_length in Hpfx. rewrite length_app in Hpfx.
               enough (1 ≤ length (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ2) (take n ts)))).
               { enough (1 ≤ length (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ2) (drop n ts)))) by
                 (simpl in Hpfx; lia).
                 destruct (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ2) (drop n ts))).
                 - clear -Hrn_f. set_solver.
                 - simpl. lia. }
               destruct (filter (is_ret ∘ snd) (filter (λ x, x.1 = τ2) (take n ts))).
               - clear -Hrt_f. set_solver.
               - simpl. lia. }
          -- exists v₀, v₀'.
             rewrite filter_cons_False; last by simpl; auto.
             rewrite filter_nil right_id. assumption.
        * (* Hlin_sound *)
          rewrite /ts'_head_lin filter_app.
          rewrite filter_cons_False; last by simpl; auto.
          rewrite filter_nil right_id.
          assumption.
        * (* Hval_then_not_pr *)
          intros τ1₀ τ2₀ Hin_m₀ Hτ2_bounded₀.
          rewrite /ts'_head_lin filter_app in Hτ2_bounded₀ |- *.
          rewrite filter_cons_False in Hτ2_bounded₀ |- *; try by simpl; auto.
          rewrite filter_nil right_id in Hτ2_bounded₀ |- *.
          eapply Hval_then_not_pr; eassumption.
        * (* Hstate_of_trace *)
          by rewrite (state_of_trace_ret_pop n τ2 (NonEmpty v_pop) Hwf Hlookup).
        * (* Hempty_as early as possible *)
          intros τ₀ [Hτ₀_pending Hτ₀_not_lin] Hτ₀_pop_emp.
          rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_not_lin; last by simpl; auto.
          rewrite filter_nil right_id in Hτ₀_not_lin.
          assert (Hτ₀_pending_old: τ₀ ∈ trace_pendingOp (drop n ts)).
          { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
            rewrite Hdrop_eq.
            apply filter_tag_trace_pendingOp.
            destruct (decide (τ₀ = τ2)) as [-> | Hne].
            - rewrite filter_cons_True //.
              apply trace_pendingOp_ret_elem_of.
            - rewrite filter_cons_False //.
              rewrite -filter_tag_trace_pendingOp.
              assumption. }
          destruct (Hempty_aeap τ₀ (conj Hτ₀_pending_old Hτ₀_not_lin) Hτ₀_pop_emp)
            as (icall & Hicall_lookup & Hicall_covers).
          exists icall. split; first assumption.
          intros i Hi.
          destruct (decide (i = n)) as [-> | Hne].
          -- assert (Hn_gt_icall : icall < n).
              { destruct (decide (icall = n)) as [->|]; [|lia].
                rewrite Hlookup in Hicall_lookup. discriminate. }
              destruct (Hicall_covers (n-1) ltac:(lia)) as (τ1c & τ2c & Hinm & Hcover).
              exists τ1c, τ2c. split; [exact Hinm|].
              rewrite /push_pop_covers in Hcover |- *.
              destruct (ret_of_tag ts τ1c) as [[iret_c [? tret]]|] eqn:Hiret; [|done].
              destruct (call_of_tag ts τ2c) as [[icall_c [? tcall]]|] eqn:Hicall_eq; [|done].
              simpl in Hcover |- *.
              split; first lia.
              cut (icall_c ≠ n); first lia.
              intros ->.
              rewrite /call_of_tag list_find_Some /= in Hicall_eq.
              destruct Hicall_eq as (Hlookup_call & [-> His_call] & _).
              rewrite Hlookup in Hlookup_call. injection Hlookup_call as <- <-.
              by simpl in His_call.
          -- apply Hicall_covers. lia.
        * (* Hpush_as late as possible *)
          intros τ₀ [Hτ₀_pending Hτ₀_lin] Hτ₀_push.
          rewrite /ts'_head_lin filter_app filter_cons_False in Hτ₀_lin; last by simpl; auto.
          rewrite filter_nil right_id in Hτ₀_lin.
          assert (Hτ₀_pending_old: τ₀ ∈ trace_pendingOp (drop n ts)).
          { pose proof (drop_S _ _ _ Hlookup) as Hdrop_eq.
            rewrite Hdrop_eq.
            apply filter_tag_trace_pendingOp.
            destruct (decide (τ₀ = τ2)) as [-> | Hne].
            - rewrite filter_cons_True //.
              apply trace_pendingOp_ret_elem_of.
            - rewrite filter_cons_False //.
              rewrite -filter_tag_trace_pendingOp.
              assumption. }
          destruct (Hpush_alap τ₀ (conj Hτ₀_pending_old Hτ₀_lin) Hτ₀_push)
            as (τ2_0 & Hin_m₀ & Hτ2_0_lin).
          exists τ2_0. split; first assumption.
          rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
          rewrite filter_nil right_id.
          exact Hτ2_0_lin.
        * (* Hpop as early as possible *)
          intros τ1₀ τ2₀ Hin_m₀ Hτ1₀_called Hτ2₀_called.
          rewrite (take_S_r _ _ _ Hlookup) !filter_app !fmap_app in Hτ1₀_called, Hτ2₀_called.
          rewrite filter_cons_False in Hτ1₀_called; last by simpl; auto.
          rewrite filter_cons_False in Hτ2₀_called; last by simpl; auto.
          rewrite filter_nil fmap_nil right_id in Hτ1₀_called, Hτ2₀_called.
          rewrite /ts'_head_lin filter_app filter_cons_False; last by simpl; auto.
          rewrite filter_nil right_id.
          exact (Hpop_aeap _ _ Hin_m₀ Hτ1₀_called Hτ2₀_called).
        * (* Hpop_lin_consistent *)
          intros τ₀ v₀_c v₀'_c Hτ₀_pop Hin_lin.
          apply elem_of_app in Hin_lin as [Hlin_old | Hlin_new].
          { exact (Hpop_lin_consistent _ _ _ Hτ₀_pop Hlin_old). }
          rewrite elem_of_cons elem_of_nil in Hlin_new.
          destruct Hlin_new as [Habs|[]]. discriminate.
        (**************** End LLM-generated code. *****************)
  Qed.

  Local Lemma τ_in_filter_lin ts' τ :
    ts = filter (not ∘ is_lin ∘ snd) ts' →
    per_tag_linearized ts' →
    τ ∈ ts.*1 →
    τ ∈ (filter (is_lin ∘ snd) ts').*1.
  Proof.
    intros Hfilter Hper_tag_lin Hin.
    destruct (Hcomplete τ) as (v&v'&[HFalse|Heq]).
    { exfalso.
      destruct (list_elem_of_fmap_1 fst ts τ Hin) as ([τ' t] & Heq & Hin').
      simpl in Heq. subst τ'. clear Hin.
      assert (Hin_filter_tag: (τ,t) ∈ filter (λ x, x.1 = τ) ts).
      { by rewrite list_elem_of_filter. }
      rewrite HFalse in Hin_filter_tag. set_solver. }
    (* rewrite Heq in Hin_filter_tag.
    rewrite !elem_of_cons elem_of_nil right_id in Hin_filter_tag. *)
    destruct (Hper_tag_lin τ) as (v_&v'_&[l Heq']).

    (* show that filter (not ∘ is_lin ∘ snd) l = nil *)
    rewrite Hfilter list_filter_comm in Heq.
    apply (f_equal (filter (not∘is_lin∘snd))) in Heq' as Heq''.
    rewrite filter_app Heq in Heq''.
    rewrite filter_cons_True in Heq''; last by simpl; auto.
    rewrite filter_cons_False in Heq''; last by simpl; auto.
    rewrite filter_cons_True in Heq''; last by simpl; auto.
    rewrite filter_nil in Heq''.
    rewrite -(right_id_L [] (++) [(τ, Call v_); (τ, Ret v'_)]) in Heq''.
    apply app_inj_1 in Heq'' as [Heq''1 Heq''2]; last done.
    injection  Heq''1 as -> ->.

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

    (* now we know (τ,Lin v v') ∈ ts' *)
    assert (Hin': (τ,Lin v v') ∈ ts').
    { apply (list_elem_of_filter_1 (λ t, t.1 = τ)).
      rewrite -Heq'. set_solver. }
    change (τ) with (τ,Lin v v').1.
    apply list_elem_of_fmap_2.
    apply list_elem_of_filter_2; done.
  Qed.

  Lemma trace_linearizable_bag_destruct :
    per_tag_wellformed_bag rme valid_value ts →
    per_tag_pop_empty_sound ts m →
    ∃ ts',
      ts = filter (not ∘ is_lin ∘ snd) ts'
    ∧ per_tag_linearized ts'
    ∧ (∃ s', linearized_sound (M:=bag_model rme valid_value) (filter (is_lin ∘ snd) ts') s_init s')
    ∧ (∀ τ1 τ2, (τ1,τ2) ∈ m → [τ1;τ2] `sublist_of` (filter (is_lin ∘ snd) ts').*1).
  Proof.
    intros Hwf Hempty_sound.
    destruct (trace_linearizable_bag_destruct_ind (length ts) Hwf Hempty_sound)
      as (ts' & s' & Hfilter & Hper_tag_lin & Hlin_sound & Hval_then_not_pr & _).
    rewrite !take_ge // in Hfilter, Hval_then_not_pr.
    exists ts'.
    split_and!; try assumption.
    - exists s'. done.
    - intros τ1 τ2 Hin. apply Hval_then_not_pr; first assumption.
      + apply τ_in_filter_lin; try assumption.
        eapply (list_elem_of_fmap_2 fst _ (τ2,_)).
        eapply valid_match_call_pop; eassumption.
  Qed.
End proof.
