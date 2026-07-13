From stdpp Require Import finite.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.bag Require Import base linear_points.
From iris_logatom.pure_logic.aspect.queue Require Import ext.abstract_queue base.

(* FIXME: inline these two very simply lemmas. *)
Local Lemma list_filter_lookup_pred {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (i : nat) (x : A) :
  filter P l !! i = Some x → P x.
Proof. by intros [??]%list_elem_of_lookup_2%list_elem_of_filter. Qed.
Local Lemma list_filter_lookup_orig {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (i : nat) (x : A) :
  filter P l !! i = Some x → x ∈ l.
Proof. by intros [??]%list_elem_of_lookup_2%list_elem_of_filter. Qed.

(* FIXME: move to elsewhere *)
Local Lemma filter_NoDup_at {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (x : A) (i j : nat) :
  filter P l !! i = Some x → filter P l !! j = Some x → P x →
  (∀ i' j', l !! i' = Some x → l !! j' = Some x → i' = j') →
  i = j.
Proof.
  revert i j. induction l as [|a l IH]; intros i j Hi Hj HP Huniq.
  { rewrite filter_nil in Hi. done. }
  destruct (decide (P a)) as [HPa|HnPa].
  - rewrite filter_cons_True // in Hi, Hj.
    destruct i as [|i'], j as [|j']; simpl in Hi, Hj; [done| | |].
    + (* i=0, j=S j': a=x. x in filter P l at j'. x ∈ l at some position k.
         Huniq: (a::l) !! 0 = Some x and (a::l) !! (S k) = Some x → 0 = S k. ⊥ *)
      simplify_eq.
      assert (Hin : x ∈ l).
      { eapply list_elem_of_filter_1, list_elem_of_lookup_2. exact Hj. }
      apply list_elem_of_lookup_1 in Hin as [k_pos Hk_pos].
      enough (0 = Datatypes.S k_pos) by lia. apply Huniq; [done|exact Hk_pos].
    + simplify_eq.
      assert (Hin : x ∈ l).
      { eapply list_elem_of_filter_1, list_elem_of_lookup_2. exact Hi. }
      apply list_elem_of_lookup_1 in Hin as [k_pos Hk_pos].
      enough (Datatypes.S k_pos = 0) by lia. apply Huniq; [exact Hk_pos|done].
    + f_equal. eapply IH; [exact Hi|exact Hj|exact HP|].
      intros i'' j'' Hi'' Hj''.
      assert (Datatypes.S i'' = Datatypes.S j'') by (apply Huniq; done). lia.
  - rewrite filter_cons_False // in Hi, Hj.
    eapply IH; [exact Hi|exact Hj|exact HP|].
    intros i'' j'' Hi'' Hj''.
    assert (Datatypes.S i'' = Datatypes.S j'') by (apply Huniq; done). lia.
Qed.

(* FIXME: move to elsewhere *)
Local Lemma filter_at_most_once {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (x : A) :
  P x →
  (∀ k1 k2, filter P l !! k1 = Some x → filter P l !! k2 = Some x → k1 = k2) →
  ∀ i j, l !! i = Some x → l !! j = Some x → i = j.
Proof.
  intros HP Hfuniq. induction l as [|a l IH]; intros i j Hi Hj.
  { done. }
  destruct (decide (P a)) as [HPa|HnPa].
  - destruct i as [|i'], j as [|j']; simpl in Hi, Hj; [done| | |].
    + simplify_eq. exfalso.
      assert (Hin : x ∈ filter P l).
      { apply list_elem_of_filter_2; [exact HP|]. eapply list_elem_of_lookup_2. exact Hj. }
      apply list_elem_of_lookup_1 in Hin as [k_filt Hk_filt].
      enough (Datatypes.S k_filt = (0:nat)) by discriminate.
      apply (Hfuniq (Datatypes.S k_filt) 0);
        rewrite filter_cons_True; try exact HP; done.
    + simplify_eq. exfalso.
      assert (Hin : x ∈ filter P l).
      { apply list_elem_of_filter_2; [exact HP|]. eapply list_elem_of_lookup_2. exact Hi. }
      apply list_elem_of_lookup_1 in Hin as [k_filt Hk_filt].
      enough ((0:nat) = Datatypes.S k_filt) by discriminate.
      apply (Hfuniq 0 (Datatypes.S k_filt));
        rewrite filter_cons_True; try exact HP; done.
    + f_equal. eapply IH; [|exact Hi|exact Hj].
      intros k1 k2 Hk1 Hk2.
      enough (Datatypes.S k1 = Datatypes.S k2) by lia.
      apply (Hfuniq (Datatypes.S k1) (Datatypes.S k2));
        rewrite filter_cons_True; try exact HP; done.
  - destruct i as [|i'], j as [|j']; simpl in Hi, Hj; [done| | |].
    + simplify_eq. exfalso. apply HnPa. exact HP.
    + simplify_eq. exfalso. apply HnPa. exact HP.
    + f_equal. eapply IH; [|exact Hi|exact Hj].
      intros k1 k2 Hk1 Hk2.
      apply Hfuniq; rewrite filter_cons_False //.
Qed.

(* FIXME: move to elsewhere *)
Local Lemma NoDup_split_unique {A} (l l1 l2 l1' l2' : list A) (x : A) :
  NoDup l → l = l1 ++ x :: l2 → l = l1' ++ x :: l2' →
  x ∉ l1 → x ∉ l1' → l1 = l1'.
Proof.
  intros Hnd Heq1 Heq2 Hnotin1 Hnotin2.
  (* x at position |l1| in l and position |l1'| in l. NoDup → |l1| = |l1'|. *)
  assert (Hlen_eq : length l1 = length l1').
  { assert (Hpos1 : l !! length l1 = Some x).
    { rewrite Heq1 lookup_app_r // Nat.sub_diag //. }
    assert (Hpos2 : l !! length l1' = Some x).
    { rewrite Heq2 lookup_app_r // Nat.sub_diag //. }
    eapply NoDup_lookup; eassumption. }
  subst l. apply app_inj_1 in Heq2 as [? _]; [done|lia].
Qed.

Section proof.
  Variables (rme : response_mayempty) (valid_value : val → Prop) (ts : list (positive * trace)) (m : list (positive*positive)).
  Hypothesis Hvalid : valid_match ts m.
  Hypothesis Hcomplete : per_tag_complete ts.
  Hypothesis Hclosed : closed_match ts m.

  Local Instance trace_operation_eq_dec :
    EqDecision { τ: positive | τ ∈ events_of_trace ts }.
  Proof. solve_decision. Defined.

  Local Program Instance trace_operation_finite :
    Finite { τ: positive | τ ∈ events_of_trace ts } :=
    {| enum := list_filter_sig (λ τ, τ ∈ events_of_trace ts)
                                (elements (events_of_trace ts)) |}.
  Next Obligation.
    apply (NoDup_fmap_1 proj1_sig).
    rewrite list_filter_sig_filter.
    apply NoDup_filter, NoDup_elements.
  Qed.
  Next Obligation.
    intros [τ Hτ]. apply (list_elem_of_fmap_inj proj1_sig).
    rewrite list_filter_sig_filter.
    rewrite list_elem_of_filter.
    split; [done | by apply elem_of_elements].
  Qed.

  Local Instance trace_queue_model : abstract_queue_model := {|
    operation := { τ: positive | τ ∈ events_of_trace ts };
    operation_eq_dec := trace_operation_eq_dec;
    operation_finite := trace_operation_finite;
  |}.

  Definition trace_pre : relation operation :=
    λ op1 op2, pre_of_trace ts (`op1) (`op2).

  Definition trace_prt ts' : relation operation :=
    λ op1 op2, prt_of_trace ts' (`op1) (`op2).

  Definition trace_val : relation operation :=
    λ op1 op2, (`op1, `op2) ∈ m.

  Definition trace_empty : operation → Prop :=
    λ op, empty_of_trace_match ts m (`op).

   Local Lemma call_ret_le {call ret x y τ} :
    call_of_tag ts τ = Some (call, x) →
    ret_of_tag ts τ = Some (ret, y) →
    call < ret.
  Proof.
    intros Hcall Hret.
    destruct x as [τ_call t_call].
    destruct y as [τ_ret t_ret].
    destruct (decide (call < ret)) as [|HFalse]; first lia.
    exfalso.
    rewrite /call_of_tag list_find_Some in Hcall.
    destruct Hcall as (Hlookup_call & [Heq His_call] & _).
    simpl in Heq, His_call. subst τ_call.
    destruct t_call as [v| |]; simpl in His_call; [|done..].
    rewrite /ret_of_tag list_find_Some in Hret.
    destruct Hret as (Hlookup_ret & [Heq His_ret] & _).
    simpl in Heq, His_ret. subst τ_ret.
    destruct t_ret as [| |v']; simpl in His_ret; [done..|].
    destruct (decide (call = ret)) as [->|Hne].
    { rewrite Hlookup_call in Hlookup_ret. discriminate. }

    (* [filter (λ x, x.1 = τ2) ts] should be [(τ, Call _); (τ, Ret _)] *)
    destruct (Hcomplete τ) as (v0 & v0' & [Heq|Heq]).
    { apply list_elem_of_lookup_2 in Hlookup_call.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hlookup_call; last done.
      rewrite Heq in Hlookup_call.
      set_solver. }

    (* but [filter (λ x, x.1 = τ) ts] is [(τ, Ret _); (τ, Ret _)] by ret < call *)
    pose proof (Heq_ts := take_drop_middle _ _ _ Hlookup_call). apply eq_comm in Heq_ts.
    rewrite -(lookup_take_lt _ call) in Hlookup_ret; last lia.
    destruct (list_elem_of_split_length _ _ _ Hlookup_ret) as (l1 & l2 & Heq_ret & _).
    rewrite Heq_ret in Heq_ts.
    rewrite -assoc in Heq_ts.
    apply (f_equal (filter (λ x, x.1 = τ))) in Heq_ts.
    rewrite !filter_app !filter_cons_True // in Heq_ts.

    (* derive contradiction *)
    rewrite Heq_ts in Heq.
    destruct (filter (λ x, x.1 = τ) l1); last first.
    { apply (f_equal length) in Heq.
      rewrite !length_app !length_cons length_nil in Heq. lia. }
    rewrite left_id in Heq.
    destruct (filter (λ x, x.1 = τ) l2); last first.
    { apply (f_equal length) in Heq.
      rewrite !length_app !length_cons length_nil in Heq. lia. }
    destruct (filter (λ x, x.1 = τ) (drop _ ts)); last first.
    { apply (f_equal length) in Heq.
      rewrite !length_app !length_cons length_nil in Heq. lia. }
    discriminate.
  Qed.


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
    - (* decidable *)
      intros [τ1 ?] [τ2 ?]. unfold trace_pre. simpl.
      destruct (decide (pre_of_trace ts τ1 τ2)); [by left | by right].
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
    - (* decidable *)
      intros [τ1 ?] [τ2 ?]. unfold trace_prt. simpl.
      destruct (decide (prt_of_trace ts' τ1 τ2)); [by left | by right].
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

  Lemma enqueue_once_trace_val : enqueue_once trace_val.
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

  Lemma dequeue_once_trace_val : dequeue_once trace_val.
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
      destruct (Hcomplete ia) as (?&?&[Heq|Heq]).
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
      destruct (Hcomplete ra) as (?&?&[Heq|Heq]).
      { rewrite Heq in Hra_call. set_solver. }
      rewrite Heq in Hra_call, Hra_ret.
      rewrite !elem_of_cons !elem_of_nil !right_id in Hra_call, Hra_ret.
      destruct Hra_call as [Hra_call|]; last discriminate.
      destruct Hra_ret as [Hra_ret|]; last discriminate.
      simplify_eq.
  Qed.

  Lemma all_dequeued_or_empty_trace_val_trace_empty :
    per_tag_wellformed_bag rme valid_value ts →
    all_dequeued_or_empty trace_val trace_empty.
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
    destruct (Hcomplete ia) as (?&?&[Heq|Heq]).
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
    destruct (Hptl τ') as (w & w' & Hprefix).
    pose proof (elem_of_prefix _ _ _ Hin_i Hprefix) as H1.
    pose proof (elem_of_prefix _ _ _ Hin_j Hprefix) as H2.
    rewrite !elem_of_cons !elem_of_nil !right_id in H1, H2.
    (* Both must be the Lin element — Call and Ret fail is_lin *)
    assert (Heq_i : ev_i = Lin w w').
    { destruct H1 as [H1|[H1|H1]]; apply (f_equal snd) in H1; simpl in H1; subst;
        try done; simpl in Hlin_i; done. }
    assert (Heq_j : ev_j = Lin w w').
    { destruct H2 as [H2|[H2|H2]]; apply (f_equal snd) in H2; simpl in H2; subst;
        try done; simpl in Hlin_j; done. }
    subst ev_i ev_j.
    eapply (filter_NoDup_at (is_lin ∘ snd) ts'₀ _ i j Hfi Hfj Hlin_i).
    intros i' j' Hi' Hj'.
    assert (Hi'_filt : (τ', Lin w w') ∈ filter (λ x, x.1 = τ') ts'₀).
    { apply list_elem_of_filter_2; [done|]. eapply list_elem_of_lookup_2. exact Hi'. }
    assert (Hj'_filt : (τ', Lin w w') ∈ filter (λ x, x.1 = τ') ts'₀).
    { apply list_elem_of_filter_2; [done|]. eapply list_elem_of_lookup_2. exact Hj'. }
    eapply (filter_at_most_once (λ x, x.1 = τ') ts'₀ (τ', Lin w w') eq_refl).
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
    omap (λ '(_, ev), match ev with Lin (InjLV _) (InjRV v) => Some v | _ => None end) lts.
  Local Definition bag_push_vals (lts : list (positive * trace)) : list val :=
    omap (λ '(_, ev), match ev with Lin (InjRV v) (LitV LitUnit) => Some v | _ => None end) lts.

  Local Lemma bag_pop_ne_vals_app l1 l2 :
    bag_pop_ne_vals (l1 ++ l2) = bag_pop_ne_vals l1 ++ bag_pop_ne_vals l2.
  Proof. clear. apply omap_app. Qed.
  Local Lemma bag_push_vals_app l1 l2 :
    bag_push_vals (l1 ++ l2) = bag_push_vals l1 ++ bag_push_vals l2.
  Proof. clear. apply omap_app. Qed.
  Local Lemma bag_push_vals_push τ w :
    bag_push_vals [(τ, Lin (SOMEV w) (#()))] = [w].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_pop_ne_vals_push τ w :
    bag_pop_ne_vals [(τ, Lin (SOMEV w) (#()))] = [].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_push_vals_pop_empty τ :
    bag_push_vals [(τ, Lin NONEV NONEV)] = [].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_pop_ne_vals_pop_empty τ :
    bag_pop_ne_vals [(τ, Lin NONEV NONEV)] = [].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_push_vals_pop_ne τ w :
    bag_push_vals [(τ, Lin NONEV (SOMEV w))] = [].
  Proof. clear. reflexivity. Qed.
  Local Lemma bag_pop_ne_vals_pop_ne τ w :
    bag_pop_ne_vals [(τ, Lin NONEV (SOMEV w))] = [w].
  Proof. clear. reflexivity. Qed.

  (* Size balance for linearized_sound on the bag model:
     size s' + #pops = size s + #pushes. *)
  Local Lemma linearized_sound_bag_size_balance
    (lts : list (positive * trace)) (s s' : gmultiset val) :
    linearized_sound (M:=bag_model rme valid_value) lts s s' →
    size s' + length (bag_pop_ne_vals lts) = size s + length (bag_push_vals lts).
  Proof.
    clear.
    induction 1 as [s|s0 s s' τ v v' ts Hls IH Hvr Hrr].
    - simpl. lia.
    - change (@linear.S (bag_model rme valid_value)) with (gmultiset val) in *.
      destruct Hrr as (r & Heq_req & Hrr).
      destruct r as [w|].
      + (* Push w *)
        destruct Hrr as [-> ->]. simpl in Heq_req. subst v.
        rewrite bag_pop_ne_vals_app bag_push_vals_app
                bag_pop_ne_vals_push bag_push_vals_push !length_app length_cons length_nil.
        rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
      + (* Pop *)
        simpl in Heq_req. subst v.
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
    (∀ τ, τ ∈ tags → ∃ v, (τ, Lin (InjRV v) (LitV LitUnit)) ∈ l) →
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
    (∀ τ, τ ∈ tags → ∃ w, (τ, Lin NONEV (SOMEV w)) ∈ l) →
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
    (∀ τ v w, (τ, Lin (InjLV v) (InjRV w)) ∈ l → τ ∈ tags) →
    length (bag_pop_ne_vals l) ≤ length tags.
  Proof.
    clear. revert tags. induction l as [|[τ0 ev0] rest IH]; intros tags Hnd_l Hnd_tags Htags.
    - simpl. lia.
    - rewrite fmap_cons in Hnd_l.
      apply NoDup_cons in Hnd_l as [Hnotin Hnd_rest].
      rewrite (_ : (τ0, ev0) :: rest = [(τ0, ev0)] ++ rest) // bag_pop_ne_vals_app length_app.
      assert (Hrest_le : ∀ ev, (∀ τ' w', (τ', Lin NONEV (SOMEV w')) ∈ rest → τ' ∈ tags) →
                bag_pop_ne_vals [(τ0, ev)] = [] →
                length (bag_pop_ne_vals rest) ≤ length tags →
                length (bag_pop_ne_vals [(τ0, ev)]) + length (bag_pop_ne_vals rest) ≤ length tags).
      { intros ev' ? ->. simpl. lia. }
      destruct ev0 as [v_c|vr vr'|v_r].
      { apply Hrest_le.
        - intros ???.
          eapply Htags, elem_of_cons.
          right. eassumption.
        - reflexivity.
        - apply IH; [done..|].
          intros ????.
          eapply Htags, elem_of_cons.
          right. eassumption. }
      2: { apply Hrest_le.
        - intros ???.
          eapply Htags, elem_of_cons.
          right. eassumption.
        - reflexivity.
        - apply IH; [done..|].
          intros ????.
          eapply Htags, elem_of_cons.
          right. eassumption. }
      (* Lin case *)
      destruct vr; destruct vr';
        try (rewrite /bag_pop_ne_vals /=; rewrite /bag_pop_ne_vals in IH;
             apply (IH tags); auto; intros τ' v' w' Hin'; eapply Htags; right; exact Hin').
      (* Only InjLV × InjRV survives *)
      simpl.
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
     By linearized_sound, the bag at τ3 is non-empty. Contradiction with Pop IsEmpty. *)
  Local Lemma trace_prt_no_cross_match ts' :
    per_tag_wellformed_bag rme valid_value ts →
    ts = filter (not ∘ is_lin ∘ snd) ts' →
    per_tag_linearized ts' →
    NoDup (filter (is_lin ∘ snd) ts').*1 →
    (∃ s', linearized_sound (M:=bag_model rme valid_value) (filter (is_lin ∘ snd) ts') s_init s') →
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
        apply (list_elem_of_fmap_2 fst _ (τ3, Call (encode_request (Push v)))).
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
        apply (list_elem_of_fmap_2 fst _ (τ3, Call (encode_request Pop))).
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
        destruct (Hcomplete τ3) as (vc & vc' & [Heq_c|Heq_c]).
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
      (* Split linearized_sound at τ3 *)
      rewrite /lts in Hlts_split. rewrite Hlts_split in Hls.
      destruct ev_τ3 as [|v_req v_resp|]; simpl in Hlin_ev_τ3; try done.
      apply linearized_sound_app_inv in Hls as (s_mid & Hls_before & Hls_rest).
      apply linearized_sound_cons_inv in Hls_rest as (s_after_τ3 & _ & Hrr & _).
      assert (Hv_resp : v_resp = encode_response IsEmpty).
      { destruct (Hptl τ3) as (w & w' & Hprefix).
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
      { destruct Hrr as (r & Heq_req & Hrr_match).
        destruct r.
        - destruct Hrr_match as [_ Habs]. rewrite Hv_resp in Habs. discriminate.
        - destruct Hrr_match as [Hempty|(v' & _ & _ & Habs)].
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
      { assert (Hbal := linearized_sound_bag_size_balance _ _ _ Hls_before).
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
      assert (Hlin_ret : ∀ τ0 vr vr', (τ0, Lin vr vr') ∈ lts →
                (τ0, Ret vr') ∈ ts).
      { intros τ0 vr vr' Hin_lts0.
        apply list_elem_of_filter in Hin_lts0 as [_ Hin_ts'0].
        destruct (Hptl τ0) as (w0 & w0' & Hprefix0).
        apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hin_ts'0 as Hfilt0; last done.
        pose proof (elem_of_prefix _ _ _ Hfilt0 Hprefix0) as Hmem.
        rewrite !elem_of_cons elem_of_nil in Hmem.
        destruct Hmem as [Hmem|[Hmem|[Hmem|[]]]];
          apply (f_equal snd) in Hmem; simpl in Hmem; try discriminate.
        injection Hmem as Heq_w0 Heq_w0'. subst w0 w0'.
        assert (Hcall_ts0 : (τ0, Call vr) ∈ ts).
        { assert (Hlin_filt : (τ0, Lin vr vr') ∈ filter (λ x, x.1 = τ0) ts').
          { apply list_elem_of_filter_2; done. }
          set (ft := filter (λ x : positive * trace, x.1 = τ0) ts') in *.
          destruct ft as [|c1 rest_f] eqn:Hf.
          { set_solver. }
          assert (Hc1 : c1 = (τ0, Call vr)).
          { exact (prefix_cons_inv_1 _ _ _ _ Hprefix0). }
          rewrite Hfilt_orig. apply list_elem_of_filter_2; [compute_done|].
          apply (list_elem_of_filter_1 (λ x, x.1 = τ0)). subst ft c1. rewrite Hf. clear. set_solver. }
        destruct (Hcomplete τ0) as (vc & vc' & [Heq_c|Heq_c]).
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
      assert (Hpop_ne_in_mb2 : ∀ τ' w, (τ', Lin NONEV (SOMEV w)) ∈ lts_before →
                                         τ' ∈ m_before.*2).
      { intros τ' w Hin_before0.
        assert (Hin_lts0 : (τ', Lin NONEV (SOMEV w)) ∈ lts).
        { rewrite /lts Hlts_split. apply elem_of_app. left. exact Hin_before0. }
        assert (Hret : (τ', Ret (SOMEV w)) ∈ ts).
        { exact (Hlin_ret _ _ _ Hin_lts0). }
        assert (Hτ'_m2 : τ' ∈ m.*2).
        { destruct Hvalid as (Hpvt_sub & _). apply Hpvt_sub.
          apply (list_elem_of_fmap_2 fst _ (τ', Ret (SOMEV w))).
          apply list_elem_of_filter_2; [|exact Hret].
          rewrite /is_ret_pop_val. eexists. done. }
        apply list_elem_of_fmap_1 in Hτ'_m2 as ([τ_push τ_pop'] & Heq_τ & Hin_m0).
        simpl in Heq_τ. subst τ_pop'.
        apply (list_elem_of_fmap_2 snd _ (τ_push, τ')).
        apply list_elem_of_filter_2; [|exact Hin_m0].
        simpl. apply (list_elem_of_fmap_2 fst _ (τ', Lin NONEV (SOMEV w))).
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
        (τ0, Lin (InjRV v0) (LitV LitUnit)) ∈ l → v0 ∈ bag_push_vals l).
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
        (τ0, Lin (InjLV v0) (InjRV w0)) ∈ l → w0 ∈ bag_pop_ne_vals l).
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
            apply linearized_sound_valid_request in Hls_before.
            rewrite Forall_forall in Hls_before.
            destruct (Hls_before _ Hin0) as [(v_push & _ & Henc) | Henc];
              simpl in Henc; by simplify_eq. }
          exact (Hpop_ne_in_mb2 τ0 w0 Hin0). }
      (* Hupper: 1 + |m_before| ≤ |bag_push_vals lts_before| *)
      (* Each matched push and τ1 contribute a distinct value to bag_push_vals *)
      assert (Hupper : 1 + length m_before ≤ length (bag_push_vals lts_before)).
      { (* Show each τ ∈ m_before.*1 has push Lin event, extract its value *)
        assert (Hmb1_val : ∀ τ0, τ0 ∈ m_before.*1 →
                  ∃ v0, v0 ∈ bag_push_vals lts_before ∧
                        (τ0, Lin (SOMEV v0) (#())) ∈ lts_before).
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
          destruct ev0 as [|vr00 vr00'|]; simpl in Hlin0; try done.
          assert (Hret0 := Hlin_ret τ0 vr00 vr00' Hin_lts0').
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
            (* Derive vr00 = SOMEV vw from two prefix constraints *)
            assert (Hvr : vr00 = SOMEV vw).
            { (* vr00 = SOMEV v0 from per_tag_linearized prefix *)
              destruct (Hptl τ0) as (w0c & w0c' & Hpfx0c).
              assert (Hcall_ts' : (τ0, Call (SOMEV v0)) ∈ ts').
              { apply list_elem_of_filter_1 in Hcall. rewrite Hfilt_orig in Hcall.
                exact (list_elem_of_filter_1 _ _ _ Hcall). }
              apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hcall_ts'; last done.
              pose proof (elem_of_prefix _ _ _ Hcall_ts' Hpfx0c) as Hpos.
              rewrite !elem_of_cons elem_of_nil in Hpos.
              destruct Hpos as [Hpos|[Hpos|[Hpos|[]]]];
                try (apply (f_equal snd) in Hpos; simpl in Hpos; discriminate).
              apply (f_equal snd) in Hpos. simpl in Hpos. injection Hpos as <-.
              (* Now w0c = SOMEV v0. Show vr00 = w0c from Lin event *)
              assert (Hlin_in : (τ0, Lin vr00 vr00') ∈ filter (λ x, x.1 = τ0) ts').
              { apply list_elem_of_filter_2; [done|exact Hin_ts'00]. }
              pose proof (elem_of_prefix _ _ _ Hlin_in Hpfx0c) as Hpos2.
              rewrite !elem_of_cons elem_of_nil in Hpos2.
              destruct Hpos2 as [Hpos2|[Hpos2|[Hpos2|[]]]];
                try (apply (f_equal snd) in Hpos2; simpl in Hpos2; discriminate).
              apply (f_equal snd) in Hpos2. simpl in Hpos2.
              assert (Hvr_eq1 : vr00 = SOMEV v0) by (injection Hpos2; done).
              assert (Hvr_eq2 : v0 = vw).
              { apply (f_equal snd) in Hm1. simpl in Hm1. injection Hm1; done. }
              congruence. }
            assert (Hvr_eq3 : vr00' = #()).
            { apply (f_equal snd) in Hm2. simpl in Hm2. injection Hm2; done. }
            subst vr00 vr00'.
            exists vw. split; [exact (Hpush_in_vals _ _ _ Hin0)|exact Hin0].
          - exfalso.
            apply (list_elem_of_filter_2 (λ x, x.1 = τ0)) in Hcall; last done.
            pose proof (elem_of_prefix _ _ _ Hcall Hpfx_pop) as Hm1.
            rewrite !elem_of_cons elem_of_nil right_id in Hm1.
            destruct Hm1 as [Hm1|Hm1];
              apply (f_equal snd) in Hm1; simpl in Hm1; discriminate. }
        (* τ1 also has a push value in bag_push_vals *)
        assert (Hτ1_val : ∃ v0, v0 ∈ bag_push_vals lts_before ∧
                                 (τ1, Lin (SOMEV v0) (#())) ∈ lts_before).
        { destruct (valid_match_call_push ts m τ1 τ2 Hvalid Hin_m) as [v0 Hcall].
          apply list_elem_of_fmap_1 in Hτ1_in_before as ([τ1'' ev0] & Heqτ1 & Hin0).
          simpl in Heqτ1. subst τ1''.
          assert (Hin_lts0 : (τ1, ev0) ∈ lts).
          { rewrite /lts Hlts_split. apply elem_of_app. left. exact Hin0. }
          pose proof Hin_lts0 as Hin_lts0'.
          apply list_elem_of_filter in Hin_lts0 as [Hlin0 Hin_ts'01].
          destruct ev0 as [|vr01 vr01'|]; simpl in Hlin0; try done.
          assert (Hret0 := Hlin_ret τ1 vr01 vr01' Hin_lts0').
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
            assert (Hvr : vr01 = SOMEV vw).
            { destruct (Hptl τ1) as (w0c & w0c' & Hpfx0c).
              assert (Hcall_ts' : (τ1, Call (SOMEV v0)) ∈ ts').
              { apply list_elem_of_filter_1 in Hcall. rewrite Hfilt_orig in Hcall.
                exact (list_elem_of_filter_1 _ _ _ Hcall). }
              apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hcall_ts'; last done.
              pose proof (elem_of_prefix _ _ _ Hcall_ts' Hpfx0c) as Hpos.
              rewrite !elem_of_cons elem_of_nil in Hpos.
              destruct Hpos as [Hpos|[Hpos|[Hpos|[]]]];
                try (apply (f_equal snd) in Hpos; simpl in Hpos; discriminate).
              apply (f_equal snd) in Hpos. simpl in Hpos. injection Hpos as <-.
              assert (Hlin_in : (τ1, Lin vr01 vr01') ∈ filter (λ x, x.1 = τ1) ts').
              { apply list_elem_of_filter_2; [done|exact Hin_ts'01]. }
              pose proof (elem_of_prefix _ _ _ Hlin_in Hpfx0c) as Hpos2.
              rewrite !elem_of_cons elem_of_nil in Hpos2.
              destruct Hpos2 as [Hpos2|[Hpos2|[Hpos2|[]]]];
                try (apply (f_equal snd) in Hpos2; simpl in Hpos2; discriminate).
              assert (Hvr_eq1 : vr01 = SOMEV v0) by (apply (f_equal snd) in Hpos2; simpl in Hpos2; injection Hpos2; done).
              assert (Hvr_eq2 : v0 = vw) by (apply (f_equal snd) in Hm1; simpl in Hm1; injection Hm1; done).
              congruence. }
            assert (Hvr' : vr01' = #()) by (apply (f_equal snd) in Hm2; simpl in Hm2; injection Hm2; done).
            subst vr01 vr01'.
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
    destruct (Hptl τ1) as (v1 & v1' & Hptl_τ1).
    destruct (Hptl τ2) as (v2 & v2' & Hptl_τ2).
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
    (* Determine p_call = (τ2, Call v2) *)
    assert (Hp_call_in_ts' : p_call ∈ ts').
    { rewrite Hfilter in Hcall2_lookup.
      exact (list_filter_lookup_orig _ _ _ _ Hcall2_lookup). }
    assert (Hp_call_eq : p_call = (τ2, Call v2)).
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
                      [(τ1, Call v1); (τ1, Lin v1 v1'); (τ1, Ret v1')]).
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
        assert (Hlin_in_take : (τ1, Lin v1 v1') ∈ take lin1 ts').
        { apply (list_elem_of_filter_1 (λ x, x.1 = τ1)). rewrite Hfilt_eq. set_solver. }
        apply list_elem_of_lookup_1 in Hlin_in_take as [k Hk_take].
        assert (Hk_lt : k < lin1).
        { apply lookup_lt_Some in Hk_take. rewrite length_take in Hk_take.
          apply lookup_lt_Some in Hlt1_lookup. lia. }
        assert (Hk_ts' : ts' !! k = Some (τ1, Lin v1 v1')).
        { apply lookup_take_Some in Hk_take. tauto. }
        apply (Hlt1_min k (τ1, Lin v1 v1') Hk_ts' Hk_lt).
        split; [done|simpl; done]. }
    (* === Step B: call2 < length(filter P (take lin2 ts')) === *)
    (* Decompose ts' at lin2 *)
    pose proof (take_drop_middle ts' lin2 (τ2, lt2) Hlt2_lookup) as Hts'_decomp2.
    assert (Hts_decomp2 : ts = filter (not ∘ is_lin ∘ snd) (take lin2 ts') ++
                                filter (not ∘ is_lin ∘ snd) (drop (Datatypes.S lin2) ts')).
    { rewrite Hfilter -{1}Hts'_decomp2 filter_app filter_cons_False //.
      simpl. tauto. }
    set A2 := filter (not ∘ is_lin ∘ snd) (take lin2 ts').
    (* p_call = (τ2, Call v2) ∈ take lin2 ts' *)
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
    (* The tag-τ2 filter before lin2 must be [(τ2, Call v2)] (not []) *)
    assert (Hfilt_τ2_before : filter (λ t, t.1 = τ2) (take lin2 ts') = [(τ2, Call v2)]).
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
        apply (Hno_lin_before (τ2, Lin v2 v2')); [set_solver|simpl; done]. }
    (* (τ2, Call v2) ∈ take lin2 ts' *)
    assert (Hcall_in_take : (τ2, Call v2) ∈ take lin2 ts').
    { apply (list_elem_of_filter_1 (λ x, x.1 = τ2)).
      rewrite Hfilt_τ2_before. apply elem_of_cons. left. done. }
    (* p_call ∉ drop (Datatypes.S lin2) ts' *)
    assert (Hp_call_notin_drop : p_call ∉ drop (Datatypes.S lin2) ts').
    { rewrite Hp_call_eq. intros Habs_in.
      assert (Hcall_in_fa : (τ2, Call v2) ∈ filter (λ t, t.1 = τ2) (drop (Datatypes.S lin2) ts')).
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
    (∃ s', linearized_sound (M:=bag_model rme valid_value) (filter (is_lin ∘ snd) ts') s_init s') →
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
        destruct (Hcomplete a) as (v & v' & [Heq|Heq]).
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
      as (ts' & Hfilter & Hper_tag_lin & Hlin_sound & Hval_then_not_pr).
    split; first by eapply conc_history_trace_pre.
    exists (trace_prt ts').
    split; first by eapply trace_pre_prt_subrelation.
    split; last by eapply trace_prt_correct_empty.
    split; last by eapply trichotomy_trace_prt.
    constructor.
    - by eapply conc_history_trace_prt.
    - by apply enqueue_once_trace_val.
    - by apply dequeue_once_trace_val.
    - by apply val_order_trace_val.
    - by apply all_dequeued_or_empty_trace_val_trace_empty.
    - by apply empty_then_not_val_trace_val_trace_empty.
    - by apply val_then_not_pr_trace_prt_trace_val.
    - intros [τ ?]. unfold trace_empty. simpl.
      destruct (decide (empty_of_trace_match ts m τ)); [by left | by right].
    - intros [τ1 ?] [τ2 ?]. unfold trace_val. simpl.
      destruct (decide ((τ1, τ2) ∈ m)); [by left | by right].
  Qed.

  Lemma I_queue_pre__order_correct :
    I_queue_pre ts m → order_correct trace_pre trace_val.
  Proof.
    intros (_ & _ & Hoc & _) [e1 ?] [e2 ?] [d1 ?] [d2 ?].
    rewrite /trace_pre /trace_val /=.
    apply Hoc.
  Qed.

  (**********************************************************)
  (* Begin LLM-generated code. *)
  (* tool: Claude Code 2.1.111
     model: Claude Opus 4.7 (claude-opus-4-7[1m])
     parameters:
        effort = xhigh
        context window = 1000000
        max output tokens = 128000 *)

  (* ===== Helper: sort operations by an abstract prt relation ===== *)
  (* Given a prt relation that is a strict total order (Trichotomy + Irreflexive +
     Transitive) on operation, there exists a linear enumeration of
     [elements (events_of_trace ts)] respecting prt. *)
  Local Lemma prt_sort_exists
      (prt : relation operation)
      (Htri : Trichotomy prt)
      (Htrans : Transitive prt)
      (Hirr : Irreflexive prt) :
    ∃ ord : list positive,
      NoDup ord ∧
      (∀ τ, τ ∈ ord ↔ τ ∈ events_of_trace ts) ∧
      (∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
        i < j →
        ord !! i = Some τ1 →
        ord !! j = Some τ2 →
        prt (τ1 ↾ H1) (τ2 ↾ H2)).
  Proof.
    (* Work with the list [elements (events_of_trace ts)] and induct on its length. *)
    assert (Hevent_pi : ∀ τ, ProofIrrel (τ ∈ events_of_trace ts)).
    { intros. apply _. }
    (* Pick-min helper: given a non-empty list, find a prt-minimum. *)
    assert (Hpickmin : ∀ (l : list positive),
      NoDup l →
      (∀ τ, τ ∈ l → τ ∈ events_of_trace ts) →
      l ≠ [] →
      ∃ τmin,
        τmin ∈ l ∧
        ∀ τ (Hτ : τ ∈ events_of_trace ts) (Hmn : τmin ∈ events_of_trace ts),
          τ ∈ l → τ ≠ τmin → prt (τmin ↾ Hmn) (τ ↾ Hτ)).
    { intros l. induction l as [|a rest IH]; intros Hnd Hsub Hne; first done.
      destruct rest as [|b rest'] eqn:Hrest.
      - exists a. split; first by left.
        intros τ Hτ Hmn Hin Hne_τ.
        rewrite list_elem_of_singleton in Hin. done.
      - assert (Hnd' : NoDup (b :: rest')).
        { apply NoDup_cons in Hnd. tauto. }
        assert (Hsub' : ∀ τ, τ ∈ (b :: rest') → τ ∈ events_of_trace ts).
        { intros τ Hin. apply Hsub. right. exact Hin. }
        destruct (IH Hnd' Hsub' ltac:(done)) as (mn & Hmn_in & Hmn_min).
        assert (Ha_in_et : a ∈ events_of_trace ts) by (apply Hsub; left).
        assert (Hmn_in_et : mn ∈ events_of_trace ts) by (apply Hsub; right; exact Hmn_in).
        destruct (trichotomy prt (a ↾ Ha_in_et) (mn ↾ Hmn_in_et)) as [Ham|[Hameq|Hma]].
        + (* a < mn: a is the new min *)
          exists a. split; first by left.
          intros τ Hτ Hm2 Hin Hne_τ.
          rewrite elem_of_cons in Hin.
          destruct Hin as [->|Hin]; first done.
          destruct (decide (τ = mn)) as [->|Hne_m].
          * rewrite (proof_irrel Hm2 Ha_in_et). rewrite (proof_irrel Hτ Hmn_in_et).
            exact Ham.
          * rewrite (proof_irrel Hm2 Ha_in_et).
            assert (Hprt_mτ : prt (mn ↾ Hmn_in_et) (τ ↾ Hτ)).
            { apply Hmn_min; done. }
            etrans; [exact Ham|exact Hprt_mτ].
        + (* a = mn (as operations): impossible by NoDup *)
          exfalso. apply (f_equal proj1_sig) in Hameq. simpl in Hameq. subst mn.
          apply NoDup_cons in Hnd as [Hna _]. apply Hna. exact Hmn_in.
        + (* mn < a: mn is still the min *)
          exists mn. split; first by right.
          intros τ Hτ Hm2 Hin Hne_τ.
          rewrite elem_of_cons in Hin.
          destruct Hin as [->|Hin].
          * rewrite (proof_irrel Hm2 Hmn_in_et). rewrite (proof_irrel Hτ Ha_in_et).
            exact Hma.
          * destruct (decide (τ = mn)) as [->|Hne_m]; first done.
            rewrite (proof_irrel Hm2 Hmn_in_et).
            apply Hmn_min; done. }
    (* Now construct the sort by induction on length. *)
    assert (Hsort : ∀ n (l : list positive),
      length l = n →
      NoDup l →
      (∀ τ, τ ∈ l → τ ∈ events_of_trace ts) →
      ∃ ord, NoDup ord ∧ (∀ τ, τ ∈ ord ↔ τ ∈ l) ∧
        (∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
          i < j → ord !! i = Some τ1 → ord !! j = Some τ2 →
          prt (τ1 ↾ H1) (τ2 ↾ H2))).
    { intros n. induction n as [|n IH]; intros l Hlen Hnd Hsub.
      - destruct l; last (simpl in Hlen; lia).
        exists []. split_and!; [constructor|intros; done|].
        intros ? ? ? ? ? ? ? Habs. simpl in Habs. done.
      - destruct l as [|a rest]; first (simpl in Hlen; lia).
        destruct (Hpickmin (a :: rest) Hnd Hsub ltac:(done))
          as (mn & Hmn_in & Hmn_min).
        assert (Hmn_in_et : mn ∈ events_of_trace ts) by (apply Hsub; exact Hmn_in).
        (* Split (a :: rest) around mn: (a :: rest) = before ++ mn :: after,
           with mn ∉ before and mn ∉ after (from NoDup). *)
        apply list_elem_of_split in Hmn_in as (before & after & Hsplit).
        set (rest' := before ++ after).
        assert (Hnd_rest' : NoDup rest').
        { unfold rest'. rewrite Hsplit in Hnd.
          rewrite NoDup_app in Hnd. destruct Hnd as (Hnd_b & Hmn_in_b & Hnd_rest).
          rewrite NoDup_cons in Hnd_rest. destruct Hnd_rest as [Hmn_in_a Hnd_a].
          rewrite NoDup_app. split_and!; try done.
          intros x Hx_in_b Hx_in_a. apply (Hmn_in_b x Hx_in_b).
          right. exact Hx_in_a. }
        assert (Hsub_rest' : ∀ τ, τ ∈ rest' → τ ∈ events_of_trace ts).
        { intros τ Hin_rest. apply Hsub. rewrite Hsplit.
          apply elem_of_app in Hin_rest as [Hin_b|Hin_a].
          - apply elem_of_app. left. exact Hin_b.
          - apply elem_of_app. right. right. exact Hin_a. }
        assert (Hlen_rest' : length rest' = n).
        { unfold rest'. rewrite length_app.
          apply (f_equal length) in Hsplit. rewrite length_app /= in Hsplit.
          simpl in Hlen. lia. }
        assert (Hmn_notin_rest' : mn ∉ rest').
        { unfold rest'. rewrite Hsplit in Hnd.
          rewrite NoDup_app in Hnd. destruct Hnd as (_ & Hmn_in_b & Hnd_rest).
          rewrite NoDup_cons in Hnd_rest. destruct Hnd_rest as [Hmn_in_a _].
          intros Hmn_in_r. apply elem_of_app in Hmn_in_r as [|].
          - apply (Hmn_in_b mn); [done|left; done].
          - done. }
        destruct (IH rest' Hlen_rest' Hnd_rest' Hsub_rest')
          as (ord_rest & Hnd_ord & Hord_mem & Hord_sorted).
        exists (mn :: ord_rest).
        split_and!.
        + apply NoDup_cons. split; last exact Hnd_ord.
          intros Hm_in_ord. apply Hord_mem in Hm_in_ord.
          apply Hmn_notin_rest'. exact Hm_in_ord.
        + intros τ. split.
          * intros Hin_τ.
            rewrite elem_of_cons in Hin_τ.
            rewrite Hsplit.
            clear -Hin_τ Hord_mem Hsub.
            destruct Hin_τ as [->|Hin_rest]; first set_solver.
            apply Hord_mem in Hin_rest. unfold rest' in Hin_rest.
            clear -Hin_rest. set_solver.
          * intros Hin_l.
            destruct (decide (τ = mn)) as [->|Hne];
              first (left; done).
            right. apply Hord_mem. unfold rest'.
            rewrite Hsplit in Hin_l.
            clear -Hin_l Hne. set_solver.
        + intros i j τ1 τ2 H1 H2 Hij Hi Hj.
          destruct i as [|i']; destruct j as [|j'].
          * lia.
          * simpl in Hi. injection Hi as <-.
            simpl in Hj.
            assert (Hτ2_in : τ2 ∈ ord_rest).
            { eapply list_elem_of_lookup_2; exact Hj. }
            assert (Hτ2_in_rest' : τ2 ∈ rest') by (apply Hord_mem; exact Hτ2_in).
            assert (Hτ2_in_l : τ2 ∈ a :: rest).
            { rewrite Hsplit. unfold rest' in Hτ2_in_rest'.
              apply elem_of_app in Hτ2_in_rest' as [|].
              - apply elem_of_app. left. done.
              - apply elem_of_app. right. right. done. }
            assert (Hne : τ2 ≠ mn).
            { intros ->. apply Hmn_notin_rest'. exact Hτ2_in_rest'. }
            apply Hmn_min; done.
          * lia.
          * simpl in Hi, Hj.
            apply (Hord_sorted i' j' _ _ H1 H2); [lia|exact Hi|exact Hj]. }
    destruct (Hsort _ _ eq_refl (NoDup_elements _)
                (λ τ Hin, proj1 (elem_of_elements (events_of_trace ts) τ) Hin))
      as (ord & Hnd & Hmem & Hsorted).
    exists ord. split_and!; try done.
    intros τ. split.
    - intros Hin. apply Hmem in Hin. apply elem_of_elements. exact Hin.
    - intros Hin. apply Hmem. apply elem_of_elements. exact Hin.
  Qed.

  (* ===== Helper: every tag is push or pop ===== *)
  Local Lemma tag_is_push_or_pop (Hadq : all_dequeued_or_empty trace_val trace_empty) τ :
    τ ∈ events_of_trace ts →
    τ ∈ push_of_trace ts ∨ τ ∈ pop_of_trace ts.
  Proof.
    intros Hτ.
    destruct (Hadq (τ ↾ Hτ)) as [Hemp|([τ' Hτ'] & Hval)].
    - (* empty pop: τ ∈ pop_of_trace *)
      right. destruct Hemp as [Hpop _]. simpl in Hpop. exact Hpop.
    - (* val case *)
      simpl in Hval.
      destruct Hval as [Hval|Hval].
      + (* val τ τ': τ is push *)
        left.
        destruct (valid_match_call_push _ _ _ _ Hvalid Hval) as [v Hcall].
        apply (list_elem_of_fmap_2 fst _ (τ, Call (encode_request (Push v)))).
        apply list_elem_of_filter_2; last exact Hcall.
        exists v. done.
      + (* val τ' τ: τ is matched pop *)
        right.
        pose proof (valid_match_call_pop _ _ _ _ Hvalid Hval) as Hcall.
        apply (list_elem_of_fmap_2 fst _ (τ, Call (encode_request Pop))).
        apply list_elem_of_filter_2; last exact Hcall.
        done.
  Qed.

  (* ===== Call valid: every Call in ts has an encoded queue request ===== *)
  Local Lemma call_valid_ts :
    per_tag_wellformed_bag rme valid_value ts →
    all_dequeued_or_empty trace_val trace_empty →
    call_valid (M:=queue_model rme valid_value) ts.
  Proof.
    intros Hwf Hadq.
    apply Forall_forall. intros [τ ev] Hin.
    destruct ev as [r|v v'|r]; [|done|done].
    simpl.
    assert (Hτ : τ ∈ events_of_trace ts).
    { unfold events_of_trace. apply elem_of_list_to_set.
      apply (list_elem_of_fmap_2 fst _ (τ, Call r)). exact Hin. }
    (* From per_tag_complete, there's a unique Call for tag τ *)
    apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin as Hin_tag; last done.
    destruct (Hcomplete τ) as (vc & vr & [Hfilt|Hfilt]).
    { rewrite Hfilt in Hin_tag. set_solver. }
    (* So vc = r *)
    rewrite Hfilt in Hin_tag.
    rewrite !elem_of_cons elem_of_nil in Hin_tag.
    destruct Hin_tag as [Heq|[Heq|Habs]]; last done; last first.
    { discriminate. }
    simplify_eq.
    (* Now the unique Call for τ is (τ, Call r) with vc = r *)
    destruct (tag_is_push_or_pop Hadq τ Hτ) as [Hpush|Hpop].
    - destruct (push_tag_in_trace _ _ Hpush) as [w Hcall_push].
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hcall_push as Hpush_tag; last done.
      rewrite Hfilt in Hpush_tag.
      rewrite !elem_of_cons elem_of_nil right_id in Hpush_tag.
      destruct Hpush_tag as [Heq2|Heq2].
      + simplify_eq. left. exists w. split; last reflexivity.
        destruct (Hwf τ) as [[v_push [Hvv Hfilter]] | [? [_ Hfilter]]].
        * rewrite Hfilt in Hfilter.
          apply prefix_cons_inv_1 in Hfilter as Heq.
          injection Heq as ->. assumption.
        * rewrite Hfilt in Hfilter.
          apply prefix_cons_inv_1 in Hfilter as Heq.
          discriminate Heq.
      + discriminate.
    - pose proof (pop_tag_in_trace _ _ Hpop) as Hcall_pop.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hcall_pop as Hpop_tag; last done.
      rewrite Hfilt in Hpop_tag.
      rewrite !elem_of_cons elem_of_nil in Hpop_tag.
      destruct Hpop_tag as [Heq2|[Heq2|[]]].
      + simplify_eq. right. reflexivity.
      + discriminate.
  Qed.

  (* tag_classification is not used by the main lemma (the Ret value for push
     isn't constrained to #() from Section hypotheses — the downstream caller
     instantiates via close_trace which enforces it, but within the binding
     Section we don't have that guarantee). *)

  (* ===== The Lin event value for tag τ =====
     For τ ∈ events_of_trace ts, extract the Call and Ret values directly
     from ts (they form the filter [(τ, Call vc); (τ, Ret vr)] by per_tag_complete).
     The Lin event for τ will be (τ, Lin vc vr), matching the queue semantics
     (the Call request equals the Lin request; the Ret response equals the Lin
     response). For τ ∉ events_of_trace ts, the value doesn't matter since no
     Lin is inserted for such a tag. *)
  Local Definition lin_event_val (τ : positive) : val * val :=
    match filter (λ x, x.1 = τ) ts with
    | (_, Call vc) :: (_, Ret vr) :: _ => (vc, vr)
    | _ => (#(), #())
    end.

  Local Lemma lin_event_val_of τ vc vr :
    filter (λ x, x.1 = τ) ts = [(τ, Call vc); (τ, Ret vr)] →
    lin_event_val τ = (vc, vr).
  Proof.
    intros Hfilt. unfold lin_event_val. rewrite Hfilt. done.
  Qed.

  (* ===== Insertion of Lin events into ts in prt order =====
     Correct approach: maintain a (prefix, suffix) state.
     For each τ in ord (in prt order):
     - If τ's Call is already in prefix, insert Lin(τ) at end of prefix.
     - Else, advance suffix until we find Call(τ), move it to prefix,
       then insert Lin(τ) at end of prefix.
     This ensures Lin events appear in prt order in the final trace,
     while preserving the per-tag "Call before Lin before Ret" invariant
     (Ret of τ stays in suffix when τ is processed, because otherwise
     some prt-earlier operation τ'' would have Call after Ret(τ),
     implying trace_pre(τ, τ'') and thus prt(τ, τ'') — contradiction). *)

  (* Move elements from suffix to prefix until we find a Call(τ). *)
  Local Fixpoint advance_to_call (τ : positive)
      (prefix suffix : list (positive * trace))
      : list (positive * trace) * list (positive * trace) :=
    match suffix with
    | [] => (prefix, [])
    | (τ', Call v') :: rest =>
      if decide (τ' = τ) then
        (prefix ++ [(τ, Call v')], rest)
      else
        advance_to_call τ (prefix ++ [(τ', Call v')]) rest
    | evt :: rest =>
      advance_to_call τ (prefix ++ [evt]) rest
    end.

  (* Insert one Lin: either directly (Call already in prefix) or after advancing. *)
  Local Definition insert_one_lin (τ : positive) (v v' : val)
      (prefix suffix : list (positive * trace))
      : list (positive * trace) * list (positive * trace) :=
    if decide (τ ∈ (filter (is_call ∘ snd) prefix).*1) then
      (prefix ++ [(τ, Lin v v')], suffix)
    else
      let '(p, s) := advance_to_call τ prefix suffix in
      (p ++ [(τ, Lin v v')], s).

  (* Process all Lins in prt order. *)
  Local Fixpoint insert_lins_in_order (ord : list positive)
      (prefix suffix : list (positive * trace))
      : list (positive * trace) :=
    match ord with
    | [] => prefix ++ suffix
    | τ :: rest =>
      let '(v, v') := lin_event_val τ in
      let '(p, s) := insert_one_lin τ v v' prefix suffix in
      insert_lins_in_order rest p s
    end.

  Local Definition ts'_queue (ord : list positive) : list (positive * trace) :=
    insert_lins_in_order ord [] ts.

  (* ===== Structural lemmas: filter preservation ===== *)
  (* advance_to_call is content-preserving: p ++ s = prefix ++ suffix. *)
  Local Lemma advance_to_call_preserves τ prefix suffix :
    ∀ p s,
    advance_to_call τ prefix suffix = (p, s) →
    p ++ s = prefix ++ suffix.
  Proof.
    revert prefix. induction suffix as [|[τ' ev] rest IH]; intros prefix p s Heq.
    - simpl in Heq. injection Heq as <- <-. by rewrite app_nil_r.
    - destruct ev as [v'|vl vl'|r].
      + simpl in Heq. destruct (decide (τ' = τ)) as [->|Hne].
        * injection Heq as <- <-. by rewrite -app_assoc.
        * apply IH in Heq. rewrite Heq. by rewrite -app_assoc.
      + simpl in Heq. apply IH in Heq. rewrite Heq. by rewrite -app_assoc.
      + simpl in Heq. apply IH in Heq. rewrite Heq. by rewrite -app_assoc.
  Qed.

  (* insert_one_lin only ADDS one Lin event; non-Lin content is preserved. *)
  Local Lemma insert_one_lin_filter_not_lin τ v v' prefix suffix :
    ∀ p s,
    insert_one_lin τ v v' prefix suffix = (p, s) →
    filter (not ∘ is_lin ∘ snd) (p ++ s)
      = filter (not ∘ is_lin ∘ snd) (prefix ++ suffix).
  Proof.
    intros p s Heq.
    unfold insert_one_lin in Heq.
    assert (Hne : ¬ (not ∘ is_lin ∘ snd) (τ, Lin v v')).
    { simpl. intros Habs. apply Habs. done. }
    destruct (decide (τ ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|Hnin].
    - injection Heq as <- <-.
      rewrite -app_assoc. simpl.
      rewrite !filter_app.
      rewrite (filter_cons_False _ (τ, Lin v v') _ Hne). done.
    - destruct (advance_to_call τ prefix suffix) as [p' s'] eqn:Hadv.
      injection Heq as <- <-.
      pose proof (advance_to_call_preserves _ _ _ _ _ Hadv) as Hpres.
      rewrite -app_assoc. simpl.
      rewrite !filter_app.
      rewrite (filter_cons_False _ (τ, Lin v v') _ Hne).
      rewrite -filter_app. rewrite Hpres. rewrite filter_app. done.
  Qed.

  Local Lemma insert_lins_in_order_filter_not_lin ord prefix suffix :
    filter (not ∘ is_lin ∘ snd) (insert_lins_in_order ord prefix suffix)
      = filter (not ∘ is_lin ∘ snd) (prefix ++ suffix).
  Proof.
    revert prefix suffix. induction ord as [|τ rest IH]; intros prefix suffix.
    - simpl. done.
    - simpl. destruct (lin_event_val τ) as [v v'] eqn:Hval.
      destruct (insert_one_lin τ v v' prefix suffix) as [p s] eqn:Heq.
      rewrite IH.
      eapply insert_one_lin_filter_not_lin. exact Heq.
  Qed.

  Local Lemma ts_no_lin_event :
    ∀ τ v v', (τ, Lin v v') ∉ ts.
  Proof.
    intros τ v v' Hin.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin as Hin_tag; last done.
    destruct (Hcomplete τ) as (vc & vr & [Hfilt|Hfilt]).
    - rewrite Hfilt in Hin_tag. set_solver.
    - rewrite Hfilt in Hin_tag.
      rewrite !elem_of_cons elem_of_nil in Hin_tag.
      destruct Hin_tag as [Habs|[Habs|Habs]];
        try (discriminate || done).
  Qed.

  Local Lemma filter_all_true {A} (P : A → Prop) `{!∀ x, Decision (P x)} (l : list A) :
    Forall P l → filter P l = l.
  Proof.
    induction l as [|a l' IH]; first done.
    intros Hall.
    apply Forall_cons in Hall as [Ha Hall'].
    rewrite filter_cons_True; last done.
    f_equal. apply IH. exact Hall'.
  Qed.

  Local Lemma ts_filter_not_lin_self :
    filter (not ∘ is_lin ∘ snd) ts = ts.
  Proof.
    apply filter_all_true.
    apply Forall_forall. intros [τ ev] Hin.
    unfold compose. simpl.
    destruct ev as [r|v v'|r].
    - intros Habs. exact Habs.
    - intros _. eapply ts_no_lin_event. exact Hin.
    - intros Habs. exact Habs.
  Qed.

  Local Lemma ts'_queue_filter_not_lin ord :
    filter (not ∘ is_lin ∘ snd) (ts'_queue ord) = ts.
  Proof.
    unfold ts'_queue. rewrite insert_lins_in_order_filter_not_lin.
    simpl. apply ts_filter_not_lin_self.
  Qed.

  (* advance_to_call preserves per-tag filter content. *)
  Local Lemma advance_to_call_tag_filter (τ τ' : positive) prefix suffix p s :
    advance_to_call τ' prefix suffix = (p, s) →
    filter (λ x, x.1 = τ) (p ++ s) = filter (λ x, x.1 = τ) (prefix ++ suffix).
  Proof.
    intros Heq. rewrite (advance_to_call_preserves _ _ _ _ _ Heq). done.
  Qed.

  (* insert_one_lin adds at most one Lin (only when τ' = τ) to the per-tag filter. *)
  Local Lemma insert_one_lin_other_tag_filter (τ τ' : positive) v v' prefix suffix p s :
    τ ≠ τ' →
    insert_one_lin τ' v v' prefix suffix = (p, s) →
    filter (λ x, x.1 = τ) (p ++ s) = filter (λ x, x.1 = τ) (prefix ++ suffix).
  Proof.
    intros Hne Heq.
    unfold insert_one_lin in Heq.
    destruct (decide (τ' ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|Hnin].
    - injection Heq as <- <-.
      rewrite -app_assoc. simpl.
      rewrite !filter_app.
      rewrite (filter_cons_False _ (τ', Lin v v') _);
        last (simpl; intros Habs; apply Hne; done).
      done.
    - destruct (advance_to_call τ' prefix suffix) as [p' s'] eqn:Hadv.
      injection Heq as <- <-.
      pose proof (advance_to_call_preserves _ _ _ _ _ Hadv) as Hpres.
      rewrite -app_assoc. simpl.
      rewrite !filter_app.
      rewrite (filter_cons_False _ (τ', Lin v v') _);
        last (simpl; intros Habs; apply Hne; done).
      rewrite -!filter_app Hpres. done.
  Qed.

  (* If τ is not in ord, the fold leaves the tag filter untouched. *)
  Local Lemma insert_lins_in_order_tag_notin_ord (τ : positive) ord' prefix suffix :
    τ ∉ ord' →
    filter (λ x, x.1 = τ) (insert_lins_in_order ord' prefix suffix)
      = filter (λ x, x.1 = τ) (prefix ++ suffix).
  Proof.
    revert prefix suffix. induction ord' as [|τ' rest IH]; intros prefix suffix Hne.
    - simpl. done.
    - apply not_elem_of_cons in Hne as [Hne1 Hne2].
      simpl. destruct (lin_event_val τ') as [v v'] eqn:Hval.
      destruct (insert_one_lin τ' v v' prefix suffix) as [p s] eqn:Heq.
      rewrite IH; last done.
      apply (insert_one_lin_other_tag_filter _ _ _ _ _ _ _ _ Hne1 Heq).
  Qed.

  (* State-tracking helper: returns (p, s) pair through the fold. *)
  Local Fixpoint insert_lins_state (ord : list positive)
      (prefix suffix : list (positive * trace))
      : list (positive * trace) * list (positive * trace) :=
    match ord with
    | [] => (prefix, suffix)
    | τ :: rest =>
      let '(v, v') := lin_event_val τ in
      let '(p, s) := insert_one_lin τ v v' prefix suffix in
      insert_lins_state rest p s
    end.

  Local Lemma insert_lins_in_order_eq_state ord prefix suffix :
    insert_lins_in_order ord prefix suffix =
      (let '(p, s) := insert_lins_state ord prefix suffix in p ++ s).
  Proof.
    revert prefix suffix. induction ord as [|τ rest IH]; intros prefix suffix; first done.
    simpl. destruct (lin_event_val τ) as [v v'].
    destruct (insert_one_lin τ v v' prefix suffix) as [p s].
    apply IH.
  Qed.

  Local Lemma insert_lins_state_app ord1 ord2 prefix suffix :
    insert_lins_state (ord1 ++ ord2) prefix suffix =
      (let '(p, s) := insert_lins_state ord1 prefix suffix in
       insert_lins_state ord2 p s).
  Proof.
    revert prefix suffix. induction ord1 as [|τ rest IH]; intros prefix suffix; first done.
    simpl. destruct (lin_event_val τ) as [v v'].
    destruct (insert_one_lin τ v v' prefix suffix) as [p s].
    apply IH.
  Qed.

  (* For τ ∉ ord, state preserves prefix/suffix combined. *)
  Local Lemma insert_lins_state_notin_preserve (τ : positive) ord' prefix suffix p s :
    τ ∉ ord' →
    insert_lins_state ord' prefix suffix = (p, s) →
    filter (λ x, x.1 = τ) (p ++ s) = filter (λ x, x.1 = τ) (prefix ++ suffix).
  Proof.
    revert prefix suffix p s.
    induction ord' as [|τ' rest IH]; intros prefix suffix p s Hne Hstate.
    - simpl in Hstate. injection Hstate as <- <-. done.
    - apply not_elem_of_cons in Hne as [Hne1 Hne2].
      simpl in Hstate. destruct (lin_event_val τ') as [v v'] eqn:Hval.
      destruct (insert_one_lin τ' v v' prefix suffix) as [p' s'] eqn:Heq.
      rewrite (IH p' s' p s Hne2 Hstate).
      apply (insert_one_lin_other_tag_filter _ _ _ _ _ _ _ _ Hne1 Heq).
  Qed.

  (* advance_to_call preserves suffix-is-drop-tail: if old suffix = drop k l,
     then new suffix = drop k' l for some k' ≥ k. *)
  Local Lemma advance_to_call_suffix_drop τ' l k prefix suffix p s :
    suffix = drop k l →
    advance_to_call τ' prefix suffix = (p, s) →
    ∃ k', k ≤ k' ∧ s = drop k' l.
  Proof.
    revert k prefix. induction suffix as [|[τ'' ev] rest IH]; intros k prefix Hdrop Heq.
    - simpl in Heq. injection Heq as <- <-.
      exists k. split; first done. exact Hdrop.
    - (* suffix = (τ'', ev) :: rest = drop k l.  So rest = drop (S k) l. *)
      assert (Hkl : l !! k = Some (τ'', ev)).
      { apply (f_equal (λ x, x !! 0)) in Hdrop. simpl in Hdrop.
        rewrite lookup_drop Nat.add_0_r in Hdrop. symmetry. exact Hdrop. }
      assert (Hrest : rest = drop (Datatypes.S k) l).
      { pose proof (drop_S _ _ _ Hkl) as Hs.
        rewrite Hs in Hdrop. injection Hdrop. done. }
      destruct ev as [w|vl vl'|r]; simpl in Heq.
      + destruct (decide (τ'' = τ')) as [->|Hne].
        * injection Heq as <- <-.
          exists (Datatypes.S k). split; first lia. exact Hrest.
        * destruct (IH (Datatypes.S k) _ Hrest Heq) as (k' & Hk' & Hs).
          exists k'. split; [lia|exact Hs].
      + destruct (IH (Datatypes.S k) _ Hrest Heq) as (k' & Hk' & Hs).
        exists k'. split; [lia|exact Hs].
      + destruct (IH (Datatypes.S k) _ Hrest Heq) as (k' & Hk' & Hs).
        exists k'. split; [lia|exact Hs].
  Qed.

  (* insert_one_lin preserves suffix-is-drop-tail of ts. *)
  Local Lemma insert_one_lin_suffix_drop τ' v v' k prefix suffix p s :
    suffix = drop k ts →
    insert_one_lin τ' v v' prefix suffix = (p, s) →
    ∃ k', k ≤ k' ∧ s = drop k' ts.
  Proof.
    intros Hdrop Heq.
    unfold insert_one_lin in Heq.
    destruct (decide (τ' ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|Hnin].
    - injection Heq as <- <-. exists k. split; first done. exact Hdrop.
    - destruct (advance_to_call τ' prefix suffix) as [p' s'] eqn:Hadv.
      injection Heq as <- <-.
      by apply (advance_to_call_suffix_drop _ _ _ _ _ _ _ Hdrop) in Hadv.
  Qed.

  Local Lemma insert_lins_state_suffix_drop ord' prefix suffix p s :
    (∃ k, suffix = drop k ts) →
    insert_lins_state ord' prefix suffix = (p, s) →
    ∃ k, s = drop k ts.
  Proof.
    revert prefix suffix p s.
    induction ord' as [|τ' rest IH]; intros prefix suffix p s [k Hdrop] Hstate.
    - simpl in Hstate. injection Hstate as <- <-.
      exists k. exact Hdrop.
    - simpl in Hstate.
      destruct (lin_event_val τ') as [v v'] eqn:Hval.
      destruct (insert_one_lin τ' v v' prefix suffix) as [p' s'] eqn:Heq.
      destruct (insert_one_lin_suffix_drop _ _ _ _ _ _ _ _ Hdrop Heq) as (k' & _ & Hs').
      apply (IH p' s' p s (ex_intro _ k' Hs') Hstate).
  Qed.

  (* Given a trace and positions, the call_of_tag and ret_of_tag positions. *)
  (* For τ ∈ events_of_trace ts with filter (tag=τ) ts = [Call vc; Ret vr],
     these have specific positions (given by list_find). *)

  Local Lemma call_of_tag_pos τ vc vr :
    filter (λ x, x.1 = τ) ts = [(τ, Call vc); (τ, Ret vr)] →
    ∃ cp, call_of_tag ts τ = Some (cp, (τ, Call vc)).
  Proof.
    intros Hfilt.
    assert (Hin : (τ, Call vc) ∈ ts).
    { apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
      rewrite Hfilt. set_solver. }
    pose proof (list_find_elem_of (λ x, x.1 = τ ∧ is_call x.2) ts (τ, Call vc)
      Hin ltac:(split; done)) as Hfind.
    destruct (list_find _ ts) as [[cp [τ'' ev]]|] eqn:Hlf; last by destruct Hfind.
    exists cp. unfold call_of_tag. rewrite Hlf.
    apply list_find_Some in Hlf as (Hlookup & [Htag Hcall] & _).
    simpl in Htag, Hcall. subst τ''.
    destruct ev as [w| |]; [|done|done].
    (* w must equal vc because filter is unique *)
    apply list_elem_of_lookup_2 in Hlookup.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hlookup; last done.
    rewrite Hfilt in Hlookup.
    rewrite !elem_of_cons elem_of_nil in Hlookup.
    destruct Hlookup as [Heq1|[Heq1|Heq1]]; [injection Heq1 as <-; done|discriminate|done].
  Qed.

  Local Lemma ret_of_tag_pos τ vc vr :
    filter (λ x, x.1 = τ) ts = [(τ, Call vc); (τ, Ret vr)] →
    ∃ rp, ret_of_tag ts τ = Some (rp, (τ, Ret vr)).
  Proof.
    intros Hfilt.
    assert (Hin : (τ, Ret vr) ∈ ts).
    { apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
      rewrite Hfilt. set_solver. }
    pose proof (list_find_elem_of (λ x, x.1 = τ ∧ is_ret x.2) ts (τ, Ret vr)
      Hin ltac:(split; done)) as Hfind.
    destruct (list_find _ ts) as [[rp [τ'' ev]]|] eqn:Hlf; last by destruct Hfind.
    exists rp. unfold ret_of_tag. rewrite Hlf.
    apply list_find_Some in Hlf as (Hlookup & [Htag Hret] & _).
    simpl in Htag, Hret. subst τ''.
    destruct ev as [|vl vl'|w]; [done|done|].
    apply list_elem_of_lookup_2 in Hlookup.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hlookup; last done.
    rewrite Hfilt in Hlookup.
    rewrite !elem_of_cons elem_of_nil in Hlookup.
    destruct Hlookup as [Heq1|[Heq1|Heq1]]; [discriminate|injection Heq1 as <-; done|done].
  Qed.

  (* The crux: after processing ord_before, the suffix is `drop k ts` with k ≤ r_τ,
     where r_τ is the position of Ret(τ) in ts.  This is proved by induction on
     ord_before using the prt-sortedness invariant. *)

  (* Helper: for each τ_step ∈ ord_before, c_{τ_step} < r_τ (via prt). *)
  Local Lemma prt_sorted_call_before_ret_pos
      (prt : relation operation)
      (Hsub : subrelation trace_pre prt)
      (Htrans : Transitive prt)
      (Hirr : Irreflexive prt)
      (Hanti : Antisymmetric operation eq prt)
      (τ : positive) (Hτ : τ ∈ events_of_trace ts)
      ord_before ord_after rp vr :
      NoDup (ord_before ++ τ :: ord_after) →
      (∀ τ', τ' ∈ ord_before ++ τ :: ord_after → τ' ∈ events_of_trace ts) →
      (∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
        i < j →
        (ord_before ++ τ :: ord_after) !! i = Some τ1 →
        (ord_before ++ τ :: ord_after) !! j = Some τ2 →
        prt (τ1 ↾ H1) (τ2 ↾ H2)) →
      ret_of_tag ts τ = Some (rp, (τ, Ret vr)) →
      ∀ τ_step c_step ev_step,
        τ_step ∈ ord_before →
        call_of_tag ts τ_step = Some (c_step, (τ_step, Call ev_step)) →
        c_step < rp.
  Proof.
    intros Hnd Hsub_ord Hsorted Hret_τ τ_step c_step ev_step Hstep Hcall_step.
    destruct (decide (c_step < rp)) as [|Hge]; first done.
    exfalso.
    (* c_step ≥ rp. Since they're different, c_step > rp, so rp < c_step.
       By definition of pre_of_trace: trace_pre τ τ_step.
       By Hsub, prt (τ ↾ _) (τ_step ↾ _).
       But τ_step ∈ ord_before, and τ is at position (length ord_before) in ord.
       Prt-sortedness: prt (τ_step ↾ _) (τ ↾ _).
       Contradiction via Transitive + Irreflexive. *)
    assert (Hrp_lt : rp < c_step).
    { destruct (decide (rp = c_step)) as [Heq|Hne]; last lia.
      (* rp = c_step would mean Ret and Call at same position — impossible *)
      subst c_step. apply list_find_Some in Hret_τ as (Hlkr & _ & _).
      apply list_find_Some in Hcall_step as (Hlkc & _ & _).
      rewrite Hlkr in Hlkc. injection Hlkc as Hc1 Hc2. discriminate. }
    (* Now show trace_pre τ τ_step *)
    assert (Hstep_et : τ_step ∈ events_of_trace ts).
    { apply Hsub_ord. apply elem_of_app. left. exact Hstep. }
    assert (Htrace_pre : trace_pre (τ ↾ Hτ) (τ_step ↾ Hstep_et)).
    { unfold trace_pre. simpl. unfold pre_of_trace.
      rewrite Hret_τ Hcall_step /=. exact Hrp_lt. }
    pose proof (Hsub _ _ Htrace_pre) as Hprt_fwd.
    (* Now prt (τ_step ↾ _) (τ ↾ _) via Hsorted *)
    apply list_elem_of_lookup_1 in Hstep as (i & Histep).
    assert (Hpos_τ : (ord_before ++ τ :: ord_after) !! (length ord_before) = Some τ).
    { rewrite lookup_app_r; last lia. replace (length ord_before - length ord_before) with 0 by lia.
      done. }
    assert (Hpos_step : (ord_before ++ τ :: ord_after) !! i = Some τ_step).
    { rewrite lookup_app_l; last (apply lookup_lt_Some in Histep; lia).
      exact Histep. }
    assert (Hi_lt : i < length ord_before) by (apply lookup_lt_Some in Histep; lia).
    pose proof (Hsorted i (length ord_before) τ_step τ Hstep_et Hτ
                        ltac:(lia) Hpos_step Hpos_τ) as Hprt_bwd.
    (* prt (τ ↾ Hτ) (τ_step ↾ Hstep_et) AND prt (τ_step ↾ Hstep_et) (τ ↾ Hτ) *)
    pose proof (Htrans _ _ _ Hprt_fwd Hprt_bwd) as Hcycle.
    apply (Hirr _ Hcycle).
  Qed.

  (* advance_to_call: if Call(τ) is somewhere in the suffix, advance moves it to prefix. *)
  Local Lemma advance_to_call_finds (τ : positive) (prefix suffix : list (positive * trace))
      (p s : list (positive * trace)) :
    advance_to_call τ prefix suffix = (p, s) →
    (∃ v, (τ, Call v) ∈ suffix) →
    ∃ v, (τ, Call v) ∈ p.
  Proof.
    revert prefix. induction suffix as [|[τ'' ev] rest IH]; intros prefix Heq Hex.
    - destruct Hex as [v Hv]. set_solver.
    - destruct ev as [w|vl vl'|r]; simpl in Heq.
      + destruct (decide (τ'' = τ)) as [->|Hne].
        * injection Heq as <- <-. exists w. apply elem_of_app. right. apply elem_of_cons. left. done.
        * destruct Hex as [v Hv].
          apply elem_of_cons in Hv as [Heq'|Hv].
          { injection Heq'. intros. subst. done. }
          destruct (IH _ Heq ltac:(exists v; exact Hv)) as [v2 Hv2].
          exists v2. exact Hv2.
      + destruct Hex as [v Hv]. apply elem_of_cons in Hv as [Heq'|Hv]; first discriminate.
        destruct (IH _ Heq ltac:(exists v; exact Hv)) as [v2 Hv2].
        exists v2. exact Hv2.
      + destruct Hex as [v Hv]. apply elem_of_cons in Hv as [Heq'|Hv]; first discriminate.
        destruct (IH _ Heq ltac:(exists v; exact Hv)) as [v2 Hv2].
        exists v2. exact Hv2.
  Qed.

  (* advance_to_call: when Call(τ) is the FIRST Call(τ) in l at position c,
     and the scan starts at k ≤ c, then after advance the new suffix is drop (c+1) l. *)
  Local Lemma advance_to_call_at_first l τ c vc :
    l !! c = Some (τ, Call vc) →
    (∀ j, j < c → ∀ v, l !! j ≠ Some (τ, Call v)) →
    ∀ k prefix p s, k ≤ c →
    advance_to_call τ prefix (drop k l) = (p, s) →
    s = drop (Datatypes.S c) l.
  Proof.
    intros Hlc Hfirst k prefix p s Hk Heq.
    (* Induct on c - k: the number of elements advance scans before finding Call(τ). *)
    remember (c - k) as n eqn:Hn.
    revert k prefix p s Hk Hn Heq.
    induction n as [|n IH]; intros k prefix p s Hk Hn Heq.
    - (* c - k = 0, so k = c *)
      assert (k = c) by lia. subst k.
      (* suffix = drop c l. By Hlc, drop c l = (τ, Call vc) :: drop (S c) l. *)
      rewrite (drop_S l _ c Hlc) in Heq.
      simpl in Heq.
      destruct (decide (τ = τ)) as [_|Hne]; last done.
      injection Heq as <- <-. done.
    - (* c - k = S n, so k < c *)
      assert (Hklt : k < c) by lia.
      (* l !! k exists and is not Call(τ) *)
      assert (∃ ev, l !! k = Some ev) as [ev Hek].
      { apply lookup_lt_is_Some_2. apply lookup_lt_Some in Hlc. lia. }
      rewrite (drop_S l _ k Hek) in Heq.
      (* advance_to_call τ prefix ((k-th el) :: drop (S k) l) *)
      destruct ev as [τ_k ev_k]. simpl in Heq.
      destruct ev_k as [w|vl vl'|r].
      + (* Call: check if τ_k = τ *)
        destruct (decide (τ_k = τ)) as [->|Hne].
        * (* τ_k = τ: but Hfirst says no Call(τ) before c. k < c and l !! k = Some (τ, Call w) *)
          exfalso. eapply (Hfirst k Hklt). exact Hek.
        * (* τ_k ≠ τ: continue advance *)
          apply (IH (Datatypes.S k) _ _ _ ltac:(lia) ltac:(lia) Heq).
      + apply (IH (Datatypes.S k) _ _ _ ltac:(lia) ltac:(lia) Heq).
      + apply (IH (Datatypes.S k) _ _ _ ltac:(lia) ltac:(lia) Heq).
  Qed.

  (* insert_one_lin case B: when Call(τ) is at position c in ts and k ≤ c,
     the new suffix is drop (c+1) ts. *)
  Local Lemma insert_one_lin_case_b_suffix τ v v' prefix k p s c vc :
    call_of_tag ts τ = Some (c, (τ, Call vc)) →
    τ ∉ (filter (is_call ∘ snd) prefix).*1 →
    k ≤ c →
    insert_one_lin τ v v' prefix (drop k ts) = (p, s) →
    s = drop (Datatypes.S c) ts.
  Proof.
    intros Hcall Hnin Hk Heq.
    unfold insert_one_lin in Heq.
    destruct (decide (τ ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|_]; first done.
    destruct (advance_to_call τ prefix (drop k ts)) as [p' s'] eqn:Hadv.
    injection Heq as <- <-.
    apply list_find_Some in Hcall as (Hlc & [Htag Hcc] & Hfirst).
    simpl in Htag, Hcc. destruct Htag.
    assert (Hnoearlier : ∀ j, j < c → ∀ v0, ts !! j ≠ Some (τ, Call v0)).
    { intros j Hjlt v0 Hjeq.
      apply (Hfirst j (τ, Call v0) Hjeq Hjlt).
      split; [done|simpl; done]. }
    exact (advance_to_call_at_first ts τ c vc Hlc Hnoearlier k prefix p' s' Hk Hadv).
  Qed.

  (* Invariant through the fold: maintains both (a) s = drop k ts, and
     (b) filter (not∘is_lin∘snd) prefix = take k ts.  From (b), Call(τ_step)
     at position c_step < k must be in prefix.  Combined with case B's
     Hnin (Call not in prefix), we get k ≤ c_step. *)
  Local Lemma insert_lins_state_drop_bound (rp : nat) ord' prefix k p s :
    (∀ τ', τ' ∈ ord' →
      ∀ c ev, call_of_tag ts τ' = Some (c, (τ', Call ev)) → c < rp) →
    (∀ τ', τ' ∈ ord' →
      ∃ c ev, call_of_tag ts τ' = Some (c, (τ', Call ev))) →
    k ≤ rp →
    k ≤ length ts →
    filter (not ∘ is_lin ∘ snd) prefix = take k ts →
    insert_lins_state ord' prefix (drop k ts) = (p, s) →
    ∃ k', k' ≤ rp ∧ s = drop k' ts ∧
          filter (not ∘ is_lin ∘ snd) p = take k' ts.
  Proof.
    revert prefix k p s.
    induction ord' as [|τ_step rest IH]; intros prefix k p s Hc_bound Hcall_ex Hk Hk_len Hprefix_filt Hstate.
    - simpl in Hstate. injection Hstate as <- <-.
      exists k. split_and!; done.
    - simpl in Hstate.
      destruct (lin_event_val τ_step) as [v v'] eqn:Hval.
      destruct (insert_one_lin τ_step v v' prefix (drop k ts)) as [p' s'] eqn:Heq.
      unfold insert_one_lin in Heq.
      destruct (decide (τ_step ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|Hnin].
      + (* Case A: s' = drop k ts, k' = k.  prefix grows by Lin event. *)
        injection Heq as <- <-.
        (* Goal: invariants preserved for rest.
           prefix' = prefix ++ [(τ_step, Lin v v')]
           filter not-lin prefix' = filter not-lin prefix = take k ts. *)
        assert (Hprefix'_filt : filter (not ∘ is_lin ∘ snd) (prefix ++ [(τ_step, Lin v v')])
                                = take k ts).
        { rewrite filter_app.
          rewrite (filter_cons_False _ (τ_step, Lin v v')); last (simpl; intros Hlin; apply Hlin; done).
          rewrite filter_nil app_nil_r. exact Hprefix_filt. }
        apply (IH _ _ _ _ (λ τ' Hτ' c ev H, Hc_bound τ' (proj2 (elem_of_cons _ _ _) (or_intror Hτ')) c ev H)
                           (λ τ' Hτ', Hcall_ex τ' (proj2 (elem_of_cons _ _ _) (or_intror Hτ')))
                           Hk Hk_len Hprefix'_filt Hstate).
      + (* Case B *)
        destruct (Hcall_ex τ_step (proj2 (elem_of_cons _ _ _) (or_introl eq_refl))) as (c_step & ev_step & Hcall_step).
        assert (Hc_bound_step : c_step < rp).
        { apply (Hc_bound τ_step (proj2 (elem_of_cons _ _ _) (or_introl eq_refl)) c_step ev_step Hcall_step). }
        (* Prove k ≤ c_step using the prefix filter invariant. *)
        assert (Hk_step : k ≤ c_step).
        { destruct (decide (k ≤ c_step)) as [|Hgt]; first done.
          exfalso. apply Hnin.
          (* Call(τ_step) at position c_step < k in ts is in take k ts,
             hence in filter not-lin prefix = take k ts. *)
          apply list_find_Some in Hcall_step as (Hlc & _ & _).
          assert (Hin_take : (τ_step, Call ev_step) ∈ take k ts).
          { apply list_elem_of_lookup_2 with c_step.
            rewrite lookup_take_lt; [exact Hlc|lia]. }
          rewrite -Hprefix_filt in Hin_take.
          apply list_elem_of_filter in Hin_take as [_ Hin_p].
          apply (list_elem_of_fmap_2 fst _ (τ_step, Call ev_step)).
          apply list_elem_of_filter_2; [done|exact Hin_p]. }
        destruct (advance_to_call τ_step prefix (drop k ts)) as [p_adv s_adv] eqn:Hadv.
        injection Heq as <- <-.
        apply list_find_Some in Hcall_step as (Hlc & [Htag Hcc] & Hfirst).
        simpl in Htag, Hcc. destruct Htag.
        assert (Hnoearlier : ∀ j, j < c_step → ∀ v0, ts !! j ≠ Some (τ_step, Call v0)).
        { intros j Hjlt v0 Hjeq.
          apply (Hfirst j (τ_step, Call v0) Hjeq Hjlt).
          split; [done|simpl; done]. }
        assert (Hs_adv : s_adv = drop (Datatypes.S c_step) ts).
        { exact (advance_to_call_at_first ts τ_step c_step ev_step Hlc Hnoearlier
                  k prefix p_adv s_adv Hk_step Hadv). }
        (* Now s' = drop (S c_step) ts after injection. *)
        (* Also, advance_to_call preserves content: p_adv ++ s_adv = prefix ++ drop k ts *)
        assert (Hcontent : p_adv ++ s_adv = prefix ++ drop k ts).
        { exact (advance_to_call_preserves _ _ _ _ _ Hadv). }
        (* New prefix filter: filter not-lin (p_adv ++ [(τ_step, Lin v v')]) = take (S c_step) ts *)
        assert (Hprefix''_filt :
          filter (not ∘ is_lin ∘ snd) (p_adv ++ [(τ_step, Lin v v')]) = take (Datatypes.S c_step) ts).
        { rewrite filter_app.
          rewrite (filter_cons_False _ (τ_step, Lin v v')); last (simpl; intros Hlin; apply Hlin; done).
          rewrite filter_nil app_nil_r.
          (* filter not-lin p_adv = take (S c_step) ts *)
          assert (Hnolinsfx : filter (not ∘ is_lin ∘ snd) s_adv = s_adv).
          { rewrite Hs_adv. apply filter_all_true.
            apply Forall_forall. intros [τ'' ev''] Hin''.
            unfold compose. simpl.
            destruct ev'' as [r|vl vl'|r].
            - intros Habs. exact Habs.
            - intros _. apply list_elem_of_lookup_1 in Hin'' as [j Hj].
              rewrite lookup_drop in Hj.
              eapply ts_no_lin_event. eapply list_elem_of_lookup_2. exact Hj.
            - intros Habs. exact Habs. }
          assert (Hnolindrop_k : filter (not ∘ is_lin ∘ snd) (drop k ts) = drop k ts).
          { apply filter_all_true.
            apply Forall_forall. intros [τ'' ev''] Hin''.
            unfold compose. simpl.
            destruct ev'' as [r|vl vl'|r].
            - intros Habs. exact Habs.
            - intros _. apply list_elem_of_lookup_1 in Hin'' as [j Hj].
              rewrite lookup_drop in Hj.
              eapply ts_no_lin_event. eapply list_elem_of_lookup_2. exact Hj.
            - intros Habs. exact Habs. }
          apply (f_equal (filter (not ∘ is_lin ∘ snd))) in Hcontent.
          rewrite !filter_app in Hcontent.
          rewrite Hnolinsfx Hnolindrop_k Hprefix_filt in Hcontent.
          rewrite Hs_adv in Hcontent.
          assert (Hts_eq : take k ts ++ drop k ts = take (Datatypes.S c_step) ts ++ drop (Datatypes.S c_step) ts).
          { rewrite !take_drop. done. }
          rewrite Hts_eq in Hcontent.
          assert (Hlen_eq : length (drop (Datatypes.S c_step) ts) = length (drop (Datatypes.S c_step) ts))
            by done.
          apply app_inj_2 in Hcontent as [Hptake _]; [exact Hptake|done].
        }
        (* Now apply IH *)
        assert (Hk'_len : Datatypes.S c_step ≤ length ts).
        { apply lookup_lt_Some in Hlc. lia. }
        assert (Hk'_rp : Datatypes.S c_step ≤ rp) by lia.
        rewrite Hs_adv in Hstate.
        apply (IH _ _ _ _ (λ τ' Hτ' c ev H, Hc_bound τ' (proj2 (elem_of_cons _ _ _) (or_intror Hτ')) c ev H)
                           (λ τ' Hτ', Hcall_ex τ' (proj2 (elem_of_cons _ _ _) (or_intror Hτ')))
                           Hk'_rp Hk'_len Hprefix''_filt Hstate).
  Qed.

  (* Main crux lemma. Extended to expose k such that s = drop k ts and k ≤ rp. *)
  Local Lemma insert_lins_state_process_τ
      (prt : relation operation)
      (Hsub : subrelation trace_pre prt)
      (Htrans : Transitive prt)
      (Hirr : Irreflexive prt)
      (Hanti : Antisymmetric operation eq prt)
      (τ : positive) (Hτ : τ ∈ events_of_trace ts) ord_before ord_after vc vr rp :
      NoDup (ord_before ++ τ :: ord_after) →
      (∀ τ', τ' ∈ ord_before ++ τ :: ord_after → τ' ∈ events_of_trace ts) →
      (∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
        i < j →
        (ord_before ++ τ :: ord_after) !! i = Some τ1 →
        (ord_before ++ τ :: ord_after) !! j = Some τ2 →
        prt (τ1 ↾ H1) (τ2 ↾ H2)) →
      filter (λ x, x.1 = τ) ts = [(τ, Call vc); (τ, Ret vr)] →
      ret_of_tag ts τ = Some (rp, (τ, Ret vr)) →
      ∀ p s,
        insert_lins_state ord_before [] ts = (p, s) →
        filter (λ x, x.1 = τ) (p ++ s) = [(τ, Call vc); (τ, Ret vr)] ∧
        (∃ k, k ≤ rp ∧ s = drop k ts ∧ filter (not ∘ is_lin ∘ snd) p = take k ts) ∧
        (τ, Ret vr) ∈ s.
  Proof.
    intros Hnd Hsub_ord Hsorted Hfilt Hret_τ p s Hstate.
    assert (Hne : τ ∉ ord_before).
    { apply NoDup_app in Hnd. destruct Hnd as (_ & Hne & _).
      intros Hin. apply (Hne τ Hin). apply elem_of_cons. left. done. }
    split.
    { rewrite (insert_lins_state_notin_preserve _ _ _ _ _ _ Hne Hstate).
      simpl. exact Hfilt. }
    (* Apply the drop_bound lemma *)
    assert (Hc_bound : ∀ τ', τ' ∈ ord_before →
      ∀ c ev, call_of_tag ts τ' = Some (c, (τ', Call ev)) → c < rp).
    { intros τ' Hτ'_in c ev Hcall.
      eapply (prt_sorted_call_before_ret_pos prt Hsub Htrans Hirr Hanti
                τ Hτ ord_before ord_after rp vr
                Hnd Hsub_ord Hsorted Hret_τ τ' c ev Hτ'_in Hcall). }
    assert (Hcall_ex : ∀ τ', τ' ∈ ord_before →
      ∃ c ev, call_of_tag ts τ' = Some (c, (τ', Call ev))).
    { intros τ' Hτ'_in.
      assert (Hτ'_ev : τ' ∈ events_of_trace ts).
      { apply Hsub_ord. apply elem_of_app. left. exact Hτ'_in. }
      destruct (Hcomplete τ') as (vc' & vr' & [Hempty|Hfilt']).
      { exfalso. unfold events_of_trace in Hτ'_ev.
        apply elem_of_list_to_set in Hτ'_ev.
        apply list_elem_of_fmap_1 in Hτ'_ev as ([τ'' ev''] & Heq & Hin'').
        simpl in Heq. subst τ''.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ')) in Hin'' as Hfilt_in; last done.
        rewrite Hempty in Hfilt_in. set_solver. }
      destruct (call_of_tag_pos τ' vc' vr' Hfilt') as (c & Hcall).
      exists c, vc'. exact Hcall. }
    assert (Hrp_lt_len : rp < length ts).
    { apply list_find_Some in Hret_τ as (Hlkr & _ & _).
      apply lookup_lt_Some in Hlkr. exact Hlkr. }
    destruct (insert_lins_state_drop_bound rp ord_before [] 0 p s
                Hc_bound Hcall_ex ltac:(lia) ltac:(lia)
                ltac:(simpl; done) Hstate) as (k' & Hk'_le & Hs_eq & Hp_filt).
    split.
    { exists k'. split_and!; done. }
    rewrite Hs_eq.
    apply list_elem_of_lookup_2 with (rp - k').
    rewrite lookup_drop.
    apply list_find_Some in Hret_τ as (Hlkr & _ & _).
    replace (k' + (rp - k')) with rp by lia.
    exact Hlkr.
  Qed.

  (* Helper: c < rp when filter ts = [Call vc; Ret vr].
     Uses the minimality property of list_find. *)
  Local Lemma call_lt_ret_pos τ vc vr c rp :
    filter (λ x, x.1 = τ) ts = [(τ, Call vc); (τ, Ret vr)] →
    call_of_tag ts τ = Some (c, (τ, Call vc)) →
    ret_of_tag ts τ = Some (rp, (τ, Ret vr)) →
    c < rp.
  Proof.
    intros Hfilt Hcall Hret.
    pose proof Hcall as Hcall_full.
    pose proof Hret as Hret_full.
    apply list_find_Some in Hcall as (Hlc & _ & Hcall_min).
    apply list_find_Some in Hret as (Hlr & _ & Hret_min).
    destruct (decide (c < rp)) as [|Hge]; first done.
    exfalso.
    destruct (decide (c = rp)) as [->|Hne].
    - rewrite Hlc in Hlr. injection Hlr as Hbad. discriminate.
    - assert (Hlt : rp < c) by lia.
      assert (Hret_in_take : (τ, Ret vr) ∈ take (Datatypes.S rp) ts).
      { eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hlr|lia]. }
      assert (Hcall_nin_take : (τ, Call vc) ∉ take (Datatypes.S rp) ts).
      { intros Hin'. apply list_elem_of_lookup_1 in Hin' as [j Hj].
        apply lookup_take_Some in Hj as [Hj_ts Hj_lt].
        apply (Hcall_min j (τ, Call vc) Hj_ts ltac:(lia)).
        split; [done|simpl; done]. }
      assert (Hpfx_filt : filter (λ x, x.1 = τ) (take (Datatypes.S rp) ts)
                          `prefix_of` filter (λ x, x.1 = τ) ts).
      { apply prefix_filter. exists (drop (Datatypes.S rp) ts). symmetry. apply take_drop. }
      rewrite Hfilt in Hpfx_filt.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hret_in_take as Hret_in_filt; last done.
      destruct Hpfx_filt as [sfx Hsfx].
      destruct (filter (λ x, x.1 = τ) (take (Datatypes.S rp) ts)) as [|x1 [|x2 rest]] eqn:Hfeq.
      + set_solver.
      + rewrite elem_of_cons elem_of_nil in Hret_in_filt.
        destruct Hret_in_filt as [Heq'|[]]. subst x1.
        simpl in Hsfx. injection Hsfx as Hxx _. discriminate.
      + simpl in Hsfx. injection Hsfx as <- <- Hrest.
        apply Hcall_nin_take.
        apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
        rewrite Hfeq. apply elem_of_cons. left. done.
  Qed.

  Local Lemma ts'_queue_per_tag_linearized
      (prt : relation operation)
      (Hsub : subrelation trace_pre prt)
      (Htrans : Transitive prt)
      (Hirr : Irreflexive prt)
      (Hanti : Antisymmetric operation eq prt)
      ord
      (Hord : ∀ τ, τ ∈ ord ↔ τ ∈ events_of_trace ts)
      (Hnd : NoDup ord)
      (Hord_sorted : ∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
        i < j → ord !! i = Some τ1 → ord !! j = Some τ2 →
        prt (τ1 ↾ H1) (τ2 ↾ H2)) :
    per_tag_linearized (ts'_queue ord).
  Proof.
    intros τ.
    destruct (decide (τ ∈ ord)) as [Hin_ord|Hnin_ord]; last first.
    { (* τ ∉ ord: no Lin for τ added; filter (tag=τ) (ts'_queue ord) = filter (tag=τ) ts *)
      unfold ts'_queue.
      rewrite (insert_lins_in_order_tag_notin_ord _ _ _ _ Hnin_ord).
      simpl.
      destruct (Hcomplete τ) as (vc & vr & [Hfilt|Hfilt]).
      - exists vc, vr. rewrite Hfilt. apply prefix_nil.
      - exfalso.
        apply Hnin_ord. apply Hord.
        unfold events_of_trace. apply elem_of_list_to_set.
        apply (list_elem_of_fmap_2 fst _ (τ, Call vc)).
        apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
        rewrite Hfilt. set_solver. }
    (* τ ∈ ord *)
    apply Hord in Hin_ord as Hin_et.
    destruct (Hcomplete τ) as (vc & vr & [Hempty|Hfilt]).
    { exfalso.
      unfold events_of_trace in Hin_et.
      apply elem_of_list_to_set in Hin_et.
      apply list_elem_of_fmap_1 in Hin_et as ([τ' ev] & Heq & Hin_ts).
      simpl in Heq. subst τ'.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin_ts as Hin_τ; last done.
      rewrite Hempty in Hin_τ. set_solver. }
    exists vc, vr.
    (* Split ord at τ *)
    apply list_elem_of_split in Hin_ord as (ord_before & ord_after & Hord_split).
    (* Unfold *)
    unfold ts'_queue.
    rewrite insert_lins_in_order_eq_state.
    rewrite Hord_split.
    rewrite insert_lins_state_app.
    destruct (insert_lins_state ord_before [] ts) as [p1 s1] eqn:Hstate1.
    (* Apply process_τ to establish filter=[Call;Ret] and Ret∈s1 *)
    assert (Hnd' : NoDup (ord_before ++ τ :: ord_after)) by (by rewrite <-Hord_split).
    assert (Hsub_ord : ∀ τ', τ' ∈ ord_before ++ τ :: ord_after → τ' ∈ events_of_trace ts).
    { intros τ'' Hτ''. apply Hord. rewrite Hord_split. exact Hτ''. }
    assert (Hsorted' : ∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
      i < j →
      (ord_before ++ τ :: ord_after) !! i = Some τ1 →
      (ord_before ++ τ :: ord_after) !! j = Some τ2 →
      prt (τ1 ↾ H1) (τ2 ↾ H2)).
    { intros i j τ1 τ2 H1 H2 Hij Hi Hj.
      apply (Hord_sorted i j τ1 τ2 H1 H2 Hij).
      - rewrite Hord_split. exact Hi.
      - rewrite Hord_split. exact Hj. }
    destruct (ret_of_tag_pos τ vc vr Hfilt) as (rp & Hret_τ).
    destruct (call_of_tag_pos τ vc vr Hfilt) as (c_τ & Hcall_τ).
    pose proof (call_lt_ret_pos τ vc vr c_τ rp Hfilt Hcall_τ Hret_τ) as Hc_lt_rp.
    destruct (insert_lins_state_process_τ prt Hsub Htrans Hirr Hanti
                τ Hin_et ord_before ord_after vc vr rp
                Hnd' Hsub_ord Hsorted' Hfilt Hret_τ _ _ Hstate1)
      as (Hfilt1 & (k1 & Hk1_le & Hs1_eq & Hp1_filt) & Hret_s1).
    (* Process τ: simpl should unfold the cons case *)
    simpl.
    rewrite (lin_event_val_of τ vc vr Hfilt).
    destruct (insert_one_lin τ vc vr p1 s1) as [p2 s2] eqn:Hstate2.
    assert (Hfilt2 : filter (λ x, x.1 = τ) (p2 ++ s2) = [(τ, Call vc); (τ, Lin vc vr); (τ, Ret vr)]).
    { (* Use advance_to_call_at_first to fully characterize s_adv and p_adv filter. *)
      unfold insert_one_lin in Hstate2.
      destruct (decide (τ ∈ (filter (is_call ∘ snd) p1).*1)) as [Hin|Hnin].
      - (* Case A: Call(τ) ∈ p1. *)
        injection Hstate2 as <- <-.
        (* Show filter p1 = [Call vc] and filter s1 = [Ret vr] *)
        assert (Hcall_in_p1 : (τ, Call vc) ∈ p1).
        { apply list_elem_of_fmap_1 in Hin as ([τ'' ev''] & Heq & Hin_p1).
          simpl in Heq. subst τ''.
          apply list_elem_of_filter in Hin_p1 as [Hcall Hin_p1].
          destruct ev'' as [w| |]; simpl in Hcall; try done.
          (* (τ, Call w) ∈ p1 ⊆ non-Lin events of p1 ⊆ take k1 ts by invariant.
             In ts, Call(τ) at unique position c_τ with value vc. So w = vc. *)
          assert (Hin_nlp1 : (τ, Call w) ∈ filter (not ∘ is_lin ∘ snd) p1).
          { apply list_elem_of_filter_2; [intros Habs; exact Habs|exact Hin_p1]. }
          rewrite Hp1_filt in Hin_nlp1.
          apply list_elem_of_lookup_1 in Hin_nlp1 as [j Hj].
          apply lookup_take_Some in Hj as [Hj_ts _].
          (* ts !! j = Some (τ, Call w).  filter (tag=τ) ts = [Call vc; Ret vr].
             So (τ, Call w) ∈ filter = {Call vc, Ret vr}.  Since Call w ≠ Ret vr (different ctors),
             Call w = Call vc, so w = vc. *)
          assert (Hin_filt_ts : (τ, Call w) ∈ filter (λ x, x.1 = τ) ts).
          { apply list_elem_of_filter_2; [done|].
            eapply list_elem_of_lookup_2. exact Hj_ts. }
          rewrite Hfilt in Hin_filt_ts.
          rewrite !elem_of_cons elem_of_nil in Hin_filt_ts.
          destruct Hin_filt_ts as [Heq'|[Heq'|[]]]; [injection Heq' as <-|discriminate].
          exact Hin_p1. }
        assert (Hret_nin_p1 : (τ, Ret vr) ∉ p1).
        { intros HRet_p1.
          assert (Hin_nlp1 : (τ, Ret vr) ∈ filter (not ∘ is_lin ∘ snd) p1).
          { apply list_elem_of_filter_2; [intros Habs; exact Habs|exact HRet_p1]. }
          rewrite Hp1_filt in Hin_nlp1.
          apply list_elem_of_lookup_1 in Hin_nlp1 as [j Hj].
          apply lookup_take_Some in Hj as [Hj_ts Hj_lt].
          (* ts !! j = Some (τ, Ret vr) with j < k1 ≤ rp.  But ret_of_tag says first Ret(τ) at rp. *)
          apply list_find_Some in Hret_τ as (_ & _ & Hret_min).
          apply (Hret_min j (τ, Ret vr) Hj_ts ltac:(lia)).
          split; [done|simpl; done]. }
        assert (Hfilt_p1 : filter (λ x, x.1 = τ) p1 = [(τ, Call vc)]).
        { (* Has Call vc, doesn't have Ret vr. filter p1 ⊆ filter (p1 ++ s1) = [Call; Ret].
             filter p1 contains Call, not Ret.  So filter p1 = [Call vc]. *)
          rewrite filter_app in Hfilt1.
          apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hcall_in_p1 as Hc_f; last done.
          destruct (filter (λ x, x.1 = τ) p1) as [|x1 [|x2 rest]] eqn:Hfp.
          - set_solver.
          - rewrite elem_of_cons elem_of_nil in Hc_f.
            destruct Hc_f as [<-|[]]. simpl in Hfilt1.
            injection Hfilt1 as Heq. done.
          - exfalso.
            apply (f_equal length) in Hfilt1.
            rewrite !length_app /= in Hfilt1.
            apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hret_s1; last done.
            apply list_elem_of_lookup_1 in Hret_s1 as [i_s Hisq].
            apply lookup_lt_Some in Hisq. lia. }
        assert (Hfilt_s1 : filter (λ x, x.1 = τ) s1 = [(τ, Ret vr)]).
        { rewrite filter_app Hfilt_p1 in Hfilt1.
          simpl in Hfilt1. injection Hfilt1 as Hfilt1. exact Hfilt1. }
        rewrite !filter_app Hfilt_p1 Hfilt_s1.
        rewrite (filter_cons_True _ (τ, Lin vc vr) _); last done.
        rewrite filter_nil. done.
      - (* Case B: Call(τ) ∉ p1. *)
        destruct (advance_to_call τ p1 s1) as [p_adv s_adv] eqn:Hadv.
        injection Hstate2 as <- <-.
        (* Prove k1 ≤ c_τ: if k1 > c_τ, Call is in take k1 ts = filter not-lin p1, hence in p1. *)
        assert (Hk1_le_c : k1 ≤ c_τ).
        { destruct (decide (k1 ≤ c_τ)) as [|Hgt]; first done.
          exfalso. apply Hnin.
          apply list_find_Some in Hcall_τ as (Hlc & _ & _).
          assert (Hcall_in_take : (τ, Call vc) ∈ take k1 ts).
          { apply list_elem_of_lookup_2 with c_τ.
            rewrite lookup_take_lt; [exact Hlc|lia]. }
          rewrite -Hp1_filt in Hcall_in_take.
          apply list_elem_of_filter_1 in Hcall_in_take.
          apply (list_elem_of_fmap_2 fst _ (τ, Call vc)).
          apply list_elem_of_filter_2; [done|exact Hcall_in_take]. }
        (* s_adv = drop (S c_τ) ts via advance_to_call_at_first *)
        apply list_find_Some in Hcall_τ as (Hlc & _ & Hcall_min).
        assert (Hnoearlier : ∀ j, j < c_τ → ∀ v0, ts !! j ≠ Some (τ, Call v0)).
        { intros j Hjlt v0 Hjeq.
          apply (Hcall_min j (τ, Call v0) Hjeq Hjlt).
          split; [done|simpl; done]. }
        assert (Hs_adv_eq : s_adv = drop (Datatypes.S c_τ) ts).
        { rewrite Hs1_eq in Hadv.
          exact (advance_to_call_at_first ts τ c_τ vc Hlc Hnoearlier
                  k1 p1 p_adv s_adv Hk1_le_c Hadv). }
        (* Compute filter (tag=τ) of take (S c_τ) ts: it's exactly [(τ, Call vc)].
           Then filter (tag=τ) (drop (S c_τ) ts) = [(τ, Ret vr)] by filter_app on ts. *)
        assert (Hfilt_take_Sct : filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts)
                                  = [(τ, Call vc)]).
        { (* take (S c_τ) ts has tag-τ elements only from call at c_τ.
             No Call(τ) before c_τ (Hcall_min / Hnoearlier).  No Ret(τ) before c_τ
             (Ret at rp > c_τ). *)
          apply list_find_Some in Hret_τ as (Hlr & _ & Hret_min).
          (* Call vc is at position c_τ < S c_τ, so in take (S c_τ) ts. *)
          assert (Hcall_in_take : (τ, Call vc) ∈ take (Datatypes.S c_τ) ts).
          { apply list_elem_of_lookup_2 with c_τ.
            rewrite lookup_take_lt; [exact Hlc|lia]. }
          (* No other tag-τ element in take (S c_τ) ts. *)
          assert (Hno_other : ∀ y, y ∈ take (Datatypes.S c_τ) ts → y.1 = τ → y = (τ, Call vc)).
          { intros [τ'' ev''] Hin Htag. simpl in Htag. subst τ''.
            apply list_elem_of_lookup_1 in Hin as [j Hj].
            apply lookup_take_Some in Hj as [Hj_ts Hj_lt].
            (* ts !! j = Some (τ, ev'') with j < S c_τ, i.e., j ≤ c_τ. *)
            destruct ev'' as [w|vl vl'|r].
            - (* Call: by Hcall_min and j ≤ c_τ, j < c_τ impossible (would contradict Hcall_min).
                 So j = c_τ, then ts !! c_τ = Some (τ, Call w) and also = Some (τ, Call vc).
                 So w = vc. *)
              destruct (decide (j < c_τ)) as [Hjlt|Hjge].
              + exfalso. apply (Hcall_min j (τ, Call w) Hj_ts Hjlt).
                split; [done|simpl; done].
              + assert (j = c_τ) by lia. subst j.
                rewrite Hj_ts in Hlc. injection Hlc as Hw. congruence.
            - (* Lin: doesn't happen in ts *)
              exfalso. eapply ts_no_lin_event.
              eapply list_elem_of_lookup_2. exact Hj_ts.
            - (* Ret: at position j, but Ret at rp > c_τ ≥ j. Contradiction via Hret_min. *)
              exfalso. apply (Hret_min j (τ, Ret r) Hj_ts ltac:(lia)).
              split; [done|simpl; done]. }
          (* So filter = [Call vc] *)
          destruct (filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts)) as [|z1 [|z2 rest_z]] eqn:Hftake.
          - exfalso. apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hcall_in_take; last done.
            rewrite Hftake in Hcall_in_take. set_solver.
          - assert (Hz1_in : z1 ∈ filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts)).
            { rewrite Hftake. apply elem_of_cons. left. done. }
            apply list_elem_of_filter in Hz1_in as [Hz1_tag Hz1_in_take].
            assert (Hz1_eq : z1 = (τ, Call vc)).
            { apply Hno_other; assumption. }
            subst z1. done.
          - (* ≥ 2 elements.  z2 must be (τ, Call vc) by Hno_other.  But then filter has two
               copies of (τ, Call vc), meaning Call vc appears at 2+ positions in take.  But
               Call vc appears at most once in ts (uniqueness from Hcall_min). *)
            exfalso.
            (* filter has z1 and z2, both ≠ Ret vr (they're tag-τ elements of take).
               By Hno_other, both equal (τ, Call vc). *)
            assert (Hz1_in_filt : z1 ∈ filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts)).
            { rewrite Hftake. apply elem_of_cons. left. done. }
            assert (Hz2_in_filt : z2 ∈ filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts)).
            { rewrite Hftake. apply elem_of_cons. right. apply elem_of_cons. left. done. }
            apply list_elem_of_filter in Hz1_in_filt as [Hz1_tag Hz1_tk].
            apply list_elem_of_filter in Hz2_in_filt as [Hz2_tag Hz2_tk].
            simpl in Hz1_tag, Hz2_tag.
            pose proof (Hno_other z1 Hz1_tk Hz1_tag) as Hz1_eq.
            pose proof (Hno_other z2 Hz2_tk Hz2_tag) as Hz2_eq.
            subst z1 z2.
            (* (τ, Call vc) appears at 2+ positions in take (S c_τ) ts (corresponding to
               filter indices 0 and 1). *)
            apply list_elem_of_lookup_1 in Hz1_tk as [j1 Hj1].
            apply list_elem_of_lookup_1 in Hz2_tk as [j2 Hj2].
            apply lookup_take_Some in Hj1 as [Hj1_ts Hj1_lt].
            apply lookup_take_Some in Hj2 as [Hj2_ts Hj2_lt].
            assert (Hj1_eq : j1 = c_τ).
            { destruct (decide (j1 < c_τ)) as [Hlt|Hge].
              - exfalso. apply (Hcall_min j1 (τ, Call vc) Hj1_ts Hlt).
                split; [done|simpl; done].
              - lia. }
            assert (Hj2_eq : j2 = c_τ).
            { destruct (decide (j2 < c_τ)) as [Hlt|Hge].
              - exfalso. apply (Hcall_min j2 (τ, Call vc) Hj2_ts Hlt).
                split; [done|simpl; done].
              - lia. }
            subst j1 j2.
            assert (Hoccurs_once : ∀ j j', take (Datatypes.S c_τ) ts !! j = Some (τ, Call vc) →
                                           take (Datatypes.S c_τ) ts !! j' = Some (τ, Call vc) →
                                           j = j').
            { intros j j' Hj Hj'.
              apply lookup_take_Some in Hj as [Hj_ts Hj_lt].
              apply lookup_take_Some in Hj' as [Hj'_ts Hj'_lt].
              assert (j = c_τ).
              { destruct (decide (j < c_τ)) as [Hlt|Hge].
                - exfalso. apply (Hcall_min j (τ, Call vc) Hj_ts Hlt).
                  split; [done|simpl; done].
                - lia. }
              assert (j' = c_τ).
              { destruct (decide (j' < c_τ)) as [Hlt|Hge].
                - exfalso. apply (Hcall_min j' (τ, Call vc) Hj'_ts Hlt).
                  split; [done|simpl; done].
                - lia. }
              lia. }
            (* Now filter has (τ, Call vc) at filter-positions 0 and 1.  By filter_preserves_order_gen,
               get distinct ts positions.  But Hoccurs_once says same position.  Contradiction. *)
            (* filter_preserves_order_gen isn't in our toolkit directly; let me use list_filter_lookup_orig twice. *)
            assert (Hf0 : filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts) !! 0 = Some (τ, Call vc)).
            { rewrite Hftake. done. }
            assert (Hf1 : filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts) !! 1 = Some (τ, Call vc)).
            { rewrite Hftake. done. }
            pose proof (filter_NoDup_at (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts) (τ, Call vc) 0 1
                          Hf0 Hf1 eq_refl Hoccurs_once) as Habs.
            discriminate Habs. }
        assert (Hfilt_s_adv : filter (λ x, x.1 = τ) s_adv = [(τ, Ret vr)]).
        { rewrite Hs_adv_eq.
          (* filter ts = filter (take (S c_τ) ts) ++ filter (drop (S c_τ) ts) *)
          assert (Hfilt_split : filter (λ x, x.1 = τ) ts =
            filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts) ++
            filter (λ x, x.1 = τ) (drop (Datatypes.S c_τ) ts)).
          { rewrite -filter_app take_drop. done. }
          rewrite Hfilt Hfilt_take_Sct /= in Hfilt_split.
          injection Hfilt_split. done. }
        (* filter (tag=τ) p_adv: from Hpres, filter (p_adv ++ s_adv) = filter (p1 ++ s1) = filter (tag=τ) ts = [Call; Ret].
           Subtract filter s_adv = [Ret]: filter p_adv = [Call]. *)
        pose proof (advance_to_call_preserves _ _ _ _ _ Hadv) as Hpres.
        assert (Hfilt_p_adv : filter (λ x, x.1 = τ) p_adv = [(τ, Call vc)]).
        { (* filter (tag=τ) (p_adv ++ s_adv) = filter (tag=τ) (p1 ++ s1) = [Call vc; Ret vr] *)
          apply (f_equal (filter (λ x, x.1 = τ))) in Hpres.
          assert (Hfilt_adv_union : filter (λ x, x.1 = τ) (p_adv ++ s_adv)
                                      = [(τ, Call vc); (τ, Ret vr)]).
          { rewrite Hpres. exact Hfilt1. }
          rewrite filter_app Hfilt_s_adv in Hfilt_adv_union.
          (* filter p_adv ++ [Ret vr] = [Call vc; Ret vr], so filter p_adv = [Call vc]. *)
          destruct (filter (λ x, x.1 = τ) p_adv) as [|z1 [|z2 rest]] eqn:Hfpa.
          - simpl in Hfilt_adv_union. discriminate.
          - simpl in Hfilt_adv_union.
            by inversion Hfilt_adv_union.
          - exfalso. apply (f_equal length) in Hfilt_adv_union.
            rewrite !length_app /= in Hfilt_adv_union. simpl in Hfilt_adv_union. lia. }
        rewrite !filter_app Hfilt_p_adv Hfilt_s_adv.
        rewrite (filter_cons_True _ (τ, Lin vc vr) _); last done.
        rewrite filter_nil. done. }
    (* Now process ord_after: τ ∉ ord_after, so filter (tag=τ) unchanged. *)
    assert (Hne_after : τ ∉ ord_after).
    { intros Hτ_in_after.
      apply NoDup_app in Hnd'. destruct Hnd' as (_ & _ & Hnd_cons).
      rewrite NoDup_cons in Hnd_cons. destruct Hnd_cons as [Hne_τ _].
      apply Hne_τ. exact Hτ_in_after. }
    destruct (insert_lins_state ord_after p2 s2) as [p_final s_final] eqn:Hstate_final.
    rewrite (insert_lins_state_notin_preserve _ _ _ _ _ _ Hne_after Hstate_final).
    rewrite Hfilt2.
    exists []. simpl. done.
  Qed.

  (* advance_to_call preserves the property that the suffix has no Lin events. *)
  Local Lemma advance_to_call_suffix_no_lin τ prefix suffix :
    filter (is_lin ∘ snd) suffix = [] →
    ∀ p s, advance_to_call τ prefix suffix = (p, s) →
    filter (is_lin ∘ snd) s = [].
  Proof.
    revert prefix. induction suffix as [|[τ' ev] rest IH]; intros prefix Hlin p s Heq.
    - simpl in Heq. injection Heq as <- <-. done.
    - destruct ev as [v'|vl vl'|r].
      + simpl in Heq. destruct (decide (τ' = τ)) as [->|Hne].
        * injection Heq as <- <-.
          rewrite filter_cons_False in Hlin; last by simpl; intros [].
          exact Hlin.
        * rewrite filter_cons_False in Hlin; last by simpl; intros [].
          eapply IH; [exact Hlin|exact Heq].
      + rewrite filter_cons_True in Hlin; last by simpl.
        discriminate.
      + simpl in Heq.
        rewrite filter_cons_False in Hlin; last by simpl; intros [].
        eapply IH; [exact Hlin|exact Heq].
  Qed.

  (* advance_to_call appends to prefix only non-Lin events from suffix. *)
  Local Lemma advance_to_call_prefix_lin τ prefix suffix :
    filter (is_lin ∘ snd) suffix = [] →
    ∀ p s, advance_to_call τ prefix suffix = (p, s) →
    filter (is_lin ∘ snd) p = filter (is_lin ∘ snd) prefix.
  Proof.
    revert prefix. induction suffix as [|[τ' ev] rest IH]; intros prefix Hlin p s Heq.
    - simpl in Heq. injection Heq as <- <-. done.
    - destruct ev as [v'|vl vl'|r].
      + simpl in Heq. destruct (decide (τ' = τ)) as [->|Hne].
        * injection Heq as <- <-.
          rewrite filter_app. simpl.
          rewrite filter_cons_False; last by simpl; intros [].
          by rewrite filter_nil app_nil_r.
        * rewrite filter_cons_False in Hlin; last by simpl; intros [].
          apply IH in Heq; last exact Hlin.
          rewrite Heq filter_app. simpl.
          rewrite filter_cons_False; last by simpl; intros [].
          by rewrite filter_nil app_nil_r.
      + rewrite filter_cons_True in Hlin; last by simpl. discriminate.
      + simpl in Heq.
        rewrite filter_cons_False in Hlin; last by simpl; intros [].
        apply IH in Heq; last exact Hlin.
        rewrite Heq filter_app. simpl.
        rewrite filter_cons_False; last by simpl; intros [].
        by rewrite filter_nil app_nil_r.
  Qed.

  (* After insert_one_lin: suffix stays Lin-free; prefix gains one Lin for τ. *)
  Local Lemma insert_one_lin_lin_subseq τ v v' prefix suffix :
    filter (is_lin ∘ snd) suffix = [] →
    ∀ p s, insert_one_lin τ v v' prefix suffix = (p, s) →
    filter (is_lin ∘ snd) s = [] ∧
    (filter (is_lin ∘ snd) p).*1
      = (filter (is_lin ∘ snd) prefix).*1 ++ [τ].
  Proof.
    intros Hlin p s Heq.
    unfold insert_one_lin in Heq.
    assert (Hsingle : filter (is_lin ∘ snd) [(τ, Lin v v')] = [(τ, Lin v v')]).
    { rewrite filter_cons_True; last by simpl. by rewrite filter_nil. }
    destruct (decide (τ ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|Hnin].
    - injection Heq as <- <-. split; first exact Hlin.
      rewrite filter_app Hsingle fmap_app. done.
    - destruct (advance_to_call τ prefix suffix) as [p' s'] eqn:Hadv.
      injection Heq as <- <-.
      split.
      + eapply advance_to_call_suffix_no_lin; [exact Hlin|exact Hadv].
      + rewrite filter_app Hsingle fmap_app.
        f_equal.
        pose proof (advance_to_call_prefix_lin _ _ _ Hlin _ _ Hadv) as Hp'.
        by rewrite Hp'.
  Qed.

  (* The core inductive lemma: after processing ord, the Lin subsequence
     equals (prefix Lins) ++ ord. *)
  Local Lemma insert_lins_in_order_lin_subseq ord prefix suffix :
    filter (is_lin ∘ snd) suffix = [] →
    (filter (is_lin ∘ snd) (insert_lins_in_order ord prefix suffix)).*1
      = (filter (is_lin ∘ snd) prefix).*1 ++ ord.
  Proof.
    revert prefix suffix. induction ord as [|τ rest IH]; intros prefix suffix Hlin.
    - simpl. rewrite app_nil_r filter_app Hlin app_nil_r. done.
    - simpl. destruct (lin_event_val τ) as [v v'] eqn:Hval.
      destruct (insert_one_lin τ v v' prefix suffix) as [p s] eqn:Heq.
      pose proof (insert_one_lin_lin_subseq _ _ _ _ _ Hlin _ _ Heq) as [Hs_lin Hp_lin].
      rewrite IH; last exact Hs_lin.
      rewrite Hp_lin.
      by rewrite -app_assoc.
  Qed.

  Local Lemma ts_filter_lin_empty :
    filter (is_lin ∘ snd) ts = [].
  Proof.
    apply (nil_length_inv).
    destruct (filter (is_lin ∘ snd) ts) as [|hd tl] eqn:Heq; first done.
    exfalso.
    assert (Hin : hd ∈ filter (is_lin ∘ snd) ts).
    { rewrite Heq. apply elem_of_cons. left. done. }
    apply list_elem_of_filter in Hin as [Hlin Hin_ts].
    destruct hd as [τ ev]. simpl in Hlin.
    destruct ev; [done| |done].
    eapply ts_no_lin_event. exact Hin_ts.
  Qed.

  Local Lemma ts'_queue_lin_filter ord
      (Hord : ∀ τ, τ ∈ ord ↔ τ ∈ events_of_trace ts)
      (Hnd : NoDup ord) :
    (filter (is_lin ∘ snd) (ts'_queue ord)).*1 = ord.
  Proof.
    unfold ts'_queue.
    rewrite insert_lins_in_order_lin_subseq; last exact ts_filter_lin_empty.
    simpl. done.
  Qed.

  (* ===== Stronger: the full Lin-event filter list ===== *)
  Local Definition lin_events_of_ord (ord : list positive) : list (positive * trace) :=
    map (λ τ, (τ, Lin (lin_event_val τ).1 (lin_event_val τ).2)) ord.

  Local Lemma insert_one_lin_lin_events τ v v' prefix suffix p s :
    filter (is_lin ∘ snd) suffix = [] →
    insert_one_lin τ v v' prefix suffix = (p, s) →
    filter (is_lin ∘ snd) p = filter (is_lin ∘ snd) prefix ++ [(τ, Lin v v')].
  Proof.
    intros Hlin Heq.
    unfold insert_one_lin in Heq.
    assert (Hlin_single : filter (is_lin ∘ snd) [(τ, Lin v v')] = [(τ, Lin v v')]).
    { rewrite filter_cons_True; last by simpl. by rewrite filter_nil. }
    destruct (decide (τ ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|Hnin].
    - injection Heq as <- <-.
      rewrite filter_app Hlin_single. done.
    - destruct (advance_to_call τ prefix suffix) as [p' s'] eqn:Hadv.
      injection Heq as <- <-.
      rewrite filter_app Hlin_single.
      f_equal.
      pose proof (advance_to_call_preserves _ _ _ _ _ Hadv) as Hpres.
      apply (f_equal (filter (is_lin ∘ snd))) in Hpres.
      rewrite !filter_app in Hpres.
      pose proof (advance_to_call_suffix_no_lin _ _ _ Hlin _ _ Hadv) as Hs'_lin.
      rewrite Hs'_lin Hlin !app_nil_r in Hpres.
      exact Hpres.
  Qed.

  Local Lemma insert_lins_in_order_lin_events ord prefix suffix :
    filter (is_lin ∘ snd) suffix = [] →
    filter (is_lin ∘ snd) (insert_lins_in_order ord prefix suffix)
      = filter (is_lin ∘ snd) prefix ++ lin_events_of_ord ord.
  Proof.
    revert prefix suffix. induction ord as [|τ rest IH]; intros prefix suffix Hlin.
    - simpl. rewrite app_nil_r filter_app Hlin app_nil_r. done.
    - simpl. destruct (lin_event_val τ) as [v v'] eqn:Hval.
      destruct (insert_one_lin τ v v' prefix suffix) as [p s] eqn:Heq.
      pose proof (insert_one_lin_lin_events _ _ _ _ _ _ _ Hlin Heq) as Hp_lin.
      pose proof (insert_one_lin_lin_subseq _ _ _ _ _ Hlin _ _ Heq) as [Hs_lin _].
      rewrite IH; last exact Hs_lin.
      rewrite Hp_lin.
      unfold lin_events_of_ord. simpl map.
      replace ((lin_event_val τ).1) with v by (rewrite Hval; done).
      replace ((lin_event_val τ).2) with v' by (rewrite Hval; done).
      by rewrite -app_assoc.
  Qed.

  Local Lemma ts'_queue_lin_filter_events ord :
    filter (is_lin ∘ snd) (ts'_queue ord) = lin_events_of_ord ord.
  Proof.
    unfold ts'_queue.
    rewrite insert_lins_in_order_lin_events; last exact ts_filter_lin_empty.
    simpl. done.
  Qed.

  (* ===== Queue state reconstruction ===== *)

  Local Definition push_value_of (τ : positive) : val :=
    match (lin_event_val τ).1 with
    | InjRV v => v
    | _ => #()
    end.

  Local Lemma push_value_of_push τ v vr :
    filter (λ x, x.1 = τ) ts = [(τ, Call (encode_request (Push v))); (τ, Ret vr)] →
    push_value_of τ = v.
  Proof.
    intros Hfilt. unfold push_value_of. unfold lin_event_val. rewrite Hfilt. done.
  Qed.

  (* Predicate: τ has a matched pop in `all`. Decidable since bounded by `m`. *)
  Local Definition has_matched_pop_in (τ : positive) (all : list positive) : Prop :=
    Exists (λ p : positive * positive, p.1 = τ ∧ p.2 ∈ all) m.

  Local Instance has_matched_pop_in_dec τ all : Decision (has_matched_pop_in τ all).
  Proof. unfold has_matched_pop_in. apply Exists_dec. intros p. apply _. Defined.

  Local Lemma has_matched_pop_in_iff τ all :
    has_matched_pop_in τ all ↔ ∃ τ', (τ, τ') ∈ m ∧ τ' ∈ all.
  Proof.
    unfold has_matched_pop_in.
    rewrite Exists_exists.
    split.
    - intros ([τa τb] & Hin & Heq & Hin_all). simpl in Heq. subst τa.
      exists τb. done.
    - intros (τ' & Hin & Hin_all).
      exists (τ, τ'). done.
  Qed.

  Local Fixpoint live_pushes_aux (sub : list positive) (all : list positive) : list positive :=
    match sub with
    | [] => []
    | τ :: rest =>
      let tail := live_pushes_aux rest all in
      if decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ all)
      then τ :: tail
      else tail
    end.

  Local Definition live_pushes_of (sub : list positive) : list positive :=
    live_pushes_aux sub sub.

  Local Definition queue_state_of (sub : list positive) : list val :=
    map push_value_of (live_pushes_of sub).

  (* ===== Helper lemmas for queue_state_of ===== *)

  Local Lemma live_pushes_aux_app sub1 sub2 all :
    live_pushes_aux (sub1 ++ sub2) all
      = live_pushes_aux sub1 all ++ live_pushes_aux sub2 all.
  Proof.
    induction sub1 as [|τ rest IH]; first done.
    simpl. rewrite IH.
    by destruct (decide _).
  Qed.

  Local Lemma live_pushes_aux_change_all sub all1 all2 :
    (∀ τ, τ ∈ sub → (has_matched_pop_in τ all1 ↔ has_matched_pop_in τ all2)) →
    live_pushes_aux sub all1 = live_pushes_aux sub all2.
  Proof.
    induction sub as [|τ rest IH]; first done.
    intros Heq. simpl.
    rewrite IH.
    2: { intros τ' Hin. apply Heq. apply elem_of_cons. right. exact Hin. }
    assert (Heqh : has_matched_pop_in τ all1 ↔ has_matched_pop_in τ all2).
    { apply Heq. apply elem_of_cons. left. done. }
    destruct (decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ all1)) as [[Hp Hnmp]|Hn1];
    destruct (decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ all2)) as [[Hp2 Hnmp2]|Hn2]; try done.
    - exfalso. apply Hn2. split; [done|]. rewrite <- Heqh. done.
    - exfalso. apply Hn1. split; [done|]. rewrite Heqh. done.
  Qed.

  (* If τ ∉ push_of_trace (τ is pop), adding it to all doesn't affect live_pushes
     of any push τ_p ≠ τ unless τ_p's matched pop equals τ. For τ_p a push with
     matched pop = τ, τ_p becomes dead. *)
  Local Lemma has_matched_pop_in_snoc τ all x :
    has_matched_pop_in τ (all ++ [x]) ↔ has_matched_pop_in τ all ∨ (τ, x) ∈ m.
  Proof.
    rewrite !has_matched_pop_in_iff.
    split.
    - intros (τ' & Hmin & Hinall).
      rewrite elem_of_app in Hinall.
      destruct Hinall as [Hin|Hin].
      + left. exists τ'. done.
      + apply list_elem_of_singleton in Hin. subst τ'.
        right. done.
    - intros [(τ' & Hmin & Hin)|Hin].
      + exists τ'. split; first done. rewrite elem_of_app. left. done.
      + exists x. split; first done. rewrite elem_of_app. right. apply list_elem_of_singleton. done.
  Qed.

  (* If τ ∈ push_of_trace and τ_p ∈ push_of_trace, then (τ_p, τ) ∉ m.
     Because valid_match says τ (being in m.*2) has Call Pop, but τ ∈ push_of_trace
     means τ has Call Push; per_tag_complete gives a unique Call. *)
  Local Lemma push_not_in_matched_pop τ_p τ :
    τ ∈ push_of_trace ts → ¬ (τ_p, τ) ∈ m.
  Proof.
    intros Hpush Hin.
    pose proof (valid_match_call_pop _ _ _ _ Hvalid Hin) as Hcall_pop.
    destruct (push_tag_in_trace _ _ Hpush) as [v Hcall_push].
    destruct (Hcomplete τ) as (vc & vr & [Hfilt|Hfilt]).
    { assert (Hin_push : (τ, Call (encode_request (Push v))) ∈ filter (λ x, x.1 = τ) ts).
      { apply list_elem_of_filter_2; done. }
      rewrite Hfilt in Hin_push. set_solver. }
    assert (Hin_push : (τ, Call (encode_request (Push v))) ∈ filter (λ x, x.1 = τ) ts)
      by (apply list_elem_of_filter_2; done).
    assert (Hin_pop : (τ, Call (encode_request Pop)) ∈ filter (λ x, x.1 = τ) ts)
      by (apply list_elem_of_filter_2; done).
    rewrite Hfilt in Hin_push, Hin_pop.
    rewrite !elem_of_cons elem_of_nil in Hin_push.
    rewrite !elem_of_cons elem_of_nil in Hin_pop.
    destruct Hin_push as [Heq_push|[Heq_push|[]]]; destruct Hin_pop as [Heq_pop|[Heq_pop|[]]];
      try discriminate.
    injection Heq_push as Heq_push.
    injection Heq_pop as Heq_pop.
    congruence.
  Qed.

  (* Live pushes aux is stable under adding a push to `all`. *)
  Local Lemma live_pushes_aux_push_all sub all τ_new :
    τ_new ∈ push_of_trace ts →
    live_pushes_aux sub (all ++ [τ_new]) = live_pushes_aux sub all.
  Proof.
    intros Hpush. apply live_pushes_aux_change_all.
    intros τ' _.
    rewrite has_matched_pop_in_snoc.
    split.
    - intros [H|H]; first done.
      exfalso. eapply push_not_in_matched_pop; done.
    - intros H. left. exact H.
  Qed.

  (* Step: push with no matched pop in sub ++ [τ] adds push_value_of τ to queue. *)
  Local Lemma queue_state_of_push_step sub τ :
    τ ∈ push_of_trace ts →
    ¬ has_matched_pop_in τ (sub ++ [τ]) →
    queue_state_of (sub ++ [τ]) = queue_state_of sub ++ [push_value_of τ].
  Proof.
    intros Hpush Hnmp.
    unfold queue_state_of, live_pushes_of.
    rewrite live_pushes_aux_app.
    rewrite (live_pushes_aux_push_all sub sub τ Hpush).
    rewrite map_app. f_equal.
    simpl.
    destruct (decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ (sub ++ [τ]))) as [_|Habs].
    - done.
    - exfalso. apply Habs. split; done.
  Qed.

  (* Step: a non-push pop (τ ∉ push_of_trace) doesn't add a new push to the queue,
     but may remove a push τ_p from live if (τ_p, τ) ∈ m. *)
  Local Lemma live_pushes_aux_pop_all sub all τ_new :
    τ_new ∉ push_of_trace ts →
    live_pushes_aux sub (all ++ [τ_new])
      = List.filter (λ τ_p, if decide ((τ_p, τ_new) ∈ m) then false else true)
                    (live_pushes_aux sub all).
  Proof.
    intros Hnpush. induction sub as [|τ rest IH]; first done.
    simpl. rewrite IH.
    destruct (decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ (all ++ [τ_new]))) as [[Hp Hnmp1]|Hn1];
    destruct (decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ all)) as [[Hp2 Hnmp2]|Hn2];
    simpl.
    - destruct (decide ((τ, τ_new) ∈ m)) as [Hin|Hnin].
      + exfalso. apply Hnmp1. apply has_matched_pop_in_snoc. right. done.
      + done.
    - exfalso. apply Hn2. split; first done.
      intros Hmpa. apply Hnmp1. apply has_matched_pop_in_snoc. left. done.
    - assert (Hmatch_ext : has_matched_pop_in τ (all ++ [τ_new])).
      { destruct (decide (has_matched_pop_in τ (all ++ [τ_new]))); first done.
        exfalso. apply Hn1. split; done. }
      apply has_matched_pop_in_snoc in Hmatch_ext as [Habs|Hin].
      { done. }
      destruct (decide ((τ, τ_new) ∈ m)) as [_|Hnin]; last done.
      done.
    - destruct (decide ((τ, τ_new) ∈ m)); done.
  Qed.

  Local Lemma queue_state_of_nonpush_step sub τ :
    τ ∉ push_of_trace ts →
    queue_state_of (sub ++ [τ])
      = map push_value_of
          (List.filter (λ τ_p, if decide ((τ_p, τ) ∈ m) then false else true)
                       (live_pushes_of sub)).
  Proof.
    intros Hnpush.
    unfold queue_state_of, live_pushes_of.
    rewrite live_pushes_aux_app.
    rewrite (live_pushes_aux_pop_all sub sub τ Hnpush).
    simpl.
    destruct (decide (τ ∈ push_of_trace ts ∧ _)) as [[Hp _]|_].
    - exfalso. apply Hnpush. exact Hp.
    - by rewrite app_nil_r.
  Qed.

  (* live_pushes are always in push_of_trace. *)
  Local Lemma live_pushes_aux_subseteq_push sub all τ :
    τ ∈ live_pushes_aux sub all → τ ∈ push_of_trace ts.
  Proof.
    revert τ. induction sub as [|τ' rest IH]; intros τ Hin; first by inversion Hin.
    simpl in Hin.
    destruct (decide (τ' ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ' all)) as [[Hp _]|_].
    - apply elem_of_cons in Hin as [->|Hin]; first done. by eapply IH.
    - by eapply IH.
  Qed.

  Local Lemma live_pushes_subseteq_push sub τ :
    τ ∈ live_pushes_of sub → τ ∈ push_of_trace ts.
  Proof. apply live_pushes_aux_subseteq_push. Qed.

  (* live_pushes_aux sub all is a sublist of sub. *)
  Local Lemma live_pushes_aux_sublist sub all τ :
    τ ∈ live_pushes_aux sub all → τ ∈ sub.
  Proof.
    revert τ. induction sub as [|τ' rest IH]; intros τ Hin; first by inversion Hin.
    simpl in Hin.
    destruct (decide _) as [_|_].
    - apply elem_of_cons in Hin as [->|Hin]; first by apply elem_of_cons; left.
      apply elem_of_cons. right. by eapply IH.
    - apply elem_of_cons. right. by eapply IH.
  Qed.

  Local Lemma live_pushes_sublist sub τ :
    τ ∈ live_pushes_of sub → τ ∈ sub.
  Proof. apply live_pushes_aux_sublist. Qed.

  Local Lemma live_pushes_aux_not_matched sub all τ :
    τ ∈ live_pushes_aux sub all → ¬ has_matched_pop_in τ all.
  Proof.
    revert τ. induction sub as [|τ' rest IH]; intros τ Hin; first by inversion Hin.
    simpl in Hin.
    destruct (decide (τ' ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ' all)) as [[_ Hnm]|_].
    - apply elem_of_cons in Hin as [->|Hin]; [done|by eapply IH].
    - by eapply IH.
  Qed.

  Local Lemma live_pushes_not_matched sub τ :
    τ ∈ live_pushes_of sub → ¬ has_matched_pop_in τ sub.
  Proof. apply live_pushes_aux_not_matched. Qed.

  (* NoDup preservation. *)
  Local Lemma NoDup_live_pushes_aux sub all :
    NoDup sub → NoDup (live_pushes_aux sub all).
  Proof.
    induction sub as [|τ' rest IH]; first by intros; apply NoDup_nil.
    intros Hnd. simpl.
    apply NoDup_cons in Hnd as [Hne Hnd].
    destruct (decide _) as [_|_].
    - apply NoDup_cons. split.
      + intros Hin. apply Hne. by apply live_pushes_aux_sublist in Hin.
      + by apply IH.
    - by apply IH.
  Qed.

  Local Lemma NoDup_live_pushes sub :
    NoDup sub → NoDup (live_pushes_of sub).
  Proof. apply NoDup_live_pushes_aux. Qed.

  (* Helper: a list's filter with a predicate that's always true equals the list. *)
  Local Lemma List_filter_all_true {A} (P : A → bool) (l : list A) :
    (∀ x, x ∈ l → P x = true) →
    List.filter P l = l.
  Proof.
    induction l as [|x rest IH]; first done.
    intros Hall. simpl.
    rewrite (Hall x (proj2 (elem_of_cons _ _ _) (or_introl eq_refl))).
    f_equal. apply IH. intros y Hin. apply Hall. apply elem_of_cons. by right.
  Qed.

  (* All-true-filter on a list: if no τ_q in l has (τ_q, τ) ∈ m, filter is identity. *)
  Local Lemma filter_out_matched_all_none (l : list positive) τ :
    (∀ τ_q, τ_q ∈ l → (τ_q, τ) ∉ m) →
    List.filter (λ τ_q, if decide ((τ_q, τ) ∈ m) then false else true) l = l.
  Proof.
    intros Hno.
    apply List_filter_all_true.
    intros x Hin.
    destruct (decide _) as [Hxm|_]; last done.
    exfalso. by apply (Hno x).
  Qed.

  (* Filter by matched removes exactly τ_p when it's at head. *)
  Local Lemma filter_out_matched_head (l : list positive) τ_p τ :
    (∃ rest, l = τ_p :: rest) →
    (τ_p, τ) ∈ m →
    (∀ τ_q, τ_q ∈ tail l → (τ_q, τ) ∉ m) →
    List.filter (λ τ_q, if decide ((τ_q, τ) ∈ m) then false else true) l = tail l.
  Proof.
    intros [rest Hl_cons] Hin_m Hrest.
    rewrite Hl_cons. simpl.
    destruct (decide ((τ_p, τ) ∈ m)) as [_|Habs]; last done.
    apply List_filter_all_true.
    intros x Hx_in.
    destruct (decide _) as [Hxm|_]; last done.
    exfalso. apply (Hrest x).
    - rewrite Hl_cons. simpl. exact Hx_in.
    - exact Hxm.
  Qed.

  (* ===== Tag classification helpers (parameterized by per_tag_wellformed_bag) ===== *)

  (* For push τ: filter (tag=τ) ts = [(τ, Call (Push v)); (τ, Ret #())]. *)
  Local Lemma push_tag_filter (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts) τ :
    τ ∈ push_of_trace ts →
    ∃ v, filter (λ x, x.1 = τ) ts = [(τ, Call (encode_request (Push v))); (τ, Ret #())].
  Proof.
    intros Hpush.
    destruct (push_tag_in_trace _ _ Hpush) as [v Hcall].
    assert (Hin_filt : (τ, Call (encode_request (Push v))) ∈ filter (λ x, x.1 = τ) ts).
    { apply list_elem_of_filter_2; done. }
    destruct (Hcomplete τ) as (vc & vr & [Hempty|Hfilt]).
    { rewrite Hempty in Hin_filt. set_solver. }
    destruct (Hper_tag_wf τ) as [[w [_ Hpfx]]|[r [_ Hpfx]]].
    - rewrite Hfilt in Hpfx.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as Heq1.
      apply prefix_cons_inv_2 in Hpfx as Hpfx1.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx1) as Heq2.
      injection Heq1 as Hvc.
      injection Heq2 as Hvr.
      subst vc vr.
      (* Now Hfilt says filter = [(τ, Call (Push w)); (τ, Ret #())] *)
      assert (Hv_eq : v = w).
      { rewrite Hfilt in Hin_filt.
        rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_filt.
        destruct Hin_filt as [Heq|[Heq|[]]]; [|discriminate].
        by simplify_eq. }
      subst w. exists v. exact Hfilt.
    - (* pop pattern — contradicts τ ∈ push_of_trace *)
      exfalso.
      rewrite Hfilt in Hpfx.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as Hcall_eq.
      injection Hcall_eq as Hcall_eq.
      rewrite Hfilt in Hin_filt.
      rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_filt.
      destruct Hin_filt as [Heq|[Heq|[]]]; [|discriminate].
      by simplify_eq.
  Qed.

  (* For pop τ: filter (tag=τ) ts = [(τ, Call Pop); (τ, Ret (encode_response r))]. *)
  Local Lemma pop_tag_filter (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts) τ :
    τ ∈ pop_of_trace ts →
    ∃ r, filter (λ x, x.1 = τ) ts = [(τ, Call (encode_request Pop)); (τ, Ret (encode_response r))].
  Proof.
    intros Hpop.
    pose proof (pop_tag_in_trace _ _ Hpop) as Hcall.
    assert (Hin_filt : (τ, Call (encode_request Pop)) ∈ filter (λ x, x.1 = τ) ts).
    { apply list_elem_of_filter_2; done. }
    destruct (Hcomplete τ) as (vc & vr & [Hempty|Hfilt]).
    { rewrite Hempty in Hin_filt. set_solver. }
    destruct (Hper_tag_wf τ) as [[w [_ Hpfx]]|[r [_ Hpfx]]].
    - (* push pattern — contradicts τ ∈ pop_of_trace *)
      exfalso.
      rewrite Hfilt in Hpfx.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as Hcall_eq.
      injection Hcall_eq as Hcall_eq.
      rewrite Hfilt in Hin_filt.
      rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_filt.
      destruct Hin_filt as [Heq|[Heq|[]]]; [|discriminate].
      by simplify_eq.
    - rewrite Hfilt in Hpfx.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as Heq1.
      apply prefix_cons_inv_2 in Hpfx as Hpfx1.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx1) as Heq2.
      injection Heq1 as Hvc.
      injection Heq2 as Hvr.
      subst vc vr.
      exists r. exact Hfilt.
  Qed.

  (* For matched pop τ (τ_p, τ) ∈ m: filter has Ret (NonEmpty v) where v is τ_p's push value. *)
  Local Lemma matched_pop_filter (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts) τ_p τ v :
    (τ_p, τ) ∈ m →
    (τ_p, Call (encode_request (Push v))) ∈ ts →
    τ ∈ pop_of_trace ts →
    filter (λ x, x.1 = τ) ts = [(τ, Call (encode_request Pop));
                                (τ, Ret (encode_response (NonEmpty v)))].
  Proof.
    intros Hin_m Hcall_push Hpop.
    destruct (pop_tag_filter Hper_tag_wf τ Hpop) as [r Hfilt].
    destruct Hvalid as (_ & _ & Hforall).
    rewrite Forall_forall in Hforall.
    pose proof (Hforall _ Hin_m) as (_ & _ & v' & Hcall_p' & Hret_or).
    (* v' = v by inj *)
    assert (Hv_eq : v' = v).
    { (* (τ_p, Call Push v) ∈ ts and (τ_p, Call Push v') ∈ ts; both in filter(tag=τ_p).
         filter has at most one Call entry, so they're equal. *)
      destruct (Hcomplete τ_p) as (vc_p & vr_p & [Hempty_p|Hfilt_p]).
      { assert (Hin_p : (τ_p, Call (encode_request (Push v))) ∈ filter (λ x, x.1 = τ_p) ts)
          by (apply list_elem_of_filter_2; done).
        rewrite Hempty_p in Hin_p. set_solver. }
      assert (Hin_v : (τ_p, Call (encode_request (Push v))) ∈ filter (λ x, x.1 = τ_p) ts)
        by (apply list_elem_of_filter_2; done).
      assert (Hin_v' : (τ_p, Call (encode_request (Push v'))) ∈ filter (λ x, x.1 = τ_p) ts)
        by (apply list_elem_of_filter_2; done).
      rewrite Hfilt_p in Hin_v, Hin_v'.
      rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_v.
      rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_v'.
      destruct Hin_v as [Heq|[?|[]]]; last discriminate.
      destruct Hin_v' as [Heq'|[?|[]]]; last discriminate.
      simplify_eq. done. }
    subst v'.
    destruct Hret_or as [Hret|Hnoret].
    2: { (* τ has no Ret, contradicts Hcomplete + filter-nonempty *)
      exfalso. apply Hnoret.
      apply (list_elem_of_fmap_2 fst _ (τ, Ret (encode_response r))).
      apply list_elem_of_filter_2; first done.
      apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
      rewrite Hfilt. apply elem_of_cons. right. apply elem_of_cons. left. done. }
    (* Hret : (τ, Ret (encode_response (NonEmpty v))) ∈ ts *)
    assert (Hin_ret : (τ, Ret (encode_response (NonEmpty v))) ∈ filter (λ x, x.1 = τ) ts)
      by (apply list_elem_of_filter_2; done).
    rewrite Hfilt in Hin_ret.
    rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_ret.
    destruct Hin_ret as [Habs|[Heq|[]]]; first discriminate.
    injection Heq as Heq.
    destruct r as [|v_r]; simpl in Heq; try discriminate.
    injection Heq as <-. exact Hfilt.
  Qed.

  (* For empty pop τ: filter (tag=τ) ts = [(τ, Call Pop); (τ, Ret IsEmpty)]. *)
  Local Lemma empty_pop_filter (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts) τ :
    τ ∈ pop_of_trace ts → τ ∉ m.*2 →
    filter (λ x, x.1 = τ) ts = [(τ, Call (encode_request Pop));
                                (τ, Ret (encode_response IsEmpty))].
  Proof.
    intros Hpop Hnotm.
    destruct (pop_tag_filter Hper_tag_wf τ Hpop) as [r Hfilt].
    destruct Hclosed as (_ & Hforall).
    rewrite Forall_forall in Hforall.
    pose proof (Hforall _ Hpop) as [Habs|[Hret|Hnoret]]; first done.
    - (* (τ, Ret IsEmpty) ∈ ts, so r must = IsEmpty by uniqueness *)
      assert (Hin_r : (τ, Ret (encode_response r)) ∈ ts).
      { apply (list_elem_of_filter_1 (λ x, x.1 = τ)). rewrite Hfilt.
        apply elem_of_cons. right. apply elem_of_cons. left. done. }
      assert (Hin_emp : (τ, Ret (encode_response IsEmpty)) ∈ filter (λ x, x.1 = τ) ts)
        by (apply list_elem_of_filter_2; done).
      rewrite Hfilt in Hin_emp.
      rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_emp.
      destruct Hin_emp as [Habs|[Heq|[]]]; first discriminate.
      injection Heq as Heq.
      destruct r as [|v_r]; simpl in Heq; try discriminate.
      exact Hfilt.
    - (* τ has no Ret, contradiction *)
      exfalso. apply Hnoret.
      apply (list_elem_of_fmap_2 fst _ (τ, Ret (encode_response r))).
      apply list_elem_of_filter_2; first done.
      apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
      rewrite Hfilt. apply elem_of_cons. right. apply elem_of_cons. left. done.
  Qed.

  (* Decomposition lemmas for live_pushes_aux *)
  Local Lemma live_pushes_aux_empty sub all :
    (∀ τ_q, τ_q ∈ sub → ¬ (τ_q ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ_q all)) →
    live_pushes_aux sub all = [].
  Proof.
    induction sub as [|τ rest IH]; first done.
    intros Hall. simpl.
    destruct (decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ all)) as [Hlive|Hnlive].
    - exfalso. apply (Hall τ); [|done]. apply elem_of_cons. left. done.
    - apply IH. intros τ_q Hin. apply Hall. apply elem_of_cons. right. done.
  Qed.

  Local Lemma live_pushes_aux_head_decomp sub all τ_p prefix suffix :
    sub = prefix ++ τ_p :: suffix →
    τ_p ∈ push_of_trace ts →
    ¬ has_matched_pop_in τ_p all →
    (∀ τ_q, τ_q ∈ prefix → ¬ (τ_q ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ_q all)) →
    live_pushes_aux sub all = τ_p :: live_pushes_aux suffix all.
  Proof.
    intros -> Hpush Hnmp Hprefix.
    rewrite live_pushes_aux_app.
    rewrite (live_pushes_aux_empty prefix all Hprefix). simpl.
    destruct (decide (τ_p ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ_p all)) as [_|Habs].
    - done.
    - exfalso. apply Habs. split; done.
  Qed.

  (* ===== Main inductive soundness property ===== *)
  Local Lemma queue_state_invariant
      (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts)
      (prt : relation operation)
      (Hsub : subrelation trace_pre prt)
      (Htri : Trichotomy prt)
      (Htrans : Transitive prt)
      (Hirr : Irreflexive prt)
      (Hvnpr : val_then_not_pr prt trace_val)
      (Hfifo : sequential_fifo prt trace_val)
      (Hcorrect : correct_empty prt trace_val trace_empty)
      (Hadq_emp : all_dequeued_or_empty trace_val trace_empty)
      (ord : list positive)
      (Hord_nodup : NoDup ord)
      (Hord_mem : ∀ τ, τ ∈ ord ↔ τ ∈ events_of_trace ts)
      (Hord_sorted : ∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
        i < j → ord !! i = Some τ1 → ord !! j = Some τ2 →
        prt (τ1 ↾ H1) (τ2 ↾ H2)) :
    ∃ s', linearized_sound (M:=queue_model rme valid_value)
            (filter (is_lin ∘ snd) (ts'_queue ord)) s_init s'.
  Proof.
    rewrite ts'_queue_lin_filter_events.
    (* Strong IH: for each k ≤ length ord, the take-k prefix of Lin events
       is sound and ends in queue_state_of (take k ord). *)
    assert (Hmain : ∀ k, k ≤ length ord →
      linearized_sound (M:=queue_model rme valid_value)
        (take k (lin_events_of_ord ord)) s_init (queue_state_of (take k ord))).
    { intros k. induction k as [|k IHk]; intros Hk.
      - rewrite !take_0. simpl. apply linearized_sound_nil.
      - assert (Hk' : k ≤ length ord) by lia.
        assert (Hk'' : k < length ord) by lia.
        destruct (lookup_lt_is_Some_2 ord k Hk'') as [τ Hord_k].
        assert (Hτ_et : τ ∈ events_of_trace ts).
        { apply Hord_mem. eapply list_elem_of_lookup_2; eauto. }
        assert (Htake_ord : take (Datatypes.S k) ord = take k ord ++ [τ]).
        { by apply take_S_r. }
        assert (Htake_lin : take (Datatypes.S k) (lin_events_of_ord ord)
                          = take k (lin_events_of_ord ord) ++
                            [(τ, Lin (lin_event_val τ).1 (lin_event_val τ).2)]).
        { unfold lin_events_of_ord.
          assert (Hlk : map (λ τ0, (τ0, Lin (lin_event_val τ0).1 (lin_event_val τ0).2)) ord
                       !! k
                     = Some (τ, Lin (lin_event_val τ).1 (lin_event_val τ).2)).
          { rewrite list_lookup_fmap. rewrite Hord_k. done. }
          rewrite (take_S_r _ _ _ Hlk). done. }
        rewrite Htake_lin Htake_ord.
        (* τ ∉ take k ord (from NoDup ord and τ at position k) *)
        assert (Hτ_not_in_tk : τ ∉ take k ord).
        { intros Hin_tk.
          apply list_elem_of_lookup_1 in Hin_tk as (j & Hj).
          apply lookup_take_Some in Hj as [Hj Hjlt].
          assert (j = k) by (eapply NoDup_lookup; [exact Hord_nodup|exact Hj|exact Hord_k]).
          lia. }
        (* Case split on τ *)
        destruct (tag_is_push_or_pop Hadq_emp τ Hτ_et) as [Hpush|Hpop].
        + (* ===== PUSH case ===== *)
          destruct (push_tag_filter Hper_tag_wf τ Hpush) as [v Hfilt].
          rewrite (lin_event_val_of τ _ _ Hfilt). simpl.
          (* Goal: linearized_sound (... ++ [(τ, Lin (Push v) #())]) [] (queue_state_of (take k ord ++ [τ])) *)
          (* ¬ has_matched_pop_in τ (take k ord ++ [τ]) *)
          assert (Hnmp : ¬ has_matched_pop_in τ (take k ord ++ [τ])).
          { intros Hmp%has_matched_pop_in_iff.
            destruct Hmp as (τ_pop & Hin_m & Hin_tk).
            rewrite elem_of_app list_elem_of_singleton in Hin_tk.
            destruct Hin_tk as [Hin_tk|Heqtp].
            - apply list_elem_of_lookup_1 in Hin_tk as (i_pop & Hi_pop).
              apply lookup_take_Some in Hi_pop as [Hi_pop Hi_lt].
              assert (Hτ_pop_et : τ_pop ∈ events_of_trace ts).
              { apply Hord_mem. eapply list_elem_of_lookup_2; eauto. }
              pose proof (Hord_sorted i_pop k τ_pop τ Hτ_pop_et Hτ_et Hi_lt Hi_pop Hord_k) as Hprt_pt.
              pose proof (Hvnpr (τ ↾ Hτ_et) (τ_pop ↾ Hτ_pop_et) Hin_m) as Hnprt.
              by apply Hnprt.
            - subst τ_pop. by eapply push_not_in_matched_pop. }
          rewrite (queue_state_of_push_step _ _ Hpush Hnmp).
          rewrite (push_value_of_push τ v #() Hfilt).
          eapply linearized_sound_snoc.
          * apply IHk. exact Hk'.
          * left. exists v. split; last reflexivity.
            destruct (Hper_tag_wf τ) as [(v_push & ? & Hfilter) | (? & _ & Hfilter)];
              rewrite Hfilt in Hfilter; apply prefix_cons_inv_1 in Hfilter;
              by simplify_eq.
          * exists (Push v). done.
        + (* ===== POP case ===== *)
          assert (Hτ_npush : τ ∉ push_of_trace ts).
          { intros Hτ_push. eapply push_xor_pop_of_trace; eauto. }
          destruct (decide (τ ∈ m.*2)) as [Hmatched|Hempty_test].
          * (* === MATCHED POP case === *)
            apply list_elem_of_fmap_1 in Hmatched as ((τ_p & τ') & Heq & Hin_m).
            simpl in Heq. subst τ'.
            destruct (valid_match_call_push _ _ _ _ Hvalid Hin_m) as [v Hcall_p].
            assert (Hτ_p_push : τ_p ∈ push_of_trace ts).
            { apply (list_elem_of_fmap_2 fst _ (τ_p, Call (encode_request (Push v)))).
              apply list_elem_of_filter_2; last exact Hcall_p.
              simpl. exists v. done. }
            assert (Hτ_p_et : τ_p ∈ events_of_trace ts).
            { apply elem_of_list_to_set.
              apply (list_elem_of_fmap_2 fst _ (τ_p, Call (encode_request (Push v)))); done. }
            pose proof (matched_pop_filter Hper_tag_wf τ_p τ v Hin_m Hcall_p Hpop) as Hfilt.
            rewrite (lin_event_val_of τ _ _ Hfilt). simpl.
            (* Show τ_p ∈ take k ord and get its position i_p < k. *)
            assert (Hτ_p_lookup : ∃ i_p, i_p < k ∧ ord !! i_p = Some τ_p).
            { assert (Hτ_p_in_ord : τ_p ∈ ord) by (apply Hord_mem; done).
              apply list_elem_of_lookup_1 in Hτ_p_in_ord as (i_p & Hi_p).
              destruct (decide (i_p = k)) as [->|Hne].
              { exfalso. rewrite Hi_p in Hord_k. injection Hord_k as <-.
                by eapply push_xor_pop_of_trace. }
              destruct (Nat.lt_trichotomy i_p k) as [Hlt|[Heq|Hgt]]; [|done|].
              - exists i_p. done.
              - exfalso.
                assert (Hk_lt : k < i_p) by lia.
                pose proof (Hord_sorted k i_p τ τ_p Hτ_et Hτ_p_et Hk_lt Hord_k Hi_p) as Hprt_tp.
                pose proof (Hvnpr (τ_p ↾ Hτ_p_et) (τ ↾ Hτ_et) Hin_m) as Hnprt.
                by apply Hnprt. }
            destruct Hτ_p_lookup as (i_p & Hi_p_lt & Hi_p).
            assert (Hτ_p_in_tk : τ_p ∈ take k ord).
            { eapply list_elem_of_lookup_2. apply lookup_take_Some. split; done. }
            (* Uniqueness: for any τ_q with (τ_q, τ) ∈ m, τ_q = τ_p (via NoDup m.*2). *)
            assert (Huniq : ∀ τ_q, (τ_q, τ) ∈ m → τ_q = τ_p).
            { intros τ_q Hin_q.
              destruct Hvalid as (_ & (_ & Hnd_snd) & _).
              apply list_elem_of_lookup_1 in Hin_q as (j1 & Hj1).
              apply list_elem_of_lookup_1 in Hin_m as (j2 & Hj2).
              assert (Hjeq : j1 = j2).
              { apply (NoDup_lookup _ _ _ τ Hnd_snd).
                - rewrite list_lookup_fmap Hj1. done.
                - rewrite list_lookup_fmap Hj2. done. }
              subst j1. rewrite Hj1 in Hj2. by simplify_eq. }
            (* Uniqueness: for any τ_pop' with (τ_p, τ_pop') ∈ m, τ_pop' = τ (via NoDup m.*1). *)
            assert (Huniq_pop : ∀ τ_pop', (τ_p, τ_pop') ∈ m → τ_pop' = τ).
            { intros τ_pop' Hin_m'.
              destruct Hvalid as (_ & (Hnd_fst & _) & _).
              apply list_elem_of_lookup_1 in Hin_m' as (j1 & Hj1).
              apply list_elem_of_lookup_1 in Hin_m as (j2 & Hj2).
              assert (Hjeq : j1 = j2).
              { apply (NoDup_lookup _ _ _ τ_p Hnd_fst).
                - rewrite list_lookup_fmap Hj1. done.
                - rewrite list_lookup_fmap Hj2. done. }
              subst j1. rewrite Hj1 in Hj2. by simplify_eq. }
            (* τ_p is not matched in take k ord (its matched pop is τ ∉ take k ord). *)
            assert (Hτ_p_nmp : ¬ has_matched_pop_in τ_p (take k ord)).
            { intros (τ_pop' & Hin_m' & Hin_tk)%has_matched_pop_in_iff.
              apply Huniq_pop in Hin_m' as ->.
              by apply Hτ_not_in_tk. }
            (* Now show no τ_q at position j < i_p in take k ord is live. *)
            assert (Hnone_before : ∀ τ_q, τ_q ∈ take i_p ord →
                      ¬ (τ_q ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ_q (take k ord))).
            { intros τ_q Hin_q [Hpush_q Hnmp_q].
              apply list_elem_of_lookup_1 in Hin_q as (i_q & Hi_q).
              apply lookup_take_Some in Hi_q as [Hi_q Hi_q_lt].
              (* τ_q at position i_q < i_p in ord. *)
              (* τ_q ∈ push_of_trace, so ∃ τ_qp, (τ_q, τ_qp) ∈ m (by closed_match). *)
              destruct Hclosed as [Hpush_sub _].
              assert (Hτ_q_in_m : τ_q ∈ m.*1) by (apply Hpush_sub; done).
              apply list_elem_of_fmap_1 in Hτ_q_in_m as ((τ_q' & τ_qp) & Heq & Hin_q_m).
              simpl in Heq. subst τ_q'.
              assert (Hτ_qp_pop : τ_qp ∈ pop_of_trace ts).
              { pose proof (valid_match_call_pop _ _ _ _ Hvalid Hin_q_m) as Hcall_qp.
                apply (list_elem_of_fmap_2 fst _ (τ_qp, Call (encode_request Pop))).
                apply list_elem_of_filter_2; done. }
              assert (Hτ_qp_et : τ_qp ∈ events_of_trace ts).
              { apply elem_of_list_to_set.
                apply (list_elem_of_fmap_2 fst _ (τ_qp, Call (encode_request Pop))).
                pose proof (valid_match_call_pop _ _ _ _ Hvalid Hin_q_m); done. }
              apply Hord_mem in Hτ_qp_et as Hτ_qp_in_ord.
              apply list_elem_of_lookup_1 in Hτ_qp_in_ord as (j_qp & Hj_qp).
              (* τ_qp's position in ord *)
              assert (Hτ_qp_et' : τ_qp ∈ events_of_trace ts) by (apply Hord_mem; eapply list_elem_of_lookup_2; done).
              destruct (Nat.lt_trichotomy j_qp k) as [Hlt|[Heq|Hgt]].
              - (* j_qp < k: τ_qp ∈ take k ord, so has_matched_pop_in τ_q (take k ord) TRUE,
                   contradicting Hnmp_q. *)
                apply Hnmp_q. apply has_matched_pop_in_iff. exists τ_qp.
                split; first done.
                eapply list_elem_of_lookup_2. apply lookup_take_Some. split; done.
              - (* j_qp = k: τ_qp = τ; uniq gives τ_q = τ_p; but i_q < i_p = τ_p's pos; contradiction. *)
                subst j_qp. rewrite Hj_qp in Hord_k. injection Hord_k as Hqp_eq.
                subst τ_qp.
                assert (Hqeq : τ_q = τ_p) by (apply Huniq; done).
                subst τ_q.
                assert (i_q = i_p) by (eapply NoDup_lookup; [exact Hord_nodup|exact Hi_q|exact Hi_p]).
                lia.
              - (* j_qp > k: prt τ τ_qp (sorted). And FIFO: prt τ_q τ_p → prt τ_qp τ. Contradiction. *)
                assert (Hi_q_lt_i_p : i_q < i_p) by lia.
                assert (Hτ_q_et : τ_q ∈ events_of_trace ts).
                { apply Hord_mem. eapply list_elem_of_lookup_2. exact Hi_q. }
                pose proof (Hord_sorted i_q i_p τ_q τ_p Hτ_q_et Hτ_p_et Hi_q_lt_i_p Hi_q Hi_p) as Hprt_qp.
                pose proof (Hfifo (τ_q ↾ Hτ_q_et) (τ_p ↾ Hτ_p_et) (τ_qp ↾ Hτ_qp_et') (τ ↾ Hτ_et) Hin_q_m Hin_m Hprt_qp) as Hprt_qp_τ.
                assert (Hk_lt_j : k < j_qp) by lia.
                pose proof (Hord_sorted k j_qp τ τ_qp Hτ_et Hτ_qp_et' Hk_lt_j Hord_k Hj_qp) as Hprt_τ_qp.
                pose proof (Htrans _ _ _ Hprt_qp_τ Hprt_τ_qp) as Hcy.
                by apply (Hirr _ Hcy). }
            (* Now we can decompose live_pushes_of (take k ord). *)
            assert (Htake_split : take k ord = take i_p (take k ord) ++ τ_p :: drop (Datatypes.S i_p) (take k ord)).
            { apply eq_sym. apply take_drop_middle.
              apply lookup_take_Some. split; [|lia]. done. }
            assert (Htake_prefix : take i_p (take k ord) = take i_p ord).
            { rewrite take_take. f_equal. lia. }
            assert (Hlp_decomp : live_pushes_of (take k ord)
              = τ_p :: live_pushes_aux (drop (Datatypes.S i_p) (take k ord)) (take k ord)).
            { unfold live_pushes_of.
              apply (live_pushes_aux_head_decomp _ _ τ_p (take i_p (take k ord))
                                                  (drop (Datatypes.S i_p) (take k ord))).
              - exact Htake_split.
              - exact Hτ_p_push.
              - exact Hτ_p_nmp.
              - rewrite Htake_prefix. exact Hnone_before. }
            (* Get Hfilt_p: filter (tag=τ_p) ts = [(τ_p, Call (Push v)); (τ_p, Ret #())] *)
            assert (Hfilt_p : filter (λ x, x.1 = τ_p) ts
                             = [(τ_p, Call (encode_request (Push v))); (τ_p, Ret #())]).
            { destruct (push_tag_filter Hper_tag_wf τ_p Hτ_p_push) as [v' Hfilt'].
              assert (Hv_eq : v' = v).
              { assert (Hin_v : (τ_p, Call (encode_request (Push v))) ∈ filter (λ x, x.1 = τ_p) ts)
                  by (apply list_elem_of_filter_2; done).
                rewrite Hfilt' in Hin_v.
                rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_v.
                destruct Hin_v as [Heq|[?|[]]]; last discriminate.
                by simplify_eq. }
              subst v'. exact Hfilt'. }
            (* Key equation: queue_state_of (take k ord) = v :: queue_state_of (take k ord ++ [τ]) *)
            assert (Hstate_eq : queue_state_of (take k ord) = v :: queue_state_of (take k ord ++ [τ])).
            { unfold queue_state_of at 1. rewrite Hlp_decomp. simpl.
              rewrite (push_value_of_push τ_p v #() Hfilt_p).
              f_equal.
              rewrite (queue_state_of_nonpush_step _ _ Hτ_npush).
              unfold queue_state_of. rewrite Hlp_decomp.
              rewrite (filter_out_matched_head _ τ_p τ (ex_intro _ _ eq_refl) Hin_m).
              - done.
              - (* No other τ_q in tail has (τ_q, τ) ∈ m *)
                intros τ_q Hin_q Hin_m_q.
                simpl in Hin_q.
                pose proof (Huniq τ_q Hin_m_q) as ->.
                assert (Hnd_lp : NoDup (live_pushes_of (take k ord))).
                { apply NoDup_live_pushes.
                  rewrite <- (take_drop k ord) in Hord_nodup.
                  by apply NoDup_app in Hord_nodup as (? & _). }
                rewrite Hlp_decomp in Hnd_lp.
                apply NoDup_cons in Hnd_lp as [Hne _]. done. }
            eapply linearized_sound_snoc.
            -- apply IHk. exact Hk'.
            -- right. reflexivity.
            -- exists Pop. simpl. rewrite Hstate_eq. done.
          * (* === EMPTY POP case === *)
            assert (Hempty : trace_empty (τ ↾ Hτ_et)).
            { unfold trace_empty, empty_of_trace_match. simpl. done. }
            pose proof (empty_pop_filter Hper_tag_wf τ Hpop Hempty_test) as Hfilt.
            rewrite (lin_event_val_of τ _ _ Hfilt). simpl.
            (* Show queue_state_of (take k ord) = [] *)
            assert (Hstate_empty : queue_state_of (take k ord) = []).
            { unfold queue_state_of, live_pushes_of.
              rewrite (live_pushes_aux_empty (take k ord) (take k ord)).
              - done.
              - intros τ_q Hin_q [Hpush_q Hnmp_q].
                apply list_elem_of_lookup_1 in Hin_q as (i_q & Hi_q).
                apply lookup_take_Some in Hi_q as [Hi_q Hi_q_lt].
                assert (Hτ_q_et : τ_q ∈ events_of_trace ts).
                { apply Hord_mem. eapply list_elem_of_lookup_2. exact Hi_q. }
                (* τ_q ∈ push_of_trace → ∃ τ_qp, (τ_q, τ_qp) ∈ m *)
                destruct Hclosed as [Hpush_sub _].
                assert (Hτ_q_in_m : τ_q ∈ m.*1) by (apply Hpush_sub; done).
                apply list_elem_of_fmap_1 in Hτ_q_in_m as ((τ_q' & τ_qp) & Heq & Hin_q_m).
                simpl in Heq. subst τ_q'.
                assert (Hτ_qp_pop : τ_qp ∈ pop_of_trace ts).
                { pose proof (valid_match_call_pop _ _ _ _ Hvalid Hin_q_m) as Hcall_qp.
                  apply (list_elem_of_fmap_2 fst _ (τ_qp, Call (encode_request Pop))).
                  apply list_elem_of_filter_2; done. }
                assert (Hτ_qp_et : τ_qp ∈ events_of_trace ts).
                { apply elem_of_list_to_set.
                  apply (list_elem_of_fmap_2 fst _ (τ_qp, Call (encode_request Pop))).
                  pose proof (valid_match_call_pop _ _ _ _ Hvalid Hin_q_m); done. }
                apply Hord_mem in Hτ_qp_et as Hτ_qp_in_ord.
                apply list_elem_of_lookup_1 in Hτ_qp_in_ord as (j_qp & Hj_qp).
                assert (Hτ_qp_et' : τ_qp ∈ events_of_trace ts)
                  by (apply Hord_mem; eapply list_elem_of_lookup_2; done).
                destruct (Nat.lt_trichotomy j_qp k) as [Hlt|[Heq|Hgt]].
                + (* j_qp < k: τ_qp ∈ take k ord → τ_q is matched; Hnmp_q contradiction *)
                  apply Hnmp_q. apply has_matched_pop_in_iff. exists τ_qp.
                  split; first done.
                  eapply list_elem_of_lookup_2. apply lookup_take_Some. split; done.
                + (* j_qp = k: τ_qp = τ; (τ_q, τ) ∈ m means τ ∈ m.*2; contradicts Hempty_test *)
                  subst j_qp. rewrite Hj_qp in Hord_k. injection Hord_k as <-.
                  apply Hempty_test. apply (list_elem_of_fmap_2 snd _ (τ_q, τ_qp)); done.
                + (* j_qp > k: use correct_empty *)
                  pose proof (Hcorrect (τ ↾ Hτ_et) Hempty (τ_q ↾ Hτ_q_et) (τ_qp ↾ Hτ_qp_et') Hin_q_m)
                    as [[Hprt1 Hprt2]|[Hprt1 Hprt2]].
                  * (* prt τ_qp τ, but prt τ τ_qp (sorted k < j_qp), contradiction *)
                    assert (Hk_lt_j : k < j_qp) by lia.
                    pose proof (Hord_sorted k j_qp τ τ_qp Hτ_et Hτ_qp_et' Hk_lt_j Hord_k Hj_qp) as Hprt_τ_qp.
                    pose proof (Htrans _ _ _ Hprt2 Hprt_τ_qp) as Hcy.
                    by apply (Hirr _ Hcy).
                  * (* prt τ τ_q, but prt τ_q τ (sorted i_q < k), contradiction *)
                    pose proof (Hord_sorted i_q k τ_q τ Hτ_q_et Hτ_et Hi_q_lt Hi_q Hord_k) as Hprt_q_τ.
                    pose proof (Htrans _ _ _ Hprt1 Hprt_q_τ) as Hcy.
                    by apply (Hirr _ Hcy). }
            (* Now show queue_state_of (take k ord ++ [τ]) = [] *)
            assert (Hstate_empty2 : queue_state_of (take k ord ++ [τ]) = []).
            { rewrite (queue_state_of_nonpush_step _ _ Hτ_npush).
              unfold queue_state_of in Hstate_empty.
              destruct (live_pushes_of (take k ord)); last discriminate.
              done. }
            rewrite Hstate_empty2.
            eapply linearized_sound_snoc.
            -- apply IHk. exact Hk'.
            -- right. reflexivity.
            -- exists Pop. simpl. rewrite Hstate_empty.
               destruct rme; first done.
               exfalso.
               destruct (Hper_tag_wf τ) as [(? & _ & Hpfx)|(r & Hr_ne & Hpfx)].
               { rewrite Hfilt in Hpfx. apply prefix_cons_inv_1 in Hpfx. discriminate. }
               rewrite Hfilt in Hpfx.
               apply prefix_cons_inv_2, prefix_cons_inv_1 in Hpfx.
               injection Hpfx as Hr_eq.
               assert (r = IsEmpty) as ->.
               { destruct r; simpl in Hr_eq; [done|discriminate]. }
               by apply Hr_ne.
    }
    exists (queue_state_of ord).
    replace (lin_events_of_ord ord) with (take (length ord) (lin_events_of_ord ord)).
    2: { apply take_ge. unfold lin_events_of_ord. rewrite length_map. lia. }
    replace ord with (take (length ord) ord) at 3.
    2: { apply take_ge. lia. }
    apply Hmain. lia.
  Qed.

  Lemma linearizable_queue__trace_linearizable_queue :
    per_tag_wellformed_bag rme valid_value ts →
    linearizable_queue trace_pre trace_val trace_empty →
    trace_linearizable (M:=queue_model rme valid_value) ts.
  Proof.
    intros Hper_tag_wf Hlinq.
    destruct Hlinq as (Hch & prt & Hsub & Hseq).
    destruct Hseq as [Hses Hfifo].
    destruct Hses as [Hseh Hcorrect].
    destruct Hseh as [Hwfe Htri].
    pose proof Hwfe as Hwfe0.
    destruct Hwfe as [Hprt_ch Henq_once Hdeq_once Hval_order Hadq_emp Hemp_notval Hvnpr].
    (* Extract prt properties from ConcHistory *)
    pose proof Hprt_ch as Hprt_ch0.
    destruct Hprt_ch as [Htrans Hanti Hirr _].
    (* Get the sorted order *)
    destruct (prt_sort_exists prt Htri Htrans Hirr)
      as (ord & Hord_nodup & Hord_mem & Hord_sorted).
    (* Assemble the result *)
    split.
    { exact (call_valid_ts Hper_tag_wf Hadq_emp). }
    exists (ts'_queue ord).
    split_and!.
    - symmetry. exact (ts'_queue_filter_not_lin ord).
    - exact (ts'_queue_per_tag_linearized prt Hsub Htrans Hirr Hanti
               ord Hord_mem Hord_nodup Hord_sorted).
    - exact (queue_state_invariant Hper_tag_wf prt Hsub Htri Htrans Hirr Hvnpr Hfifo Hcorrect Hadq_emp
               ord Hord_nodup Hord_mem Hord_sorted).
  Qed.
  (* End LLM-generated code. *)
  (**********************************************************)
End proof.
