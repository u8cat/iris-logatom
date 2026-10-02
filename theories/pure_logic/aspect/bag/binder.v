(* Model-independent part of the trace <-> history binding, shared by the queue and
   stack theorems: the history instance over the events of a complete trace, sorting by
   a total order, and the insertion of Lin events that realizes a sorted order. *)
From stdpp Require Import finite.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.bag Require Import base.

(* FIXME: inline these two very simply lemmas. *)
Lemma list_filter_lookup_pred {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (i : nat) (x : A) :
  filter P l !! i = Some x → P x.
Proof. by intros [??]%list_elem_of_lookup_2%list_elem_of_filter. Qed.
Lemma list_filter_lookup_orig {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (i : nat) (x : A) :
  filter P l !! i = Some x → x ∈ l.
Proof. by intros [??]%list_elem_of_lookup_2%list_elem_of_filter. Qed.

(* FIXME: move to elsewhere *)
Lemma filter_NoDup_at {A} (P : A → Prop) `{!∀ x, Decision (P x)}
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
Lemma filter_at_most_once {A} (P : A → Prop) `{!∀ x, Decision (P x)}
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
Lemma NoDup_split_unique {A} (l l1 l2 l1' l2' : list A) (x : A) :
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

Section binder.
  Variables (rme : response_mayempty) (valid_value : val → Prop) (ts : list (positive * trace)) (m : list (positive*positive)).
  Hypothesis Hvalid : valid_match ts m.
  Hypothesis Hcomplete : per_tag_complete ts.
  Hypothesis Hclosed : closed_match ts m.

  Definition trace_op : Type := { τ: positive | τ ∈ events_of_trace ts }.

  Global Instance trace_operation_eq_dec : EqDecision trace_op.
  Proof. solve_decision. Defined.

  Global Program Instance trace_operation_finite : Finite trace_op :=
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

  Definition trace_pre : relation trace_op :=
    λ op1 op2, pre_of_trace ts (`op1) (`op2).

  Definition trace_prt ts' : relation trace_op :=
    λ op1 op2, prt_of_trace ts' (`op1) (`op2).

  Definition trace_val : relation trace_op :=
    λ op1 op2, (`op1, `op2) ∈ m.

  Definition trace_empty : trace_op → Prop :=
    λ op, empty_of_trace_match ts m (`op).

   Lemma call_ret_le {call ret x y τ} :
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
    destruct t_call as [nv v| |]; simpl in His_call; [|done..].
    rewrite /ret_of_tag list_find_Some in Hret.
    destruct Hret as (Hlookup_ret & [Heq His_ret] & _).
    simpl in Heq, His_ret. subst τ_ret.
    destruct t_ret as [| |v']; simpl in His_ret; [done..|].
    destruct (decide (call = ret)) as [->|Hne].
    { rewrite Hlookup_call in Hlookup_ret. discriminate. }

    (* [filter (λ x, x.1 = τ2) ts] should be [(τ, Call _); (τ, Ret _)] *)
    destruct (Hcomplete τ) as (nv0 & v0 & v0' & [Heq|Heq]).
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
     Transitive) on trace_op, there exists a linear enumeration of
     [elements (events_of_trace ts)] respecting prt. *)
  Lemma prt_sort_exists
      (prt : relation trace_op)
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
  Lemma tag_is_push_or_pop (Hwf : per_tag_wellformed_bag rme valid_value ts) τ :
    τ ∈ events_of_trace ts →
    τ ∈ push_of_trace ts ∨ τ ∈ pop_of_trace ts.
  Proof. intros Hτ. by eapply push_or_pop_of_trace. Qed.

  (* ===== Call valid: every Call in ts is a valid request of a bag-like model ===== *)
  Lemma call_valid_ts (M : model) :
    M.(valid_requests) = [valid_value; λ v, v = #()] →
    per_tag_wellformed_bag rme valid_value ts →
    call_valid (M:=M) ts.
  Proof.
    intros HM Hwf.
    apply Forall_forall. intros [τ ev] Hin.
    destruct ev as [nr r|nv v v'|r]; [|done|done].
    simpl. rewrite HM.
    assert (Hτ : τ ∈ events_of_trace ts).
    { unfold events_of_trace. apply elem_of_list_to_set.
      apply (list_elem_of_fmap_2 fst _ (τ, Call nr r)). exact Hin. }
    (* From per_tag_complete, there's a unique Call for tag τ *)
    apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin as Hin_tag; last done.
    destruct (Hcomplete τ) as (nvc & vc & vr & [Hfilt|Hfilt]).
    { rewrite Hfilt in Hin_tag. set_solver. }
    (* So vc = r *)
    rewrite Hfilt in Hin_tag.
    rewrite !elem_of_cons elem_of_nil in Hin_tag.
    destruct Hin_tag as [Heq|[Heq|Habs]]; last done; last first.
    { discriminate. }
    simplify_eq.
    (* Now the unique Call for τ is (τ, Call nr r) with vc = r *)
    destruct (tag_is_push_or_pop Hwf τ Hτ) as [Hpush|Hpop].
    - destruct (push_tag_in_trace _ _ Hpush) as [w Hcall_push].
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hcall_push as Hpush_tag; last done.
      rewrite Hfilt in Hpush_tag.
      rewrite !elem_of_cons elem_of_nil right_id in Hpush_tag.
      destruct Hpush_tag as [Heq2|Heq2].
      + simplify_eq. simpl.
        destruct (Hwf τ) as [[v_push [Hvv Hfilter]] | [? [_ Hfilter]]].
        * rewrite Hfilt in Hfilter.
          apply prefix_cons_inv_1 in Hfilter as Heq.
          simplify_eq. assumption.
        * rewrite Hfilt in Hfilter.
          apply prefix_cons_inv_1 in Hfilter as Heq.
          by simplify_eq.
      + discriminate.
    - pose proof (pop_tag_in_trace _ _ Hpop) as Hcall_pop.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hcall_pop as Hpop_tag; last done.
      rewrite Hfilt in Hpop_tag.
      rewrite !elem_of_cons elem_of_nil in Hpop_tag.
      destruct Hpop_tag as [Heq2|[Heq2|[]]].
      + simplify_eq. by simpl.
      + discriminate.
  Qed.

  (* tag_classification is not used by the main lemma (the Ret value for push
     isn't constrained to #() from Section hypotheses — the downstream caller
     instantiates via close_trace which enforces it, but within the binding
     Section we don't have that guarantee). *)

  (* ===== The Lin event value for tag τ =====
     For τ ∈ events_of_trace ts, extract the Call and Ret values directly
     from ts (they form the filter [(τ, Call nvc vc); (τ, Ret vr)] by per_tag_complete).
     The Lin event for τ will be (τ, Lin nvc vc vr), matching the queue semantics
     (the Call request equals the Lin request; the Ret response equals the Lin
     response). For τ ∉ events_of_trace ts, the value doesn't matter since no
     Lin is inserted for such a tag. *)
  Definition lin_event_val (τ : positive) : nat * val * val :=
    match filter (λ x, x.1 = τ) ts with
    | (_, Call nc vc) :: (_, Ret vr) :: _ => (nc, vc, vr)
    | _ => (Push, #(), #())
    end.

  Lemma lin_event_val_of τ nc vc vr :
    filter (λ x, x.1 = τ) ts = [(τ, Call nc vc); (τ, Ret vr)] →
    lin_event_val τ = (nc, vc, vr).
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
     some prt-earlier trace_op τ'' would have Call after Ret(τ),
     implying trace_pre(τ, τ'') and thus prt(τ, τ'') — contradiction). *)

  (* Move elements from suffix to prefix until we find a Call(τ). *)
  Fixpoint advance_to_call (τ : positive)
      (prefix suffix : list (positive * trace))
      : list (positive * trace) * list (positive * trace) :=
    match suffix with
    | [] => (prefix, [])
    | (τ', Call n' v') :: rest =>
      if decide (τ' = τ) then
        (prefix ++ [(τ, Call n' v')], rest)
      else
        advance_to_call τ (prefix ++ [(τ', Call n' v')]) rest
    | evt :: rest =>
      advance_to_call τ (prefix ++ [evt]) rest
    end.

  (* Insert one Lin: either directly (Call already in prefix) or after advancing. *)
  Definition insert_one_lin (τ : positive) (n : nat) (v v' : val)
      (prefix suffix : list (positive * trace))
      : list (positive * trace) * list (positive * trace) :=
    if decide (τ ∈ (filter (is_call ∘ snd) prefix).*1) then
      (prefix ++ [(τ, Lin n v v')], suffix)
    else
      let '(p, s) := advance_to_call τ prefix suffix in
      (p ++ [(τ, Lin n v v')], s).

  (* Process all Lins in prt order. *)
  Fixpoint insert_lins_in_order (ord : list positive)
      (prefix suffix : list (positive * trace))
      : list (positive * trace) :=
    match ord with
    | [] => prefix ++ suffix
    | τ :: rest =>
      let '(n, v, v') := lin_event_val τ in
      let '(p, s) := insert_one_lin τ n v v' prefix suffix in
      insert_lins_in_order rest p s
    end.

  Definition ts'_lin (ord : list positive) : list (positive * trace) :=
    insert_lins_in_order ord [] ts.

  (* ===== Structural lemmas: filter preservation ===== *)
  (* advance_to_call is content-preserving: p ++ s = prefix ++ suffix. *)
  Lemma advance_to_call_preserves τ prefix suffix :
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
  Lemma insert_one_lin_filter_not_lin τ n v v' prefix suffix :
    ∀ p s,
    insert_one_lin τ n v v' prefix suffix = (p, s) →
    filter (not ∘ is_lin ∘ snd) (p ++ s)
      = filter (not ∘ is_lin ∘ snd) (prefix ++ suffix).
  Proof.
    intros p s Heq.
    unfold insert_one_lin in Heq.
    assert (Hne : ¬ (not ∘ is_lin ∘ snd) (τ, Lin n v v')).
    { simpl. intros Habs. apply Habs. done. }
    destruct (decide (τ ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|Hnin].
    - injection Heq as <- <-.
      rewrite -app_assoc. simpl.
      rewrite !filter_app.
      rewrite (filter_cons_False _ (τ, Lin n v v') _ Hne). done.
    - destruct (advance_to_call τ prefix suffix) as [p' s'] eqn:Hadv.
      injection Heq as <- <-.
      pose proof (advance_to_call_preserves _ _ _ _ _ Hadv) as Hpres.
      rewrite -app_assoc. simpl.
      rewrite !filter_app.
      rewrite (filter_cons_False _ (τ, Lin n v v') _ Hne).
      rewrite -filter_app. rewrite Hpres. rewrite filter_app. done.
  Qed.

  Lemma insert_lins_in_order_filter_not_lin ord prefix suffix :
    filter (not ∘ is_lin ∘ snd) (insert_lins_in_order ord prefix suffix)
      = filter (not ∘ is_lin ∘ snd) (prefix ++ suffix).
  Proof.
    revert prefix suffix. induction ord as [|τ rest IH]; intros prefix suffix.
    - simpl. done.
    - simpl. destruct (lin_event_val τ) as [[n v] v'] eqn:Hval.
      destruct (insert_one_lin τ n v v' prefix suffix) as [p s] eqn:Heq.
      rewrite IH.
      eapply insert_one_lin_filter_not_lin. exact Heq.
  Qed.

  Lemma ts_no_lin_event :
    ∀ τ n v v', (τ, Lin n v v') ∉ ts.
  Proof.
    intros τ n v v' Hin.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin as Hin_tag; last done.
    destruct (Hcomplete τ) as (nvc & vc & vr & [Hfilt|Hfilt]).
    - rewrite Hfilt in Hin_tag. set_solver.
    - rewrite Hfilt in Hin_tag.
      rewrite !elem_of_cons elem_of_nil in Hin_tag.
      destruct Hin_tag as [Habs|[Habs|Habs]];
        try (discriminate || done).
  Qed.

  Lemma filter_all_true {A} (P : A → Prop) `{!∀ x, Decision (P x)} (l : list A) :
    Forall P l → filter P l = l.
  Proof.
    induction l as [|a l' IH]; first done.
    intros Hall.
    apply Forall_cons in Hall as [Ha Hall'].
    rewrite filter_cons_True; last done.
    f_equal. apply IH. exact Hall'.
  Qed.

  Lemma ts_filter_not_lin_self :
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

  Lemma ts'_lin_filter_not_lin ord :
    filter (not ∘ is_lin ∘ snd) (ts'_lin ord) = ts.
  Proof.
    unfold ts'_lin. rewrite insert_lins_in_order_filter_not_lin.
    simpl. apply ts_filter_not_lin_self.
  Qed.

  (* advance_to_call preserves per-tag filter content. *)
  Lemma advance_to_call_tag_filter (τ τ' : positive) prefix suffix p s :
    advance_to_call τ' prefix suffix = (p, s) →
    filter (λ x, x.1 = τ) (p ++ s) = filter (λ x, x.1 = τ) (prefix ++ suffix).
  Proof.
    intros Heq. rewrite (advance_to_call_preserves _ _ _ _ _ Heq). done.
  Qed.

  (* insert_one_lin adds at most one Lin (only when τ' = τ) to the per-tag filter. *)
  Lemma insert_one_lin_other_tag_filter (τ τ' : positive) n v v' prefix suffix p s :
    τ ≠ τ' →
    insert_one_lin τ' n v v' prefix suffix = (p, s) →
    filter (λ x, x.1 = τ) (p ++ s) = filter (λ x, x.1 = τ) (prefix ++ suffix).
  Proof.
    intros Hne Heq.
    unfold insert_one_lin in Heq.
    destruct (decide (τ' ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|Hnin].
    - injection Heq as <- <-.
      rewrite -app_assoc. simpl.
      rewrite !filter_app.
      rewrite (filter_cons_False _ (τ', Lin n v v') _);
        last (simpl; intros Habs; apply Hne; done).
      done.
    - destruct (advance_to_call τ' prefix suffix) as [p' s'] eqn:Hadv.
      injection Heq as <- <-.
      pose proof (advance_to_call_preserves _ _ _ _ _ Hadv) as Hpres.
      rewrite -app_assoc. simpl.
      rewrite !filter_app.
      rewrite (filter_cons_False _ (τ', Lin n v v') _);
        last (simpl; intros Habs; apply Hne; done).
      rewrite -!filter_app Hpres. done.
  Qed.

  (* If τ is not in ord, the fold leaves the tag filter untouched. *)
  Lemma insert_lins_in_order_tag_notin_ord (τ : positive) ord' prefix suffix :
    τ ∉ ord' →
    filter (λ x, x.1 = τ) (insert_lins_in_order ord' prefix suffix)
      = filter (λ x, x.1 = τ) (prefix ++ suffix).
  Proof.
    revert prefix suffix. induction ord' as [|τ' rest IH]; intros prefix suffix Hne.
    - simpl. done.
    - apply not_elem_of_cons in Hne as [Hne1 Hne2].
      simpl. destruct (lin_event_val τ') as [[n v] v'] eqn:Hval.
      destruct (insert_one_lin τ' n v v' prefix suffix) as [p s] eqn:Heq.
      rewrite IH; last done.
      apply (insert_one_lin_other_tag_filter _ _ _ _ _ _ _ _ _ Hne1 Heq).
  Qed.

  (* State-tracking helper: returns (p, s) pair through the fold. *)
  Fixpoint insert_lins_state (ord : list positive)
      (prefix suffix : list (positive * trace))
      : list (positive * trace) * list (positive * trace) :=
    match ord with
    | [] => (prefix, suffix)
    | τ :: rest =>
      let '(n, v, v') := lin_event_val τ in
      let '(p, s) := insert_one_lin τ n v v' prefix suffix in
      insert_lins_state rest p s
    end.

  Lemma insert_lins_in_order_eq_state ord prefix suffix :
    insert_lins_in_order ord prefix suffix =
      (let '(p, s) := insert_lins_state ord prefix suffix in p ++ s).
  Proof.
    revert prefix suffix. induction ord as [|τ rest IH]; intros prefix suffix; first done.
    simpl. destruct (lin_event_val τ) as [[n v] v'].
    destruct (insert_one_lin τ n v v' prefix suffix) as [p s].
    apply IH.
  Qed.

  Lemma insert_lins_state_app ord1 ord2 prefix suffix :
    insert_lins_state (ord1 ++ ord2) prefix suffix =
      (let '(p, s) := insert_lins_state ord1 prefix suffix in
       insert_lins_state ord2 p s).
  Proof.
    revert prefix suffix. induction ord1 as [|τ rest IH]; intros prefix suffix; first done.
    simpl. destruct (lin_event_val τ) as [[n v] v'].
    destruct (insert_one_lin τ n v v' prefix suffix) as [p s].
    apply IH.
  Qed.

  (* For τ ∉ ord, state preserves prefix/suffix combined. *)
  Lemma insert_lins_state_notin_preserve (τ : positive) ord' prefix suffix p s :
    τ ∉ ord' →
    insert_lins_state ord' prefix suffix = (p, s) →
    filter (λ x, x.1 = τ) (p ++ s) = filter (λ x, x.1 = τ) (prefix ++ suffix).
  Proof.
    revert prefix suffix p s.
    induction ord' as [|τ' rest IH]; intros prefix suffix p s Hne Hstate.
    - simpl in Hstate. injection Hstate as <- <-. done.
    - apply not_elem_of_cons in Hne as [Hne1 Hne2].
      simpl in Hstate. destruct (lin_event_val τ') as [[n v] v'] eqn:Hval.
      destruct (insert_one_lin τ' n v v' prefix suffix) as [p' s'] eqn:Heq.
      rewrite (IH p' s' p s Hne2 Hstate).
      apply (insert_one_lin_other_tag_filter _ _ _ _ _ _ _ _ _ Hne1 Heq).
  Qed.

  (* advance_to_call preserves suffix-is-drop-tail: if old suffix = drop k l,
     then new suffix = drop k' l for some k' ≥ k. *)
  Lemma advance_to_call_suffix_drop τ' l k prefix suffix p s :
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
  Lemma insert_one_lin_suffix_drop τ' n v v' k prefix suffix p s :
    suffix = drop k ts →
    insert_one_lin τ' n v v' prefix suffix = (p, s) →
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

  Lemma insert_lins_state_suffix_drop ord' prefix suffix p s :
    (∃ k, suffix = drop k ts) →
    insert_lins_state ord' prefix suffix = (p, s) →
    ∃ k, s = drop k ts.
  Proof.
    revert prefix suffix p s.
    induction ord' as [|τ' rest IH]; intros prefix suffix p s [k Hdrop] Hstate.
    - simpl in Hstate. injection Hstate as <- <-.
      exists k. exact Hdrop.
    - simpl in Hstate.
      destruct (lin_event_val τ') as [[n v] v'] eqn:Hval.
      destruct (insert_one_lin τ' n v v' prefix suffix) as [p' s'] eqn:Heq.
      destruct (insert_one_lin_suffix_drop _ _ _ _ _ _ _ _ _ Hdrop Heq) as (k' & _ & Hs').
      apply (IH p' s' p s (ex_intro _ k' Hs') Hstate).
  Qed.

  (* Given a trace and positions, the call_of_tag and ret_of_tag positions. *)
  (* For τ ∈ events_of_trace ts with filter (tag=τ) ts = [Call nvc vc; Ret vr],
     these have specific positions (given by list_find). *)

  Lemma call_of_tag_pos τ nvc vc vr :
    filter (λ x, x.1 = τ) ts = [(τ, Call nvc vc); (τ, Ret vr)] →
    ∃ cp, call_of_tag ts τ = Some (cp, (τ, Call nvc vc)).
  Proof.
    intros Hfilt.
    assert (Hin : (τ, Call nvc vc) ∈ ts).
    { apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
      rewrite Hfilt. set_solver. }
    pose proof (list_find_elem_of (λ x, x.1 = τ ∧ is_call x.2) ts (τ, Call nvc vc)
      Hin ltac:(split; done)) as Hfind.
    destruct (list_find _ ts) as [[cp [τ'' ev]]|] eqn:Hlf; last by destruct Hfind.
    exists cp. unfold call_of_tag. rewrite Hlf.
    apply list_find_Some in Hlf as (Hlookup & [Htag Hcall] & _).
    simpl in Htag, Hcall. subst τ''.
    destruct ev as [nw w| |]; [|done|done].
    (* w must equal vc because filter is unique *)
    apply list_elem_of_lookup_2 in Hlookup.
    apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hlookup; last done.
    rewrite Hfilt in Hlookup.
    rewrite !elem_of_cons elem_of_nil in Hlookup.
    destruct Hlookup as [Heq1|[Heq1|Heq1]]; [injection Heq1 as <- <-; done|discriminate|done].
  Qed.

  Lemma ret_of_tag_pos τ nvc vc vr :
    filter (λ x, x.1 = τ) ts = [(τ, Call nvc vc); (τ, Ret vr)] →
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
    destruct ev as [|nvl vl vl'|w]; [done|done|].
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
  Lemma prt_sorted_call_before_ret_pos
      (prt : relation trace_op)
      (Hsub : subrelation trace_pre prt)
      (Htrans : Transitive prt)
      (Hirr : Irreflexive prt)
      (Hanti : Antisymmetric trace_op eq prt)
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
      ∀ τ_step c_step n_step ev_step,
        τ_step ∈ ord_before →
        call_of_tag ts τ_step = Some (c_step, (τ_step, Call n_step ev_step)) →
        c_step < rp.
  Proof.
    intros Hnd Hsub_ord Hsorted Hret_τ τ_step c_step n_step ev_step Hstep Hcall_step.
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
  Lemma advance_to_call_finds (τ : positive) (prefix suffix : list (positive * trace))
      (p s : list (positive * trace)) :
    advance_to_call τ prefix suffix = (p, s) →
    (∃ nc v, (τ, Call nc v) ∈ suffix) →
    ∃ nc v, (τ, Call nc v) ∈ p.
  Proof.
    revert prefix. induction suffix as [|[τ'' ev] rest IH]; intros prefix Heq Hex.
    - destruct Hex as (nc & v & Hv). set_solver.
    - destruct ev as [nw w|nvl vl vl'|r]; simpl in Heq.
      + destruct (decide (τ'' = τ)) as [->|Hne].
        * injection Heq as <- <-. exists nw, w.
          apply elem_of_app. right. apply elem_of_cons. left. done.
        * destruct Hex as (nc & v & Hv).
          apply elem_of_cons in Hv as [Heq'|Hv].
          { injection Heq'. intros. subst. done. }
          destruct (IH _ Heq ltac:(exists nc, v; exact Hv)) as (nc2 & v2 & Hv2).
          exists nc2, v2. exact Hv2.
      + destruct Hex as (nc & v & Hv). apply elem_of_cons in Hv as [Heq'|Hv]; first discriminate.
        destruct (IH _ Heq ltac:(exists nc, v; exact Hv)) as (nc2 & v2 & Hv2).
        exists nc2, v2. exact Hv2.
      + destruct Hex as (nc & v & Hv). apply elem_of_cons in Hv as [Heq'|Hv]; first discriminate.
        destruct (IH _ Heq ltac:(exists nc, v; exact Hv)) as (nc2 & v2 & Hv2).
        exists nc2, v2. exact Hv2.
  Qed.

  (* advance_to_call: when Call(τ) is the FIRST Call(τ) in l at position c,
     and the scan starts at k ≤ c, then after advance the new suffix is drop (c+1) l. *)
  Lemma advance_to_call_at_first l τ c nvc vc :
    l !! c = Some (τ, Call nvc vc) →
    (∀ j, j < c → ∀ nv v, l !! j ≠ Some (τ, Call nv v)) →
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
      (* suffix = drop c l. By Hlc, drop c l = (τ, Call nvc vc) :: drop (S c) l. *)
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
      destruct ev_k as [nw w|nvl vl vl'|r].
      + (* Call: check if τ_k = τ *)
        destruct (decide (τ_k = τ)) as [->|Hne].
        * (* τ_k = τ: but Hfirst says no Call(τ) before c. k < c and l !! k = Some (τ, Call nw w) *)
          exfalso. eapply (Hfirst k Hklt). exact Hek.
        * (* τ_k ≠ τ: continue advance *)
          apply (IH (Datatypes.S k) _ _ _ ltac:(lia) ltac:(lia) Heq).
      + apply (IH (Datatypes.S k) _ _ _ ltac:(lia) ltac:(lia) Heq).
      + apply (IH (Datatypes.S k) _ _ _ ltac:(lia) ltac:(lia) Heq).
  Qed.

  (* insert_one_lin case B: when Call(τ) is at position c in ts and k ≤ c,
     the new suffix is drop (c+1) ts. *)
  Lemma insert_one_lin_case_b_suffix τ n v v' prefix k p s c nvc vc :
    call_of_tag ts τ = Some (c, (τ, Call nvc vc)) →
    τ ∉ (filter (is_call ∘ snd) prefix).*1 →
    k ≤ c →
    insert_one_lin τ n v v' prefix (drop k ts) = (p, s) →
    s = drop (Datatypes.S c) ts.
  Proof.
    intros Hcall Hnin Hk Heq.
    unfold insert_one_lin in Heq.
    destruct (decide (τ ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|_]; first done.
    destruct (advance_to_call τ prefix (drop k ts)) as [p' s'] eqn:Hadv.
    injection Heq as <- <-.
    apply list_find_Some in Hcall as (Hlc & [Htag Hcc] & Hfirst).
    simpl in Htag, Hcc. destruct Htag.
    assert (Hnoearlier : ∀ j, j < c → ∀ nv0 v0, ts !! j ≠ Some (τ, Call nv0 v0)).
    { intros j Hjlt nv0 v0 Hjeq.
      apply (Hfirst j (τ, Call nv0 v0) Hjeq Hjlt).
      split; [done|simpl; done]. }
    exact (advance_to_call_at_first ts τ c nvc vc Hlc Hnoearlier k prefix p' s' Hk Hadv).
  Qed.

  (* Invariant through the fold: maintains both (a) s = drop k ts, and
     (b) filter (not∘is_lin∘snd) prefix = take k ts.  From (b), Call(τ_step)
     at position c_step < k must be in prefix.  Combined with case B's
     Hnin (Call not in prefix), we get k ≤ c_step. *)
  Lemma insert_lins_state_drop_bound (rp : nat) ord' prefix k p s :
    (∀ τ', τ' ∈ ord' →
      ∀ c nev ev, call_of_tag ts τ' = Some (c, (τ', Call nev ev)) → c < rp) →
    (∀ τ', τ' ∈ ord' →
      ∃ c nev ev, call_of_tag ts τ' = Some (c, (τ', Call nev ev))) →
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
      destruct (lin_event_val τ_step) as [[n v] v'] eqn:Hval.
      destruct (insert_one_lin τ_step n v v' prefix (drop k ts)) as [p' s'] eqn:Heq.
      unfold insert_one_lin in Heq.
      destruct (decide (τ_step ∈ (filter (is_call ∘ snd) prefix).*1)) as [Hin|Hnin].
      + (* Case A: s' = drop k ts, k' = k.  prefix grows by Lin event. *)
        injection Heq as <- <-.
        (* Goal: invariants preserved for rest.
           prefix' = prefix ++ [(τ_step, Lin n v v')]
           filter not-lin prefix' = filter not-lin prefix = take k ts. *)
        assert (Hprefix'_filt : filter (not ∘ is_lin ∘ snd) (prefix ++ [(τ_step, Lin n v v')])
                                = take k ts).
        { rewrite filter_app.
          rewrite (filter_cons_False _ (τ_step, Lin n v v')); last (simpl; intros Hlin; apply Hlin; done).
          rewrite filter_nil app_nil_r. exact Hprefix_filt. }
        apply (IH _ _ _ _ (λ τ' Hτ' c nev ev H, Hc_bound τ' (proj2 (elem_of_cons _ _ _) (or_intror Hτ')) c nev ev H)
                           (λ τ' Hτ', Hcall_ex τ' (proj2 (elem_of_cons _ _ _) (or_intror Hτ')))
                           Hk Hk_len Hprefix'_filt Hstate).
      + (* Case B *)
        destruct (Hcall_ex τ_step (proj2 (elem_of_cons _ _ _) (or_introl eq_refl))) as (c_step & n_step & ev_step & Hcall_step).
        assert (Hc_bound_step : c_step < rp).
        { apply (Hc_bound τ_step (proj2 (elem_of_cons _ _ _) (or_introl eq_refl)) c_step n_step ev_step Hcall_step). }
        (* Prove k ≤ c_step using the prefix filter invariant. *)
        assert (Hk_step : k ≤ c_step).
        { destruct (decide (k ≤ c_step)) as [|Hgt]; first done.
          exfalso. apply Hnin.
          (* Call(τ_step) at position c_step < k in ts is in take k ts,
             hence in filter not-lin prefix = take k ts. *)
          apply list_find_Some in Hcall_step as (Hlc & _ & _).
          assert (Hin_take : (τ_step, Call n_step ev_step) ∈ take k ts).
          { apply list_elem_of_lookup_2 with c_step.
            rewrite lookup_take_lt; [exact Hlc|lia]. }
          rewrite -Hprefix_filt in Hin_take.
          apply list_elem_of_filter in Hin_take as [_ Hin_p].
          apply (list_elem_of_fmap_2 fst _ (τ_step, Call n_step ev_step)).
          apply list_elem_of_filter_2; [done|exact Hin_p]. }
        destruct (advance_to_call τ_step prefix (drop k ts)) as [p_adv s_adv] eqn:Hadv.
        injection Heq as <- <-.
        apply list_find_Some in Hcall_step as (Hlc & [Htag Hcc] & Hfirst).
        simpl in Htag, Hcc. destruct Htag.
        assert (Hnoearlier : ∀ j, j < c_step → ∀ nv0 v0, ts !! j ≠ Some (τ_step, Call nv0 v0)).
        { intros j Hjlt nv0 v0 Hjeq.
          apply (Hfirst j (τ_step, Call nv0 v0) Hjeq Hjlt).
          split; [done|simpl; done]. }
        assert (Hs_adv : s_adv = drop (Datatypes.S c_step) ts).
        { exact (advance_to_call_at_first ts τ_step c_step n_step ev_step Hlc Hnoearlier
                  k prefix p_adv s_adv Hk_step Hadv). }
        (* Now s' = drop (S c_step) ts after injection. *)
        (* Also, advance_to_call preserves content: p_adv ++ s_adv = prefix ++ drop k ts *)
        assert (Hcontent : p_adv ++ s_adv = prefix ++ drop k ts).
        { exact (advance_to_call_preserves _ _ _ _ _ Hadv). }
        (* New prefix filter: filter not-lin (p_adv ++ [(τ_step, Lin n v v')]) = take (S c_step) ts *)
        assert (Hprefix''_filt :
          filter (not ∘ is_lin ∘ snd) (p_adv ++ [(τ_step, Lin n v v')]) = take (Datatypes.S c_step) ts).
        { rewrite filter_app.
          rewrite (filter_cons_False _ (τ_step, Lin n v v')); last (simpl; intros Hlin; apply Hlin; done).
          rewrite filter_nil app_nil_r.
          (* filter not-lin p_adv = take (S c_step) ts *)
          assert (Hnolinsfx : filter (not ∘ is_lin ∘ snd) s_adv = s_adv).
          { rewrite Hs_adv. apply filter_all_true.
            apply Forall_forall. intros [τ'' ev''] Hin''.
            unfold compose. simpl.
            destruct ev'' as [nr r|nvl vl vl'|r].
            - intros Habs. exact Habs.
            - intros _. apply list_elem_of_lookup_1 in Hin'' as [j Hj].
              rewrite lookup_drop in Hj.
              eapply ts_no_lin_event. eapply list_elem_of_lookup_2. exact Hj.
            - intros Habs. exact Habs. }
          assert (Hnolindrop_k : filter (not ∘ is_lin ∘ snd) (drop k ts) = drop k ts).
          { apply filter_all_true.
            apply Forall_forall. intros [τ'' ev''] Hin''.
            unfold compose. simpl.
            destruct ev'' as [nr r|nvl vl vl'|r].
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
        apply (IH _ _ _ _ (λ τ' Hτ' c nev ev H, Hc_bound τ' (proj2 (elem_of_cons _ _ _) (or_intror Hτ')) c nev ev H)
                           (λ τ' Hτ', Hcall_ex τ' (proj2 (elem_of_cons _ _ _) (or_intror Hτ')))
                           Hk'_rp Hk'_len Hprefix''_filt Hstate).
  Qed.

  (* Main crux lemma. Extended to expose k such that s = drop k ts and k ≤ rp. *)
  Lemma insert_lins_state_process_τ
      (prt : relation trace_op)
      (Hsub : subrelation trace_pre prt)
      (Htrans : Transitive prt)
      (Hirr : Irreflexive prt)
      (Hanti : Antisymmetric trace_op eq prt)
      (τ : positive) (Hτ : τ ∈ events_of_trace ts) ord_before ord_after nvc vc vr rp :
      NoDup (ord_before ++ τ :: ord_after) →
      (∀ τ', τ' ∈ ord_before ++ τ :: ord_after → τ' ∈ events_of_trace ts) →
      (∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
        i < j →
        (ord_before ++ τ :: ord_after) !! i = Some τ1 →
        (ord_before ++ τ :: ord_after) !! j = Some τ2 →
        prt (τ1 ↾ H1) (τ2 ↾ H2)) →
      filter (λ x, x.1 = τ) ts = [(τ, Call nvc vc); (τ, Ret vr)] →
      ret_of_tag ts τ = Some (rp, (τ, Ret vr)) →
      ∀ p s,
        insert_lins_state ord_before [] ts = (p, s) →
        filter (λ x, x.1 = τ) (p ++ s) = [(τ, Call nvc vc); (τ, Ret vr)] ∧
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
      ∀ c nev ev, call_of_tag ts τ' = Some (c, (τ', Call nev ev)) → c < rp).
    { intros τ' Hτ'_in c nev ev Hcall.
      eapply (prt_sorted_call_before_ret_pos prt Hsub Htrans Hirr Hanti
                τ Hτ ord_before ord_after rp vr
                Hnd Hsub_ord Hsorted Hret_τ τ' c nev ev Hτ'_in Hcall). }
    assert (Hcall_ex : ∀ τ', τ' ∈ ord_before →
      ∃ c nev ev, call_of_tag ts τ' = Some (c, (τ', Call nev ev))).
    { intros τ' Hτ'_in.
      assert (Hτ'_ev : τ' ∈ events_of_trace ts).
      { apply Hsub_ord. apply elem_of_app. left. exact Hτ'_in. }
      destruct (Hcomplete τ') as (nvc' & vc' & vr' & [Hempty|Hfilt']).
      { exfalso. unfold events_of_trace in Hτ'_ev.
        apply elem_of_list_to_set in Hτ'_ev.
        apply list_elem_of_fmap_1 in Hτ'_ev as ([τ'' ev''] & Heq & Hin'').
        simpl in Heq. subst τ''.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ')) in Hin'' as Hfilt_in; last done.
        rewrite Hempty in Hfilt_in. set_solver. }
      destruct (call_of_tag_pos τ' nvc' vc' vr' Hfilt') as (c & Hcall).
      exists c, nvc', vc'. exact Hcall. }
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

  (* Helper: c < rp when filter ts = [Call nvc vc; Ret vr].
     Uses the minimality property of list_find. *)
  Lemma call_lt_ret_pos τ nvc vc vr c rp :
    filter (λ x, x.1 = τ) ts = [(τ, Call nvc vc); (τ, Ret vr)] →
    call_of_tag ts τ = Some (c, (τ, Call nvc vc)) →
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
      assert (Hcall_nin_take : (τ, Call nvc vc) ∉ take (Datatypes.S rp) ts).
      { intros Hin'. apply list_elem_of_lookup_1 in Hin' as [j Hj].
        apply lookup_take_Some in Hj as [Hj_ts Hj_lt].
        apply (Hcall_min j (τ, Call nvc vc) Hj_ts ltac:(lia)).
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

  Lemma ts'_lin_per_tag_linearized
      (prt : relation trace_op)
      (Hsub : subrelation trace_pre prt)
      (Htrans : Transitive prt)
      (Hirr : Irreflexive prt)
      (Hanti : Antisymmetric trace_op eq prt)
      ord
      (Hord : ∀ τ, τ ∈ ord ↔ τ ∈ events_of_trace ts)
      (Hnd : NoDup ord)
      (Hord_sorted : ∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
        i < j → ord !! i = Some τ1 → ord !! j = Some τ2 →
        prt (τ1 ↾ H1) (τ2 ↾ H2)) :
    per_tag_linearized (ts'_lin ord).
  Proof.
    intros τ.
    destruct (decide (τ ∈ ord)) as [Hin_ord|Hnin_ord]; last first.
    { (* τ ∉ ord: no Lin for τ added; filter (tag=τ) (ts'_lin ord) = filter (tag=τ) ts *)
      unfold ts'_lin.
      rewrite (insert_lins_in_order_tag_notin_ord _ _ _ _ Hnin_ord).
      simpl.
      destruct (Hcomplete τ) as (nvc & vc & vr & [Hfilt|Hfilt]).
      - exists nvc, vc, vr. rewrite Hfilt. apply prefix_nil.
      - exfalso.
        apply Hnin_ord. apply Hord.
        unfold events_of_trace. apply elem_of_list_to_set.
        apply (list_elem_of_fmap_2 fst _ (τ, Call nvc vc)).
        apply (list_elem_of_filter_1 (λ x, x.1 = τ)).
        rewrite Hfilt. set_solver. }
    (* τ ∈ ord *)
    apply Hord in Hin_ord as Hin_et.
    destruct (Hcomplete τ) as (nvc & vc & vr & [Hempty|Hfilt]).
    { exfalso.
      unfold events_of_trace in Hin_et.
      apply elem_of_list_to_set in Hin_et.
      apply list_elem_of_fmap_1 in Hin_et as ([τ' ev] & Heq & Hin_ts).
      simpl in Heq. subst τ'.
      apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hin_ts as Hin_τ; last done.
      rewrite Hempty in Hin_τ. set_solver. }
    exists nvc, vc, vr.
    (* Split ord at τ *)
    apply list_elem_of_split in Hin_ord as (ord_before & ord_after & Hord_split).
    (* Unfold *)
    unfold ts'_lin.
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
    destruct (ret_of_tag_pos τ nvc vc vr Hfilt) as (rp & Hret_τ).
    destruct (call_of_tag_pos τ nvc vc vr Hfilt) as (c_τ & Hcall_τ).
    pose proof (call_lt_ret_pos τ nvc vc vr c_τ rp Hfilt Hcall_τ Hret_τ) as Hc_lt_rp.
    destruct (insert_lins_state_process_τ prt Hsub Htrans Hirr Hanti
                τ Hin_et ord_before ord_after nvc vc vr rp
                Hnd' Hsub_ord Hsorted' Hfilt Hret_τ _ _ Hstate1)
      as (Hfilt1 & (k1 & Hk1_le & Hs1_eq & Hp1_filt) & Hret_s1).
    (* Process τ: simpl should unfold the cons case *)
    simpl.
    rewrite (lin_event_val_of τ nvc vc vr Hfilt).
    destruct (insert_one_lin τ nvc vc vr p1 s1) as [p2 s2] eqn:Hstate2.
    assert (Hfilt2 : filter (λ x, x.1 = τ) (p2 ++ s2) = [(τ, Call nvc vc); (τ, Lin nvc vc vr); (τ, Ret vr)]).
    { (* Use advance_to_call_at_first to fully characterize s_adv and p_adv filter. *)
      unfold insert_one_lin in Hstate2.
      destruct (decide (τ ∈ (filter (is_call ∘ snd) p1).*1)) as [Hin|Hnin].
      - (* Case A: Call(τ) ∈ p1. *)
        injection Hstate2 as <- <-.
        (* Show filter p1 = [Call nvc vc] and filter s1 = [Ret vr] *)
        assert (Hcall_in_p1 : (τ, Call nvc vc) ∈ p1).
        { apply list_elem_of_fmap_1 in Hin as ([τ'' ev''] & Heq & Hin_p1).
          simpl in Heq. subst τ''.
          apply list_elem_of_filter in Hin_p1 as [Hcall Hin_p1].
          destruct ev'' as [nw w| |]; simpl in Hcall; try done.
          (* (τ, Call nw w) ∈ p1 ⊆ non-Lin events of p1 ⊆ take k1 ts by invariant.
             In ts, Call(τ) at unique position c_τ with value vc. So w = vc. *)
          assert (Hin_nlp1 : (τ, Call nw w) ∈ filter (not ∘ is_lin ∘ snd) p1).
          { apply list_elem_of_filter_2; [intros Habs; exact Habs|exact Hin_p1]. }
          rewrite Hp1_filt in Hin_nlp1.
          apply list_elem_of_lookup_1 in Hin_nlp1 as [j Hj].
          apply lookup_take_Some in Hj as [Hj_ts _].
          (* ts !! j = Some (τ, Call nw w).  filter (tag=τ) ts = [Call nvc vc; Ret vr].
             So (τ, Call nw w) ∈ filter = {Call nvc vc, Ret vr}.  Since Call nw w ≠ Ret vr (different ctors),
             Call nw w = Call nvc vc, so w = vc. *)
          assert (Hin_filt_ts : (τ, Call nw w) ∈ filter (λ x, x.1 = τ) ts).
          { apply list_elem_of_filter_2; [done|].
            eapply list_elem_of_lookup_2. exact Hj_ts. }
          rewrite Hfilt in Hin_filt_ts.
          rewrite !elem_of_cons elem_of_nil in Hin_filt_ts.
          destruct Hin_filt_ts as [Heq'|[Heq'|[]]]; [injection Heq' as <- <-|discriminate].
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
        assert (Hfilt_p1 : filter (λ x, x.1 = τ) p1 = [(τ, Call nvc vc)]).
        { (* Has Call nvc vc, doesn't have Ret vr. filter p1 ⊆ filter (p1 ++ s1) = [Call; Ret].
             filter p1 contains Call, not Ret.  So filter p1 = [Call nvc vc]. *)
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
        rewrite (filter_cons_True _ (τ, Lin nvc vc vr) _); last done.
        rewrite filter_nil. done.
      - (* Case B: Call(τ) ∉ p1. *)
        destruct (advance_to_call τ p1 s1) as [p_adv s_adv] eqn:Hadv.
        injection Hstate2 as <- <-.
        (* Prove k1 ≤ c_τ: if k1 > c_τ, Call is in take k1 ts = filter not-lin p1, hence in p1. *)
        assert (Hk1_le_c : k1 ≤ c_τ).
        { destruct (decide (k1 ≤ c_τ)) as [|Hgt]; first done.
          exfalso. apply Hnin.
          apply list_find_Some in Hcall_τ as (Hlc & _ & _).
          assert (Hcall_in_take : (τ, Call nvc vc) ∈ take k1 ts).
          { apply list_elem_of_lookup_2 with c_τ.
            rewrite lookup_take_lt; [exact Hlc|lia]. }
          rewrite -Hp1_filt in Hcall_in_take.
          apply list_elem_of_filter_1 in Hcall_in_take.
          apply (list_elem_of_fmap_2 fst _ (τ, Call nvc vc)).
          apply list_elem_of_filter_2; [done|exact Hcall_in_take]. }
        (* s_adv = drop (S c_τ) ts via advance_to_call_at_first *)
        apply list_find_Some in Hcall_τ as (Hlc & _ & Hcall_min).
        assert (Hnoearlier : ∀ j, j < c_τ → ∀ nv0 v0, ts !! j ≠ Some (τ, Call nv0 v0)).
        { intros j Hjlt nv0 v0 Hjeq.
          apply (Hcall_min j (τ, Call nv0 v0) Hjeq Hjlt).
          split; [done|simpl; done]. }
        assert (Hs_adv_eq : s_adv = drop (Datatypes.S c_τ) ts).
        { rewrite Hs1_eq in Hadv.
          exact (advance_to_call_at_first ts τ c_τ nvc vc Hlc Hnoearlier
                  k1 p1 p_adv s_adv Hk1_le_c Hadv). }
        (* Compute filter (tag=τ) of take (S c_τ) ts: it's exactly [(τ, Call nvc vc)].
           Then filter (tag=τ) (drop (S c_τ) ts) = [(τ, Ret vr)] by filter_app on ts. *)
        assert (Hfilt_take_Sct : filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts)
                                  = [(τ, Call nvc vc)]).
        { (* take (S c_τ) ts has tag-τ elements only from call at c_τ.
             No Call(τ) before c_τ (Hcall_min / Hnoearlier).  No Ret(τ) before c_τ
             (Ret at rp > c_τ). *)
          apply list_find_Some in Hret_τ as (Hlr & _ & Hret_min).
          (* Call nvc vc is at position c_τ < S c_τ, so in take (S c_τ) ts. *)
          assert (Hcall_in_take : (τ, Call nvc vc) ∈ take (Datatypes.S c_τ) ts).
          { apply list_elem_of_lookup_2 with c_τ.
            rewrite lookup_take_lt; [exact Hlc|lia]. }
          (* No other tag-τ element in take (S c_τ) ts. *)
          assert (Hno_other : ∀ y, y ∈ take (Datatypes.S c_τ) ts → y.1 = τ → y = (τ, Call nvc vc)).
          { intros [τ'' ev''] Hin Htag. simpl in Htag. subst τ''.
            apply list_elem_of_lookup_1 in Hin as [j Hj].
            apply lookup_take_Some in Hj as [Hj_ts Hj_lt].
            (* ts !! j = Some (τ, ev'') with j < S c_τ, i.e., j ≤ c_τ. *)
            destruct ev'' as [nw w|vl vl'|r].
            - (* Call: by Hcall_min and j ≤ c_τ, j < c_τ impossible (would contradict Hcall_min).
                 So j = c_τ, then ts !! c_τ = Some (τ, Call nw w) and also = Some (τ, Call nvc vc).
                 So w = vc. *)
              destruct (decide (j < c_τ)) as [Hjlt|Hjge].
              + exfalso. apply (Hcall_min j (τ, Call nw w) Hj_ts Hjlt).
                split; [done|simpl; done].
              + assert (j = c_τ) by lia. subst j.
                rewrite Hj_ts in Hlc. injection Hlc as Hnw Hw. congruence.
            - (* Lin: doesn't happen in ts *)
              exfalso. eapply ts_no_lin_event.
              eapply list_elem_of_lookup_2. exact Hj_ts.
            - (* Ret: at position j, but Ret at rp > c_τ ≥ j. Contradiction via Hret_min. *)
              exfalso. apply (Hret_min j (τ, Ret r) Hj_ts ltac:(lia)).
              split; [done|simpl; done]. }
          (* So filter = [Call nvc vc] *)
          destruct (filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts)) as [|z1 [|z2 rest_z]] eqn:Hftake.
          - exfalso. apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hcall_in_take; last done.
            rewrite Hftake in Hcall_in_take. set_solver.
          - assert (Hz1_in : z1 ∈ filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts)).
            { rewrite Hftake. apply elem_of_cons. left. done. }
            apply list_elem_of_filter in Hz1_in as [Hz1_tag Hz1_in_take].
            assert (Hz1_eq : z1 = (τ, Call nvc vc)).
            { apply Hno_other; assumption. }
            subst z1. done.
          - (* ≥ 2 elements.  z2 must be (τ, Call nvc vc) by Hno_other.  But then filter has two
               copies of (τ, Call nvc vc), meaning Call nvc vc appears at 2+ positions in take.  But
               Call nvc vc appears at most once in ts (uniqueness from Hcall_min). *)
            exfalso.
            (* filter has z1 and z2, both ≠ Ret vr (they're tag-τ elements of take).
               By Hno_other, both equal (τ, Call nvc vc). *)
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
            (* (τ, Call nvc vc) appears at 2+ positions in take (S c_τ) ts (corresponding to
               filter indices 0 and 1). *)
            apply list_elem_of_lookup_1 in Hz1_tk as [j1 Hj1].
            apply list_elem_of_lookup_1 in Hz2_tk as [j2 Hj2].
            apply lookup_take_Some in Hj1 as [Hj1_ts Hj1_lt].
            apply lookup_take_Some in Hj2 as [Hj2_ts Hj2_lt].
            assert (Hj1_eq : j1 = c_τ).
            { destruct (decide (j1 < c_τ)) as [Hlt|Hge].
              - exfalso. apply (Hcall_min j1 (τ, Call nvc vc) Hj1_ts Hlt).
                split; [done|simpl; done].
              - lia. }
            assert (Hj2_eq : j2 = c_τ).
            { destruct (decide (j2 < c_τ)) as [Hlt|Hge].
              - exfalso. apply (Hcall_min j2 (τ, Call nvc vc) Hj2_ts Hlt).
                split; [done|simpl; done].
              - lia. }
            subst j1 j2.
            assert (Hoccurs_once : ∀ j j', take (Datatypes.S c_τ) ts !! j = Some (τ, Call nvc vc) →
                                           take (Datatypes.S c_τ) ts !! j' = Some (τ, Call nvc vc) →
                                           j = j').
            { intros j j' Hj Hj'.
              apply lookup_take_Some in Hj as [Hj_ts Hj_lt].
              apply lookup_take_Some in Hj' as [Hj'_ts Hj'_lt].
              assert (j = c_τ).
              { destruct (decide (j < c_τ)) as [Hlt|Hge].
                - exfalso. apply (Hcall_min j (τ, Call nvc vc) Hj_ts Hlt).
                  split; [done|simpl; done].
                - lia. }
              assert (j' = c_τ).
              { destruct (decide (j' < c_τ)) as [Hlt|Hge].
                - exfalso. apply (Hcall_min j' (τ, Call nvc vc) Hj'_ts Hlt).
                  split; [done|simpl; done].
                - lia. }
              lia. }
            (* Now filter has (τ, Call nvc vc) at filter-positions 0 and 1.  By filter_preserves_order_gen,
               get distinct ts positions.  But Hoccurs_once says same position.  Contradiction. *)
            (* filter_preserves_order_gen isn't in our toolkit directly; let me use list_filter_lookup_orig twice. *)
            assert (Hf0 : filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts) !! 0 = Some (τ, Call nvc vc)).
            { rewrite Hftake. done. }
            assert (Hf1 : filter (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts) !! 1 = Some (τ, Call nvc vc)).
            { rewrite Hftake. done. }
            pose proof (filter_NoDup_at (λ x, x.1 = τ) (take (Datatypes.S c_τ) ts) (τ, Call nvc vc) 0 1
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
        assert (Hfilt_p_adv : filter (λ x, x.1 = τ) p_adv = [(τ, Call nvc vc)]).
        { (* filter (tag=τ) (p_adv ++ s_adv) = filter (tag=τ) (p1 ++ s1) = [Call nvc vc; Ret vr] *)
          apply (f_equal (filter (λ x, x.1 = τ))) in Hpres.
          assert (Hfilt_adv_union : filter (λ x, x.1 = τ) (p_adv ++ s_adv)
                                      = [(τ, Call nvc vc); (τ, Ret vr)]).
          { rewrite Hpres. exact Hfilt1. }
          rewrite filter_app Hfilt_s_adv in Hfilt_adv_union.
          (* filter p_adv ++ [Ret vr] = [Call nvc vc; Ret vr], so filter p_adv = [Call nvc vc]. *)
          destruct (filter (λ x, x.1 = τ) p_adv) as [|z1 [|z2 rest]] eqn:Hfpa.
          - simpl in Hfilt_adv_union. discriminate.
          - simpl in Hfilt_adv_union.
            by inversion Hfilt_adv_union.
          - exfalso. apply (f_equal length) in Hfilt_adv_union.
            rewrite !length_app /= in Hfilt_adv_union. simpl in Hfilt_adv_union. lia. }
        rewrite !filter_app Hfilt_p_adv Hfilt_s_adv.
        rewrite (filter_cons_True _ (τ, Lin nvc vc vr) _); last done.
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
  Lemma advance_to_call_suffix_no_lin τ prefix suffix :
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
  Lemma advance_to_call_prefix_lin τ prefix suffix :
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
  Lemma insert_one_lin_lin_subseq τ n v v' prefix suffix :
    filter (is_lin ∘ snd) suffix = [] →
    ∀ p s, insert_one_lin τ n v v' prefix suffix = (p, s) →
    filter (is_lin ∘ snd) s = [] ∧
    (filter (is_lin ∘ snd) p).*1
      = (filter (is_lin ∘ snd) prefix).*1 ++ [τ].
  Proof.
    intros Hlin p s Heq.
    unfold insert_one_lin in Heq.
    assert (Hsingle : filter (is_lin ∘ snd) [(τ, Lin n v v')] = [(τ, Lin n v v')]).
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
  Lemma insert_lins_in_order_lin_subseq ord prefix suffix :
    filter (is_lin ∘ snd) suffix = [] →
    (filter (is_lin ∘ snd) (insert_lins_in_order ord prefix suffix)).*1
      = (filter (is_lin ∘ snd) prefix).*1 ++ ord.
  Proof.
    revert prefix suffix. induction ord as [|τ rest IH]; intros prefix suffix Hlin.
    - simpl. rewrite app_nil_r filter_app Hlin app_nil_r. done.
    - simpl. destruct (lin_event_val τ) as [[n v] v'] eqn:Hval.
      destruct (insert_one_lin τ n v v' prefix suffix) as [p s] eqn:Heq.
      pose proof (insert_one_lin_lin_subseq _ _ _ _ _ _ Hlin _ _ Heq) as [Hs_lin Hp_lin].
      rewrite IH; last exact Hs_lin.
      rewrite Hp_lin.
      by rewrite -app_assoc.
  Qed.

  Lemma ts_filter_lin_empty :
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

  Lemma ts'_lin_lin_filter ord
      (Hord : ∀ τ, τ ∈ ord ↔ τ ∈ events_of_trace ts)
      (Hnd : NoDup ord) :
    (filter (is_lin ∘ snd) (ts'_lin ord)).*1 = ord.
  Proof.
    unfold ts'_lin.
    rewrite insert_lins_in_order_lin_subseq; last exact ts_filter_lin_empty.
    simpl. done.
  Qed.

  (* ===== Stronger: the full Lin-event filter list ===== *)
  Definition lin_events_of_ord (ord : list positive) : list (positive * trace) :=
    map (λ τ, (τ, Lin (lin_event_val τ).1.1 (lin_event_val τ).1.2 (lin_event_val τ).2)) ord.

  Lemma insert_one_lin_lin_events τ n v v' prefix suffix p s :
    filter (is_lin ∘ snd) suffix = [] →
    insert_one_lin τ n v v' prefix suffix = (p, s) →
    filter (is_lin ∘ snd) p = filter (is_lin ∘ snd) prefix ++ [(τ, Lin n v v')].
  Proof.
    intros Hlin Heq.
    unfold insert_one_lin in Heq.
    assert (Hlin_single : filter (is_lin ∘ snd) [(τ, Lin n v v')] = [(τ, Lin n v v')]).
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

  Lemma insert_lins_in_order_lin_events ord prefix suffix :
    filter (is_lin ∘ snd) suffix = [] →
    filter (is_lin ∘ snd) (insert_lins_in_order ord prefix suffix)
      = filter (is_lin ∘ snd) prefix ++ lin_events_of_ord ord.
  Proof.
    revert prefix suffix. induction ord as [|τ rest IH]; intros prefix suffix Hlin.
    - simpl. rewrite app_nil_r filter_app Hlin app_nil_r. done.
    - simpl. destruct (lin_event_val τ) as [[n v] v'] eqn:Hval.
      destruct (insert_one_lin τ n v v' prefix suffix) as [p s] eqn:Heq.
      pose proof (insert_one_lin_lin_events _ _ _ _ _ _ _ _ Hlin Heq) as Hp_lin.
      pose proof (insert_one_lin_lin_subseq _ _ _ _ _ _ Hlin _ _ Heq) as [Hs_lin _].
      rewrite IH; last exact Hs_lin.
      rewrite Hp_lin.
      unfold lin_events_of_ord. simpl map.
      replace ((lin_event_val τ).1.1) with n by (rewrite Hval; done).
      replace ((lin_event_val τ).1.2) with v by (rewrite Hval; done).
      replace ((lin_event_val τ).2) with v' by (rewrite Hval; done).
      by rewrite -app_assoc.
  Qed.

  Lemma ts'_lin_lin_filter_events ord :
    filter (is_lin ∘ snd) (ts'_lin ord) = lin_events_of_ord ord.
  Proof.
    unfold ts'_lin.
    rewrite insert_lins_in_order_lin_events; last exact ts_filter_lin_empty.
    simpl. done.
  Qed.

  (* ===== Queue state reconstruction ===== *)

  Definition push_value_of (τ : positive) : val :=
    match lin_event_val τ with
    | (0, v, _) => v
    | _ => #()
    end.

  Lemma push_value_of_push τ v vr :
    filter (λ x, x.1 = τ) ts = [(τ, Call Push v); (τ, Ret vr)] →
    push_value_of τ = v.
  Proof.
    intros Hfilt. unfold push_value_of. unfold lin_event_val. rewrite Hfilt. done.
  Qed.

  (* Predicate: τ has a matched pop in `all`. Decidable since bounded by `m`. *)
  Definition has_matched_pop_in (τ : positive) (all : list positive) : Prop :=
    Exists (λ p : positive * positive, p.1 = τ ∧ p.2 ∈ all) m.

  Global Instance has_matched_pop_in_dec τ all : Decision (has_matched_pop_in τ all).
  Proof. unfold has_matched_pop_in. apply Exists_dec. intros p. apply _. Defined.

  Lemma has_matched_pop_in_iff τ all :
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

  Fixpoint live_pushes_aux (sub : list positive) (all : list positive) : list positive :=
    match sub with
    | [] => []
    | τ :: rest =>
      let tail := live_pushes_aux rest all in
      if decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ all)
      then τ :: tail
      else tail
    end.

  Definition live_pushes_of (sub : list positive) : list positive :=
    live_pushes_aux sub sub.



  Lemma live_pushes_aux_app sub1 sub2 all :
    live_pushes_aux (sub1 ++ sub2) all
      = live_pushes_aux sub1 all ++ live_pushes_aux sub2 all.
  Proof.
    induction sub1 as [|τ rest IH]; first done.
    simpl. rewrite IH.
    by destruct (decide _).
  Qed.

  Lemma live_pushes_aux_change_all sub all1 all2 :
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
  Lemma has_matched_pop_in_snoc τ all x :
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
  Lemma push_not_in_matched_pop τ_p τ :
    τ ∈ push_of_trace ts → ¬ (τ_p, τ) ∈ m.
  Proof.
    intros Hpush Hin.
    pose proof (valid_match_call_pop _ _ _ _ Hvalid Hin) as Hcall_pop.
    destruct (push_tag_in_trace _ _ Hpush) as [v Hcall_push].
    destruct (Hcomplete τ) as (nvc & vc & vr & [Hfilt|Hfilt]).
    { assert (Hin_push : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts).
      { apply list_elem_of_filter_2; done. }
      rewrite Hfilt in Hin_push. set_solver. }
    assert (Hin_push : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts)
      by (apply list_elem_of_filter_2; done).
    assert (Hin_pop : (τ, Call Pop #()) ∈ filter (λ x, x.1 = τ) ts)
      by (apply list_elem_of_filter_2; done).
    rewrite Hfilt in Hin_push, Hin_pop.
    rewrite !elem_of_cons elem_of_nil in Hin_push.
    rewrite !elem_of_cons elem_of_nil in Hin_pop.
    destruct Hin_push as [Heq_push|[Heq_push|[]]]; destruct Hin_pop as [Heq_pop|[Heq_pop|[]]];
      try discriminate.
    injection Heq_push as Hnp _.
    injection Heq_pop as Hnq _.
    subst nvc. discriminate Hnq.
  Qed.

  (* Live pushes aux is stable under adding a push to `all`. *)
  Lemma live_pushes_aux_push_all sub all τ_new :
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


  (* Step: a non-push pop (τ ∉ push_of_trace) doesn't add a new push to the queue,
     but may remove a push τ_p from live if (τ_p, τ) ∈ m. *)
  Lemma live_pushes_aux_pop_all sub all τ_new :
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


  (* live_pushes are always in push_of_trace. *)
  Lemma live_pushes_aux_subseteq_push sub all τ :
    τ ∈ live_pushes_aux sub all → τ ∈ push_of_trace ts.
  Proof.
    revert τ. induction sub as [|τ' rest IH]; intros τ Hin; first by inversion Hin.
    simpl in Hin.
    destruct (decide (τ' ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ' all)) as [[Hp _]|_].
    - apply elem_of_cons in Hin as [->|Hin]; first done. by eapply IH.
    - by eapply IH.
  Qed.

  Lemma live_pushes_subseteq_push sub τ :
    τ ∈ live_pushes_of sub → τ ∈ push_of_trace ts.
  Proof. apply live_pushes_aux_subseteq_push. Qed.

  (* live_pushes_aux sub all is a sublist of sub. *)
  Lemma live_pushes_aux_sublist sub all τ :
    τ ∈ live_pushes_aux sub all → τ ∈ sub.
  Proof.
    revert τ. induction sub as [|τ' rest IH]; intros τ Hin; first by inversion Hin.
    simpl in Hin.
    destruct (decide _) as [_|_].
    - apply elem_of_cons in Hin as [->|Hin]; first by apply elem_of_cons; left.
      apply elem_of_cons. right. by eapply IH.
    - apply elem_of_cons. right. by eapply IH.
  Qed.

  Lemma live_pushes_sublist sub τ :
    τ ∈ live_pushes_of sub → τ ∈ sub.
  Proof. apply live_pushes_aux_sublist. Qed.

  Lemma live_pushes_aux_not_matched sub all τ :
    τ ∈ live_pushes_aux sub all → ¬ has_matched_pop_in τ all.
  Proof.
    revert τ. induction sub as [|τ' rest IH]; intros τ Hin; first by inversion Hin.
    simpl in Hin.
    destruct (decide (τ' ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ' all)) as [[_ Hnm]|_].
    - apply elem_of_cons in Hin as [->|Hin]; [done|by eapply IH].
    - by eapply IH.
  Qed.

  Lemma live_pushes_not_matched sub τ :
    τ ∈ live_pushes_of sub → ¬ has_matched_pop_in τ sub.
  Proof. apply live_pushes_aux_not_matched. Qed.

  (* NoDup preservation. *)
  Lemma NoDup_live_pushes_aux sub all :
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

  Lemma NoDup_live_pushes sub :
    NoDup sub → NoDup (live_pushes_of sub).
  Proof. apply NoDup_live_pushes_aux. Qed.

  (* Helper: a list's filter with a predicate that's always true equals the list. *)
  Lemma List_filter_all_true {A} (P : A → bool) (l : list A) :
    (∀ x, x ∈ l → P x = true) →
    List.filter P l = l.
  Proof.
    induction l as [|x rest IH]; first done.
    intros Hall. simpl.
    rewrite (Hall x (proj2 (elem_of_cons _ _ _) (or_introl eq_refl))).
    f_equal. apply IH. intros y Hin. apply Hall. apply elem_of_cons. by right.
  Qed.

  (* All-true-filter on a list: if no τ_q in l has (τ_q, τ) ∈ m, filter is identity. *)
  Lemma filter_out_matched_all_none (l : list positive) τ :
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
  Lemma filter_out_matched_head (l : list positive) τ_p τ :
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
  Lemma push_tag_filter (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts) τ :
    τ ∈ push_of_trace ts →
    ∃ v, filter (λ x, x.1 = τ) ts = [(τ, Call Push v); (τ, Ret #())].
  Proof.
    intros Hpush.
    destruct (push_tag_in_trace _ _ Hpush) as [v Hcall].
    assert (Hin_filt : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts).
    { apply list_elem_of_filter_2; done. }
    destruct (Hcomplete τ) as (nvc & vc & vr & [Hempty|Hfilt]).
    { rewrite Hempty in Hin_filt. set_solver. }
    destruct (Hper_tag_wf τ) as [[w [_ Hpfx]]|[r [_ Hpfx]]].
    - rewrite Hfilt in Hpfx.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as Heq1.
      apply prefix_cons_inv_2 in Hpfx as Hpfx1.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx1) as Heq2.
      injection Heq1 as Hnvc Hvc.
      injection Heq2 as Hvr.
      subst nvc vc vr.
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
      injection Hcall_eq as Hncall_eq Hcall_eq.
      rewrite Hfilt in Hin_filt.
      rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_filt.
      destruct Hin_filt as [Heq|[Heq|[]]]; [|discriminate].
      by simplify_eq.
  Qed.

  (* For pop τ: filter (tag=τ) ts = [(τ, Call Pop); (τ, Ret (encode_response r))]. *)
  Lemma pop_tag_filter (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts) τ :
    τ ∈ pop_of_trace ts →
    ∃ r, filter (λ x, x.1 = τ) ts = [(τ, Call Pop #()); (τ, Ret (encode_response r))].
  Proof.
    intros Hpop.
    pose proof (pop_tag_in_trace _ _ Hpop) as Hcall.
    assert (Hin_filt : (τ, Call Pop #()) ∈ filter (λ x, x.1 = τ) ts).
    { apply list_elem_of_filter_2; done. }
    destruct (Hcomplete τ) as (nvc & vc & vr & [Hempty|Hfilt]).
    { rewrite Hempty in Hin_filt. set_solver. }
    destruct (Hper_tag_wf τ) as [[w [_ Hpfx]]|[r [_ Hpfx]]].
    - (* push pattern — contradicts τ ∈ pop_of_trace *)
      exfalso.
      rewrite Hfilt in Hpfx.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as Hcall_eq.
      injection Hcall_eq as Hncall_eq Hcall_eq.
      rewrite Hfilt in Hin_filt.
      rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_filt.
      destruct Hin_filt as [Heq|[Heq|[]]]; [|discriminate].
      by simplify_eq.
    - rewrite Hfilt in Hpfx.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as Heq1.
      apply prefix_cons_inv_2 in Hpfx as Hpfx1.
      pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx1) as Heq2.
      injection Heq1 as Hnvc Hvc.
      injection Heq2 as Hvr.
      subst nvc vc vr.
      exists r. exact Hfilt.
  Qed.

  (* For matched pop τ (τ_p, τ) ∈ m: filter has Ret (NonEmpty v) where v is τ_p's push value. *)
  Lemma matched_pop_filter (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts) τ_p τ v :
    (τ_p, τ) ∈ m →
    (τ_p, Call Push v) ∈ ts →
    τ ∈ pop_of_trace ts →
    filter (λ x, x.1 = τ) ts = [(τ, Call Pop #());
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
      destruct (Hcomplete τ_p) as (nvc_p & vc_p & vr_p & [Hempty_p|Hfilt_p]).
      { assert (Hin_p : (τ_p, Call Push v) ∈ filter (λ x, x.1 = τ_p) ts)
          by (apply list_elem_of_filter_2; done).
        rewrite Hempty_p in Hin_p. set_solver. }
      assert (Hin_v : (τ_p, Call Push v) ∈ filter (λ x, x.1 = τ_p) ts)
        by (apply list_elem_of_filter_2; done).
      assert (Hin_v' : (τ_p, Call Push v') ∈ filter (λ x, x.1 = τ_p) ts)
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
  Lemma empty_pop_filter (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts) τ :
    τ ∈ pop_of_trace ts → τ ∉ m.*2 →
    filter (λ x, x.1 = τ) ts = [(τ, Call Pop #());
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
  Lemma live_pushes_aux_empty sub all :
    (∀ τ_q, τ_q ∈ sub → ¬ (τ_q ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ_q all)) →
    live_pushes_aux sub all = [].
  Proof.
    induction sub as [|τ rest IH]; first done.
    intros Hall. simpl.
    destruct (decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ all)) as [Hlive|Hnlive].
    - exfalso. apply (Hall τ); [|done]. apply elem_of_cons. left. done.
    - apply IH. intros τ_q Hin. apply Hall. apply elem_of_cons. right. done.
  Qed.

  Lemma live_pushes_aux_head_decomp sub all τ_p prefix suffix :
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
End binder.
