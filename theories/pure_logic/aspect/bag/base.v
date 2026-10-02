From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.models Require Export bag_like.

Section relations.
  Context (ts : list (positive*trace)).

  (* A pair of push/pop (τ1,τ2) covers index i iif
    idx(Ret τ1) < i < idx(Call τ2)
    This means at index i, the value pushed by the push must be in the bag. *)
  Definition push_pop_covers (τ1 τ2 : positive) (i : nat) :=
    default False (
      iret ← ret_of_tag ts τ1;
      icall ← call_of_tag ts τ2;
      mret (iret.1 < i < icall.1)).

  Definition dangling_push_covers (τ1 : positive) (i : nat) :=
    default False ((λ iret, iret.1 < i) <$> ret_of_tag ts τ1).

  (* A pop(∅) is linearizable iff it is not covered by any push/pop pair at some point. *)
  Definition pop_empty_linearizable (m : list (positive*positive)) (τ : positive) :=
    ∃ icall iret i, ts !! icall = Some (τ, Call Pop #())
                  ∧ ts !! iret = Some (τ, Ret (encode_response IsEmpty))
                  ∧ icall ≤ i ≤ iret
                  ∧ (∀ τ1 τ2, (τ1,τ2) ∈ m → ¬ push_pop_covers τ1 τ2 i)
                  ∧ (∀ τ1, τ1 ∈ push_of_trace ts ∧ τ1 ∉ m.*1 → ¬ dangling_push_covers τ1 i).

  Definition per_tag_pop_empty_sound m :=
    ∀ τ, τ ∈ (filter (is_ret_pop_emp∘snd) ts).*1 → pop_empty_linearizable m τ.

  (* TODO: consider moving this definition to linear.v *)
  (* The [e ≺c e'] relation.
    This is also the standard defintion of precedence. *)
  Definition pre_of_trace : relation positive :=
    λ τ1 τ2,
      default False (ret1 ← ret_of_tag ts τ1;
      call2 ← call_of_tag ts τ2;
      mret (ret1.1 < call2.1)).

  (* The total order relation extracted from a linearized trace. *)
  Definition prt_of_trace : relation positive :=
    λ τ1 τ2,
      default False (lin1 ← lin_of_tag ts τ1;
      lin2 ← lin_of_tag ts τ2;
      mret (lin1.1 < lin2.1)).

  Global Instance pre_of_trace_decision τ1 τ2 : Decision (pre_of_trace τ1 τ2).
  Proof.
    rewrite /pre_of_trace.
    destruct ret_of_tag; simpl; last solve_decision.
    destruct call_of_tag; simpl; solve_decision.
  Defined.

  Global Instance prt_of_trace_decision τ1 τ2 : Decision (prt_of_trace τ1 τ2).
  Proof.
    rewrite /prt_of_trace.
    destruct (lin_of_tag ts τ1); simpl; last solve_decision.
    destruct (lin_of_tag ts τ2); simpl; solve_decision.
  Defined.

  (* A match is a list of (call tag,ret tag) pairs that relates a pop with a push *)
  Definition valid_match (m : list (positive*positive)) : Prop :=
    pop_val_of_trace ts ⊆ m.*2 (* every finished pop is matched *)
  ∧ (NoDup m.*1 ∧ NoDup m.*2) (* injective in both directions *)
  ∧ Forall (λ '(τ1,τ2), ¬ pre_of_trace τ2 τ1 (* Push starts before Pop finishes *)
      ∧ (τ2, Call Pop #()) ∈ ts (* τ2 was called *)
      ∧ ∃ v, (τ1,Call Push v) ∈ ts (* τ1 was called *)
            (* τ2 returns the same value or τ2 has not returned yet *)
           ∧ ((τ2,Ret (encode_response (NonEmpty v))) ∈ ts
              ∨ τ2 ∉ (filter (is_ret ∘ snd) ts).*1)) m.

  (* A trace is *complete* is every Call is paired with a Ret (this is
    required by Henzinger et al. (2013)). A trace is *closed* if every
    Push/Enqueue is matched with a Pop/Dequeue (this is required by
    Dodds et al. (2015)). Here we use “pair” for the relation between
    Call and Ret, and “match” for the relation between Push and Pop. *)
  Definition closed_match (m : list (positive*positive)) : Prop :=
    (* every push is matched (one direction of ⊆ is enough becase
      valid_match has handled to reversed direction) *)
    push_of_trace ts ⊆ m.*1
  ∧ Forall (λ τ, τ ∈ m.*2 (* each pop is either matched *)
              ∨ (τ,Ret (encode_response IsEmpty)) ∈ ts (* or returns ∅ *)
              ∨ τ ∉ (filter (is_ret ∘ snd) ts).*1) (pop_of_trace ts). (* or unfinshed *)

  (* Whether a pop returns empty; m must be a closed match *)
  Definition empty_of_trace_match (m : list (positive*positive)) : positive → Prop :=
    λ τ, τ ∈ pop_of_trace ts ∧ τ ∉ m.*2.

  Global Instance empty_of_trace_match_decision m τ : Decision (empty_of_trace_match m τ).
  Proof. rewrite /empty_of_trace_match. apply _. Defined.
End relations.

(* Facts about valid match. *)
Lemma valid_match_call_push ts m τ1 τ2 :
  valid_match ts m → (τ1,τ2) ∈ m →
  ∃ v, (τ1,Call Push v) ∈ ts.
Proof.
  intros (_ & _ & Hper_tag_valid) Hin.
  rewrite Forall_forall in Hper_tag_valid.
  destruct (Hper_tag_valid _ Hin) as (_ & _ & ? & Hcall & _).
  eexists. done.
Qed.

Lemma valid_match_inj_call ts m τ1 τ1' τ2 :
  valid_match ts m → (τ1,τ2) ∈ m → (τ1',τ2) ∈ m →
  τ1 = τ1'.
Proof.
  intros (_ & [_ Hnodup] & _) Hin1 Hin2.
  apply list_elem_of_lookup_1 in Hin1 as [i Hi].
  apply list_elem_of_lookup_1 in Hin2 as [j Hj].
  assert (Hi' : m.*2 !! i = Some τ2).
  { by rewrite list_lookup_fmap Hi. }
  assert (Hj' : m.*2 !! j = Some τ2).
  { by rewrite list_lookup_fmap Hj. }
  assert (Heq : i = j) by (eapply NoDup_lookup; eassumption).
  subst j. rewrite Hj in Hi. injection Hi as ->. done.
Qed.

Lemma valid_match_lookup_call_push ts m τ1 τ2 i n₀ v₀ :
  per_tag_wellformed ts →
  valid_match ts m → (τ1,τ2) ∈ m →
  ts !! i = Some (τ1,Call n₀ v₀) →
  n₀ = Push.
Proof.
  intros Hwf (_ & _ & Hper_tag_valid) Hin Hcall%list_elem_of_lookup_2.
  rewrite Forall_forall in Hper_tag_valid.
  destruct (Hper_tag_valid _ Hin) as (_ & _ & ? & Hcall' & _).
  opose proof (per_tag_partial_wellformed_inj_call _ _ _ _ _ _ _ Hcall Hcall') as [-> ->].
  { by apply per_tag_wellformed_per_tag_partial_wellformed. }
  reflexivity.
Qed.

Lemma valid_match_call_pop ts m τ1 τ2 :
  valid_match ts m → (τ1,τ2) ∈ m →
  (τ2,Call Pop #()) ∈ ts.
Proof.
  intros (_ & _ & Hper_tag_valid) Hin.
  rewrite Forall_forall in Hper_tag_valid.
  destruct (Hper_tag_valid _ Hin) as (_ & Hcall & _).
  assumption.
Qed.

Lemma valid_match_inj_ret ts m τ1 τ2 τ2' :
  valid_match ts m → (τ1,τ2) ∈ m → (τ1,τ2') ∈ m →
  τ2 = τ2'.
Proof.
  intros (_ & [Hnodup _] & _) Hin1 Hin2.
  apply list_elem_of_lookup_1 in Hin1 as [i Hi].
  apply list_elem_of_lookup_1 in Hin2 as [j Hj].
  assert (Hi' : m.*1 !! i = Some τ1).
  { by rewrite list_lookup_fmap Hi. }
  assert (Hj' : m.*1 !! j = Some τ1).
  { by rewrite list_lookup_fmap Hj. }
  assert (Heq : i = j) by (eapply NoDup_lookup; eassumption).
  subst j. rewrite Hj in Hi. injection Hi as ->. done.
Qed.

Lemma valid_match_lookup_call_pop ts m τ1 τ2 i n₀ v₀ :
  per_tag_wellformed ts →
  valid_match ts m → (τ1,τ2) ∈ m →
  ts !! i = Some (τ2,Call n₀ v₀) →
  n₀ = Pop ∧ v₀ = #().
Proof.
  intros Hwf (_ & _ & Hper_tag_valid) Hin Hcall%list_elem_of_lookup_2.
  rewrite Forall_forall in Hper_tag_valid.
  destruct (Hper_tag_valid _ Hin) as (_ & Hcall' & _).
  opose proof (per_tag_partial_wellformed_inj_call _ _ _ _ _ _ _ Hcall Hcall') as [-> ->].
  { by apply per_tag_wellformed_per_tag_partial_wellformed. }
  done.
Qed.

Lemma valid_match_ne ts m τ1 τ2 :
  per_tag_wellformed ts →
  valid_match ts m →
  (τ1,τ2) ∈ m → τ1 ≠ τ2.
Proof.
  intros Hwf Hvalid Hin <-.
  destruct (valid_match_call_push ts m τ1 τ1 Hvalid Hin) as [vpush Hpush].
  pose proof (valid_match_call_pop ts m τ1 τ1 Hvalid Hin) as Hpop.
  apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hpush; last done.
  apply (list_elem_of_filter_2 (λ x, x.1 = τ1)) in Hpop; last done.
  destruct (Hwf τ1) as (n & v & v' & Hprefix).
  eapply elem_of_prefix in Hpush; last exact Hprefix.
  eapply elem_of_prefix in Hpop; last exact Hprefix.
  rewrite !elem_of_cons !elem_of_nil !right_id in Hpush,Hpop.
  destruct Hpush, Hpop; simplify_eq.
Qed.

Lemma valid_match_nil : valid_match [] [].
Proof.
  split_and!.
  - set_solver.
  - apply NoDup_nil_2.
  - apply NoDup_nil_2.
  - by apply Forall_nil.
Qed.

Lemma valid_match_snoc_call_push ts m τ v :
  valid_match ts m → τ ∉ ts.*1 →
  valid_match (ts ++ [(τ, Call Push v)]) m.
Proof.
  intros Hvalid_match Hfresh.
  destruct Hvalid_match as (Hpop_subset & Hnodup & Hvalid_match).
  split; last split; [|assumption|].
  - rewrite /pop_val_of_trace filter_app filter_cons_False; last compute_done.
    rewrite filter_nil right_id_L.
    assumption.
  - apply (Forall_impl _ _ _ Hvalid_match).
    intros [τ1 τ2] (Hnot_pre & Hcall_pop & v' & Hcall_push & Hret_pop).
    split_and!; last (exists v'; split); [|set_solver..|].
    + intros Hpre. contradict Hnot_pre.
      rewrite /pre_of_trace in Hpre |- *.
      destruct (ret_of_tag (ts ++ _)) as [(i,x)|] eqn:Hrot; last done.
      assert (ret_of_tag ts τ2 = Some (i,x)) as ->.
      { rewrite /ret_of_tag in Hrot |- *.
        rewrite list_find_app_Some in Hrot.
        destruct Hrot as [|(_ & _ & HFalse)]; first done.
        exfalso.
        simpl in HFalse.
        rewrite decide_False in HFalse; first done.
        intros [??]. done. }
      simpl in Hpre |-*.
      destruct (call_of_tag (ts++_)) as [(j,y)|] eqn:Hcot; last done.
      assert (call_of_tag ts τ1 = Some (j,y)) as ->.
      { rewrite /call_of_tag in Hcot |- *.
        rewrite list_find_app_Some in Hcot.
        destruct Hcot as [|(_ & _ & HFalse)]; first done.
        exfalso.
        simpl in HFalse.
        rewrite decide_False in HFalse; first done.
        intros [<- _].
        apply (list_elem_of_fmap_2 fst) in Hcall_push.
        done. }
      done.
    + destruct Hret_pop.
      * left. set_solver.
      * right.
        rewrite filter_app filter_cons_False; last compute_done.
        rewrite filter_nil right_id_L.
        assumption.
Qed.

Lemma valid_match_snoc_call_pop ts m τ :
  valid_match ts m → τ ∉ ts.*1 →
  valid_match (ts ++ [(τ, Call Pop #())]) m.
Proof.
  intros Hvalid_match Hfresh.
  destruct Hvalid_match as (Hpop_subset & Hnodup & Hvalid_match).
  split; last split; [|assumption|].
  - rewrite /pop_val_of_trace filter_app filter_cons_False; last compute_done.
    rewrite filter_nil right_id_L.
    assumption.
  - apply (Forall_impl _ _ _ Hvalid_match).
    intros [τ1 τ2] (Hnot_pre & Hcall_pop & v' & Hcall_push & Hret_pop).
    split_and!; last (exists v'; split); [|set_solver..|].
    + intros Hpre. contradict Hnot_pre.
      rewrite /pre_of_trace in Hpre |- *.
      destruct (ret_of_tag (ts ++ _)) as [(i,x)|] eqn:Hrot; last done.
      assert (ret_of_tag ts τ2 = Some (i,x)) as ->.
      { rewrite /ret_of_tag in Hrot |- *.
        rewrite list_find_app_Some in Hrot.
        destruct Hrot as [|(_ & _ & HFalse)]; first done.
        exfalso.
        simpl in HFalse.
        rewrite decide_False in HFalse; first done.
        intros [??]. done. }
      simpl in Hpre |-*.
      destruct (call_of_tag (ts++_)) as [(j,y)|] eqn:Hcot; last done.
      assert (call_of_tag ts τ1 = Some (j,y)) as ->.
      { rewrite /call_of_tag in Hcot |- *.
        rewrite list_find_app_Some in Hcot.
        destruct Hcot as [|(_ & _ & HFalse)]; first done.
        exfalso.
        simpl in HFalse.
        rewrite decide_False in HFalse; first done.
        intros [<- _].
        apply (list_elem_of_fmap_2 fst) in Hcall_push.
        done. }
      done.
    + destruct Hret_pop.
      * left. set_solver.
      * right.
        rewrite filter_app filter_cons_False; last compute_done.
        rewrite filter_nil right_id_L.
        assumption.
Qed.

Lemma valid_match_snoc_ret_push ts m τ v :
  valid_match ts m → filter (λ x, x.1 = τ) ts = [(τ,Call Push v)] →
  valid_match (ts ++ [(τ, Ret #())]) m.
Proof.
  intros Hvalid_match Hfilter.
  destruct Hvalid_match as (Hpop_subset & Hnodup & Hvalid_match).
  split; last split; [|assumption|].
  - rewrite /pop_val_of_trace filter_app filter_cons_False; last compute_done.
    rewrite filter_nil right_id_L.
    assumption.
  - apply (Forall_impl _ _ _ Hvalid_match).
    intros [τ1 τ2] (Hnot_pre & Hcall_pop & v' & Hcall_push & Hret_pop).
    split_and!; last (exists v'; split); [|set_solver..|].
    + intros Hpre. contradict Hnot_pre.
      rewrite /pre_of_trace in Hpre |- *.
      destruct (ret_of_tag (ts ++ _)) as [(i,x)|] eqn:Hrot; last done.
      assert (ret_of_tag ts τ2 = Some (i,x)) as ->.
      { rewrite /ret_of_tag in Hrot |- *.
        rewrite list_find_app_Some in Hrot.
        destruct Hrot as [|(Hi_ge_len & Hnot_found & Hfound)]; first done.
        exfalso.
        rewrite /= in Hfound.
        case_decide as Hτ_τ2; last done.
        destruct Hτ_τ2 as [<- _].
        injection Hfound as Hi_le_len <-.
        assert (i = length ts) as -> by lia.
        destruct (call_of_tag (ts ++ _)) as [(j,y)|] eqn:Hcot; last done.
        simpl in Hpre.
        rewrite list_find_app_Some in Hcot.
        destruct Hcot as [[Hlookup _]%list_find_Some|(_ & _ & Hfound)].
        { apply lookup_lt_Some in Hlookup. lia. }
        simpl in Hfound.
        rewrite decide_False in Hfound; first done.
        intros [_ ?]. done. }
      simpl in Hpre |-*.
      destruct (call_of_tag (ts++_)) as [(j,y)|] eqn:Hcot; last done.
      simpl in Hpre.
      assert (call_of_tag ts τ1 = Some (j,y)) as ->.
      { rewrite /call_of_tag in Hcot |- *.
        rewrite list_find_app_Some in Hcot.
        destruct Hcot as [|(_ & _ & HFalse)]; first done.
        exfalso.
        simpl in HFalse.
        rewrite decide_False in HFalse; first done.
        intros [_ ?]. done. }
      done.
    + destruct Hret_pop.
      * left. set_solver.
      * right.
        rewrite filter_app filter_cons_True; last compute_done.
        rewrite filter_nil fmap_app fmap_cons fmap_nil /=.
        apply not_elem_of_app. split; first assumption.
        intros ->%list_elem_of_singleton.
        apply (list_elem_of_filter_2 (λ x, x.1 = τ)) in Hcall_pop; last done.
        destruct (list_elem_of_split _ _ Hcall_pop) as (l1 & l2 & Heq).
        rewrite Heq in Hfilter. clear -Hfilter.
        assert (l1 = [] ∧ l2 = []) as [-> ->].
        { rewrite -!length_zero_iff_nil.
          apply (f_equal length) in Hfilter.
          rewrite length_app !length_cons length_nil in Hfilter.
          lia. }
        discriminate.
Qed.

Lemma valid_match_snoc_ret_pop_empty ts m τ :
  valid_match ts m → τ ∉ m.*2 →
  filter (λ x, x.1 = τ) ts = [(τ,Call Pop #())] →
  valid_match (ts ++ [(τ, Ret (encode_response IsEmpty))]) m.
Proof.
  intros Hvalid_match Hunmatched Hfilter.
  destruct Hvalid_match as (Hpop_subset & Hnodup & Hvalid_match).
  split; last split; [|assumption|].
  - rewrite /pop_val_of_trace filter_app filter_cons_False; last compute_done.
    rewrite filter_nil right_id_L.
    assumption.
  - rewrite 2!Forall_forall in Hvalid_match |-*.
    intros [τ1 τ2] Hin.
    destruct (Hvalid_match (τ1,τ2) Hin) as (Hnot_pre & Hcall_pop & v' & Hcall_push & Hret_pop).
    split_and!; last (exists v'; split); [|set_solver..|].
    + intros Hpre. contradict Hnot_pre.
      rewrite /pre_of_trace in Hpre |- *.
      destruct (ret_of_tag (ts ++ _)) as [(i,x)|] eqn:Hrot; last done.
      assert (ret_of_tag ts τ2 = Some (i,x)) as ->.
      { rewrite /ret_of_tag in Hrot |- *.
        rewrite list_find_app_Some in Hrot.
        destruct Hrot as [|(Hi_ge_len & Hnot_found & Hfound)]; first done.
        exfalso.
        rewrite /= in Hfound.
        case_decide as Hτ_τ2; last done.
        destruct Hτ_τ2 as [<- _].
        injection Hfound as Hi_le_len <-.
        assert (i = length ts) as -> by lia.
        destruct (call_of_tag (ts ++ _)) as [(j,y)|] eqn:Hcot; last done.
        simpl in Hpre.
        rewrite list_find_app_Some in Hcot.
        destruct Hcot as [[Hlookup _]%list_find_Some|(_ & _ & Hfound)].
        { apply lookup_lt_Some in Hlookup. lia. }
        simpl in Hfound.
        rewrite decide_False in Hfound; first done.
        intros [_ ?]. done. }
      simpl in Hpre |-*.
      destruct (call_of_tag (ts++_)) as [(j,y)|] eqn:Hcot; last done.
      simpl in Hpre.
      assert (call_of_tag ts τ1 = Some (j,y)) as ->.
      { rewrite /call_of_tag in Hcot |- *.
        rewrite list_find_app_Some in Hcot.
        destruct Hcot as [|(_ & _ & HFalse)]; first done.
        exfalso.
        simpl in HFalse.
        rewrite decide_False in HFalse; first done.
        intros [_ ?]. done. }
      done.
    + destruct Hret_pop.
      * left. set_solver.
      * right.
        rewrite filter_app filter_cons_True; last compute_done.
        rewrite filter_nil fmap_app fmap_cons fmap_nil /=.
        apply not_elem_of_app. split; first assumption.
        intros ->%list_elem_of_singleton.
        apply (list_elem_of_fmap_2 snd) in Hin.
        apply Hunmatched. assumption.
Qed.

Lemma valid_match_snoc_ret_pop_val rme valid_value ts m τ1 τ2 v :
  per_tag_wellformed_bag rme valid_value ts →
  valid_match ts m →
  (τ1, τ2) ∈ m →
  (τ1, Call Push v) ∈ ts →
  filter (λ x, x.1 = τ2) ts = [(τ2, Call Pop #())] →
  valid_match (ts ++ [(τ2, Ret (encode_response (NonEmpty v)))]) m.
Proof.
  intros Hwf Hvalid_match Hmatched Hcall Hfilter.
  pose proof (Hvalid_match' := Hvalid_match).
  destruct Hvalid_match as (Hpop_subset & Hnodup & Hvalid_match).
  split; last split; [|assumption|].
  - rewrite /pop_val_of_trace filter_app filter_cons_True; last compute_done.
    rewrite filter_nil fmap_app fmap_cons fmap_nil /=.
    apply (list_elem_of_fmap_2 snd) in Hmatched.
    set_solver.
  - rewrite 2!Forall_forall in Hvalid_match |-*.
    intros [τ1' τ2'] Hin.
    destruct (Hvalid_match (τ1',τ2') Hin) as (Hnot_pre & Hcall_pop & v' & Hcall_push & Hret_pop).
    split_and!; last (exists v'; split); [|set_solver..|].
    + intros Hpre. contradict Hnot_pre.
      rewrite /pre_of_trace in Hpre |- *.
      destruct (ret_of_tag (ts ++ _)) as [(i,x)|] eqn:Hrot; last done.
      assert (ret_of_tag ts τ2' = Some (i,x)) as ->.
      { rewrite /ret_of_tag in Hrot |- *.
        rewrite list_find_app_Some in Hrot.
        destruct Hrot as [|(Hi_ge_len & Hnot_found & Hfound)]; first done.
        exfalso.
        rewrite /= in Hfound.
        case_decide as Hτ_τ2; last done.
        destruct Hτ_τ2 as [<- _].
        injection Hfound as Hi_le_len <-.
        assert (i = length ts) as -> by lia.
        destruct (call_of_tag (ts ++ _)) as [(j,y)|] eqn:Hcot; last done.
        simpl in Hpre.
        rewrite list_find_app_Some in Hcot.
        destruct Hcot as [[Hlookup _]%list_find_Some|(_ & _ & Hfound)].
        { apply lookup_lt_Some in Hlookup. lia. }
        simpl in Hfound.
        rewrite decide_False in Hfound; first done.
        intros [_ ?]. done. }
      simpl in Hpre |-*.
      destruct (call_of_tag (ts++_)) as [(j,y)|] eqn:Hcot; last done.
      simpl in Hpre.
      assert (call_of_tag ts τ1' = Some (j,y)) as ->.
      { rewrite /call_of_tag in Hcot |- *.
        rewrite list_find_app_Some in Hcot.
        destruct Hcot as [|(_ & _ & HFalse)]; first done.
        exfalso.
        simpl in HFalse.
        rewrite decide_False in HFalse; first done.
        intros [_ ?]. done. }
      done.
    + destruct Hret_pop.
      * left. set_solver.
      * destruct (decide (τ2 = τ2')) as [<- | Hne].
        --left.
          pose proof (valid_match_inj_call ts m _ _ _ Hvalid_match' Hmatched Hin) as <-.
          opose proof (per_tag_partial_wellformed_inj_call ts τ1 _ _ _ _ _ Hcall Hcall_push) as [Hnn' Hvv'].
          { by eapply per_tag_wellformed_per_tag_partial_wellformed, per_tag_wellformed_bag_wellformed. }
          simplify_eq.
          clear. set_solver.
        --right.
          rewrite filter_app filter_cons_True; last compute_done.
          rewrite filter_nil fmap_app fmap_cons fmap_nil /=.
          apply not_elem_of_app. split; first assumption.
          intros ->%list_elem_of_singleton.
          contradiction.
Qed.

Lemma valid_match_snoc_match ts m τ1 τ2 v :
  valid_match ts m →
  τ1 ∉ m.*1 → τ2 ∉ m.*2 →
  (τ1, Call Push v) ∈ ts →
  (τ2, Call Pop #()) ∈ ts →
  τ2 ∉ (filter (is_ret ∘ snd) ts).*1 →
  valid_match ts (m ++ [(τ1,τ2)]).
Proof.
  intros Hvalid_match Hfresh1 Hfresh2 Hcall_push Hcall_pop Hnot_ret.
  destruct Hvalid_match as (Hpop_subset & [Hnodup1 Hnodup2] & Hvalid_match).
  split_and!.
  - rewrite fmap_snoc /=. set_solver.
  - rewrite fmap_snoc /=. apply NoDup_app.
    split_and!; [done| |apply NoDup_singleton].
    intros ? ? ->%list_elem_of_singleton.
    contradiction.
  - rewrite fmap_snoc /=. apply NoDup_app.
    split_and!; [done| |apply NoDup_singleton].
    intros ? ? ->%list_elem_of_singleton.
    contradiction.
  - apply Forall_app. split; first done.
    apply Forall_singleton.
    split_and!; last (exists v; split); [|set_solver..].
    rewrite /pre_of_trace => HFalse.
    destruct (ret_of_tag ts τ2) as [(i,(τ,t))|] eqn:Hrot; last done.
    rewrite /ret_of_tag list_find_Some in Hrot.
    destruct Hrot as (Hret%list_elem_of_lookup_2 & [Heq His_ret] & _).
    simpl in Heq, His_ret. subst τ.
    apply (list_elem_of_filter_2 (is_ret∘snd)) in Hret; last done.
    apply (list_elem_of_fmap_2 fst) in Hret.
    contradiction.
Qed.

Lemma per_tag_pop_empty_sound_nil : per_tag_pop_empty_sound [] [].
Proof. intros ?. rewrite filter_nil. set_solver. Qed.

(**********************************************************)
(* Begin LLM-generated code. *)
(* claude-opus-4-7[1m], max effort Claude Code 2.1.111 *)

(*** Local helper lemmas. ***)

(* Backward direction of push_pop_covers under app: when τ_b has a Call event
   in ts0 (so call_of_tag is preserved) and i < length ts0 (so a "ret-in-rest"
   index is too large), push_pop_covers (ts0 ++ rest) implies push_pop_covers ts0. *)
Local Lemma push_pop_covers_app_inv (ts0 : list (positive * trace)) rest τ_a τ_b i :
  (∃ n v, (τ_b, Call n v) ∈ ts0) →
  i < length ts0 →
  push_pop_covers (ts0 ++ rest) τ_a τ_b i →
  push_pop_covers ts0 τ_a τ_b i.
Proof.
  intros (n_b & v_b & Hcall_b) Hi_lt Hcov_ext.
  rewrite /push_pop_covers in Hcov_ext |- *.
  destruct (ret_of_tag (ts0 ++ rest) τ_a) as [[ir tr]|] eqn:Hret_ext;
    simpl in Hcov_ext; [|done].
  destruct (call_of_tag (ts0 ++ rest) τ_b) as [[ic tc]|] eqn:Hcall_ext;
    simpl in Hcov_ext; [|done].
  destruct Hcov_ext as [Hir_lt Hi_lt_ic].
  rewrite /call_of_tag list_find_app_Some in Hcall_ext.
  destruct Hcall_ext as [Hcall_ts | (_ & Hcall_none & _)]; last first.
  - exfalso. apply list_find_None in Hcall_none. rewrite Forall_forall in Hcall_none.
    specialize (Hcall_none _ Hcall_b). simpl in Hcall_none. apply Hcall_none. done.
  - rewrite /ret_of_tag list_find_app_Some in Hret_ext.
    destruct Hret_ext as [Hret_ts | (Hge_ir & _ & _)]; last lia.
    rewrite /ret_of_tag /call_of_tag Hret_ts Hcall_ts /=. split; assumption.
Qed.

(* Backward direction of dangling_push_covers under app: when i < length ts0
   (so a "ret-in-rest" index is too large), dangling_push_covers (ts0 ++ rest)
   implies dangling_push_covers ts0. *)
Local Lemma dangling_push_covers_app_inv (ts0 : list (positive * trace)) rest τ_a i :
  i < length ts0 →
  dangling_push_covers (ts0 ++ rest) τ_a i →
  dangling_push_covers ts0 τ_a i.
Proof.
  intros Hi_lt Hcov_ext.
  rewrite /dangling_push_covers in Hcov_ext |- *.
  destruct (ret_of_tag (ts0 ++ rest) τ_a) as [[ir tr]|] eqn:Hret_ext;
    simpl in Hcov_ext; [|done].
  rewrite /ret_of_tag list_find_app_Some in Hret_ext.
  destruct Hret_ext as [Hret_ts | (Hge_ir & _ & _)]; last lia.
  rewrite /ret_of_tag Hret_ts /=. exact Hcov_ext.
Qed.

(*** Main lemmas. ***)

Lemma per_tag_pop_empty_sound_snoc_call_push ts m τ v :
  valid_match ts m →
  per_tag_pop_empty_sound ts m → τ ∉ ts.*1 →
  per_tag_pop_empty_sound (ts ++ [(τ, Call Push v)]) m.
Proof.
  intros Hvm Hps Hfresh τ' Hτ'_in.
  rewrite filter_app filter_cons_False in Hτ'_in; last compute_done.
  rewrite filter_nil right_id_L in Hτ'_in.
  destruct (Hps τ' Hτ'_in)
    as (icall & iret & i & Hcall_lkp & Hret_lkp & Hi_le & Hno_match & Hno_dangling).
  pose proof (lookup_lt_Some _ _ _ Hret_lkp) as Hiret_lt.
  assert (Hi_lt : i < length ts) by lia.
  exists icall, iret, i.
  split; [|split; [|split; [|split]]].
  - by apply lookup_app_l_Some.
  - by apply lookup_app_l_Some.
  - exact Hi_le.
  - intros τ_a τ_b Hin Hcov_ext.
    pose proof (valid_match_call_pop _ _ _ _ Hvm Hin) as Hcall_τ_b.
    apply (Hno_match τ_a τ_b Hin).
    eapply push_pop_covers_app_inv;
      [do 2 eexists; exact Hcall_τ_b | exact Hi_lt | exact Hcov_ext].
  - intros τ_a [Hτ_a_push Hτ_a_nm] Hcov_ext.
    rewrite /push_of_trace filter_app fmap_app in Hτ_a_push.
    rewrite filter_cons_True /= in Hτ_a_push; last by exists v.
    apply elem_of_app in Hτ_a_push as [Hτ_a_push_ts | Hτ_a_eq].
    + apply (Hno_dangling τ_a (conj Hτ_a_push_ts Hτ_a_nm)).
      eapply dangling_push_covers_app_inv; [exact Hi_lt | exact Hcov_ext].
    + apply list_elem_of_singleton in Hτ_a_eq. subst τ_a.
      exfalso. rewrite /dangling_push_covers in Hcov_ext.
      destruct (ret_of_tag (ts ++ _) τ) as [[ir tr]|] eqn:Hret_ext;
        simpl in Hcov_ext; [|done].
      rewrite /ret_of_tag list_find_app_Some in Hret_ext.
      destruct Hret_ext as [Hret_ts | (Hge_ir & _ & _)]; last lia.
      apply Hfresh.
      apply list_find_Some in Hret_ts as (Hlookup & [Htag _] & _).
      rewrite -Htag. apply (list_elem_of_fmap_2 fst _ tr).
      by apply list_elem_of_lookup_2 in Hlookup.
Qed.

Lemma per_tag_pop_empty_sound_snoc_call_pop ts m τ :
  valid_match ts m →
  per_tag_pop_empty_sound ts m → τ ∉ ts.*1 →
  per_tag_pop_empty_sound (ts ++ [(τ, Call Pop #())]) m.
Proof.
  intros Hvm Hps Hfresh τ' Hτ'_in.
  rewrite filter_app filter_cons_False in Hτ'_in; last compute_done.
  rewrite filter_nil right_id_L in Hτ'_in.
  destruct (Hps τ' Hτ'_in)
    as (icall & iret & i & Hcall_lkp & Hret_lkp & Hi_le & Hno_match & Hno_dangling).
  pose proof (lookup_lt_Some _ _ _ Hret_lkp) as Hiret_lt.
  assert (Hi_lt : i < length ts) by lia.
  exists icall, iret, i.
  split; [|split; [|split; [|split]]].
  - by apply lookup_app_l_Some.
  - by apply lookup_app_l_Some.
  - exact Hi_le.
  - intros τ_a τ_b Hin Hcov_ext.
    pose proof (valid_match_call_pop _ _ _ _ Hvm Hin) as Hcall_τ_b.
    apply (Hno_match τ_a τ_b Hin).
    eapply push_pop_covers_app_inv;
      [do 2 eexists; exact Hcall_τ_b | exact Hi_lt | exact Hcov_ext].
  - intros τ_a [Hτ_a_push Hτ_a_nm] Hcov_ext.
    rewrite /push_of_trace filter_app fmap_app in Hτ_a_push.
    rewrite filter_cons_False in Hτ_a_push; last compute_done.
    rewrite filter_nil right_id_L in Hτ_a_push.
    apply (Hno_dangling τ_a (conj Hτ_a_push Hτ_a_nm)).
    eapply dangling_push_covers_app_inv; [exact Hi_lt | exact Hcov_ext].
Qed.

Lemma per_tag_pop_empty_sound_snoc_ret_push ts m τ v :
  valid_match ts m →
  per_tag_pop_empty_sound ts m → filter (λ x, x.1 = τ) ts = [(τ,Call Push v)] →
  per_tag_pop_empty_sound (ts ++ [(τ, Ret #())]) m.
Proof.
  intros Hvm Hps Hfilter τ' Hτ'_in.
  rewrite filter_app filter_cons_False in Hτ'_in; last compute_done.
  rewrite filter_nil right_id_L in Hτ'_in.
  destruct (Hps τ' Hτ'_in)
    as (icall & iret & i & Hcall_lkp & Hret_lkp & Hi_le & Hno_match & Hno_dangling).
  pose proof (lookup_lt_Some _ _ _ Hret_lkp) as Hiret_lt.
  assert (Hi_lt : i < length ts) by lia.
  exists icall, iret, i.
  split; [|split; [|split; [|split]]].
  - by apply lookup_app_l_Some.
  - by apply lookup_app_l_Some.
  - exact Hi_le.
  - intros τ_a τ_b Hin Hcov_ext.
    pose proof (valid_match_call_pop _ _ _ _ Hvm Hin) as Hcall_τ_b.
    apply (Hno_match τ_a τ_b Hin).
    eapply push_pop_covers_app_inv;
      [do 2 eexists; exact Hcall_τ_b | exact Hi_lt | exact Hcov_ext].
  - intros τ_a [Hτ_a_push Hτ_a_nm] Hcov_ext.
    rewrite /push_of_trace filter_app fmap_app in Hτ_a_push.
    rewrite filter_cons_False in Hτ_a_push; last compute_done.
    rewrite filter_nil right_id_L in Hτ_a_push.
    apply (Hno_dangling τ_a (conj Hτ_a_push Hτ_a_nm)).
    eapply dangling_push_covers_app_inv; [exact Hi_lt | exact Hcov_ext].
Qed.

Lemma per_tag_pop_empty_sound_snoc_ret_pop_val ts m τ v :
  valid_match ts m →
  per_tag_pop_empty_sound ts m → filter (λ x, x.1 = τ) ts = [(τ,Call Pop #())] →
  per_tag_pop_empty_sound (ts ++ [(τ, Ret (encode_response (NonEmpty v)))]) m.
Proof.
  intros Hvm Hps Hfilter τ' Hτ'_in.
  rewrite filter_app filter_cons_False in Hτ'_in; last compute_done.
  rewrite filter_nil right_id_L in Hτ'_in.
  destruct (Hps τ' Hτ'_in)
    as (icall & iret & i & Hcall_lkp & Hret_lkp & Hi_le & Hno_match & Hno_dangling).
  pose proof (lookup_lt_Some _ _ _ Hret_lkp) as Hiret_lt.
  assert (Hi_lt : i < length ts) by lia.
  exists icall, iret, i.
  split; [|split; [|split; [|split]]].
  - by apply lookup_app_l_Some.
  - by apply lookup_app_l_Some.
  - exact Hi_le.
  - intros τ_a τ_b Hin Hcov_ext.
    pose proof (valid_match_call_pop _ _ _ _ Hvm Hin) as Hcall_τ_b.
    apply (Hno_match τ_a τ_b Hin).
    eapply push_pop_covers_app_inv;
      [do 2 eexists; exact Hcall_τ_b | exact Hi_lt | exact Hcov_ext].
  - intros τ_a [Hτ_a_push Hτ_a_nm] Hcov_ext.
    rewrite /push_of_trace filter_app fmap_app in Hτ_a_push.
    rewrite filter_cons_False in Hτ_a_push; last compute_done.
    rewrite filter_nil right_id_L in Hτ_a_push.
    apply (Hno_dangling τ_a (conj Hτ_a_push Hτ_a_nm)).
    eapply dangling_push_covers_app_inv; [exact Hi_lt | exact Hcov_ext].
Qed.

(* Appending a Ret of a pop does not change the Call positions, nor the Ret
   positions of other tags. *)
Local Lemma ret_of_tag_snoc_ne ts τ τ' e :
  τ' ≠ τ → ret_of_tag (ts ++ [(τ, e)]) τ' = ret_of_tag ts τ'.
Proof.
  intros Hne. rewrite /ret_of_tag.
  destruct (list_find _ ts) as [[j x]|] eqn:Hf.
  - by apply list_find_app_l.
  - rewrite list_find_app_r //=. case_decide as Hc; last done.
    destruct Hc as [Hc _]. simpl in Hc. congruence.
Qed.

Local Lemma call_of_tag_snoc_ret ts τ τ' r :
  call_of_tag (ts ++ [(τ, Ret r)]) τ' = call_of_tag ts τ'.
Proof.
  rewrite /call_of_tag.
  destruct (list_find _ ts) as [[j x]|] eqn:Hf.
  - by apply list_find_app_l.
  - rewrite list_find_app_r //=. case_decide as Hc; last done.
    by destruct Hc as [_ Hc].
Qed.

(* A pop may return EMPTY if, at some index i between its Call and now, no
   matched push/pop pair covers i and no unmatched push dangles over i. *)
Lemma per_tag_pop_empty_sound_snoc_ret_pop_empty ts m τ icall i :
  valid_match ts m →
  per_tag_pop_empty_sound ts m →
  filter (λ x, x.1 = τ) ts = [(τ, Call Pop #())] →
  ts !! icall = Some (τ, Call Pop #()) →
  icall ≤ i ≤ length ts →
  (∀ τ1 τ2, (τ1, τ2) ∈ m → ¬ push_pop_covers ts τ1 τ2 i) →
  (∀ τ1, τ1 ∈ push_of_trace ts ∧ τ1 ∉ m.*1 → ¬ dangling_push_covers ts τ1 i) →
  per_tag_pop_empty_sound (ts ++ [(τ, Ret (encode_response IsEmpty))]) m.
Proof.
  intros Hvm Hps Hfilter Hicall Hi Hno_match Hno_dangling τ' Hτ'_in.
  set (e := (τ, Ret (encode_response IsEmpty))).
  assert (Hpush_ne : ∀ τ1, τ1 ∈ push_of_trace ts → τ1 ≠ τ).
  { intros τ1 Hpush ->. apply push_tag_in_trace in Hpush as [v Hv].
    assert (Hin : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts)
      by (apply list_elem_of_filter; done).
    rewrite Hfilter list_elem_of_singleton in Hin. discriminate. }
  assert (Hpush_eq : push_of_trace (ts ++ [e]) = push_of_trace ts).
  { rewrite /push_of_trace filter_app filter_cons_False; last compute_done.
    by rewrite filter_nil right_id_L. }
  assert (Hcov_eq : ∀ τa τb j, τa ≠ τ →
    push_pop_covers (ts ++ [e]) τa τb j ↔ push_pop_covers ts τa τb j).
  { intros τa τb j Hne.
    by rewrite /push_pop_covers ret_of_tag_snoc_ne // call_of_tag_snoc_ret. }
  assert (Hdang_eq : ∀ τa j, τa ≠ τ →
    dangling_push_covers (ts ++ [e]) τa j ↔ dangling_push_covers ts τa j).
  { intros τa j Hne. by rewrite /dangling_push_covers ret_of_tag_snoc_ne. }
  assert (Hm_ne : ∀ τa τb, (τa, τb) ∈ m → τa ≠ τ).
  { intros τa τb Hin. apply Hpush_ne.
    destruct (valid_match_call_push _ _ _ _ Hvm Hin) as [v Hv].
    apply (list_elem_of_fmap_2 fst _ (τa, Call Push v)).
    apply list_elem_of_filter_2; [by exists v | exact Hv]. }
  rewrite filter_app filter_cons_True in Hτ'_in; last done.
  rewrite filter_nil fmap_app /= elem_of_app list_elem_of_singleton in Hτ'_in.
  destruct Hτ'_in as [Hold | ->].
  - destruct (Hps τ' Hold)
      as (icall' & iret' & i' & Hcall_lkp & Hret_lkp & Hi_le & Hno_match' & Hno_dangling').
    exists icall', iret', i'.
    split; [|split; [|split; [|split]]].
    + by apply lookup_app_l_Some.
    + by apply lookup_app_l_Some.
    + exact Hi_le.
    + intros τa τb Hin Hcov. apply (Hno_match' τa τb Hin).
      by apply (Hcov_eq τa τb i' (Hm_ne _ _ Hin)).
    + intros τa [Hpush Hnm] Hcov. rewrite Hpush_eq in Hpush.
      apply (Hno_dangling' τa (conj Hpush Hnm)).
      by apply (Hdang_eq τa i' (Hpush_ne _ Hpush)).
  - exists icall, (length ts), i.
    split; [|split; [|split; [|split]]].
    + by apply lookup_app_l_Some.
    + by rewrite lookup_app_r // Nat.sub_diag.
    + exact Hi.
    + intros τa τb Hin Hcov. apply (Hno_match τa τb Hin).
      by apply (Hcov_eq τa τb i (Hm_ne _ _ Hin)).
    + intros τa [Hpush Hnm] Hcov. rewrite Hpush_eq in Hpush.
      apply (Hno_dangling τa (conj Hpush Hnm)).
      by apply (Hdang_eq τa i (Hpush_ne _ Hpush)).
Qed.

(* This lemma additionally requires (τ1, Call Push v) ∈ ts (with new arg v).
   Without it, the lemma is provably false: a counterexample exists where
   τ1's Ret is way before τ2's Call, with some empty pop in between, so the
   new pair (τ1, τ2) push_pop_covers some i. The Call Push hypothesis is used
   together with τ1 ∉ m.*1 to invoke the original Hno_dangling for τ1, ruling
   out the new push_pop_cover. The hypothesis is available at the call site
   of [I_queue_pre_snoc_match] (passed as Hcall_push). *)
Lemma per_tag_pop_empty_sound_snoc_match ts m τ1 τ2 v :
  per_tag_pop_empty_sound ts m →
  τ1 ∉ m.*1 → τ2 ∉ m.*2 →
  (τ1, Call Push v) ∈ ts →
  per_tag_pop_empty_sound ts (m ++ [(τ1, τ2)]).
Proof.
  intros Hps Hτ1_nm Hτ2_nm Hcall_τ1 τ' Hτ'_in.
  destruct (Hps τ' Hτ'_in)
    as (icall & iret & i & Hcall_lkp & Hret_lkp & Hi_le & Hno_match & Hno_dangling).
  exists icall, iret, i.
  split; [|split; [|split; [|split]]].
  - exact Hcall_lkp.
  - exact Hret_lkp.
  - exact Hi_le.
  - intros τ_a τ_b Hin Hcov.
    apply elem_of_app in Hin as [Hin_old | Hin_new].
    + exact (Hno_match τ_a τ_b Hin_old Hcov).
    + apply list_elem_of_singleton in Hin_new. injection Hin_new as -> ->.
      apply (Hno_dangling τ1).
      * split.
        -- apply (list_elem_of_fmap_2 fst _ (τ1, Call Push v)).
           apply list_elem_of_filter_2; [by exists v | exact Hcall_τ1].
        -- exact Hτ1_nm.
      * rewrite /push_pop_covers in Hcov.
        rewrite /dangling_push_covers.
        destruct (ret_of_tag ts τ1) as [[ir tr]|] eqn:Hret;
          simpl in Hcov |- *; [|done].
        destruct (call_of_tag ts τ2) as [[ic tc]|] eqn:Hcall;
          simpl in Hcov; [|done].
        destruct Hcov as [Hir_lt _]. exact Hir_lt.
  - intros τ_a [Hτ_a_push Hτ_a_nm_new] Hcov.
    assert (Hτ_a_nm : τ_a ∉ m.*1).
    { intros Habs. apply Hτ_a_nm_new.
      rewrite fmap_app /=. apply elem_of_app. left. exact Habs. }
    apply (Hno_dangling τ_a (conj Hτ_a_push Hτ_a_nm) Hcov).
Qed.

(* Reusable lemma discovered by LLM. *)
Lemma not_pre_of_trace_app ts ts' τ1 τ2 :
  (∃ n v, (τ2, Call n v) ∈ ts) →
  ¬ pre_of_trace ts τ1 τ2 →
  ¬ pre_of_trace (ts ++ ts') τ1 τ2.
Proof.
  intros (nc & vc & Hcall1) Hpre Hpre'.
  rewrite /pre_of_trace in Hpre', Hpre.
  destruct (ret_of_tag (ts ++ ts') τ1) as [[i_ret t_ret]|] eqn:Hret_ext;
    simpl in Hpre'; [|done].
  destruct (call_of_tag (ts ++ ts') τ2) as [[i_call t_call]|] eqn:Hcall_ext;
    simpl in Hpre'; [|done].
  rewrite /call_of_tag list_find_app_Some in Hcall_ext.
  destruct Hcall_ext as [Hcall_ts|[_ [Hcall_none _]]].
  - (* Call found in ts0 at position i_call *)
    rewrite /ret_of_tag list_find_app_Some in Hret_ext.
    destruct Hret_ext as [Hret_ts|[Hlen_ret [Hret_none _]]].
    + (* Ret found in ts0: pre_of_trace ts0 has same values *)
      apply Hpre.
      rewrite /ret_of_tag Hret_ts. simpl.
      rewrite /call_of_tag Hcall_ts. simpl. exact Hpre'.
    + (* Ret not in ts0, found in rest at position ≥ |ts0| *)
      (* i_ret ≥ |ts0|, but call is at position i_call in ts0, so i_call < |ts0| *)
      (* From list_find_Some, i_call < length ts0 *)
      apply list_find_Some in Hcall_ts as (Hlookup & _ & _).
      apply lookup_lt_Some in Hlookup.
      lia.
  - (* Call not found in ts0 — contradiction *)
    exfalso.
    apply list_find_None in Hcall_none.
    rewrite Forall_forall in Hcall_none.
    specialize (Hcall_none (τ2, Call nc vc) Hcall1).
    simpl in Hcall_none. apply Hcall_none. done.
Qed.

(* Reusable lemma discovered by LLM. *)
Lemma pre_of_trace_app_inv ts ts' τ1 τ2 :
  (∃ n v, (τ2, Call n v) ∈ ts) →
  pre_of_trace (ts ++ ts') τ1 τ2 →
  pre_of_trace ts τ1 τ2.
Proof.
  intros Hcall Hpre.
  destruct (decide (pre_of_trace ts τ1 τ2)) as [|Hno]; first done.
  exfalso. exact (not_pre_of_trace_app ts ts' τ1 τ2 Hcall Hno Hpre).
Qed.
(* End LLM-generated code. *)
(**********************************************************)
