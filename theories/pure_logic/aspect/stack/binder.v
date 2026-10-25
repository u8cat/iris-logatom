From stdpp Require Import finite.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.queue Require binder.
From iris_logatom.pure_logic.aspect.queue.ext Require conc_his_rel.
From iris_logatom.pure_logic.aspect.stack.ext Require Import conc_his_rel vis_rr.
From iris_logatom.pure_logic.aspect.bag Require Import base binder.
From iris_logatom.pure_logic.aspect.stack Require Import base vis.

(* The trace <-> history binding for stacks. The history instance and the set-part of
   the binding are shared with queues: the queue development already proves that a
   complete, closed trace is linearizable as a set (in the queue port's classes), and
   the bridge below transports this to the stack port's classes. *)

Module Q := iris_logatom.pure_logic.aspect.queue.ext.conc_his_rel.

Local Instance relation_union {A} : Union (relation A) :=
  λ r1 r2, Relation_Operators.union A r1 r2.

(* ===== Bridge between the queue port's and the stack port's history classes ===== *)
Section bridge.
  Context {A : Type} `{!EqDecision A} `{!Finite A}.

  Local Instance bridge_queue_model : Q.abstract_queue_model :=
    Q.AbstractQueueModel A _ _.
  Local Instance bridge_stack_model : abstract_stack_model :=
    AbstractStackModel A _ _.

  Lemma conc_history_queue_stack (pre : relation A) :
    Q.ConcHistory pre → ConcHistory pre.
  Proof. intros [Htrans Hanti Hirr Habcd _]. constructor; [done..|exact Habcd]. Qed.

  Lemma linearizable_set_queue_stack (pre val : relation A) (empty : A → Prop) :
    Q.linearizable_set pre val empty → linearizable_set pre val empty.
  Proof.
    intros [Hch (prt & Hsub & Hset)].
    split; first by apply conc_history_queue_stack.
    exists prt. split; first done.
    destruct Hset as [[[Hch' Hpush Hpop Hvo Hadq Hetnv Hvnp _ _] Htri] Hce].
    constructor; [constructor; [constructor|]|].
    - by apply conc_history_queue_stack.
    - exists (enum A). split; [apply NoDup_enum | intros x _; apply elem_of_enum].
    - exact Hpush.
    - exact Hpop.
    - exact Hvo.
    - exact Hadq.
    - exact Hetnv.
    - exact Hvnp.
    - exact Htri.
    - exact Hce.
  Qed.
End bridge.

(* ===== The stack history of a complete, closed trace ===== *)
Section stack_binder.
  Variables (rme : response_mayempty) (valid_value : val → Prop)
    (ts : list (positive * trace)) (m : list (positive * positive)).
  Hypothesis Hvalid : valid_match ts m.
  Hypothesis Hcomplete : per_tag_complete ts.
  Hypothesis Hclosed : closed_match ts m.

  Local Instance trace_stack_model : abstract_stack_model :=
    AbstractStackModel (trace_op ts) _ _.

  Definition trace_pre : relation operation :=
    λ op1 op2, pre_of_trace ts (`op1) (`op2).

  Definition trace_val : relation operation :=
    λ op1 op2, (`op1, `op2) ∈ m.

  Definition trace_empty : operation → Prop :=
    λ op, empty_of_trace_match ts m (`op).

  Lemma conc_history_trace_pre : ConcHistory trace_pre.
  Proof.
    apply (conc_history_queue_stack (A:=trace_op ts)).
    exact (queue.binder.conc_history_trace_pre ts m Hvalid Hcomplete Hclosed).
  Qed.

  Lemma trace_linearizable_bag__linearizable_set :
    per_tag_wellformed_bag rme valid_value ts →
    per_tag_pop_empty_sound ts m →
    linearizable_set trace_pre trace_val trace_empty.
  Proof.
    intros Hwf Hes.
    apply (linearizable_set_queue_stack (A:=trace_op ts)).
    exact (queue.binder.trace_linearizable_bag__linearizable_set
             rme valid_value ts m Hvalid Hcomplete Hclosed Hwf Hes).
  Qed.

  (* ===== The premise on a closed trace gives order-correctness ===== *)

  Definition trace_ir (ir : list (positive * positive)) : relation operation :=
    λ op1 op2, ir_rel ts m ir (`op1) (`op2).

  Lemma I_stack_pre__order_correct ir :
    per_tag_wellformed_bag rme valid_value ts →
    I_stack_pre ts m ir →
    order_correct trace_pre trace_val.
  Proof.
    intros Hwf (_ & _ & Hirwf & Hacyc & Hlifo).
    destruct Hclosed as [Hpush_m _].
    assert (Hev_pop : ∀ x y, (x, y) ∈ m → y ∈ events_of_trace ts).
    { intros x y Hin. apply elem_of_list_to_set.
      apply (list_elem_of_fmap_2 fst _ (y, Call Pop #())).
      exact (valid_match_call_pop _ _ _ _ Hvalid Hin). }
    assert (Hev_push : ∀ x y, (x, y) ∈ m → x ∈ events_of_trace ts).
    { intros x y Hin. destruct (valid_match_call_push _ _ _ _ Hvalid Hin) as [v Hv].
      apply elem_of_list_to_set. by apply (list_elem_of_fmap_2 fst _ (x, Call Push v)). }
    assert (His_push : ∀ a : operation, is_push trace_val a ↔ `a ∈ push_of_trace ts).
    { intros a. split.
      - intros [b Hab]. destruct (valid_match_call_push _ _ _ _ Hvalid Hab) as [v Hv].
        apply (list_elem_of_fmap_2 fst _ (`a, Call Push v)).
        apply list_elem_of_filter_2; [by exists v|done].
      - intros Ha. apply Hpush_m in Ha as ([x y] & Heq & Hin)%list_elem_of_fmap_1.
        simpl in Heq. subst x. by exists (y ↾ Hev_pop _ _ Hin). }
    assert (His_pop : ∀ a : operation, is_pop trace_val a ↔ `a ∈ m.*2).
    { intros a. split.
      - intros [b Hba]. by apply (list_elem_of_fmap_2 snd _ (`b, `a)).
      - intros ([x y] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst y.
        by exists (x ↾ Hev_push _ _ Hin). }
    assert (Hpp : ∀ x, x ∈ push_of_trace ts → x ∉ m.*2).
    { intros x Hx ([y z] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst z.
      apply (push_xor_pop_of_trace ts rme valid_value x Hwf Hx).
      apply (list_elem_of_fmap_2 fst _ (x, Call Pop #())).
      apply list_elem_of_filter_2; [done|exact (valid_match_call_pop _ _ _ _ Hvalid Hin)]. }
    exists (trace_ir ir). split_and!.
    - constructor.
      + intros a b [Hin|(Ha & Hb & _)].
        * destruct (Hirwf _ _ Hin) as [Hap Hbm].
          left. split; [by apply His_push|by apply His_pop].
        * right. split; [by apply His_pop|by apply His_push].
      + intros a b Ha Hb. apply His_push in Ha. apply His_pop in Hb.
        destruct (decide ((`a, `b) ∈ ir)) as [Hin|Hnin]; [left; by left|right; right; done].
    - intros a Ha. apply (Hacyc (`a)).
      assert (Htc : ∀ x y, tc (trace_pre ∪ trace_ir ir) x y → tc (stk_rel ts m ir) (`x) (`y)).
      { intros x y H. induction H as [x y H|x z y H _ IH].
        - apply tc_once. destruct H as [H|H]; [by left|by right].
        - eapply tc_l; [|exact IH]. destruct H as [H|H]; [by left|by right]. }
      by apply Htc.
    - intros ia ra ib Hval Hpre (Hpia & Hpib & Hor) Hir.
      apply His_push in Hpia, Hpib.
      assert (Hir' : (`ib, `ra) ∈ ir).
      { destruct Hir as [Hin|(Hib & _)]; [done|]. by destruct (Hpp (`ib)). }
      assert (Hins : ins_tr ts m ir (`ia) (`ib)).
      { split_and!; [done|done|].
        destruct Hor as [H|(c & H1 & H2)]; [by left|right; by exists (`c)]. }
      destruct (Hlifo (`ia) (`ra) (`ib) Hval Hpre Hins Hir') as (pb & Hpb & Hn).
      exists (pb ↾ Hev_pop _ _ Hpb). split; [done|].
      intros (_ & _ & [H|(c & H1 & H2)]); apply Hn; [by left|right; by exists (`c)].
  Qed.

  (* ===== The vis/rr premise on a closed trace gives the premises of Lemma 3 ===== *)

  Local Lemma trace_ev_pop x y : (x, y) ∈ m → y ∈ events_of_trace ts.
  Proof.
    intros Hin. apply elem_of_list_to_set.
    apply (list_elem_of_fmap_2 fst _ (y, Call Pop #())).
    exact (valid_match_call_pop _ _ _ _ Hvalid Hin).
  Qed.

  Local Lemma trace_ev_push x y : (x, y) ∈ m → x ∈ events_of_trace ts.
  Proof.
    intros Hin. destruct (valid_match_call_push _ _ _ _ Hvalid Hin) as [v Hv].
    apply elem_of_list_to_set. by apply (list_elem_of_fmap_2 fst _ (x, Call Push v)).
  Qed.

  Local Lemma trace_is_push (a : operation) : is_push trace_val a ↔ `a ∈ push_of_trace ts.
  Proof.
    split.
    - intros [b Hab]. destruct (valid_match_call_push _ _ _ _ Hvalid Hab) as [v Hv].
      apply (list_elem_of_fmap_2 fst _ (`a, Call Push v)).
      apply list_elem_of_filter_2; [by exists v|done].
    - intros Ha. destruct Hclosed as [Hpush_m _].
      apply Hpush_m in Ha as ([x y] & Heq & Hin)%list_elem_of_fmap_1.
      simpl in Heq. subst x. by exists (y ↾ trace_ev_pop _ _ Hin).
  Qed.

  Local Lemma trace_is_pop (a : operation) : is_pop trace_val a ↔ `a ∈ m.*2.
  Proof.
    split.
    - intros [b Hba]. by apply (list_elem_of_fmap_2 snd _ (`b, `a)).
    - intros ([x y] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst y.
      by exists (x ↾ trace_ev_push _ _ Hin).
  Qed.

  Definition trace_vis (f : positive → nat) : relation operation :=
    λ op1 op2, vis_rk ts m f (`op1) (`op2).

  Definition trace_rr (r : positive → nat) : relation operation :=
    λ op1 op2, `op1 ∈ m.*2 ∧ `op2 ∈ m.*2 ∧ r (`op1) < r (`op2).

  Lemma closed_vis__vis_rr f r :
    per_tag_wellformed_bag rme valid_value ts →
    closed_vis ts m f r →
    VisRr (non_empty_pre trace_pre trace_empty) trace_val (trace_vis f) (trace_rr r).
  Proof.
    intros Hwf Hcv.
    assert (Hpp : ∀ x, x ∈ push_of_trace ts → x ∉ m.*2).
    { intros x Hx ([y z] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst z.
      apply (push_xor_pop_of_trace ts rme valid_value x Hwf Hx).
      apply (list_elem_of_fmap_2 fst _ (x, Call Pop #())).
      apply list_elem_of_filter_2; [done|exact (valid_match_call_pop _ _ _ _ Hvalid Hin)]. }
    assert (Hop : ∀ a : operation, ¬ trace_empty a → vis_op ts m (`a)).
    { intros [τ Hτ] Hne. simpl.
      destruct (push_or_pop_of_trace ts rme valid_value τ Hwf Hτ) as [Hpush|Hpop]; [by left|right].
      destruct (decide (τ ∈ m.*2)) as [|Hn]; [done|]. exfalso. by apply Hne. }
    assert (Hch_ne : ConcHistory (non_empty_pre trace_pre trace_empty)).
    { apply pre_conc_history_then_non_empty_pre_conc_history, conc_history_trace_pre. }
    assert (Hsig : ∀ a b : operation, a ≠ b → `a ≠ `b).
    { intros a b Hne Heq. apply Hne. by apply (sig_eq_pi _). }
    constructor.
    - constructor.
      + intros a b [(Ha & Hb & _)|(Ha & Hb & _)].
        * left. split; [by apply trace_is_push|by apply trace_is_pop].
        * right. split; [by apply trace_is_pop|by apply trace_is_push].
      + intros a b Ha Hb. apply trace_is_push in Ha. apply trace_is_pop in Hb.
        assert (Hab : `a ≠ `b) by (intros Heq; apply (Hpp (`a) Ha); by rewrite Heq).
        destruct (Nat.lt_total (f (`a)) (f (`b))) as [Hlt|[Heq|Hlt]].
        * left. left. done.
        * exfalso. by apply (cv_inj _ _ _ _ Hcv (`a) (`b)); [left|right|..].
        * right. right. done.
    - apply (acyclic_of_rank (M:=trace_stack_model) _ (λ o, f (`o))).
      intros a b [(Hpre & Hna & Hnb)|[(_ & _ & Hlt)|(_ & _ & Hlt)]]; [|done|done].
      apply (cv_pre _ _ _ _ Hcv); [done|by apply Hop|by apply Hop].
    - intros a b Ha Hb Hne. apply trace_is_pop in Ha, Hb.
      destruct (Nat.lt_total (r (`a)) (r (`b))) as [Hlt|[Heq|Hlt]].
      + left. done.
      + exfalso. exact (cv_rr_inj _ _ _ _ Hcv (`a) (`b) Ha Hb (Hsig a b Hne) Heq).
      + right. done.
    - apply (acyclic_union_rank (M:=trace_stack_model) _ _ (λ o, `o ∈ m.*2) (λ o, r (`o))).
      + by destruct Hch_ne.
      + by destruct Hch_ne.
      + intros a b Hab. exact Hab.
      + intros a b Ha Hb (Hpre & _ & _). by apply (cv_rr_pre _ _ _ _ Hcv).
    - intros ia ra ib Hval (Hpre & _ & _) Hts Hvis.
      assert (Hra : `ra ∈ m.*2) by (by apply (list_elem_of_fmap_2 snd _ (`ia, `ra))).
      assert (Hib : `ib ∈ push_of_trace ts).
      { destruct Hvis as [(? & _ & _)|(_ & Hra' & _)]; [done|]. by destruct (Hpp (`ra)). }
      assert (Hfib : f (`ib) < f (`ra)) by (by destruct Hvis as [(_ & _ & ?)|(_ & _ & ?)]).
      assert (Hts' : ts_rk ts m f (`ia) (`ib)).
      { destruct Hts as [(Hp & _ & _)|[(c & (Hp & _ & _) & Hc)|(d & c & (Hp & _ & _) & Hd & Hc)]].
        - by left.
        - right; left. by exists (`c).
        - right; right. by exists (`d), (`c). }
      destruct (cv_lifo _ _ _ _ Hcv (`ia) (`ra) (`ib) Hval Hpre Hts' Hib Hfib) as (pb & Hpb & Hlt).
      exists (pb ↾ trace_ev_pop _ _ Hpb). split; [done|].
      split_and!; [by apply (list_elem_of_fmap_2 snd _ (`ib, pb))|done|done].
  Qed.

  (* ===== A linearization in the stack port gives a trace linearization ===== *)

  Local Notation has_matched_pop_in := (bag.binder.has_matched_pop_in m).
  Local Notation lin_event_val := (bag.binder.lin_event_val ts).
  Local Notation lin_events_of_ord := (bag.binder.lin_events_of_ord ts).
  Local Notation live_pushes_of := (bag.binder.live_pushes_of ts m).
  Local Notation push_value_of := (bag.binder.push_value_of ts).

  (* The stack contents after the operations in [sub]: live pushes, latest first. *)
  Local Definition stack_state_of (sub : list positive) : list val :=
    reverse (push_value_of <$> live_pushes_of sub).

  Local Lemma stack_state_of_push_step sub τ :
    τ ∈ push_of_trace ts →
    ¬ has_matched_pop_in τ (sub ++ [τ]) →
    stack_state_of (sub ++ [τ]) = push_value_of τ :: stack_state_of sub.
  Proof.
    intros Hpush Hnmp.
    rewrite /stack_state_of /live_pushes_of.
    rewrite (live_pushes_aux_app ts m).
    rewrite (live_pushes_aux_push_all ts m Hvalid Hcomplete Hclosed sub sub τ Hpush).
    simpl. destruct (decide (τ ∈ push_of_trace ts ∧ _)) as [_|Habs].
    - by rewrite fmap_app reverse_app.
    - exfalso. by apply Habs.
  Qed.

  Local Lemma live_pushes_of_nonpush_step sub τ :
    τ ∉ push_of_trace ts →
    live_pushes_of (sub ++ [τ])
      = List.filter (λ τ_p, if decide ((τ_p, τ) ∈ m) then false else true)
                    (live_pushes_of sub).
  Proof.
    intros Hnpush.
    rewrite /live_pushes_of (live_pushes_aux_app ts m).
    rewrite (live_pushes_aux_pop_all ts m sub sub τ Hnpush).
    simpl. destruct (decide (τ ∈ push_of_trace ts ∧ _)) as [[Hp _]|_].
    - by destruct Hnpush.
    - by rewrite app_nil_r.
  Qed.

  Local Lemma stack_state_invariant
      (Hper_tag_wf : per_tag_wellformed_bag rme valid_value ts)
      (prt : relation operation)
      (Hsub : subrelation trace_pre prt)
      (Htri : Trichotomy prt)
      (Htrans : Transitive prt)
      (Hirr : Irreflexive prt)
      (Hvnpr : val_then_not_pr prt trace_val)
      (Hlifo : sequential_lifo prt trace_val)
      (Hcorrect : correct_empty prt trace_val trace_empty)
      (ord : list positive)
      (Hord_nodup : NoDup ord)
      (Hord_mem : ∀ τ, τ ∈ ord ↔ τ ∈ events_of_trace ts)
      (Hord_sorted : ∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
        i < j → ord !! i = Some τ1 → ord !! j = Some τ2 →
        prt (τ1 ↾ H1) (τ2 ↾ H2)) :
    ∃ s', rtcL (model_step (M:=stack_model rme valid_value)) s_init s'
            (filter (is_lin ∘ snd) (ts'_lin ts ord)).
  Proof.
    rewrite (ts'_lin_lin_filter_events ts m Hvalid Hcomplete Hclosed).
    assert (Hmain : ∀ k, k ≤ length ord →
      rtcL (model_step (M:=stack_model rme valid_value))
        s_init (stack_state_of (take k ord)) (take k (lin_events_of_ord ord))).
    { intros k. induction k as [|k IHk]; intros Hk.
      - rewrite !take_0. simpl. apply rtcL_refl.
      - assert (Hk' : k ≤ length ord) by lia.
        assert (Hk'' : k < length ord) by lia.
        destruct (lookup_lt_is_Some_2 ord k Hk'') as [τ Hord_k].
        assert (Hτ_et : τ ∈ events_of_trace ts).
        { apply Hord_mem. eapply list_elem_of_lookup_2; eauto. }
        assert (Htake_ord : take (Datatypes.S k) ord = take k ord ++ [τ]).
        { by apply take_S_r. }
        assert (Htake_lin : take (Datatypes.S k) (lin_events_of_ord ord)
                          = take k (lin_events_of_ord ord) ++
                            [(τ, Lin (lin_event_val τ).1.1 (lin_event_val τ).1.2 (lin_event_val τ).2)]).
        { rewrite /lin_events_of_ord.
          assert (Hlk : map (λ τ0, (τ0, Lin (lin_event_val τ0).1.1 (lin_event_val τ0).1.2 (lin_event_val τ0).2)) ord
                       !! k
                     = Some (τ, Lin (lin_event_val τ).1.1 (lin_event_val τ).1.2 (lin_event_val τ).2)).
          { rewrite list_lookup_fmap. rewrite Hord_k. done. }
          rewrite (take_S_r _ _ _ Hlk). done. }
        rewrite Htake_lin Htake_ord.
        assert (Hτ_not_in_tk : τ ∉ take k ord).
        { intros Hin_tk.
          apply list_elem_of_lookup_1 in Hin_tk as (j & Hj).
          apply lookup_take_Some in Hj as [Hj Hjlt].
          assert (j = k) by (eapply NoDup_lookup; [exact Hord_nodup|exact Hj|exact Hord_k]).
          lia. }
        destruct (tag_is_push_or_pop rme valid_value ts Hper_tag_wf τ Hτ_et) as [Hpush|Hpop].
        + (* ===== PUSH case ===== *)
          destruct (push_tag_filter rme valid_value ts m Hvalid Hcomplete Hclosed Hper_tag_wf τ Hpush)
            as [v Hfilt].
          rewrite (lin_event_val_of ts τ _ _ _ Hfilt). simpl.
          assert (Hnmp : ¬ has_matched_pop_in τ (take k ord ++ [τ])).
          { intros Hmp%(has_matched_pop_in_iff m).
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
            - subst τ_pop. by eapply (push_not_in_matched_pop ts m Hvalid Hcomplete Hclosed). }
          rewrite (stack_state_of_push_step _ _ Hpush Hnmp).
          rewrite (push_value_of_push ts τ v #() Hfilt).
          eapply rtcL_r; [|constructor].
          * apply IHk. exact Hk'.
          * simpl.
            destruct (Hper_tag_wf τ) as [(v_push & ? & Hfilter) | (? & _ & Hfilter)];
              rewrite Hfilt in Hfilter; apply prefix_cons_inv_1 in Hfilter;
              by simplify_eq.
          * simpl. split; reflexivity.
        + (* ===== POP case ===== *)
          assert (Hτ_npush : τ ∉ push_of_trace ts).
          { intros Hτ_push. eapply push_xor_pop_of_trace; eauto. }
          destruct (decide (τ ∈ m.*2)) as [Hmatched|Hempty_test].
          * (* === MATCHED POP case === *)
            apply list_elem_of_fmap_1 in Hmatched as ((τ_p & τ') & Heq & Hin_m).
            simpl in Heq. subst τ'.
            destruct (valid_match_call_push _ _ _ _ Hvalid Hin_m) as [v Hcall_p].
            assert (Hτ_p_push : τ_p ∈ push_of_trace ts).
            { apply (list_elem_of_fmap_2 fst _ (τ_p, Call Push v)).
              apply list_elem_of_filter_2; last exact Hcall_p.
              simpl. exists v. done. }
            assert (Hτ_p_et : τ_p ∈ events_of_trace ts).
            { apply elem_of_list_to_set.
              apply (list_elem_of_fmap_2 fst _ (τ_p, Call Push v)); done. }
            pose proof (matched_pop_filter rme valid_value ts m Hvalid Hcomplete Hclosed
                          Hper_tag_wf τ_p τ v Hin_m Hcall_p Hpop) as Hfilt.
            rewrite (lin_event_val_of ts τ _ _ _ Hfilt). simpl.
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
            assert (Hτ_p_nmp : ¬ has_matched_pop_in τ_p (take k ord)).
            { intros (τ_pop' & Hin_m' & Hin_tk)%(has_matched_pop_in_iff m).
              apply Huniq_pop in Hin_m' as ->.
              by apply Hτ_not_in_tk. }
            (* LIFO: no push after τ_p in take k ord is live. *)
            assert (Hnone_after : ∀ τ_q, τ_q ∈ drop (Datatypes.S i_p) (take k ord) →
                      ¬ (τ_q ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ_q (take k ord))).
            { intros τ_q Hin_q [Hpush_q Hnmp_q].
              apply list_elem_of_lookup_1 in Hin_q as (d & Hd).
              rewrite lookup_drop lookup_take_Some in Hd. destruct Hd as [Hi_q Hi_q_lt].
              set (i_q := Datatypes.S i_p + d) in *.
              destruct Hclosed as [Hpush_sub _].
              assert (Hτ_q_in_m : τ_q ∈ m.*1) by (apply Hpush_sub; done).
              apply list_elem_of_fmap_1 in Hτ_q_in_m as ((τ_q' & τ_qp) & Heq & Hin_q_m).
              simpl in Heq. subst τ_q'.
              assert (Hτ_qp_et : τ_qp ∈ events_of_trace ts).
              { apply elem_of_list_to_set.
                apply (list_elem_of_fmap_2 fst _ (τ_qp, Call Pop #())).
                exact (valid_match_call_pop _ _ _ _ Hvalid Hin_q_m). }
              apply Hord_mem in Hτ_qp_et as Hτ_qp_in_ord.
              apply list_elem_of_lookup_1 in Hτ_qp_in_ord as (j_qp & Hj_qp).
              destruct (Nat.lt_trichotomy j_qp k) as [Hlt|[Heq|Hgt]].
              - apply Hnmp_q. apply (has_matched_pop_in_iff m). exists τ_qp.
                split; first done.
                eapply list_elem_of_lookup_2. apply lookup_take_Some. split; done.
              - subst j_qp. rewrite Hj_qp in Hord_k. injection Hord_k as Hqp_eq.
                subst τ_qp.
                assert (Hqeq : τ_q = τ_p) by (apply Huniq; done).
                subst τ_q.
                assert (i_q = i_p) by (eapply NoDup_lookup; [exact Hord_nodup|exact Hi_q|exact Hi_p]).
                lia.
              - (* j_qp > k: prt τ_p τ_q and prt τ_q τ, so LIFO gives prt τ_qp τ;
                   but prt τ τ_qp (sorted). Contradiction. *)
                assert (Hτ_q_et : τ_q ∈ events_of_trace ts).
                { apply Hord_mem. eapply list_elem_of_lookup_2. exact Hi_q. }
                assert (Hip_iq : i_p < i_q) by lia.
                pose proof (Hord_sorted i_p i_q τ_p τ_q Hτ_p_et Hτ_q_et Hip_iq Hi_p Hi_q) as Hprt_pq.
                pose proof (Hord_sorted i_q k τ_q τ Hτ_q_et Hτ_et Hi_q_lt Hi_q Hord_k) as Hprt_qτ.
                pose proof (Hlifo (τ_p ↾ Hτ_p_et) (τ_q ↾ Hτ_q_et) (τ ↾ Hτ_et) (τ_qp ↾ Hτ_qp_et)
                              Hin_m Hin_q_m Hprt_pq Hprt_qτ) as Hprt_qp_τ.
                assert (Hk_lt_j : k < j_qp) by lia.
                pose proof (Hord_sorted k j_qp τ τ_qp Hτ_et Hτ_qp_et Hk_lt_j Hord_k Hj_qp) as Hprt_τ_qp.
                pose proof (Htrans _ _ _ Hprt_qp_τ Hprt_τ_qp) as Hcy.
                by apply (Hirr _ Hcy). }
            (* So τ_p is the last live push. *)
            assert (Htake_split : take k ord = take i_p (take k ord) ++ τ_p :: drop (Datatypes.S i_p) (take k ord)).
            { apply eq_sym. apply take_drop_middle.
              apply lookup_take_Some. split; [|lia]. done. }
            assert (Hlp_decomp : live_pushes_of (take k ord)
              = live_pushes_aux ts m (take i_p (take k ord)) (take k ord) ++ [τ_p]).
            { rewrite /live_pushes_of {1}Htake_split (live_pushes_aux_app ts m) /=.
              rewrite (live_pushes_aux_empty ts m _ _ Hnone_after).
              destruct (decide (τ_p ∈ push_of_trace ts ∧ _)) as [_|Habs]; [done|].
              exfalso. by apply Habs. }
            assert (Hfilt_p : filter (λ x, x.1 = τ_p) ts
                             = [(τ_p, Call Push v); (τ_p, Ret #())]).
            { destruct (push_tag_filter rme valid_value ts m Hvalid Hcomplete Hclosed
                          Hper_tag_wf τ_p Hτ_p_push) as [v' Hfilt'].
              assert (Hv_eq : v' = v).
              { assert (Hin_v : (τ_p, Call Push v) ∈ filter (λ x, x.1 = τ_p) ts)
                  by (apply list_elem_of_filter_2; done).
                rewrite Hfilt' in Hin_v.
                rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_v.
                destruct Hin_v as [Heq|[?|[]]]; last discriminate.
                by simplify_eq. }
              subst v'. exact Hfilt'. }
            assert (Hstate_eq : stack_state_of (take k ord) = v :: stack_state_of (take k ord ++ [τ])).
            { rewrite /stack_state_of (live_pushes_of_nonpush_step _ _ Hτ_npush) Hlp_decomp.
              rewrite List.filter_app /=.
              destruct (decide ((τ_p, τ) ∈ m)) as [_|]; [|done].
              rewrite app_nil_r fmap_app reverse_app /=.
              rewrite (push_value_of_push ts τ_p v #() Hfilt_p).
              f_equal. f_equal. f_equal. symmetry.
              apply List_filter_all_true.
              intros τ_q Hin_q.
              destruct (decide ((τ_q, τ) ∈ m)) as [Hin_m_q|]; [|done].
              exfalso. pose proof (Huniq τ_q Hin_m_q) as ->.
              assert (Hnd_lp : NoDup (live_pushes_of (take k ord))).
              { apply (NoDup_live_pushes ts m).
                rewrite <- (take_drop k ord) in Hord_nodup.
                by apply NoDup_app in Hord_nodup as (? & _). }
              rewrite Hlp_decomp in Hnd_lp.
              apply NoDup_app in Hnd_lp as (_ & Hdisj & _).
              apply (Hdisj τ_p Hin_q). by left. }
            eapply rtcL_r; [|constructor].
            -- apply IHk. exact Hk'.
            -- reflexivity.
            -- simpl. rewrite Hstate_eq. done.
          * (* === EMPTY POP case === *)
            assert (Hempty : trace_empty (τ ↾ Hτ_et)).
            { unfold trace_empty, empty_of_trace_match. simpl. done. }
            pose proof (empty_pop_filter rme valid_value ts m Hvalid Hcomplete Hclosed
                          Hper_tag_wf τ Hpop Hempty_test) as Hfilt.
            rewrite (lin_event_val_of ts τ _ _ _ Hfilt). simpl.
            assert (Hlp_empty : live_pushes_of (take k ord) = []).
            { rewrite /live_pushes_of.
              apply (live_pushes_aux_empty ts m (take k ord) (take k ord)).
              intros τ_q Hin_q [Hpush_q Hnmp_q].
              apply list_elem_of_lookup_1 in Hin_q as (i_q & Hi_q).
              apply lookup_take_Some in Hi_q as [Hi_q Hi_q_lt].
              assert (Hτ_q_et : τ_q ∈ events_of_trace ts).
              { apply Hord_mem. eapply list_elem_of_lookup_2. exact Hi_q. }
              destruct Hclosed as [Hpush_sub _].
              assert (Hτ_q_in_m : τ_q ∈ m.*1) by (apply Hpush_sub; done).
              apply list_elem_of_fmap_1 in Hτ_q_in_m as ((τ_q' & τ_qp) & Heq & Hin_q_m).
              simpl in Heq. subst τ_q'.
              assert (Hτ_qp_et : τ_qp ∈ events_of_trace ts).
              { apply elem_of_list_to_set.
                apply (list_elem_of_fmap_2 fst _ (τ_qp, Call Pop #())).
                exact (valid_match_call_pop _ _ _ _ Hvalid Hin_q_m). }
              apply Hord_mem in Hτ_qp_et as Hτ_qp_in_ord.
              apply list_elem_of_lookup_1 in Hτ_qp_in_ord as (j_qp & Hj_qp).
              destruct (Nat.lt_trichotomy j_qp k) as [Hlt|[Heq|Hgt]].
              + apply Hnmp_q. apply (has_matched_pop_in_iff m). exists τ_qp.
                split; first done.
                eapply list_elem_of_lookup_2. apply lookup_take_Some. split; done.
              + subst j_qp. rewrite Hj_qp in Hord_k. injection Hord_k as <-.
                apply Hempty_test. apply (list_elem_of_fmap_2 snd _ (τ_q, τ_qp)); done.
              + pose proof (Hcorrect (τ ↾ Hτ_et) Hempty (τ_q ↾ Hτ_q_et) (τ_qp ↾ Hτ_qp_et) Hin_q_m)
                  as [[Hprt1 Hprt2]|[Hprt1 Hprt2]].
                * assert (Hk_lt_j : k < j_qp) by lia.
                  pose proof (Hord_sorted k j_qp τ τ_qp Hτ_et Hτ_qp_et Hk_lt_j Hord_k Hj_qp) as Hprt_τ_qp.
                  pose proof (Htrans _ _ _ Hprt2 Hprt_τ_qp) as Hcy.
                  by apply (Hirr _ Hcy).
                * pose proof (Hord_sorted i_q k τ_q τ Hτ_q_et Hτ_et Hi_q_lt Hi_q Hord_k) as Hprt_q_τ.
                  pose proof (Htrans _ _ _ Hprt1 Hprt_q_τ) as Hcy.
                  by apply (Hirr _ Hcy). }
            assert (Hstate_empty : stack_state_of (take k ord) = []).
            { by rewrite /stack_state_of Hlp_empty. }
            assert (Hstate_empty2 : stack_state_of (take k ord ++ [τ]) = []).
            { by rewrite /stack_state_of (live_pushes_of_nonpush_step _ _ Hτ_npush) Hlp_empty. }
            rewrite Hstate_empty2.
            eapply rtcL_r; [|constructor].
            -- apply IHk. exact Hk'.
            -- reflexivity.
            -- simpl. rewrite Hstate_empty.
               destruct rme; first done.
               exfalso.
               destruct (Hper_tag_wf τ) as [(? & _ & Hpfx)|(r & Hr_ne & Hpfx)].
               { rewrite Hfilt in Hpfx. apply prefix_cons_inv_1 in Hpfx. discriminate. }
               rewrite Hfilt in Hpfx.
               apply prefix_cons_inv_2, prefix_cons_inv_1 in Hpfx.
               injection Hpfx as Hr_eq.
               assert (r = IsEmpty) as ->.
               { destruct r; simpl in Hr_eq; [done|discriminate]. }
               by apply Hr_ne. }
    exists (stack_state_of ord).
    replace (lin_events_of_ord ord) with (take (length ord) (lin_events_of_ord ord)).
    2: { apply take_ge. rewrite /lin_events_of_ord length_map. lia. }
    replace ord with (take (length ord) ord) at 1.
    2: { apply take_ge. lia. }
    apply Hmain. lia.
  Qed.

  Lemma linearizable_stack__trace_linearizable_stack :
    per_tag_wellformed_bag rme valid_value ts →
    linearizable_stack trace_pre trace_val trace_empty →
    trace_linearizable (M:=stack_model rme valid_value) ts.
  Proof.
    intros Hper_tag_wf (Hch & prt & Hsub & Hseq).
    destruct Hseq as [Hses Hlifo].
    destruct Hses as [Hseh Hcorrect].
    destruct Hseh as [Hwfe Htri].
    destruct Hwfe as [Hprt_ch _ _ _ _ _ _ Hvnpr].
    destruct Hprt_ch as [Htrans Hanti Hirr _].
    destruct (prt_sort_exists ts prt Htri Htrans Hirr)
      as (ord & Hord_nodup & Hord_mem & Hord_sorted).
    split.
    { exact (call_valid_ts rme valid_value ts m Hvalid Hcomplete Hclosed
               (stack_model rme valid_value) eq_refl Hper_tag_wf). }
    exists (ts'_lin ts ord).
    split_and!.
    - symmetry. exact (ts'_lin_filter_not_lin ts m Hvalid Hcomplete Hclosed ord).
    - exact (ts'_lin_per_tag_linearized valid_value ts m Hvalid Hcomplete Hclosed
               prt Hsub Htrans Hirr Hanti ord Hord_mem Hord_nodup Hord_sorted).
    - exact (stack_state_invariant Hper_tag_wf prt Hsub Htri Htrans Hirr Hvnpr Hlifo Hcorrect
               ord Hord_nodup Hord_mem Hord_sorted).
  Qed.
End stack_binder.
