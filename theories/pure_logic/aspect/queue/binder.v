From stdpp Require Import finite.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.bag Require Import base linear_points binder.
From iris_logatom.pure_logic.aspect.bag Require set_binder.
From iris_logatom.pure_logic.aspect.queue Require Import ext.abstract_queue base.

(* The queue-specific part of the trace <-> history binding. The model-independent part
   (history instance, sorting, Lin insertion, live pushes) is in bag/binder.v, and the
   linearizability of the trace as a set history is in bag/set_binder.v; the relations
   below are those of bag/binder.v, typed by the queue model of the trace. *)

Section proof.
  Variables (rme : response_mayempty) (valid_value : val → Prop) (ts : list (positive * trace)) (m : list (positive*positive)).
  Hypothesis Hvalid : valid_match ts m.
  Hypothesis Hcomplete : per_tag_complete ts.
  Hypothesis Hclosed : closed_match ts m.

  Local Notation has_matched_pop_in := (bag.binder.has_matched_pop_in m).
  Local Notation lin_event_val := (bag.binder.lin_event_val ts).
  Local Notation lin_events_of_ord := (bag.binder.lin_events_of_ord ts).
  Local Notation live_pushes_of := (bag.binder.live_pushes_of ts m).
  Local Notation push_value_of := (bag.binder.push_value_of ts).

  Local Instance trace_queue_model : abstract_queue_model := {|
    operation := trace_op ts;
    operation_eq_dec := _;
    operation_finite := _;
  |}.

  Definition trace_pre : relation operation :=
    λ op1 op2, pre_of_trace ts (`op1) (`op2).

  Definition trace_val : relation operation :=
    λ op1 op2, (`op1, `op2) ∈ m.

  Definition trace_empty : operation → Prop :=
    λ op, empty_of_trace_match ts m (`op).

  Global Instance trace_pre_dec : RelDecision trace_pre.
  Proof. intros a b. unfold trace_pre. apply _. Qed.

  Global Instance trace_val_dec : RelDecision trace_val.
  Proof. intros a b. unfold trace_val. apply _. Qed.

  Global Instance trace_empty_dec a : Decision (trace_empty a).
  Proof. unfold trace_empty. apply _. Qed.

  Lemma trace_linearizable_bag__linearizable_set :
    per_tag_wellformed_bag rme valid_value ts →
    per_tag_pop_empty_sound ts m →
    linearizable_set trace_pre trace_val trace_empty.
  Proof.
    exact (set_binder.trace_linearizable_bag__linearizable_set
             rme valid_value ts m Hvalid Hcomplete Hclosed).
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

  (* ===== Queue state reconstruction ===== *)
  Local Definition queue_state_of (sub : list positive) : list val :=
    map push_value_of (live_pushes_of sub).

  (* ===== Helper lemmas for queue_state_of ===== *)

  (* Step: push with no matched pop in sub ++ [τ] adds push_value_of τ to queue. *)
  Local Lemma queue_state_of_push_step sub τ :
    τ ∈ push_of_trace ts →
    ¬ has_matched_pop_in τ (sub ++ [τ]) →
    queue_state_of (sub ++ [τ]) = queue_state_of sub ++ [push_value_of τ].
  Proof.
    intros Hpush Hnmp.
    rewrite /queue_state_of /live_pushes_of.
    rewrite (live_pushes_aux_app ts m).
    rewrite (live_pushes_aux_push_all ts m Hvalid Hcomplete Hclosed sub sub τ Hpush).
    rewrite map_app. f_equal.
    simpl.
    destruct (decide (τ ∈ push_of_trace ts ∧ ¬ has_matched_pop_in τ (sub ++ [τ]))) as [_|Habs].
    - done.
    - exfalso. apply Habs. split; done.
  Qed.

  Local Lemma queue_state_of_nonpush_step sub τ :
    τ ∉ push_of_trace ts →
    queue_state_of (sub ++ [τ])
      = map push_value_of
          (List.filter (λ τ_p, if decide ((τ_p, τ) ∈ m) then false else true)
                       (live_pushes_of sub)).
  Proof.
    intros Hnpush.
    rewrite /queue_state_of /live_pushes_of.
    rewrite (live_pushes_aux_app ts m).
    rewrite (live_pushes_aux_pop_all ts m sub sub τ Hnpush).
    simpl.
    destruct (decide (τ ∈ push_of_trace ts ∧ _)) as [[Hp _]|_].
    - exfalso. apply Hnpush. exact Hp.
    - by rewrite app_nil_r.
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
      (Hadq_emp : all_popped_or_empty trace_val trace_empty)
      (ord : list positive)
      (Hord_nodup : NoDup ord)
      (Hord_mem : ∀ τ, τ ∈ ord ↔ τ ∈ events_of_trace ts)
      (Hord_sorted : ∀ i j τ1 τ2 (H1 : τ1 ∈ events_of_trace ts) (H2 : τ2 ∈ events_of_trace ts),
        i < j → ord !! i = Some τ1 → ord !! j = Some τ2 →
        prt (τ1 ↾ H1) (τ2 ↾ H2)) :
    ∃ s', rtcL (model_step (M:=queue_model rme valid_value)) s_init s'
            (filter (is_lin ∘ snd) (ts'_lin ts ord)).
  Proof.
    rewrite (ts'_lin_lin_filter_events ts m Hvalid Hcomplete Hclosed).
    (* Strong IH: for each k ≤ length ord, the take-k prefix of Lin events
       is sound and ends in queue_state_of (take k ord). *)
    assert (Hmain : ∀ k, k ≤ length ord →
      rtcL (model_step (M:=queue_model rme valid_value))
        s_init (queue_state_of (take k ord)) (take k (lin_events_of_ord ord))).
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
        (* τ ∉ take k ord (from NoDup ord and τ at position k) *)
        assert (Hτ_not_in_tk : τ ∉ take k ord).
        { intros Hin_tk.
          apply list_elem_of_lookup_1 in Hin_tk as (j & Hj).
          apply lookup_take_Some in Hj as [Hj Hjlt].
          assert (j = k) by (eapply NoDup_lookup; [exact Hord_nodup|exact Hj|exact Hord_k]).
          lia. }
        (* Case split on τ *)
        destruct (tag_is_push_or_pop rme valid_value ts Hper_tag_wf τ Hτ_et) as [Hpush|Hpop].
        + (* ===== PUSH case ===== *)
          destruct (push_tag_filter rme valid_value ts m Hvalid Hcomplete Hclosed Hper_tag_wf τ Hpush) as [v Hfilt].
          rewrite (lin_event_val_of ts τ _ _ _ Hfilt). simpl.
          (* Goal: rtcL model_step [] (queue_state_of (take k ord ++ [τ])) (... ++ [(τ, Lin (Push v) #())]) *)
          (* ¬ has_matched_pop_in τ (take k ord ++ [τ]) *)
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
          rewrite (queue_state_of_push_step _ _ Hpush Hnmp).
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
            pose proof (matched_pop_filter rme valid_value ts m Hvalid Hcomplete Hclosed Hper_tag_wf τ_p τ v Hin_m Hcall_p Hpop) as Hfilt.
            rewrite (lin_event_val_of ts τ _ _ _ Hfilt). simpl.
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
            { intros (τ_pop' & Hin_m' & Hin_tk)%(has_matched_pop_in_iff m).
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
                apply (list_elem_of_fmap_2 fst _ (τ_qp, Call Pop #())).
                apply list_elem_of_filter_2; done. }
              assert (Hτ_qp_et : τ_qp ∈ events_of_trace ts).
              { apply elem_of_list_to_set.
                apply (list_elem_of_fmap_2 fst _ (τ_qp, Call Pop #())).
                pose proof (valid_match_call_pop _ _ _ _ Hvalid Hin_q_m); done. }
              apply Hord_mem in Hτ_qp_et as Hτ_qp_in_ord.
              apply list_elem_of_lookup_1 in Hτ_qp_in_ord as (j_qp & Hj_qp).
              (* τ_qp's position in ord *)
              assert (Hτ_qp_et' : τ_qp ∈ events_of_trace ts) by (apply Hord_mem; eapply list_elem_of_lookup_2; done).
              destruct (Nat.lt_trichotomy j_qp k) as [Hlt|[Heq|Hgt]].
              - (* j_qp < k: τ_qp ∈ take k ord, so has_matched_pop_in τ_q (take k ord) TRUE,
                   contradicting Hnmp_q. *)
                apply Hnmp_q. apply (has_matched_pop_in_iff m). exists τ_qp.
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
              = τ_p :: live_pushes_aux ts m (drop (Datatypes.S i_p) (take k ord)) (take k ord)).
            { rewrite /live_pushes_of.
              apply (live_pushes_aux_head_decomp ts m _ _ τ_p (take i_p (take k ord))
                                                  (drop (Datatypes.S i_p) (take k ord))).
              - exact Htake_split.
              - exact Hτ_p_push.
              - exact Hτ_p_nmp.
              - rewrite Htake_prefix. exact Hnone_before. }
            (* Get Hfilt_p: filter (tag=τ_p) ts = [(τ_p, Call (Push v)); (τ_p, Ret #())] *)
            assert (Hfilt_p : filter (λ x, x.1 = τ_p) ts
                             = [(τ_p, Call Push v); (τ_p, Ret #())]).
            { destruct (push_tag_filter rme valid_value ts m Hvalid Hcomplete Hclosed Hper_tag_wf τ_p Hτ_p_push) as [v' Hfilt'].
              assert (Hv_eq : v' = v).
              { assert (Hin_v : (τ_p, Call Push v) ∈ filter (λ x, x.1 = τ_p) ts)
                  by (apply list_elem_of_filter_2; done).
                rewrite Hfilt' in Hin_v.
                rewrite elem_of_cons elem_of_cons elem_of_nil in Hin_v.
                destruct Hin_v as [Heq|[?|[]]]; last discriminate.
                by simplify_eq. }
              subst v'. exact Hfilt'. }
            (* Key equation: queue_state_of (take k ord) = v :: queue_state_of (take k ord ++ [τ]) *)
            assert (Hstate_eq : queue_state_of (take k ord) = v :: queue_state_of (take k ord ++ [τ])).
            { unfold queue_state_of at 1. rewrite Hlp_decomp. simpl.
              rewrite (push_value_of_push ts τ_p v #() Hfilt_p).
              f_equal.
              rewrite (queue_state_of_nonpush_step _ _ Hτ_npush).
              unfold queue_state_of. rewrite Hlp_decomp.
              rewrite (filter_out_matched_head m _ τ_p τ (ex_intro _ _ eq_refl) Hin_m).
              - done.
              - (* No other τ_q in tail has (τ_q, τ) ∈ m *)
                intros τ_q Hin_q Hin_m_q.
                simpl in Hin_q.
                pose proof (Huniq τ_q Hin_m_q) as ->.
                assert (Hnd_lp : NoDup (live_pushes_of (take k ord))).
                { apply (NoDup_live_pushes ts m).
                  rewrite <- (take_drop k ord) in Hord_nodup.
                  by apply NoDup_app in Hord_nodup as (? & _). }
                rewrite Hlp_decomp in Hnd_lp.
                apply NoDup_cons in Hnd_lp as [Hne _]. done. }
            eapply rtcL_r; [|constructor].
            -- apply IHk. exact Hk'.
            -- reflexivity.
            -- simpl. rewrite Hstate_eq. done.
          * (* === EMPTY POP case === *)
            assert (Hempty : trace_empty (τ ↾ Hτ_et)).
            { unfold trace_empty, empty_of_trace_match. simpl. done. }
            pose proof (empty_pop_filter rme valid_value ts m Hvalid Hcomplete Hclosed Hper_tag_wf τ Hpop Hempty_test) as Hfilt.
            rewrite (lin_event_val_of ts τ _ _ _ Hfilt). simpl.
            (* Show queue_state_of (take k ord) = [] *)
            assert (Hstate_empty : queue_state_of (take k ord) = []).
            { rewrite /queue_state_of /live_pushes_of.
              rewrite (live_pushes_aux_empty ts m (take k ord) (take k ord)).
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
                  apply (list_elem_of_fmap_2 fst _ (τ_qp, Call Pop #())).
                  apply list_elem_of_filter_2; done. }
                assert (Hτ_qp_et : τ_qp ∈ events_of_trace ts).
                { apply elem_of_list_to_set.
                  apply (list_elem_of_fmap_2 fst _ (τ_qp, Call Pop #())).
                  pose proof (valid_match_call_pop _ _ _ _ Hvalid Hin_q_m); done. }
                apply Hord_mem in Hτ_qp_et as Hτ_qp_in_ord.
                apply list_elem_of_lookup_1 in Hτ_qp_in_ord as (j_qp & Hj_qp).
                assert (Hτ_qp_et' : τ_qp ∈ events_of_trace ts)
                  by (apply Hord_mem; eapply list_elem_of_lookup_2; done).
                destruct (Nat.lt_trichotomy j_qp k) as [Hlt|[Heq|Hgt]].
                + (* j_qp < k: τ_qp ∈ take k ord → τ_q is matched; Hnmp_q contradiction *)
                  apply Hnmp_q. apply (has_matched_pop_in_iff m). exists τ_qp.
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
               by apply Hr_ne.
    }
    exists (queue_state_of ord).
    replace (lin_events_of_ord ord) with (take (length ord) (lin_events_of_ord ord)).
    2: { apply take_ge. rewrite /lin_events_of_ord. rewrite length_map. lia. }
    replace ord with (take (length ord) ord) at 1.
    2: { apply take_ge. lia. }
    apply Hmain. lia.
  Qed.

  Lemma linearizable_queue__trace_linearizable_queue :
    per_tag_wellformed_bag rme valid_value ts →
    linearizable_queue trace_pre trace_val trace_empty →
    trace_linearizable (M:=queue_model rme valid_value) ts.
  Proof.
    intros Hper_tag_wf Hlinq.
    destruct Hlinq as (Hch & prt & _ & Hsub & Hseq).
    destruct Hseq as [Hses Hfifo].
    destruct Hses as [Hseh Hcorrect].
    destruct Hseh as [Hwfe Htri].
    pose proof Hwfe as Hwfe0.
    destruct Hwfe as [Hprt_ch _ Henq_once Hdeq_once Hval_order Hadq_emp Hemp_notval Hvnpr].
    (* Extract prt properties from ConcHistory *)
    pose proof Hprt_ch as Hprt_ch0.
    destruct Hprt_ch as [Htrans Hanti Hirr _].
    (* Get the sorted order *)
    destruct (prt_sort_exists ts prt Htri Htrans Hirr)
      as (ord & Hord_nodup & Hord_mem & Hord_sorted).
    (* Assemble the result *)
    split.
    { exact (call_valid_ts rme valid_value ts m Hvalid Hcomplete Hclosed (queue_model rme valid_value) eq_refl Hper_tag_wf). }
    exists (ts'_lin ts ord).
    split_and!.
    - symmetry. exact (ts'_lin_filter_not_lin ts m Hvalid Hcomplete Hclosed ord).
    - exact (ts'_lin_per_tag_linearized valid_value ts m Hvalid Hcomplete Hclosed prt Hsub Htrans Hirr Hanti
               ord Hord_mem Hord_nodup Hord_sorted).
    - exact (queue_state_invariant Hper_tag_wf prt Hsub Htri Htrans Hirr Hvnpr Hfifo Hcorrect Hadq_emp
               ord Hord_nodup Hord_mem Hord_sorted).
  Qed.
  (* End LLM-generated code. *)
  (**********************************************************)
End proof.
