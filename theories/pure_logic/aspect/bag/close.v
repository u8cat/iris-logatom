From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.models Require Export bag_like.
From iris_logatom.pure_logic.aspect.bag Require Import base.

(* This function returns a list of trace entries to add. *)
Local Definition complete_trace_add_push (unpaired_pushes : list positive) :=
  (λ τ, (τ, Ret #())) <$> unpaired_pushes.

(* Return values: (1) a list edges to be added to the match relation;
  (2) the remaining unmatched push *)
Local Fixpoint complete_trace_add_match (unpaired_pops : list positive)
  (m : list (positive*positive)) (unmatched_pushes : list positive) :=
  match unpaired_pops with
  | [] => ([], unmatched_pushes)
  | τ2::unpaired_pops =>
    match find (λ x, bool_decide (x.2 = τ2)) m with
    | Some _ => complete_trace_add_match unpaired_pops m unmatched_pushes
    | None =>
      match unmatched_pushes with
      | τ1::unmatched_pushes =>
        let '(m_add, ump) := complete_trace_add_match unpaired_pops m unmatched_pushes in
        ((τ1,τ2)::m_add, ump)
      | [] => complete_trace_add_match unpaired_pops m []
      end
    end
  end.

Local Definition ret_val_of_call (c : nat * val) : val :=
  encode_response (NonEmpty c.2).

(* Returns a list of trace entries to add. Unmatched unfinished pops are
   not given a Ret here; their Call events are removed from [ts] in
   [close_trace] instead. *)
Local Definition complete_trace_remove_pop (unpaired_pops : list positive)
  (calls : gmap positive (nat*val)) (m_app_m_add : list (positive*positive)) :=
  omap (λ τ2,
    match find (λ x, bool_decide (x.2 = τ2)) m_app_m_add with
    | Some (τ1,_) => Some (τ2, Ret (ret_val_of_call (calls!!!τ1)))
    | None => None
    end) unpaired_pops.

(* Returns a list edges to be added to the match relation *)
Local Fixpoint close_trace_add_match (unmatched_pushes : list positive) (next_tag : positive) :=
  match unmatched_pushes with
  | [] => []
  | τ1::unmatched_pushes =>
    let τ2 := next_tag in
    (τ1,τ2)::close_trace_add_match unmatched_pushes (τ2+1)
  end.

(* Pop Call events for fresh tags, in m_add order. *)
Local Definition close_trace_add_pop_calls (m_add : list (positive*positive)) :=
  (λ '(τ1,τ2), (τ2, Call Pop #())) <$> m_add.

(* Pop Ret events for fresh tags, in m_add order. Each Ret τ2 returns the
   value of the matched push τ1, looked up in [calls]. *)
Local Definition close_trace_add_pop_rets (calls : gmap positive (nat*val)) (m_add : list (positive*positive)) :=
  (λ '(τ1,τ2), (τ2, Ret (ret_val_of_call (calls!!!τ1)))) <$> m_add.

(* Combined pop events: Calls front-loaded, Rets back-loaded.
   In [close_trace], the Calls section and Rets section are SEPARATED by
   [new_pops1] so that, for stack LIFO linearizability, each fresh Pop's
   Call comes before any [npop1] Ret event. *)
Local Definition close_trace_add_pop (calls : gmap positive (nat*val)) (m_add : list (positive*positive)) :=
  close_trace_add_pop_calls m_add ++ close_trace_add_pop_rets calls m_add.

Local Strategy 100 [close_trace_add_pop close_trace_add_pop_calls close_trace_add_pop_rets].

Local Definition max_tag (τs : list positive) :=
  foldl (λ x y, x `max` y)%positive 1%positive τs.

Local Definition unpaired_operations (ts : list (positive*trace)) (m : list (positive*positive)) :=
  let call_pushes := (filter (is_call_push∘snd) ts).*1 in
  let call_pops := (filter (is_call_pop∘snd) ts).*1 in
  let ret_pushes := (filter (is_ret_push∘snd) ts).*1 in
  let ret_pops := (filter (is_ret_pop∘snd) ts).*1 in
  (list_difference call_pushes ret_pushes,
    list_difference call_pops ret_pops,
    list_difference call_pushes m.*1).

Local Definition extract_calls (ts : list (positive*trace)) : gmap positive (nat*val) :=
  list_to_map (omap (λ x : positive * trace,
    match x with (τ, Call n v) => Some (τ, (n, v)) | _ => None end) ts).

Definition close_trace (ts : list (positive*trace)) (m : list (positive*positive)) :=
  let '(unpaired_pushes, unpaired_pops, unmatched_pushes) := unpaired_operations ts m in
  let calls := extract_calls ts in
  let new_pushes := complete_trace_add_push unpaired_pushes in
  let (new_matches1, unmatched_pushes) := complete_trace_add_match unpaired_pops m unmatched_pushes in
  let new_pops1 := complete_trace_remove_pop unpaired_pops calls (m++new_matches1) in
  let unmatched_pops := list_difference unpaired_pops (m++new_matches1).*2 in
  let ts' := filter (λ x, x.1 ∉ unmatched_pops) ts in
  let new_matches2 := close_trace_add_match unmatched_pushes (max_tag ts.*1 + 1) in
  let new_pop2_calls := close_trace_add_pop_calls new_matches2 in
  let new_pop2_rets := close_trace_add_pop_rets calls new_matches2 in
  (ts'++new_pushes++new_pop2_calls++new_pops1++new_pop2_rets, m++new_matches1++new_matches2).

Lemma close_prefix (M : model) rme valid_value ts m :
  M.(valid_requests) = [valid_value; λ v, v = #()] →
  per_tag_wellformed_bag rme valid_value ts →
  ∃ ts_mid,
    ts_mid `prefix_of` (close_trace ts m).1
    ∧ is_adding_call (M := M) ts ts_mid.
Proof.
(*************** Begin LLM-generated code. ****************)
(* Claude Opus 4.7 (1M context, xhigh effort, v2.1.111) *)
  intros HM Hwf.
  rewrite /close_trace.
  destruct (unpaired_operations ts m) as [[up upop] ump_init] eqn:Hops.
  destruct (complete_trace_add_match upop m ump_init) as [nm1 ump'] eqn:Hmatch.
  simpl.
  set (U := list_difference upop (m ++ nm1).*2).
  set (ts_mid := filter (λ x : positive * trace, x.1 ∉ U) ts).
  exists ts_mid. split.
  { eexists. reflexivity. }
  (* Helper: τ ∈ U ⊆ unpaired_pops, so τ ∈ ts.*1 with Call Pop and no Ret Pop *)
  assert (HU_unp : ∀ τ, τ ∈ U → τ ∈ upop).
  { intros τ Hin. by apply list_elem_of_difference in Hin as [? _]. }
  assert (Hl1_eq : upop = list_difference (filter (is_call_pop ∘ snd) ts).*1
                                       (filter (is_ret_pop ∘ snd) ts).*1).
  { rewrite /unpaired_operations in Hops. by injection Hops as _ <- _. }
  (* Each τ ∈ U has Call Pop in ts and no Ret Pop in ts *)
  assert (HU_call : ∀ τ, τ ∈ U → (τ, Call Pop #()) ∈ ts).
  { intros τ Hin.
    apply HU_unp in Hin. rewrite Hl1_eq in Hin.
    apply list_elem_of_difference in Hin as [Hcall _].
    apply list_elem_of_fmap_1 in Hcall as ([τ' ev] & Heq & Hin').
    simpl in Heq. subst τ'.
    apply list_elem_of_filter in Hin' as [Hpop Hin_ts].
    rewrite /is_call_pop /= in Hpop. by rewrite Hpop in Hin_ts. }
  assert (HU_no_ret : ∀ τ, τ ∈ U → τ ∉ (filter (is_ret_pop ∘ snd) ts).*1).
  { intros τ Hin.
    apply HU_unp in Hin. rewrite Hl1_eq in Hin.
    by apply list_elem_of_difference in Hin as [_ ?]. }
  (* Filter (tag = τ) ts = [(τ, Call Pop)] for τ ∈ U, by wellformedness *)
  assert (Hfilt_τ : ∀ τ, τ ∈ U →
            filter (λ x : positive * trace, x.1 = τ) ts
            = [(τ, Call Pop #())]).
  { intros τ Hin.
    pose proof (HU_call τ Hin) as Hcall.
    pose proof (HU_no_ret τ Hin) as Hno_ret.
    assert (Hin_filt : (τ, Call Pop #())
                       ∈ filter (λ x, x.1 = τ) ts)
      by (apply list_elem_of_filter; done).
    destruct (Hwf τ) as [(? & _ & Hpfx)|(r & _ & Hpfx)].
    - exfalso.
      pose proof (elem_of_prefix _ _ _ Hin_filt Hpfx) as Hp.
      rewrite !elem_of_cons elem_of_nil right_id in Hp.
      destruct Hp as [Hp|Hp]; apply (f_equal snd) in Hp; simpl in Hp; discriminate.
    - destruct (filter (λ x, x.1 = τ) ts) as [|x [|y ys]] eqn:Hfilt_eq;
        first by set_solver.
      + pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as ->. done.
      + exfalso. apply Hno_ret.
        apply prefix_cons_inv_2 in Hpfx.
        pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx) as ->.
        apply (list_elem_of_fmap_2 fst _ (τ, Ret (encode_response r))).
        apply list_elem_of_filter_2; first by (eexists; done).
        assert (H' : (τ, Ret (encode_response r))
                     ∈ filter (λ x, x.1 = τ) ts)
          by (rewrite Hfilt_eq; clear; set_solver).
        by apply list_elem_of_filter in H' as [_ ?]. }
  (* events_of_trace ts_mid = {τ ∈ ts.*1 | τ ∉ U} *)
  assert (Hev_eq : ∀ τ, τ ∈ events_of_trace ts_mid ↔ τ ∈ ts.*1 ∧ τ ∉ U).
  { intros τ. split.
    - intros Hin. apply elem_of_list_to_set, list_elem_of_fmap_1 in Hin
        as ([τ' t'] & -> & Hin_mid).
      rewrite /ts_mid in Hin_mid.
      apply list_elem_of_filter in Hin_mid as [Hni Hin_ts]. simpl in Hni.
      split; last exact Hni.
      apply (list_elem_of_fmap_2 fst _ (τ', t')). exact Hin_ts.
    - intros [Hin Hni].
      apply elem_of_list_to_set.
      apply list_elem_of_fmap_1 in Hin as ([τ' t'] & -> & Hin_ts).
      apply (list_elem_of_fmap_2 fst _ (τ', t')).
      rewrite /ts_mid. apply list_elem_of_filter_2; done. }
  (* Show is_adding_call. *)
  split_and!.
  - (* ts_mid = filter (∈ events_of_trace ts_mid) ts *)
    rewrite /ts_mid. apply list_filter_ext.
    intros [τ' t'] Hin_ts. simpl. rewrite Hev_eq.
    assert (Hin' : τ' ∈ ts.*1)
      by (apply (list_elem_of_fmap_2 fst _ (τ', t')); exact Hin_ts).
    naive_solver.
  - (* Forall valid_call on removed events *)
    apply Forall_forall. intros [τ' t'] Hin_filt.
    apply list_elem_of_filter in Hin_filt as [Hni Hin_ts].
    simpl in Hni. rewrite Hev_eq in Hni.
    apply not_and_l in Hni as [Habs|Hin_U].
    { exfalso. apply Habs.
      apply (list_elem_of_fmap_2 fst _ (τ', t')). exact Hin_ts. }
    { (* τ' ∈ U *)
      apply dec_stable in Hin_U.
      pose proof (Hfilt_τ τ' Hin_U) as Heq.
      assert (Hin' : (τ', t') ∈ filter (λ x, x.1 = τ') ts)
        by (apply list_elem_of_filter_2; done).
      rewrite Heq in Hin'.
      apply elem_of_cons in Hin' as [Heq'|Habs];
        last by apply not_elem_of_nil in Habs.
      injection Heq' as Ht'. subst t'.
      rewrite HM /=. done. }
  - (* NoDup tags of removed events: each tag is in U (NoDup) and appears
       exactly once via Hfilt_τ. *)
    (* The set of tags τ with x.1 ∉ events_of_trace ts_mid for some x ∈ ts is U. *)
    assert (Hfilt_eq :
      filter (λ x : positive * trace, x.1 ∉ events_of_trace ts_mid) ts
      = filter (λ x : positive * trace, x.1 ∈ U) ts).
    { apply list_filter_ext. intros [τ' t'] Hin_ts. simpl. rewrite Hev_eq.
      assert (Hin' : τ' ∈ ts.*1)
        by (apply (list_elem_of_fmap_2 fst _ (τ', t')); exact Hin_ts).
      split.
      - intros Hni. apply not_and_l in Hni as [Habs|H_U]; first done.
        by apply dec_stable.
      - intros HU [_ Hni]. by apply Hni. }
    rewrite Hfilt_eq.
    (* Direct induction on ts using Hfilt_τ, generalizing U. *)
    clear -Hfilt_τ U. clearbody U.
    revert U Hfilt_τ.
    induction ts as [|[τ' t'] rest IH]; intros U Hfilt_τ;
      first by (rewrite filter_nil fmap_nil; constructor).
    destruct (decide (τ' ∈ U)) as [Hin|Hni].
    + rewrite filter_cons_True //. rewrite fmap_cons. apply NoDup_cons. split.
      * (* τ' ∉ filter rest: by Hfilt_τ, τ' has only one event in (τ',t')::rest *)
        pose proof (Hfilt_τ τ' Hin) as Heq.
        rewrite filter_cons_True // in Heq. injection Heq as _ Hfilt_rest_nil.
        intros Hin_filt.
        apply list_elem_of_fmap_1 in Hin_filt as ([τ_x t_x] & Heq_τ & Hin_rest).
        simpl in Heq_τ. subst τ_x.
        apply list_elem_of_filter in Hin_rest as [_ Hin_rest_ts].
        assert (Habs : (τ', t_x) ∈ filter (λ x, x.1 = τ') rest)
          by (apply list_elem_of_filter_2; done).
        rewrite Hfilt_rest_nil in Habs. by apply not_elem_of_nil in Habs.
      * (* Rest has no τ' events, so filter (∈ U) rest = filter (∈ U\{τ'}) rest. *)
        pose proof (Hfilt_τ τ' Hin) as Heq_full.
        rewrite filter_cons_True // in Heq_full.
        injection Heq_full as _ Hfilt_rest_nil.
        assert (Hτ'_no_in_rest : ∀ x, x ∈ rest → x.1 ≠ τ').
        { intros [τ_x t_x] Hx Heq_τ. simpl in Heq_τ. subst τ_x.
          assert (Habs : (τ', t_x) ∈ filter (λ x, x.1 = τ') rest)
            by (apply list_elem_of_filter_2; done).
          rewrite Hfilt_rest_nil in Habs. by apply not_elem_of_nil in Habs. }
        assert (Heq_filt :
          filter (λ x : positive * trace, x.1 ∈ U) rest
          = filter (λ x : positive * trace, x.1 ∈ filter (λ τ, τ ≠ τ') U) rest).
        { apply list_filter_ext. intros x Hx. simpl.
          rewrite list_elem_of_filter.
          pose proof (Hτ'_no_in_rest _ Hx) as Hne. naive_solver. }
        rewrite Heq_filt.
        apply (IH (filter (λ τ, τ ≠ τ') U)).
        intros τ Hin_τ.
        apply list_elem_of_filter in Hin_τ as [Hne_τ Hin_τ_U].
        pose proof (Hfilt_τ τ Hin_τ_U) as Heq.
        rewrite filter_cons_False in Heq; last (simpl; auto). exact Heq.
    + rewrite filter_cons_False //.
      apply (IH U). intros τ Hin_τ.
      pose proof (Hfilt_τ τ Hin_τ) as Heq.
      rewrite filter_cons in Heq.
      destruct (decide ((τ', t').1 = τ)) as [Hsame|Hdiff]; last exact Heq.
      simpl in Hsame. subst τ'.
      exfalso. by apply Hni.
(**************** End LLM-generated code. *****************)
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

(* Helper: entries in complete_trace_add_push *)
Local Lemma complete_trace_add_push_elem τ t up :
  (τ, t) ∈ complete_trace_add_push up ↔ t = Ret #() ∧ τ ∈ up.
Proof.
  rewrite /complete_trace_add_push list_elem_of_fmap. split.
  - intros (τ' & Heq & Hin). injection Heq as <- ->. done.
  - intros [-> Hin]. exists τ. done.
Qed.

(* Helper: entries in complete_trace_remove_pop are Ret events for tags in upop *)
Local Lemma complete_trace_remove_pop_elem τ t upop calls m0 :
  (τ, t) ∈ complete_trace_remove_pop upop calls m0 →
  is_ret t ∧ τ ∈ upop.
Proof.
  rewrite /complete_trace_remove_pop list_elem_of_omap.
  intros (τ2 & Hin & Heq).
  destruct (find _ m0) as [[τ1 ?]|] eqn:Hfind; last done.
  injection Heq as Hτ Ht. subst τ t.
  split; [eexists; reflexivity|exact Hin].
Qed.

(* Helper: entries in close_trace_add_pop *)
Local Lemma close_trace_add_pop_elem τ t calls m_add :
  (τ, t) ∈ close_trace_add_pop calls m_add →
  ∃ τ1, (τ1, τ) ∈ m_add.
Proof.
  rewrite /close_trace_add_pop.
  intros [Hin|Hin]%elem_of_app.
  - apply list_elem_of_fmap in Hin as ([τ1' τ2'] & Heq & Hin_m).
    injection Heq as -> ->. eexists. exact Hin_m.
  - apply list_elem_of_fmap in Hin as ([τ1' τ2'] & Heq & Hin_m).
    injection Heq as -> ->. eexists. exact Hin_m.
Qed.

(* Helper: tags in close_trace_add_match are fresh *)
Local Lemma close_trace_add_match_tags_fresh τ1 τ2 ump next :
  (τ1, τ2) ∈ close_trace_add_match ump next →
  (next ≤ τ2)%positive.
Proof.
  revert next. induction ump as [|τ1' ump IH]; first by set_solver.
  intros next. simpl.
  intros [Heq|Hin]%elem_of_cons.
  - injection Heq as -> ->. lia.
  - specialize (IH (next + 1)%positive Hin). lia.
Qed.

(* Helper: tags in close_trace_add_pop have fresh tags *)
Local Lemma close_trace_add_pop_fresh_tag τ t calls ump next :
  (τ, t) ∈ close_trace_add_pop calls (close_trace_add_match ump next) →
  (next ≤ τ)%positive.
Proof.
  intros Hin.
  apply close_trace_add_pop_elem in Hin as [τ1 Hin].
  eapply close_trace_add_match_tags_fresh. exact Hin.
Qed.

(* Helper: NoDup of close_trace_add_match.*2 (uses fresh tag property). *)
Local Lemma close_trace_add_match_snd_nodup ump next :
  NoDup (close_trace_add_match ump next).*2.
Proof.
  revert next. induction ump as [|τ1 ump IH]; first by constructor.
  intros next. simpl. apply NoDup_cons. split.
  - intros Hin.
    apply list_elem_of_fmap_1 in Hin as ([τ1' τ2'] & Heq & Hin).
    simpl in Heq. subst τ2'.
    apply close_trace_add_match_tags_fresh in Hin. lia.
  - exact (IH (next + 1)%positive).
Qed.

(* Helper: foldl Pos.max accumulator is a lower bound *)
Local Lemma foldl_max_acc_le (acc : positive) l :
  (acc ≤ foldl Pos.max acc l)%positive.
Proof.
  revert acc. induction l as [|x l IH]; simpl; intros acc.
  - lia.
  - transitivity (Pos.max acc x)%positive; [lia|exact (IH _)].
Qed.

(* Helper: every element ≤ foldl Pos.max *)
Local Lemma foldl_max_elem_le τ (acc : positive) l :
  τ ∈ l → (τ ≤ foldl Pos.max acc l)%positive.
Proof.
  revert acc. induction l as [|x l IH]; first by set_solver.
  intros acc [->|Hin]%elem_of_cons; simpl.
  - transitivity (Pos.max acc x)%positive; [lia|exact (foldl_max_acc_le _ _)].
  - exact (IH _ Hin).
Qed.

(* Helper: max_tag is an upper bound *)
Local Lemma max_tag_upper_bound τ l :
  τ ∈ l → (τ ≤ max_tag l)%positive.
Proof. rewrite /max_tag. apply foldl_max_elem_le. Qed.

(* Helper: tag in ts implies tag ≤ max_tag *)
Local Lemma tag_in_ts_le_max_tag (ts0 : list (positive * trace)) τ ev :
  (τ, ev) ∈ ts0 → (τ ≤ max_tag ts0.*1)%positive.
Proof.
  intros Hin.
  apply max_tag_upper_bound.
  apply (list_elem_of_fmap_2 fst _ (τ, ev)). exact Hin.
Qed.

(* Helper: filter of np for non-member is empty *)
Local Lemma filter_np_not_in τ up :
  τ ∉ up →
  filter (λ x : positive * trace, x.1 = τ) (complete_trace_add_push up) = [].
Proof.
  intros Hnotin. apply filter_False_nil, Forall_forall.
  intros [τ' t'] Hin. simpl. intros ->.
  apply complete_trace_add_push_elem in Hin as [_ ?]. done.
Qed.

(* Helper: filter of npop1 for non-member is empty *)
Local Lemma filter_npop1_not_in τ upop calls m0 :
  τ ∉ upop →
  filter (λ x : positive * trace, x.1 = τ) (complete_trace_remove_pop upop calls m0) = [].
Proof.
  intros Hnotin. apply filter_False_nil, Forall_forall.
  intros [τ' t'] Hin. simpl. intros ->.
  apply complete_trace_remove_pop_elem in Hin as [_ ?]. done.
Qed.

(* Helper: filter of npop2 for old tag is empty *)
Local Lemma filter_npop2_old_tag τ (ev : trace) (ts0 : list (positive * trace)) ump calls next :
  (τ, ev) ∈ ts0 →
  next = (max_tag ts0.*1 + 1)%positive →
  filter (λ x : positive * trace, x.1 = τ) (close_trace_add_pop calls (close_trace_add_match ump next)) = [].
Proof.
  intros Hin_ts Hnext. apply filter_False_nil, Forall_forall.
  intros [τ' t'] Hin'. simpl. intros ->.
  pose proof (close_trace_add_pop_fresh_tag _ _ _ _ _ Hin').
  pose proof (tag_in_ts_le_max_tag _ _ _ Hin_ts).
  lia.
Qed.

(* Helper: complete_trace_add_match preserves: nm1.*2 ⊆ upop *)
Local Lemma complete_trace_add_match_snd_sub upop m0 ump :
  (complete_trace_add_match upop m0 ump).1.*2 ⊆ upop.
Proof.
  revert ump. induction upop as [|τ2 upop IH]; first by set_solver.
  intros ump. simpl.
  destruct (find _ m0) as [?|].
  - intros x Hx. apply elem_of_cons. right. exact (IH ump x Hx).
  - destruct ump as [|τ1 ump'].
    + intros x Hx. apply elem_of_cons. right. exact (IH [] x Hx).
    + destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
      simpl. intros x [->|Hx]%elem_of_cons.
      * set_solver.
      * apply elem_of_cons. right.
        assert (Hx' : x ∈ (complete_trace_add_match upop m0 ump').1.*2)
          by (rewrite Hrec; exact Hx).
        exact (IH ump' x Hx').
Qed.

(* Helper: complete_trace_add_match preserves: nm1.*1 ⊆ ump *)
Local Lemma complete_trace_add_match_fst_sub upop m0 ump :
  (complete_trace_add_match upop m0 ump).1.*1 ⊆ ump.
Proof.
  revert ump. induction upop as [|τ2 upop IH]; first by set_solver.
  intros ump. simpl.
  destruct (find _ m0) as [?|].
  - exact (IH ump).
  - destruct ump as [|τ1 ump'].
    + exact (IH []).
    + destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
      simpl. intros x [->|Hx]%elem_of_cons.
      * set_solver.
      * apply elem_of_cons. right.
        assert (Hx' : x ∈ (complete_trace_add_match upop m0 ump').1.*1)
          by (rewrite Hrec; exact Hx).
        exact (IH ump' x Hx').
Qed.

(* Helper: remaining ump is subset of original *)
Local Lemma complete_trace_add_match_remaining_sub upop m0 ump :
  (complete_trace_add_match upop m0 ump).2 ⊆ ump.
Proof.
  revert ump. induction upop as [|τ2 upop IH]; first done.
  intros ump. simpl.
  destruct (find _ m0) as [?|].
  - exact (IH ump).
  - destruct ump as [|τ1 ump'].
    + exact (IH []).
    + destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
      simpl. etrans.
      { assert (H : (complete_trace_add_match upop m0 ump').2 ⊆ ump')
          by exact (IH ump').
        rewrite Hrec in H. exact H. }
      set_solver.
Qed.

(* Helper: nm1.*1 forms a prefix of ump_init, with ump' as the suffix.
   I.e., ump = nm1.*1 ++ ump'. *)
Local Lemma complete_trace_add_match_split upop m0 ump :
  ump = (complete_trace_add_match upop m0 ump).1.*1
        ++ (complete_trace_add_match upop m0 ump).2.
Proof.
  revert ump. induction upop as [|τ2 upop IH]; first done.
  intros ump. simpl.
  destruct (find _ m0) as [?|].
  - exact (IH ump).
  - destruct ump as [|τ1 ump'].
    + by rewrite (IH []).
    + destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
      simpl. f_equal.
      assert (H : ump' = (complete_trace_add_match upop m0 ump').1.*1
                          ++ (complete_trace_add_match upop m0 ump').2)
        by exact (IH ump').
      rewrite Hrec /= in H. exact H.
Qed.

(* Helper: ump is covered by nm1.*1 and ump' *)
Local Lemma complete_trace_add_match_cover upop m0 ump τ :
  τ ∈ ump →
  τ ∈ (complete_trace_add_match upop m0 ump).1.*1
  ∨ τ ∈ (complete_trace_add_match upop m0 ump).2.
Proof.
  revert ump. induction upop as [|τ2 upop IH]; first by (intros; right).
  intros ump Hin. simpl.
  destruct (find _ m0) as [?|].
  - exact (IH ump Hin).
  - destruct ump as [|τ1 ump'].
    + by set_solver.
    + destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
      simpl.
      apply elem_of_cons in Hin as [->|Hin].
      * left. set_solver.
      * destruct (IH ump' Hin) as [Hl|Hr].
        { left. rewrite Hrec /= in Hl. set_solver. }
        { right. rewrite Hrec /= in Hr. exact Hr. }
Qed.

(* Helper: close_trace_add_match fst side *)
Local Lemma close_trace_add_match_fst ump next :
  (close_trace_add_match ump next).*1 = ump.
Proof.
  revert next. induction ump as [|τ1 ump IH]; first done.
  intros next. simpl. f_equal. exact (IH (next + 1)%positive).
Qed.

(* Helper: lookup in close_trace_add_match. The i-th pair has first component
   ump !! i and some second component. *)
Local Lemma close_trace_add_match_lookup ump next i τ :
  ump !! i = Some τ →
  ∃ τ', close_trace_add_match ump next !! i = Some (τ, τ').
Proof.
  revert next i. induction ump as [|τ1 ump IH]; first by intros ? i; rewrite lookup_nil.
  intros next [|i] Hlk; simpl in Hlk.
  - injection Hlk as ->. simpl. by eexists.
  - simpl. exact (IH _ i Hlk).
Qed.

(* Helper: pair lookup in close_trace_add_match implies fst is in ump at same index. *)
Local Lemma close_trace_add_match_lookup_inv ump next i τ τ' :
  close_trace_add_match ump next !! i = Some (τ, τ') →
  ump !! i = Some τ.
Proof.
  revert next i. induction ump as [|τ1 ump IH]; first by intros ? i; rewrite lookup_nil.
  intros next [|i] Hlk; simpl in Hlk.
  - injection Hlk as -> ->. done.
  - simpl. exact (IH _ i Hlk).
Qed.

(* Helper: lookup of Call in close_trace_add_pop at index i (for i < length m_add). *)
Local Lemma close_trace_add_pop_lookup_call calls m_add i τ1 τ2 :
  m_add !! i = Some (τ1, τ2) →
  close_trace_add_pop calls m_add !! i = Some (τ2, Call Pop #()).
Proof.
  intros Hlk. rewrite /close_trace_add_pop.
  rewrite lookup_app_l; last (rewrite length_fmap; by eapply lookup_lt_Some).
  rewrite list_lookup_fmap Hlk //.
Qed.

(* Helper: lookup of Ret in close_trace_add_pop at index length m_add + i. *)
Local Lemma close_trace_add_pop_lookup_ret calls m_add i τ1 τ2 :
  m_add !! i = Some (τ1, τ2) →
  close_trace_add_pop calls m_add !! (length m_add + i) = Some (τ2, Ret (ret_val_of_call (calls !!! τ1))).
Proof.
  intros Hlk. rewrite /close_trace_add_pop.
  rewrite lookup_app_r; last (rewrite length_fmap; lia).
  rewrite length_fmap.
  replace (length m_add + i - length m_add) with i by lia.
  rewrite list_lookup_fmap Hlk //.
Qed.

(* Helper: length of close_trace_add_pop is 2 * length of m_add. *)
Local Lemma close_trace_add_pop_length calls m_add :
  length (close_trace_add_pop calls m_add) = 2 * length m_add.
Proof.
  rewrite /close_trace_add_pop length_app !length_fmap. lia.
Qed.

(* Helper: lookup of any entry in close_trace_add_pop.
   In the new layout, positions [0, length m_add) carry Call events
   and positions [length m_add, 2 * length m_add) carry Ret events. *)
Local Lemma close_trace_add_pop_lookup_inv calls m_add p τ ev :
  close_trace_add_pop calls m_add !! p = Some (τ, ev) →
  ∃ k τ1, m_add !! k = Some (τ1, τ) ∧
          ((p = k ∧ ev = Call Pop #()) ∨
           (p = length m_add + k ∧ ev = Ret (ret_val_of_call (calls !!! τ1)))).
Proof.
  intros Hlk. rewrite /close_trace_add_pop in Hlk.
  rewrite lookup_app_Some in Hlk.
  destruct Hlk as [Hlk | [Hge Hlk]].
  - (* Calls section *)
    rewrite list_lookup_fmap fmap_Some in Hlk.
    destruct Hlk as ([τ1' τ2'] & Hm_lk & Heq).
    injection Heq as -> ->.
    exists p, τ1'. split; first done. left. done.
  - (* Rets section *)
    rewrite length_fmap in Hge.
    rewrite length_fmap in Hlk.
    rewrite list_lookup_fmap fmap_Some in Hlk.
    destruct Hlk as ([τ1' τ2'] & Hm_lk & Heq).
    injection Heq as -> ->.
    exists (p - length m_add), τ1'. split; first done.
    right. split; [lia|done].
Qed.

(* Helper: a tag with Call event in close_trace_add_pop is at position k < length m_add. *)
Local Lemma close_trace_add_pop_call_pos_unique calls m_add p τ :
  NoDup m_add.*2 →
  close_trace_add_pop calls m_add !! p = Some (τ, Call Pop #()) →
  ∃ k τ1, m_add !! k = Some (τ1, τ) ∧ p = k.
Proof.
  intros Hnd Hlk.
  apply close_trace_add_pop_lookup_inv in Hlk
    as (k & τ1 & Hm_lk & [[Hp_eq _]|[_ Habs]]).
  - exists k, τ1. by split.
  - discriminate.
Qed.

(* Helper: a tag with Ret event in close_trace_add_pop is at position length m_add + k. *)
Local Lemma close_trace_add_pop_ret_pos_unique calls m_add p τ r :
  close_trace_add_pop calls m_add !! p = Some (τ, Ret r) →
  ∃ k τ1, m_add !! k = Some (τ1, τ) ∧ p = length m_add + k ∧ r = ret_val_of_call (calls !!! τ1).
Proof.
  intros Hlk.
  apply close_trace_add_pop_lookup_inv in Hlk
    as (k & τ1 & Hm_lk & [[_ Habs]|[Hp_eq Hev_eq]]).
  - discriminate.
  - exists k, τ1. injection Hev_eq as ->. by split_and!.
Qed.

(* Helper: entries in close_trace_add_match *)
Local Lemma close_trace_add_match_elem τ1 τ2 ump next :
  (τ1, τ2) ∈ close_trace_add_match ump next →
  τ1 ∈ ump.
Proof.
  revert next. induction ump as [|τ1' ump IH]; first by set_solver.
  intros next [Heq|Hin]%elem_of_cons.
  - injection Heq as -> ->. set_solver.
  - apply elem_of_cons. right. exact (IH _ Hin).
Qed.

(* Helper: filter of np for a member gives exactly one Ret *)
Local Lemma filter_np_in τ up :
  NoDup up →
  τ ∈ up →
  filter (λ x : positive * trace, x.1 = τ) (complete_trace_add_push up) = [(τ, Ret #())].
Proof.
  intros Hnd Hin.
  induction up as [|τ' up IH]; first by set_solver.
  apply NoDup_cons in Hnd as [Hnotin Hnd].
  apply elem_of_cons in Hin as [->|Hin].
  - simpl. rewrite filter_cons_True; last done.
    rewrite filter_np_not_in; first done.
    done.
  - simpl. rewrite filter_cons_False.
    + exact (IH Hnd Hin).
    + simpl. intros ->. done.
Qed.

(* Helper: filter of npop1 for a matched member gives exactly one Ret *)
Local Lemma filter_npop1_in τ upop calls m0 :
  NoDup upop →
  τ ∈ upop →
  (∃ τ1 z, find (λ x : positive * positive, bool_decide (x.2 = τ)) m0 = Some (τ1, z)) →
  ∃ v, filter (λ x : positive * trace, x.1 = τ) (complete_trace_remove_pop upop calls m0) = [(τ, Ret v)].
Proof.
  intros Hnd Hin Hmatched.
  induction upop as [|τ' upop IH]; first by set_solver.
  apply NoDup_cons in Hnd as [Hnotin Hnd].
  rewrite /complete_trace_remove_pop /=.
  apply elem_of_cons in Hin as [->|Hin].
  - destruct Hmatched as (τ1 & z & Hfind). rewrite Hfind /=.
    rewrite filter_cons_True; last done.
    rewrite filter_npop1_not_in; first by eexists.
    done.
  - destruct (find (λ x : positive * positive, bool_decide (x.2 = τ')) m0)
      as [[τ1 ?]|] eqn:Hfind'; simpl.
    + rewrite filter_cons_False.
      * exact (IH Hnd Hin).
      * simpl. intros ->. done.
    + exact (IH Hnd Hin).
Qed.

(* Strengthened version: filter is exactly [(τ, Ret (ret_val_of_call (calls !!! τ1)))] when find returns (τ1, τ). *)
Local Lemma filter_npop1_in_exact τ τ1 upop calls m0 :
  NoDup upop →
  τ ∈ upop →
  find (λ x : positive * positive, bool_decide (x.2 = τ)) m0 = Some (τ1, τ) →
  filter (λ x : positive * trace, x.1 = τ) (complete_trace_remove_pop upop calls m0)
    = [(τ, Ret (ret_val_of_call (calls !!! τ1)))].
Proof.
  intros Hnd Hin Hfind.
  induction upop as [|τ' upop_rest IH]; first by set_solver.
  apply NoDup_cons in Hnd as [Hnotin Hnd].
  rewrite /complete_trace_remove_pop /=.
  apply elem_of_cons in Hin as [->|Hin_rest].
  - rewrite Hfind /=.
    rewrite filter_cons_True //=.
    rewrite filter_npop1_not_in; first done.
    done.
  - destruct (find (λ x : positive * positive, bool_decide (x.2 = τ')) m0)
      as [[τ1' τ2']|] eqn:Hfind'; simpl.
    + rewrite filter_cons_False.
      * exact (IH Hnd Hin_rest).
      * simpl. intros ->.
        apply find_some in Hfind' as [_ Hbd].
        apply bool_decide_eq_true_1 in Hbd. simpl in Hbd. subst τ2'.
        apply Hnotin. exact Hin_rest.
    + exact (IH Hnd Hin_rest).
Qed.

(* Helper: filter of npop1 for an unmatched tag is empty *)
Local Lemma filter_npop1_in_unmatched τ upop calls m0 :
  find (λ x : positive * positive, bool_decide (x.2 = τ)) m0 = None →
  filter (λ x : positive * trace, x.1 = τ) (complete_trace_remove_pop upop calls m0) = [].
Proof.
  intros Hnone.
  induction upop as [|τ' upop IH]; first done.
  rewrite /complete_trace_remove_pop /=.
  destruct (find (λ x : positive * positive, bool_decide (x.2 = τ')) m0)
    as [[τ1 ?]|] eqn:Hfind'; simpl.
  - destruct (decide (τ' = τ)) as [->|Hne].
    + rewrite Hfind' in Hnone. discriminate.
    + rewrite filter_cons_False; last (simpl; congruence). exact IH.
  - exact IH.
Qed.

(* Helper: if x satisfies P and appears at most once in l,
   then it appears at most once in filter P l *)
Local Lemma count_occ_filter_le {A} `{EqDecision A}
    (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) (x : A) :
  P x →
  (∀ i j, l !! i = Some x → l !! j = Some x → i = j) →
  (∀ i j, filter P l !! i = Some x → filter P l !! j = Some x → i = j).
Proof.
  intros Hpx Huniq i j Hi Hj.
  (* Both filter P l !! i = Some x and !! j = Some x *)
  (* x ∈ filter P l means x ∈ l *)
  (* Since x appears at most once in l and filter is a sublist,
     x appears at most once in filter P l *)
  (* Use induction on l tracking i and j *)
  revert i j Hi Hj. revert Huniq.
  induction l as [|a l IH]; intros Huniq i j Hi Hj.
  - rewrite filter_nil in Hi. destruct i; discriminate.
  - destruct (decide (P a)).
    + rewrite filter_cons_True in Hi, Hj; [|done..].
      destruct i as [|i], j as [|j]; simpl in Hi, Hj.
      * done.
      * injection Hi as Heqa. subst a.
        assert (Hin_j : x ∈ filter P l) by (eapply list_elem_of_lookup_2; exact Hj).
        apply list_elem_of_filter in Hin_j as [_ Hin_j].
        apply list_elem_of_lookup_1 in Hin_j as [k Hk].
        assert (H0k : 0 = Datatypes.S k) by (apply Huniq; [done|exact Hk]).
        lia.
      * injection Hj as Heqa. subst a.
        assert (Hin_i : x ∈ filter P l) by (eapply list_elem_of_lookup_2; exact Hi).
        apply list_elem_of_filter in Hin_i as [_ Hin_i].
        apply list_elem_of_lookup_1 in Hin_i as [k Hk].
        assert (H0k : 0 = Datatypes.S k) by (apply Huniq; [done|exact Hk]).
        lia.
      * f_equal.
        assert (Huniq' : ∀ i0 j0 : nat, l !! i0 = Some x → l !! j0 = Some x → i0 = j0).
        { intros i0 j0 Hi0 Hj0.
          assert (Datatypes.S i0 = Datatypes.S j0) by (apply Huniq; [exact Hi0|exact Hj0]).
          lia. }
        exact (IH Huniq' i j Hi Hj).
    + rewrite filter_cons_False in Hi, Hj; [|done..].
      assert (Huniq' : ∀ i0 j0 : nat, l !! i0 = Some x → l !! j0 = Some x → i0 = j0).
      { intros i0 j0 Hi0 Hj0.
        assert (Datatypes.S i0 = Datatypes.S j0) by (apply Huniq; [exact Hi0|exact Hj0]).
        lia. }
      exact (IH Huniq' i j Hi Hj).
Qed.

(* Helper: NoDup of call_push/call_pop tag projections under wellformedness. *)
Local Lemma call_push_tags_nodup rme valid_value ts0 :
  per_tag_wellformed_bag rme valid_value ts0 →
  NoDup (filter (is_call_push ∘ snd) ts0).*1.
Proof.
  intros Hwf.
  apply NoDup_alt.
  intros i j τ0.
  rewrite !list_lookup_fmap.
  intros Hi Hj.
  destruct (filter (is_call_push ∘ snd) ts0 !! i) as [[τi ti]|] eqn:Hfi; simpl in Hi; [|discriminate].
  destruct (filter (is_call_push ∘ snd) ts0 !! j) as [[τj tj]|] eqn:Hfj; simpl in Hj; [|discriminate].
  injection Hi as Heqi. injection Hj as Heqj. subst τi τj.
  (* Both entries are in the filter and in ts0 *)
  assert (Hin_i := list_elem_of_lookup_2 _ _ _ Hfi).
  assert (Hin_j := list_elem_of_lookup_2 _ _ _ Hfj).
  apply list_elem_of_filter in Hin_i as [Hpush_i Hin_i].
  apply list_elem_of_filter in Hin_j as [Hpush_j Hin_j].
  simpl in Hpush_i, Hpush_j.
  destruct Hpush_i as [vi ->]. destruct Hpush_j as [vj ->].
  (* Determine vi = vj = w from wellformedness *)
  destruct (Hwf τ0) as [(w & _ & Hpfx)|(r & _ & Hpfx)].
  - assert (Hin_fi : (τ0, Call Push vi) ∈ filter (λ x, x.1 = τ0) ts0).
    { apply list_elem_of_filter. done. }
    assert (Hin_fj : (τ0, Call Push vj) ∈ filter (λ x, x.1 = τ0) ts0).
    { apply list_elem_of_filter. done. }
    eapply elem_of_prefix in Hin_fi; last exact Hpfx.
    eapply elem_of_prefix in Hin_fj; last exact Hpfx.
    assert (Hvi : vi = w).
    { apply elem_of_cons in Hin_fi as [Heq|Hin]; [|apply elem_of_cons in Hin as [Habs|?]; [discriminate|by set_solver]].
      by simplify_eq. }
    assert (Hvj : vj = w).
    { apply elem_of_cons in Hin_fj as [Heq|Hin]; [|apply elem_of_cons in Hin as [Habs|?]; [discriminate|by set_solver]].
      by simplify_eq. }
    subst vi vj.
    (* Now both filter entries are (τ0, Call Push w). Show they're at the same position. *)
    (* (τ0, Call Push w) appears at most once in filter (tag=τ0) ts0 *)
    assert (Hnd_filt : NoDup (filter (λ x, x.1 = τ0) ts0)).
    { destruct (filter (λ x, x.1 = τ0) ts0) as [|a [|b rest]] eqn:Hfilt_eq.
      - constructor.
      - constructor; [set_solver|constructor].
      - destruct (Hwf τ0) as [(?&_&Hpfx')|(?&_&Hpfx')]; rewrite Hfilt_eq in Hpfx';
        apply prefix_cons_inv_1 in Hpfx' as Ha;
        apply prefix_cons_inv_2, prefix_cons_inv_1 in Hpfx' as Hb;
        apply prefix_cons_inv_2, prefix_nil_inv in Hpfx'; subst rest a b;
        repeat constructor; set_solver. }
    (* (τ0, Call Push w) appears at most once in ts0 *)
    assert (Huniq_ts0 : ∀ i0 j0, ts0 !! i0 = Some (τ0, Call Push w) →
                                   ts0 !! j0 = Some (τ0, Call Push w) → i0 = j0).
    { intros i0 j0 Hi0 Hj0.
      clear -Hi0 Hj0 Hnd_filt.
      revert i0 j0 Hi0 Hj0 Hnd_filt.
      induction ts0 as [|[τ' t'] ts0' IH]; intros i0 j0 Hi0 Hj0 Hnd_filt.
      - destruct i0; discriminate.
      - destruct (decide (τ' = τ0)) as [->|Hne].
        + rewrite filter_cons_True in Hnd_filt; last done.
          apply NoDup_cons in Hnd_filt as [Hnotin Hnd_filt'].
          destruct i0 as [|i0], j0 as [|j0]; simpl in Hi0, Hj0.
          * done.
          * simplify_eq.
            exfalso. apply Hnotin. apply list_elem_of_filter. split; [done|].
            eapply list_elem_of_lookup_2. exact Hj0.
          * simplify_eq.
            exfalso. apply Hnotin. apply list_elem_of_filter. split; [done|].
            eapply list_elem_of_lookup_2. exact Hi0.
          * f_equal. exact (IH i0 j0 Hi0 Hj0 Hnd_filt').
        + rewrite filter_cons_False in Hnd_filt; last (simpl; done).
          destruct i0 as [|i0], j0 as [|j0]; simpl in Hi0, Hj0.
          * done.
          * simplify_eq.
          * simplify_eq.
          * f_equal. exact (IH i0 j0 Hi0 Hj0 Hnd_filt). }
    (* Now use count_occ_filter_le to transfer uniqueness to is_call_push filter *)
    assert (Huniq_filt : ∀ i0 j0,
      filter (is_call_push ∘ snd) ts0 !! i0 = Some (τ0, Call Push w) →
      filter (is_call_push ∘ snd) ts0 !! j0 = Some (τ0, Call Push w) → i0 = j0).
    { apply count_occ_filter_le; [exists w; done|exact Huniq_ts0]. }
    exact (Huniq_filt i j Hfi Hfj).
  - (* pop case: impossible *)
    exfalso.
    assert (Hin_fi : (τ0, Call Push vi) ∈ filter (λ x, x.1 = τ0) ts0).
    { apply list_elem_of_filter. done. }
    eapply elem_of_prefix in Hin_fi; last exact Hpfx.
    apply elem_of_cons in Hin_fi as [Habs|Hin_fi]; [discriminate|].
    apply elem_of_cons in Hin_fi as [Habs|?]; [discriminate|by set_solver].
Qed.

Local Lemma call_pop_tags_nodup rme valid_value ts0 :
  per_tag_wellformed_bag rme valid_value ts0 →
  NoDup (filter (is_call_pop ∘ snd) ts0).*1.
Proof.
  intros Hwf.
  apply NoDup_alt.
  intros i j τ0.
  rewrite !list_lookup_fmap.
  intros Hi Hj.
  destruct (filter (is_call_pop ∘ snd) ts0 !! i) as [[τi ti]|] eqn:Hfi; simpl in Hi; [|discriminate].
  destruct (filter (is_call_pop ∘ snd) ts0 !! j) as [[τj tj]|] eqn:Hfj; simpl in Hj; [|discriminate].
  injection Hi as Heqi. injection Hj as Heqj. subst τi τj.
  assert (Hin_i := list_elem_of_lookup_2 _ _ _ Hfi).
  assert (Hin_j := list_elem_of_lookup_2 _ _ _ Hfj).
  apply list_elem_of_filter in Hin_i as [Hpop_i Hin_i].
  apply list_elem_of_filter in Hin_j as [Hpop_j Hin_j].
  rewrite /is_call_pop /= in Hpop_i. rewrite /is_call_pop /= in Hpop_j. subst ti tj.
  (* Both are (τ0, Call Pop). Show uniqueness in ts0. *)
  destruct (Hwf τ0) as [(w & _ & Hpfx)|(r & Hpfx)].
  - (* push case: impossible *)
    exfalso.
    assert (Hin_fi : (τ0, Call Pop #()) ∈ filter (λ x, x.1 = τ0) ts0).
    { apply list_elem_of_filter. done. }
    eapply elem_of_prefix in Hin_fi; last exact Hpfx.
    apply elem_of_cons in Hin_fi as [Habs|Hin_fi]; [discriminate|].
    apply elem_of_cons in Hin_fi as [Habs|?]; [discriminate|by set_solver].
  - (* pop case *)
    assert (Hnd_filt : NoDup (filter (λ x, x.1 = τ0) ts0)).
    { destruct (filter (λ x, x.1 = τ0) ts0) as [|a [|b rest]] eqn:Hfilt_eq.
      - constructor.
      - constructor; [set_solver|constructor].
      - destruct (Hwf τ0) as [(?&_&Hpfx')|(?&_&Hpfx')]; rewrite Hfilt_eq in Hpfx';
        apply prefix_cons_inv_1 in Hpfx' as Ha;
        apply prefix_cons_inv_2, prefix_cons_inv_1 in Hpfx' as Hb;
        apply prefix_cons_inv_2, prefix_nil_inv in Hpfx'; subst rest a b;
        repeat constructor; set_solver. }
    assert (Huniq_ts0 : ∀ i0 j0, ts0 !! i0 = Some (τ0, Call Pop #()) →
                                   ts0 !! j0 = Some (τ0, Call Pop #()) → i0 = j0).
    { intros i0 j0 Hi0 Hj0.
      clear -Hi0 Hj0 Hnd_filt.
      revert i0 j0 Hi0 Hj0 Hnd_filt.
      induction ts0 as [|[τ' t'] ts0' IH]; intros i0 j0 Hi0 Hj0 Hnd_filt.
      - destruct i0; discriminate.
      - destruct (decide (τ' = τ0)) as [->|Hne].
        + rewrite filter_cons_True in Hnd_filt; last done.
          apply NoDup_cons in Hnd_filt as [Hnotin Hnd_filt'].
          destruct i0 as [|i0], j0 as [|j0]; simpl in Hi0, Hj0.
          * done.
          * simplify_eq.
            exfalso. apply Hnotin. apply list_elem_of_filter. split; [done|].
            eapply list_elem_of_lookup_2. exact Hj0.
          * simplify_eq.
            exfalso. apply Hnotin. apply list_elem_of_filter. split; [done|].
            eapply list_elem_of_lookup_2. exact Hi0.
          * f_equal. exact (IH i0 j0 Hi0 Hj0 Hnd_filt').
        + rewrite filter_cons_False in Hnd_filt; last (simpl; done).
          destruct i0 as [|i0], j0 as [|j0]; simpl in Hi0, Hj0.
          * done.
          * simplify_eq.
          * simplify_eq.
          * f_equal. exact (IH i0 j0 Hi0 Hj0 Hnd_filt). }
    assert (Huniq_filt : ∀ i0 j0,
      filter (is_call_pop ∘ snd) ts0 !! i0 = Some (τ0, Call Pop #()) →
      filter (is_call_pop ∘ snd) ts0 !! j0 = Some (τ0, Call Pop #()) → i0 = j0).
    { apply count_occ_filter_le; [done|exact Huniq_ts0]. }
    exact (Huniq_filt i j Hfi Hfj).
Qed.

(* Helper: NoDup of unpaired operations *)
Local Lemma unpaired_pushes_nodup rme valid_value ts0 m0 :
  per_tag_wellformed_bag rme valid_value ts0 →
  NoDup (unpaired_operations ts0 m0).1.1.
Proof.
  intros Hwf. rewrite /unpaired_operations.
  apply NoDup_list_difference.
  exact (call_push_tags_nodup _ _ _ Hwf).
Qed.

Local Lemma unpaired_pops_nodup rme valid_value ts0 m0 :
  per_tag_wellformed_bag rme valid_value ts0 →
  NoDup (unpaired_operations ts0 m0).1.2.
Proof.
  intros Hwf. rewrite /unpaired_operations.
  apply NoDup_list_difference.
  exact (call_pop_tags_nodup _ _ _ Hwf).
Qed.

(* Helper: unpaired push tags are push tags *)
Local Lemma unpaired_push_is_push ts0 m0 τ :
  τ ∈ (unpaired_operations ts0 m0).1.1 →
  τ ∈ push_of_trace ts0.
Proof.
  rewrite /unpaired_operations /push_of_trace.
  intros Hin. apply list_elem_of_difference in Hin as [? _]. assumption.
Qed.

(* Helper: unpaired push tags don't have Ret in ts *)
Local Lemma unpaired_push_no_ret ts0 m0 τ :
  τ ∈ (unpaired_operations ts0 m0).1.1 →
  τ ∉ (filter (is_ret_push ∘ snd) ts0).*1.
Proof.
  rewrite /unpaired_operations.
  intros Hin. apply list_elem_of_difference in Hin as [_ ?]. assumption.
Qed.

(* Helper: unpaired pop tags are pop tags *)
Local Lemma unpaired_pop_is_pop ts0 m0 τ :
  τ ∈ (unpaired_operations ts0 m0).1.2 →
  τ ∈ pop_of_trace ts0.
Proof.
  rewrite /unpaired_operations /pop_of_trace.
  intros Hin. apply list_elem_of_difference in Hin as [? _]. assumption.
Qed.

(* Helper: unpaired pop tags don't have Ret in ts *)
Local Lemma unpaired_pop_no_ret ts0 m0 τ :
  τ ∈ (unpaired_operations ts0 m0).1.2 →
  τ ∉ (filter (is_ret_pop ∘ snd) ts0).*1.
Proof.
  rewrite /unpaired_operations.
  intros Hin. apply list_elem_of_difference in Hin as [_ ?]. assumption.
Qed.

(* Helper: for an old tag, filter of npop2 is empty *)
Local Lemma filter_npop2_not_in_ts τ ts0 calls ump next :
  (∃ ev : trace, (τ, ev) ∈ ts0) →
  next = (max_tag ts0.*1 + 1)%positive →
  filter (λ x : positive * trace, x.1 = τ) (close_trace_add_pop calls (close_trace_add_match ump next)) = [].
Proof.
  intros [ev Hin] Hnext.
  exact (filter_npop2_old_tag τ ev ts0 ump calls next Hin Hnext).
Qed.

(* Helper: a tag in per_tag_wellformed_bag with a push Call has filter starting with Call Push *)
Local Lemma wellformed_push_filter_prefix rme valid_value ts0 τ v :
  per_tag_wellformed_bag rme valid_value ts0 →
  (τ, Call Push v) ∈ ts0 →
  filter (λ x : positive * trace, x.1 = τ) ts0 = [(τ, Call Push v)]
  ∨ filter (λ x : positive * trace, x.1 = τ) ts0 = [(τ, Call Push v); (τ, Ret #())].
Proof.
  intros Hwf Hin.
  assert (Hin_filt : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts0).
  { apply list_elem_of_filter. done. }
  destruct (Hwf τ) as [(w & _ & Hpfx)|(r & _ & Hpfx)].
  - assert (Hw : w = v).
    { assert (Hin_target : (τ, Call Push v) ∈
        [(τ, Call Push w); (τ, Ret #())]).
      { eapply elem_of_prefix; eassumption. }
      apply elem_of_cons in Hin_target as [Heq|Hin_target].
      - injection Heq as Heq. rewrite /encode_response in Heq. by simplify_eq.
      - apply elem_of_cons in Hin_target as [Habs|?]; [discriminate|by set_solver]. }
    subst w.
    destruct (filter (λ x, x.1 = τ) ts0) as [|x xs] eqn:Hfilt; first by set_solver.
    apply prefix_cons_inv_1 in Hpfx as Hx.
    destruct xs as [|y ys].
    + left. rewrite Hx //.
    + right.
      pose proof (Hwf τ) as Hwf'.
      destruct Hwf' as [(w & _ & Hpfx')|(r & _ & Hpfx')].
      * rewrite Hfilt in Hpfx'.
        pose proof (prefix_cons_inv_1 _ _ _ _ Hpfx') as Hx'.
        rewrite Hx in Hx'. assert (w = v) as -> by (injection Hx'; rewrite /encode_response; congruence).
        apply prefix_cons_inv_2 in Hpfx'.
        apply prefix_cons_inv_1 in Hpfx' as Hy.
        apply prefix_cons_inv_2, prefix_nil_inv in Hpfx'. subst ys.
        rewrite Hx Hy //.
      * rewrite Hfilt in Hpfx'. apply prefix_cons_inv_1 in Hpfx'.
        rewrite Hx in Hpfx'. discriminate.
  - exfalso.
    eapply elem_of_prefix in Hin_filt; last exact Hpfx.
    apply elem_of_cons in Hin_filt as [Habs|Hin_filt].
    + discriminate.
    + apply elem_of_cons in Hin_filt as [Habs|?]; [discriminate|by set_solver].
Qed.

(* Helper: complete push filter in ts is exactly [Call; Ret] *)
Local Lemma complete_push_filter rme valid_value ts0 m0 τ v :
  per_tag_wellformed_bag rme valid_value ts0 →
  (τ, Call Push v) ∈ ts0 →
  τ ∉ (unpaired_operations ts0 m0).1.1 →
  filter (λ x : positive * trace, x.1 = τ) ts0 = [(τ, Call Push v); (τ, Ret #())].
Proof.
  intros Hwf Hin Hnotin.
  destruct (wellformed_push_filter_prefix _ _ _ _ _ Hwf Hin) as [Heq|Heq]; last exact Heq.
  exfalso. apply Hnotin.
  rewrite /unpaired_operations.
  apply list_elem_of_difference. split.
  - apply (list_elem_of_fmap_2 fst _ (τ, Call Push v)).
    apply list_elem_of_filter. split; [exists v; done|exact Hin].
  - intros Hin_ret.
    apply list_elem_of_fmap_1 in Hin_ret as ([τ' ev] & Heq' & Hin_ret).
    simpl in Heq'. subst τ'.
    apply list_elem_of_filter in Hin_ret as [Hret Hin_ret].
    simpl in Hret. rewrite Hret in Hin_ret.
    assert (Hin_filt : (τ, Ret #()) ∈ filter (λ x, x.1 = τ) ts0).
    { apply list_elem_of_filter. done. }
    rewrite Heq in Hin_filt. apply elem_of_cons in Hin_filt as [Habs|?]; [discriminate|by set_solver].
Qed.

(* Helper: incomplete push filter in ts is exactly [Call] *)
Local Lemma incomplete_push_filter rme valid_value ts0 m0 τ v :
  per_tag_wellformed_bag rme valid_value ts0 →
  (τ, Call Push v) ∈ ts0 →
  τ ∈ (unpaired_operations ts0 m0).1.1 →
  filter (λ x : positive * trace, x.1 = τ) ts0 = [(τ, Call Push v)].
Proof.
  intros Hwf Hin Hup.
  destruct (wellformed_push_filter_prefix _ _ _ _ _ Hwf Hin) as [Heq|Heq].
  - exact Heq.
  - exfalso.
    apply unpaired_push_no_ret in Hup.
    apply Hup.
    assert (Hin_ret : (τ, Ret #()) ∈ ts0).
    { assert (H : (τ, Ret #()) ∈ filter (λ x, x.1 = τ) ts0) by (rewrite Heq; set_solver).
      by apply list_elem_of_filter in H as [_ ?]. }
    apply (list_elem_of_fmap_2 fst _ (τ, Ret #())).
    apply list_elem_of_filter. split; [done|exact Hin_ret].
Qed.

(* Helper: wellformed pop filter *)
Local Lemma wellformed_pop_filter_prefix rme valid_value ts0 τ :
  per_tag_wellformed_bag rme valid_value ts0 →
  (τ, Call Pop #()) ∈ ts0 →
  filter (λ x : positive * trace, x.1 = τ) ts0 = [(τ, Call Pop #())]
  ∨ ∃ r, (if rme then True else r ≠ IsEmpty)
       ∧ filter (λ x : positive * trace, x.1 = τ) ts0 = [(τ, Call Pop #()); (τ, Ret (encode_response r))].
Proof.
  intros Hwf Hin.
  assert (Hin_filt : (τ, Call Pop #()) ∈ filter (λ x, x.1 = τ) ts0).
  { apply list_elem_of_filter. done. }
  destruct (Hwf τ) as [(w & _ & Hpfx)|(r & Hr_ne & Hpfx)].
  - exfalso.
    eapply elem_of_prefix in Hin_filt; last exact Hpfx.
    apply elem_of_cons in Hin_filt as [Habs|Hin_filt].
    + discriminate.
    + apply elem_of_cons in Hin_filt as [Habs|Hin_filt]; [discriminate|by set_solver].
  - destruct (filter (λ x, x.1 = τ) ts0) as [|x xs] eqn:Heq; first by set_solver.
    apply prefix_cons_inv_1 in Hpfx as Hx.
    destruct xs as [|y ys].
    + left. rewrite Hx //.
    + right.
      apply prefix_cons_inv_2 in Hpfx.
      apply prefix_cons_inv_1 in Hpfx as Hy.
      apply prefix_cons_inv_2, prefix_nil_inv in Hpfx. subst ys.
      exists r. split; first exact Hr_ne. rewrite Hx Hy //.
Qed.

(* Helper: incomplete pop filter in ts is exactly [Call] *)
Local Lemma incomplete_pop_filter rme valid_value ts0 m0 τ :
  per_tag_wellformed_bag rme valid_value ts0 →
  (τ, Call Pop #()) ∈ ts0 →
  τ ∈ (unpaired_operations ts0 m0).1.2 →
  filter (λ x : positive * trace, x.1 = τ) ts0 = [(τ, Call Pop #())].
Proof.
  intros Hwf Hin Hupop.
  destruct (wellformed_pop_filter_prefix _ _ _ _ Hwf Hin) as [Heq|(r & _ & Heq)].
  - exact Heq.
  - exfalso.
    apply unpaired_pop_no_ret in Hupop.
    apply Hupop.
    assert (Hin_ret : (τ, Ret (encode_response r)) ∈ ts0).
    { assert (H : (τ, Ret (encode_response r)) ∈ filter (λ x, x.1 = τ) ts0) by (rewrite Heq; set_solver).
      by apply list_elem_of_filter in H as [_ ?]. }
    apply (list_elem_of_fmap_2 fst _ (τ, Ret (encode_response r))).
    apply list_elem_of_filter. split; last exact Hin_ret.
    simpl. exists r. done.
Qed.

(* Helper: complete pop filter in ts is exactly [Call; Ret r] for some r,
   plus r ≠ IsEmpty when rme = NeverEmpty. *)
Local Lemma complete_pop_filter_wf rme valid_value ts0 m0 τ :
  per_tag_wellformed_bag rme valid_value ts0 →
  (τ, Call Pop #()) ∈ ts0 →
  τ ∉ (unpaired_operations ts0 m0).1.2 →
  ∃ r, (if rme then True else r ≠ IsEmpty)
       ∧ filter (λ x : positive * trace, x.1 = τ) ts0
         = [(τ, Call Pop #()); (τ, Ret (encode_response r))].
Proof.
  intros Hwf Hin Hnotin.
  destruct (wellformed_pop_filter_prefix _ _ _ _ Hwf Hin) as [Heq|(r & Hr_ne & Heq)].
  - exfalso. apply Hnotin.
    rewrite /unpaired_operations.
    apply list_elem_of_difference. split.
    + apply (list_elem_of_fmap_2 fst _ (τ, Call Pop #())).
      apply list_elem_of_filter. split; [done|exact Hin].
    + intros Hin_ret.
      apply list_elem_of_fmap_1 in Hin_ret as ([τ' ev] & Heq' & Hin_ret).
      simpl in Heq'. subst τ'.
      apply list_elem_of_filter in Hin_ret as [Hret Hin_ret].
      simpl in Hret. destruct Hret as [r ->].
      assert (Hin_filt : (τ, Ret (encode_response r)) ∈ filter (λ x, x.1 = τ) ts0).
      { apply list_elem_of_filter. done. }
      rewrite Heq in Hin_filt.
      apply elem_of_cons in Hin_filt as [Habs|?]; [discriminate|by set_solver].
  - exists r. split; [exact Hr_ne|exact Heq].
Qed.

(* Helper: push tag is not in upop *)
Local Lemma push_tag_not_upop rme valid_value ts0 m0 τ :
  per_tag_wellformed_bag rme valid_value ts0 →
  τ ∈ push_of_trace ts0 →
  τ ∉ (unpaired_operations ts0 m0).1.2.
Proof.
  intros Hwf Hpush Hupop.
  apply unpaired_pop_is_pop in Hupop.
  exact (push_xor_pop_of_trace _ _ _ _ Hwf Hpush Hupop).
Qed.

(* Helper: pop tag is not in up *)
Local Lemma pop_tag_not_up rme valid_value ts0 m0 τ :
  per_tag_wellformed_bag rme valid_value ts0 →
  τ ∈ pop_of_trace ts0 →
  τ ∉ (unpaired_operations ts0 m0).1.1.
Proof.
  intros Hwf Hpop Hup.
  apply unpaired_push_is_push in Hup.
  exact (push_xor_pop_of_trace _ _ _ _ Hwf Hup Hpop).
Qed.

(* Helper: a tag in npop2 is not in ts *)
Local Lemma npop2_tag_not_in_ts ts0 τ t calls ump :
  (τ, t) ∈ close_trace_add_pop calls (close_trace_add_match ump (max_tag ts0.*1 + 1)) →
  ∀ ev : trace, (τ, ev) ∉ ts0.
Proof.
  intros Hin ev Hin_ts.
  pose proof (close_trace_add_pop_fresh_tag _ _ _ _ _ Hin).
  pose proof (tag_in_ts_le_max_tag _ _ _ Hin_ts).
  lia.
Qed.

(* Helper: entries in close_trace_add_pop have specific structure *)
Local Lemma close_trace_add_pop_structure calls m_add :
  ∀ τ t, (τ, t) ∈ close_trace_add_pop calls m_add →
  t = Call Pop #() ∨ ∃ τ1, (τ1, τ) ∈ m_add ∧ t = Ret (ret_val_of_call (calls !!! τ1)).
Proof.
  rewrite /close_trace_add_pop.
  intros τ t [Hin|Hin]%elem_of_app.
  - apply list_elem_of_fmap in Hin as ([τ1' τ2'] & Heq & Hin_m).
    injection Heq as -> ->. left. done.
  - apply list_elem_of_fmap in Hin as ([τ1' τ2'] & Heq & Hin_m).
    injection Heq as -> ->. right. eexists. split; [exact Hin_m|done].
Qed.

(* Helper: filter of close_trace_add_pop for non-member tag *)
Local Lemma filter_close_trace_add_pop_not_in τ calls m_add :
  τ ∉ m_add.*2 →
  filter (λ x : positive * trace, x.1 = τ) (close_trace_add_pop calls m_add) = [].
Proof.
  intros Hnotin. apply filter_False_nil, Forall_forall.
  intros [τ' t'] Hin. simpl. intros ->.
  apply close_trace_add_pop_elem in Hin as [τ1 Hin].
  apply Hnotin. apply (list_elem_of_fmap_2 snd _ (τ1, τ)). exact Hin.
Qed.

(* Helper: filter the Calls section of close_trace_add_pop for a specific tag τ. *)
Local Lemma filter_calls_of_close_trace_add_pop_in_exact τ τ1 (m_add : list (positive * positive)) :
  NoDup m_add.*2 →
  (τ1, τ) ∈ m_add →
  filter (λ x : positive * trace, x.1 = τ)
         ((λ '(_, τ2), (τ2, Call Pop #())) <$> m_add)
    = [(τ, Call Pop #())].
Proof.
  intros Hnd Hin.
  induction m_add as [|[τ1' τ2'] m_add IH]; first by set_solver.
  apply NoDup_cons in Hnd as [Hnotin Hnd]. simpl in Hnotin.
  apply elem_of_cons in Hin as [Heq|Hin].
  - injection Heq as Heq1 Heq2. subst τ1' τ2'.
    simpl. rewrite filter_cons_True; last done.
    rewrite (filter_False_nil _ ((λ '(_, τ2), _) <$> m_add)); first done.
    apply Forall_forall. intros [τ'' t''] Hin' Heq_simpl.
    simpl in Heq_simpl. subst τ''.
    apply Hnotin. apply list_elem_of_fmap_1 in Hin' as ([τa τb] & Heq & Hin_m).
    simpl in Heq. injection Heq as Hτb_eq Ht_eq. subst τb.
    apply (list_elem_of_fmap_2 snd _ (τa, τ)). exact Hin_m.
  - assert (Hne : τ2' ≠ τ).
    { intros ->. apply Hnotin.
      apply (list_elem_of_fmap_2 snd _ (τ1, τ)). exact Hin. }
    simpl. rewrite filter_cons_False; last (simpl; done).
    exact (IH Hnd Hin).
Qed.

Local Lemma filter_rets_of_close_trace_add_pop_in_exact τ τ1 (calls : gmap positive (nat*val)) (m_add : list (positive * positive)) :
  NoDup m_add.*2 →
  (τ1, τ) ∈ m_add →
  filter (λ x : positive * trace, x.1 = τ)
         ((λ '(τ1', τ2'), (τ2', Ret (ret_val_of_call (calls !!! τ1')))) <$> m_add)
    = [(τ, Ret (ret_val_of_call (calls !!! τ1)))].
Proof.
  intros Hnd Hin.
  induction m_add as [|[τ1' τ2'] m_add IH]; first by set_solver.
  apply NoDup_cons in Hnd as [Hnotin Hnd]. simpl in Hnotin.
  apply elem_of_cons in Hin as [Heq|Hin].
  - injection Heq as Heq1 Heq2. subst τ1' τ2'.
    simpl. rewrite filter_cons_True; last done.
    rewrite (filter_False_nil _ ((λ '(τ1', τ2'), _) <$> m_add)); first done.
    apply Forall_forall. intros [τ'' t''] Hin' Heq_simpl.
    simpl in Heq_simpl. subst τ''.
    apply Hnotin. apply list_elem_of_fmap_1 in Hin' as ([τa τb] & Heq & Hin_m).
    simpl in Heq. injection Heq as Hτb_eq Ht_eq. subst τb.
    apply (list_elem_of_fmap_2 snd _ (τa, τ)). exact Hin_m.
  - assert (Hne : τ2' ≠ τ).
    { intros ->. apply Hnotin.
      apply (list_elem_of_fmap_2 snd _ (τ1, τ)). exact Hin. }
    simpl. rewrite filter_cons_False; last (simpl; done).
    exact (IH Hnd Hin).
Qed.

(* Helper: filter of close_trace_add_pop for a specific (τ1, τ) pair. *)
Local Lemma filter_close_trace_add_pop_in_exact τ τ1 calls m_add :
  NoDup m_add.*2 →
  (τ1, τ) ∈ m_add →
  filter (λ x : positive * trace, x.1 = τ) (close_trace_add_pop calls m_add)
    = [(τ, Call Pop #()); (τ, Ret (ret_val_of_call (calls !!! τ1)))].
Proof.
  intros Hnd Hin.
  rewrite /close_trace_add_pop filter_app.
  rewrite (filter_calls_of_close_trace_add_pop_in_exact _ τ1) //.
  rewrite (filter_rets_of_close_trace_add_pop_in_exact _ τ1) //.
Qed.

(* Helper: filter of close_trace_add_pop for a member tag *)
Local Lemma filter_close_trace_add_pop_in τ calls m_add :
  NoDup m_add.*2 →
  (∃ τ1, (τ1, τ) ∈ m_add) →
  ∃ v, filter (λ x : positive * trace, x.1 = τ) (close_trace_add_pop calls m_add)
       = [(τ, Call Pop #()); (τ, Ret v)].
Proof.
  intros Hnd [τ1 Hin].
  exists (ret_val_of_call (calls !!! τ1)).
  by apply filter_close_trace_add_pop_in_exact.
Qed.

(* Helper: tags in unpaired operations are ≤ max_tag *)
Local Lemma unpaired_push_le_max ts0 m0 τ :
  τ ∈ (unpaired_operations ts0 m0).1.1 →
  (τ ≤ max_tag ts0.*1)%positive.
Proof.
  intros Hin.
  apply unpaired_push_is_push in Hin.
  apply push_tag_in_trace in Hin as [v Hin].
  eapply tag_in_ts_le_max_tag. exact Hin.
Qed.

Local Lemma unpaired_pop_le_max ts0 m0 τ :
  τ ∈ (unpaired_operations ts0 m0).1.2 →
  (τ ≤ max_tag ts0.*1)%positive.
Proof.
  intros Hin.
  apply unpaired_pop_is_pop in Hin.
  apply pop_tag_in_trace in Hin.
  eapply tag_in_ts_le_max_tag. exact Hin.
Qed.

(* Helper: fresh npop2 tags are not in np or npop1 *)
Local Lemma npop2_tag_not_in_up ts0 m0 τ ump :
  (∃ τ1, (τ1, τ) ∈ close_trace_add_match ump (max_tag ts0.*1 + 1)) →
  τ ∉ (unpaired_operations ts0 m0).1.1.
Proof.
  intros [τ1 Hin] Hin_up.
  pose proof (close_trace_add_match_tags_fresh _ _ _ _ Hin).
  pose proof (unpaired_push_le_max _ _ _ Hin_up).
  lia.
Qed.

Local Lemma npop2_tag_not_in_upop ts0 m0 τ ump :
  (∃ τ1, (τ1, τ) ∈ close_trace_add_match ump (max_tag ts0.*1 + 1)) →
  τ ∉ (unpaired_operations ts0 m0).1.2.
Proof.
  intros [τ1 Hin] Hin_upop.
  pose proof (close_trace_add_match_tags_fresh _ _ _ _ Hin).
  pose proof (unpaired_pop_le_max _ _ _ Hin_upop).
  lia.
Qed.

Local Lemma complete_trace_add_match_nm1_find upop m0 ump τ1 τ2 :
  (τ1, τ2) ∈ (complete_trace_add_match upop m0 ump).1 →
  find (λ x : positive * positive, bool_decide (x.2 = τ2)) m0 = None.
Proof.
  revert ump. induction upop as [|τ2' upop IH]; first by set_solver.
  intros ump. simpl.
  destruct (find (λ x, bool_decide (x.2 = τ2')) m0) as [p|] eqn:Hfind.
  - exact (IH ump).
  - destruct ump as [|τ1' ump'].
    + exact (IH []).
    + destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
      simpl. intros [Heq|Hin]%elem_of_cons.
      * injection Heq as -> ->. exact Hfind.
      * assert (Hin' : (τ1, τ2) ∈ (complete_trace_add_match upop m0 ump').1)
          by (rewrite Hrec; exact Hin).
        exact (IH ump' Hin').
Qed.

Local Lemma find_some_elem {A} (P : A → bool) (l : list A) (x : A) :
  x ∈ l → P x = true → ∃ y, find P l = Some y.
Proof.
  intros Hin Hpx.
  induction l as [|a l IH]; first by set_solver.
  simpl. destruct (P a) eqn:Hpa.
  - eexists. done.
  - apply elem_of_cons in Hin as [->|Hin].
    + rewrite Hpx in Hpa. discriminate.
    + exact (IH Hin).
Qed.

Local Lemma complete_trace_add_match_nm1_not_in_m0 upop m0 ump τ2 :
  τ2 ∈ (complete_trace_add_match upop m0 ump).1.*2 →
  τ2 ∉ m0.*2.
Proof.
  intros Hin Hin_m0.
  apply list_elem_of_fmap_1 in Hin as ([τ1' τ2'] & Heq & Hin_nm1).
  simpl in Heq. subst τ2'.
  pose proof (complete_trace_add_match_nm1_find _ _ _ _ _ Hin_nm1) as Hfind.
  apply list_elem_of_fmap_1 in Hin_m0 as ([τ1'' τ2''] & Heq2 & Hin_m0').
  simpl in Heq2. subst τ2''.
  assert (Hex : ∃ y, find (λ x : positive * positive, bool_decide (x.2 = τ2)) m0 = Some y).
  { eapply find_some_elem; first exact Hin_m0'.
    apply bool_decide_eq_true_2. done. }
  destruct Hex as [y Hy]. rewrite Hy in Hfind. discriminate.
Qed.

Local Lemma complete_trace_add_match_snd_nodup upop m0 ump :
  NoDup upop →
  NoDup (complete_trace_add_match upop m0 ump).1.*2.
Proof.
  revert ump. induction upop as [|τ2 upop IH]; intros ump Hnd.
  - simpl. constructor.
  - apply NoDup_cons in Hnd as [Hnotin Hnd].
    simpl.
    destruct (find _ m0) as [?|].
    + exact (IH ump Hnd).
    + destruct ump as [|τ1 ump'].
      * exact (IH [] Hnd).
      * destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
        simpl. apply NoDup_cons. split.
        { intros Hin.
          assert (Hin' : τ2 ∈ (complete_trace_add_match upop m0 ump').1.*2)
            by (rewrite Hrec; exact Hin).
          apply Hnotin.
          exact (complete_trace_add_match_snd_sub _ _ _ _ Hin'). }
        { assert (H := IH ump' Hnd).
          rewrite Hrec /= in H. exact H. }
Qed.

Local Lemma complete_trace_add_match_fst_nodup upop m0 ump :
  NoDup ump →
  NoDup (complete_trace_add_match upop m0 ump).1.*1.
Proof.
  revert ump. induction upop as [|τ2 upop IH]; intros ump Hnd.
  - simpl. constructor.
  - simpl.
    destruct (find _ m0) as [?|].
    + exact (IH ump Hnd).
    + destruct ump as [|τ1 ump'].
      * exact (IH [] Hnd).
      * apply NoDup_cons in Hnd as [Hnotin Hnd].
        destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
        simpl. apply NoDup_cons. split.
        { intros Hin.
          assert (Hin' : τ1 ∈ (complete_trace_add_match upop m0 ump').1.*1)
            by (rewrite Hrec; exact Hin).
          apply Hnotin.
          exact (complete_trace_add_match_fst_sub _ _ _ _ Hin'). }
        { assert (H := IH ump' Hnd).
          rewrite Hrec /= in H. exact H. }
Qed.

Local Lemma complete_trace_add_match_remaining_nodup upop m0 ump :
  NoDup ump →
  NoDup (complete_trace_add_match upop m0 ump).2.
Proof.
  revert ump. induction upop as [|τ2 upop IH]; intros ump Hnd.
  - simpl. exact Hnd.
  - simpl.
    destruct (find _ m0) as [?|].
    + exact (IH ump Hnd).
    + destruct ump as [|τ1 ump'].
      * exact (IH [] Hnd).
      * apply NoDup_cons in Hnd as [Hnotin Hnd].
        destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
        simpl. assert (H := IH ump' Hnd). rewrite Hrec /= in H. exact H.
Qed.

Local Lemma complete_trace_add_match_fst_snd_disjoint upop m0 ump :
  NoDup ump →
  ∀ τ, τ ∈ (complete_trace_add_match upop m0 ump).1.*1 →
       τ ∉ (complete_trace_add_match upop m0 ump).2.
Proof.
  intro Hnd_ump.
  revert ump Hnd_ump. induction upop as [|τ2 upop IH]; intros ump Hnd_ump.
  - simpl. intros τ. set_solver.
  - simpl.
    destruct (find _ m0) as [?|].
    + exact (IH ump Hnd_ump).
    + destruct ump as [|τ1 ump'].
      * exact (IH [] Hnd_ump).
      * apply NoDup_cons in Hnd_ump as [Hnotin Hnd].
        destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
        simpl. intros τ [->|Hin]%elem_of_cons Hin2.
        { assert (Hin2' : τ1 ∈ (complete_trace_add_match upop m0 ump').2)
            by (rewrite Hrec; exact Hin2).
          pose proof (H := complete_trace_add_match_remaining_sub upop m0 ump' τ1 Hin2').
          exact (Hnotin H). }
        { assert (Hin' : τ ∈ (complete_trace_add_match upop m0 ump').1.*1)
            by (rewrite Hrec; exact Hin).
          assert (Hin2' : τ ∈ (complete_trace_add_match upop m0 ump').2)
            by (rewrite Hrec; exact Hin2).
          exact (IH ump' Hnd τ Hin' Hin2'). }
Qed.

Local Lemma nm1_snd_not_in_nm2_snd (ts0 : list (positive * trace)) upop m0 ump :
  upop ⊆ pop_of_trace ts0 →
  ∀ τ, τ ∈ (complete_trace_add_match upop m0 ump).1.*2 →
       τ ∉ (close_trace_add_match (complete_trace_add_match upop m0 ump).2 (max_tag ts0.*1 + 1)).*2.
Proof.
  intros Hupop_sub τ Hin1 Hin2.
  pose proof (complete_trace_add_match_snd_sub upop m0 ump τ Hin1) as Hupop.
  apply list_elem_of_fmap_1 in Hin2 as ([τ1' τ2'] & Heq & Hin_nm2).
  simpl in Heq. subst τ2'.
  apply close_trace_add_match_tags_fresh in Hin_nm2.
  assert (Hpop : τ ∈ pop_of_trace ts0) by (apply Hupop_sub; exact Hupop).
  apply pop_tag_in_trace in Hpop.
  pose proof (tag_in_ts_le_max_tag _ _ _ Hpop).
  lia.
Qed.

Local Lemma complete_trace_remove_pop_ret_val τ upop calls m_app :
  τ ∈ upop →
  (∃ τ1, find (λ x : positive * positive, bool_decide (x.2 = τ)) m_app = Some (τ1, τ)
         ∧ (τ, Ret (ret_val_of_call (calls !!! τ1))) ∈ complete_trace_remove_pop upop calls m_app)
  ∨ (find (λ x : positive * positive, bool_decide (x.2 = τ)) m_app = None
     ∧ filter (λ x : positive * trace, x.1 = τ) (complete_trace_remove_pop upop calls m_app) = []).
Proof.
  intros Hin.
  rewrite /complete_trace_remove_pop.
  destruct (find (λ x : positive * positive, bool_decide (x.2 = τ)) m_app) as [[τ1 τ2']|] eqn:Hfind.
  - left.
    assert (Hfind_copy := Hfind).
    apply find_some in Hfind_copy as [Hin_f Hbd].
    apply bool_decide_eq_true_1 in Hbd. simpl in Hbd. subst τ2'.
    exists τ1. split; [done|].
    apply list_elem_of_omap. exists τ. split; first exact Hin. rewrite Hfind. done.
  - right. split; first done.
    apply (filter_npop1_in_unmatched _ upop calls). exact Hfind.
Qed.

Local Lemma extract_calls_lookup rme valid_value (ts0 : list (positive * trace)) τ n v :
  per_tag_wellformed_bag rme valid_value ts0 →
  (τ, Call n v) ∈ ts0 →
  extract_calls ts0 !!! τ = (n, v).
Proof.
  intros Hwf0 Hin.
  rewrite /extract_calls lookup_total_alt.
  assert (Hin_omap : (τ, (n, v)) ∈ omap (λ x : positive * trace,
    match x with (τ0, Call n0 v0) => Some (τ0, (n0, v0)) | _ => None end) ts0).
  { apply list_elem_of_omap. exists (τ, Call n v). split; [exact Hin|done]. }
  set (omap_result := omap (λ x : positive * trace,
    match x with (τ0, Call n0 v0) => Some (τ0, (n0, v0)) | _ => None end) ts0).
  assert (Hlookup : (list_to_map omap_result : gmap positive (nat*val)) !! τ = Some (n, v)).
  { apply elem_of_list_to_map_1'.
    - (* Uniqueness: any other Call of τ has the same operation and value *)
      intros y Hin_y.
      apply list_elem_of_omap in Hin_y as ([τ_y t_y] & Hin_ts_y & Heq_y).
      destruct t_y as [n_y v_y| |]; try discriminate. injection Heq_y as -> <-.
      opose proof (per_tag_partial_wellformed_inj_call ts0 τ n v n_y v_y _ Hin Hin_ts_y)
        as [-> ->]; last done.
      by eapply per_tag_wellformed_per_tag_partial_wellformed,
                per_tag_wellformed_bag_wellformed.
    - exact Hin_omap. }
  rewrite Hlookup. done.
Qed.

Local Lemma npop1_matched_ret rme valid_value ts0 τ1 τ2 v upop0 calls0 m_nm :
  per_tag_wellformed_bag rme valid_value ts0 →
  NoDup m_nm.*2 →
  (τ1, τ2) ∈ m_nm →
  τ2 ∈ upop0 →
  (τ1, Call Push v) ∈ ts0 →
  calls0 = extract_calls ts0 →
  (τ2, Ret (encode_response (NonEmpty v))) ∈ complete_trace_remove_pop upop0 calls0 m_nm.
Proof.
  intros Hwf0 Hnd Hin_m Hin_upop Hcall_push Hcalls.
  rewrite /complete_trace_remove_pop.
  apply list_elem_of_omap. exists τ2. split; first exact Hin_upop.
  (* find (λ x, bool_decide (x.2 = τ2)) m_nm should return Some (τ1, τ2) *)
  assert (Hfind : ∃ τ1_f, find (λ x : positive * positive, bool_decide (x.2 = τ2)) m_nm = Some (τ1_f, τ2) ∧ (τ1_f, τ2) ∈ m_nm).
  { assert (Hex := find_some_elem (λ x : positive * positive, bool_decide (x.2 = τ2)) m_nm (τ1, τ2) Hin_m).
    assert (Hbd : bool_decide ((τ1, τ2).2 = τ2) = true) by (apply bool_decide_eq_true_2; done).
    destruct (Hex Hbd) as [y Hy].
    assert (Hy_copy := Hy).
    apply find_some in Hy_copy as [Hin_y Hbd_y].
    apply bool_decide_eq_true_1 in Hbd_y. simpl in Hbd_y.
    destruct y as [τ1_f τ2_f]. simpl in Hbd_y. subst τ2_f.
    exists τ1_f. split; [exact Hy|].
    apply list_elem_of_In. exact Hin_y. }
  destruct Hfind as [τ1_f [Hfind Hin_f]].
  rewrite Hfind.
  (* τ1_f = τ1 because NoDup m_nm.*2 and both (τ1, τ2) and (τ1_f, τ2) ∈ m_nm *)
  assert (Heq : τ1_f = τ1).
  { assert (Hnd' := proj1 (NoDup_alt m_nm.*2) Hnd).
    apply list_elem_of_lookup_1 in Hin_m as [i Hi].
    apply list_elem_of_lookup_1 in Hin_f as [j Hj].
    assert (Hij : i = j).
    { apply (Hnd' i j τ2).
      - rewrite list_lookup_fmap Hi. done.
      - rewrite list_lookup_fmap Hj. done. }
    subst j. rewrite Hi in Hj. by injection Hj. }
  subst τ1_f.
  f_equal.
  rewrite Hcalls (extract_calls_lookup _ _ ts0 τ1 Push v Hwf0 Hcall_push).
  done.
Qed.

(* Adding an element h that is neither a τ1-Call nor a τ2-Ret leaves
   pre_of_trace τ2 τ1 unchanged. *)
Local Lemma pre_of_trace_cons_irrelevant (h : positive * trace) ts τ1 τ2 :
  ¬ (h.1 = τ1 ∧ is_call h.2) →
  ¬ (h.1 = τ2 ∧ is_ret h.2) →
  pre_of_trace (h :: ts) τ2 τ1 ↔ pre_of_trace ts τ2 τ1.
Proof.
  intros Hh1 Hh2.
  rewrite /pre_of_trace /ret_of_tag /call_of_tag /=.
  destruct (decide (h.1 = τ2 ∧ is_ret h.2)) as [Habs|_]; first by destruct (Hh2 Habs).
  destruct (decide (h.1 = τ1 ∧ is_call h.2)) as [Habs|_]; first by destruct (Hh1 Habs).
  destruct (list_find (λ t : positive * trace, t.1 = τ2 ∧ is_ret t.2) ts) as [[i_ret x_ret]|];
    simpl; last done.
  destruct (list_find (λ t : positive * trace, t.1 = τ1 ∧ is_call t.2) ts) as [[i_call x_call]|];
    simpl; last done.
  by rewrite -Nat.succ_lt_mono.
Qed.

(* Filtering by (x.1 ∉ U) preserves pre_of_trace τ2 τ1 when both τ1, τ2 ∉ U. *)
Local Lemma pre_of_trace_filter_iff (U : list positive) ts τ1 τ2 :
  τ1 ∉ U → τ2 ∉ U →
  pre_of_trace (filter (λ x : positive * trace, x.1 ∉ U) ts) τ2 τ1 ↔
  pre_of_trace ts τ2 τ1.
Proof.
  intros HU1 HU2.
  induction ts as [|[τ t] ts IH]; first done.
  rewrite filter_cons.
  destruct (decide ((τ, t).1 ∉ U)) as [Hni|Hin]; cycle 1.
  - (* τ ∈ U. Then τ ≠ τ1 (HU1) and τ ≠ τ2 (HU2). Cons is irrelevant on RHS. *)
    simpl in Hin. apply dec_stable in Hin.
    rewrite (pre_of_trace_cons_irrelevant (τ, t)); [exact IH| |].
    + simpl. intros [-> _]. exact (HU1 Hin).
    + simpl. intros [-> _]. exact (HU2 Hin).
  - (* τ ∉ U: kept by filter. Both sides cons (τ, t). *)
    destruct (decide ((τ, t).1 = τ1 ∧ is_call (τ, t).2)) as [[Heq1 Hcall]|Hno1].
    + (* (τ, t) is a τ1-Call: pre_of_trace is False on both sides regardless of the tail. *)
      simpl in Heq1, Hcall. subst τ.
      assert (Hnot_ret : ¬ is_ret t) by (destruct t as [|?|?]; simpl in *; tauto).
      assert (Hpre_false : ∀ ts0, ¬ pre_of_trace ((τ1, t) :: ts0) τ2 τ1).
      { intros ts0 H.
        rewrite /pre_of_trace /ret_of_tag /call_of_tag /= in H.
        destruct (decide (τ1 = τ2 ∧ is_ret t)) as [[_ Habs]|_];
          first by destruct (Hnot_ret Habs).
        destruct (decide (τ1 = τ1 ∧ is_call t)) as [_|Habs];
          last by exfalso; apply Habs; done.
        destruct (list_find _ ts0) as [[i_ret x_ret]|]; cbn in H; last exact H.
        unfold mbind, option_bind, mret, option_ret in H. cbn in H. lia. }
      split; intros Hp; exfalso; eapply Hpre_false; exact Hp.
    + destruct (decide ((τ, t).1 = τ2 ∧ is_ret (τ, t).2)) as [[Heq2 Hret]|Hno2].
      * (* (τ, t) is a τ2-Ret. Both sides reduce to whether some τ1-Call exists in tail. *)
        simpl in Heq2, Hret. subst τ.
        assert (Hnot_call : ¬ is_call t) by (destruct t as [|?|?]; simpl in *; tauto).
        assert (Hpre_iff_call : ∀ ts0,
          pre_of_trace ((τ2, t) :: ts0) τ2 τ1 ↔
          is_Some (list_find (λ x' : positive * trace, x'.1 = τ1 ∧ is_call x'.2) ts0)).
        { intros ts0. split.
          - intros Hp. rewrite /pre_of_trace /ret_of_tag /call_of_tag /= in Hp.
            destruct (decide (τ2 = τ2 ∧ is_ret t)) as [_|Habs];
              last by exfalso; apply Habs; done.
            destruct (decide (τ2 = τ1 ∧ is_call t)) as [[_ Habs]|_];
              first by destruct (Hnot_call Habs).
            destruct (list_find _ ts0) as [[i_call x_call]|] eqn:Hfind.
            + by eexists.
            + exfalso. cbn in Hp. unfold mbind, option_bind, mret, option_ret in Hp. cbn in Hp. exact Hp.
          - intros [[i_c x_c] Hfind].
            rewrite /pre_of_trace /ret_of_tag /call_of_tag /=.
            destruct (decide (τ2 = τ2 ∧ is_ret t)) as [_|Habs];
              last by exfalso; apply Habs; done.
            destruct (decide (τ2 = τ1 ∧ is_call t)) as [[_ Habs]|_];
              first by destruct (Hnot_call Habs).
            rewrite Hfind. cbn. unfold mbind, option_bind, mret, option_ret. cbn. lia. }
        rewrite !Hpre_iff_call.
        (* Use that τ1 ∉ U preserves τ1-Calls under filter. *)
        split.
        -- intros [[i_c x_c] Hfind].
           apply list_find_Some in Hfind as (Hlk & [Hτ1 Hcall'] & _).
           apply list_elem_of_lookup_2 in Hlk.
           apply list_elem_of_filter in Hlk as [_ Hin].
           apply (list_find_elem_of _ ts x_c Hin).
           split; done.
        -- intros [[i_c x_c] Hfind].
           apply list_find_Some in Hfind as (Hlk & [Hτ1 Hcall'] & _).
           apply list_elem_of_lookup_2 in Hlk.
           assert (Hin_filt : x_c ∈ filter (λ x : positive * trace, x.1 ∉ U) ts).
           { apply list_elem_of_filter_2; [|exact Hlk]. simpl. by rewrite Hτ1. }
           apply (list_find_elem_of _ _ x_c Hin_filt).
           split; done.
      * (* (τ, t) is neither τ1-Call nor τ2-Ret. Apply pre_of_trace_cons_irrelevant on both sides. *)
        rewrite (pre_of_trace_cons_irrelevant (τ, t)); [|exact Hno1|exact Hno2].
        rewrite (pre_of_trace_cons_irrelevant (τ, t) ts); [|exact Hno1|exact Hno2].
        exact IH.
Qed.

Lemma close_preserves_validity rme valid_value ts m :
  per_tag_wellformed_bag rme valid_value ts →
  valid_match ts m →
  valid_match (close_trace ts m).1 (close_trace ts m).2.
Proof.
  intros Hwf Hvalid.
  pose proof Hvalid as Hvalid_orig.
  destruct Hvalid as (Hcov & [Hnd_m1 Hnd_m2] & Hforall).
  rewrite /close_trace.
  destruct (unpaired_operations ts m) as [[up upop] ump_init] eqn:Hops.
  destruct (complete_trace_add_match upop m ump_init) as [nm1 ump'] eqn:Hmatch.
  set (calls := extract_calls ts).
  set (np := complete_trace_add_push up).
  set (npop1 := complete_trace_remove_pop upop calls (m ++ nm1)).
  set (U := list_difference upop (m ++ nm1).*2).
  set (ts' := filter (λ x : positive * trace, x.1 ∉ U) ts).
  set (nm2 := close_trace_add_match ump' (max_tag ts.*1 + 1)).
  set (npop2_calls := close_trace_add_pop_calls nm2).
  set (npop2_rets := close_trace_add_pop_rets calls nm2).
  set (npop2 := close_trace_add_pop calls nm2).
  simpl.
  (* Useful facts *)
  assert (Hupop_is : upop = (unpaired_operations ts m).1.2)
    by (rewrite /unpaired_operations in Hops; by injection Hops as _ <- _).
  assert (Hup_is : up = (unpaired_operations ts m).1.1)
    by (rewrite /unpaired_operations in Hops; by injection Hops as <- _ _).
  assert (Hump_init_is : ump_init = (unpaired_operations ts m).2)
    by (rewrite /unpaired_operations in Hops; by injection Hops as _ _ <-).
  assert (Hupop_nd : NoDup upop)
    by (rewrite Hupop_is; eapply unpaired_pops_nodup; exact Hwf).
  assert (Hupop_sub : upop ⊆ pop_of_trace ts).
  { rewrite Hupop_is. intros τ Hin. by eapply unpaired_pop_is_pop. }
  assert (Hnm1 : nm1 = (complete_trace_add_match upop m ump_init).1)
    by (rewrite Hmatch; done).
  assert (Hump' : ump' = (complete_trace_add_match upop m ump_init).2)
    by (rewrite Hmatch; done).
  assert (Hnm1_snd_sub : nm1.*2 ⊆ upop).
  { rewrite Hnm1. apply complete_trace_add_match_snd_sub. }
  assert (Hnm1_fst_sub : nm1.*1 ⊆ ump_init).
  { rewrite Hnm1. apply complete_trace_add_match_fst_sub. }
  assert (Hump'_sub : ump' ⊆ ump_init).
  { rewrite Hump'. apply complete_trace_add_match_remaining_sub. }
  assert (Hump_init_sub_push : ump_init ⊆ push_of_trace ts).
  { rewrite Hump_init_is. intros τ Hin.
    rewrite /unpaired_operations /= in Hin.
    apply list_elem_of_difference in Hin as [Hin_push _]. exact Hin_push. }
  assert (Hump_init_disj_m1 : ∀ τ, τ ∈ ump_init → τ ∉ m.*1).
  { rewrite Hump_init_is. intros τ Hin Hin_m1.
    rewrite /unpaired_operations /= in Hin.
    apply list_elem_of_difference in Hin as [_ Hni].
    by apply Hni. }
  assert (Hnm1_nd2 : NoDup nm1.*2).
  { rewrite Hnm1. apply complete_trace_add_match_snd_nodup. exact Hupop_nd. }
  assert (Hump_init_nd : NoDup ump_init).
  { rewrite Hump_init_is /unpaired_operations /=.
    apply NoDup_list_difference. exact (call_push_tags_nodup _ _ _ Hwf). }
  assert (Hnm1_nd1 : NoDup nm1.*1).
  { rewrite Hnm1. apply complete_trace_add_match_fst_nodup. exact Hump_init_nd. }
  assert (Hnm2_nd2 : NoDup nm2.*2).
  { rewrite /nm2. apply close_trace_add_match_snd_nodup. }
  assert (Hnm2_fst : nm2.*1 = ump').
  { rewrite /nm2. apply close_trace_add_match_fst. }
  assert (Hnm2_fst_sub_push : nm2.*1 ⊆ push_of_trace ts).
  { rewrite Hnm2_fst. by etrans. }
  (* Pop tags ∉ U is a frequent fact: any τ with (τ, Call Pop) ∈ ts where τ matched in m *)
  assert (Hm2_not_U : ∀ τ, τ ∈ m.*2 → τ ∉ U).
  { intros τ Hin Hni. apply list_elem_of_difference in Hni as [_ Habs].
    apply Habs. apply list_elem_of_fmap_1 in Hin as ([τ1' τ2'] & -> & Hin').
    apply (list_elem_of_fmap_2 snd _ (τ1', τ2')). rewrite elem_of_app. by left. }
  assert (Hnm1_2_not_U : ∀ τ, τ ∈ nm1.*2 → τ ∉ U).
  { intros τ Hin Hni. apply list_elem_of_difference in Hni as [_ Habs].
    apply Habs. apply list_elem_of_fmap_1 in Hin as ([τ1' τ2'] & -> & Hin').
    apply (list_elem_of_fmap_2 snd _ (τ1', τ2')). rewrite elem_of_app. by right. }
  assert (Hpush_not_U : ∀ τ, τ ∈ push_of_trace ts → τ ∉ U).
  { intros τ Hin Hni. apply list_elem_of_difference in Hni as [Hin_upop _].
    apply (push_xor_pop_of_trace ts rme valid_value τ Hwf Hin).
    by apply Hupop_sub. }
  assert (Hts'_in : ∀ τ ev, τ ∉ U → (τ, ev) ∈ ts → (τ, ev) ∈ ts').
  { intros τ ev Hni Hin. rewrite /ts'. apply list_elem_of_filter_2; done. }
  (* Disjointness facts *)
  assert (Hm1_disj_nm1 : ∀ τ, τ ∈ m.*1 → τ ∉ nm1.*1).
  { intros τ Hin1 Hin2. exact (Hump_init_disj_m1 τ (Hnm1_fst_sub _ Hin2) Hin1). }
  assert (Hm1_disj_nm2 : ∀ τ, τ ∈ m.*1 → τ ∉ nm2.*1).
  { intros τ Hin1 Hin2. apply (Hump_init_disj_m1 τ).
    apply Hump'_sub. by rewrite -Hnm2_fst. exact Hin1. }
  assert (Hnm1_disj_nm2_1 : ∀ τ, τ ∈ nm1.*1 → τ ∉ nm2.*1).
  { intros τ Hin1 Hin2.
    rewrite Hnm1 in Hin1.
    rewrite Hnm2_fst Hump' in Hin2.
    pose proof (complete_trace_add_match_fst_snd_disjoint upop m ump_init) as Hdisj.
    apply (Hdisj Hump_init_nd τ Hin1 Hin2). }
  assert (Hm2_disj_nm1 : ∀ τ, τ ∈ m.*2 → τ ∉ nm1.*2).
  { intros τ Hin1 Hin2.
    apply (complete_trace_add_match_nm1_not_in_m0 upop m ump_init τ);
      [by rewrite -Hnm1 | exact Hin1]. }
  assert (Hm2_disj_nm2 : ∀ τ, τ ∈ m.*2 → τ ∉ nm2.*2).
  { intros τ Hin1 Hin2.
    apply list_elem_of_fmap_1 in Hin2 as ([τ1' τ2'] & Heq & Hin_nm2).
    simpl in Heq. subst τ2'.
    apply close_trace_add_match_tags_fresh in Hin_nm2.
    apply list_elem_of_fmap_1 in Hin1 as ([τ1'' τ2''] & Heq2 & Hin_m).
    simpl in Heq2. subst τ2''.
    pose proof (Hforall' := Hforall). rewrite Forall_forall in Hforall'.
    destruct (Hforall' _ Hin_m) as (_ & Hcall_pop & _).
    pose proof (tag_in_ts_le_max_tag _ _ _ Hcall_pop) as Hle.
    lia. }
  assert (Hnm1_disj_nm2_2 : ∀ τ, τ ∈ nm1.*2 → τ ∉ nm2.*2).
  { intros τ Hin1 Hin2.
    rewrite Hnm1 in Hin1.
    rewrite /nm2 Hump' in Hin2.
    exact (nm1_snd_not_in_nm2_snd ts upop m ump_init Hupop_sub τ Hin1 Hin2). }
  (* Each pop tag survives if it's in m++nm1++nm2 .*2 *)
  rewrite /valid_match.
  split_and!.
  - (* pop_val_of_trace (close_trace).1 ⊆ (m ++ nm1 ++ nm2).*2 *)
    rewrite /pop_val_of_trace.
    intros τ Hin.
    apply list_elem_of_fmap_1 in Hin as ([τ' ev] & Heq & Hin_filt).
    simpl in Heq. subst τ'.
    apply list_elem_of_filter in Hin_filt as [Hev_pop_val Hin_close].
    rewrite /is_ret_pop_val in Hev_pop_val. simpl in Hev_pop_val.
    destruct Hev_pop_val as [w ->].
    rewrite -/ts' -/np -/npop2_calls -/npop1 -/npop2_rets in Hin_close.
    apply elem_of_app in Hin_close as [Hin_ts'|Hin_rest].
    + (* in ts': preserved Ret NonEmpty in ts. So τ ∈ pop_val_of_trace ts ⊆ m.*2. *)
      apply list_elem_of_filter in Hin_ts' as [_ Hin_ts].
      assert (Hτ_pop_val : τ ∈ pop_val_of_trace ts).
      { apply (list_elem_of_fmap_2 fst _ (τ, Ret (encode_response (NonEmpty w)))).
        apply list_elem_of_filter; split; [eexists; done|exact Hin_ts]. }
      specialize (Hcov τ Hτ_pop_val).
      rewrite !fmap_app !elem_of_app. by left.
    + apply elem_of_app in Hin_rest as [Hin_np|Hin_rest].
      { exfalso.
        apply complete_trace_add_push_elem in Hin_np as [Habs _]. discriminate. }
      apply elem_of_app in Hin_rest as [Hin_npop2_calls|Hin_rest].
      { exfalso.
        rewrite /npop2_calls /close_trace_add_pop_calls in Hin_npop2_calls.
        apply list_elem_of_fmap_1 in Hin_npop2_calls as ([τ1' τ2'] & Heq & _).
        injection Heq as _ Habs. discriminate. }
      apply elem_of_app in Hin_rest as [Hin_npop1|Hin_npop2_rets].
      * (* in npop1: τ ∈ (m++nm1).*2 (matched). *)
        rewrite /npop1 /complete_trace_remove_pop list_elem_of_omap in Hin_npop1.
        destruct Hin_npop1 as (τin & _ & Hopt).
        destruct (find _ (m ++ nm1)) as [[τ1' τ2']|] eqn:Hfind; last discriminate.
        injection Hopt as Heq_τ _. subst τin.
        apply find_some in Hfind as [Hin_pair Hbd].
        apply bool_decide_eq_true_1 in Hbd. simpl in Hbd. subst τ2'.
        apply list_elem_of_In in Hin_pair.
        rewrite !fmap_app !elem_of_app.
        rewrite elem_of_app in Hin_pair.
        destruct Hin_pair as [Hin_m|Hin_nm1].
        -- left.
           apply (list_elem_of_fmap_2 snd _ (τ1', τ)). exact Hin_m.
        -- right. left.
           apply (list_elem_of_fmap_2 snd _ (τ1', τ)). exact Hin_nm1.
      * (* in npop2_rets: τ ∈ nm2.*2. *)
        rewrite /npop2_rets /close_trace_add_pop_rets in Hin_npop2_rets.
        apply list_elem_of_fmap_1 in Hin_npop2_rets as ([τ1' τ2'] & Heq & Hin_nm2).
        injection Heq as -> _.
        rewrite !fmap_app !elem_of_app. right. right.
        apply (list_elem_of_fmap_2 snd _ (τ1', τ2')). exact Hin_nm2.
  - (* NoDup (m ++ nm1 ++ nm2).*1 *)
    rewrite !fmap_app.
    apply NoDup_app. split_and!.
    + exact Hnd_m1.
    + intros τ Hin1 Hin2.
      rewrite elem_of_app in Hin2.
      destruct Hin2 as [Hin_nm1|Hin_nm2].
      * exact (Hm1_disj_nm1 τ Hin1 Hin_nm1).
      * exact (Hm1_disj_nm2 τ Hin1 Hin_nm2).
    + apply NoDup_app. split_and!.
      * exact Hnm1_nd1.
      * intros τ Hin1 Hin2.
        exact (Hnm1_disj_nm2_1 τ Hin1 Hin2).
      * rewrite Hnm2_fst Hump'.
        apply complete_trace_add_match_remaining_nodup. exact Hump_init_nd.
  - (* NoDup (m ++ nm1 ++ nm2).*2 *)
    rewrite !fmap_app.
    apply NoDup_app. split_and!.
    + exact Hnd_m2.
    + intros τ Hin1 Hin2.
      rewrite elem_of_app in Hin2.
      destruct Hin2 as [Hin_nm1|Hin_nm2].
      * exact (Hm2_disj_nm1 τ Hin1 Hin_nm1).
      * exact (Hm2_disj_nm2 τ Hin1 Hin_nm2).
    + apply NoDup_app. split_and!.
      * exact Hnm1_nd2.
      * intros τ Hin1 Hin2.
        exact (Hnm1_disj_nm2_2 τ Hin1 Hin2).
      * exact Hnm2_nd2.
  - (* Forall over m ++ nm1 ++ nm2 *)
    assert (Hnm_nd2 : NoDup (m ++ nm1).*2).
    { rewrite fmap_app. apply NoDup_app. split_and!.
      - exact Hnd_m2.
      - intros τ Hin1 Hin2. exact (Hm2_disj_nm1 τ Hin1 Hin2).
      - exact Hnm1_nd2. }
    apply Forall_app. split; [|apply Forall_app; split].
    + (* m case *)
      apply Forall_forall. intros [τ1 τ2] Hin_m.
      pose proof (Hforall_ts := Hforall). rewrite Forall_forall in Hforall_ts.
      destruct (Hforall_ts _ Hin_m) as (Hno_pre & Hcall_pop_ts & v & Hcall_push_ts & Hret_or).
      assert (Hτ1_push : τ1 ∈ push_of_trace ts).
      { apply (list_elem_of_fmap_2 fst _ (τ1, Call Push v)).
        apply list_elem_of_filter; split; [eexists; done|exact Hcall_push_ts]. }
      assert (Hτ1_not_U : τ1 ∉ U) by exact (Hpush_not_U _ Hτ1_push).
      assert (Hτ2_in_m2 : τ2 ∈ m.*2)
        by (apply (list_elem_of_fmap_2 snd _ (τ1, τ2)); exact Hin_m).
      assert (Hτ2_not_U : τ2 ∉ U) by exact (Hm2_not_U _ Hτ2_in_m2).
      assert (Hcall_push_in_ts' : (τ1, Call Push v) ∈ ts')
        by exact (Hts'_in _ _ Hτ1_not_U Hcall_push_ts).
      split_and!.
      * (* ¬ pre_of_trace close τ2 τ1 *)
        apply (not_pre_of_trace_app ts' (np ++ npop2_calls ++ npop1 ++ npop2_rets) τ2 τ1).
        { do 2 eexists. exact Hcall_push_in_ts'. }
        rewrite (pre_of_trace_filter_iff U ts τ1 τ2 Hτ1_not_U Hτ2_not_U).
        exact Hno_pre.
      * apply elem_of_app. left. exact (Hts'_in _ _ Hτ2_not_U Hcall_pop_ts).
      * exists v. split.
        { apply elem_of_app. left. exact Hcall_push_in_ts'. }
        destruct Hret_or as [Hret_in_ts|Hτ2_unfinished].
        -- left. apply elem_of_app. left.
           exact (Hts'_in _ _ Hτ2_not_U Hret_in_ts).
        -- left. apply elem_of_app. right. apply elem_of_app. right.
           apply elem_of_app. right. apply elem_of_app. left.
           assert (Hτ2_in_upop : τ2 ∈ upop).
           { rewrite Hupop_is /unpaired_operations /=.
             apply list_elem_of_difference. split.
             - apply (list_elem_of_fmap_2 fst _ (τ2, Call Pop #())).
               apply list_elem_of_filter; split; [done|exact Hcall_pop_ts].
             - intros Hin. apply Hτ2_unfinished.
               apply list_elem_of_fmap_1 in Hin as ([τ' ev] & Heq & Hin_filt).
               simpl in Heq. subst τ'.
               apply list_elem_of_filter in Hin_filt as [Hev_pop Hin_ts].
               rewrite /is_ret_pop /= in Hev_pop.
               destruct Hev_pop as [r ->].
               apply (list_elem_of_fmap_2 fst _ (τ2, Ret (encode_response r))).
               apply list_elem_of_filter; split; [done|exact Hin_ts]. }
           assert (Hin_pair : (τ1, τ2) ∈ m ++ nm1) by (apply elem_of_app; by left).
           exact (npop1_matched_ret rme valid_value ts τ1 τ2 v upop calls (m ++ nm1)
                    Hwf Hnm_nd2 Hin_pair Hτ2_in_upop Hcall_push_ts eq_refl).
    + (* nm1 case *)
      apply Forall_forall. intros [τ1 τ2] Hin_nm1.
      assert (Hτ1_in_ump_init : τ1 ∈ ump_init).
      { apply Hnm1_fst_sub. apply (list_elem_of_fmap_2 fst _ (τ1, τ2)). exact Hin_nm1. }
      assert (Hτ1_in_push : τ1 ∈ push_of_trace ts) by exact (Hump_init_sub_push _ Hτ1_in_ump_init).
      destruct (push_tag_in_trace _ _ Hτ1_in_push) as [v Hcall_push_ts].
      assert (Hτ1_not_U : τ1 ∉ U) by exact (Hpush_not_U _ Hτ1_in_push).
      assert (Hτ2_in_upop : τ2 ∈ upop).
      { apply Hnm1_snd_sub. apply (list_elem_of_fmap_2 snd _ (τ1, τ2)). exact Hin_nm1. }
      assert (Hτ2_in_pop : τ2 ∈ pop_of_trace ts) by exact (Hupop_sub _ Hτ2_in_upop).
      pose proof (Hcall_pop_ts := pop_tag_in_trace _ _ Hτ2_in_pop).
      assert (Hτ2_in_nm1_2 : τ2 ∈ nm1.*2)
        by (apply (list_elem_of_fmap_2 snd _ (τ1, τ2)); exact Hin_nm1).
      assert (Hτ2_not_U : τ2 ∉ U) by exact (Hnm1_2_not_U _ Hτ2_in_nm1_2).
      assert (Hcall_push_in_ts' : (τ1, Call Push v) ∈ ts')
        by exact (Hts'_in _ _ Hτ1_not_U Hcall_push_ts).
      assert (Hin_pair : (τ1, τ2) ∈ m ++ nm1) by (apply elem_of_app; by right).
      assert (Hret_in_npop1 : (τ2, Ret (encode_response (NonEmpty v))) ∈ npop1)
        by exact (npop1_matched_ret rme valid_value ts τ1 τ2 v upop calls (m ++ nm1)
                    Hwf Hnm_nd2 Hin_pair Hτ2_in_upop Hcall_push_ts eq_refl).
      (* No Ret for τ2 in ts (since τ2 ∈ upop = list_difference call_pops ret_pops) *)
      assert (Hτ2_no_ret_ts : τ2 ∉ (filter (is_ret_pop ∘ snd) ts).*1).
      { rewrite Hupop_is /unpaired_operations /= in Hτ2_in_upop.
        apply list_elem_of_difference in Hτ2_in_upop as [_ ?]. done. }
      split_and!.
      * (* ¬ pre_of_trace close τ2 τ1: τ2 has no Ret in ts → no Ret in ts'. *)
        intros Hpre.
        rewrite /pre_of_trace in Hpre.
        destruct (ret_of_tag _ τ2) as [[i_ret [τ_r ev_r]]|] eqn:Hret_close;
          simpl in Hpre; last done.
        destruct (call_of_tag _ τ1) as [[i_call [τ_c ev_c]]|] eqn:Hcall_close;
          simpl in Hpre; last done.
        rewrite /ret_of_tag list_find_app_Some in Hret_close.
        rewrite /call_of_tag list_find_app_Some in Hcall_close.
        destruct Hcall_close as [Hcall_in_ts'|[Hlen_call [Hcall_none_ts' _]]].
        2: { exfalso. apply list_find_None in Hcall_none_ts'.
             rewrite Forall_forall in Hcall_none_ts'.
             apply (Hcall_none_ts' _ Hcall_push_in_ts'). simpl. by split. }
        apply list_find_Some in Hcall_in_ts' as (Hlk_call & _ & _).
        apply lookup_lt_Some in Hlk_call.
        destruct Hret_close as [Hret_in_ts'|[Hlen_ret _]].
        { (* τ2 has Ret in ts' but τ2 has no Ret in ts → contradiction *)
          exfalso.
          apply list_find_Some in Hret_in_ts' as (Hlk_ret & [Heq_τ Hev_ret] & _).
          simpl in Heq_τ. subst τ_r.
          apply Hτ2_no_ret_ts.
          apply list_elem_of_lookup_2 in Hlk_ret.
          rewrite /ts' in Hlk_ret.
          apply list_elem_of_filter in Hlk_ret as [_ Hin_ts].
          destruct ev_r as [|? ?|rv]; simpl in Hev_ret; try done.
          (* By per_tag_wellformed_bag, rv = encode_response r for some r since τ2 is a pop tag. *)
          destruct (Hwf τ2) as [(vp & _ & Hpfx)|(rp & _ & Hpfx)].
          { exfalso. (* τ2 has Push call pattern but we have (τ2, Call Pop) ∈ ts *)
            assert (Hin_filt : (τ2, Call Pop #()) ∈ filter (λ x, x.1 = τ2) ts).
            { apply list_elem_of_filter. done. }
            eapply elem_of_prefix in Hin_filt; last exact Hpfx.
            apply elem_of_cons in Hin_filt as [Heq|Hin_filt].
            - injection Heq as Habs. discriminate.
            - apply elem_of_cons in Hin_filt as [Heq|?]; last by set_solver.
              injection Heq as Habs. discriminate. }
          assert (Hin_filt : (τ2, Ret rv) ∈ filter (λ x, x.1 = τ2) ts).
          { apply list_elem_of_filter. done. }
          eapply elem_of_prefix in Hin_filt; last exact Hpfx.
          apply elem_of_cons in Hin_filt as [Heq|Hin_filt].
          { injection Heq as Habs. discriminate. }
          apply elem_of_cons in Hin_filt as [Heq|?]; last by set_solver.
          injection Heq as ->.
          apply (list_elem_of_fmap_2 fst _ (τ2, Ret (encode_response rp))).
          apply list_elem_of_filter; split; [|exact Hin_ts].
          eexists. reflexivity. }
        (* Ret in (np ++ npop1 ++ npop2) at position ≥ length ts' *)
        lia.
      * apply elem_of_app. left. exact (Hts'_in _ _ Hτ2_not_U Hcall_pop_ts).
      * exists v. split.
        { apply elem_of_app. left. exact Hcall_push_in_ts'. }
        left. apply elem_of_app. right. apply elem_of_app. right.
        apply elem_of_app. right. apply elem_of_app. left.
        exact Hret_in_npop1.
    + (* nm2 case *)
      apply Forall_forall. intros [τ1 τ2] Hin_nm2.
      assert (Hτ1_in_ump' : τ1 ∈ ump').
      { rewrite -Hnm2_fst.
        apply (list_elem_of_fmap_2 fst _ (τ1, τ2)). exact Hin_nm2. }
      assert (Hτ1_in_ump_init : τ1 ∈ ump_init) by exact (Hump'_sub _ Hτ1_in_ump').
      assert (Hτ1_in_push : τ1 ∈ push_of_trace ts) by exact (Hump_init_sub_push _ Hτ1_in_ump_init).
      destruct (push_tag_in_trace _ _ Hτ1_in_push) as [v Hcall_push_ts].
      assert (Hτ1_not_U : τ1 ∉ U) by exact (Hpush_not_U _ Hτ1_in_push).
      assert (Hcall_push_in_ts' : (τ1, Call Push v) ∈ ts')
        by exact (Hts'_in _ _ Hτ1_not_U Hcall_push_ts).
      (* npop2_calls contains (τ2, Call Pop); npop2_rets contains (τ2, Ret (ret_val_of_call (calls!!!τ1))) *)
      assert (Hcall_pop_in_npop2_calls : (τ2, Call Pop #()) ∈ npop2_calls).
      { rewrite /npop2_calls /close_trace_add_pop_calls.
        apply list_elem_of_fmap. exists (τ1, τ2). split; [reflexivity|exact Hin_nm2]. }
      assert (Hret_in_npop2_rets : (τ2, Ret (ret_val_of_call (calls !!! τ1))) ∈ npop2_rets).
      { rewrite /npop2_rets /close_trace_add_pop_rets.
        apply list_elem_of_fmap. exists (τ1, τ2). split; [reflexivity|exact Hin_nm2]. }
      assert (Hcalls_eq : ret_val_of_call (calls !!! τ1) = encode_response (NonEmpty v)).
      { rewrite /calls (extract_calls_lookup _ _ ts τ1 _ _ Hwf Hcall_push_ts). done. }
      assert (Hτ2_fresh : (max_tag ts.*1 + 1 ≤ τ2)%positive).
      { eapply close_trace_add_match_tags_fresh. rewrite -/nm2. exact Hin_nm2. }
      split_and!.
      * (* ¬ pre_of_trace close τ2 τ1: τ2 doesn't appear in ts (fresh).
            τ1's Call is in ts'. τ2's Ret is in npop2 (after ts' ++ np ++ npop1). *)
        intros Hpre.
        rewrite /pre_of_trace in Hpre.
        destruct (ret_of_tag _ τ2) as [[i_ret [τ_r ev_r]]|] eqn:Hret_close;
          simpl in Hpre; last done.
        destruct (call_of_tag _ τ1) as [[i_call [τ_c ev_c]]|] eqn:Hcall_close;
          simpl in Hpre; last done.
        rewrite /call_of_tag list_find_app_Some in Hcall_close.
        rewrite /ret_of_tag list_find_app_Some in Hret_close.
        destruct Hcall_close as [Hcall_in_ts'|[Hlen_call [Hcall_none_ts' _]]].
        2: { exfalso. apply list_find_None in Hcall_none_ts'.
             rewrite Forall_forall in Hcall_none_ts'.
             apply (Hcall_none_ts' _ Hcall_push_in_ts'). simpl. by split. }
        apply list_find_Some in Hcall_in_ts' as (Hlk_call & _ & _).
        apply lookup_lt_Some in Hlk_call.
        destruct Hret_close as [Hret_in_ts'|[Hlen_ret _]]; last lia.
        (* If τ2's Ret is in ts', then τ2 ∈ ts.*1, contradicting fresh. *)
        exfalso.
        apply list_find_Some in Hret_in_ts' as (Hlk_ret & [Heq_τ _] & _).
        simpl in Heq_τ. subst τ_r.
        apply list_elem_of_lookup_2 in Hlk_ret.
        rewrite /ts' in Hlk_ret.
        apply list_elem_of_filter in Hlk_ret as [_ Hin_ts].
        pose proof (tag_in_ts_le_max_tag _ _ _ Hin_ts).
        lia.
      * apply elem_of_app. right. apply elem_of_app. right. apply elem_of_app. left.
        exact Hcall_pop_in_npop2_calls.
      * exists v. split.
        { apply elem_of_app. left. exact Hcall_push_in_ts'. }
        left. apply elem_of_app. right. apply elem_of_app. right.
        apply elem_of_app. right. apply elem_of_app. right.
        rewrite Hcalls_eq in Hret_in_npop2_rets.
        change (encode_response (NonEmpty v)) with (encode_response (NonEmpty v)).
        exact Hret_in_npop2_rets.
Qed.

Lemma close_preserves_wellformed rme valid_value ts m :
  per_tag_wellformed_bag rme valid_value ts →
  valid_match ts m →
  per_tag_wellformed_bag rme valid_value (close_trace ts m).1.
Proof.
  intros Hwf Hvalid τ.
  rewrite /close_trace.
  destruct (unpaired_operations ts m) as [[up upop] ump_init] eqn:Hops.
  destruct (complete_trace_add_match upop m ump_init) as [nm1 ump'] eqn:Hmatch.
  set (calls := extract_calls ts).
  set (np := complete_trace_add_push up).
  set (npop1 := complete_trace_remove_pop upop calls (m ++ nm1)).
  set (U := list_difference upop (m ++ nm1).*2).
  set (ts' := filter (λ x : positive * trace, x.1 ∉ U) ts).
  set (nm2 := close_trace_add_match ump' (max_tag ts.*1 + 1)).
  set (npop2_calls := close_trace_add_pop_calls nm2).
  set (npop2_rets := close_trace_add_pop_rets calls nm2).
  set (npop2 := close_trace_add_pop calls nm2).
  simpl.
  assert (Hupop_is : upop = (unpaired_operations ts m).1.2)
    by (rewrite /unpaired_operations in Hops; by injection Hops as _ <- _).
  assert (Hup_is : up = (unpaired_operations ts m).1.1)
    by (rewrite /unpaired_operations in Hops; by injection Hops as <- _ _).
  assert (Hump_init_is : ump_init = (unpaired_operations ts m).2)
    by (rewrite /unpaired_operations in Hops; by injection Hops as _ _ <-).
  assert (Hupop_nd : NoDup upop)
    by (rewrite Hupop_is; eapply unpaired_pops_nodup; exact Hwf).
  assert (Hnm1_eq : nm1 = (complete_trace_add_match upop m ump_init).1)
    by (rewrite Hmatch; done).
  assert (Hump'_eq : ump' = (complete_trace_add_match upop m ump_init).2)
    by (rewrite Hmatch; done).
  assert (Hump'_sub : ump' ⊆ ump_init).
  { rewrite Hump'_eq. apply complete_trace_add_match_remaining_sub. }
  assert (Hump_init_sub_push : ump_init ⊆ push_of_trace ts).
  { rewrite Hump_init_is /unpaired_operations /=.
    intros τ0 Hin. apply list_elem_of_difference in Hin as [? _]. done. }
  rewrite !filter_app.
  destruct (decide (τ ∈ U)) as [Hτ_U | Hτ_nU].
  { (* τ unmatched unpaired pop: filtered out of ts'; not in any added block. *)
    assert (Hupop_τ : τ ∈ upop)
      by (apply list_elem_of_difference in Hτ_U as [? _]; done).
    assert (Hτ_pop : τ ∈ pop_of_trace ts).
    { rewrite Hupop_is in Hupop_τ. exact (unpaired_pop_is_pop _ m _ Hupop_τ). }
    pose proof (pop_tag_in_trace _ _ Hτ_pop) as Hcall_pop.
    assert (Hτ_npush : τ ∉ push_of_trace ts)
      by (intros ?; eapply push_xor_pop_of_trace; eauto).
    assert (Hτ_nup : τ ∉ up).
    { rewrite Hup_is. eapply pop_tag_not_up; eauto. }
    assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts' = []).
    { apply filter_False_nil, Forall_forall.
      intros [τ' t'] Hin'. simpl. intros ->.
      rewrite /ts' in Hin'.
      apply list_elem_of_filter in Hin' as [Hni _]. simpl in Hni. done. }
    assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
    { apply filter_np_not_in. exact Hτ_nup. }
    assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
    { rewrite /npop1.
      apply (filter_npop1_in_unmatched τ upop calls).
      destruct (find (λ x : positive * positive, bool_decide (x.2 = τ)) (m ++ nm1))
        as [[τ1 τ2]|] eqn:Hfind; last reflexivity.
      exfalso.
      pose proof Hfind as Hfind_copy.
      apply find_some in Hfind_copy as [Hin_pair Hbd].
      apply bool_decide_eq_true_1 in Hbd. simpl in Hbd. subst τ2.
      apply list_elem_of_difference in Hτ_U as [_ Hni]. apply Hni.
      apply (list_elem_of_fmap_2 snd _ (τ1, τ)).
      by apply list_elem_of_In. }
    assert (Hfilt_npop2 : filter (λ x : positive * trace, x.1 = τ) npop2 = []).
    { rewrite /npop2.
      apply (filter_npop2_old_tag τ (Call Pop #()) ts _ calls); last reflexivity.
      exact Hcall_pop. }
    rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
    apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
    rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
    (* Use Hwf τ to get a valid witness. Since τ has Call Pop in ts, it's the pop branch. *)
    destruct (Hwf τ) as [(w & _ & Hpfx) | (r & Hr_ne & _)].
    - exfalso.
      assert (Hin_filt : (τ, Call Pop #()) ∈ filter (λ x, x.1 = τ) ts).
      { apply list_elem_of_filter. done. }
      eapply elem_of_prefix in Hin_filt; last exact Hpfx.
      apply elem_of_cons in Hin_filt as [Habs|Hin_filt].
      + injection Habs as Habs. discriminate.
      + apply elem_of_cons in Hin_filt as [Habs|?]; [discriminate|by set_solver].
    - right. exists r. split; [exact Hr_ne|apply prefix_nil]. }
  (* τ ∉ U *)
  destruct (decide (τ ∈ push_of_trace ts)) as [Hpush | Hnpush].
  { (* τ is a push tag *)
    destruct (push_tag_in_trace _ _ Hpush) as [v Hin_ts].
    (* Get valid_value v from Hwf. *)
    assert (Hvv : valid_value v).
    { destruct (Hwf τ) as [(w & Hvw & Hpfx)|(r & _ & Hpfx)].
      - assert (Hw : w = v).
        { assert (Hin_filt : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts).
          { apply list_elem_of_filter. done. }
          eapply elem_of_prefix in Hin_filt; last exact Hpfx.
          apply elem_of_cons in Hin_filt as [Heq|Hin_filt].
          - injection Heq as Heq. rewrite /encode_response in Heq. by simplify_eq.
          - apply elem_of_cons in Hin_filt as [Habs|?]; [discriminate|by set_solver]. }
        by subst w.
      - exfalso.
        assert (Hin_filt : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts).
        { apply list_elem_of_filter. done. }
        eapply elem_of_prefix in Hin_filt; last exact Hpfx.
        apply elem_of_cons in Hin_filt as [Heq|Hin_filt].
        + injection Heq as Habs. discriminate.
        + apply elem_of_cons in Hin_filt as [Habs|?]; [discriminate|by set_solver]. }
    assert (Hτ_npop : τ ∉ pop_of_trace ts)
      by (intros ?; eapply push_xor_pop_of_trace; eauto).
    assert (Hτ_nupop : τ ∉ upop).
    { rewrite Hupop_is. intros Hin. apply Hτ_npop. exact (unpaired_pop_is_pop _ m _ Hin). }
    assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
    { rewrite /npop1. apply filter_npop1_not_in. exact Hτ_nupop. }
    assert (Hfilt_npop2 : filter (λ x : positive * trace, x.1 = τ) npop2 = []).
    { rewrite /npop2.
      apply (filter_npop2_old_tag τ (Call Push v) ts _ calls); last reflexivity.
      exact Hin_ts. }
    destruct (decide (τ ∈ up)) as [Hin_up | Hnotin_up].
    - (* incomplete push *)
      assert (Hin_up' : τ ∈ (unpaired_operations ts m).1.1) by (rewrite -Hup_is; exact Hin_up).
      assert (Hfilt_ts : filter (λ x : positive * trace, x.1 = τ) ts
                        = [(τ, Call Push v)]).
      { exact (incomplete_push_filter rme valid_value ts m τ v Hwf Hin_ts Hin_up'). }
      assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts'
                          = [(τ, Call Push v)]).
      { rewrite /ts' list_filter_comm. rewrite Hfilt_ts. simpl.
        rewrite filter_cons_True //. }
      assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np
                         = [(τ, Ret #())]).
      { rewrite /np. apply filter_np_in.
        - rewrite Hup_is. eapply unpaired_pushes_nodup. exact Hwf.
        - exact Hin_up. }
      rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
      apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
      rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
      left. exists v. split; [exact Hvv|by exists []; rewrite app_nil_r].
    - (* complete push *)
      assert (Hnotin_up' : τ ∉ (unpaired_operations ts m).1.1) by (rewrite -Hup_is; exact Hnotin_up).
      assert (Hfilt_ts : filter (λ x : positive * trace, x.1 = τ) ts
                        = [(τ, Call Push v); (τ, Ret #())]).
      { exact (complete_push_filter rme valid_value ts m τ v Hwf Hin_ts Hnotin_up'). }
      assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts'
                          = [(τ, Call Push v); (τ, Ret #())]).
      { rewrite /ts' list_filter_comm. rewrite Hfilt_ts. simpl.
        rewrite filter_cons_True //. rewrite filter_cons_True //. }
      assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
      { rewrite /np. apply filter_np_not_in. exact Hnotin_up. }
      rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
      apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
      rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
      left. exists v. split; [exact Hvv|by exists []; rewrite app_nil_r]. }
  destruct (decide (τ ∈ pop_of_trace ts)) as [Hpop | Hnpop].
  { (* τ is a pop tag (and not in U, so matched if unpaired). *)
    pose proof (pop_tag_in_trace _ _ Hpop) as Hin_ts.
    assert (Hτ_nup : τ ∉ up).
    { rewrite Hup_is. eapply pop_tag_not_up; eauto. }
    assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
    { rewrite /np. apply filter_np_not_in. exact Hτ_nup. }
    assert (Hfilt_npop2 : filter (λ x : positive * trace, x.1 = τ) npop2 = []).
    { rewrite /npop2.
      apply (filter_npop2_old_tag τ (Call Pop #()) ts _ calls); last reflexivity.
      exact Hin_ts. }
    destruct (decide (τ ∈ upop)) as [Hin_upop | Hnotin_upop].
    - (* incomplete pop, matched (since τ ∉ U) *)
      assert (Hτ_in_match : τ ∈ (m ++ nm1).*2).
      { destruct (decide (τ ∈ (m ++ nm1).*2)); first done.
        exfalso. apply Hτ_nU. rewrite /U. apply list_elem_of_difference. done. }
      apply list_elem_of_fmap_1 in Hτ_in_match as ([τ1 τ2] & Heq & Hin_pair).
      simpl in Heq. subst τ2.
      assert (Hin_upop' : τ ∈ (unpaired_operations ts m).1.2)
        by (rewrite -Hupop_is; exact Hin_upop).
      assert (Hfilt_ts : filter (λ x : positive * trace, x.1 = τ) ts
                        = [(τ, Call Pop #())]).
      { exact (incomplete_pop_filter rme valid_value ts m τ Hwf Hin_ts Hin_upop'). }
      assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts'
                          = [(τ, Call Pop #())]).
      { rewrite /ts' list_filter_comm. rewrite Hfilt_ts. simpl.
        rewrite filter_cons_True //. }
      (* Get τ1's Call Push v. *)
      assert (Hτ1_call : ∃ v, (τ1, Call Push v) ∈ ts).
      { rewrite elem_of_app in Hin_pair.
        destruct Hin_pair as [Hin_m|Hin_nm1].
        - destruct (valid_match_call_push _ _ _ _ Hvalid Hin_m) as [v ?]. by exists v.
        - assert (Hτ1_in_init : τ1 ∈ ump_init).
          { assert (Hsub : nm1.*1 ⊆ ump_init).
            { assert (Heq : nm1 = (complete_trace_add_match upop m ump_init).1)
                by (rewrite Hmatch; done).
              rewrite Heq. apply complete_trace_add_match_fst_sub. }
            apply Hsub.
            apply (list_elem_of_fmap_2 fst _ (τ1, τ)). exact Hin_nm1. }
          apply Hump_init_sub_push, push_tag_in_trace in Hτ1_in_init. exact Hτ1_in_init. }
      destruct Hτ1_call as [vp Hτ1_in_ts].
      assert (Hcalls_τ1 : ret_val_of_call (calls !!! τ1) = encode_response (NonEmpty vp)).
      { rewrite /calls (extract_calls_lookup _ _ ts τ1 _ _ Hwf Hτ1_in_ts). done. }
      (* Find for τ in m ++ nm1 returns Some (τ1', _) for some τ1' (NoDup gives τ1' = τ1). *)
      assert (Hfind : find (λ x : positive * positive, bool_decide (x.2 = τ)) (m ++ nm1) = Some (τ1, τ)).
      { destruct (find_some_elem (λ x : positive * positive, bool_decide (x.2 = τ)) (m ++ nm1) (τ1, τ) Hin_pair) as [y Hy].
        - apply bool_decide_eq_true_2. done.
        - apply find_some in Hy as Hy_copy. destruct Hy_copy as [Hin_y Hbd_y].
          apply bool_decide_eq_true_1 in Hbd_y.
          destruct y as [τ1' τ2']. simpl in Hbd_y. subst τ2'.
          assert (Hnd : NoDup (m ++ nm1).*2).
          { rewrite fmap_app. apply NoDup_app. split_and!.
            - destruct Hvalid as (_ & [_ ?] & _). done.
            - intros τx Hin1 Hin2.
              apply (complete_trace_add_match_nm1_not_in_m0 upop m ump_init τx);
                [by rewrite -Hnm1_eq | exact Hin1].
            - rewrite Hnm1_eq. apply complete_trace_add_match_snd_nodup. exact Hupop_nd. }
          assert (Heq : τ1' = τ1).
          { apply list_elem_of_In in Hin_y.
            apply list_elem_of_lookup_1 in Hin_y as [i Hi].
            apply list_elem_of_lookup_1 in Hin_pair as [j Hj].
            assert (Hij : i = j).
            { apply (proj1 (NoDup_alt _) Hnd i j τ).
              - rewrite list_lookup_fmap Hi. done.
              - rewrite list_lookup_fmap Hj. done. }
            subst j. rewrite Hi in Hj. by injection Hj. }
          subst τ1'. exact Hy. }
      assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1
                            = [(τ, Ret (encode_response (NonEmpty vp)))]).
      { rewrite -Hcalls_τ1.
        rewrite /npop1.
        exact (filter_npop1_in_exact τ τ1 upop calls (m ++ nm1) Hupop_nd Hin_upop Hfind). }
      rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
      apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
      rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
      right. exists (NonEmpty vp). split.
      + by destruct rme.
      + change (encode_response (NonEmpty vp)) with (encode_response (NonEmpty vp)).
        by exists []; rewrite app_nil_r.
    - (* complete pop *)
      assert (Hnotin_upop' : τ ∉ (unpaired_operations ts m).1.2)
        by (rewrite -Hupop_is; exact Hnotin_upop).
      destruct (complete_pop_filter_wf rme valid_value ts m τ Hwf Hin_ts Hnotin_upop')
        as [r [Hr_ne Hfilt_ts]].
      assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts'
                          = [(τ, Call Pop #()); (τ, Ret (encode_response r))]).
      { rewrite /ts' list_filter_comm. rewrite Hfilt_ts. simpl.
        rewrite filter_cons_True //. rewrite filter_cons_True //. }
      assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
      { rewrite /npop1. apply filter_npop1_not_in. exact Hnotin_upop. }
      rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
      apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
      rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
      right. exists r. split; [exact Hr_ne|by exists []; rewrite app_nil_r]. }
  (* τ neither push nor pop in ts *)
  destruct (decide (τ ∈ nm2.*2)) as [Hin_nm2 | Hnotin_nm2].
  { assert (Hex : ∃ τ1, (τ1, τ) ∈ nm2).
    { apply list_elem_of_fmap_1 in Hin_nm2 as ([τ1' τ2'] & Heq & Hin).
      simpl in Heq. subst τ2'. exists τ1'. exact Hin. }
    assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts' = []).
    { apply filter_False_nil, Forall_forall.
      intros [τ' t'] Hin'. simpl. intros ->.
      rewrite /ts' in Hin'.
      apply list_elem_of_filter in Hin' as [_ Hin_ts].
      destruct Hex as [τ1 Hnm2_in].
      apply close_trace_add_match_tags_fresh in Hnm2_in.
      pose proof (tag_in_ts_le_max_tag _ _ _ Hin_ts). lia. }
    assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
    { rewrite /np. apply filter_np_not_in.
      intros Hin. apply Hnpush. rewrite Hup_is in Hin.
      exact (unpaired_push_is_push _ m _ Hin). }
    assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
    { rewrite /npop1. apply filter_npop1_not_in.
      intros Hin. apply Hnpop. rewrite Hupop_is in Hin.
      exact (unpaired_pop_is_pop _ m _ Hin). }
    (* Get τ1's Push v call. *)
    destruct Hex as [τ1 Hin_nm2'].
    assert (Hτ1_in_ump' : τ1 ∈ ump').
    { assert (Heq : nm2.*1 = ump').
      { rewrite /nm2. apply close_trace_add_match_fst. }
      rewrite -Heq. apply (list_elem_of_fmap_2 fst _ (τ1, τ)). exact Hin_nm2'. }
    assert (Hτ1_in_init : τ1 ∈ ump_init) by exact (Hump'_sub _ Hτ1_in_ump').
    assert (Hτ1_push : τ1 ∈ push_of_trace ts) by exact (Hump_init_sub_push _ Hτ1_in_init).
    destruct (push_tag_in_trace _ _ Hτ1_push) as [vp Hτ1_in_ts].
    assert (Hcalls_τ1 : ret_val_of_call (calls !!! τ1) = encode_response (NonEmpty vp)).
    { rewrite /calls (extract_calls_lookup _ _ ts τ1 _ _ Hwf Hτ1_in_ts). done. }
    assert (Hnm2_nd : NoDup nm2.*2).
    { rewrite /nm2. apply close_trace_add_match_snd_nodup. }
    assert (Hfilt_npop2_calls : filter (λ x : positive * trace, x.1 = τ) npop2_calls
                          = [(τ, Call Pop #())]).
    { rewrite /npop2_calls.
      exact (filter_calls_of_close_trace_add_pop_in_exact τ τ1 nm2 Hnm2_nd Hin_nm2'). }
    assert (Hfilt_npop2_rets : filter (λ x : positive * trace, x.1 = τ) npop2_rets
                          = [(τ, Ret (ret_val_of_call (calls !!! τ1)))]).
    { rewrite /npop2_rets.
      exact (filter_rets_of_close_trace_add_pop_in_exact τ τ1 calls nm2 Hnm2_nd Hin_nm2'). }
    rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets Hcalls_τ1.
    right. exists (NonEmpty vp). split.
    - by destruct rme.
    - change (encode_response (NonEmpty vp)) with (encode_response (NonEmpty vp)).
      by exists []; rewrite app_nil_r. }
  (* τ absent from everything *)
  assert (Hfilt_ts : filter (λ x : positive * trace, x.1 = τ) ts = []).
  { apply filter_False_nil, Forall_forall.
    intros [τ' t'] Hin. simpl. intros ->.
    destruct (Hwf τ) as [(v & _ & Hpfx) | (r & _ & Hpfx)].
    - apply Hnpush.
      assert (Hin_filt : (τ, t') ∈ filter (λ x, x.1 = τ) ts)
        by (apply list_elem_of_filter; done).
      destruct (filter (λ x, x.1 = τ) ts) as [|x xs] eqn:Heq; first by set_solver.
      apply prefix_cons_inv_1 in Hpfx as Hx. subst x.
      apply (list_elem_of_fmap_2 fst _ (τ, Call Push v)).
      apply list_elem_of_filter; split; [eexists; done|].
      assert (Hin_call : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts)
        by (rewrite Heq; set_solver).
      by apply list_elem_of_filter in Hin_call as [_ ?].
    - apply Hnpop.
      assert (Hin_filt : (τ, t') ∈ filter (λ x, x.1 = τ) ts)
        by (apply list_elem_of_filter; done).
      destruct (filter (λ x, x.1 = τ) ts) as [|x xs] eqn:Heq; first by set_solver.
      apply prefix_cons_inv_1 in Hpfx as Hx. subst x.
      apply (list_elem_of_fmap_2 fst _ (τ, Call Pop #())).
      apply list_elem_of_filter; split; [done|].
      assert (Hin_call : (τ, Call Pop #()) ∈ filter (λ x, x.1 = τ) ts)
        by (rewrite Heq; set_solver).
      by apply list_elem_of_filter in Hin_call as [_ ?]. }
  assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts' = []).
  { rewrite /ts' list_filter_comm Hfilt_ts. by rewrite filter_nil. }
  assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
  { rewrite /np. apply filter_np_not_in.
    intros Hin. apply Hnpush. rewrite Hup_is in Hin.
    exact (unpaired_push_is_push _ m _ Hin). }
  assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
  { rewrite /npop1. apply filter_npop1_not_in.
    intros Hin. apply Hnpop. rewrite Hupop_is in Hin.
    exact (unpaired_pop_is_pop _ m _ Hin). }
  assert (Hfilt_npop2 : filter (λ x : positive * trace, x.1 = τ) npop2 = []).
  { rewrite /npop2. apply filter_close_trace_add_pop_not_in. exact Hnotin_nm2. }
  rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
  apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
  rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
  destruct (Hwf τ) as [(v & Hvv & _)|(r & Hr_ne & _)].
  - left. exists v. split; [exact Hvv|apply prefix_nil].
  - right. exists r. split; [exact Hr_ne|apply prefix_nil].
Qed.

Local Lemma ret_of_tag_app_prefix ts0 rest τ i x :
  ret_of_tag ts0 τ = Some (i, x) →
  ret_of_tag (ts0 ++ rest) τ = Some (i, x).
Proof.
  rewrite /ret_of_tag. intros H. rewrite list_find_app_Some. left. exact H.
Qed.

Local Lemma call_of_tag_app_prefix ts0 rest τ i x :
  call_of_tag ts0 τ = Some (i, x) →
  call_of_tag (ts0 ++ rest) τ = Some (i, x).
Proof.
  rewrite /call_of_tag. intros H. rewrite list_find_app_Some. left. exact H.
Qed.

Local Lemma push_pop_covers_app_prefix ts0 rest τ1 τ2 i :
  push_pop_covers ts0 τ1 τ2 i →
  push_pop_covers (ts0 ++ rest) τ1 τ2 i.
Proof.
  rewrite /push_pop_covers.
  destruct (ret_of_tag ts0 τ1) as [[ir tr]|] eqn:Hr; simpl; [|done].
  destruct (call_of_tag ts0 τ2) as [[ic tc]|] eqn:Hc; simpl; [|done].
  intros Hcov.
  rewrite (ret_of_tag_app_prefix _ rest _ _ _ Hr). simpl.
  rewrite (call_of_tag_app_prefix _ rest _ _ _ Hc). simpl.
  exact Hcov.
Qed.

Local Lemma dangling_push_covers_app_prefix ts0 rest τ1 i :
  dangling_push_covers ts0 τ1 i →
  dangling_push_covers (ts0 ++ rest) τ1 i.
Proof.
  rewrite /dangling_push_covers.
  destruct (ret_of_tag ts0 τ1) as [[ir tr]|] eqn:Hr; simpl; [|done].
  intros Hcov.
  rewrite (ret_of_tag_app_prefix _ rest _ _ _ Hr). simpl. exact Hcov.
Qed.

(* Key lemma: when a pop gets IsEmpty in npop1, find returned Some matching push
   whose recorded call value is IsEmpty. (In the previous design, find=None could
   also produce IsEmpty; the new [complete_trace_remove_pop] omits unmatched pops
   entirely, so only the Some case remains.) *)
Local Lemma npop1_is_empty_find τ upop calls0 m_nm :
  (τ, Ret (encode_response IsEmpty)) ∈ complete_trace_remove_pop upop calls0 m_nm →
  ∃ τ1, find (λ x : positive * positive, bool_decide (x.2 = τ)) m_nm = Some (τ1, τ)
           ∧ ret_val_of_call (calls0 !!! τ1) = encode_response IsEmpty.
Proof.
  rewrite /complete_trace_remove_pop.
  intros Hin. apply list_elem_of_omap in Hin as (τ2 & Hin_upop & Heq).
  destruct (find (λ x : positive * positive, bool_decide (x.2 = τ2)) m_nm) as [[τ1 p2]|] eqn:Hfind;
    last discriminate.
  injection Heq as Hτ Hrv. subst τ.
  pose proof (Hfind_copy := Hfind).
  apply find_some in Hfind_copy as [_ Hbd]. apply bool_decide_eq_true_1 in Hbd. simpl in Hbd. subst p2.
  exists τ1. split; [exact Hfind|]. by simplify_eq.
Qed.

(* When a pop's find in m ++ nm1 returns None, τ ∉ nm1.*2 *)
Local Lemma find_none_not_in_snd {A} (τ : positive) (l : list (A * positive)) :
  find (λ x : A * positive, bool_decide (x.2 = τ)) l = None →
  τ ∉ l.*2.
Proof.
  intros Hfind Hin.
  apply list_elem_of_fmap_1 in Hin as ([a b] & Heq & Hin_l).
  simpl in Heq. subst b.
  assert (Hex : ∃ y, find (λ x : A * positive, bool_decide (x.2 = τ)) l = Some y).
  { eapply find_some_elem; first exact Hin_l.
    apply bool_decide_eq_true_2. done. }
  destruct Hex as [y Hy]. rewrite Hy in Hfind. discriminate.
Qed.

(* Helper: complete_trace_add_match with empty ump always returns empty .2 *)
Local Lemma complete_trace_add_match_nil_ump upop m0 :
  (complete_trace_add_match upop m0 []).2 = [].
Proof.
  induction upop as [|τ2 upop IH]; first done.
  simpl. destruct (find _ m0) as [?|].
  - exact IH.
  - exact IH.
Qed.

(* Helper: if τ2 in nm1.*2, then τ2 appears in the result after processing τ2 *)
Local Lemma complete_trace_add_match_self_in upop m0 ump τ2 :
  find (λ x : positive * positive, bool_decide (x.2 = τ2)) m0 = None →
  ump ≠ [] →
  τ2 ∈ (complete_trace_add_match (τ2 :: upop) m0 ump).1.*2.
Proof.
  intros Hfind_none Hne.
  simpl. rewrite Hfind_none.
  destruct ump as [|τ1 ump']; first done.
  destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
  simpl. set_solver.
Qed.

(* Key structural lemma: if τ ∈ upop and τ ∉ nm1.*2, then when
   complete_trace_add_match processed τ, ump was already empty.
   Hence ump' = []. *)
Local Lemma complete_trace_add_match_unmatched_empty upop m0 ump τ :
  τ ∈ upop →
  find (λ x : positive * positive, bool_decide (x.2 = τ)) m0 = None →
  τ ∉ (complete_trace_add_match upop m0 ump).1.*2 →
  (complete_trace_add_match upop m0 ump).2 = [].
Proof.
  revert ump. induction upop as [|τ2 upop IH]; first by set_solver.
  intros ump Hin Hfind_m0 Hnotin.
  apply elem_of_cons in Hin as [->|Hin].
  - (* τ = τ2: this is the pop being processed *)
    simpl in Hnotin |- *. rewrite Hfind_m0 in Hnotin |- *.
    destruct ump as [|τ1 ump'].
    + (* ump = []: recursive call with [] *)
      apply complete_trace_add_match_nil_ump.
    + (* ump = τ1 :: ump': τ2 is matched in nm1 *)
      exfalso. apply Hnotin.
      destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''].
      simpl. set_solver.
  - (* τ ∈ upop: τ2 is processed first *)
    simpl in Hnotin |- *.
    destruct (find (λ x, bool_decide (x.2 = τ2)) m0) as [?|].
    + (* τ2 found in m0: skip, recurse *)
      exact (IH ump Hin Hfind_m0 Hnotin).
    + (* τ2 not in m0 *)
      destruct ump as [|τ1 ump'].
      * (* ump empty: recurse with [] *)
        exact (IH [] Hin Hfind_m0 Hnotin).
      * (* ump = τ1 :: ump': τ2 matches τ1 *)
        destruct (complete_trace_add_match upop m0 ump') as [nm1' ump''] eqn:Hrec.
        simpl in Hnotin |- *.
        assert (Hnotin' : τ ∉ (complete_trace_add_match upop m0 ump').1.*2).
        { rewrite Hrec. simpl. intros Hin'. apply Hnotin. set_solver. }
        assert (H := IH ump' Hin Hfind_m0 Hnotin').
        rewrite Hrec in H. simpl in H. exact H.
Qed.

(* No new push Calls in np, npop1, npop2 *)
Local Lemma no_push_call_in_np τ v up :
  (τ, Call Push v) ∉ complete_trace_add_push up.
Proof.
  intros Hin. apply complete_trace_add_push_elem in Hin as [Heq _]. discriminate.
Qed.

Local Lemma no_push_call_in_npop1 τ v upop calls m0 :
  (τ, Call Push v) ∉ complete_trace_remove_pop upop calls m0.
Proof.
  intros Hin. apply complete_trace_remove_pop_elem in Hin as [Hret _].
  simpl in Hret. done.
Qed.

Local Lemma no_push_call_in_npop2 τ v calls m_add :
  (τ, Call Push v) ∉ close_trace_add_pop calls m_add.
Proof.
  intros Hin.
  apply close_trace_add_pop_structure in Hin as [Heq|[τ1 [_ Heq]]]; discriminate.
Qed.

Local Lemma push_of_trace_ext ts0 rest :
  (∀ τ v, (τ, Call Push v) ∉ rest) →
  push_of_trace (ts0 ++ rest) = push_of_trace ts0.
Proof.
  intros Hno_push.
  rewrite /push_of_trace filter_app.
  assert (Hnil : filter (is_call_push ∘ snd) rest = []).
  { apply filter_False_nil, Forall_forall. intros [τ' t'] Hin. simpl. intros [v ->].
    exact (Hno_push τ' v Hin). }
  rewrite Hnil app_nil_r. done.
Qed.

(* Helper: ret_of_tag not found in ts means not found in ts for that tag *)
Local Lemma ret_of_tag_none_no_ret ts0 τ :
  ret_of_tag ts0 τ = None →
  ∀ v, (τ, Ret v) ∉ ts0.
Proof.
  intros Hnone v Hin.
  apply list_find_None in Hnone.
  rewrite Forall_forall in Hnone.
  apply list_elem_of_lookup_1 in Hin as [i Hi].
  specialize (Hnone _ (list_elem_of_lookup_2 _ _ _ Hi)).
  simpl in Hnone. apply Hnone. done.
Qed.

(* Helper: ret_of_tag ts_ext τ1 when τ1's Ret is not in ts but in np *)
Local Lemma ret_of_tag_not_in_ts_ge ts0 rest τ1 :
  ret_of_tag ts0 τ1 = None →
  ∀ i x, ret_of_tag (ts0 ++ rest) τ1 = Some (i, x) → i ≥ length ts0.
Proof.
  intros Hnone i x Hfind.
  rewrite /ret_of_tag list_find_app_Some in Hfind.
  destruct Hfind as [Hts|[Hlen [_ Hrest]]].
  - rewrite /ret_of_tag in Hnone. rewrite Hnone in Hts. discriminate.
  - lia.
Qed.

(* Position-mapping helper: for τ ∉ U with ts !! k = Some (τ, ev), the
   filtered trace has the same entry at position [φ_pos U ts k]. *)
Local Definition φ_pos (U : list positive) (ts : list (positive * trace)) (k : nat) : nat :=
  length (filter (λ x : positive * trace, x.1 ∉ U) (take k ts)).

Local Lemma φ_pos_lookup U ts k τ ev :
  ts !! k = Some (τ, ev) → τ ∉ U →
  filter (λ x : positive * trace, x.1 ∉ U) ts !! (φ_pos U ts k) = Some (τ, ev).
Proof.
  intros Hlk Hni.
  rewrite /φ_pos.
  rewrite -{2}(take_drop k ts).
  rewrite filter_app.
  rewrite lookup_app_r; last done.
  rewrite Nat.sub_diag.
  erewrite drop_S; last exact Hlk.
  rewrite filter_cons_True //.
Qed.

Local Lemma φ_pos_monotone U ts k1 k2 :
  k1 ≤ k2 → φ_pos U ts k1 ≤ φ_pos U ts k2.
Proof.
  intros Hle. rewrite /φ_pos.
  replace k2 with (k1 + (k2 - k1)) by lia.
  rewrite -take_take_drop.
  rewrite filter_app length_app. lia.
Qed.

Local Lemma φ_pos_succ_preserved U ts k τ ev :
  ts !! k = Some (τ, ev) → τ ∉ U →
  φ_pos U ts (Datatypes.S k) = φ_pos U ts k + 1.
Proof.
  intros Hlk Hni.
  rewrite /φ_pos.
  erewrite take_S_r; last exact Hlk.
  rewrite filter_app length_app.
  rewrite filter_cons_True //=.
Qed.

Local Lemma φ_pos_strict U ts k1 k2 τ ev :
  k1 < k2 → ts !! k1 = Some (τ, ev) → τ ∉ U →
  φ_pos U ts k1 < φ_pos U ts k2.
Proof.
  intros Hlt Hlk Hni.
  pose proof (φ_pos_succ_preserved U ts k1 τ ev Hlk Hni) as Heq.
  pose proof (φ_pos_monotone U ts (Datatypes.S k1) k2 Hlt) as Hle.
  lia.
Qed.

(* Reverse: φ_pos a < φ_pos b → a < b (since φ_pos is non-decreasing). *)
Local Lemma φ_pos_lt_inv U ts k1 k2 :
  φ_pos U ts k1 < φ_pos U ts k2 → k1 < k2.
Proof.
  intros Hlt.
  destruct (decide (k1 < k2)) as [|]; first done.
  exfalso. assert (k2 ≤ k1) by lia.
  pose proof (φ_pos_monotone U ts k2 k1) as Hle. lia.
Qed.

(* Bound: φ_pos U ts k ≤ length (filter (∉ U) ts). *)
Local Lemma φ_pos_bound U ts k :
  φ_pos U ts k ≤ length (filter (λ x : positive * trace, x.1 ∉ U) ts).
Proof.
  rewrite /φ_pos.
  rewrite -{2}(take_drop k ts) filter_app length_app. lia.
Qed.

(* Inverse: every position in ts' = filter (∉ U) ts comes from some preserved position in ts. *)
Local Lemma φ_pos_inv_lookup U ts n y :
  filter (λ x : positive * trace, x.1 ∉ U) ts !! n = Some y →
  ∃ k, ts !! k = Some y ∧ φ_pos U ts k = n ∧ y.1 ∉ U.
Proof.
  revert n. induction ts as [|x ts IH]; intros n; first done.
  rewrite filter_cons. destruct (decide (x.1 ∉ U)) as [Hni|Hin].
  - destruct n as [|n']; simpl; intros Hlk.
    + injection Hlk as <-. exists 0. split_and!; [done|done|exact Hni].
    + destruct (IH n' Hlk) as (k & Hk_lk & Hk_φ & Hk_ni).
      exists (Datatypes.S k). split_and!; [done| |exact Hk_ni].
      rewrite /φ_pos. simpl.
      rewrite filter_cons_True; last exact Hni.
      simpl. by f_equal.
  - intros Hlk.
    destruct (IH n Hlk) as (k & Hk_lk & Hk_φ & Hk_ni).
    exists (Datatypes.S k). split_and!; [done| |exact Hk_ni].
    rewrite /φ_pos. simpl.
    rewrite filter_cons_False; last exact Hin.
    exact Hk_φ.
Qed.

Lemma close_preserves_pop_empty_sound rme valid_value ts m :
  per_tag_wellformed_bag rme valid_value ts →
  per_tag_pop_empty_sound ts m →
  valid_match ts m →
  per_tag_pop_empty_sound (close_trace ts m).1 (close_trace ts m).2.
Proof.
  intros Hwf Hps Hvalid.
  pose proof Hvalid as Hvalid'.
  destruct Hvalid as (Hcov & [Hnd_m1 Hnd_m2] & Hforall).
  intros τ' Hτ'_in.
  rewrite /close_trace in Hτ'_in |- *.
  destruct (unpaired_operations ts m) as [[up upop] ump_init] eqn:Hops.
  destruct (complete_trace_add_match upop m ump_init) as [nm1 ump'] eqn:Hmatch.
  set (calls := extract_calls ts).
  set (np := complete_trace_add_push up).
  set (npop1 := complete_trace_remove_pop upop calls (m ++ nm1)).
  set (U := list_difference upop (m ++ nm1).*2).
  set (ts' := filter (λ x : positive * trace, x.1 ∉ U) ts).
  set (nm2 := close_trace_add_match ump' (max_tag ts.*1 + 1)).
  set (npop2_calls := close_trace_add_pop_calls nm2).
  set (npop2_rets := close_trace_add_pop_rets calls nm2).
  set (npop2 := close_trace_add_pop calls nm2).
  simpl in Hτ'_in |- *.
  (* Setup *)
  assert (Hupop_is : upop = (unpaired_operations ts m).1.2)
    by (rewrite /unpaired_operations in Hops; by injection Hops as _ <- _).
  assert (Hump_init_is : ump_init = (unpaired_operations ts m).2)
    by (rewrite /unpaired_operations in Hops; by injection Hops as _ _ <-).
  assert (Hupop_nd : NoDup upop)
    by (rewrite Hupop_is; eapply unpaired_pops_nodup; exact Hwf).
  assert (Hupop_sub : upop ⊆ pop_of_trace ts).
  { rewrite Hupop_is. intros τ Hin. by eapply unpaired_pop_is_pop. }
  assert (Hnm1_snd_sub : nm1.*2 ⊆ upop).
  { assert (Heq : nm1 = (complete_trace_add_match upop m ump_init).1)
      by (rewrite Hmatch; done).
    rewrite Heq. apply complete_trace_add_match_snd_sub. }
  assert (Hnm1_fst_sub : nm1.*1 ⊆ ump_init).
  { assert (Heq : nm1 = (complete_trace_add_match upop m ump_init).1)
      by (rewrite Hmatch; done).
    rewrite Heq. apply complete_trace_add_match_fst_sub. }
  assert (Hump_init_sub_push : ump_init ⊆ push_of_trace ts).
  { rewrite Hump_init_is /unpaired_operations /=.
    intros τ Hin. apply list_elem_of_difference in Hin as [? _]. done. }
  assert (Hump_init_disj_m1 : ∀ τ, τ ∈ ump_init → τ ∉ m.*1).
  { rewrite Hump_init_is /unpaired_operations /=.
    intros τ Hin Hin_m1.
    apply list_elem_of_difference in Hin as [_ Hni]. by apply Hni. }
  assert (Hnm1_fst_sub_push : nm1.*1 ⊆ push_of_trace ts).
  { etrans; eassumption. }
  assert (Hump'_sub : ump' ⊆ ump_init).
  { assert (Heq : ump' = (complete_trace_add_match upop m ump_init).2)
      by (rewrite Hmatch; done).
    rewrite Heq. apply complete_trace_add_match_remaining_sub. }
  assert (Hnm2_fst : nm2.*1 = ump').
  { rewrite /nm2. apply close_trace_add_match_fst. }
  assert (Hpush_not_U : ∀ τ, τ ∈ push_of_trace ts → τ ∉ U).
  { intros τ Hin Hni. apply list_elem_of_difference in Hni as [Hin_upop _].
    apply (push_xor_pop_of_trace ts rme valid_value τ Hwf Hin).
    by apply Hupop_sub. }
  (* Step 1: extract τ''s Ret IsEmpty entry from close_trace into ts. *)
  apply list_elem_of_fmap_1 in Hτ'_in as ([τ_p t_p] & Heq & Hin_filt).
  simpl in Heq. subst τ_p.
  apply list_elem_of_filter in Hin_filt as [Hev_pop_emp Hin_close].
  rewrite /is_ret_pop_emp in Hev_pop_emp. simpl in Hev_pop_emp. subst t_p.
  rewrite -/ts' -/np -/npop2_calls -/npop1 -/npop2_rets in Hin_close.
  (* Each part of close_trace: only ts' can contain (τ', Ret IsEmpty). *)
  assert (Hin_ts : (τ', Ret (encode_response IsEmpty)) ∈ ts).
  { apply elem_of_app in Hin_close as [Hin_ts'|Hin_rest].
    - rewrite /ts' in Hin_ts'.
      apply list_elem_of_filter in Hin_ts' as [_ ?]. done.
    - exfalso.
      apply elem_of_app in Hin_rest as [Hin_np|Hin_rest].
      { apply complete_trace_add_push_elem in Hin_np as [Habs _]. discriminate. }
      apply elem_of_app in Hin_rest as [Hin_npop2_calls|Hin_rest].
      { rewrite /npop2_calls /close_trace_add_pop_calls in Hin_npop2_calls.
        apply list_elem_of_fmap in Hin_npop2_calls as ([τ1 τ2] & Heq & _).
        injection Heq as _ Habs. discriminate. }
      apply elem_of_app in Hin_rest as [Hin_npop1|Hin_npop2_rets].
      + rewrite /npop1 /complete_trace_remove_pop list_elem_of_omap in Hin_npop1.
        destruct Hin_npop1 as (τ_x & _ & Hopt).
        destruct (find (λ x : positive * positive, bool_decide (x.2 = τ_x)) (m ++ nm1))
          as [[τ1 τ2]|] eqn:Hfind; last discriminate.
        injection Hopt as _ Hev.
        apply find_some in Hfind as [Hin_pair _].
        apply list_elem_of_In in Hin_pair.
        rewrite elem_of_app in Hin_pair.
        assert (Hpush : ∃ v, (τ1, Call Push v) ∈ ts).
        { destruct Hin_pair as [Hin_m|Hin_nm1].
          - destruct (valid_match_call_push _ _ _ _ Hvalid' Hin_m) as [v ?].
            by exists v.
          - assert (Hin1 : τ1 ∈ ump_init).
            { apply Hnm1_fst_sub.
              apply (list_elem_of_fmap_2 fst _ (τ1, τ2)). exact Hin_nm1. }
            apply push_tag_in_trace. by apply Hump_init_sub_push. }
        destruct Hpush as [v Hcall_push].
        assert (Hcalls_eq : ret_val_of_call (calls !!! τ1) = encode_response (NonEmpty v)).
        { rewrite /calls (extract_calls_lookup _ _ ts τ1 _ _ Hwf Hcall_push). done. }
        rewrite Hcalls_eq /= in Hev. discriminate.
      + rewrite /npop2_rets /close_trace_add_pop_rets in Hin_npop2_rets.
        apply list_elem_of_fmap in Hin_npop2_rets as ([τ1 τ2] & Heq & Hin_nm2).
        injection Heq as _ Hev.
        assert (Hτ1_in_ump' : τ1 ∈ ump').
        { assert (H : nm2.*1 = ump').
          { rewrite /nm2. apply close_trace_add_match_fst. }
          rewrite -H. apply (list_elem_of_fmap_2 fst _ (τ1, τ2)). exact Hin_nm2. }
        assert (Hτ1_in_ump_init : τ1 ∈ ump_init).
        { assert (Hsub : ump' ⊆ ump_init).
          { assert (Heq : ump' = (complete_trace_add_match upop m ump_init).2)
              by (rewrite Hmatch; done).
            rewrite Heq. apply complete_trace_add_match_remaining_sub. }
          by apply Hsub. }
        rewrite Hump_init_is /unpaired_operations /= in Hτ1_in_ump_init.
        apply list_elem_of_difference in Hτ1_in_ump_init as [Hτ1_push _].
        destruct (push_tag_in_trace _ _ Hτ1_push) as [v Hcall_push].
        assert (Hcalls_eq : ret_val_of_call (calls !!! τ1) = encode_response (NonEmpty v)).
        { rewrite /calls (extract_calls_lookup _ _ ts τ1 _ _ Hwf Hcall_push). done. }
        rewrite Hcalls_eq /= in Hev. discriminate. }
  (* τ' ∉ U since τ' has Ret in ts (not in upop = call ∖ ret pops) *)
  assert (Hτ'_not_U : τ' ∉ U).
  { intros Hin. apply list_elem_of_difference in Hin as [Hin_upop _].
    rewrite Hupop_is /unpaired_operations /= in Hin_upop.
    apply list_elem_of_difference in Hin_upop as [_ Hno_ret].
    apply Hno_ret.
    apply (list_elem_of_fmap_2 fst _ (τ', Ret (encode_response IsEmpty))).
    apply list_elem_of_filter; split; [eexists; reflexivity|exact Hin_ts]. }
  (* Step 2: get original witness from Hps *)
  assert (Hτ'_in_orig : τ' ∈ (filter (is_ret_pop_emp ∘ snd) ts).*1).
  { apply (list_elem_of_fmap_2 fst _ (τ', Ret (encode_response IsEmpty))).
    apply list_elem_of_filter; split; [done|exact Hin_ts]. }
  destruct (Hps τ' Hτ'_in_orig)
    as (icall_o & iret_o & i_o & Hcall_lkp & Hret_lkp & Hi_le & Hno_match & Hno_dangling).
  (* Step 3: lift positions to close_trace via φ_pos U ts. *)
  set (icall_c := φ_pos U ts icall_o).
  set (iret_c := φ_pos U ts iret_o).
  set (i_c := φ_pos U ts i_o).
  exists icall_c, iret_c, i_c.
  (* Subgoals *)
  assert (Hicall_ni : (icall_o, (τ', Call Pop #())).2.1 ∉ U).
  { simpl. exact Hτ'_not_U. }
  assert (Hcall_close : ts' !! icall_c = Some (τ', Call Pop #())).
  { rewrite /icall_c. apply (φ_pos_lookup U ts icall_o τ').
    - exact Hcall_lkp.
    - exact Hτ'_not_U. }
  assert (Hret_close : ts' !! iret_c = Some (τ', Ret (encode_response IsEmpty))).
  { rewrite /iret_c. apply (φ_pos_lookup U ts iret_o τ').
    - exact Hret_lkp.
    - exact Hτ'_not_U. }
  assert (Hicall_lt : icall_c < length ts').
  { apply lookup_lt_Some in Hcall_close. exact Hcall_close. }
  assert (Hiret_lt : iret_c < length ts').
  { apply lookup_lt_Some in Hret_close. exact Hret_close. }
  destruct Hi_le as [Hicall_le_i Hi_le_iret].
  split_and!.
  - (* close_trace.1 !! icall_c = (τ', Call Pop) *)
    rewrite /ts' in Hcall_close.
    by apply lookup_app_l_Some.
  - rewrite /ts' in Hret_close.
    by apply lookup_app_l_Some.
  - rewrite /icall_c /i_c. by apply φ_pos_monotone.
  - rewrite /i_c /iret_c. by apply φ_pos_monotone.
  - (* push_pop_covers: ¬covers for all (τ1, τ2) ∈ m++nm1++nm2 at i_c. *)
    intros τ1 τ2 Hin_pair Hcover.
    (* Establish τ1 is a push tag in ts (and τ1 ∉ U). *)
    assert (Hτ1_call : ∃ v, (τ1, Call Push v) ∈ ts).
    { rewrite !elem_of_app in Hin_pair.
      destruct Hin_pair as [Hin_m | [Hin_nm1 | Hin_nm2]].
      - destruct (valid_match_call_push _ _ _ _ Hvalid' Hin_m) as [v ?]. by exists v.
      - assert (Hτ1_in_init : τ1 ∈ ump_init).
        { apply Hnm1_fst_sub.
          apply (list_elem_of_fmap_2 fst _ (τ1, τ2)). exact Hin_nm1. }
        apply Hump_init_sub_push, push_tag_in_trace in Hτ1_in_init. exact Hτ1_in_init.
      - assert (Hτ1_in_ump' : τ1 ∈ ump').
        { rewrite -Hnm2_fst.
          apply (list_elem_of_fmap_2 fst _ (τ1, τ2)). exact Hin_nm2. }
        apply Hump'_sub, Hump_init_sub_push, push_tag_in_trace in Hτ1_in_ump'.
        exact Hτ1_in_ump'. }
    destruct Hτ1_call as [v Hτ1_in_ts].
    assert (Hτ1_push : τ1 ∈ push_of_trace ts).
    { apply (list_elem_of_fmap_2 fst _ (τ1, Call Push v)).
      apply list_elem_of_filter; split; [eexists; reflexivity|exact Hτ1_in_ts]. }
    assert (Hτ1_not_U : τ1 ∉ U) by exact (Hpush_not_U _ Hτ1_push).
    rewrite /push_pop_covers in Hcover.
    destruct (ret_of_tag _ τ1) as [[ir1 [τ_r tr1]]|] eqn:Hr1_close;
      simpl in Hcover; last done.
    destruct (call_of_tag _ τ2) as [[ic2 [τ_c tc2]]|] eqn:Hc2_close;
      simpl in Hcover; last done.
    destruct Hcover as [Hir1_lt Hi_lt_ic2].
    (* i_c ≤ iret_c < length ts'. *)
    assert (Hi_le_iret_c : i_c ≤ iret_c).
    { rewrite /i_c /iret_c. by apply φ_pos_monotone. }
    assert (Hi_lt_len_ts' : i_c < length ts') by lia.
    assert (Hir1_lt_len : ir1 < length ts') by lia.
    (* So ir1 corresponds to a position in ts' (the first part of close_trace). *)
    rewrite /ret_of_tag list_find_app_Some in Hr1_close.
    destruct Hr1_close as [Hr1_ts'|[Hge_ir1 _]]; cycle 1.
    { (* impossible: ir1 ≥ length ts' but we have ir1 < length ts' *) lia. }
    apply list_find_Some in Hr1_ts' as (Hlk_r1 & [Hτr_eq Hev_r_isret] & Hbefore_r1).
    simpl in Hτr_eq. subst τ_r.
    (* tr1 = Ret tval *)
    assert (Htr1_ret : ∃ tval, tr1 = Ret tval).
    { destruct tr1 as [|? ?|tval]; simpl in Hev_r_isret; try done.
      by exists tval. }
    destruct Htr1_ret as [tval Htr1_eq]. subst tr1.
    (* Use φ_pos_inv_lookup to get the unique k_r1 with φ_pos k_r1 = ir1. *)
    rewrite /ts' in Hlk_r1.
    apply φ_pos_inv_lookup in Hlk_r1 as (k_r1 & Hts_lk_r1 & Hφ_k_r1 & _).
    (* Now case split on (τ1, τ2) ∈ m vs nm1 vs nm2. *)
    rewrite !elem_of_app in Hin_pair.
    destruct Hin_pair as [Hin_m | [Hin_nm1 | Hin_nm2]].
    + (* (τ1, τ2) ∈ m: use Hno_match. *)
      pose proof (valid_match_call_pop _ _ _ _ Hvalid' Hin_m) as Hτ2_call_in_ts.
      assert (Hτ2_in_m2 : τ2 ∈ m.*2)
        by (apply (list_elem_of_fmap_2 snd _ (τ1, τ2)); exact Hin_m).
      assert (Hτ2_not_U : τ2 ∉ U).
      { intros Hin. apply list_elem_of_difference in Hin as [_ Habs].
        apply Habs. apply (list_elem_of_fmap_2 snd _ (τ1, τ2)).
        rewrite elem_of_app. by left. }
      (* call_of_tag close τ2 is in ts' (since τ2 has Call Pop in ts and τ2 ∉ U). *)
      rewrite /call_of_tag list_find_app_Some in Hc2_close.
      destruct Hc2_close as [Hc2_ts'|[_ [Hc2_none _]]]; cycle 1.
      { (* contradiction: τ2's Call Pop in ts ⇒ in ts'. *)
        exfalso. apply list_find_None in Hc2_none.
        rewrite Forall_forall in Hc2_none.
        apply (Hc2_none (τ2, Call Pop #())).
        - rewrite /ts'. apply list_elem_of_filter_2; done.
        - simpl. done. }
      apply list_find_Some in Hc2_ts' as (Hlk_c2 & [Hτc_eq Hev_c_iscall] & Hbefore_c2).
      simpl in Hτc_eq. subst τ_c.
      rewrite /ts' in Hlk_c2.
      apply φ_pos_inv_lookup in Hlk_c2 as (k_c2 & Hts_lk_c2 & Hφ_k_c2 & _).
      (* Now apply Hno_match. *)
      apply (Hno_match τ1 τ2 Hin_m).
      rewrite /push_pop_covers /ret_of_tag /call_of_tag.
      assert (Hfind_r1_ts : ∃ ir x, list_find (λ t, t.1 = τ1 ∧ is_ret t.2) ts = Some (ir, x) ∧ ir ≤ k_r1).
      { destruct (list_find (λ t, t.1 = τ1 ∧ is_ret t.2) ts) as [[ir x]|] eqn:Hf.
        - exists ir, x. split; [done|].
          apply list_find_Some in Hf as (_ & _ & Hbefore).
          destruct (Nat.le_gt_cases ir k_r1) as [|]; first done.
          exfalso. specialize (Hbefore k_r1 (τ1, Ret tval) Hts_lk_r1).
          apply Hbefore; first lia.
          split; [done|eexists; reflexivity].
        - exfalso. apply list_find_None in Hf. rewrite Forall_forall in Hf.
          apply (Hf (τ1, Ret tval) (list_elem_of_lookup_2 _ _ _ Hts_lk_r1)).
          split; [done|eexists; reflexivity]. }
      destruct Hfind_r1_ts as (ir & xr & Hfind_r1_ts_eq & Hir_le).
      rewrite Hfind_r1_ts_eq /=.
      (* tc2 = Call vc' for some vc' *)
      assert (Htc2_call : ∃ nc' vc', tc2 = Call nc' vc').
      { destruct tc2 as [nvc' vc'| |]; simpl in Hev_c_iscall; try done.
        by do 2 eexists. }
      destruct Htc2_call as (nc' & vc' & Htc2_eq). subst tc2.
      assert (Hfind_c2_ts : ∃ ic x, list_find (λ t, t.1 = τ2 ∧ is_call t.2) ts = Some (ic, x) ∧ ic ≤ k_c2).
      { destruct (list_find (λ t, t.1 = τ2 ∧ is_call t.2) ts) as [[ic x]|] eqn:Hf.
        - exists ic, x. split; [done|].
          apply list_find_Some in Hf as (_ & _ & Hbefore).
          destruct (Nat.le_gt_cases ic k_c2) as [|]; first done.
          exfalso. specialize (Hbefore k_c2 (τ2, Call nc' vc') Hts_lk_c2).
          apply Hbefore; first lia.
          split; [done|done].
        - exfalso. apply list_find_None in Hf. rewrite Forall_forall in Hf.
          apply (Hf (τ2, Call nc' vc') (list_elem_of_lookup_2 _ _ _ Hts_lk_c2)).
          split; [done|done]. }
      destruct Hfind_c2_ts as (ic & xc & Hfind_c2_ts_eq & Hic_le).
      rewrite Hfind_c2_ts_eq /=.
      simpl.
      assert (Hir_le_k_r1 : ir ≤ k_r1).
      { apply list_find_Some in Hfind_r1_ts_eq as (_ & _ & Hbefore_ir).
        destruct (Nat.le_gt_cases ir k_r1) as [|]; first done.
        exfalso. specialize (Hbefore_ir k_r1 (τ1, Ret tval) Hts_lk_r1).
        apply Hbefore_ir; first lia.
        split; [done|eexists; reflexivity]. }
      assert (Hir1_eq : ir1 = φ_pos U ts ir).
      { destruct xr as [τ_x ev_x].
        apply list_find_Some in Hfind_r1_ts_eq as (Hlk_ir & [Hτ_ir Hev_ir_isret] & _).
        simpl in Hτ_ir, Hev_ir_isret. subst τ_x.
        destruct ev_x as [|? ?|w]; simpl in Hev_ir_isret; try done.
        pose proof (φ_pos_lookup U ts ir τ1 (Ret w) Hlk_ir Hτ1_not_U) as Hlk_φir.
        apply Nat.le_antisymm.
        - (* ir1 ≤ φ_pos U ts ir: by list_find minimality on ts'. *)
          pose proof Hbefore_r1 as Hbefore.
          destruct (Nat.le_gt_cases ir1 (φ_pos U ts ir)) as [|]; first lia.
          exfalso. specialize (Hbefore (φ_pos U ts ir) (τ1, Ret w) Hlk_φir).
          apply Hbefore; first lia.
          split; [done|by eexists; reflexivity].
        - (* φ_pos U ts ir ≤ φ_pos U ts k_r1 = ir1, since ir ≤ k_r1. *)
          rewrite -Hφ_k_r1. by apply φ_pos_monotone. }
      assert (Hic_le_k_c2 : ic ≤ k_c2).
      { apply list_find_Some in Hfind_c2_ts_eq as (_ & _ & Hbefore_ic).
        destruct (Nat.le_gt_cases ic k_c2) as [|]; first done.
        exfalso. specialize (Hbefore_ic k_c2 (τ2, Call nc' vc') Hts_lk_c2).
        apply Hbefore_ic; first lia.
        split; [done|done]. }
      assert (Hic2_eq : ic2 = φ_pos U ts ic).
      { destruct xc as [τ_x ev_x].
        apply list_find_Some in Hfind_c2_ts_eq as (Hlk_ic & [Hτ_ic Hev_ic_iscall] & _).
        simpl in Hτ_ic, Hev_ic_iscall. subst τ_x.
        destruct ev_x as [nvc vc| |]; simpl in Hev_ic_iscall; try done.
        pose proof (φ_pos_lookup U ts ic τ2 (Call nvc vc) Hlk_ic Hτ2_not_U) as Hlk_φic.
        apply Nat.le_antisymm.
        - destruct (Nat.le_gt_cases ic2 (φ_pos U ts ic)) as [|]; first lia.
          exfalso. specialize (Hbefore_c2 (φ_pos U ts ic) (τ2, Call nvc vc) Hlk_φic).
          apply Hbefore_c2; first lia.
          split; [done|done].
        - rewrite -Hφ_k_c2. by apply φ_pos_monotone. }
      (* Now: ir1 = φ_pos ir, ic2 = φ_pos ic, i_c = φ_pos i_o. *)
      (* From ir1 < i_c < ic2: φ_pos ir < φ_pos i_o < φ_pos ic. *)
      (* By φ_pos_lt_inv: ir < i_o < ic. So push_pop_covers ts τ1 τ2 i_o. ✓ *)
      split.
      * apply (φ_pos_lt_inv U ts ir i_o). lia.
      * apply (φ_pos_lt_inv U ts i_o ic). lia.
    + (* (τ1, τ2) ∈ nm1: τ1 ∉ m.*1. Use Hno_dangling. *)
      assert (Hτ1_in_init : τ1 ∈ ump_init).
      { apply Hnm1_fst_sub.
        apply (list_elem_of_fmap_2 fst _ (τ1, τ2)). exact Hin_nm1. }
      assert (Hτ1_notin_m : τ1 ∉ m.*1) by exact (Hump_init_disj_m1 _ Hτ1_in_init).
      apply (Hno_dangling τ1 (conj Hτ1_push Hτ1_notin_m)).
      rewrite /dangling_push_covers /ret_of_tag.
      assert (Hfind_r1_ts : ∃ ir x, list_find (λ t, t.1 = τ1 ∧ is_ret t.2) ts = Some (ir, x) ∧ ir ≤ k_r1).
      { destruct (list_find (λ t, t.1 = τ1 ∧ is_ret t.2) ts) as [[ir x]|] eqn:Hf.
        - exists ir, x. split; [done|].
          apply list_find_Some in Hf as (_ & _ & Hbefore).
          destruct (Nat.le_gt_cases ir k_r1) as [|]; first done.
          exfalso. specialize (Hbefore k_r1 (τ1, Ret tval) Hts_lk_r1).
          apply Hbefore; first lia. split; [done|eexists; reflexivity].
        - exfalso. apply list_find_None in Hf. rewrite Forall_forall in Hf.
          apply (Hf (τ1, Ret tval) (list_elem_of_lookup_2 _ _ _ Hts_lk_r1)).
          split; [done|eexists; reflexivity]. }
      destruct Hfind_r1_ts as (ir & xr & Hfind_eq & Hir_le).
      rewrite Hfind_eq. simpl.
      apply (φ_pos_lt_inv U ts ir i_o).
      apply (Nat.le_lt_trans _ ir1); last exact Hir1_lt.
      rewrite -Hφ_k_r1. by apply φ_pos_monotone.
    + (* (τ1, τ2) ∈ nm2: similar to nm1. *)
      assert (Hτ1_in_ump' : τ1 ∈ ump').
      { rewrite -Hnm2_fst.
        apply (list_elem_of_fmap_2 fst _ (τ1, τ2)). exact Hin_nm2. }
      assert (Hτ1_in_init : τ1 ∈ ump_init) by exact (Hump'_sub _ Hτ1_in_ump').
      assert (Hτ1_notin_m : τ1 ∉ m.*1) by exact (Hump_init_disj_m1 _ Hτ1_in_init).
      apply (Hno_dangling τ1 (conj Hτ1_push Hτ1_notin_m)).
      rewrite /dangling_push_covers /ret_of_tag.
      assert (Hfind_r1_ts : ∃ ir x, list_find (λ t, t.1 = τ1 ∧ is_ret t.2) ts = Some (ir, x) ∧ ir ≤ k_r1).
      { destruct (list_find (λ t, t.1 = τ1 ∧ is_ret t.2) ts) as [[ir x]|] eqn:Hf.
        - exists ir, x. split; [done|].
          apply list_find_Some in Hf as (_ & _ & Hbefore).
          destruct (Nat.le_gt_cases ir k_r1) as [|]; first done.
          exfalso. specialize (Hbefore k_r1 (τ1, Ret tval) Hts_lk_r1).
          apply Hbefore; first lia. split; [done|eexists; reflexivity].
        - exfalso. apply list_find_None in Hf. rewrite Forall_forall in Hf.
          apply (Hf (τ1, Ret tval) (list_elem_of_lookup_2 _ _ _ Hts_lk_r1)).
          split; [done|eexists; reflexivity]. }
      destruct Hfind_r1_ts as (ir & xr & Hfind_eq & Hir_le).
      rewrite Hfind_eq. simpl.
      apply (φ_pos_lt_inv U ts ir i_o).
      apply (Nat.le_lt_trans _ ir1); last exact Hir1_lt.
      rewrite -Hφ_k_r1. by apply φ_pos_monotone.
  - (* Dangling case: vacuous since every push tag in close_trace is matched. *)
    intros τ1 [Hτ1_push Hτ1_nm].
    exfalso. apply Hτ1_nm.
    rewrite /push_of_trace !filter_app !fmap_app in Hτ1_push.
    assert (Hnp : filter (is_call_push ∘ snd) np = []).
    { subst np. apply filter_False_nil. rewrite Forall_forall.
      intros [τx tx] Hin. apply complete_trace_add_push_elem in Hin as [-> _].
      rewrite /is_call_push /=. intros [? ?]; discriminate. }
    assert (Hnpop1 : filter (is_call_push ∘ snd) npop1 = []).
    { subst npop1. apply filter_False_nil. rewrite Forall_forall.
      intros [τx tx] Hin. apply complete_trace_remove_pop_elem in Hin as [Hret _].
      destruct tx; simpl in Hret; try done. rewrite /is_call_push /=.
      intros [? ?]; discriminate. }
    assert (Hnpop2 : filter (is_call_push ∘ snd) npop2 = []).
    { subst npop2. apply filter_False_nil. rewrite Forall_forall.
      intros [τx tx] Hin.
      rewrite /close_trace_add_pop elem_of_app in Hin.
      destruct Hin as [Hin_c | Hin_r].
      - apply list_elem_of_fmap_1 in Hin_c as ([τ1' τ2'] & Heq & _).
        injection Heq as -> ->.
        rewrite /is_call_push /=. intros [v Hv]. discriminate.
      - apply list_elem_of_fmap_1 in Hin_r as ([τ1' τ2'] & Heq & _).
        injection Heq as -> ->.
        rewrite /is_call_push /=. intros [v Hv]. discriminate. }
    rewrite /npop2 /close_trace_add_pop filter_app in Hnpop2.
    apply app_eq_nil in Hnpop2 as [HnpC HnpR].
    rewrite Hnp Hnpop1 HnpC HnpR !fmap_nil !app_nil_r in Hτ1_push.
    assert (Hτ1_in_ts : τ1 ∈ (filter (is_call_push ∘ snd) ts).*1).
    { apply list_elem_of_fmap_1 in Hτ1_push as ([τx tx] & Heq & Hfilt).
      simpl in Heq. subst τx.
      apply list_elem_of_filter in Hfilt as [Hpush Hin_ts'].
      rewrite /ts' in Hin_ts'.
      apply list_elem_of_filter in Hin_ts' as [_ Hin_ts2].
      apply (list_elem_of_fmap_2 fst _ (τ1, tx)).
      apply list_elem_of_filter; done. }
    rewrite !fmap_app !elem_of_app.
    destruct (decide (τ1 ∈ m.*1)) as [Hm|Hnm]; first by left.
    right.
    assert (Hump : τ1 ∈ ump_init).
    { rewrite Hump_init_is /unpaired_operations /=.
      apply list_elem_of_difference. done. }
    pose proof (complete_trace_add_match_cover upop m ump_init τ1 Hump) as [Hl|Hr].
    + left. rewrite Hmatch /= in Hl. exact Hl.
    + right. rewrite Hmatch /= in Hr.
      rewrite /nm2 close_trace_add_match_fst. exact Hr.
Qed.

(* Helper: complete_trace_add_push entries are all Ret #(), so call_valid trivially *)
Local Lemma call_valid_np rme valid_value up :
  call_valid (M:=bag_model rme valid_value) (complete_trace_add_push up).
Proof.
  rewrite /call_valid /complete_trace_add_push. apply Forall_fmap.
  apply Forall_forall. intros τ _. done.
Qed.

(* Helper: complete_trace_remove_pop entries are all Ret, so call_valid trivially *)
Local Lemma call_valid_npop1 rme valid_value upop calls m0 :
  call_valid (M:=bag_model rme valid_value) (complete_trace_remove_pop upop calls m0).
Proof.
  rewrite /call_valid /complete_trace_remove_pop.
  apply Forall_forall. intros [τ t] Hin.
  apply list_elem_of_omap in Hin as (τ2 & _ & Heq).
  destruct (find (λ x : positive * positive, bool_decide (x.2 = τ2)) m0) as [[τ1 ?]|]; last done.
  injection Heq as Hτ Ht. subst τ t. done.
Qed.

(* Helper: close_trace_add_pop entries are Call Pop or Ret, both valid *)
Local Lemma call_valid_npop2 rme valid_value calls m_add :
  call_valid (M:=bag_model rme valid_value) (close_trace_add_pop calls m_add).
Proof.
  rewrite /call_valid /close_trace_add_pop.
  apply Forall_app. split.
  - apply Forall_fmap. apply Forall_forall. intros [τ1 τ2] _.
    simpl. done.
  - apply Forall_fmap. apply Forall_forall. intros [τ1 τ2] _.
    done.
Qed.

(* Helper: Forall (is_lin ∘ snd) implies filter (is_lin ∘ snd) is identity *)
Local Lemma filter_is_lin_all_lin (l : list (positive*trace)) :
  Forall (is_lin ∘ snd) l → filter (is_lin ∘ snd) l = l.
Proof.
  induction l as [|[τ t] l IH]; [done|].
  intros HF. rewrite Forall_cons in HF. destruct HF as [Hlin HF].
  rewrite filter_cons_True; [|exact Hlin].
  f_equal. exact (IH HF).
Qed.

(* Helper: Forall (not ∘ is_lin ∘ snd) implies filter (not ∘ is_lin ∘ snd) is identity *)
Local Lemma filter_not_lin_all_not_lin (l : list (positive*trace)) :
  Forall (not ∘ is_lin ∘ snd) l → filter (not ∘ is_lin ∘ snd) l = l.
Proof.
  induction l as [|[τ t] l IH]; [done|].
  intros HF. rewrite Forall_cons in HF. destruct HF as [Hnlin HF].
  rewrite filter_cons_True; [|exact Hnlin].
  f_equal. exact (IH HF).
Qed.

(* Helper: Forall (is_lin ∘ snd) implies filter (not ∘ is_lin ∘ snd) is [] *)
Local Lemma filter_not_lin_all_lin (l : list (positive*trace)) :
  Forall (is_lin ∘ snd) l → filter (not ∘ is_lin ∘ snd) l = [].
Proof.
  induction l as [|[τ t] l IH]; [done|].
  intros HF. rewrite Forall_cons in HF. destruct HF as [Hlin HF].
  rewrite filter_cons_False; [exact (IH HF)|].
  simpl. destruct t; simpl in Hlin |- *; tauto.
Qed.

(* Helper: Forall (not ∘ is_lin ∘ snd) implies filter (is_lin ∘ snd) is [] *)
Local Lemma filter_is_lin_all_not_lin (l : list (positive*trace)) :
  Forall (not ∘ is_lin ∘ snd) l → filter (is_lin ∘ snd) l = [].
Proof.
  induction l as [|[τ t] l IH]; [done|].
  intros HF. rewrite Forall_cons in HF. destruct HF as [Hnlin HF].
  rewrite filter_cons_False; [exact (IH HF)|].
  simpl. destruct t; simpl in Hnlin |- *; tauto.
Qed.

(* Helper: np has no Lin events *)
Local Lemma np_no_lin up :
  Forall (not ∘ is_lin ∘ snd) (complete_trace_add_push up).
Proof.
  rewrite /complete_trace_add_push.
  induction up as [|τ up IH]; [done|].
  simpl. apply Forall_cons. split; [compute_done|exact IH].
Qed.

(* Helper: npop1 has no Lin events *)
Local Lemma npop1_no_lin upop calls m0 :
  Forall (not ∘ is_lin ∘ snd) (complete_trace_remove_pop upop calls m0).
Proof.
  apply Forall_forall. intros [τ t] Hin.
  apply complete_trace_remove_pop_elem in Hin as [Hret _].
  destruct t; simpl in Hret; try done. compute_done.
Qed.

(* Helper: npop2 has no Lin events *)
Local Lemma npop2_no_lin calls m_add :
  Forall (not ∘ is_lin ∘ snd) (close_trace_add_pop calls m_add).
Proof.
  rewrite /close_trace_add_pop.
  apply Forall_app. split.
  - apply Forall_fmap. apply Forall_forall. intros [τ1 τ2] _. compute_done.
  - apply Forall_fmap. apply Forall_forall. intros [τ1 τ2] _. compute_done.
Qed.

(* Helper: ts_ext has no Lin events *)
Local Lemma ts_ext_no_lin rme valid_value ts0 up0 upop0 calls0 m_nm nm2_0 :
  per_tag_wellformed_bag rme valid_value ts0 →
  Forall (not ∘ is_lin ∘ snd)
    (ts0 ++ complete_trace_add_push up0
         ++ complete_trace_remove_pop upop0 calls0 m_nm
         ++ close_trace_add_pop calls0 nm2_0).
Proof.
  intros Hwf0.
  rewrite !Forall_app. split; [|split; [|split]].
  - apply Forall_forall. intros [τ0 t0] Hin0. simpl.
    destruct (Hwf0 τ0) as [(v0 & _ & Hpfx0)|(r0 & _ & Hpfx0)];
      (assert (Hin_filt : (τ0, t0) ∈ filter (λ x, x.1 = τ0) ts0)
        by (apply list_elem_of_filter; done));
      (eapply elem_of_prefix in Hin_filt; [|exact Hpfx0]);
      (apply elem_of_cons in Hin_filt as [Heq|Hin_filt];
        [simplify_eq; compute_done|]);
      (apply elem_of_cons in Hin_filt as [Heq|?];
        [simplify_eq; compute_done|by set_solver]).
  - exact (np_no_lin up0).
  - exact (npop1_no_lin upop0 calls0 m_nm).
  - pose proof (npop2_no_lin calls0 nm2_0) as Hnp2.
    rewrite /close_trace_add_pop in Hnp2.
    apply Forall_app in Hnp2 as [HC HR]. by split.
Qed.

(* Helper: extract_calls on a per_tag_complete list with no Lin events *)
Local Lemma extract_calls_ext_lookup ts_ext0 τ n v :
  Forall (not ∘ is_lin ∘ snd) ts_ext0 →
  per_tag_complete ts_ext0 →
  (τ, Call n v) ∈ ts_ext0 →
  extract_calls ts_ext0 !!! τ = (n, v).
Proof.
  intros Hno_lin Hcomplete Hin.
  rewrite /extract_calls lookup_total_alt.
  set (omap_result := omap (λ x : positive * trace,
    match x with (τ0, Call n0 v0) => Some (τ0, (n0, v0)) | _ => None end) ts_ext0).
  assert (Hin_omap : (τ, (n, v)) ∈ omap_result).
  { apply list_elem_of_omap. exists (τ, Call n v). split; [exact Hin|done]. }
  assert (Hlookup : (list_to_map omap_result : gmap positive (nat*val)) !! τ
                    = Some (n, v)).
  { apply elem_of_list_to_map_1'.
    - intros y Hin_y.
      apply list_elem_of_omap in Hin_y as ([τ_y t_y] & Hin_ts_y & Heq_y).
      destruct t_y as [n_y v_y| |]; try discriminate.
      injection Heq_y as -> <-.
      opose proof (per_tag_partial_wellformed_inj_call ts_ext0 τ n v n_y v_y _ Hin Hin_ts_y)
        as [-> ->]; last done.
      by eapply per_tag_wellformed_per_tag_partial_wellformed,
                per_tag_complete_per_tag_wellformed.
    - exact Hin_omap. }
  rewrite Hlookup. done.
Qed.

(* Helper: extract_calls lookup for wellformed traces.
   Under per_tag_wellformed_bag, each tag has at most one Call, so
   extract_calls gives the correct value. *)
Local Lemma extract_calls_lookup_wf rme valid_value ts0 τ n v :
  per_tag_wellformed_bag rme valid_value ts0 →
  (τ, Call n v) ∈ ts0 →
  extract_calls ts0 !!! τ = (n, v).
Proof. exact (extract_calls_lookup _ _ ts0 τ n v). Qed.

(* Helper: insert_lins construction — MIXED strategy:
   - Push tags: insert Lin right AFTER Call (push Lin early)
   - Pop tags: insert Lin right BEFORE Ret (pop Lin late)
   This ensures push Lin <= pop Lin via valid_match (push Call <= pop Ret). *)
Local Definition insert_lins (cmap : gmap positive (nat*val))
    (ts_ext0 : list (positive * trace)) : list (positive * trace) :=
  mjoin ((λ '(τ, ev),
    match ev with
    | Call n v =>
        if decide (is_call_push (Call n v)) then
          [(τ, Call n v); (τ, Lin n v #())]   (* push: Lin after Call *)
        else
          [(τ, Call n v)]                     (* pop: no Lin here *)
    | Ret v =>
        if decide (is_ret_push (Ret v)) then
          [(τ, Ret v)]                        (* push: no Lin here *)
        else
          [(τ, Lin Pop #() v); (τ, Ret v)]    (* pop: Lin before Ret *)
    | Lin n v1 v2 => [(τ, Lin n v1 v2)]
    end) <$> ts_ext0).

(* Helper: unfold insert_lins for push Call *)
Local Lemma insert_lins_cons_call_push cmap τ nc cv ts_ext0 :
  is_call_push (Call nc cv) →
  insert_lins cmap ((τ, Call nc cv) :: ts_ext0) =
  [(τ, Call nc cv); (τ, Lin nc cv #())] ++ insert_lins cmap ts_ext0.
Proof.
  intros Hpush. unfold insert_lins. simpl.
  destruct (decide (is_call_push (Call nc cv))); [done|contradiction].
Qed.

(* Helper: unfold insert_lins for pop Call *)
Local Lemma insert_lins_cons_call_pop cmap τ nc cv ts_ext0 :
  ¬ is_call_push (Call nc cv) →
  insert_lins cmap ((τ, Call nc cv) :: ts_ext0) =
  [(τ, Call nc cv)] ++ insert_lins cmap ts_ext0.
Proof.
  intros Hnpush. unfold insert_lins. simpl.
  destruct (decide (is_call_push (Call nc cv))); [contradiction|done].
Qed.

(* Helper: unfold insert_lins for push Ret *)
Local Lemma insert_lins_cons_ret_push cmap τ rv ts_ext0 :
  is_ret_push (Ret rv) →
  insert_lins cmap ((τ, Ret rv) :: ts_ext0) =
  [(τ, Ret rv)] ++ insert_lins cmap ts_ext0.
Proof.
  intros Hpush. unfold insert_lins. simpl.
  destruct (decide (is_ret_push (Ret rv))); [done|contradiction].
Qed.

(* Helper: unfold insert_lins for pop Ret *)
Local Lemma insert_lins_cons_ret_pop cmap τ rv ts_ext0 :
  ¬ is_ret_push (Ret rv) →
  insert_lins cmap ((τ, Ret rv) :: ts_ext0) =
  [(τ, Lin Pop #() rv); (τ, Ret rv)] ++ insert_lins cmap ts_ext0.
Proof.
  intros Hnpush. unfold insert_lins. simpl.
  destruct (decide (is_ret_push (Ret rv))); [contradiction|done].
Qed.

(* Helper: unfold insert_lins for Lin *)
Local Lemma insert_lins_cons_lin cmap τ ln lv1 lv2 ts_ext0 :
  insert_lins cmap ((τ, Lin ln lv1 lv2) :: ts_ext0) =
  [(τ, Lin ln lv1 lv2)] ++ insert_lins cmap ts_ext0.
Proof. done. Qed.

(* Helper: filter (not ∘ is_lin ∘ snd) of insert_lins gives back ts_ext *)
Local Lemma insert_lins_filter_not_lin cmap ts_ext0 :
  Forall (not ∘ is_lin ∘ snd) ts_ext0 →
  filter (not ∘ is_lin ∘ snd) (insert_lins cmap ts_ext0) = ts_ext0.
Proof.
  intros Hno_lin.
  induction ts_ext0 as [|[τ t] ts_ext0 IH].
  { rewrite /insert_lins /= filter_nil. done. }
  apply Forall_cons in Hno_lin as [Ht Hno_lin].
  simpl in Ht. destruct t as [nc cv|nl lv1 lv2|rv]; simpl in Ht.
  - (* Call *)
    destruct (decide (is_call_push (Call nc cv))) as [Hpush|Hnpush].
    + rewrite (insert_lins_cons_call_push _ _ _ _ _ Hpush) filter_app
        filter_cons_True; [|compute_done].
      rewrite filter_cons_False; [|by intros H; apply H].
      rewrite filter_nil //. f_equal. exact (IH Hno_lin).
    + rewrite (insert_lins_cons_call_pop _ _ _ _ _ Hnpush) filter_app
        filter_cons_True; [|compute_done].
      rewrite filter_nil //. f_equal. exact (IH Hno_lin).
  - exfalso. exact (Ht I).
  - (* Ret *)
    destruct (decide (is_ret_push (Ret rv))) as [Hpush|Hnpush].
    + rewrite (insert_lins_cons_ret_push _ _ _ _ Hpush) filter_app
        filter_cons_True; [|compute_done].
      rewrite filter_nil //. f_equal. exact (IH Hno_lin).
    + rewrite (insert_lins_cons_ret_pop _ _ _ _ Hnpush) filter_app.
      rewrite filter_cons_False; [|by intros H; apply H].
      rewrite filter_cons_True; [|compute_done].
      rewrite filter_nil //. f_equal. exact (IH Hno_lin).
Qed.

(* Helper: filter (is_lin ∘ snd) of insert_lins *)
Local Lemma insert_lins_filter_lin cmap ts_ext0 :
  Forall (not ∘ is_lin ∘ snd) ts_ext0 →
  filter (is_lin ∘ snd) (insert_lins cmap ts_ext0) =
    omap (λ '(τ, ev),
      match ev with
      | Call n v =>
          if decide (is_call_push (Call n v)) then Some (τ, Lin n v #())
          else None
      | Ret v =>
          if decide (is_ret_push (Ret v)) then None
          else Some (τ, Lin Pop #() v)
      | Lin _ _ _ => None
      end) ts_ext0.
Proof.
  intros Hno_lin.
  induction ts_ext0 as [|[τ t] ts_ext0 IH].
  { rewrite /insert_lins /= filter_nil. done. }
  apply Forall_cons in Hno_lin as [Ht Hno_lin].
  simpl in Ht. destruct t as [nc cv|nl lv1 lv2|rv]; simpl in Ht.
  - (* Call *)
    destruct (decide (is_call_push (Call nc cv))) as [Hpush|Hnpush].
    + rewrite (insert_lins_cons_call_push _ _ _ _ _ Hpush) filter_app
        filter_cons_False; [|compute_done].
      rewrite filter_cons_True; [|done].
      rewrite filter_nil. simpl.
      destruct (decide (is_call_push (Call nc cv))); [|contradiction].
      simpl. f_equal. exact (IH Hno_lin).
    + rewrite (insert_lins_cons_call_pop _ _ _ _ _ Hnpush) filter_app
        filter_cons_False; [|compute_done].
      rewrite filter_nil //. simpl.
      destruct (decide (is_call_push (Call nc cv))); [contradiction|].
      simpl. exact (IH Hno_lin).
  - exfalso. exact (Ht I).
  - (* Ret *)
    destruct (decide (is_ret_push (Ret rv))) as [Hpush|Hnpush].
    + rewrite (insert_lins_cons_ret_push _ _ _ _ Hpush) filter_app
        filter_cons_False; [|compute_done].
      rewrite filter_nil //. simpl.
      destruct (decide (is_ret_push (Ret rv))); [|contradiction].
      simpl. exact (IH Hno_lin).
    + rewrite (insert_lins_cons_ret_pop _ _ _ _ Hnpush) filter_app.
      rewrite filter_cons_True; [|done].
      rewrite filter_cons_False; [|compute_done].
      rewrite filter_nil. simpl.
      destruct (decide (is_ret_push (Ret rv))); [contradiction|].
      simpl. f_equal. exact (IH Hno_lin).
Qed.

(* Helper: filter for tag τ of insert_lins when tag has no events *)
Local Lemma insert_lins_filter_tag_empty cmap ts_ext0 τ :
  Forall (not ∘ is_lin ∘ snd) ts_ext0 →
  filter (λ x : positive * trace, x.1 = τ) ts_ext0 = [] →
  filter (λ x : positive * trace, x.1 = τ) (insert_lins cmap ts_ext0) = [].
Proof.
  intros Hno_lin Hempty.
  induction ts_ext0 as [|[τ0 t0] ts_ext0 IH].
  { done. }
  apply Forall_cons in Hno_lin as [Ht0 Hno_lin]. simpl in Ht0.
  assert (Hne : τ0 ≠ τ).
  { intros ->. destruct t0 as [nc cv|nl lv1 lv2|rv]; simpl in Ht0.
    - assert (H : (τ, Call nc cv) ∈ filter (λ x, x.1 = τ) ((τ, Call nc cv) :: ts_ext0)).
      { apply list_elem_of_filter. split; [done|set_solver]. }
      rewrite Hempty in H. set_solver.
    - exfalso. exact (Ht0 I).
    - assert (H : (τ, Ret rv) ∈ filter (λ x, x.1 = τ) ((τ, Ret rv) :: ts_ext0)).
      { apply list_elem_of_filter. split; [done|set_solver]. }
      rewrite Hempty in H. set_solver. }
  assert (Htail : filter (λ x : positive * trace, x.1 = τ) ts_ext0 = []).
  { destruct t0 as [nc cv|nl lv1 lv2|rv]; simpl in Ht0;
    [rewrite filter_cons_False in Hempty; [exact Hempty|simpl; done]
    |exfalso; exact (Ht0 I)
    |rewrite filter_cons_False in Hempty; [exact Hempty|simpl; done]]. }
  destruct t0 as [nc cv|nl lv1 lv2|rv]; simpl in Ht0.
  + (* Call *)
    destruct (decide (is_call_push (Call nc cv))) as [Hpush|Hnpush].
    * rewrite (insert_lins_cons_call_push _ _ _ _ _ Hpush) filter_app
        filter_cons_False; [|simpl; done].
      rewrite filter_cons_False; [|simpl; done].
      rewrite filter_nil //. exact (IH Hno_lin Htail).
    * rewrite (insert_lins_cons_call_pop _ _ _ _ _ Hnpush) filter_app
        filter_cons_False; [|simpl; done].
      rewrite filter_nil //. exact (IH Hno_lin Htail).
  + exfalso. exact (Ht0 I).
  + (* Ret *)
    destruct (decide (is_ret_push (Ret rv))) as [Hpush|Hnpush].
    * rewrite (insert_lins_cons_ret_push _ _ _ _ Hpush) filter_app
        filter_cons_False; [|simpl; done].
      rewrite filter_nil //. exact (IH Hno_lin Htail).
    * rewrite (insert_lins_cons_ret_pop _ _ _ _ Hnpush) filter_app
        filter_cons_False; [|simpl; done].
      rewrite filter_cons_False; [|simpl; done].
      rewrite filter_nil //. exact (IH Hno_lin Htail).
Qed.

(* Helper: filter for tag τ in insert_lins of a tail containing only Ret for τ.
   For POP tags (¬ is_ret_push), this gives [Lin v v'; Ret v']. *)
Local Lemma insert_lins_filter_tag_ret_tail_pop cmap ts_tail τ v' :
  Forall (not ∘ is_lin ∘ snd) ts_tail →
  filter (λ x : positive * trace, x.1 = τ) ts_tail = [(τ, Ret v')] →
  ¬ is_ret_push (Ret v') →
  filter (λ x : positive * trace, x.1 = τ) (insert_lins cmap ts_tail)
    = [(τ, Lin Pop #() v'); (τ, Ret v')].
Proof.
  intros Hno_lin Hfull Hnpush_r.
  induction ts_tail as [|[τ1 t1] ts_tail IH2].
  { discriminate. }
  apply Forall_cons in Hno_lin as [Ht1 Hno_lin]. simpl in Ht1.
  destruct (decide (τ1 = τ)) as [->|Hne2].
  - destruct t1 as [nc1 cv1|nl1 lv1 lv2|rv1]; simpl in Ht1.
    + rewrite filter_cons_True in Hfull; last done.
      injection Hfull as Habs. discriminate.
    + exfalso. exact (Ht1 I).
    + rewrite filter_cons_True in Hfull; last done.
      assert (rv1 = v') as -> by (injection Hfull; done).
      assert (Htail2 : filter (λ x : positive * trace, x.1 = τ) ts_tail = [])
        by (injection Hfull; done).
      rewrite (insert_lins_cons_ret_pop _ _ _ _ Hnpush_r) filter_app
        filter_cons_True; last done.
      rewrite filter_cons_True; last done.
      rewrite filter_nil.
      rewrite (insert_lins_filter_tag_empty cmap ts_tail τ Hno_lin Htail2). done.
  - assert (Htail2 : filter (λ x : positive * trace, x.1 = τ) ts_tail = [(τ, Ret v')]).
    { destruct t1 as [nc1 cv1|nl1 lv1 lv2|rv1]; simpl in Ht1;
      [rewrite filter_cons_False in Hfull; [exact Hfull|simpl; done]
      |exfalso; exact (Ht1 I)
      |rewrite filter_cons_False in Hfull; [exact Hfull|simpl; done]]. }
    destruct t1 as [nc1 cv1|nl1 lv1 lv2|rv1]; simpl in Ht1.
    + destruct (decide (is_call_push (Call nc1 cv1))) as [Hp|Hnp].
      * rewrite (insert_lins_cons_call_push _ _ _ _ _ Hp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH2 Hno_lin Htail2).
      * rewrite (insert_lins_cons_call_pop _ _ _ _ _ Hnp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH2 Hno_lin Htail2).
    + exfalso. exact (Ht1 I).
    + destruct (decide (is_ret_push (Ret rv1))) as [Hp|Hnp].
      * rewrite (insert_lins_cons_ret_push _ _ _ _ Hp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH2 Hno_lin Htail2).
      * rewrite (insert_lins_cons_ret_pop _ _ _ _ Hnp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH2 Hno_lin Htail2).
Qed.

(* Helper: filter for tag τ in insert_lins of a tail containing only Ret for τ.
   For PUSH tags (is_ret_push), this gives [Ret v']. *)
Local Lemma insert_lins_filter_tag_ret_tail_push cmap ts_tail τ v' :
  Forall (not ∘ is_lin ∘ snd) ts_tail →
  filter (λ x : positive * trace, x.1 = τ) ts_tail = [(τ, Ret v')] →
  is_ret_push (Ret v') →
  filter (λ x : positive * trace, x.1 = τ) (insert_lins cmap ts_tail)
    = [(τ, Ret v')].
Proof.
  intros Hno_lin Hfull Hpush_r.
  induction ts_tail as [|[τ1 t1] ts_tail IH2].
  { discriminate. }
  apply Forall_cons in Hno_lin as [Ht1 Hno_lin]. simpl in Ht1.
  destruct (decide (τ1 = τ)) as [->|Hne2].
  - destruct t1 as [nc1 cv1|nl1 lv1 lv2|rv1]; simpl in Ht1.
    + rewrite filter_cons_True in Hfull; last done.
      injection Hfull as Habs. discriminate.
    + exfalso. exact (Ht1 I).
    + rewrite filter_cons_True in Hfull; last done.
      assert (rv1 = v') as -> by (injection Hfull; done).
      assert (Htail2 : filter (λ x : positive * trace, x.1 = τ) ts_tail = [])
        by (injection Hfull; done).
      rewrite (insert_lins_cons_ret_push _ _ _ _ Hpush_r) filter_app
        filter_cons_True; last done.
      rewrite filter_nil.
      rewrite (insert_lins_filter_tag_empty cmap ts_tail τ Hno_lin Htail2). done.
  - assert (Htail2 : filter (λ x : positive * trace, x.1 = τ) ts_tail = [(τ, Ret v')]).
    { destruct t1 as [nc1 cv1|nl1 lv1 lv2|rv1]; simpl in Ht1;
      [rewrite filter_cons_False in Hfull; [exact Hfull|simpl; done]
      |exfalso; exact (Ht1 I)
      |rewrite filter_cons_False in Hfull; [exact Hfull|simpl; done]]. }
    destruct t1 as [nc1 cv1|nl1 lv1 lv2|rv1]; simpl in Ht1.
    + destruct (decide (is_call_push (Call nc1 cv1))) as [Hp|Hnp].
      * rewrite (insert_lins_cons_call_push _ _ _ _ _ Hp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH2 Hno_lin Htail2).
      * rewrite (insert_lins_cons_call_pop _ _ _ _ _ Hnp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH2 Hno_lin Htail2).
    + exfalso. exact (Ht1 I).
    + destruct (decide (is_ret_push (Ret rv1))) as [Hp|Hnp].
      * rewrite (insert_lins_cons_ret_push _ _ _ _ Hp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH2 Hno_lin Htail2).
      * rewrite (insert_lins_cons_ret_pop _ _ _ _ Hnp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH2 Hno_lin Htail2).
Qed.

(* Helper: filter for tag τ of insert_lins when tag has Call and Ret.
   Requires consistency: is_call_push(Call n v) ↔ is_ret_push(Ret v'). *)
Local Lemma insert_lins_filter_tag_full cmap ts_ext0 τ n v v' :
  Forall (not ∘ is_lin ∘ snd) ts_ext0 →
  filter (λ x : positive * trace, x.1 = τ) ts_ext0 = [(τ, Call n v); (τ, Ret v')] →
  (¬ is_call_push (Call n v) → n = Pop ∧ v = #()) →
  (is_call_push (Call n v) → is_ret_push (Ret v')) →
  (¬ is_call_push (Call n v) → ¬ is_ret_push (Ret v')) →
  filter (λ x : positive * trace, x.1 = τ) (insert_lins cmap ts_ext0)
    = [(τ, Call n v); (τ, Lin n v v'); (τ, Ret v')].
Proof.
  intros Hno_lin Hfull Hpop Hpush_consist Hpop_consist.
  induction ts_ext0 as [|[τ0 t0] ts_ext0 IH].
  { rewrite /= in Hfull. discriminate. }
  apply Forall_cons in Hno_lin as [Ht0 Hno_lin]. simpl in Ht0.
  destruct (decide (τ0 = τ)) as [->|Hne].
  + (* the head is the Call of τ *)
    rewrite filter_cons_True in Hfull; last done.
    assert (Hfull' : filter (λ x : positive * trace, x.1 = τ) ts_ext0 = [(τ, Ret v')])
      by (by inversion Hfull).
    assert (Ht0' : t0 = Call n v) by (by inversion Hfull).
    subst t0.
    destruct (decide (is_call_push (Call n v))) as [Hpush|Hnpush].
    * (* Push Call: emits [(τ, Call n v); (τ, Lin n v #())] *)
      assert (Hpr := Hpush_consist Hpush).
      rewrite /is_ret_push in Hpr. injection Hpr as ->.
      rewrite (insert_lins_cons_call_push _ _ _ _ _ Hpush) filter_app
        filter_cons_True; last done.
      rewrite filter_cons_True; last done.
      rewrite filter_nil.
      rewrite (insert_lins_filter_tag_ret_tail_push cmap ts_ext0 τ #() Hno_lin Hfull').
      { done. }
      { done. }
    * (* Pop Call: emits [(τ, Call n v)] *)
      assert (Hnpr := Hpop_consist Hnpush).
      destruct (Hpop Hnpush) as [-> ->].
      rewrite (insert_lins_cons_call_pop _ _ _ _ _ Hnpush) filter_app
        filter_cons_True; last done.
      rewrite filter_nil. f_equal.
      exact (insert_lins_filter_tag_ret_tail_pop cmap ts_ext0 τ v' Hno_lin Hfull' Hnpr).
  + assert (Htail : filter (λ x : positive * trace, x.1 = τ) ts_ext0 =
      [(τ, Call n v); (τ, Ret v')]).
    { destruct t0 as [nc cv|nl lv1 lv2|rv]; simpl in Ht0;
      [rewrite filter_cons_False in Hfull; [exact Hfull|simpl; done]
      |exfalso; exact (Ht0 I)
      |rewrite filter_cons_False in Hfull; [exact Hfull|simpl; done]]. }
    destruct t0 as [nc cv|nl lv1 lv2|rv]; simpl in Ht0.
    * destruct (decide (is_call_push (Call nc cv))) as [Hp|Hnp].
      { rewrite (insert_lins_cons_call_push _ _ _ _ _ Hp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH Hno_lin Htail). }
      { rewrite (insert_lins_cons_call_pop _ _ _ _ _ Hnp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH Hno_lin Htail). }
    * exfalso. exact (Ht0 I).
    * destruct (decide (is_ret_push (Ret rv))) as [Hp|Hnp].
      { rewrite (insert_lins_cons_ret_push _ _ _ _ Hp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH Hno_lin Htail). }
      { rewrite (insert_lins_cons_ret_pop _ _ _ _ Hnp) filter_app
          filter_cons_False; [|simpl; done].
        rewrite filter_cons_False; [|simpl; done].
        rewrite filter_nil //. exact (IH Hno_lin Htail). }
Qed.

(* Helper: per_tag_linearized of insert_lins when ts_ext is per_tag_complete *)
Local Lemma insert_lins_per_tag_linearized rme valid_value cmap ts_ext0 :
  Forall (not ∘ is_lin ∘ snd) ts_ext0 →
  per_tag_complete ts_ext0 →
  per_tag_wellformed_bag rme valid_value ts_ext0 →
  per_tag_linearized (insert_lins cmap ts_ext0).
Proof.
  intros Hno_lin Hcomplete Hwfb τ.
  destruct (Hcomplete τ) as (n & v & v' & [Hempty | Hfull]).
  - rewrite (insert_lins_filter_tag_empty cmap ts_ext0 τ Hno_lin Hempty).
    exists Push, #(), #(). apply prefix_nil.
  (* Prove push/pop consistency from per_tag_wellformed_bag *)
  - assert (Hpop : ¬ is_call_push (Call n v) → n = Pop ∧ v = #()).
    { intros Hnpush.
      destruct (Hwfb τ) as [(w & _ & Hpfx)|(r & _ & Hpfx)].
      - exfalso. apply Hnpush.
        assert (H : [(τ, Call n v); (τ, Ret v')] `prefix_of`
          [(τ, Call Push w); (τ, Ret #())]).
        { rewrite -Hfull. exact Hpfx. }
        apply prefix_cons_inv_1 in H. simplify_eq. by exists w.
      - assert (H : [(τ, Call n v); (τ, Ret v')] `prefix_of`
          [(τ, Call Pop #()); (τ, Ret (encode_response r))]).
        { rewrite -Hfull. exact Hpfx. }
        apply prefix_cons_inv_1 in H. simplify_eq. split; reflexivity. }
    assert (Hpush_consist : is_call_push (Call n v) → is_ret_push (Ret v')).
    { intros Hpush.
      destruct (Hwfb τ) as [(w' & _ & Hpfx)|(r & _ & Hpfx)].
      - assert (H : [(τ, Call n v); (τ, Ret v')] `prefix_of`
          [(τ, Call Push w'); (τ, Ret #())]).
        { rewrite -Hfull. exact Hpfx. }
        apply prefix_cons_inv_2 in H.
        apply prefix_cons_inv_1 in H.
        rewrite /is_ret_push. by inversion H.
      - exfalso. destruct Hpush as [w Hw].
        assert (H : [(τ, Call n v); (τ, Ret v')] `prefix_of`
          [(τ, Call Pop #()); (τ, Ret (encode_response r))]).
        { rewrite -Hfull. exact Hpfx. }
        apply prefix_cons_inv_1 in H. simplify_eq. }
    assert (Hpop_consist : ¬ is_call_push (Call n v) → ¬ is_ret_push (Ret v')).
    { intros Hnpush Hpr.
      destruct (Hwfb τ) as [(w & _ & Hpfx)|(r & _ & Hpfx)].
      - assert (H : [(τ, Call n v); (τ, Ret v')] `prefix_of`
          [(τ, Call Push w); (τ, Ret #())]).
        { rewrite -Hfull. exact Hpfx. }
        apply prefix_cons_inv_1 in H. simplify_eq.
        apply Hnpush. by exists w.
      - rewrite /is_ret_push in Hpr. injection Hpr as ->.
        assert (H : [(τ, Call n v); (τ, Ret #())] `prefix_of`
          [(τ, Call Pop #()); (τ, Ret (encode_response r))]).
        { rewrite -Hfull. exact Hpfx. }
        apply prefix_cons_inv_2 in H.
        apply prefix_cons_inv_1 in H.
        destruct r; simplify_eq. }
    rewrite (insert_lins_filter_tag_full cmap ts_ext0 τ n v v' Hno_lin Hfull Hpop
      Hpush_consist Hpop_consist).
    exists n, v, v'. reflexivity.
Qed.

(* Helper: for per_tag_complete + per_tag_wellformed_bag traces, each Ret
   event is either a push Ret (#()) or a pop Ret (encode_response r). *)
Local Lemma ret_event_push_or_pop rme valid_value (cmap : gmap positive (nat*val)) ts_ext0 τ rv :
  per_tag_wellformed_bag rme valid_value ts_ext0 →
  per_tag_complete ts_ext0 →
  (∀ τ n v, (τ, Call n v) ∈ ts_ext0 → cmap !!! τ = (n, v)) →
  (τ, Ret rv) ∈ ts_ext0 →
  (∃ w, cmap !!! τ = (Push, w) ∧ rv = #()) ∨
  (cmap !!! τ = (Pop, #()) ∧ ∃ r, rv = encode_response r).
Proof.
  intros Hwfb Hcomplete Hcmap Hin.
  (* From per_tag_complete: filter for τ is [] or [Call nc cv; Ret rv'] *)
  destruct (Hcomplete τ) as (nc & cv & rv' & [Hempty|Hfull]).
  { (* filter = [] contradicts (τ, Ret rv) ∈ ts_ext0 *)
    exfalso.
    assert (H : (τ, Ret rv) ∈ filter (λ x, x.1 = τ) ts_ext0).
    { apply list_elem_of_filter. done. }
    rewrite Hempty in H. set_solver. }
  (* filter = [(τ, Call nc cv); (τ, Ret rv')] *)
  assert (Hrv_eq : rv = rv').
  { assert (H : (τ, Ret rv) ∈ filter (λ x, x.1 = τ) ts_ext0).
    { apply list_elem_of_filter. done. }
    rewrite Hfull in H. apply elem_of_cons in H as [H|H].
    - by inversion H.
    - apply elem_of_cons in H as [H|H].
      + by inversion H.
      + set_solver. }
  subst rv'.
  assert (Hcall_in : (τ, Call nc cv) ∈ ts_ext0).
  { assert (H : (τ, Call nc cv) ∈ filter (λ x, x.1 = τ) ts_ext0)
      by (rewrite Hfull; set_solver).
    by apply list_elem_of_filter in H as [_ ?]. }
  assert (Hcmap_eq : cmap !!! τ = (nc, cv)) by (exact (Hcmap τ nc cv Hcall_in)).
  (* From per_tag_wellformed_bag: push or pop pattern *)
  destruct (Hwfb τ) as [(w & _ & Hpfx)|(r & _ & Hpfx)].
  - (* Push pattern: nc = Push and cv = w *)
    assert (Hcv_push : Call nc cv = Call Push w).
    { assert (H : [(τ, Call nc cv); (τ, Ret rv)] `prefix_of`
        [(τ, Call Push w); (τ, Ret #())]).
      { rewrite -Hfull. exact Hpfx. }
      apply prefix_cons_inv_1 in H. by inversion H. }
    injection Hcv_push as -> ->.
    left. exists w.
    split. { rewrite Hcmap_eq. done. }
    (* rv = #() from prefix *)
    assert (H : [(τ, Call Push w); (τ, Ret rv)] `prefix_of`
      [(τ, Call Push w); (τ, Ret #())]).
    { rewrite -Hfull. exact Hpfx. }
    apply prefix_cons_inv_2 in H.
    apply prefix_cons_inv_1 in H. by inversion H.
  - (* Pop pattern: nc = Pop and cv = #() *)
    assert (Hcv_pop : Call nc cv = Call Pop #()).
    { assert (H : [(τ, Call nc cv); (τ, Ret rv)] `prefix_of`
        [(τ, Call Pop #()); (τ, Ret (encode_response r))]).
      { rewrite -Hfull. exact Hpfx. }
      apply prefix_cons_inv_1 in H. by inversion H. }
    injection Hcv_pop as -> ->.
    right.
    split. { rewrite Hcmap_eq. done. }
    (* rv = encode_response r from prefix *)
    assert (H : [(τ, Call Pop #()); (τ, Ret rv)] `prefix_of`
      [(τ, Call Pop #()); (τ, Ret (encode_response r))]).
    { rewrite -Hfull. exact Hpfx. }
    apply prefix_cons_inv_2 in H.
    apply prefix_cons_inv_1 in H.
    exists r. by inversion H.
Qed.

(* The main lemma *)
(* Helper: NoDup of close_trace_add_match second components *)
(* Helper: complete pop filter in ts is exactly [Call; Ret] *)
Local Lemma complete_pop_filter rme valid_value ts0 m0 τ :
  per_tag_wellformed_bag rme valid_value ts0 →
  (τ, Call Pop #()) ∈ ts0 →
  τ ∉ (unpaired_operations ts0 m0).1.2 →
  ∃ r, filter (λ x : positive * trace, x.1 = τ) ts0 = [(τ, Call Pop #()); (τ, Ret (encode_response r))].
Proof.
  intros Hwf Hin Hnotin.
  destruct (wellformed_pop_filter_prefix _ _ _ _ Hwf Hin) as [Heq|(r & _ & Heq)].
  - exfalso. apply Hnotin.
    rewrite /unpaired_operations.
    apply list_elem_of_difference. split.
    + apply (list_elem_of_fmap_2 fst _ (τ, Call Pop #())).
      apply list_elem_of_filter. split; [done|exact Hin].
    + intros Hin_ret.
      apply list_elem_of_fmap_1 in Hin_ret as ([τ' ev] & Heq' & Hin_ret).
      simpl in Heq'. subst τ'.
      apply list_elem_of_filter in Hin_ret as [Hret Hin_ret].
      simpl in Hret. destruct Hret as [r ->].
      assert (Hin_filt : (τ, Ret (encode_response r)) ∈ filter (λ x, x.1 = τ) ts0).
      { apply list_elem_of_filter. done. }
      rewrite Heq in Hin_filt. apply elem_of_cons in Hin_filt as [Habs|?]; [discriminate|by set_solver].
  - exists r. exact Heq.
Qed.

Lemma close_complete rme valid_value ts m :
  per_tag_wellformed_bag rme valid_value ts →
  valid_match ts m →
  per_tag_complete (close_trace ts m).1.
Proof.
  intros Hwf Hvalid τ.
  rewrite /close_trace.
  destruct (unpaired_operations ts m) as [[up upop] ump_init] eqn:Hops.
  destruct (complete_trace_add_match upop m ump_init) as [nm1 ump'] eqn:Hmatch.
  set (calls := extract_calls ts).
  set (np := complete_trace_add_push up).
  set (npop1 := complete_trace_remove_pop upop calls (m ++ nm1)).
  set (U := list_difference upop (m ++ nm1).*2).
  set (ts' := filter (λ x : positive * trace, x.1 ∉ U) ts).
  set (nm2 := close_trace_add_match ump' (max_tag ts.*1 + 1)).
  set (npop2_calls := close_trace_add_pop_calls nm2).
  set (npop2_rets := close_trace_add_pop_rets calls nm2).
  set (npop2 := close_trace_add_pop calls nm2).
  simpl.
  (* Useful equalities *)
  assert (Hupop_is : upop = (unpaired_operations ts m).1.2)
    by (rewrite /unpaired_operations in Hops; by injection Hops as _ <- _).
  assert (Hup_is : up = (unpaired_operations ts m).1.1)
    by (rewrite /unpaired_operations in Hops; by injection Hops as <- _ _).
  assert (Hump_init_is : ump_init = (unpaired_operations ts m).2)
    by (rewrite /unpaired_operations in Hops; by injection Hops as _ _ <-).
  assert (Hupop_nd : NoDup upop)
    by (rewrite Hupop_is; eapply unpaired_pops_nodup; exact Hwf).
  rewrite !filter_app.
  destruct (decide (τ ∈ U)) as [Hτ_U | Hτ_nU].
  { (* τ unmatched unpaired pop: filtered out of ts'; not in any added block. *)
    assert (Hupop_τ : τ ∈ upop)
      by (apply list_elem_of_difference in Hτ_U as [? _]; done).
    assert (Hτ_pop : τ ∈ pop_of_trace ts).
    { rewrite Hupop_is in Hupop_τ. exact (unpaired_pop_is_pop _ m _ Hupop_τ). }
    pose proof (pop_tag_in_trace _ _ Hτ_pop) as Hcall_pop.
    assert (Hτ_npush : τ ∉ push_of_trace ts)
      by (intros ?; eapply push_xor_pop_of_trace; eauto).
    assert (Hτ_nup : τ ∉ up).
    { rewrite Hup_is. eapply pop_tag_not_up; eauto. }
    assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts' = []).
    { apply filter_False_nil, Forall_forall.
      intros [τ' t'] Hin'. simpl. intros ->.
      rewrite /ts' in Hin'.
      apply list_elem_of_filter in Hin' as [Hni _]. simpl in Hni. done. }
    assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
    { apply filter_np_not_in. exact Hτ_nup. }
    assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
    { rewrite /npop1.
      apply (filter_npop1_in_unmatched τ upop calls).
      destruct (find (λ x : positive * positive, bool_decide (x.2 = τ)) (m ++ nm1))
        as [[τ1 τ2]|] eqn:Hfind; last reflexivity.
      exfalso.
      pose proof Hfind as Hfind_copy.
      apply find_some in Hfind_copy as [Hin_pair Hbd].
      apply bool_decide_eq_true_1 in Hbd. simpl in Hbd. subst τ2.
      apply list_elem_of_difference in Hτ_U as [_ Hni]. apply Hni.
      apply (list_elem_of_fmap_2 snd _ (τ1, τ)).
      by apply list_elem_of_In. }
    assert (Hfilt_npop2 : filter (λ x : positive * trace, x.1 = τ) npop2 = []).
    { rewrite /npop2.
      apply (filter_npop2_old_tag τ (Call Pop #()) ts _ calls); last reflexivity.
      exact Hcall_pop. }
    rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
    apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
    rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
    by exists Pop, #(), #(); left. }
  (* τ ∉ U *)
  assert (Hts'_ts : ∀ τ' t', τ' ∉ U → ((τ', t') ∈ ts' ↔ (τ', t') ∈ ts)).
  { intros τ' t' Hni. rewrite /ts'. split.
    - intros Hi. by apply list_elem_of_filter in Hi as [_ ?].
    - intros Hi. apply list_elem_of_filter_2; done. }
  destruct (decide (τ ∈ push_of_trace ts)) as [Hpush | Hnpush].
  { (* τ is a push tag *)
    destruct (push_tag_in_trace _ _ Hpush) as [v Hin_ts].
    assert (Hτ_npop : τ ∉ pop_of_trace ts)
      by (intros ?; eapply push_xor_pop_of_trace; eauto).
    assert (Hτ_nupop : τ ∉ upop).
    { rewrite Hupop_is. intros Hin. apply Hτ_npop. exact (unpaired_pop_is_pop _ m _ Hin). }
    assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
    { rewrite /npop1. apply filter_npop1_not_in. exact Hτ_nupop. }
    assert (Hfilt_npop2 : filter (λ x : positive * trace, x.1 = τ) npop2 = []).
    { rewrite /npop2.
      apply (filter_npop2_old_tag τ (Call Push v) ts _ calls); last reflexivity.
      exact Hin_ts. }
    destruct (decide (τ ∈ up)) as [Hin_up | Hnotin_up].
    - (* incomplete push *)
      assert (Hin_up' : τ ∈ (unpaired_operations ts m).1.1) by (rewrite -Hup_is; exact Hin_up).
      assert (Hfilt_ts : filter (λ x : positive * trace, x.1 = τ) ts
                        = [(τ, Call Push v)]).
      { exact (incomplete_push_filter rme valid_value ts m τ v Hwf Hin_ts Hin_up'). }
      assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts'
                          = [(τ, Call Push v)]).
      { rewrite /ts' list_filter_comm. rewrite Hfilt_ts. simpl.
        rewrite filter_cons_True //. }
      assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np
                         = [(τ, Ret #())]).
      { rewrite /np. apply filter_np_in.
        - rewrite Hup_is. eapply unpaired_pushes_nodup. exact Hwf.
        - exact Hin_up. }
      rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
      apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
      rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
      exists Push, v, #(). right. done.
    - (* complete push *)
      assert (Hnotin_up' : τ ∉ (unpaired_operations ts m).1.1) by (rewrite -Hup_is; exact Hnotin_up).
      assert (Hfilt_ts : filter (λ x : positive * trace, x.1 = τ) ts
                        = [(τ, Call Push v); (τ, Ret #())]).
      { exact (complete_push_filter rme valid_value ts m τ v Hwf Hin_ts Hnotin_up'). }
      assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts'
                          = [(τ, Call Push v); (τ, Ret #())]).
      { rewrite /ts' list_filter_comm. rewrite Hfilt_ts. simpl.
        rewrite filter_cons_True //. rewrite filter_cons_True //. }
      assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
      { rewrite /np. apply filter_np_not_in. exact Hnotin_up. }
      rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
      apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
      rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
      exists Push, v, #(). right. done. }
  destruct (decide (τ ∈ pop_of_trace ts)) as [Hpop | Hnpop].
  { (* τ is a pop tag (and not in U, so matched if unpaired). *)
    pose proof (pop_tag_in_trace _ _ Hpop) as Hin_ts.
    assert (Hτ_nup : τ ∉ up).
    { rewrite Hup_is. eapply pop_tag_not_up; eauto. }
    assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
    { rewrite /np. apply filter_np_not_in. exact Hτ_nup. }
    assert (Hfilt_npop2 : filter (λ x : positive * trace, x.1 = τ) npop2 = []).
    { rewrite /npop2.
      apply (filter_npop2_old_tag τ (Call Pop #()) ts _ calls); last reflexivity.
      exact Hin_ts. }
    destruct (decide (τ ∈ upop)) as [Hin_upop | Hnotin_upop].
    - (* incomplete pop, matched (since τ ∉ U) *)
      assert (Hτ_in_match : τ ∈ (m ++ nm1).*2).
      { destruct (decide (τ ∈ (m ++ nm1).*2)); first done.
        exfalso. apply Hτ_nU. rewrite /U. apply list_elem_of_difference. done. }
      assert (Hfind : ∃ τ1 z, find (λ x : positive * positive, bool_decide (x.2 = τ)) (m ++ nm1) = Some (τ1, z)).
      { apply list_elem_of_fmap_1 in Hτ_in_match as ([τ1 τ2] & -> & Hin_pair).
        destruct (find_some_elem (λ x : positive * positive, bool_decide (x.2 = τ2)) (m ++ nm1) (τ1, τ2) Hin_pair) as [y Hy].
        - apply bool_decide_eq_true_2. done.
        - destruct y as [τ1' τ2']. exists τ1', τ2'. exact Hy. }
      assert (Hin_upop' : τ ∈ (unpaired_operations ts m).1.2)
        by (rewrite -Hupop_is; exact Hin_upop).
      assert (Hfilt_ts : filter (λ x : positive * trace, x.1 = τ) ts
                        = [(τ, Call Pop #())]).
      { exact (incomplete_pop_filter rme valid_value ts m τ Hwf Hin_ts Hin_upop'). }
      assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts'
                          = [(τ, Call Pop #())]).
      { rewrite /ts' list_filter_comm. rewrite Hfilt_ts. simpl.
        rewrite filter_cons_True //. }
      destruct (filter_npop1_in τ upop calls (m ++ nm1) Hupop_nd Hin_upop Hfind)
        as [v Hfilt_npop1].
      rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
      apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
      rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
      exists Pop, #(), v. right. done.
    - (* complete pop *)
      assert (Hnotin_upop' : τ ∉ (unpaired_operations ts m).1.2)
        by (rewrite -Hupop_is; exact Hnotin_upop).
      destruct (complete_pop_filter rme valid_value ts m τ Hwf Hin_ts Hnotin_upop')
        as [r Hfilt_ts].
      assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts'
                          = [(τ, Call Pop #()); (τ, Ret (encode_response r))]).
      { rewrite /ts' list_filter_comm. rewrite Hfilt_ts. simpl.
        rewrite filter_cons_True //. rewrite filter_cons_True //. }
      assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
      { rewrite /npop1. apply filter_npop1_not_in. exact Hnotin_upop. }
      rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
      apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
      rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
      exists Pop, #(), (encode_response r). right. done. }
  (* τ neither push nor pop in ts *)
  destruct (decide (τ ∈ nm2.*2)) as [Hin_nm2 | Hnotin_nm2].
  { assert (Hex : ∃ τ1, (τ1, τ) ∈ nm2).
    { apply list_elem_of_fmap_1 in Hin_nm2 as ([τ1' τ2'] & Heq & Hin).
      simpl in Heq. subst τ2'. exists τ1'. exact Hin. }
    assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts' = []).
    { apply filter_False_nil, Forall_forall.
      intros [τ' t'] Hin'. simpl. intros ->.
      rewrite /ts' in Hin'.
      apply list_elem_of_filter in Hin' as [_ Hin_ts].
      destruct Hex as [τ1 Hnm2_in].
      apply close_trace_add_match_tags_fresh in Hnm2_in.
      pose proof (tag_in_ts_le_max_tag _ _ _ Hin_ts). lia. }
    assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
    { rewrite /np. apply filter_np_not_in.
      intros Hin. apply Hnpush. rewrite Hup_is in Hin.
      exact (unpaired_push_is_push _ m _ Hin). }
    assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
    { rewrite /npop1. apply filter_npop1_not_in.
      intros Hin. apply Hnpop. rewrite Hupop_is in Hin.
      exact (unpaired_pop_is_pop _ m _ Hin). }
    assert (Hnm2_nd : NoDup nm2.*2).
    { rewrite /nm2. apply close_trace_add_match_snd_nodup. }
    destruct Hex as [τ1 Hin_nm2_pair].
    assert (Hfilt_npop2_calls : filter (λ x : positive * trace, x.1 = τ) npop2_calls
                                = [(τ, Call Pop #())]).
    { rewrite /npop2_calls.
      exact (filter_calls_of_close_trace_add_pop_in_exact τ τ1 nm2 Hnm2_nd Hin_nm2_pair). }
    assert (Hfilt_npop2_rets : filter (λ x : positive * trace, x.1 = τ) npop2_rets
                                = [(τ, Ret (ret_val_of_call (calls !!! τ1)))]).
    { rewrite /npop2_rets.
      exact (filter_rets_of_close_trace_add_pop_in_exact τ τ1 calls nm2 Hnm2_nd Hin_nm2_pair). }
    rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
    exists Pop, #(), (ret_val_of_call (calls !!! τ1)). right. done. }
  (* τ absent from everything *)
  assert (Hfilt_ts : filter (λ x : positive * trace, x.1 = τ) ts = []).
  { apply filter_False_nil, Forall_forall.
    intros [τ' t'] Hin. simpl. intros ->.
    destruct (Hwf τ) as [(v & _ & Hpfx) | (r & _ & Hpfx)].
    - apply Hnpush.
      assert (Hin_filt : (τ, t') ∈ filter (λ x, x.1 = τ) ts)
        by (apply list_elem_of_filter; done).
      destruct (filter (λ x, x.1 = τ) ts) as [|x xs] eqn:Heq; first by set_solver.
      apply prefix_cons_inv_1 in Hpfx as Hx. subst x.
      apply (list_elem_of_fmap_2 fst _ (τ, Call Push v)).
      apply list_elem_of_filter; split; [eexists; done|].
      assert (Hin_call : (τ, Call Push v) ∈ filter (λ x, x.1 = τ) ts)
        by (rewrite Heq; set_solver).
      by apply list_elem_of_filter in Hin_call as [_ ?].
    - apply Hnpop.
      assert (Hin_filt : (τ, t') ∈ filter (λ x, x.1 = τ) ts)
        by (apply list_elem_of_filter; done).
      destruct (filter (λ x, x.1 = τ) ts) as [|x xs] eqn:Heq; first by set_solver.
      apply prefix_cons_inv_1 in Hpfx as Hx. subst x.
      apply (list_elem_of_fmap_2 fst _ (τ, Call Pop #())).
      apply list_elem_of_filter; split; [done|].
      assert (Hin_call : (τ, Call Pop #()) ∈ filter (λ x, x.1 = τ) ts)
        by (rewrite Heq; set_solver).
      by apply list_elem_of_filter in Hin_call as [_ ?]. }
  assert (Hfilt_ts' : filter (λ x : positive * trace, x.1 = τ) ts' = []).
  { rewrite /ts' list_filter_comm Hfilt_ts. by rewrite filter_nil. }
  assert (Hfilt_np : filter (λ x : positive * trace, x.1 = τ) np = []).
  { rewrite /np. apply filter_np_not_in.
    intros Hin. apply Hnpush. rewrite Hup_is in Hin.
    exact (unpaired_push_is_push _ m _ Hin). }
  assert (Hfilt_npop1 : filter (λ x : positive * trace, x.1 = τ) npop1 = []).
  { rewrite /npop1. apply filter_npop1_not_in.
    intros Hin. apply Hnpop. rewrite Hupop_is in Hin.
    exact (unpaired_pop_is_pop _ m _ Hin). }
  assert (Hfilt_npop2 : filter (λ x : positive * trace, x.1 = τ) npop2 = []).
  { rewrite /npop2. apply filter_close_trace_add_pop_not_in. exact Hnotin_nm2. }
  rewrite /npop2 /close_trace_add_pop filter_app in Hfilt_npop2.
  apply app_eq_nil in Hfilt_npop2 as [Hfilt_npop2_calls Hfilt_npop2_rets].
  rewrite Hfilt_ts' Hfilt_np Hfilt_npop2_calls Hfilt_npop1 Hfilt_npop2_rets.
  by exists Pop, #(), #(); left.
Qed.

Lemma close_closed rme valid_value ts m :
  per_tag_wellformed_bag rme valid_value ts →
  valid_match ts m →
  closed_match (close_trace ts m).1 (close_trace ts m).2.
Proof.
  intros Hwf Hvalid.
  destruct Hvalid as (Hcov & [Hnd_m1 Hnd_m2] & Hforall).
  rewrite /close_trace.
  destruct (unpaired_operations ts m) as [[up upop] ump_init] eqn:Hops.
  destruct (complete_trace_add_match upop m ump_init) as [nm1 ump'] eqn:Hmatch.
  set (calls := extract_calls ts).
  set (np := complete_trace_add_push up).
  set (npop1 := complete_trace_remove_pop upop calls (m ++ nm1)).
  set (U := list_difference upop (m ++ nm1).*2).
  set (ts' := filter (λ x : positive * trace, x.1 ∉ U) ts).
  set (nm2 := close_trace_add_match ump' (max_tag ts.*1 + 1)).
  set (npop2_calls := close_trace_add_pop_calls nm2).
  set (npop2_rets := close_trace_add_pop_rets calls nm2).
  set (npop2 := close_trace_add_pop calls nm2).
  simpl.
  assert (Hupop_is : upop = (unpaired_operations ts m).1.2)
    by (rewrite /unpaired_operations in Hops; by injection Hops as _ <- _).
  assert (Hupop_nd : NoDup upop)
    by (rewrite Hupop_is; eapply unpaired_pops_nodup; exact Hwf).
  assert (Hupop_sub : upop ⊆ pop_of_trace ts).
  { rewrite Hupop_is. intros τ Hin. by eapply unpaired_pop_is_pop. }
  assert (Hnm1_snd_sub : nm1.*2 ⊆ upop).
  { assert (Heq : nm1 = (complete_trace_add_match upop m ump_init).1)
      by (rewrite Hmatch; done).
    rewrite Heq. apply complete_trace_add_match_snd_sub. }
  rewrite /closed_match. split.
  - (* push_of_trace closed ⊆ (m ++ nm1 ++ nm2).*1 *)
    rewrite -/calls -/np -/nm1 -/npop2_calls -/npop1 -/U -/ts' -/nm2 -/npop2_rets.
    intros τ Hτ_push_close.
    rewrite /push_of_trace !filter_app !fmap_app in Hτ_push_close.
    assert (Hnp : filter (is_call_push ∘ snd) np = []).
    { subst np. apply filter_False_nil. rewrite Forall_forall.
      intros [τ' t'] Hin. apply complete_trace_add_push_elem in Hin as [-> _].
      rewrite /is_call_push /=. intros [? ?]; discriminate. }
    assert (Hnpop1 : filter (is_call_push ∘ snd) npop1 = []).
    { subst npop1. apply filter_False_nil. rewrite Forall_forall.
      intros [τ' t'] Hin. apply complete_trace_remove_pop_elem in Hin as [Hret _].
      destruct t'; simpl in Hret; try done. rewrite /is_call_push /=.
      intros [? ?]; discriminate. }
    assert (Hnpop2 : filter (is_call_push ∘ snd) npop2 = []).
    { subst npop2. apply filter_False_nil. rewrite Forall_forall.
      intros [τ' t'] Hin.
      rewrite /close_trace_add_pop elem_of_app in Hin.
      destruct Hin as [Hin_c | Hin_r].
      - apply list_elem_of_fmap_1 in Hin_c as ([τ1' τ2'] & Heq & _).
        injection Heq as -> ->.
        rewrite /is_call_push /=. intros [v Hv]. discriminate.
      - apply list_elem_of_fmap_1 in Hin_r as ([τ1' τ2'] & Heq & _).
        injection Heq as -> ->.
        rewrite /is_call_push /=. intros [v Hv]. discriminate. }
    rewrite /npop2 /close_trace_add_pop filter_app in Hnpop2.
    apply app_eq_nil in Hnpop2 as [HnpC HnpR].
    rewrite Hnp HnpC Hnpop1 HnpR !fmap_nil !app_nil_r in Hτ_push_close.
    (* τ has Call Push in ts'. Hence in ts. *)
    assert (Hτ_in_ts : τ ∈ (filter (is_call_push ∘ snd) ts).*1).
    { apply list_elem_of_fmap_1 in Hτ_push_close as ([τ' t'] & Heq & Hfilt).
      simpl in Heq. subst τ'.
      apply list_elem_of_filter in Hfilt as [Hpush Hin_ts'].
      rewrite /ts' in Hin_ts'.
      apply list_elem_of_filter in Hin_ts' as [_ Hin_ts].
      apply (list_elem_of_fmap_2 fst _ (τ, t')).
      apply list_elem_of_filter; done. }
    rewrite !fmap_app !elem_of_app.
    destruct (decide (τ ∈ m.*1)) as [Hm|Hnm]; first by left.
    right.
    assert (Hump : τ ∈ ump_init).
    { rewrite /unpaired_operations in Hops.
      injection Hops as _ _ <-. apply list_elem_of_difference. done. }
    pose proof (complete_trace_add_match_cover upop m ump_init τ Hump) as [Hl|Hr].
    + left. rewrite Hmatch /= in Hl. exact Hl.
    + right. rewrite Hmatch /= in Hr.
      rewrite /nm2. rewrite close_trace_add_match_fst. exact Hr.
  - (* Each pop in closed trace is matched / IsEmpty / unfinished. *)
    rewrite -/calls -/np -/nm1 -/npop2_calls -/npop1 -/U -/ts' -/nm2 -/npop2_rets.
    apply Forall_forall. intros τ Hτ_pop_close.
    (* Decompose pop_of_trace (close_trace ts m).1. *)
    rewrite /pop_of_trace in Hτ_pop_close.
    apply list_elem_of_fmap_1 in Hτ_pop_close as ([τ' ev] & Heq & Hin_filt).
    simpl in Heq. subst τ'.
    apply list_elem_of_filter in Hin_filt as [Hcall_pop Hin_close].
    rewrite /is_call_pop /= in Hcall_pop. subst ev.
    apply elem_of_app in Hin_close as [Hin_ts'|Hin_rest].
    + (* τ ∈ ts' has Call Pop *)
      apply list_elem_of_filter in Hin_ts' as [HnU Hin_ts]. simpl in HnU.
      assert (Hτ_pop_ts : τ ∈ pop_of_trace ts).
      { apply (list_elem_of_fmap_2 fst _ (τ, Call Pop #())).
        apply list_elem_of_filter; split; [done|exact Hin_ts]. }
      destruct (decide (τ ∈ upop)) as [Hin_upop|Hnin_upop].
      * (* τ unpaired pop, but not in U → τ ∈ (m++nm1).*2 *)
        assert (Hτ_in_match : τ ∈ (m ++ nm1).*2).
        { destruct (decide (τ ∈ (m ++ nm1).*2)) as [|Habs]; first done.
          exfalso. apply HnU. apply list_elem_of_difference. done. }
        left.
        rewrite !fmap_app !elem_of_app in Hτ_in_match |- *.
        destruct Hτ_in_match as [Hl|Hr]; [by left|right; left; done].
      * (* τ has Ret in ts (not in upop). *)
        rewrite Hupop_is in Hnin_upop.
        assert (Hret_in : τ ∈ (filter (is_ret_pop ∘ snd) ts).*1).
        { rewrite /unpaired_operations in Hnin_upop.
          destruct (decide (τ ∈ (filter (is_ret_pop ∘ snd) ts).*1)) as [|Habs]; first done.
          exfalso. apply Hnin_upop.
          apply list_elem_of_difference. split.
          - apply (list_elem_of_fmap_2 fst _ (τ, Call Pop #())).
            apply list_elem_of_filter; split; [done|exact Hin_ts].
          - exact Habs. }
        apply list_elem_of_fmap_1 in Hret_in as ([τ_r ev_r] & Heq_τ & Hin_ret).
        simpl in Heq_τ. subst τ_r.
        apply list_elem_of_filter in Hin_ret as [Hev_pop Hin_ret_ts].
        rewrite /is_ret_pop in Hev_pop. simpl in Hev_pop.
        destruct Hev_pop as [r ->].
        destruct r as [|w].
        -- (* IsEmpty: covered by middle case *)
           right. left.
           assert (Hpreserved : (τ, Ret (encode_response IsEmpty)) ∈ ts').
           { rewrite /ts'. apply list_elem_of_filter_2; done. }
           apply elem_of_app. left. exact Hpreserved.
        -- (* NonEmpty w: τ ∈ pop_val_of_trace ts ⊆ m.*2 *)
           left.
           assert (Hpop_val : τ ∈ pop_val_of_trace ts).
           { rewrite /pop_val_of_trace.
             apply (list_elem_of_fmap_2 fst _ (τ, Ret (encode_response (NonEmpty w)))).
             apply list_elem_of_filter; split; [eexists; done|exact Hin_ret_ts]. }
           specialize (Hcov τ Hpop_val).
           rewrite !fmap_app !elem_of_app. by left.
    + (* τ in np ++ npop2_calls ++ npop1 ++ npop2_rets: only npop2_calls has Call Pop *)
      apply elem_of_app in Hin_rest as [Hin_np|Hin_rest].
      { exfalso.
        apply complete_trace_add_push_elem in Hin_np as [Habs _]. discriminate. }
      apply elem_of_app in Hin_rest as [Hin_npop2_calls|Hin_rest].
      { (* npop2_calls: τ has Call Pop and is in nm2.*2 *)
        rewrite /npop2_calls /close_trace_add_pop_calls in Hin_npop2_calls.
        apply list_elem_of_fmap_1 in Hin_npop2_calls as ([τ1 τ2] & Heq & Hin_nm2).
        simplify_eq.
        left.
        rewrite !fmap_app !elem_of_app. right. right.
        apply (list_elem_of_fmap_2 snd _ (τ1, τ2)). exact Hin_nm2. }
      apply elem_of_app in Hin_rest as [Hin_npop1|Hin_npop2_rets].
      { exfalso.
        apply complete_trace_remove_pop_elem in Hin_npop1 as [Habs _].
        rewrite /is_ret in Habs. done. }
      (* npop2_rets *)
      exfalso.
      rewrite /npop2_rets /close_trace_add_pop_rets in Hin_npop2_rets.
      apply list_elem_of_fmap_1 in Hin_npop2_rets as ([τ1 τ2] & Heq & _).
      injection Heq as _ Habs. discriminate.
Qed.
(* End LLM-generated code. *)
(**********************************************************)
