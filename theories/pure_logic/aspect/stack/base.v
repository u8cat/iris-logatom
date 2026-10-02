From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Export bag.base.

(* The premise of the trace-level stack theorem.

   Besides the match [m] (push, pop) of the bag theory, the prover maintains an
   insert-remove relation in the sense of Dodds, Haas, and Kirsch (POPL'15), built
   incrementally: [ir] contains edges (x, p) meaning "push x is ordered before the
   matched pop p". The edges of p are fixed when p is matched; every other pair of a
   (called) push and a matched pop is implicitly ordered pop-before-push. Hence pushes
   called later are automatically after p, and the already constructed part of the
   relation never changes. *)

Section relations.
  Context (ts : list (positive * trace)) (m : list (positive * positive))
    (ir : list (positive * positive)).

  Definition ir_rel : relation positive := λ a b,
    (a, b) ∈ ir ∨ (a ∈ m.*2 ∧ b ∈ push_of_trace ts ∧ (b, a) ∉ ir).

  (* precedence together with the insert-remove relation *)
  Definition stk_rel : relation positive := λ a b,
    pre_of_trace ts a b ∨ ir_rel a b.

  (* derived orders on pushes (ins) and pops (rem), Definition 3 of the paper *)
  Definition ins_tr : relation positive := λ a b,
    a ∈ push_of_trace ts ∧ b ∈ push_of_trace ts ∧
    (pre_of_trace ts a b ∨ ∃ c, pre_of_trace ts a c ∧ ir_rel c b).

  Definition rem_tr : relation positive := λ a b,
    pre_of_trace ts a b ∨ ∃ c, ir_rel a c ∧ ir_rel c b.

  Definition ir_wf : Prop :=
    ∀ x p, (x, p) ∈ ir → x ∈ push_of_trace ts ∧ p ∈ m.*2.

  Definition ir_acyclic : Prop :=
    ∀ τ, ¬ tc stk_rel τ τ.

  (* condition 2 of order-correctness (Definition 5), where the pushed element must be
     matched already *)
  Definition ir_lifo : Prop :=
    ∀ a pa b, (a, pa) ∈ m → pre_of_trace ts a pa → ins_tr a b → (b, pa) ∈ ir →
      ∃ pb, (b, pb) ∈ m ∧ ¬ rem_tr pa pb.
End relations.

Definition I_stack_pre ts m ir :=
    valid_match ts m
  ∧ per_tag_pop_empty_sound ts m
  ∧ ir_wf ts m ir
  ∧ ir_acyclic ts m ir
  ∧ ir_lifo ts m ir.

Definition I_stack ts := ∃ m ir, I_stack_pre ts m ir.

(* ====================================================================== *)
(* Generic facts about pre_of_trace and transitive closures.              *)
(* ====================================================================== *)

Lemma pre_of_trace_app_mono ts ts' τ1 τ2 :
  pre_of_trace ts τ1 τ2 → pre_of_trace (ts ++ ts') τ1 τ2.
Proof.
  rewrite /pre_of_trace.
  destruct (ret_of_tag ts τ1) as [[i x]|] eqn:Hr; simpl; [|done].
  destruct (call_of_tag ts τ2) as [[j y]|] eqn:Hc; simpl; [|done].
  intros Hlt.
  rewrite /ret_of_tag (list_find_app_l _ _ _ _ _ Hr) /=.
  by rewrite /call_of_tag (list_find_app_l _ _ _ _ _ Hc) /=.
Qed.

Lemma pre_of_trace_app_iff ts ts' τ1 τ2 :
  (∃ n v, (τ2, Call n v) ∈ ts) →
  pre_of_trace (ts ++ ts') τ1 τ2 ↔ pre_of_trace ts τ1 τ2.
Proof.
  intros Hcall. split; [by apply pre_of_trace_app_inv | apply pre_of_trace_app_mono].
Qed.

Lemma pre_of_trace_ret ts τ1 τ2 :
  pre_of_trace ts τ1 τ2 → ∃ r, (τ1, Ret r) ∈ ts.
Proof.
  rewrite /pre_of_trace.
  destruct (ret_of_tag ts τ1) as [[i [τ t]]|] eqn:Hr; simpl; [|done].
  intros _. apply list_find_Some in Hr as (Hlk & [Htag Hret] & _).
  simpl in Htag, Hret. subst τ. destruct t as [| |r]; try done.
  exists r. by eapply list_elem_of_lookup_2.
Qed.

Lemma pre_of_trace_call ts τ1 τ2 :
  pre_of_trace ts τ1 τ2 → ∃ n v, (τ2, Call n v) ∈ ts.
Proof.
  rewrite /pre_of_trace.
  destruct (ret_of_tag ts τ1) as [[i x]|]; simpl; [|done].
  destruct (call_of_tag ts τ2) as [[j [τ t]]|] eqn:Hc; simpl; [|done].
  intros _. apply list_find_Some in Hc as (Hlk & [Htag Hcall] & _).
  simpl in Htag, Hcall. subst τ. destruct t as [n v| |]; try done.
  exists n, v. by eapply list_elem_of_lookup_2.
Qed.

(* A path in [R'] avoiding the sink [s] of [R'] is a path in [R]. *)
Lemma tc_avoid_sink {A} (R R' : relation A) (s : A) :
  (∀ a b, R' a b → b ≠ s → R a b) →
  (∀ b, ¬ R' s b) →
  ∀ x y, tc R' x y → y ≠ s → tc R x y.
Proof.
  intros Hsub Hsink x y Hxy. induction Hxy as [x y Hxy|x z y Hxz Hzy IH]; intros Hy.
  - apply tc_once. by apply Hsub.
  - assert (Hz : z ≠ s).
    { intros ->. destruct Hzy as [? ? H|? ? ? H _]; by eapply Hsink. }
    eapply tc_l; [by apply Hsub | by apply IH].
Qed.

Lemma tc_sink_acyclic {A} `{!EqDecision A} (R R' : relation A) (s : A) :
  (∀ a b, R' a b → b ≠ s → R a b) →
  (∀ b, ¬ R' s b) →
  (∀ x, ¬ tc R x x) → ∀ x, ¬ tc R' x x.
Proof.
  intros Hsub Hsink Hacyc x Hx.
  destruct (decide (x = s)) as [->|Hne].
  - inversion Hx as [? ? H|? ? ? H _]; by eapply Hsink.
  - eapply Hacyc, tc_avoid_sink; done.
Qed.

Lemma tc_iff {A} (R R' : relation A) :
  (∀ a b, R a b ↔ R' a b) → ∀ x y, tc R x y ↔ tc R' x y.
Proof.
  intros Heq x y. split; intros H; induction H as [x y H|x z y H _ IH];
    (apply tc_once; by apply Heq) || (eapply tc_l; [by apply Heq|done]).
Qed.

(* ====================================================================== *)
(* Appending a call or return event.                                      *)
(* ====================================================================== *)

Lemma push_of_trace_snoc_ret ts τ r :
  push_of_trace (ts ++ [(τ, Ret r)]) = push_of_trace ts.
Proof.
  rewrite /push_of_trace filter_app filter_cons_False; last by intros [? ?].
  by rewrite filter_nil right_id_L.
Qed.

Lemma push_of_trace_snoc_call_sub ts τ n v x :
  x ∈ push_of_trace ts → x ∈ push_of_trace (ts ++ [(τ, Call n v)]).
Proof. rewrite /push_of_trace filter_app fmap_app elem_of_app. by left. Qed.

Lemma push_of_trace_snoc_call_inv ts τ n v x :
  x ∈ push_of_trace (ts ++ [(τ, Call n v)]) → x ∈ push_of_trace ts ∨ x = τ.
Proof.
  rewrite /push_of_trace filter_app fmap_app elem_of_app.
  intros [Hx|Hx]; [by left|right].
  apply list_elem_of_fmap_1 in Hx as ([y e] & -> & Hy).
  apply list_elem_of_filter in Hy as [_ Hy].
  apply list_elem_of_singleton in Hy. by simplify_eq.
Qed.

Lemma pre_snoc_ret_iff ts τ r a b :
  pre_of_trace (ts ++ [(τ, Ret r)]) a b ↔ pre_of_trace ts a b.
Proof.
  split; [|apply pre_of_trace_app_mono].
  intros Hpre. apply (pre_of_trace_app_inv ts [(τ, Ret r)]); last done.
  destruct (pre_of_trace_call _ _ _ Hpre) as (n & v & Hin).
  apply elem_of_app in Hin as [Hin|Hin]; first by eauto.
  apply list_elem_of_singleton in Hin. discriminate.
Qed.

Lemma pre_snoc_call_old ts τ n v a b :
  b ≠ τ →
  pre_of_trace (ts ++ [(τ, Call n v)]) a b ↔ pre_of_trace ts a b.
Proof.
  intros Hne. split; [|apply pre_of_trace_app_mono].
  intros Hpre. apply (pre_of_trace_app_inv ts [(τ, Call n v)]); last done.
  destruct (pre_of_trace_call _ _ _ Hpre) as (n' & v' & Hin).
  apply elem_of_app in Hin as [Hin|Hin]; first by eauto.
  apply list_elem_of_singleton in Hin. by simplify_eq.
Qed.

Lemma pre_snoc_call_new_l ts τ n v b :
  τ ∉ ts.*1 → ¬ pre_of_trace (ts ++ [(τ, Call n v)]) τ b.
Proof.
  intros Hfresh Hpre. destruct (pre_of_trace_ret _ _ _ Hpre) as [r Hin].
  apply elem_of_app in Hin as [Hin|Hin].
  - apply Hfresh. by apply (list_elem_of_fmap_2 fst _ (τ, Ret r)).
  - apply list_elem_of_singleton in Hin. discriminate.
Qed.

(* If precedence and the set of pushes do not change, the stack part of the premise is
   preserved. *)
Local Lemma ir_inv_transfer ts ts' m ir :
  (∀ a b, pre_of_trace ts' a b ↔ pre_of_trace ts a b) →
  push_of_trace ts' = push_of_trace ts →
  ir_wf ts m ir ∧ ir_acyclic ts m ir ∧ ir_lifo ts m ir →
  ir_wf ts' m ir ∧ ir_acyclic ts' m ir ∧ ir_lifo ts' m ir.
Proof.
  intros Hpre Hpush (Hwf & Hacyc & Hlifo).
  assert (Hrel : ∀ a b, ir_rel ts' m ir a b ↔ ir_rel ts m ir a b).
  { intros a b. by rewrite /ir_rel Hpush. }
  assert (Hstk : ∀ a b, stk_rel ts' m ir a b ↔ stk_rel ts m ir a b).
  { intros a b. by rewrite /stk_rel Hpre Hrel. }
  split_and!.
  - intros x p Hin. rewrite Hpush. by apply Hwf.
  - intros τ Hτ. apply (Hacyc τ). by apply (tc_iff _ _ Hstk).
  - intros a pa b Hm Hpre_apa (Ha & Hb & Hor) Hir.
    rewrite Hpre in Hpre_apa. rewrite Hpush in Ha Hb.
    assert (Hins : ins_tr ts m ir a b).
    { split_and!; [done|done|].
      destruct Hor as [Hp|(c & Hp & Hc)]; [left; by apply Hpre|].
      right. exists c. split; [by apply Hpre|by apply Hrel]. }
    destruct (Hlifo a pa b Hm Hpre_apa Hins Hir) as (pb & Hpb & Hrem).
    exists pb. split; first done.
    intros [Hp|(c & H1 & H2)]; apply Hrem; [left; by apply Hpre|].
    right. exists c. split; by apply Hrel.
Qed.

Lemma ir_inv_snoc_ret ts m ir τ r :
  ir_wf ts m ir ∧ ir_acyclic ts m ir ∧ ir_lifo ts m ir →
  ir_wf (ts ++ [(τ, Ret r)]) m ir ∧ ir_acyclic (ts ++ [(τ, Ret r)]) m ir ∧
  ir_lifo (ts ++ [(τ, Ret r)]) m ir.
Proof. apply ir_inv_transfer; [apply pre_snoc_ret_iff|apply push_of_trace_snoc_ret]. Qed.

(* A fresh call has only incoming edges, so it cannot close a cycle or create a new
   instance of the LIFO condition. *)
Lemma ir_inv_snoc_call ts m ir τ n v :
  valid_match ts m → τ ∉ ts.*1 →
  ir_wf ts m ir ∧ ir_acyclic ts m ir ∧ ir_lifo ts m ir →
  ir_wf (ts ++ [(τ, Call n v)]) m ir ∧ ir_acyclic (ts ++ [(τ, Call n v)]) m ir ∧
  ir_lifo (ts ++ [(τ, Call n v)]) m ir.
Proof.
  intros Hvm Hfresh (Hwf & Hacyc & Hlifo).
  set (ts' := ts ++ [(τ, Call n v)]).
  assert (Hτ_m2 : τ ∉ m.*2).
  { intros ([x y] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst y.
    apply Hfresh. apply (list_elem_of_fmap_2 fst _ (τ, Call Pop #())).
    exact (valid_match_call_pop _ _ _ _ Hvm Hin). }
  assert (Hτ_push : τ ∉ push_of_trace ts).
  { intros Hp. apply push_tag_in_trace in Hp as [w Hw]. apply Hfresh.
    by apply (list_elem_of_fmap_2 fst _ (τ, Call Push w)). }
  assert (Hτ_ir1 : ∀ y, (τ, y) ∉ ir) by (intros y Hin; by apply Hτ_push, (Hwf τ y Hin)).
  assert (Hrel_old : ∀ a b, b ≠ τ → ir_rel ts' m ir a b ↔ ir_rel ts m ir a b).
  { intros a b Hb. rewrite /ir_rel. split.
    - intros [Hin|(Ha & Hbp & Hn)]; [by left|right; split_and!; try done].
      destruct (push_of_trace_snoc_call_inv ts τ n v b Hbp) as [?| ->]; [done|congruence].
    - intros [Hin|(Ha & Hbp & Hn)]; [by left|right; split_and!; try done].
      by apply push_of_trace_snoc_call_sub. }
  assert (Hrel_new : ∀ b, ¬ ir_rel ts' m ir τ b).
  { intros b [Hin|(Ha & _)]; [by eapply Hτ_ir1|done]. }
  assert (Hstk_old : ∀ a b, stk_rel ts' m ir a b → b ≠ τ → stk_rel ts m ir a b).
  { intros a b [Hp|Hr] Hb; [left; by apply (pre_snoc_call_old ts τ n v) in Hp|].
    right. by apply Hrel_old. }
  assert (Hstk_new : ∀ b, ¬ stk_rel ts' m ir τ b).
  { intros b [Hp|Hr]; [exact (pre_snoc_call_new_l ts τ n v b Hfresh Hp)|exact (Hrel_new b Hr)]. }
  split_and!.
  - intros x p Hin. destruct (Hwf x p Hin). split; [by apply push_of_trace_snoc_call_sub|done].
  - exact (tc_sink_acyclic _ _ τ Hstk_old Hstk_new Hacyc).
  - intros a pa b Hm Hpre_apa (Ha & Hb & Hor) Hir.
    assert (Hb_old : b ∈ push_of_trace ts) by (by destruct (Hwf b pa Hir)).
    assert (Hbτ : b ≠ τ) by (intros ->; done).
    assert (Hpaτ : pa ≠ τ).
    { intros ->. apply Hτ_m2. by apply (list_elem_of_fmap_2 snd _ (a, τ)). }
    assert (Haτ : a ≠ τ) by (intros ->; exact (pre_snoc_call_new_l ts τ n v pa Hfresh Hpre_apa)).
    apply (pre_snoc_call_old ts τ n v) in Hpre_apa; last done.
    assert (Hins : ins_tr ts m ir a b).
    { split_and!.
      - destruct (push_of_trace_snoc_call_inv ts τ n v a Ha) as [?| ->]; [done|congruence].
      - done.
      - destruct Hor as [Hp|(c & Hp & Hc)].
        + left. by apply (pre_snoc_call_old ts τ n v) in Hp.
        + right. exists c.
          assert (Hcτ : c ≠ τ) by (intros ->; by eapply Hrel_new; eassumption).
          split; [by apply (pre_snoc_call_old ts τ n v) in Hp|by apply Hrel_old]. }
    destruct (Hlifo a pa b Hm Hpre_apa Hins Hir) as (pb & Hpb & Hrem).
    exists pb. split; first done.
    assert (Hpbτ : pb ≠ τ).
    { intros ->. apply Hτ_m2. by apply (list_elem_of_fmap_2 snd _ (b, τ)). }
    intros [Hp|(c & H1 & H2)]; apply Hrem.
    + left. by apply (pre_snoc_call_old ts τ n v) in Hp.
    + right. exists c.
      assert (Hcτ : c ≠ τ) by (intros ->; by eapply Hrel_new; eassumption).
      split; [by apply Hrel_old in H1|by apply Hrel_old in H2].
Qed.

(* ====================================================================== *)
(* The premise under trace events.                                        *)
(* ====================================================================== *)

Lemma I_stack_pre_nil : I_stack_pre [] [] [].
Proof.
  assert (Hno : ∀ a b, ¬ stk_rel [] [] [] a b).
  { intros a b [Hp|[Hin|(Hin & _)]]; [by apply pre_of_trace_ret in Hp as [? ?%elem_of_nil]
                                       |set_solver|set_solver]. }
  split_and!.
  - apply valid_match_nil.
  - apply per_tag_pop_empty_sound_nil.
  - intros x p Hin. set_solver.
  - intros τ Hτ. inversion Hτ as [? ? H|? ? ? H _]; by eapply Hno.
  - intros a pa b Hin. set_solver.
Qed.

Lemma I_stack_nil : I_stack [].
Proof. exists [], []. apply I_stack_pre_nil. Qed.

Lemma I_stack_pre_snoc_call_push ts m ir τ v :
  I_stack_pre ts m ir → τ ∉ ts.*1 →
  I_stack_pre (ts ++ [(τ, Call Push v)]) m ir.
Proof.
  intros (Hvm & Hps & Hir) Hfresh.
  destruct (ir_inv_snoc_call ts m ir τ Push v Hvm Hfresh Hir) as (? & ? & ?).
  split_and!; try done.
  - by apply valid_match_snoc_call_push.
  - by apply per_tag_pop_empty_sound_snoc_call_push.
Qed.

Lemma I_stack_pre_snoc_call_pop ts m ir τ :
  I_stack_pre ts m ir → τ ∉ ts.*1 →
  I_stack_pre (ts ++ [(τ, Call Pop #())]) m ir.
Proof.
  intros (Hvm & Hps & Hir) Hfresh.
  destruct (ir_inv_snoc_call ts m ir τ Pop #() Hvm Hfresh Hir) as (? & ? & ?).
  split_and!; try done.
  - by apply valid_match_snoc_call_pop.
  - by apply per_tag_pop_empty_sound_snoc_call_pop.
Qed.

Lemma I_stack_pre_snoc_ret_push ts m ir τ v :
  I_stack_pre ts m ir →
  filter (λ x, x.1 = τ) ts = [(τ, Call Push v)] →
  I_stack_pre (ts ++ [(τ, Ret #())]) m ir.
Proof.
  intros (Hvm & Hps & Hir) Hfilter.
  destruct (ir_inv_snoc_ret ts m ir τ #() Hir) as (? & ? & ?).
  split_and!; try done.
  - by eapply valid_match_snoc_ret_push.
  - by eapply per_tag_pop_empty_sound_snoc_ret_push.
Qed.

(* A pop may return EMPTY when some index between its call and now is covered neither
   by a matched pair nor by an unmatched push (see per_tag_pop_empty_sound). *)
Lemma I_stack_pre_snoc_ret_pop_empty ts m ir τ icall i :
  I_stack_pre ts m ir →
  τ ∉ m.*2 →
  filter (λ x, x.1 = τ) ts = [(τ, Call Pop #())] →
  ts !! icall = Some (τ, Call Pop #()) →
  icall ≤ i ≤ length ts →
  (∀ τ1 τ2, (τ1, τ2) ∈ m → ¬ push_pop_covers ts τ1 τ2 i) →
  (∀ τ1, τ1 ∈ push_of_trace ts ∧ τ1 ∉ m.*1 → ¬ dangling_push_covers ts τ1 i) →
  I_stack_pre (ts ++ [(τ, Ret (encode_response IsEmpty))]) m ir.
Proof.
  intros (Hvm & Hps & Hir) Hτm Hfilter Hicall Hi Hmatch Hdangle.
  destruct (ir_inv_snoc_ret ts m ir τ (encode_response IsEmpty) Hir) as (? & ? & ?).
  split_and!; try done.
  - by apply valid_match_snoc_ret_pop_empty.
  - by eapply per_tag_pop_empty_sound_snoc_ret_pop_empty.
Qed.

Lemma I_stack_pre_snoc_ret_pop_val rme valid_value ts m ir τ1 τ2 v :
  per_tag_wellformed_bag rme valid_value ts →
  I_stack_pre ts m ir →
  (τ1, τ2) ∈ m →
  (τ1, Call Push v) ∈ ts →
  filter (λ x, x.1 = τ2) ts = [(τ2, Call Pop #())] →
  I_stack_pre (ts ++ [(τ2, Ret (encode_response (NonEmpty v)))]) m ir.
Proof.
  intros Hwf (Hvm & Hps & Hir) Hin Hcall Hfilter.
  destruct (ir_inv_snoc_ret ts m ir τ2 (encode_response (NonEmpty v)) Hir) as (? & ? & ?).
  split_and!; try done.
  - by eapply valid_match_snoc_ret_pop_val.
  - by eapply per_tag_pop_empty_sound_snoc_ret_pop_val.
Qed.

(* ====================================================================== *)
(* Matching a pending pop: the only step that extends m and ir.           *)
(* ====================================================================== *)

Local Lemma elem_of_ir_snoc (ir : list (positive * positive)) B p x y :
  (x, y) ∈ ir ++ ((λ z, (z, p)) <$> B) ↔ (x, y) ∈ ir ∨ (y = p ∧ x ∈ B).
Proof.
  rewrite elem_of_app list_elem_of_fmap. split.
  - intros [H|(z & Heq & Hz)]; [by left|right; by simplify_eq].
  - intros [H|[-> H]]; [by left|right; by exists x].
Qed.

Local Lemma tc_last {A} (R : relation A) x y :
  tc R x y → ∃ z, rtc R x z ∧ R z y.
Proof.
  induction 1 as [x y H|x z y H _ (z' & Hz' & Hz'y)].
  - exists x. split; [constructor|done].
  - exists z'. split; [by eapply rtc_l|done].
Qed.

(* When the pending pop p is matched with push b, the prover fixes the set B of pushes
   ordered before p; all other pushes (including future ones) are ordered after p. The
   local conditions:
   - C1: no push after p can reach (in the old relation) a push before p or an operation
     that precedes p;
   - C2: if b precedes p, every push before p that is ins-after b is already matched, and
     its pop has no push before it that is after p (so ¬ rem p pc);
   - C3: if an old pair (a, pa) has a ≺ p, every push c after p but before pa is matched
     with ¬ rem pa pc. *)
Lemma I_stack_pre_snoc_match rme valid_value ts m ir b p v (B : list positive) :
  per_tag_wellformed_bag rme valid_value ts →
  I_stack_pre ts m ir →
  b ∉ m.*1 → p ∉ m.*2 →
  (b, Call Push v) ∈ ts → (p, Call Pop #()) ∈ ts →
  p ∉ (filter (is_ret ∘ snd) ts).*1 →
  (∀ x, x ∈ B → x ∈ push_of_trace ts) →
  (∀ x u, x ∈ push_of_trace ts → x ∉ B → rtc (stk_rel ts m ir) x u →
     u ∈ B ∨ pre_of_trace ts u p → False) →
  (pre_of_trace ts b p → ∀ c, c ∈ B → c ≠ b → ins_tr ts m ir b c →
     ∃ pc, (c, pc) ∈ m ∧ ∀ e, e ∈ push_of_trace ts → e ∉ B → (e, pc) ∉ ir) →
  (∀ a pa c, (a, pa) ∈ m → pre_of_trace ts a pa → pre_of_trace ts a p →
     c ∈ push_of_trace ts → c ∉ B → c ≠ b → (c, pa) ∈ ir →
     ∃ pc, (c, pc) ∈ m ∧ ¬ rem_tr ts m ir pa pc) →
  I_stack_pre ts (m ++ [(b, p)]) (ir ++ ((λ x, (x, p)) <$> B)).
Proof.
  intros Hwf (Hvm & Hps & Hirwf & Hacyc & Hlifo) Hb_nm Hp_nm Hcall_b Hcall_p Hp_noret
    HB_push HC1 HC2 HC3.
  set (m' := m ++ [(b, p)]).
  set (ir' := ir ++ ((λ x, (x, p)) <$> B)).
  (* ---- basic facts about p and pushes ---- *)
  assert (Hp_pop : p ∈ pop_of_trace ts).
  { apply (list_elem_of_fmap_2 fst _ (p, Call Pop #())).
    by apply list_elem_of_filter_2. }
  assert (Hp_npush : p ∉ push_of_trace ts).
  { intros Hp. by eapply push_xor_pop_of_trace. }
  assert (Hb_push : b ∈ push_of_trace ts).
  { apply (list_elem_of_fmap_2 fst _ (b, Call Push v)).
    apply list_elem_of_filter_2; [by exists v|done]. }
  assert (Hm2_npush : ∀ q, q ∈ m.*2 → q ∉ push_of_trace ts).
  { intros q ([x y] & Heq & Hin)%list_elem_of_fmap_1 Hq. simpl in Heq. subst y.
    eapply (push_xor_pop_of_trace ts rme valid_value q Hwf Hq).
    apply (list_elem_of_fmap_2 fst _ (q, Call Pop #())).
    apply list_elem_of_filter_2; [done|exact (valid_match_call_pop _ _ _ _ Hvm Hin)]. }
  assert (Hpre_p : ∀ y, ¬ pre_of_trace ts p y).
  { intros y Hpre. destruct (pre_of_trace_ret _ _ _ Hpre) as [r Hr].
    apply Hp_noret. apply (list_elem_of_fmap_2 fst _ (p, Ret r)).
    by apply list_elem_of_filter_2. }
  assert (Hir_p2 : ∀ x, (x, p) ∉ ir).
  { intros x Hin. apply Hp_nm. by destruct (Hirwf x p Hin). }
  assert (Hir_p1 : ∀ y, (p, y) ∉ ir).
  { intros y Hin. apply Hp_npush. by destruct (Hirwf p y Hin). }
  assert (Hm'2 : ∀ q, q ∈ m'.*2 ↔ q ∈ m.*2 ∨ q = p).
  { intros q. by rewrite /m' fmap_app elem_of_app list_elem_of_singleton. }
  (* ---- the new relation ---- *)
  assert (E1 : ∀ x y, x ≠ p → y ≠ p → ir_rel ts m' ir' x y ↔ ir_rel ts m ir x y).
  { intros x y Hx Hy. rewrite /ir_rel !elem_of_ir_snoc Hm'2. split.
    - intros [[H|[? _]]|([H|?] & Hy' & Hn)]; [by left|done|right|done].
      split_and!; [done|done|]. intros Hin. apply Hn. by left.
    - intros [H|(H & Hy' & Hn)]; [by left; left|right].
      split_and!; [by left|done|]. intros [?|[? _]]; [done|done]. }
  assert (E2 : ∀ x, ir_rel ts m' ir' x p ↔ x ∈ B).
  { intros x. rewrite /ir_rel elem_of_ir_snoc. split.
    - intros [[H|[_ H]]|(_ & Hpp & _)]; [by destruct (Hir_p2 x)|done|done].
    - intros H. left. by right. }
  assert (E3 : ∀ y, ir_rel ts m' ir' p y ↔ y ∈ push_of_trace ts ∧ y ∉ B).
  { intros y. rewrite /ir_rel !elem_of_ir_snoc Hm'2. split.
    - intros [[H|[-> H]]|(_ & Hy & Hn)]; [by destruct (Hir_p1 y)|by apply HB_push in H|].
      split; [done|]. intros HyB. apply Hn. by right.
    - intros [Hy HyB]. right. split_and!; [by right|done|].
      intros [H|[_ H]]; [by destruct (Hir_p2 y)|done]. }
  set (R := stk_rel ts m ir).
  set (R' := stk_rel ts m' ir').
  assert (R'E1 : ∀ x y, x ≠ p → y ≠ p → R' x y ↔ R x y).
  { intros x y Hx Hy. rewrite /R /R' /stk_rel E1 //. }
  assert (R'_in : ∀ x, R' x p ↔ x ∈ B ∨ pre_of_trace ts x p).
  { intros x. rewrite /R' /stk_rel E2. tauto. }
  assert (R'_out : ∀ y, R' p y ↔ y ∈ push_of_trace ts ∧ y ∉ B).
  { intros y. rewrite /R' /stk_rel E3. split; [intros [H|H]; [by destruct (Hpre_p y)|done]|by right]. }
  assert (R_in : ∀ x, R x p → pre_of_trace ts x p).
  { intros x [H|[H|(_ & H & _)]]; [done|by destruct (Hir_p2 x)|done]. }
  (* ---- acyclicity ---- *)
  assert (Hsplit : ∀ x y, tc R' x y → x ≠ p →
            tc R x y ∨ ∃ w, rtc R x w ∧ (w ∈ B ∨ pre_of_trace ts w p) ∧ (y = p ∨ tc R' p y)).
  { intros x y Hxy. induction Hxy as [x y Hxy|x z y Hxz Hzy IH]; intros Hx.
    - destruct (decide (y = p)) as [->|Hy].
      + right. exists x. split_and!; [constructor|by apply R'_in|by left].
      + left. apply tc_once. by apply R'E1.
    - destruct (decide (z = p)) as [->|Hz].
      + right. exists x. split_and!; [constructor|by apply R'_in|by right].
      + assert (Hxz' : R x z) by (by apply R'E1).
        destruct (IH Hz) as [Hl|(w & Hw & Hin & Hy)].
        * left. by eapply tc_l.
        * right. exists w. split_and!; [by eapply rtc_l|done|done]. }
  assert (Hout : ∀ y, tc R' p y →
            ∃ c, c ∈ push_of_trace ts ∧ c ∉ B ∧ (c = y ∨ tc R' c y)).
  { intros y Hy. inversion Hy as [? ? H|? z ? H Hzy]; subst.
    - apply R'_out in H as [Hc HcB]. exists y. by split_and!; [| |left].
    - apply R'_out in H as [Hc HcB]. exists z. by split_and!; [| |right]. }
  assert (Hpush_ne_p : ∀ c, c ∈ push_of_trace ts → c ≠ p) by (intros c Hc ->; done).
  assert (Hacyc' : ∀ x, ¬ tc R' x x).
  { intros x Hx.
    destruct (decide (x = p)) as [->|Hxp].
    - destruct (Hout p Hx) as (c & Hc & HcB & [->|Hcp]); [by apply Hp_npush|].
      destruct (Hsplit c p Hcp (Hpush_ne_p c Hc)) as [HR|(w & Hw & Hin & _)].
      + destruct (tc_last _ _ _ HR) as (u & Hu & Hup).
        apply (HC1 c u Hc HcB Hu). right. by apply R_in.
      + exact (HC1 c w Hc HcB Hw Hin).
    - destruct (Hsplit x x Hx Hxp) as [HR|(w & Hw & Hin & [->|Hpx])]; [by eapply Hacyc|done|].
      destruct (Hout x Hpx) as (c & Hc & HcB & [<-|Hcx]); [exact (HC1 c w Hc HcB Hw Hin)|].
      destruct (Hsplit c x Hcx (Hpush_ne_p c Hc)) as [HR|(w' & Hw' & Hin' & _)].
      + apply (HC1 c w Hc HcB); [|done]. eapply rtc_trans; [by apply tc_rtc|exact Hw].
      + exact (HC1 c w' Hc HcB Hw' Hin'). }
  (* ---- rem between old pops is unchanged ---- *)
  assert (Hrem_old : ∀ pa pc, pa ∈ m.*2 → pc ∈ m.*2 →
            rem_tr ts m' ir' pa pc → rem_tr ts m ir pa pc).
  { intros pa pc Hpa Hpc [H|(e & H1 & H2)]; [by left|right].
    assert (Hpap : pa ≠ p) by (intros ->; done).
    assert (Hpcp : pc ≠ p) by (intros ->; done).
    assert (Hep : e ≠ p).
    { intros ->. apply E2, HB_push in H1. by apply (Hm2_npush pa). }
    exists e. split; [by apply E1 in H1|by apply E1 in H2]. }
  split_and!.
  - by eapply valid_match_snoc_match.
  - by eapply per_tag_pop_empty_sound_snoc_match.
  - intros x y Hin. apply elem_of_ir_snoc in Hin as [Hin|[-> HxB]].
    + destruct (Hirwf x y Hin). split; [done|]. apply Hm'2. by left.
    + split; [by apply HB_push|]. apply Hm'2. by right.
  - exact Hacyc'.
  - intros a pa c Hm' Hpre_apa (Ha & Hc & Hor) Hir'.
    apply elem_of_app in Hm' as [Hm|Hnew%list_elem_of_singleton].
    + (* an old pair *)
      assert (Hpa_m2 : pa ∈ m.*2) by (by apply (list_elem_of_fmap_2 snd _ (a, pa))).
      assert (Hpap : pa ≠ p) by (intros ->; done).
      apply elem_of_ir_snoc in Hir' as [Hir|[? _]]; last done.
      assert (Hold : ∀ pc, (c, pc) ∈ m → ¬ rem_tr ts m ir pa pc → ¬ rem_tr ts m' ir' pa pc).
      { intros pc Hpc Hn Hrem. apply Hn, Hrem_old; [done| |done].
        by apply (list_elem_of_fmap_2 snd _ (c, pc)). }
      assert (Hins_old : ins_tr ts m ir a c →
                ∃ pc, (c, pc) ∈ m' ∧ ¬ rem_tr ts m' ir' pa pc).
      { intros Hins. destruct (Hlifo a pa c Hm Hpre_apa Hins Hir) as (pc & Hpc & Hn).
        exists pc. split; [by apply elem_of_app; left|by apply Hold]. }
      destruct Hor as [Hp|(q & Hq & Hqc)]; [apply Hins_old; split_and!; [done|done|by left]|].
      destruct (decide (q = p)) as [->|Hqp].
      * apply E3 in Hqc as [_ HcB].
        destruct (decide (c = b)) as [->|Hcb].
        -- exists p. split; [by apply elem_of_app; right; left|].
           intros Hrem. apply (Hacyc' pa).
           assert (Hpa_p : tc R' pa p).
           { destruct Hrem as [H|(e & H1 & H2)].
             - apply tc_once. by left.
             - eapply tc_l; [by right|apply tc_once; by right]. }
           eapply tc_rtc_r; [exact Hpa_p|].
           eapply rtc_l; [apply R'_out; by split|].
           apply rtc_once. right. left. apply elem_of_ir_snoc. by left.
        -- destruct (HC3 a pa c Hm Hpre_apa Hq Hc HcB Hcb Hir) as (pc & Hpc & Hn).
           exists pc. split; [by apply elem_of_app; left|by apply Hold].
      * apply Hins_old. split_and!; [done|done|]. right. exists q.
        split; [done|]. apply E1 in Hqc; [done|done|by apply Hpush_ne_p].
    + (* the new pair *)
      injection Hnew as -> ->.
      apply elem_of_ir_snoc in Hir' as [Hir|[_ HcB]]; first by destruct (Hir_p2 c).
      destruct (decide (c = b)) as [->|Hcb].
      * exists p. split; [by apply elem_of_app; right; left|].
        intros [H|(e & H1 & H2)]; [by eapply Hpre_p|].
        apply E3 in H1 as [_ HeB]. by apply E2 in H2.
      * assert (Hins : ins_tr ts m ir b c).
        { split_and!; [done|done|].
          destruct Hor as [Hp|(q & Hq & Hqc)]; [by left|right].
          exists q. split; [done|].
          destruct (decide (q = p)) as [->|Hqp].
          - by apply E3 in Hqc as [_ ?].
          - apply E1 in Hqc; [done|done|by apply Hpush_ne_p]. }
        destruct (HC2 Hpre_apa c HcB Hcb Hins) as (pc & Hpc & Hno).
        exists pc. split; [by apply elem_of_app; left|].
        assert (Hpc_m2 : pc ∈ m.*2) by (by apply (list_elem_of_fmap_2 snd _ (c, pc))).
        assert (Hpcp : pc ≠ p) by (intros ->; done).
        intros [H|(e & H1 & H2)]; [by eapply Hpre_p|].
        apply E3 in H1 as [He HeB].
        apply E1 in H2; [|by apply Hpush_ne_p|done].
        destruct H2 as [H2|(H2 & _)]; [by apply (Hno e)|by apply (Hm2_npush e)].
Qed.
