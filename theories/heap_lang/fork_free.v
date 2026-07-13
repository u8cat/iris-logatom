(* Most of this file is LLM-generated *)
(* Claude Opus 4.7 (1M context) *)

From iris_logatom.pure_logic Require Import adequacy.
From iris.heap_lang Require Import lang.
From iris.prelude Require Import options.

(** [fork_free e] returns [true] when [e] syntactically contains no [Fork]
  and no construct that reads a value out of the heap ([Load], [Xchg],
  [CmpXchg]). The intent is that evaluating a [fork_free] expression
  can never spawn a thread: [Fork] is the only construct that adds to
  the thread pool, and ruling out heap reads whose result type is
  unconstrained ([Load], [Xchg], [CmpXchg]) prevents reduction from
  producing values whose closure bodies could not be inspected
  statically. [FAA] is allowed since its successful result is always a
  [LitInt]. We check recursively inside [RecV] bodies and nested values
  so that values produced by reduction remain fork-free. *)
Fixpoint fork_free (e : expr) : bool :=
  match e with
  | Val v => val_fork_free v
  | Var _ => true
  | Rec _ _ e => fork_free e
  | App e1 e2 => fork_free e1 && fork_free e2
  | UnOp _ e => fork_free e
  | BinOp _ e1 e2 => fork_free e1 && fork_free e2
  | If e0 e1 e2 => fork_free e0 && fork_free e1 && fork_free e2
  | Pair e1 e2 => fork_free e1 && fork_free e2
  | Fst e => fork_free e
  | Snd e => fork_free e
  | InjL e => fork_free e
  | InjR e => fork_free e
  | Case e0 e1 e2 => fork_free e0 && fork_free e1 && fork_free e2
  | AllocN e1 e2 => fork_free e1 && fork_free e2
  | Free e => fork_free e
  | Load _ => false
  | Store e1 e2 => fork_free e1 && fork_free e2
  | CmpXchg _ _ _ => false
  | Xchg _ _ => false
  | FAA e1 e2 => fork_free e1 && fork_free e2
  | Fork _ => false
  | NewProph => true
  | Resolve e0 e1 e2 => fork_free e0 && fork_free e1 && fork_free e2
  end
with val_fork_free (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV _ _ e => fork_free e
  | PairV v1 v2 => val_fork_free v1 && val_fork_free v2
  | InjLV v => val_fork_free v
  | InjRV v => val_fork_free v
  end.

(** * Preservation of [fork_free] under reduction. *)

Lemma un_op_eval_val_fork_free op v v' :
  un_op_eval op v = Some v' → val_fork_free v' = true.
Proof.
  rewrite /un_op_eval.
  destruct op, v as [l| | | |]; try destruct l; simpl;
    intros H; inversion H; done.
Qed.

Lemma bin_op_eval_val_fork_free op v1 v2 v' :
  bin_op_eval op v1 v2 = Some v' → val_fork_free v' = true.
Proof.
  intros H.
  assert (∃ l, v' = LitV l) as [? ->]; [|done].
  rewrite /bin_op_eval /bin_op_eval_int /bin_op_eval_bool /bin_op_eval_loc in H.
  repeat case_match; simpl in H; simplify_eq; by eexists.
Qed.

Lemma fork_free_subst y v e :
  val_fork_free v = true →
  fork_free e = true →
  fork_free (subst y v e) = true.
Proof.
  intros Hv. revert y.
  induction e; intros y Hff; simpl in *; try done.
  - (* Var *) case_decide; done.
  - (* Rec *) case_decide; simpl; auto.
  - (* App *) apply andb_prop in Hff as [H1 H2].
    rewrite andb_true_iff; split; auto.
  - (* UnOp *) by auto.
  - (* BinOp *) apply andb_prop in Hff as [H1 H2].
    rewrite andb_true_iff; split; auto.
  - (* If *) apply andb_prop in Hff as [Hff H3]. apply andb_prop in Hff as [H1 H2].
    rewrite !andb_true_iff; split; [split|]; auto.
  - (* Pair *) apply andb_prop in Hff as [H1 H2].
    rewrite andb_true_iff; split; auto.
  - (* Fst *) by auto.
  - (* Snd *) by auto.
  - (* InjL *) by auto.
  - (* InjR *) by auto.
  - (* Case *) apply andb_prop in Hff as [Hff H3]. apply andb_prop in Hff as [H1 H2].
    rewrite !andb_true_iff; split; [split|]; auto.
  - (* AllocN *) apply andb_prop in Hff as [H1 H2].
    rewrite andb_true_iff; split; auto.
  - (* Free *) by auto.
  - (* Store *) apply andb_prop in Hff as [H1 H2].
    rewrite andb_true_iff; split; auto.
  - (* FAA *) apply andb_prop in Hff as [H1 H2].
    rewrite andb_true_iff; split; auto.
  - (* Resolve *) apply andb_prop in Hff as [Hff H3]. apply andb_prop in Hff as [H1 H2].
    rewrite !andb_true_iff; split; [split|]; auto.
Qed.

Lemma fork_free_subst' mx v e :
  val_fork_free v = true →
  fork_free e = true →
  fork_free (subst' mx v e) = true.
Proof.
  destruct mx; simpl; [done|apply fork_free_subst].
Qed.

Lemma fork_free_base_step e σ κ e' σ' efs :
  base_step e σ κ e' σ' efs →
  fork_free e = true →
  fork_free e' = true ∧ efs = [].
Proof.
  induction 1; intros Hff; simpl in *; try done.
  - (* BetaS *) apply andb_prop in Hff as [Hrec Hv2]. simpl in Hrec.
    split; [|done].
    subst. apply fork_free_subst'; [done|].
    apply fork_free_subst'; [simpl; done|done].
  - (* UnOpS *) split; [|done]. by eapply un_op_eval_val_fork_free.
  - (* BinOpS *) split; [|done]. by eapply bin_op_eval_val_fork_free.
  - (* IfTrueS *) rewrite andb_true_iff in Hff. tauto.
  - (* IfFalseS *) rewrite andb_true_iff in Hff. tauto.
  - (* FstS *) apply andb_prop in Hff. tauto.
  - (* SndS *) apply andb_prop in Hff. tauto.
  - (* CaseLS *) apply andb_prop in Hff as [Hff Hfe2]. apply andb_prop in Hff as [Hfv Hfe1].
    split; [|done]. simpl. rewrite Hfe1 Hfv //.
  - (* CaseRS *) apply andb_prop in Hff as [Hff Hfe2]. apply andb_prop in Hff as [Hfv Hfe1].
    split; [|done]. simpl. rewrite Hfe2 Hfv //.
  - (* ResolveS *) apply andb_prop in Hff as [Hff Hw]. apply andb_prop in Hff as [He Hp].
    eauto.
Qed.

(** Helpers for [prim_step]: evaluation contexts preserve [fork_free]. *)

Lemma fork_free_fill_item_inv Ki e :
  fork_free (fill_item Ki e) = true → fork_free e = true.
Proof.
  revert e. induction Ki; intros e Hff; simpl in Hff;
    try discriminate; try done;
    repeat (apply andb_prop in Hff as [Hff ?]); try done.
  eauto.
Qed.

Lemma fork_free_fill_item_preserve Ki e e' :
  fork_free (fill_item Ki e) = true →
  fork_free e' = true →
  fork_free (fill_item Ki e') = true.
Proof.
  revert e e'. induction Ki; intros e e' Hff Hff'; simpl in *;
    try discriminate; try done;
    repeat (apply andb_prop in Hff as [Hff ?]);
    repeat (rewrite andb_true_iff); eauto 10.
Qed.

Lemma fork_free_fill_inv K e :
  fork_free (fill K e) = true → fork_free e = true.
Proof.
  revert e. induction K as [|Ki K IH] using rev_ind; intros e Hff; [done|].
  rewrite fill_app /= in Hff.
  apply IH. by apply fork_free_fill_item_inv in Hff.
Qed.

Lemma fork_free_fill_preserve K e e' :
  fork_free (fill K e) = true →
  fork_free e' = true →
  fork_free (fill K e') = true.
Proof.
  revert e e'. induction K as [|Ki K IH] using rev_ind;
    intros e e' Hff Hff'; [done|].
  rewrite !fill_app /= in Hff |- *.
  eapply fork_free_fill_item_preserve; [done|].
  eapply IH; [|done]. by apply fork_free_fill_item_inv in Hff.
Qed.

Lemma fork_free_prim_step e σ κ e' σ' efs :
  prim_step e σ κ e' σ' efs →
  fork_free e = true →
  fork_free e' = true ∧ efs = [].
Proof.
  intros [K e1 e2 -> -> Hbase] Hff.
  apply fork_free_fill_inv in Hff as Hff1.
  destruct (fork_free_base_step _ _ _ _ _ _ Hbase Hff1) as [Hff2 ->].
  split; [|done].
  eapply fork_free_fill_preserve; [exact Hff|exact Hff2].
Qed.

(** * Lifting to configurations and [rtc erased_step]. *)

Lemma erased_step_singleton_fork_free e σ t2 σ2 :
  fork_free e = true →
  erased_step ([e], σ) (t2, σ2) →
  ∃ e', t2 = [e'] ∧ fork_free e' = true.
Proof.
  intros Hff [κ Hstep].
  destruct Hstep as [e1 σ1 e2 σ2' efs t1 ttl Heq1 Heq2 Hprim].
  destruct t1 as [|x t1]; simplify_eq/=.
  - destruct (fork_free_prim_step _ _ _ _ _ _ Hprim Hff) as [Hff' ->].
    by eexists.
  - destruct t1; discriminate.
Qed.

Lemma rtc_erased_step_fork_free (ρ1 ρ2 : cfg heap_ectx_lang) :
  rtc erased_step ρ1 ρ2 →
  (∃ e, ρ1.1 = [e] ∧ fork_free e = true) →
  (∃ e', ρ2.1 = [e'] ∧ fork_free e' = true).
Proof.
  induction 1 as [|ρ ρ' ρ'' Hstep Hrtc IH]; auto.
  intros (e & Hpool & Hff_e).
  destruct ρ as [t σ]. simpl in Hpool. subst t.
  destruct ρ' as [t' σ'].
  destruct (erased_step_singleton_fork_free _ _ _ _ Hff_e Hstep) as (e'' & -> & Hff'').
  apply IH. simpl. by eexists.
Qed.

Lemma rtc_erased_step_singleton_fork_free e σ t2 σ2 :
  fork_free e = true →
  rtc erased_step ([e], σ) (t2, σ2) →
  ∃ e', t2 = [e'] ∧ fork_free e' = true.
Proof.
  intros Hff Hrtc.
  apply (rtc_erased_step_fork_free ([e], σ) (t2, σ2) Hrtc).
  simpl. by eexists.
Qed.

Lemma fork_free_sequential e :
  fork_free e = true → ∀ σ, sequential e σ.
Proof.
  intros Hff σ t2 σ2 Hrtc.
  destruct (rtc_erased_step_singleton_fork_free _ _ _ _ Hff Hrtc)
    as (e' & -> & _).
  reflexivity.
Qed.
