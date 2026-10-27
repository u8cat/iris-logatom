(* complete.v: heap_lang steps from concretizations are concretizations of
   symbolic heap_lang steps. *)
(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From stdpp Require Import ssreflect list numbers list_numbers gmap.
From iris.program_logic Require Import language.
From iris_logatom.heap_lang.decide Require Export sound wf.
From iris.heap_lang Require Import lang.

(** * Lifting evaluation contexts *)

(** The symbolic context item of [e] corresponding to a concrete one *)
Fixpoint lift_item (Ki : ectx_item) (e : sexpr) {struct Ki} : option (sectx_item * sexpr) :=
  match Ki, e with
  | AppLCtx _, SApp e1 (SVal v2) => Some (SAppLCtx v2, e1)
  | AppRCtx _, SApp e1 e2 => Some (SAppRCtx e1, e2)
  | UnOpCtx _, SUnOp op e => Some (SUnOpCtx op, e)
  | BinOpLCtx _ _, SBinOp op e1 (SVal v2) => Some (SBinOpLCtx op v2, e1)
  | BinOpRCtx _ _, SBinOp op e1 e2 => Some (SBinOpRCtx op e1, e2)
  | IfCtx _ _, SIf e0 e1 e2 => Some (SIfCtx e1 e2, e0)
  | PairLCtx _, SPair e1 (SVal v2) => Some (SPairLCtx v2, e1)
  | PairRCtx _, SPair e1 e2 => Some (SPairRCtx e1, e2)
  | FstCtx, SFst e => Some (SFstCtx, e)
  | SndCtx, SSnd e => Some (SSndCtx, e)
  | InjLCtx, SInjL e => Some (SInjLCtx, e)
  | InjRCtx, SInjR e => Some (SInjRCtx, e)
  | CaseCtx _ _, SCase e0 e1 e2 => Some (SCaseCtx e1 e2, e0)
  | AllocNLCtx _, SAllocN e1 (SVal v2) => Some (SAllocNLCtx v2, e1)
  | AllocNRCtx _, SAllocN e1 e2 => Some (SAllocNRCtx e1, e2)
  | FreeCtx, SFree e => Some (SFreeCtx, e)
  | LoadCtx, SLoad e => Some (SLoadCtx, e)
  | StoreLCtx _, SStore e1 (SVal v2) => Some (SStoreLCtx v2, e1)
  | StoreRCtx _, SStore e1 e2 => Some (SStoreRCtx e1, e2)
  | XchgLCtx _, SXchg e1 (SVal v2) => Some (SXchgLCtx v2, e1)
  | XchgRCtx _, SXchg e1 e2 => Some (SXchgRCtx e1, e2)
  | CmpXchgLCtx _ _, SCmpXchg e0 (SVal v1) (SVal v2) => Some (SCmpXchgLCtx v1 v2, e0)
  | CmpXchgMCtx _ _, SCmpXchg e0 e1 (SVal v2) => Some (SCmpXchgMCtx e0 v2, e1)
  | CmpXchgRCtx _ _, SCmpXchg e0 e1 e2 => Some (SCmpXchgRCtx e0 e1, e2)
  | FaaLCtx _, SFAA e1 (SVal v2) => Some (SFaaLCtx v2, e1)
  | FaaRCtx _, SFAA e1 e2 => Some (SFaaRCtx e1, e2)
  | ResolveLCtx K _ _, SResolve e0 (SVal v1) (SVal v2) =>
    (λ Kie, (SResolveLCtx Kie.1 v1 v2, Kie.2)) <$> lift_item K e0
  | ResolveMCtx _ _, SResolve e0 e1 (SVal v2) => Some (SResolveMCtx e0 v2, e1)
  | ResolveRCtx _ _, SResolve e0 e1 e2 => Some (SResolveRCtx e0 e1, e2)
  | _, _ => None
  end.

Lemma ac_expr_val_inv ν e v : ac_expr ν e = Val v → ∃ va, e = SVal va ∧ ac_val ν va = v.
Proof. destruct e; simpl; try discriminate. intros [= <-]. by eexists. Qed.

Lemma ac_fill_item_inv ν e Ki e' :
  ac_expr ν e = fill_item Ki e' →
  ∃ sKi se', lift_item Ki e = Some (sKi, se') ∧
    e = sfill_item sKi se' ∧ ac_item ν sKi = Ki ∧ ac_expr ν se' = e'.
Proof.
  revert e e'. induction Ki; intros e e' Heq; destruct e; simpl in Heq;
    try discriminate Heq; injection Heq; intros; subst;
    repeat match goal with
    | H : ac_expr _ ?e = Val _ |- _ => apply ac_expr_val_inv in H as (? & -> & <-)
    end.
  (* [Resolve] around a context *)
  all: try lazymatch goal with
    | IH : ∀ e e', ac_expr _ e = fill_item ?K e' → _, H : ac_expr _ _ = fill_item ?K _ |- _ =>
      destruct (IH _ _ H) as (sKi & se' & Hlift & -> & <- & <-);
      eexists _, _; split_and!; [by rewrite /= Hlift|done|done|done]
    end.
  all: eexists _, _; split_and!; [reflexivity|done|done|done].
Qed.

Lemma ac_fill_inv ν e K e' :
  ac_expr ν e = @ectx_language.fill heap_ectx_lang K e' →
  ∃ sK se', e = @ectx_language.fill sym_heap_ectx_lang sK se' ∧
    ac_item ν <$> sK = K ∧ ac_expr ν se' = e'.
Proof.
  revert e'. induction K as [|Ki K IH]; intros e' Heq.
  { by exists [], e. }
  change (@ectx_language.fill heap_ectx_lang (Ki :: K) e') with
    (@ectx_language.fill heap_ectx_lang K (fill_item Ki e')) in Heq.
  destruct (IH _ Heq) as (sK & se'' & -> & <- & Hse'').
  destruct (ac_fill_item_inv ν se'' Ki e' Hse'') as (sKi & se' & _ & -> & <- & <-).
  exists (sKi :: sK), se'. split_and!; [done|done|done].
Qed.

(** * Valuations *)

(** Update the valuation at a fresh variable *)
Definition upd_valuation (ν : valuation) (x : nat) (z : Z) : valuation :=
  λ y, if decide (y = x) then z else ν y.

Lemma upd_valuation_agree ν x z y : (y < x)%nat → upd_valuation ν x z y = ν y.
Proof. intros Hy. rewrite /upd_valuation decide_False //. lia. Qed.

Lemma upd_valuation_eq ν x z : upd_valuation ν x z x = z.
Proof. by rewrite /upd_valuation decide_True. Qed.

Section agree.
  Context (ν ν' : valuation) (n : nat) (Hagree : ∀ x, (x < n)%nat → ν' x = ν x).

  Lemma term_eval_agree' t : term_wf n t → term_eval ν' t = term_eval ν t.
  Proof. apply term_eval_agree. intros x Hx. by apply Hagree. Qed.

  Lemma ac_val_agree v : sval_wf n v → ac_val ν' v = ac_val ν v.
  Proof. apply ac_agree. intros x Hx. by apply Hagree. Qed.

  Lemma ac_expr_agree e : sexpr_wf n e → ac_expr ν' e = ac_expr ν e.
  Proof. apply ac_agree. intros x Hx. by apply Hagree. Qed.

  Lemma atom_holds_agree α : atom_wf n α → atom_holds ν' α ↔ atom_holds ν α.
  Proof.
    intros [Hl Hr]. rewrite /atom_holds (term_eval_agree' _ Hl) (term_eval_agree' _ Hr) //.
  Qed.

  Lemma atoms_hold_agree cs : Forall (atom_wf n) cs → atoms_hold ν' cs ↔ atoms_hold ν cs.
  Proof.
    induction 1 as [|α cs Hα Hcs IH]; first (split; intros _; constructor).
    rewrite /atoms_hold !Forall_cons -/(atoms_hold ν' cs) -/(atoms_hold ν cs) IH.
    by rewrite (atom_holds_agree α Hα).
  Qed.
End agree.

Lemma ac_state_agree ν ν' σ :
  (∀ x, (x < snext σ)%nat → ν' x = ν x) → sstate_wf σ → ac_state ν' σ = ac_state ν σ.
Proof.
  intros Hagree (Hh & Hu & _). rewrite /ac_state /ac_heap. f_equal.
  - f_equal. apply list_fmap_ext. intros i [k c] Hi.
    apply (Forall_lookup_1 _ _ _ _ Hh) in Hi as [Hk Hc]. simpl in Hk, Hc |- *.
    rewrite /ac_loc /ac_cell (term_eval_agree' ν ν' _ Hagree _ Hk). f_equal.
    destruct c; simpl in Hc |- *; [by rewrite (ac_val_agree ν ν' _ Hagree _ Hc)|done].
  - f_equal. apply list_fmap_ext. intros i p Hi.
    apply (Forall_lookup_1 _ _ _ _ Hu) in Hi.
    by rewrite /ac_proph (term_eval_agree' ν ν' _ Hagree _ Hi).
Qed.

Lemma ssat_agree ν ν' σ :
  (∀ x, (x < snext σ)%nat → ν' x = ν x) → sstate_wf σ → ssat ν' σ ↔ ssat ν σ.
Proof. intros Hagree (_ & _ & Hc). by apply (atoms_hold_agree ν ν' (snext σ)). Qed.

(** * Completeness of heap lookups and operators *)
Section lookup.
  Context (ν : valuation).

  Lemma sheap_lookup_complete l h cc :
    ac_heap ν h !! ac_loc ν l = Some cc →
    ∃ c cs, (c, cs) ∈ sheap_lookup l h ∧ atoms_hold ν cs ∧ ac_cell ν c = cc.
  Proof.
    induction h as [|[k c'] h IH]; simpl; first done.
    rewrite /ac_heap fmap_cons list_to_map_cons /=.
    destruct (decide (ac_loc ν l = ac_loc ν k)) as [Heq|Hne].
    - rewrite Heq lookup_insert_eq. intros [= <-].
      exists c', [Atom CEq l k]. split_and!; [by apply elem_of_cons; left| |done].
      rewrite /atoms_hold Forall_singleton /atom_holds /=. by injection Heq.
    - rewrite lookup_insert_ne //. intros Hlookup.
      destruct (IH Hlookup) as (c & cs & Hin & Hcs & <-).
      exists c, (Atom CNe l k :: cs). split_and!; [| |done].
      + apply elem_of_cons. right. apply list_elem_of_fmap. by exists (c, cs).
      + rewrite /atoms_hold Forall_cons. split; last done.
        rewrite /atom_holds /=. intros Heq. apply Hne. by rewrite /ac_loc Heq.
  Qed.

  Lemma sstate_lookup_complete l σ v :
    heap (ac_state ν σ) !! ac_loc ν l = Some (Some v) →
    ∃ va cs, (va, cs) ∈ sstate_lookup l σ ∧ atoms_hold ν cs ∧ ac_val ν va = v.
  Proof.
    intros Hlookup. destruct (sheap_lookup_complete l (sheap σ) _ Hlookup)
      as ([va|] & cs & Hin & Hcs & Hva); simpl in Hva; last discriminate Hva.
    injection Hva as <-. exists va, cs. split_and!; [|done|done].
    apply list_elem_of_omap. by exists (Some va, cs).
  Qed.

  Lemma sun_op_eval_complete op va v :
    un_op_eval op (ac_val ν va) = Some v → ∃ va', sun_op_eval op va = Some va' ∧ ac_val ν va' = v.
  Proof.
    destruct op, va as [l| | | |]; try done; destruct l; simpl; try done.
    all: intros [= <-]; by eexists.
  Qed.

  Local Lemma int_bool_complete (o : option base_lit) v :
    (∀ l, o = Some l → ∃ sl, slit_of_int_bool l = Some sl ∧ ac_lit ν sl = l) →
    LitV <$> o = Some v →
    ∃ va cs, (va, cs) ∈ match o ≫= slit_of_int_bool with
        Some l => [(SLitV l, [])] | None => [] end ∧
      atoms_hold ν cs ∧ ac_val ν va = v.
  Proof.
    intros Hint Hv. destruct o as [l|]; simpl in Hv; last done. injection Hv as <-.
    destruct (Hint l eq_refl) as (sl & Hsl & <-). exists (SLitV sl), [].
    rewrite /= Hsl. split_and!; [by apply list_elem_of_singleton|constructor|done].
  Qed.

  Local Lemma bin_op_eval_int_lit op n1 n2 l :
    bin_op_eval_int op n1 n2 = Some l → ∃ sl, slit_of_int_bool l = Some sl ∧ ac_lit ν sl = l.
  Proof. destruct op; simpl; intros [= <-]; by eexists. Qed.

  Local Lemma bin_op_eval_bool_lit op b1 b2 l :
    bin_op_eval_bool op b1 b2 = Some l → ∃ sl, slit_of_int_bool l = Some sl ∧ ac_lit ν sl = l.
  Proof. destruct op; simpl; intros [= <-]; by eexists. Qed.

  Lemma sbin_op_eval_complete op v1 v2 v :
    bin_op_eval op (ac_val ν v1) (ac_val ν v2) = Some v →
    ∃ va cs, (va, cs) ∈ sbin_op_eval op v1 v2 ∧ atoms_hold ν cs ∧ ac_val ν va = v.
  Proof.
    rewrite /bin_op_eval /sbin_op_eval. case_decide; subst.
    - case_decide as Hsafe; last done. intros [= <-].
      apply ac_vals_compare_safe in Hsafe. rewrite Hsafe.
      destruct (sval_eq_branches_complete ν v1 v2) as (cs & Hin & Hcs).
      exists (SLitV (SLitBool (bool_decide (ac_val ν v1 = ac_val ν v2)))), cs.
      split_and!; [|done|done].
      apply list_elem_of_fmap. by exists (bool_decide (ac_val ν v1 = ac_val ν v2), cs).
    - destruct v1 as [l1| | | |]; try done. destruct l1; try done.
      all: destruct v2 as [l2| | | |]; try done.
      all: destruct l2; simpl; try done.
      (* integers and booleans *)
      all: try (apply int_bool_complete; intros l Hl;
        first [by eapply bin_op_eval_int_lit|by eapply bin_op_eval_bool_lit]).
      (* locations *)
      all: destruct op; simpl; try done; intros [= <-].
      1: { eexists _, []. split_and!; [apply list_elem_of_singleton; reflexivity|constructor|].
           by rewrite /= ac_loc_add. }
      all: case_bool_decide as Hcmp; rewrite /Loc.le /Loc.lt /ac_loc /= in Hcmp.
      all: lazymatch goal with
        | |- ∃ va cs, (va, cs) ∈ [(?a, ?ca); (?b, ?cb)] ∧ _ ∧ ac_val _ va = LitV (LitBool true) =>
          exists a, ca; split_and!; [by apply elem_of_cons; left| |done]
        | |- ∃ va cs, (va, cs) ∈ [(?a, ?ca); (?b, ?cb)] ∧ _ ∧ ac_val _ va = LitV (LitBool false) =>
          exists b, cb; split_and!; [by rewrite !elem_of_cons; right; left| |done]
        end.
      all: rewrite /atoms_hold Forall_singleton /atom_holds /=; lia.
  Qed.
End lookup.

(** * Fresh names *)
Section fresh.
  Context (ν : valuation).

  Lemma alloc_complete σ n v l :
    ssat ν σ → sstate_wf σ → sval_wf (snext σ) v →
    (∀ i, (0 ≤ i)%Z → (i < n)%Z → heap (ac_state ν σ) !! (l +ₗ i) = None) →
    let ν' := upd_valuation ν (snext σ) (loc_car l) in
    ssat ν' (sstate_alloc n v σ) ∧
    ac_state ν' (sstate_alloc n v σ) = state_init_heap l n (ac_val ν v) (ac_state ν σ) ∧
    ac_loc ν' (Term (Some (snext σ)) 0) = l.
  Proof.
    intros Hsat Hwfσ Hwfv Hfresh ν'.
    assert (∀ x, (x < snext σ)%nat → ν' x = ν x) as Hagree.
    { intros x Hx. by apply upd_valuation_agree. }
    assert (ac_loc ν' (Term (Some (snext σ)) 0) = l) as Hl.
    { destruct l as [z]. rewrite /ac_loc /term_eval /term_base /ν' /= upd_valuation_eq.
      f_equal. lia. }
    split_and!; last done.
    - apply atoms_hold_app. split; last by apply (ssat_agree ν ν').
      apply Forall_forall. intros α (i & Hα & Hi%elem_of_seqZ)%list_elem_of_bind.
      apply list_elem_of_fmap in Hα as (kc & -> & Hkc).
      destruct Hwfσ as (Hh & _ & _).
      pose proof (proj1 (Forall_forall _ _) Hh kc Hkc) as [Hwfk _].
      rewrite /atom_holds /= (term_eval_agree' ν ν' _ Hagree _ Hwfk).
      intros Heq. specialize (Hfresh i ltac:(lia) ltac:(lia)).
      apply ((proj1 (ac_heap_lookup_None ν (sheap σ) _) Hfresh) kc Hkc).
      rewrite /ac_loc -Heq. destruct l as [z]. rewrite /Loc.add /term_eval /term_base /=.
      rewrite /ν' upd_valuation_eq. f_equal; lia.
    - rewrite ac_state_alloc Hl (ac_val_agree ν ν' _ Hagree _ Hwfv).
      by rewrite (ac_state_agree ν ν' σ Hagree Hwfσ).
  Qed.

  Lemma new_proph_complete σ p :
    ssat ν σ → sstate_wf σ → p ∉ used_proph_id (ac_state ν σ) →
    let ν' := upd_valuation ν (snext σ) (Z_of_proph p) in
    ssat ν' (sstate_new_proph σ) ∧
    ac_state ν' (sstate_new_proph σ) =
      state_upd_used_proph_id ({[p]} ∪.) (ac_state ν σ) ∧
    ac_proph ν' (Term (Some (snext σ)) 0) = p.
  Proof.
    intros Hsat Hwfσ Hfresh ν'.
    assert (∀ x, (x < snext σ)%nat → ν' x = ν x) as Hagree.
    { intros x Hx. by apply upd_valuation_agree. }
    assert (ac_proph ν' (Term (Some (snext σ)) 0) = p) as Hp.
    { rewrite /ac_proph /term_eval /term_base /ν' /= upd_valuation_eq Z.add_0_r.
      apply proph_of_Z_of_proph. }
    split_and!; last done.
    - apply atoms_hold_app. split; last by apply (ssat_agree ν ν').
      apply Forall_fmap, Forall_forall. intros q Hq.
      destruct Hwfσ as (_ & Hu & _).
      pose proof (proj1 (Forall_forall _ _) Hu q Hq) as Hwfq.
      rewrite /atom_holds /= (term_eval_agree' ν ν' _ Hagree _ Hwfq).
      intros Heq. apply Hfresh. rewrite /= elem_of_list_to_set list_elem_of_fmap.
      exists q. split; last done. rewrite -Hp /ac_proph Heq. done.
    - rewrite ac_state_new_proph Hp. by rewrite (ac_state_agree ν ν' σ Hagree Hwfσ).
  Qed.
End fresh.

(** * Base steps *)

(** Turn equations between concretizations and concrete constructors into
the shapes of the symbolic objects *)
Local Ltac ac_inv :=
  repeat match goal with
  | H : ?c = ac_expr _ _ |- _ => symmetry in H
  | H : ?c = ac_val _ _ |- _ => symmetry in H
  | H : ?c = ac_lit _ _ |- _ => symmetry in H
  | H : ac_expr _ _ = ?x |- _ => is_var x; subst x
  | H : ac_val _ _ = ?x |- _ => is_var x; subst x
  | H : ac_lit _ _ = ?x |- _ => is_var x; subst x
  | H : ac_expr _ ?e = _ |- _ => is_var e; destruct e; simpl in H; simplify_eq
  | H : ac_val _ ?v = _ |- _ => is_var v; destruct v; simpl in H; simplify_eq
  | H : ac_lit _ ?l = _ |- _ => is_var l; destruct l; simpl in H; simplify_eq
  end.

Definition base_complete_concl ν e σ e2 σ2 efs : Prop :=
  ∃ e' σ' efs' ν', (e', σ', efs') ∈ sbase_step e σ ∧ ssat ν' σ' ∧
    e2 = ac_expr ν' e' ∧ σ2 = ac_state ν' σ' ∧ efs = ac_expr ν' <$> efs' ∧
    ∀ x, (x < snext σ)%nat → ν' x = ν x.

Local Lemma resolve_complete ν e0 t wa σ v σ2 efs :
  base_complete_concl ν e0 σ (Val v) σ2 efs →
  sstate_wf σ → term_wf (snext σ) t →
  ac_proph ν t ∈ used_proph_id (ac_state ν σ) →
  base_complete_concl ν (SResolve e0 (SVal (SLitV (SLitProphecy t))) (SVal wa)) σ (Val v) σ2 efs.
Proof.
  intros (e' & σ' & efs' & ν' & Hin & Hsat & Hv & -> & -> & Hagree) Hwfσ Hwft Hused.
  symmetry in Hv. apply ac_expr_val_inv in Hv as (va & -> & <-).
  rewrite /= elem_of_list_to_set list_elem_of_fmap in Hused.
  destruct Hused as (q & Hq%ac_proph_inj & Hqin).
  destruct Hwfσ as (_ & Hu & _).
  pose proof (proj1 (Forall_forall _ _) Hu q Hqin) as Hwfq.
  exists (SVal va), (sstate_add_atoms [Atom CEq t q] σ'), efs', ν'. split_and!; [| |done..].
  - apply list_elem_of_bind. exists (SVal va, σ', efs'). split; last done.
    apply list_elem_of_fmap. by exists q.
  - apply ssat_add_atoms. split; last done.
    rewrite /atoms_hold Forall_singleton /atom_holds /=.
    by rewrite (term_eval_agree' ν ν' _ Hagree _ Hwft) (term_eval_agree' ν ν' _ Hagree _ Hwfq).
Qed.

Lemma sbase_step_complete ν e σ κ e2 σ2 efs :
  base_step (ac_expr ν e) (ac_state ν σ) κ e2 σ2 efs →
  ssat ν σ → sstate_wf σ → sexpr_wf (snext σ) e →
  base_complete_concl ν e σ e2 σ2 efs.
Proof.
  revert κ e2 σ2 efs. induction e; intros κc ec2 σc2 efsc Hstep Hsat Hwfσ Hwfe;
    cbn [ac_expr] in Hstep; inversion Hstep; subst; clear Hstep; ac_inv;
    simpl in Hwfe; destruct_and?.
  all: lazymatch goal with
  | |- base_complete_concl _ (SUnOp _ _) _ _ _ _ =>
    lazymatch goal with H : un_op_eval _ _ = Some _ |- _ =>
      apply sun_op_eval_complete in H as (va' & Hva' & <-) end;
    exists (SVal va'), σ, [], ν; split_and!;
      [cbn [sbase_step]; rewrite Hva'; by apply list_elem_of_singleton|done..]
  | |- base_complete_concl _ (SBinOp _ _ _) _ _ _ _ =>
    lazymatch goal with H : bin_op_eval _ _ _ = Some _ |- _ =>
      apply sbin_op_eval_complete in H as (va' & cs & Hin & Hcs & <-) end;
    exists (SVal va'), (sstate_add_atoms cs σ), [], ν; split_and!;
      [cbn [sbase_step]; apply list_elem_of_fmap; by exists (va', cs)
      |by apply ssat_add_atoms|done..]
  | |- base_complete_concl _ (SAllocN _ _) _ _ _ _ =>
    lazymatch goal with Hfresh : ∀ _, _ → _ → heap _ !! _ = None |- _ =>
      edestruct (alloc_complete ν σ) as (Hsat' & Hσ' & Hl); [done|done|done|exact Hfresh|] end;
    eexists _, _, [], _; split_and!;
      [cbn [sbase_step]; rewrite decide_True //; apply list_elem_of_singleton; reflexivity
      |exact Hsat'|by rewrite /= Hl|by rewrite Hσ'|done
      |intros; by apply upd_valuation_agree]
  | |- base_complete_concl _ SNewProph _ _ _ _ =>
    lazymatch goal with Hfresh : _ ∉ used_proph_id _ |- _ =>
      edestruct (new_proph_complete ν σ) as (Hsat' & Hσ' & Hp); [done|done|exact Hfresh|] end;
    eexists _, _, [], _; split_and!;
      [cbn [sbase_step]; apply list_elem_of_singleton; reflexivity
      |exact Hsat'|by rewrite /= Hp|by rewrite Hσ'|done
      |intros; by apply upd_valuation_agree]
  | |- base_complete_concl _ (SResolve _ _ _) _ _ _ _ =>
    apply resolve_complete; [by eauto|done|done|done]
  | |- base_complete_concl _ (SFree (SVal (SLitV (SLitLoc ?l)))) _ _ _ _ =>
    lazymatch goal with H : heap _ !! _ = Some (Some _) |- _ =>
      apply sstate_lookup_complete in H as (va & cs & Hin & Hcs & <-) end;
    exists (SVal (SLitV SLitUnit)), (sstate_add_atoms cs (sstate_upd_heap l None σ)), [], ν;
    split_and!;
      [cbn [sbase_step]; apply list_elem_of_fmap; by exists (va, cs)
      |by apply ssat_add_atoms
      |done
      |by rewrite ac_state_add_atoms ac_state_upd_heap|done..]
  | |- base_complete_concl _ (SLoad _) _ _ _ _ =>
    lazymatch goal with H : heap _ !! _ = Some (Some _) |- _ =>
      apply sstate_lookup_complete in H as (va & cs & Hin & Hcs & <-) end;
    exists (SVal va), (sstate_add_atoms cs σ), [], ν; split_and!;
      [cbn [sbase_step]; apply list_elem_of_fmap; by exists (va, cs)
      |by apply ssat_add_atoms|done..]
  | |- base_complete_concl _ (SStore (SVal (SLitV (SLitLoc ?l))) (SVal ?w)) _ _ _ _ =>
    lazymatch goal with H : heap _ !! _ = Some (Some _) |- _ =>
      apply sstate_lookup_complete in H as (va & cs & Hin & Hcs & _) end;
    exists (SVal (SLitV SLitUnit)), (sstate_add_atoms cs (sstate_upd_heap l (Some w) σ)), [], ν;
    split_and!;
      [cbn [sbase_step]; apply list_elem_of_fmap; by exists (va, cs)
      |by apply ssat_add_atoms
      |done
      |by rewrite ac_state_add_atoms ac_state_upd_heap|done..]
  | |- base_complete_concl _ (SXchg (SVal (SLitV (SLitLoc ?l))) (SVal ?w)) _ _ _ _ =>
    lazymatch goal with H : heap _ !! _ = Some (Some _) |- _ =>
      apply sstate_lookup_complete in H as (va & cs & Hin & Hcs & <-) end;
    exists (SVal va), (sstate_add_atoms cs (sstate_upd_heap l (Some w) σ)), [], ν;
    split_and!;
      [cbn [sbase_step]; apply list_elem_of_fmap; by exists (va, cs)
      |by apply ssat_add_atoms
      |done
      |by rewrite ac_state_add_atoms ac_state_upd_heap|done..]
  | |- base_complete_concl _ (SFAA (SVal (SLitV (SLitLoc ?l))) (SVal (SLitV (SLitInt ?i2))))
      _ _ _ _ =>
    lazymatch goal with H : heap _ !! _ = Some (Some _) |- _ =>
      apply sstate_lookup_complete in H as (va & cs & Hin & Hcs & Hva) end;
    ac_inv;
    lazymatch goal with Hin : (SLitV (SLitInt ?i1), _) ∈ sstate_lookup _ _ |- _ =>
      exists (SVal (SLitV (SLitInt i1))),
        (sstate_add_atoms cs (sstate_upd_heap l (Some (SLitV (SLitInt (i1 + i2)))) σ)), [], ν;
      split_and!;
        [cbn [sbase_step]; apply list_elem_of_bind; exists (SLitV (SLitInt i1), cs);
         split; [by apply list_elem_of_singleton|done]
        |by apply ssat_add_atoms
        |done
        |by rewrite ac_state_add_atoms ac_state_upd_heap|done..]
    end
  | |- base_complete_concl _ (SCmpXchg (SVal (SLitV (SLitLoc ?l))) (SVal ?v1) (SVal ?v2))
      _ _ _ _ =>
    lazymatch goal with H : heap _ !! _ = Some (Some _) |- _ =>
      apply sstate_lookup_complete in H as (vold & cs & Hin & Hcs & <-) end;
    lazymatch goal with H : vals_compare_safe _ _ |- _ =>
      apply ac_vals_compare_safe in H as Hsafe end;
    destruct (sval_eq_branches_complete ν vold v1) as (cs' & Hin' & Hcs');
    exists (SVal (SPairV vold (SLitV (SLitBool (bool_decide (ac_val ν vold = ac_val ν v1)))))),
      (sstate_add_atoms (cs' ++ cs)
        (if bool_decide (ac_val ν vold = ac_val ν v1) then sstate_upd_heap l (Some v2) σ else σ)),
      [], ν;
    split_and!;
      [cbn [sbase_step]; apply list_elem_of_bind; exists (vold, cs); split; last done;
       rewrite /= Hsafe; apply list_elem_of_fmap; by eexists (_, cs')
      |apply ssat_add_atoms; split; [by apply atoms_hold_app|by case_match]
      |done
      |rewrite ac_state_add_atoms; case_match; [by rewrite ac_state_upd_heap|done]
      |done..]
  | |- _ =>
    eexists _, σ, _, ν; split_and!;
      [cbn [sbase_step]; apply list_elem_of_singleton; reflexivity
      |done|simpl; rewrite ?ac_subst'; done|done|done|done]
  end.
Qed.


(** * Steps *)
Lemma ac_fill_item_agree ν ν' n Ki e e' :
  (∀ x, (x < n)%nat → ν' x = ν x) → sexpr_wf n (sfill_item Ki e) →
  ac_expr ν' (sfill_item Ki e') = fill_item (ac_item ν Ki) (ac_expr ν' e').
Proof.
  intros Hagree. induction Ki; simpl; intros; destruct_and?; f_equal;
    eauto using ac_expr_agree, ac_val_agree.
  all: f_equal; eauto using ac_val_agree.
Qed.

Lemma ac_fill_agree ν ν' n K e e' :
  (∀ x, (x < n)%nat → ν' x = ν x) →
  sexpr_wf n (@ectx_language.fill sym_heap_ectx_lang K e) →
  sexpr_wf n e ∧
  ac_expr ν' (@ectx_language.fill sym_heap_ectx_lang K e') =
    @ectx_language.fill heap_ectx_lang (ac_item ν <$> K) (ac_expr ν' e').
Proof.
  intros Hagree. induction K as [|Ki K IH] in e, e' |- *; intros Hwf; first done.
  change (@ectx_language.fill sym_heap_ectx_lang (Ki :: K) e) with
    (@ectx_language.fill sym_heap_ectx_lang K (sfill_item Ki e)) in Hwf.
  change (@ectx_language.fill sym_heap_ectx_lang (Ki :: K) e') with
    (@ectx_language.fill sym_heap_ectx_lang K (sfill_item Ki e')).
  destruct (IH _ (sfill_item Ki e') Hwf) as [Hwf' ->].
  split; first by eapply sexpr_wf_fill_item.
  by rewrite (ac_fill_item_agree ν ν' n Ki e e').
Qed.

Theorem sprim_step_complete ν e σ κ e2 σ2 efs :
  ssat ν σ → sstate_wf σ → sexpr_wf (snext σ) e →
  prim_step (ac_expr ν e) (ac_state ν σ) κ e2 σ2 efs →
  ∃ κa e' σ' efs' ν', prim_step e σ κa e' σ' efs' ∧ ssat ν' σ' ∧
    e2 = ac_expr ν' e' ∧ σ2 = ac_state ν' σ' ∧ efs = ac_expr ν' <$> efs' ∧
    ∀ e0, sexpr_wf (snext σ) e0 → ac_expr ν' e0 = ac_expr ν e0.
Proof.
  intros Hsat Hwfσ Hwfe [K e1' e2' Heq -> Hstep].
  apply ac_fill_inv in Heq as (sK & se & -> & <- & <-).
  destruct (ac_fill_agree ν ν (snext σ) sK se se (λ _ _, eq_refl) Hwfe) as [Hwfse _].
  destruct (sbase_step_complete ν se σ _ _ _ _ Hstep Hsat Hwfσ Hwfse)
    as (e' & σ' & efs' & ν' & Hin & Hsat' & -> & -> & -> & Hagree).
  exists [], (@ectx_language.fill sym_heap_ectx_lang sK e'), σ', efs', ν'. split_and!.
  - by apply (ectx_language.Ectx_step' (Λ:=sym_heap_ectx_lang)).
  - done.
  - by destruct (ac_fill_agree ν ν' (snext σ) sK se e' Hagree Hwfe) as [_ ->].
  - done.
  - done.
  - intros e0 Hwf0. by apply (ac_expr_agree ν ν' (snext σ)).
Qed.
