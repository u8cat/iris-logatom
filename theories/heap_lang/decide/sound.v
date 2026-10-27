(* sound.v: symbolic heap_lang steps concretize to heap_lang steps. *)
(* Most of this file is LLM-generated *)
(* Claude Opus 5.5 (1M context) *)

From stdpp Require Import ssreflect list numbers list_numbers gmap.
From iris.program_logic Require Import language.
From iris_logatom.heap_lang.decide Require Export concretize.
From iris.heap_lang Require Import lang.

(** * Concretization of states *)
Section states.
  Context (ν : valuation).

  Lemma ac_loc_add t i : ac_loc ν (term_add t i) = ac_loc ν t +ₗ i.
  Proof.
    rewrite /ac_loc /term_add /term_eval /term_base /Loc.add /=. f_equal. lia.
  Qed.

  Lemma ac_loc_var x i : ac_loc ν (Term (Some x) i) = ac_loc ν (Term (Some x) 0) +ₗ i.
  Proof. rewrite /ac_loc /term_eval /term_base /Loc.add /=. f_equal. lia. Qed.

  Lemma ac_state_add_atoms cs σ : ac_state ν (sstate_add_atoms cs σ) = ac_state ν σ.
  Proof. done. Qed.

  Lemma ssat_add_atoms cs σ : ssat ν (sstate_add_atoms cs σ) ↔ atoms_hold ν cs ∧ ssat ν σ.
  Proof. apply atoms_hold_app. Qed.

  Lemma ac_state_upd_heap l c σ :
    ac_state ν (sstate_upd_heap l c σ) =
    state_upd_heap <[ac_loc ν l := ac_cell ν c]> (ac_state ν σ).
  Proof. done. Qed.

  Lemma ac_heap_lookup_None h l :
    ac_heap ν h !! l = None ↔ ∀ kc, kc ∈ h → ac_loc ν kc.1 ≠ l.
  Proof.
    rewrite /ac_heap -not_elem_of_list_to_map -list_fmap_compose list_elem_of_fmap.
    naive_solver.
  Qed.

  Lemma sheap_lookup_sound l h c cs :
    (c, cs) ∈ sheap_lookup l h → atoms_hold ν cs → ac_heap ν h !! ac_loc ν l = Some (ac_cell ν c).
  Proof.
    revert c cs. induction h as [|[k c'] h IH]; intros c cs; simpl.
    { by intros ?%elem_of_nil. }
    rewrite /ac_heap fmap_cons list_to_map_cons /=.
    intros [[= -> ->]|([c0 cs0] & [= -> ->] & Hin)%list_elem_of_fmap]%elem_of_cons Hcs.
    - rewrite /atoms_hold Forall_singleton /atom_holds /= in Hcs.
      rewrite /ac_loc Hcs lookup_insert_eq //.
    - rewrite /atoms_hold Forall_cons in Hcs. destruct Hcs as [Hne Hcs].
      rewrite /atom_holds /= in Hne.
      rewrite lookup_insert_ne; last by rewrite /ac_loc; intros [= ?].
      by eapply IH.
  Qed.

  Lemma sstate_lookup_sound l σ v cs :
    (v, cs) ∈ sstate_lookup l σ → atoms_hold ν cs →
    heap (ac_state ν σ) !! ac_loc ν l = Some (Some (ac_val ν v)).
  Proof.
    rewrite /sstate_lookup list_elem_of_omap.
    intros ([[v'|] cs'] & Hin & Heq) Hcs; simplify_eq/=.
    by apply (sheap_lookup_sound _ _ (Some v) cs).
  Qed.

  Lemma heap_array_seqZ l n v :
    heap_array l (replicate (Z.to_nat n) v) =
    list_to_map ((λ i, (l +ₗ i, Some v)) <$> seqZ 0 n).
  Proof.
    apply map_eq. intros k. apply option_eq. intros ow.
    rewrite -elem_of_list_to_map; last first.
    { rewrite -list_fmap_compose. apply NoDup_fmap_2; last apply NoDup_seqZ.
      intros i j [= Hij]. lia. }
    rewrite heap_array_lookup list_elem_of_fmap. split.
    - intros (j & w & Hj & -> & -> & (-> & Hlt)%lookup_replicate).
      exists j. split; [done|]. apply elem_of_seqZ. lia.
    - intros (i & [= -> ->] & Hi%elem_of_seqZ). exists i, v.
      split_and!; [lia|done|done|]. apply lookup_replicate. split; [done|lia].
  Qed.

  Lemma ac_state_alloc n v σ :
    ac_state ν (sstate_alloc n v σ) =
    state_init_heap (ac_loc ν (Term (Some (snext σ)) 0)) n (ac_val ν v) (ac_state ν σ).
  Proof.
    rewrite /ac_state /state_init_heap /ac_heap /= fmap_app list_to_map_app.
    f_equal. rewrite heap_array_seqZ -list_fmap_compose. f_equal. f_equal.
    apply list_fmap_ext. intros i z _. by rewrite /= -ac_loc_var.
  Qed.

  Lemma ssat_alloc_fresh n v σ :
    ssat ν (sstate_alloc n v σ) →
    ∀ i, (0 ≤ i)%Z → (i < n)%Z →
      heap (ac_state ν σ) !! (ac_loc ν (Term (Some (snext σ)) 0) +ₗ i) = None.
  Proof.
    intros Hsat i Hi0 Hin. apply atoms_hold_app in Hsat as [Hfresh _].
    apply ac_heap_lookup_None. intros kc Hkc Heq.
    rewrite /atoms_hold Forall_forall in Hfresh.
    assert (atom_holds ν (Atom CNe (Term (Some (snext σ)) i) kc.1)) as Hne.
    { apply Hfresh, list_elem_of_bind. exists i. split.
      - apply list_elem_of_fmap. by exists kc.
      - apply elem_of_seqZ. lia. }
    apply Hne. rewrite -ac_loc_var /ac_loc in Heq. by injection Heq.
  Qed.

  Lemma ac_state_new_proph σ :
    ac_state ν (sstate_new_proph σ) =
    state_upd_used_proph_id ({[ac_proph ν (Term (Some (snext σ)) 0)]} ∪.) (ac_state ν σ).
  Proof. done. Qed.

  Lemma ac_proph_inj t1 t2 : ac_proph ν t1 = ac_proph ν t2 → term_eval ν t1 = term_eval ν t2.
  Proof.
    rewrite /ac_proph. intros Heq. apply (f_equal Z_of_proph) in Heq.
    by rewrite !Z_of_proph_of_Z in Heq.
  Qed.

  Lemma ssat_new_proph_fresh σ :
    ssat ν (sstate_new_proph σ) →
    ac_proph ν (Term (Some (snext σ)) 0) ∉ used_proph_id (ac_state ν σ).
  Proof.
    intros Hsat. apply atoms_hold_app in Hsat as [Hfresh _].
    rewrite /= elem_of_list_to_set list_elem_of_fmap. intros (p & Heq%ac_proph_inj & Hp).
    rewrite /atoms_hold Forall_fmap Forall_forall in Hfresh.
    by apply (Hfresh p).
  Qed.
End states.

(** * Operators *)
Local Ltac nil_in H := simpl in H; by apply elem_of_nil in H.

Section operators.
  Context (ν : valuation).

  Lemma sun_op_eval_sound op v v' :
    sun_op_eval op v = Some v' → un_op_eval op (ac_val ν v) = Some (ac_val ν v').
  Proof.
    destruct op, v as [l| | | |]; try done; destruct l; simpl; by intros [= <-].
  Qed.

  Lemma slit_of_int_bool_ac l l' : slit_of_int_bool l = Some l' → ac_lit ν l' = l.
  Proof. destruct l; simpl; by intros [= <-]. Qed.

  Local Lemma int_bool_sound (o : option base_lit) l :
    o ≫= slit_of_int_bool = Some l → LitV <$> o = Some (LitV (ac_lit ν l)).
  Proof. destruct o as [bl|]; simpl; [intros Hl; by rewrite (slit_of_int_bool_ac bl l Hl)|done]. Qed.

  Lemma sbin_op_eval_sound op v1 v2 v cs :
    (v, cs) ∈ sbin_op_eval op v1 v2 → atoms_hold ν cs →
    bin_op_eval op (ac_val ν v1) (ac_val ν v2) = Some (ac_val ν v).
  Proof.
    rewrite /sbin_op_eval /bin_op_eval. intros Hin Hcs. case_decide; subst.
    - destruct (svals_compare_safe v1 v2) eqn:Hsafe; last by apply elem_of_nil in Hin.
      rewrite decide_True; last by apply ac_vals_compare_safe.
      apply list_elem_of_fmap in Hin as ([b cs'] & [= -> ->] & Hin).
      by rewrite /= (sval_eq_branches_sound ν v1 v2 b cs').
    - destruct v1 as [l1| | | |]; try nil_in Hin.
      destruct l1; try nil_in Hin.
      all: destruct v2 as [l2| | | |]; try nil_in Hin.
      all: destruct l2; try nil_in Hin.
      (* integers and booleans *)
      all: simpl in Hin |- *.
      all: try (case_match eqn:Hl; [|by apply elem_of_nil in Hin];
        apply list_elem_of_singleton in Hin; injection Hin as -> ->;
        by apply int_bool_sound).
      (* locations *)
      all: apply list_elem_of_fmap in Hin as ([lr cs'] & [= -> ->] & Hin).
      all: destruct op; simpl in Hin; try by apply elem_of_nil in Hin.
      all: repeat (apply elem_of_cons in Hin as [Hin|Hin]); try by apply elem_of_nil in Hin.
      all: injection Hin as -> ->; simpl; rewrite ?ac_loc_add //.
      all: rewrite /atoms_hold Forall_singleton /atom_holds /= in Hcs.
      all: repeat f_equal; rewrite /Loc.le /Loc.lt /ac_loc /=;
        first [apply bool_decide_eq_true_2|apply bool_decide_eq_false_2]; lia.
  Qed.
End operators.

(** * Base steps *)
Section base.
  Context (ν : valuation).

  Local Lemma resolve_sound e0 σ p w v σ0 efs0 q :
    (∃ κ, base_step (ac_expr ν e0) (ac_state ν σ) κ (ac_expr ν (SVal v)) (ac_state ν σ0)
      (ac_expr ν <$> efs0)) →
    q ∈ sused σ → atoms_hold ν [Atom CEq p q] →
    ∃ κ, base_step (ac_expr ν (SResolve e0 (SVal (SLitV (SLitProphecy p))) (SVal w)))
      (ac_state ν σ) κ (ac_expr ν (SVal v)) (ac_state ν σ0) (ac_expr ν <$> efs0).
  Proof.
    intros [κ Hstep] Hq Hpq. rewrite /atoms_hold Forall_singleton /atom_holds /= in Hpq.
    eexists. apply ResolveS; first exact Hstep.
    rewrite /= elem_of_list_to_set list_elem_of_fmap.
    exists q. split; [by rewrite /ac_proph Hpq|done].
  Qed.

  Lemma sbase_step_sound e σ e' σ' efs :
    (e', σ', efs) ∈ sbase_step e σ → ssat ν σ' →
    ∃ κ, base_step (ac_expr ν e) (ac_state ν σ) κ (ac_expr ν e') (ac_state ν σ')
      (ac_expr ν <$> efs).
  Proof.
    revert e' σ' efs. induction e; intros e' σ' efs Hin Hsat;
      cbn [sbase_step] in Hin; repeat case_match; subst;
      try by apply elem_of_nil in Hin.
    all: lazymatch goal with
    | |- ∃ _, base_step (ac_expr _ (SBinOp _ _ _)) _ _ _ _ _ =>
      apply list_elem_of_fmap in Hin as ([vres cres] & [= -> -> ->] & Hvcs);
      apply ssat_add_atoms in Hsat as [Hcs Hsat];
      exists []; apply BinOpS; by eapply sbin_op_eval_sound
    | |- ∃ _, base_step (ac_expr _ (SUnOp _ _)) _ _ _ _ _ =>
      apply list_elem_of_singleton in Hin; injection Hin as -> -> ->;
      exists []; by apply UnOpS, sun_op_eval_sound
    | |- ∃ _, base_step (ac_expr _ (SApp _ _)) _ _ _ _ _ =>
      apply list_elem_of_singleton in Hin; injection Hin as -> -> ->;
      exists []; apply BetaS; by rewrite !ac_subst'
    | |- ∃ _, base_step (ac_expr _ (SAllocN _ _)) _ _ _ _ _ =>
      apply list_elem_of_singleton in Hin; injection Hin as -> -> ->;
      exists []; rewrite ac_state_alloc; apply AllocNS; first done;
      by eapply ssat_alloc_fresh
    | |- ∃ _, base_step (ac_expr _ SNewProph) _ _ _ _ _ =>
      apply list_elem_of_singleton in Hin; injection Hin as -> -> ->;
      exists []; rewrite ac_state_new_proph; apply NewProphS;
      by eapply ssat_new_proph_fresh
    | |- ∃ _, base_step (ac_expr _ (SFree _)) _ _ _ _ _ =>
      apply list_elem_of_fmap in Hin as ([vres cres] & [= -> -> ->] & Hvcs);
      apply ssat_add_atoms in Hsat as [Hcs Hsat];
      exists []; rewrite ac_state_add_atoms ac_state_upd_heap; eapply FreeS;
      by eapply sstate_lookup_sound
    | |- ∃ _, base_step (ac_expr _ (SLoad _)) _ _ _ _ _ =>
      apply list_elem_of_fmap in Hin as ([vres cres] & [= -> -> ->] & Hvcs);
      apply ssat_add_atoms in Hsat as [Hcs Hsat];
      exists []; apply LoadS; by eapply sstate_lookup_sound
    | |- ∃ _, base_step (ac_expr _ (SStore _ _)) _ _ _ _ _ =>
      apply list_elem_of_fmap in Hin as ([vres cres] & [= -> -> ->] & Hvcs);
      apply ssat_add_atoms in Hsat as [Hcs Hsat];
      exists []; rewrite ac_state_add_atoms ac_state_upd_heap; eapply StoreS;
      by eapply sstate_lookup_sound
    | |- ∃ _, base_step (ac_expr _ (SXchg _ _)) _ _ _ _ _ =>
      apply list_elem_of_fmap in Hin as ([vres cres] & [= -> -> ->] & Hvcs);
      apply ssat_add_atoms in Hsat as [Hcs Hsat];
      exists []; rewrite ac_state_add_atoms ac_state_upd_heap; apply XchgS;
      by eapply sstate_lookup_sound
    | |- ∃ _, base_step (ac_expr _ (SCmpXchg _ _ _)) _ _ _ _ _ =>
      apply list_elem_of_bind in Hin as ([vold cold] & Hin & Hvcs);
      simpl in Hin; case_match eqn:Hsafe; last (by apply elem_of_nil in Hin);
      apply list_elem_of_fmap in Hin as ([bres cres] & [= -> -> ->] & Hbcs);
      apply ssat_add_atoms in Hsat as [Hcs' Hsat]; apply atoms_hold_app in Hcs';
      exists []; rewrite ac_state_add_atoms;
      destruct bres; [rewrite ac_state_upd_heap|];
      (eapply CmpXchgS;
        [ by eapply sstate_lookup_sound, proj2
        | by apply ac_vals_compare_safe
        | symmetry; by eapply sval_eq_branches_sound, proj1 ])
    | |- ∃ _, base_step (ac_expr _ (SFAA _ _)) _ _ _ _ _ =>
      apply list_elem_of_bind in Hin as ([vold cold] & Hin & Hvcs);
      destruct vold as [[]| | | |]; simpl in Hin; try (by apply elem_of_nil in Hin);
      apply list_elem_of_singleton in Hin; injection Hin as -> -> ->;
      apply ssat_add_atoms in Hsat as [Hcs Hsat];
      exists []; rewrite ac_state_add_atoms ac_state_upd_heap; apply FaaS;
      by eapply (sstate_lookup_sound _ _ _ (SLitV (SLitInt _)))
    | |- ∃ _, base_step (ac_expr _ (SResolve _ _ _)) _ _ _ _ _ =>
      apply list_elem_of_bind in Hin as ([[e0res σ0res] efs0res] & Hin & Hin0);
      destruct e0res; simpl in Hin; try (by apply elem_of_nil in Hin);
      apply list_elem_of_fmap in Hin as (qres & [= -> -> ->] & Hq);
      apply ssat_add_atoms in Hsat as [Hpq Hsat];
      rewrite ac_state_add_atoms; eapply resolve_sound; [by eauto|exact Hq|exact Hpq]
    | |- _ =>
      apply list_elem_of_singleton in Hin; injection Hin as -> -> ->;
      exists []; simpl; econstructor
    end.
  Qed.

  (** Base steps only add to the path condition *)
  Lemma sbase_step_scons e σ e' σ' efs :
    (e', σ', efs) ∈ sbase_step e σ → scons σ `suffix_of` scons σ'.
  Proof.
    revert e' σ' efs. induction e; intros e' σ' efs Hin;
      cbn [sbase_step] in Hin; repeat case_match; subst;
      try (by apply elem_of_nil in Hin).
    all: repeat match goal with
      | H : _ ∈ [] |- _ => by apply elem_of_nil in H
      | H : _ ∈ [_] |- _ => apply list_elem_of_singleton in H; injection H as -> -> ->
      | H : (_, _, _) ∈ _ <$> _ |- _ =>
        apply list_elem_of_fmap in H as (? & [= -> -> ->] & ?)
      | H : (_, _, _) ∈ _ ≫= _ |- _ => apply list_elem_of_bind in H as (? & H & ?); simpl in H
      | H : (_, _, _) ∈ match ?x with _ => _ end |- _ => destruct x
      | H : (_, _, _) ∈ (if ?b then _ else _) |- _ => destruct b
      end.
    all: simpl; repeat (apply suffix_app_r || apply suffix_cons_r); try done.
    (* [CmpXchg]: whether the heap is updated *)
    all: try (case_match; simpl; done).
    (* [Resolve]: the path condition of the inner step *)
    all: by eauto.
  Qed.
End base.

(** * Steps *)
Lemma ac_fill ν K e :
  ac_expr ν (@ectx_language.fill sym_heap_ectx_lang K e) =
  @ectx_language.fill heap_ectx_lang (ac_item ν <$> K) (ac_expr ν e).
Proof.
  induction K as [|Ki K IH] in e |- *; first done.
  change (@ectx_language.fill sym_heap_ectx_lang (Ki :: K) e) with
    (@ectx_language.fill sym_heap_ectx_lang K (sfill_item Ki e)).
  by rewrite IH ac_fill_item.
Qed.

Theorem sprim_step_sound ν e σ κ e' σ' efs :
  prim_step e σ κ e' σ' efs → ssat ν σ' →
  ∃ κc, prim_step (ac_expr ν e) (ac_state ν σ) κc (ac_expr ν e') (ac_state ν σ')
    (ac_expr ν <$> efs).
Proof.
  intros [K e1 e2 -> -> [_ Hbase]] Hsat.
  destruct (sbase_step_sound ν _ _ _ _ _ Hbase Hsat) as [κc Hstep].
  exists κc. rewrite !ac_fill. by apply (ectx_language.Ectx_step' (Λ:=heap_ectx_lang)).
Qed.

Theorem sprim_step_sat ν e σ κ e' σ' efs :
  prim_step e σ κ e' σ' efs → ssat ν σ' → ssat ν σ.
Proof.
  intros [K e1 e2 -> -> [_ Hbase]].
  apply sbase_step_scons in Hbase as [k Hk]. rewrite /ssat Hk atoms_hold_app. naive_solver.
Qed.
