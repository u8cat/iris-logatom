(* lemmas.v — Pure support lemmas for the HW queue metaconfig proof. *)

From Stdlib.Logic Require Import FunctionalExtensionality PropExtensionality.

From stdpp Require Import base list gmap propset.
From Stdlib Require Import Sorting.Sorted Lia.
From iris_logatom.pure_logic Require Import linear.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.metaconfig Require Import tracking.
From iris.heap_lang Require Import notation.

From case_studies.hw_queue.metaconfig Require Import defs.
Import HWQMetaConfigNotation.

(** [propset] uses [≡] for extensional equality. We upgrade to Leibniz equality
    using functional and propositional extensionality. Previously
    [propset_leibniz_equiv] was in the meta theory; re-added locally for the
    HW queue metaconfig proof. NOTE: we use functional and propositional
    extensionality axioms here. *)
Local Instance propset_signle_config_q_leibniz_equiv : LeibnizEquiv (propset single_config_q).
Proof.
  intros [X_car] [Y_car] H.
  f_equal.
  apply functional_extensionality. intros x.
  apply propositional_extensionality.
  apply (H x).
Qed.

(* ====================================================================== *)
(* Filter on ts when τ does not appear in ts. *)

Lemma filter_τ_fresh_nil (ts : list (positive*trace)) (τ : positive) :
  τ ∉ ts.*1 →
  filter (λ t, t.1 = τ) ts = [].
Proof.
  intros Hfresh.
  induction ts as [|[τ' ev] ts' IH]; first done.
  rewrite filter_cons. case_decide as Heq.
  + exfalso. simpl in Heq. subst τ'.
    apply Hfresh. set_solver.
  + apply IH. intros Hin. apply Hfresh. set_solver.
Qed.

(* ====================================================================== *)
(* per_tag_wellformed snoc preservation. *)

Lemma per_tag_wellformed_snoc_call_push ts τ v :
  τ ∉ ts.*1 →
  per_tag_wellformed ts →
  per_tag_wellformed (ts ++ [(τ, Call Push v)]).
Proof.
  intros Hfresh Hwf τ'.
  destruct (decide (τ' = τ)) as [-> | Hne].
  - exists Push, v, #().
    rewrite filter_app filter_cons_True // filter_nil /=.
    rewrite (filter_τ_fresh_nil _ _ Hfresh) /=.
    apply prefix_cons. apply prefix_nil.
  - destruct (Hwf τ') as (n_a & v_a & v_b & Hpref).
    exists n_a, v_a, v_b. rewrite filter_app filter_cons_False //=.
    by rewrite filter_nil app_nil_r.
Qed.

Lemma per_tag_wellformed_snoc_call_pop ts τ :
  τ ∉ ts.*1 →
  per_tag_wellformed ts →
  per_tag_wellformed (ts ++ [(τ, Call Pop #())]).
Proof.
  intros Hfresh Hwf τ'.
  destruct (decide (τ' = τ)) as [-> | Hne].
  - exists Pop, #(), #().
    rewrite filter_app filter_cons_True // filter_nil /=.
    rewrite (filter_τ_fresh_nil _ _ Hfresh) /=.
    apply prefix_cons. apply prefix_nil.
  - destruct (Hwf τ') as (n_a & v_a & v_b & Hpref).
    exists n_a, v_a, v_b. rewrite filter_app filter_cons_False //=.
    by rewrite filter_nil app_nil_r.
Qed.

Lemma per_tag_wellformed_snoc_ret ts τ n_call v_call v_ret :
  per_tag_wellformed ts →
  filter (λ t, t.1 = τ) ts = [(τ, Call n_call v_call)] →
  per_tag_wellformed (ts ++ [(τ, Ret v_ret)]).
Proof.
  intros Hwf Hfilter τ'.
  destruct (decide (τ' = τ)) as [-> | Hne].
  - exists n_call, v_call, v_ret.
    rewrite filter_app filter_cons_True // filter_nil /=.
    rewrite Hfilter.
    exists []. by rewrite app_nil_r.
  - destruct (Hwf τ') as (n_a & v_a & v_b & Hpref).
    exists n_a, v_a, v_b. rewrite filter_app filter_cons_False //=.
    by rewrite filter_nil app_nil_r.
Qed.

(* ====================================================================== *)
(* gset/propset singleton bridge. *)

Lemma set_to_propset_singleton (x : single_config_q) :
  set_to_propset ({[ x ]} : gset single_config_q) = ({[ x ]} : propset single_config_q).
Proof.
  apply leibniz_equiv. intros y. rewrite elem_of_set_to_propset !elem_of_singleton //.
Qed.

(* ====================================================================== *)
(* Bridges between [set_to_propset] of a gset operation and the
   corresponding propset operation. These let us rewrite the output of
   [mcfg_step_call/interm/ret] (which produce propsets) into
   [set_to_propset M_g_new] form so we can chain mcfg_steps under the
   `mcfg_steps mcfg_init (set_to_propset M_g) ts` invariant.

   We use Leibniz equality (via propset_leibniz_equiv axiom) so the
   resulting form can be substituted directly into mcfg_steps without
   requiring Proper instances. *)

Lemma gset_to_propset_set_map_call
    (M_g : gset single_config_q) (τ : positive) (n : nat) (v : val) :
  ((λ '(s, π), (s, <[τ:=(n, v, None)]> π))
     <$> (set_to_propset M_g : @meta_config hwq_model))
  = set_to_propset (set_map (λ x : single_config_q,
                              (x.1, <[τ:=(n, v, None)]> x.2)) M_g
                    : gset single_config_q).
Proof.
  apply leibniz_equiv. intros [s π].
  rewrite elem_of_set_to_propset elem_of_map.
  split.
  - intros Hin.
    apply elem_of_PropSet in Hin as ([s' π'] & Heq & Hin').
    apply elem_of_set_to_propset in Hin'.
    exists (s', π'). split; [exact Heq | exact Hin'].
  - intros ([s' π'] & Heq & Hin').
    apply elem_of_PropSet. exists (s', π'). split; first exact Heq.
    apply elem_of_set_to_propset. exact Hin'.
Qed.

Lemma gset_to_propset_union_singleton
    (M_g : gset single_config_q) (x : single_config_q) :
  ({[ x ]} ∪ set_to_propset M_g : @meta_config hwq_model)
  = set_to_propset ({[ x ]} ∪ M_g : gset single_config_q).
Proof.
  apply leibniz_equiv. intros y.
  rewrite elem_of_set_to_propset.
  split.
  - intros Hin.
    apply elem_of_union in Hin as [Hin_sing|Hin_g].
    + apply elem_of_singleton in Hin_sing. subst y. set_solver.
    + rewrite elem_of_set_to_propset in Hin_g. set_solver.
  - intros Hin.
    apply elem_of_union in Hin as [Hin_sing|Hin_g].
    + apply elem_of_singleton in Hin_sing. subst y.
      apply elem_of_union. left. apply elem_of_singleton. reflexivity.
    + apply elem_of_union. right.
      rewrite elem_of_set_to_propset. exact Hin_g.
Qed.

Lemma gset_to_propset_filter_ret
    (M_g : gset single_config_q) (τ : positive) (v' : val) :
  (set_to_propset M_g
     ∩ {[ (_, π) | snd <$> (π !! τ) = Some (Some v') ]}
   : @meta_config hwq_model)
  = set_to_propset (filter (λ x : single_config_q,
       snd <$> (x.2 !! τ) = Some (Some v')) M_g
       : gset single_config_q).
Proof.
  apply leibniz_equiv. intros [s π].
  rewrite elem_of_set_to_propset.
  split.
  - intros [Hin_g Hin_filter]%elem_of_intersection.
    rewrite elem_of_set_to_propset in Hin_g.
    apply elem_of_PropSet in Hin_filter. simpl in Hin_filter.
    apply elem_of_filter. split; [exact Hin_filter | exact Hin_g].
  - intros Hin.
    apply elem_of_filter in Hin as [Hπ Hin_g].
    apply elem_of_intersection. split.
    + rewrite elem_of_set_to_propset. exact Hin_g.
    + apply elem_of_PropSet. exact Hπ.
Qed.

(* ====================================================================== *)
(* Domain of any config in any reachable meta-config is bounded by the
   tags appearing in the trace.  This is the key invariant linking
   trace freshness to the [set_Forall (τ ∉ dom π)] precondition of
   [mcfg_step_call]. *)

Lemma mcfg_step_dom_in_trace_aux
    (M_pre M_post : @meta_config hwq_model)
    (ts_pre ts_step : list (positive*trace))
    (s : @S hwq_model) (π : gmap positive proc_status) :
  mcfg_step M_pre M_post ts_step →
  (s, π) ∈ M_post →
  (* IH: every config in M_pre had its domain in ts_pre.*1 *)
  (∀ s' π', (s', π') ∈ M_pre → dom π' ⊆ list_to_set ts_pre.*1) →
  dom π ⊆ list_to_set (ts_pre ++ ts_step).*1.
Proof.
  intros Hstep Hin Hpre.
  inversion Hstep as
    [M τ n v Hf Hvr
    | M s_pre π_pre τ n v s_post v' Hsπ Hπτ Hrr
    | M τ v'];
    subst.
  - (* mcfg_step_call *)
    apply elem_of_PropSet in Hin as ([s' π'] & Heq & Hin_pre).
    simpl in Heq. injection Heq as -> ->.
    rewrite dom_insert_L.
    rewrite fmap_app list_to_set_app_L. simpl.
    pose proof (Hpre _ _ Hin_pre).
    set_solver.
  - (* mcfg_step_interm: trace contribution is [] *)
    rewrite app_nil_r.
    apply elem_of_union in Hin as [Hin | Hin].
    + apply elem_of_singleton in Hin. injection Hin as -> ->.
      rewrite dom_insert_L.
      pose proof (Hpre _ _ Hsπ).
      apply elem_of_dom_2 in Hπτ.
      set_solver.
    + by eapply Hpre.
  - (* mcfg_step_ret *)
    apply elem_of_intersection in Hin as [Hin _].
    pose proof (Hpre _ _ Hin).
    rewrite fmap_app list_to_set_app_L. simpl.
    set_solver.
Qed.

Lemma mcfg_steps_dom_in_trace_strong
    (M_pre M_full : @meta_config hwq_model)
    (ts_pre ts_step : list (positive*trace)) :
  (∀ s' π', (s', π') ∈ M_pre → dom π' ⊆ list_to_set ts_pre.*1) →
  mcfg_steps M_pre M_full ts_step →
  ∀ s π, (s, π) ∈ M_full → dom π ⊆ list_to_set (ts_pre ++ ts_step).*1.
Proof.
  intros Hpre Hsteps. revert ts_pre Hpre.
  induction Hsteps as [M | M0 M1 ts1 M2 ts2 Hstep Hsteps IH];
    intros ts_pre Hpre s π Hin.
  - rewrite app_nil_r. by eapply Hpre.
  - rewrite app_assoc.
    eapply (IH (ts_pre ++ ts1)).
    + intros s' π' Hin_pre.
      by eapply mcfg_step_dom_in_trace_aux.
    + exact Hin.
Qed.

Lemma mcfg_steps_dom_in_trace
    (M_full : @meta_config hwq_model)
    (ts : list (positive*trace))
    (s : @S hwq_model) (π : gmap positive proc_status) :
  mcfg_steps mcfg_init M_full ts →
  (s, π) ∈ M_full →
  dom π ⊆ list_to_set ts.*1.
Proof.
  intros Hsteps Hin.
  assert (Hinit_dom : ∀ s' π',
    (s', π') ∈ (mcfg_init : @meta_config hwq_model) →
    dom π' ⊆ list_to_set ([] : list (positive*trace)).*1).
  { intros s' π' Hin_init.
    change ((s', π') ∈ ({[ (s_init, ∅) ]} : @meta_config hwq_model)) in Hin_init.
    apply elem_of_singleton in Hin_init.
    injection Hin_init as -> ->. rewrite dom_empty_L. set_solver. }
  pose proof (mcfg_steps_dom_in_trace_strong mcfg_init M_full [] ts
                Hinit_dom Hsteps s π Hin) as H.
  rewrite app_nil_l in H. exact H.
Qed.

(* ====================================================================== *)
(* Request uniqueness: for any reachable mcfg, if τ appears in any config's
   dom, then π[τ].1 (the request value) equals the value set at τ's unique
   Call event. *)

(* Step-level invariant: if request value is unique across M_pre, it remains
   unique across M_post for τ not introduced in this step. *)
Lemma mcfg_step_request_value_preserved
    (M_pre M_post : @meta_config hwq_model)
    (ts_step : list (positive*trace))
    (τ : positive) (v : nat * val) :
  mcfg_step M_pre M_post ts_step →
  (* In M_pre, all configs with τ ∈ dom have π[τ].1 = v *)
  (∀ s π v_x v_resp, (s, π) ∈ M_pre → π !! τ = Some (v_x, v_resp) → v_x = v) →
  (* The step's trace contribution doesn't introduce a Call τ with different v *)
  (∀ τ' n' v', (τ', Call n' v') ∈ ts_step → τ' = τ → (n', v') = v) →
  ∀ s π v_x v_resp, (s, π) ∈ M_post → π !! τ = Some (v_x, v_resp) → v_x = v.
Proof.
  intros Hstep Hpre Hcall s π v_x v_resp Hin Hπτ.
  inversion Hstep as
    [M τ_s n_s v_s Hf Hvr
    | M s_a π_a τ_s n_s v_s s_b v' Hsa Hπaτ Hrr
    | M τ_s v'_s];
    subst.
  - (* mcfg_step_call: M_post = (λ '(s, π), (s, <[τ_s:=(n_s, v_s, None)]> π)) <$> M_pre *)
    apply elem_of_PropSet in Hin as ([s' π'] & Heq & Hin_pre).
    simpl in Heq. injection Heq as -> ->.
    destruct (decide (τ_s = τ)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hπτ.
      injection Hπτ as Hv_eq _.
      subst v_x.
      apply (Hcall τ n_s v_s); [|reflexivity].
      apply list_elem_of_singleton. reflexivity.
    + rewrite lookup_insert_ne in Hπτ; last (intros ?; apply Hne; congruence).
      apply (Hpre s' π' v_x v_resp Hin_pre Hπτ).
  - (* mcfg_step_interm: M_post = {[ (s_b, <[τ_s:=(n_s, v_s, Some v')]>π_a) ]} ∪ M_pre *)
    apply elem_of_union in Hin as [Hin_new | Hin_old].
    + apply elem_of_singleton in Hin_new. injection Hin_new as -> ->.
      destruct (decide (τ_s = τ)) as [-> | Hne].
      * rewrite lookup_insert_eq in Hπτ.
        injection Hπτ as Hv_eq _.
        subst v_x.
        (* From Hπaτ: π_a !! τ = Some (n_s, v_s, None). Apply Hpre to extract (n_s, v_s) = v. *)
        apply (Hpre s_a π_a (n_s, v_s) None Hsa Hπaτ).
      * rewrite lookup_insert_ne in Hπτ; last (intros ?; apply Hne; congruence).
        apply (Hpre s_a π_a v_x v_resp Hsa Hπτ).
    + apply (Hpre s π v_x v_resp Hin_old Hπτ).
  - (* mcfg_step_ret: M_post = M_pre ∩ filter *)
    apply elem_of_intersection in Hin as [Hin_pre _].
    apply (Hpre s π v_x v_resp Hin_pre Hπτ).
Qed.

(* Multi-step: request uniqueness preserved through any sequence of steps
   whose Call events for τ all use the value v. *)
Lemma mcfg_steps_request_value_preserved
    (M_pre M_post : @meta_config hwq_model)
    (ts_step : list (positive*trace))
    (τ : positive) (v : nat * val) :
  mcfg_steps M_pre M_post ts_step →
  (∀ s π v_x v_resp, (s, π) ∈ M_pre → π !! τ = Some (v_x, v_resp) → v_x = v) →
  (∀ τ' n' v', (τ', Call n' v') ∈ ts_step → τ' = τ → (n', v') = v) →
  ∀ s π v_x v_resp, (s, π) ∈ M_post → π !! τ = Some (v_x, v_resp) → v_x = v.
Proof.
  intros Hsteps. revert τ v.
  induction Hsteps as [M | M0 M1 ts1 M2 ts2 Hstep Hsteps IH]; intros τ v Hpre Hcall.
  - exact Hpre.
  - apply (IH τ v).
    + intros s' π' v_x' v_resp' Hin' Hπτ'.
      eapply mcfg_step_request_value_preserved; first exact Hstep.
      * exact Hpre.
      * intros τ' n' v' Hin_ts Heq. apply (Hcall τ' n' v'); last exact Heq.
        apply elem_of_app. left. exact Hin_ts.
      * exact Hin'.
      * exact Hπτ'.
    + intros τ' n' v' Hin_ts Heq. apply (Hcall τ' n' v'); last exact Heq.
      apply elem_of_app. right. exact Hin_ts.
Qed.

(* Reachability instance: if the trace has exactly one Call event for τ
   (which is the typical case for tracked operations), then all configs in
   the reachable mcfg with π[τ] defined have π[τ].1 = the Call's value. *)
Lemma mcfg_steps_request_value_from_filter
    (M_full : @meta_config hwq_model)
    (ts : list (positive*trace))
    (τ : positive) (v : nat * val) :
  mcfg_steps mcfg_init M_full ts →
  (* The trace's τ-filter has Call v as the first event (typical for tracked ops). *)
  (∀ τ' n' v', (τ', Call n' v') ∈ ts → τ' = τ → (n', v') = v) →
  ∀ s π v_x v_resp, (s, π) ∈ M_full → π !! τ = Some (v_x, v_resp) → v_x = v.
Proof.
  intros Hsteps Hcall.
  eapply mcfg_steps_request_value_preserved; first exact Hsteps; last exact Hcall.
  intros s π v_x v_resp Hin Hπτ.
  change ((s, π) ∈ ({[ (s_init, ∅) ]} : @meta_config hwq_model)) in Hin.
  apply elem_of_singleton in Hin. injection Hin as -> ->.
  rewrite lookup_empty in Hπτ. discriminate.
Qed.

(* From a trace where filter τ ts contains only (τ, Call v) as the Call event,
   derive request value uniqueness. *)
Lemma mcfg_steps_request_value_from_filter_eq
    (M_full : @meta_config hwq_model)
    (ts : list (positive*trace))
    (τ : positive) (v : nat * val) :
  mcfg_steps mcfg_init M_full ts →
  (* filter τ ts has only (τ, Call v) as its sole Call event, possibly with Ret/Lin too *)
  (* Stronger form: all Call events in ts for τ use value v *)
  (∀ τ' n' v', (τ', Call n' v') ∈ ts → τ' = τ → (n', v') = v) →
  set_Forall (λ '(_, π), ∀ v_x v_resp, π !! τ = Some (v_x, v_resp) → v_x = v) M_full.
Proof.
  intros Hsteps Hcall [s π] Hin v_x v_resp Hπτ.
  eapply mcfg_steps_request_value_from_filter; eauto.
Qed.

(* ====================================================================== *)
(* Chain LP τ in each τ-pending config of a finite gset M_g (within M_full).
   This is the key "rebuild" step from POPL'24's E1 transition: after FAA,
   the meta-config is augmented with linearizations of all currently-pending
   pushes. We use this to maintain the push_universal_witness invariant
   across Ret transitions. *)

(* Map a config to its τ-LP'd version if τ is pending in it, else identity. *)
Definition lp_or_keep_τ_push (τ : positive) (v : val)
                              (x : single_config_q) : single_config_q :=
  if decide (x.2 !! τ = Some (Push, v, None)) then
    (x.1 ++ [v], <[τ:=(Push, v, Some #())]>x.2)
  else x.

Lemma lp_or_keep_τ_push_τ_lin (τ : positive) (v : val) (x : single_config_q)
    (Hdisj : x.2 !! τ = Some (Push, v, None) ∨
             x.2 !! τ = Some (Push, v, Some #())) :
  (lp_or_keep_τ_push τ v x).2 !! τ = Some (Push, v, Some #()).
Proof.
  unfold lp_or_keep_τ_push. case_decide as Hxτ.
  - destruct x as [s π]. simpl. apply lookup_insert_eq.
  - destruct Hdisj as [Hl | Hr]; first contradiction. exact Hr.
Qed.

Lemma lp_or_keep_τ_push_τ'_preserve (τ τ' : positive) (v : val) (x : single_config_q)
    (Hne : τ' ≠ τ) :
  (lp_or_keep_τ_push τ v x).2 !! τ' = x.2 !! τ'.
Proof.
  unfold lp_or_keep_τ_push. case_decide as Hxτ.
  - destruct x as [s π]. simpl.
    rewrite lookup_insert_ne; first reflexivity.
    intros Heq. apply Hne. congruence.
  - reflexivity.
Qed.

Lemma lp_or_keep_τ_push_head_preserve (τ : positive) (v : val)
    (s' : list val) (π : gmap positive proc_status) (v_head : val) :
  ∃ s'_new,
    (lp_or_keep_τ_push τ v (v_head :: s', π)).1 = v_head :: s'_new.
Proof.
  unfold lp_or_keep_τ_push. case_decide.
  - simpl. eexists. reflexivity.
  - simpl. eexists. reflexivity.
Qed.

(* Build list of (τ, v) for currently-OpEnqStored τ with π pending. *)
Definition pending_stored_pushes_at_π
    (stat : gmap positive op_status_t)
    (π : gmap positive proc_status) : list (positive * val) :=
  map_fold (fun τ op acc =>
    match op with
    | OpEnqStored v _ =>
      if decide (π !! τ = Some (Push, v, None))
      then (τ, v) :: acc
      else acc
    | _ => acc
    end) [] stat.

Lemma pending_stored_pushes_at_π_Forall stat π :
  Forall (λ pv, π !! pv.1 = Some (Push, pv.2, None))
    (pending_stored_pushes_at_π stat π).
Proof.
  unfold pending_stored_pushes_at_π.
  apply (map_fold_weak_ind
    (λ acc _, Forall (λ pv, π !! pv.1 = Some (Push, pv.2, None)) acc)).
  - apply Forall_nil. trivial.
  - intros τ op m acc Hnone IH.
    destruct op as [v_x | v_x i_x | v_x i_x | v_x i_x | | v_x | v_x].
    + exact IH.
    + exact IH.
    + case_decide as Hπτ.
      * apply Forall_cons. split; [exact Hπτ | exact IH].
      * exact IH.
    + exact IH.
    + exact IH.
    + exact IH.
    + exact IH.
Qed.

Lemma pending_stored_pushes_at_π_implies_stored stat π τ_x v_x :
  (τ_x, v_x) ∈ pending_stored_pushes_at_π stat π →
  ∃ i, stat !! τ_x = Some (OpEnqStored v_x i).
Proof.
  unfold pending_stored_pushes_at_π.
  apply (map_fold_weak_ind
    (λ acc m, (τ_x, v_x) ∈ acc → ∃ i, m !! τ_x = Some (OpEnqStored v_x i))).
  - intros Habs. exfalso. apply elem_of_nil in Habs. exact Habs.
  - intros τ' op m' acc Hnone IH Hacc.
    destruct op as [v' | v' i' | v' i' | v' i' | | v' | v'].
    + apply IH in Hacc as (i & Hi).
      exists i. rewrite lookup_insert_ne; first exact Hi.
      intros ->. rewrite Hnone in Hi. discriminate.
    + apply IH in Hacc as (i & Hi).
      exists i. rewrite lookup_insert_ne; first exact Hi.
      intros ->. rewrite Hnone in Hi. discriminate.
    + case_decide as Hπ.
      * apply elem_of_cons in Hacc as [Heq | Hacc'].
        -- injection Heq as -> ->. exists i'. apply lookup_insert_eq.
        -- apply IH in Hacc' as (i_acc & Hi_acc).
           exists i_acc. rewrite lookup_insert_ne; first exact Hi_acc.
           intros ->. rewrite Hnone in Hi_acc. discriminate.
      * apply IH in Hacc as (i & Hi).
        exists i. rewrite lookup_insert_ne; first exact Hi.
        intros ->. rewrite Hnone in Hi. discriminate.
    + apply IH in Hacc as (i & Hi).
      exists i. rewrite lookup_insert_ne; first exact Hi.
      intros ->. rewrite Hnone in Hi. discriminate.
    + apply IH in Hacc as (i & Hi).
      exists i. rewrite lookup_insert_ne; first exact Hi.
      intros ->. rewrite Hnone in Hi. discriminate.
    + apply IH in Hacc as (i & Hi).
      exists i. rewrite lookup_insert_ne; first exact Hi.
      intros ->. rewrite Hnone in Hi. discriminate.
    + apply IH in Hacc as (i & Hi).
      exists i. rewrite lookup_insert_ne; first exact Hi.
      intros ->. rewrite Hnone in Hi. discriminate.
Qed.

Lemma pending_stored_pushes_at_π_complete stat π τ_x v_x i_x :
  stat !! τ_x = Some (OpEnqStored v_x i_x) →
  π !! τ_x = Some (Push, v_x, None) →
  (τ_x, v_x) ∈ pending_stored_pushes_at_π stat π.
Proof.
  intros Hstat Hπ.
  unfold pending_stored_pushes_at_π.
  apply (map_fold_weak_ind
    (λ acc m, m !! τ_x = Some (OpEnqStored v_x i_x) → (τ_x, v_x) ∈ acc));
    last exact Hstat.
  - intros Habs. rewrite lookup_empty in Habs. discriminate.
  - intros τ' op m' acc Hnone IH Hstat'.
    destruct (decide (τ' = τ_x)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hstat'.
      injection Hstat' as ->.
      simpl. rewrite decide_True; last exact Hπ.
      apply elem_of_cons. left. reflexivity.
    + rewrite lookup_insert_ne in Hstat'; last exact Hne.
      destruct op as [v' | v' i' | v' i' | v' i' | | v' | v'].
      * apply IH. exact Hstat'.
      * apply IH. exact Hstat'.
      * case_decide as Hπτ'.
        -- apply elem_of_cons. right. apply IH. exact Hstat'.
        -- apply IH. exact Hstat'.
      * apply IH. exact Hstat'.
      * apply IH. exact Hstat'.
      * apply IH. exact Hstat'.
      * apply IH. exact Hstat'.
Qed.

(* Destructure a chained config (in the list_to_set image of pushes). *)
Lemma chained_config_destruct
    (s_q : list val) (π_q : gmap positive proc_status)
    (pushes : list (positive * val))
    (s' : list val) (π' : gmap positive proc_status) :
  (s', π') ∈ (list_to_set (map (fun pv : positive * val =>
    ((s_q ++ [pv.2])%list, <[pv.1:=(Push, pv.2, Some #())]>π_q))
    pushes) : gset single_config_q) →
  ∃ τ_x v_x, s' = (s_q ++ [v_x])%list ∧
             π' = <[τ_x:=(Push, v_x, Some #())]>π_q ∧
             (τ_x, v_x) ∈ pushes.
Proof.
  intros Hin.
  apply elem_of_list_to_set in Hin.
  apply list_elem_of_fmap in Hin as ([τ_x v_x] & Heq & Hpv).
  exists τ_x, v_x.
  injection Heq as Hs_eq Hπ_eq.
  split_and!; [exact Hs_eq | exact Hπ_eq | exact Hpv].
Qed.

(* Chain LP a specific (τ, v) push in a single config (s_q, π_q),
   for each entry in a list of pending pushes. Returns extended M_full'
   such that each LP'd config is in M_full'. *)
Lemma mcfg_steps_chain_lp_push_list
    (M_full : @meta_config hwq_model)
    (s_q : list val) (π_q : gmap positive proc_status)
    (pushes : list (positive * val)) :
  (s_q, π_q) ∈ M_full →
  Forall (λ pv : positive * val,
            π_q !! pv.1 = Some (Push, pv.2, None)) pushes →
  ∃ (M_full' : @meta_config hwq_model),
    mcfg_steps M_full M_full' [] ∧
    M_full ⊆ M_full' ∧
    Forall (λ pv : positive * val,
            ((s_q ++ [pv.2])%list,
             <[pv.1:=(Push, pv.2, Some #())]>π_q) ∈ M_full') pushes ∧
    (* Upper bound: every y ∈ M_full' is either in M_full or is an LP'd image
       for some (τ, v) in pushes. *)
    (∀ y, y ∈ M_full' →
       y ∈ M_full ∨ ∃ pv : positive * val, pv ∈ pushes ∧
         y = ((s_q ++ [pv.2])%list,
              <[pv.1:=(Push, pv.2, Some #())]>π_q)).
Proof.
  intros Hin Hpushes.
  induction pushes as [|[τ v] pushes' IH].
  - exists M_full. split_and!.
    + apply mcfg_steps_nil.
    + reflexivity.
    + apply Forall_nil. trivial.
    + intros y Hy. left. exact Hy.
  - inversion Hpushes as [|? ? Hπτ Hpushes' Heq]; subst.
    destruct (IH Hpushes') as (M_full' & Hsteps & Hsub & Hwit & Hupper).
    assert (Hin_in_M_full' : (s_q, π_q) ∈ M_full') by (apply Hsub; exact Hin).
    pose (new_config := ((s_q ++ [v])%list,
                          <[τ:=(Push, v, Some #())]>π_q)).
    exists ({[new_config]} ∪ M_full').
    split_and!.
    + replace ([] : list (positive * trace)) with
        (([] : list (positive * trace)) ++ ([] : list (positive * trace)))
        by reflexivity.
      eapply mcfg_steps_app; first exact Hsteps.
      apply mcfg_steps_singleton.
      apply (mcfg_step_interm M_full' s_q π_q τ
              Push v (s_q ++ [v])%list #()).
      * exact Hin_in_M_full'.
      * exact Hπτ.
      * split; reflexivity.
    + intros y Hy. apply elem_of_union. right. apply Hsub. exact Hy.
    + apply Forall_cons. split.
      * unfold new_config.
        apply elem_of_union. left. apply elem_of_singleton. reflexivity.
      * eapply Forall_impl; first exact Hwit.
        intros [τ_a v_a] Hwit_a.
        simpl in Hwit_a |- *.
        apply elem_of_union. right. exact Hwit_a.
    + intros y Hy. apply elem_of_union in Hy as [Hy_new | Hy_M'].
      * apply elem_of_singleton in Hy_new. subst y.
        right. exists (τ, v). split; last reflexivity.
        apply elem_of_cons. left. reflexivity.
      * destruct (Hupper y Hy_M') as [Hy_full | (pv & Hpv_in & ->)].
        -- left. exact Hy_full.
        -- right. exists pv. split; last reflexivity.
           apply elem_of_cons. right. exact Hpv_in.
Qed.

(* LP a specific push (τ, v) in a single config. *)
Lemma mcfg_steps_lp_push_one
    (M_full : @meta_config hwq_model)
    (s_q : list val) (π_q : gmap positive proc_status)
    (τ : positive) (v : val) :
  (s_q, π_q) ∈ M_full →
  π_q !! τ = Some (Push, v, None) →
  let new_config := ((s_q ++ [v])%list,
                      <[τ:=(Push, v, Some #())]>π_q) in
  mcfg_steps M_full ({[new_config]} ∪ M_full) [].
Proof.
  intros Hin Hπτ.
  apply mcfg_steps_singleton.
  apply (mcfg_step_interm M_full s_q π_q τ
           Push v (s_q ++ [v])%list #()); try assumption.
  split; reflexivity.
Qed.

Lemma mcfg_steps_chain_lp_push_all
    (M_full : @meta_config hwq_model)
    (M_g : gset single_config_q)
    (τ : positive) (v : val) :
  set_to_propset M_g ⊆ M_full →
  ∃ (M_full' : @meta_config hwq_model),
    mcfg_steps M_full M_full' [] ∧
    M_full ⊆ M_full' ∧
    (∀ x : single_config_q, x ∈ M_g →
        x.2 !! τ = Some (Push, v, None) →
        (x.1 ++ [v], <[τ:=(Push, v, Some #())]>x.2) ∈ M_full') ∧
    (* Upper bound: M_full' adds only LP'd images of pending M_g cfgs to M_full. *)
    (∀ y, y ∈ M_full' → y ∈ M_full ∨
       ∃ x : single_config_q, x ∈ M_g ∧
         x.2 !! τ = Some (Push, v, None) ∧
         y = (x.1 ++ [v], <[τ:=(Push, v, Some #())]>x.2)).
Proof.
  intros Hsub.
  induction M_g as [|x M_g' Hnotin IH] using set_ind_L.
  - exists M_full. split_and!.
    + apply mcfg_steps_nil.
    + reflexivity.
    + intros y Hy. set_solver.
    + intros y Hy. left. exact Hy.
  - assert (Hsub' : set_to_propset M_g' ⊆ M_full).
    { intros y Hy. apply Hsub.
      apply elem_of_set_to_propset.
      apply elem_of_set_to_propset in Hy.
      set_solver. }
    destruct (IH Hsub') as (M_full' & Hsteps & Hsubset & Hwitnesses & Hupper).
    destruct (decide (x.2 !! τ = Some (Push, v, None))) as [Hxτ | Hxτ_no].
    + (* x has τ pending: add its LP'd version. *)
      pose (new_config := ((x.1 ++ [v])%list,
                           <[τ:=(Push, v, Some #())]>x.2)).
      exists ({[new_config]} ∪ M_full').
      assert (Hx_in_full : x ∈ M_full').
      { apply Hsubset. apply Hsub.
        apply elem_of_set_to_propset. set_solver. }
      destruct x as [s π]. simpl in Hxτ.
      split_and!.
      * replace ([] : list (positive * trace)) with (([] : list (positive * trace)) ++ ([] : list (positive * trace))) by reflexivity.
        eapply mcfg_steps_app; first exact Hsteps.
        apply mcfg_steps_singleton.
        apply (mcfg_step_interm M_full' s π τ
                 Push v (s ++ [v])%list #()).
        -- exact Hx_in_full.
        -- exact Hxτ.
        -- split; reflexivity.
      * intros y Hy. apply elem_of_union. right. by apply Hsubset.
      * intros y Hy Hyτ.
        apply elem_of_union in Hy as [Hy_singleton | Hy_M_g'].
        -- apply elem_of_singleton in Hy_singleton. subst y. simpl in *.
           apply elem_of_union. left. apply elem_of_singleton.
           unfold new_config. reflexivity.
        -- apply elem_of_union. right.
           exact (Hwitnesses y Hy_M_g' Hyτ).
      * intros y Hy.
        apply elem_of_union in Hy as [Hy_singleton | Hy_M_full'].
        -- apply elem_of_singleton in Hy_singleton. subst y.
           right. exists (s, π). split; last (split; [exact Hxτ | reflexivity]).
           set_solver.
        -- destruct (Hupper y Hy_M_full') as [Hy_M_full | (x' & Hx'_in & Hx'τ & ->)].
           ++ left. exact Hy_M_full.
           ++ right. exists x'. split; last (split; [exact Hx'τ | reflexivity]).
              set_solver.
    + (* x doesn't have τ pending: nothing to add. *)
      exists M_full'. split_and!; try assumption.
      * intros y Hy Hyτ.
        apply elem_of_union in Hy as [Hy_singleton | Hy_M_g'].
        -- apply elem_of_singleton in Hy_singleton. subst y.
           exfalso. apply Hxτ_no. exact Hyτ.
        -- exact (Hwitnesses y Hy_M_g' Hyτ).
      * intros y Hy.
        destruct (Hupper y Hy) as [Hy_M_full | (x' & Hx'_in & Hx'τ & ->)].
        -- left. exact Hy_M_full.
        -- right. exists x'. split; last (split; [exact Hx'τ | reflexivity]).
           set_solver.
Qed.

(* LP a specific pop (τ) on a single config (s = v :: s'). *)
Lemma mcfg_steps_lp_pop_one
    (M_full : @meta_config hwq_model)
    (v : val) (s' : list val) (π_q : gmap positive proc_status)
    (τ : positive) :
  (v :: s', π_q) ∈ M_full →
  π_q !! τ = Some (Pop, #(), None) →
  let new_config :=
    (s', <[τ:=(Pop, #(),
                Some (encode_response (NonEmpty v)))]>π_q) in
  mcfg_steps M_full ({[new_config]} ∪ M_full) [].
Proof.
  intros Hin Hπτ.
  apply mcfg_steps_singleton.
  apply (mcfg_step_interm M_full (v :: s') π_q τ
           Pop #() s' (encode_response (NonEmpty v))); try assumption.
  split; reflexivity.
Qed.

(* Two-step chain: LP push τ_e then LP pop τ_d on the result.
   From (s=[], π_init), construct (s=[], π_final) where π_final has
   τ_e LP'd as push v AND τ_d LP'd as pop NE v. *)
Lemma mcfg_steps_chain_push_then_pop
    (M_full : @meta_config hwq_model)
    (π_init : gmap positive proc_status)
    (τ_e τ_d : positive) (v : val) :
  ([], π_init) ∈ M_full →
  π_init !! τ_e = Some (Push, v, None) →
  π_init !! τ_d = Some (Pop, #(), None) →
  τ_e ≠ τ_d →
  let π_step1 := <[τ_e:=(Push, v, Some #())]>π_init in
  let π_step2 := <[τ_d:=(Pop, #(),
                          Some (encode_response (NonEmpty v)))]>π_step1 in
  let M_full' := {[([], π_step2); ([v], π_step1)]} ∪ M_full in
  mcfg_steps M_full M_full' [] ∧
  ([], π_step2) ∈ M_full' ∧
  ([v], π_step1) ∈ M_full'.
Proof.
  intros Hin_empty Hπ_e Hπ_d Hne_ed.
  simpl.
  set (π_step1 := <[τ_e:=(Push, v, Some #())]>π_init).
  set (π_step2 := <[τ_d:=(Pop, #(),
                          Some (encode_response (NonEmpty v)))]>π_step1).
  (* Step 1: LP τ_e push on ([], π_init) → add ([v], π_step1). *)
  set (M1 := {[([v], π_step1)]} ∪ M_full).
  assert (Hstep1 : mcfg_steps M_full M1 []).
  { apply mcfg_steps_singleton.
    apply (mcfg_step_interm M_full [] π_init τ_e
             Push v [v] #()); try assumption.
    split; reflexivity. }
  (* Step 2: LP τ_d pop on ([v], π_step1) → add ([], π_step2). *)
  assert (Hin_step1 : ([v], π_step1) ∈ M1).
  { apply elem_of_union. left. apply elem_of_singleton. reflexivity. }
  assert (Hπ_d_step1 : π_step1 !! τ_d = Some (Pop, #(), None)).
  { unfold π_step1. rewrite lookup_insert_ne;
      last (intros ?; apply Hne_ed; congruence). exact Hπ_d. }
  set (M2 := {[([], π_step2)]} ∪ M1).
  assert (Hstep2 : mcfg_steps M1 M2 []).
  { apply mcfg_steps_singleton.
    apply (mcfg_step_interm M1 [v] π_step1 τ_d
             Pop #() [] (encode_response (NonEmpty v))); try assumption.
    split; reflexivity. }
  (* Combine. *)
  assert (M2 = {[([], π_step2); ([v], π_step1)]} ∪ M_full) as -> by set_solver.
  split_and!.
  - replace ([] : list (positive * trace)) with
      (([] : list (positive * trace)) ++ ([] : list (positive * trace)))
      by reflexivity.
    eapply mcfg_steps_app; first exact Hstep1. exact Hstep2.
  - apply elem_of_union. left. set_solver.
  - apply elem_of_union. left. set_solver.
Qed.

(* ====================================================================== *)
(* The multiple-mcfg_step_interm chaining lemma for Phase 2 FAA enq
   closure_push universal-permutation maintenance.

   This lemma applies at Phase 2 FAA enq (NOT Phase 1 Call). At Phase 2,
   τ transitions from OpEnqPending → OpEnqReserved (FAA'd a slot). At this
   transition, τ joins the "closure-eligible" set (corresponds to TLA+'s
   GoodEnqSet, which only includes slots from FAA'd-or-later processes).

   The lemma states: given M_full containing M_g (pre-FAA), and τ already
   present in every config of M_full as Pending Push v_push (added by
   Phase 1 Call), we can chain multiple mcfg_step_interm applications to
   reach M_full' containing all LP'd-at-all-permutations configs for τ
   together with other FAA'd-or-later Pending pushes.

   The mcfg_steps trace is [] (only internal LP steps; no Call/Ret).

   Intended proof: for each (cfg, pushes) pair with τ ∈ pushes.*1, decompose
   per-permutation. Use closure_push (stat-conditioned) at pre-FAA M_g to
   find partial-LP'd base configs. Chain mcfg_step_interm in the chosen
   order to materialize each (s', LP'd) config. *)
(* Helper: cumulative-LP chain. Given (s_q, π_q) ∈ M_full and a NoDup pushes list
   where every push has π_q[pv.1] = Pending Push pv.2, materialize the
   cumulative linearized config lineraize_pending_push pushes (s_q, π_q) via
   chained mcfg_step_interm applications. *)
Lemma mcfg_steps_chain_lp_push_cumulative
    (M_full : @meta_config hwq_model)
    (s_q : list val) (π_q : gmap positive proc_status)
    (pushes : list (positive * val)) :
  (s_q, π_q) ∈ M_full →
  NoDup pushes.*1 →
  Forall (λ pv : positive * val,
            π_q !! pv.1 = Some (Push, pv.2, None)) pushes →
  ∃ (M_full' : @meta_config hwq_model),
    mcfg_steps M_full M_full' [] ∧
    M_full ⊆ M_full' ∧
    lineraize_pending_push pushes (s_q, π_q) ∈ M_full' ∧
    (* Upper bound: every y ∈ M_full' is either in M_full or is
       lineraize_pending_push prefix (s_q, π_q) for some prefix of pushes. *)
    (∀ y, y ∈ M_full' → y ∈ M_full ∨
       ∃ prefix : list (positive * val), prefix `prefix_of` pushes ∧
                  y = lineraize_pending_push prefix (s_q, π_q)).
Proof.
  intros Hin Hnd Hπ_pushes.
  induction pushes as [|pv pushes' IH] using rev_ind.
  - exists M_full. split_and!.
    + apply mcfg_steps_nil.
    + reflexivity.
    + unfold lineraize_pending_push. simpl.
      rewrite app_nil_r.
      assert (Heq_π : map_imap (λ τ_x x, if bool_decide (τ_x ∈ ([] : list positive))
                                    then Some (x.1, Some #()) else Some x) π_q = π_q).
      { apply map_eq. intros τ_x. rewrite map_lookup_imap.
        destruct (π_q !! τ_x) as [x|] eqn:Hπ_τx; rewrite Hπ_τx /=; reflexivity. }
      rewrite Heq_π. exact Hin.
    + intros y Hy. left. exact Hy.
  - destruct pv as [τ_x v_x].
    rewrite fmap_app /= in Hnd.
    apply NoDup_app in Hnd as (Hnd_pre & Hdisj & _).
    apply Forall_app in Hπ_pushes as [Hπ_pre Hπ_last].
    inversion Hπ_last as [|? ? Hπ_τx _ Heq]; subst.
    simpl in Hπ_τx.
    destruct (IH Hnd_pre Hπ_pre) as (M_full' & Hsteps & Hsubset & Hin_lin' & Hupper).
    set (s_pre := (lineraize_pending_push pushes' (s_q, π_q)).1).
    set (π_pre := (lineraize_pending_push pushes' (s_q, π_q)).2).
    assert (Hpre_eq : lineraize_pending_push pushes' (s_q, π_q) = (s_pre, π_pre))
      by reflexivity.
    rewrite Hpre_eq in Hin_lin'.
    pose (new_config :=
            ((s_pre ++ [v_x])%list,
             <[τ_x:=(Push, v_x, Some #())]>π_pre)).
    exists ({[new_config]} ∪ M_full').
    assert (Hπ_pre_τx : π_pre !! τ_x = Some (Push, v_x, None)).
    { unfold π_pre, lineraize_pending_push. simpl.
      rewrite map_lookup_imap Hπ_τx /=.
      rewrite bool_decide_eq_false_2; first reflexivity.
      intros Habs. apply (Hdisj τ_x); first exact Habs.
      apply list_elem_of_singleton. reflexivity. }
    split_and!.
    + replace ([] : list (positive * trace)) with
        (([] : list (positive * trace)) ++ ([] : list (positive * trace)))
        by reflexivity.
      eapply mcfg_steps_app; first exact Hsteps.
      apply mcfg_steps_singleton.
      apply (mcfg_step_interm M_full' s_pre π_pre τ_x
              Push v_x (s_pre ++ [v_x])%list #()).
      * exact Hin_lin'.
      * exact Hπ_pre_τx.
      * split; reflexivity.
    + intros y Hy. apply elem_of_union. right. by apply Hsubset.
    + apply elem_of_union. left. apply elem_of_singleton.
      unfold new_config.
      unfold lineraize_pending_push. simpl.
      rewrite fmap_app /=.
      rewrite app_assoc.
      f_equal.
      apply map_eq. intros τ_y.
      rewrite map_lookup_imap.
      destruct (decide (τ_y = τ_x)) as [-> | Hne_y].
      * rewrite lookup_insert_eq.
        rewrite Hπ_τx /=.
        rewrite fmap_app /=.
        rewrite bool_decide_eq_true_2; first reflexivity.
        apply elem_of_app. right. apply list_elem_of_singleton. reflexivity.
      * rewrite lookup_insert_ne; last (intros ?; apply Hne_y; congruence).
        unfold π_pre, lineraize_pending_push. simpl.
        rewrite map_lookup_imap.
        destruct (π_q !! τ_y) as [x|] eqn:Hπ_τy; rewrite Hπ_τy /=; last reflexivity.
        rewrite fmap_app /=.
        destruct (decide (τ_y ∈ pushes'.*1)) as [Hin_p | Hnin_p].
        -- rewrite (bool_decide_true (τ_y ∈ pushes'.*1 ++ [τ_x]));
             last (apply elem_of_app; by left).
           rewrite (bool_decide_true (τ_y ∈ pushes'.*1)); last exact Hin_p.
           reflexivity.
        -- rewrite (bool_decide_false (τ_y ∈ pushes'.*1 ++ [τ_x]));
             last (intros Habs; apply elem_of_app in Habs as [|Hin_τx];
                   [contradiction |
                    apply list_elem_of_singleton in Hin_τx; subst; apply Hne_y; reflexivity]).
           rewrite (bool_decide_false (τ_y ∈ pushes'.*1)); last exact Hnin_p.
           reflexivity.
    + (* Upper bound for inductive step *)
      intros y Hy.
      apply elem_of_union in Hy as [Hy_new | Hy_M'].
      * apply elem_of_singleton in Hy_new. subst y.
        right. exists (pushes' ++ [(τ_x, v_x)]). split.
        -- exists []. by rewrite app_nil_r.
        -- unfold new_config.
           unfold lineraize_pending_push. simpl.
           rewrite fmap_app /=.
           rewrite app_assoc.
           f_equal.
           apply map_eq. intros τ_y.
           rewrite map_lookup_imap.
           destruct (decide (τ_y = τ_x)) as [-> | Hne_y].
           ++ rewrite lookup_insert_eq.
              rewrite Hπ_τx /=.
              rewrite fmap_app /=.
              rewrite bool_decide_eq_true_2; first reflexivity.
              apply elem_of_app. right. apply list_elem_of_singleton. reflexivity.
           ++ rewrite lookup_insert_ne; last (intros ?; apply Hne_y; congruence).
              unfold π_pre, lineraize_pending_push. simpl.
              rewrite map_lookup_imap.
              destruct (π_q !! τ_y) as [x|] eqn:Hπ_τy; rewrite Hπ_τy /=; last reflexivity.
              rewrite fmap_app /=.
              destruct (decide (τ_y ∈ pushes'.*1)) as [Hin_p | Hnin_p].
              ** rewrite (bool_decide_true (τ_y ∈ pushes'.*1 ++ [τ_x]));
                   last (apply elem_of_app; by left).
                 rewrite (bool_decide_true (τ_y ∈ pushes'.*1)); last exact Hin_p.
                 reflexivity.
              ** rewrite (bool_decide_false (τ_y ∈ pushes'.*1 ++ [τ_x]));
                   last (intros Habs; apply elem_of_app in Habs as [|Hin_τx];
                         [contradiction |
                          apply list_elem_of_singleton in Hin_τx; subst; apply Hne_y; reflexivity]).
                 rewrite (bool_decide_false (τ_y ∈ pushes'.*1)); last exact Hnin_p.
                 reflexivity.
      * destruct (Hupper y Hy_M') as [Hy_full | (prefix & Hprefix & ->)].
        -- left. exact Hy_full.
        -- right. exists prefix. split; last reflexivity.
           apply prefix_app_r. exact Hprefix.
Qed.

(* Helper: extend M_full' to include lineraize_pending_push for all pushes
   in a given list of candidate pushes-lists, for a fixed cfg ∈ M_full. *)
Lemma mcfg_steps_chain_lp_push_all_lists
    (M_full : @meta_config hwq_model)
    (cfg : single_config_q)
    (pushes_lists : list (list (positive * val))) :
  cfg ∈ M_full →
  Forall (λ pushes,
            NoDup pushes.*1 ∧
            Forall (λ pv : positive * val,
                      cfg.2 !! pv.1 = Some (Push, pv.2, None)) pushes)
         pushes_lists →
  ∃ (M_full' : @meta_config hwq_model),
    mcfg_steps M_full M_full' [] ∧
    M_full ⊆ M_full' ∧
    Forall (λ pushes, lineraize_pending_push pushes cfg ∈ M_full') pushes_lists ∧
    (* Upper bound: every y ∈ M_full' is either in M_full or is
       lineraize_pending_push (some prefix of some pushes ∈ pushes_lists) cfg. *)
    (∀ y, y ∈ M_full' → y ∈ M_full ∨
       ∃ pushes prefix, pushes ∈ pushes_lists ∧
                        prefix `prefix_of` pushes ∧
                        y = lineraize_pending_push prefix cfg).
Proof.
  intros Hin Hall.
  induction pushes_lists as [|pushes pl' IH].
  - exists M_full. split_and!.
    + apply mcfg_steps_nil.
    + reflexivity.
    + apply Forall_nil. trivial.
    + intros y Hy. left. exact Hy.
  - inversion Hall as [|? ? [Hnd Hπ_pushes] Hall_rest Heq]; subst.
    destruct (IH Hall_rest) as (M_full' & Hsteps & Hsubset & Hwit & Hupper).
    assert (Hcfg_in : cfg ∈ M_full') by (apply Hsubset; exact Hin).
    destruct cfg as [s_q π_q]. simpl in Hπ_pushes.
    destruct (mcfg_steps_chain_lp_push_cumulative
                M_full' s_q π_q pushes Hcfg_in Hnd Hπ_pushes)
      as (M_full'' & Hsteps' & Hsubset' & Hin_lin & Hupper_cum).
    exists M_full''. split_and!.
    + replace ([] : list (positive * trace)) with
        (([] : list (positive * trace)) ++ ([] : list (positive * trace)))
        by reflexivity.
      eapply mcfg_steps_app; first exact Hsteps. exact Hsteps'.
    + intros y Hy. apply Hsubset'. by apply Hsubset.
    + apply Forall_cons. split.
      * exact Hin_lin.
      * eapply Forall_impl; first exact Hwit.
        intros pushes_x Hwit_x. apply Hsubset'. exact Hwit_x.
    + intros y Hy.
      destruct (Hupper_cum y Hy) as [Hy_M' | (prefix & Hprefix & ->)].
      * (* y ∈ M_full' = previous chain *)
        destruct (Hupper y Hy_M') as [Hy_full | (pushes_x & prefix_x & Hpush_in & Hprefix_x & ->)].
        -- left. exact Hy_full.
        -- right. exists pushes_x, prefix_x. split_and!.
           ++ apply elem_of_cons. right. exact Hpush_in.
           ++ exact Hprefix_x.
           ++ reflexivity.
      * (* y is lineraize_pending_push prefix (s_q, π_q) for prefix of pushes (this iteration) *)
        right. exists pushes, prefix. split_and!.
        -- apply elem_of_cons. left. reflexivity.
        -- exact Hprefix.
        -- reflexivity.
Qed.

(* Helper: iterate over a list of configs cfgs ⊆ M_full, materializing all
   lineraize_pending_push pushes cfg ∈ M_full' for valid pushes per cfg. *)
Lemma mcfg_steps_chain_lp_push_all_cfgs
    (M_full : @meta_config hwq_model)
    (cfgs : list single_config_q)
    (push_lists_of : single_config_q → list (list (positive * val))) :
  Forall (λ cfg, cfg ∈ M_full) cfgs →
  Forall (λ cfg, Forall (λ pushes,
            NoDup pushes.*1 ∧
            Forall (λ pv : positive * val,
                      cfg.2 !! pv.1 = Some (Push, pv.2, None)) pushes)
          (push_lists_of cfg)) cfgs →
  ∃ (M_full' : @meta_config hwq_model),
    mcfg_steps M_full M_full' [] ∧
    M_full ⊆ M_full' ∧
    Forall (λ cfg,
              Forall (λ pushes, lineraize_pending_push pushes cfg ∈ M_full')
                     (push_lists_of cfg)) cfgs ∧
    (* Upper bound: every y ∈ M_full' is either in M_full or is
       lineraize_pending_push prefix cfg for some cfg ∈ cfgs and prefix
       of some pushes ∈ push_lists_of cfg. *)
    (∀ y, y ∈ M_full' → y ∈ M_full ∨
       ∃ cfg pushes prefix, cfg ∈ cfgs ∧
                            pushes ∈ push_lists_of cfg ∧
                            prefix `prefix_of` pushes ∧
                            y = lineraize_pending_push prefix cfg).
Proof.
  intros Hin Hpushes.
  induction cfgs as [|cfg cfgs' IH].
  - exists M_full. split_and!.
    + apply mcfg_steps_nil.
    + reflexivity.
    + apply Forall_nil. trivial.
    + intros y Hy. left. exact Hy.
  - inversion Hin as [|? ? Hcfg_in Hin_rest Heq1]; subst.
    inversion Hpushes as [|? ? Hpushes_cfg Hpushes_rest Heq2]; subst.
    destruct (IH Hin_rest Hpushes_rest)
      as (M_full' & Hsteps & Hsubset & Hwit & Hupper).
    assert (Hcfg_in_M_full' : cfg ∈ M_full') by (apply Hsubset; exact Hcfg_in).
    destruct (mcfg_steps_chain_lp_push_all_lists
                M_full' cfg (push_lists_of cfg) Hcfg_in_M_full' Hpushes_cfg)
      as (M_full'' & Hsteps' & Hsubset' & Hin_lin & Hupper_lists).
    exists M_full''. split_and!.
    + replace ([] : list (positive * trace)) with
        (([] : list (positive * trace)) ++ ([] : list (positive * trace)))
        by reflexivity.
      eapply mcfg_steps_app; first exact Hsteps. exact Hsteps'.
    + intros y Hy. apply Hsubset'. by apply Hsubset.
    + apply Forall_cons. split.
      * exact Hin_lin.
      * eapply Forall_impl; first exact Hwit.
        intros cfg_x Hwit_x.
        eapply Forall_impl; first exact Hwit_x.
        intros pushes_x Hp_in. apply Hsubset'. exact Hp_in.
    + intros y Hy.
      destruct (Hupper_lists y Hy) as
        [Hy_M' | (pushes_x & prefix_x & Hpush_in & Hprefix_x & ->)].
      * destruct (Hupper y Hy_M') as
          [Hy_full | (cfg_x & pushes_x & prefix_x & Hcfg_x_in & Hpush_x_in & Hprefix_x & ->)].
        -- left. exact Hy_full.
        -- right. exists cfg_x, pushes_x, prefix_x. split_and!.
           ++ apply elem_of_cons. right. exact Hcfg_x_in.
           ++ exact Hpush_x_in.
           ++ exact Hprefix_x.
           ++ reflexivity.
      * right. exists cfg, pushes_x, prefix_x. split_and!.
        -- apply elem_of_cons. left. reflexivity.
        -- exact Hpush_in.
        -- exact Hprefix_x.
        -- reflexivity.
Qed.

Lemma mcfg_steps_chain_lp_push_all_perm
    (M_full : @meta_config hwq_model)
    (M_g : gset single_config_q)
    (stat : gmap positive op_status_t)
    (τ : positive) (v_push : val) (i_τ : nat) :
  set_to_propset M_g ⊆ M_full →
  closure_push M_g stat →
  (* Phase 2 FAA: τ is at OpEnqPending pre-FAA, transitions to OpEnqReserved. *)
  stat !! τ = Some (OpEnqPending v_push) →
  (* In all configs, τ has Pending Push v_push (set by Phase 1 Call). *)
  set_Forall (λ '(_, π), π !! τ = Some (Push, v_push, None)) M_full →
  let stat' := <[τ:=OpEnqReserved v_push i_τ]>stat in
  ∃ (M_full' : @meta_config hwq_model),
    mcfg_steps M_full M_full' [] ∧
    M_full ⊆ M_full' ∧
    (* For each cfg ∈ M_g and any pushes containing τ-and-other-FAA'd-pendings,
       the linearized config is in M_full'. This populates the closure under
       the post-FAA stat'. *)
    (∀ cfg (pushes : list (positive * val)),
        cfg ∈ M_g →
        NoDup pushes.*1 →
        pushes ⊆ pending_push_of_config cfg →
        (∀ pv, pv ∈ pushes → ∃ v i,
           stat' !! pv.1 = Some (OpEnqReserved v i) ∨
           stat' !! pv.1 = Some (OpEnqStored v i)) →
        lineraize_pending_push pushes cfg ∈ M_full') ∧
    (* Unconditional inclusion: ∀ cfg ∈ M_g, ∀ pushes ∈ all_push_lists(pending_push cfg),
       lineraize_pending_push pushes cfg ∈ M_full'. *)
    (∀ cfg pushes, cfg ∈ M_g →
        pushes ∈ all_push_lists (pending_push_of_config cfg) →
        lineraize_pending_push pushes cfg ∈ M_full') ∧
    (* Upper bound: every y ∈ M_full' is either in M_full or is
       lineraize_pending_push pushes cfg for some cfg ∈ M_g and
       pushes ∈ all_push_lists(pending_push_of_config cfg). *)
    (∀ y, y ∈ M_full' → y ∈ M_full ∨
       ∃ cfg pushes, cfg ∈ M_g ∧
                     pushes ∈ all_push_lists (pending_push_of_config cfg) ∧
                     y = lineraize_pending_push pushes cfg).
Proof.
  intros Hsub Hcl Hstat_τ Hfresh_π stat'.
  (* Plan:
     - Enumerate cfgs := elements M_g (finite list).
     - For each cfg ∈ M_g, define push_lists_of cfg as all_push_lists
       (pending_push_of_config cfg) — finite list of valid pushes-lists.
     - Apply mcfg_steps_chain_lp_push_all_cfgs to build M_full' that contains
       lineraize_pending_push pushes cfg for every (cfg, pushes) with
       pushes ∈ all_push_lists (pending_push_of_config cfg). *)
  set (push_lists_of := λ cfg : single_config_q,
                          all_push_lists (pending_push_of_config cfg)).
  assert (Hcfgs_in : Forall (λ cfg, cfg ∈ M_full) (elements M_g)).
  { apply Forall_forall. intros cfg Hcfg_in_list.
    apply Hsub. apply elem_of_set_to_propset.
    by apply elem_of_elements in Hcfg_in_list. }
  assert (Hcfgs_pushes : Forall (λ cfg, Forall (λ pushes,
              NoDup pushes.*1 ∧
              Forall (λ pv : positive * val,
                        cfg.2 !! pv.1 = Some (Push, pv.2, None)) pushes)
            (push_lists_of cfg)) (elements M_g)).
  { apply Forall_forall. intros cfg Hcfg_in_list.
    apply Forall_forall. intros pushes Hpushes_in_list.
    unfold push_lists_of, all_push_lists in Hpushes_in_list.
    apply list_elem_of_bind in Hpushes_in_list as (sub & Hpushes_perm & Hsub_in_pset).
    rewrite permutations_Permutation in Hpushes_perm.
    rewrite powermset_submseteq in Hsub_in_pset.
    assert (Hpushes_subseteq : pushes ⊆ pending_push_of_config cfg).
    { intros pv Hpv_in.
      rewrite -Hpushes_perm in Hpv_in.
      eapply elem_of_submseteq; first exact Hpv_in. exact Hsub_in_pset. }
    assert (Hnd_pending_keys : NoDup (pending_push_of_config cfg).*1).
    { destruct cfg as [s_q π_q]. unfold pending_push_of_config. simpl.
      assert (Hkeys_sub : (omap (λ '(τ', v), if v is (0, v, None) then Some (τ',v) else None)
                                 (map_to_list π_q)).*1 `sublist_of` (map_to_list π_q).*1).
      { induction (map_to_list π_q) as [|[τ' [[n' v'] resp']] tl IH'].
        - apply sublist_nil.
        - simpl.
          destruct n' as [|n'];
            try (simpl; apply sublist_cons; exact IH').
          destruct resp' as [v_resp |];
            try (simpl; apply sublist_cons; exact IH').
          simpl. apply sublist_skip. exact IH'. }
      eapply sublist_NoDup; last exact Hkeys_sub.
      apply NoDup_fst_map_to_list. }
    split.
    - assert (Hperm_keys : sub.*1 ≡ₚ pushes.*1).
      { apply fmap_Permutation. exact Hpushes_perm. }
      rewrite -Hperm_keys.
      assert (Hsub_keys : sub.*1 ⊆+ (pending_push_of_config cfg).*1).
      { apply (fmap_submseteq fst). exact Hsub_in_pset. }
      apply submseteq_sublist_l in Hsub_keys as (l2 & Hsublist & Hperm_l2).
      eapply sublist_NoDup; last exact Hsublist.
      rewrite Hperm_l2. exact Hnd_pending_keys.
    - apply Forall_forall. intros pv Hpv_in.
      destruct pv as [τ_pv v_pv]. simpl.
      assert (Hpv_in_pending : (τ_pv, v_pv) ∈ pending_push_of_config cfg)
        by (by apply Hpushes_subseteq).
      unfold pending_push_of_config in Hpv_in_pending.
      apply list_elem_of_omap in Hpv_in_pending as ([τ_x [[n_x v_x] resp]] & Hin_list & Hmatch).
      destruct n_x as [|n_x]; try discriminate.
      destruct resp as [v_resp |]; try discriminate.
      simpl in Hmatch. injection Hmatch as Heq1 Heq2. subst.
      apply elem_of_map_to_list in Hin_list.
      exact Hin_list. }
  destruct (mcfg_steps_chain_lp_push_all_cfgs M_full (elements M_g) push_lists_of
              Hcfgs_in Hcfgs_pushes) as (M_full' & Hsteps & Hsubset & Hwit & Hupper).
  exists M_full'. split_and!; try assumption.
  - intros cfg pushes Hin_g Hnd Hsubset_p Hstat_pushes.
    apply elem_of_elements in Hin_g.
    rewrite Forall_forall in Hwit.
    specialize (Hwit cfg Hin_g).
    rewrite Forall_forall in Hwit.
    apply Hwit.
    unfold push_lists_of, all_push_lists.
    apply list_elem_of_bind.
    exists pushes. split.
    + apply permutations_refl.
    + apply powermset_submseteq.
      apply NoDup_submseteq.
      * eapply NoDup_fmap_1. exact Hnd.
      * exact Hsubset_p.
  - (* Unconditional inclusion *)
    intros cfg pushes Hcfg_in Hpush_in.
    apply elem_of_elements in Hcfg_in.
    rewrite Forall_forall in Hwit.
    specialize (Hwit cfg Hcfg_in).
    rewrite Forall_forall in Hwit.
    apply Hwit. unfold push_lists_of. exact Hpush_in.
  - (* Upper bound: y ∈ M_full' iff y ∈ M_full or y is a linearized config
       for some cfg ∈ M_g and pushes ∈ all_push_lists(pending_push_of_config cfg)
       (or a prefix thereof, which is itself in all_push_lists). *)
    intros y Hy. destruct (Hupper y Hy) as
      [Hy_full | (cfg & pushes & prefix & Hcfg_in & Hpush_in & Hprefix & ->)].
    + left. exact Hy_full.
    + right. exists cfg, prefix. split_and!.
      * apply elem_of_elements in Hcfg_in. exact Hcfg_in.
      * (* prefix is in all_push_lists(pending_push_of_config cfg) since
           it's a prefix of pushes ∈ all_push_lists(...). *)
        unfold push_lists_of, all_push_lists in Hpush_in.
        apply list_elem_of_bind in Hpush_in as (sub & Hperm & Hsub_in_pset).
        rewrite permutations_Permutation in Hperm.
        rewrite powermset_submseteq in Hsub_in_pset.
        unfold all_push_lists.
        apply list_elem_of_bind.
        destruct Hprefix as [k Hk].
        exists prefix. split.
        -- apply permutations_refl.
        -- apply powermset_submseteq.
           (* prefix ⊆+ pushes (via Hk: pushes = prefix ++ k). *)
           assert (Hpref_sub : prefix ⊆+ pushes).
           { rewrite Hk. apply submseteq_inserts_r. reflexivity. }
           (* pushes ⊆+ sub (Hperm) and sub ⊆+ pending_push_of_config (Hsub_in_pset). *)
           assert (Hpushes_sub : pushes ⊆+ sub).
           { rewrite Hperm. reflexivity. }
           etrans; first exact Hpref_sub.
           etrans; first exact Hpushes_sub.
           exact Hsub_in_pset.
      * reflexivity.
Qed.

(* ====================================================================== *)
(* Pop chain LP for Phase 1 Call deq closure_pop maintenance.

   Simpler than the Push case because Pop is deterministic (one config per
   base, no permutation choices). At Phase 1 Call deq for fresh τ as Pop,
   the closure_pop universal closure requires that for each (v_h :: s_t, π_x)
   ∈ M_g (the partial tracker pre-Call), the LP'd-Pop config
   (s_t, <[τ:=LP'd Pop NE v_h]>π_x) is in the post-Call meta-config.

   This lemma states: starting from M_full (with τ fresh), we can:
   (1) Apply mcfg_step_call for τ at Pop (trace [(τ, Call NONEV)]).
   (2) Chain mcfg_step_interm for τ at each (v_h :: s_t, π_x') ∈ M_full
       to add the LP'd-Pop config to M_full'.
*)
Lemma mcfg_steps_chain_lp_pop_all
    (M_full : @meta_config hwq_model)
    (M_g : gset single_config_q)
    (τ : positive) :
  set_to_propset M_g ⊆ M_full →
  set_Forall (λ '(_, π), τ ∉ dom π) M_full →
  ∃ (M_full' : @meta_config hwq_model),
    mcfg_steps M_full M_full' [(τ, Call Pop #())] ∧
    (* For each (v_h :: s_t, π_x) ∈ M_g, the LP'd-Pop config (after Call
       mapping τ at Pop, None, then LP'd to NE v_h) is in M_full'. *)
    (∀ (v_h : val) (s_t : list val) (π_x : gmap positive proc_status),
        (v_h :: s_t, π_x) ∈ M_g →
        (s_t, <[τ:=(Pop, #(),
                     Some (encode_response (NonEmpty v_h)))]>
                (<[τ:=(Pop, #(), None)]>π_x)) ∈ M_full') ∧
    (* The Call-mapped configs (without LP) are also in M_full'. *)
    (∀ x, x ∈ M_g →
        (x.1, <[τ:=(Pop, #(), None)]>x.2) ∈ M_full') ∧
    (* Upper bound: every y ∈ M_full' is either a Call-mapped image of
       something in M_full, or an LP'd-Pop image of (v_h :: s_t, π_x) ∈ M_g. *)
    (∀ y, y ∈ M_full' →
       (∃ z, z ∈ M_full ∧ y = (z.1, <[τ:=(Pop, #(), None)]>z.2))
       ∨ (∃ v_h s_t π_x, (v_h :: s_t, π_x) ∈ M_g ∧
            y = (s_t, <[τ:=(Pop, #(),
                             Some (encode_response (NonEmpty v_h)))]>
                       (<[τ:=(Pop, #(), None)]>π_x)))).
Proof.
  intros Hsub Hτ_fresh.
  (* Step 1: Apply mcfg_step_call for τ at Pop. *)
  set (M_full_after_call :=
         ((λ '(s', π'), (s', <[τ:=(Pop, #(), None)]> π'))
            <$> M_full) : @meta_config hwq_model).
  assert (Hstep_call : mcfg_steps M_full M_full_after_call
                                  [(τ, Call Pop #())]).
  { apply mcfg_steps_singleton.
    apply (mcfg_step_call M_full τ Pop #()).
    - exact Hτ_fresh.
    - reflexivity. }
  (* Helper: every Call-mapped element is in M_full_after_call. *)
  assert (Hcall_in : ∀ x : single_config_q,
             x ∈ M_g →
             (x.1, <[τ:=(Pop, #(), None)]>x.2) ∈ M_full_after_call).
  { intros x Hx_in_g.
    unfold M_full_after_call.
    apply elem_of_PropSet.
    exists x. split; first by destruct x.
    apply Hsub. apply elem_of_set_to_propset. exact Hx_in_g. }
  (* Helper: upper bound on M_full_after_call. *)
  assert (Hcall_upper : ∀ y, y ∈ M_full_after_call →
             ∃ z, z ∈ M_full ∧ y = (z.1, <[τ:=(Pop, #(), None)]>z.2)).
  { intros y Hy. unfold M_full_after_call in Hy.
    apply elem_of_PropSet in Hy as ([s_z π_z] & Heq & Hz_in).
    exists (s_z, π_z). split; first exact Hz_in. simpl. exact Heq. }
  (* Step 2: Induct on M_g to chain LP applications. *)
  cut (∃ (M_full' : @meta_config hwq_model),
          mcfg_steps M_full_after_call M_full' [] ∧
          M_full_after_call ⊆ M_full' ∧
          (∀ (v_h : val) (s_t : list val) (π_x : gmap positive proc_status),
              (v_h :: s_t, π_x) ∈ M_g →
              (s_t, <[τ:=(Pop, #(),
                           Some (encode_response (NonEmpty v_h)))]>
                      (<[τ:=(Pop, #(), None)]>π_x)) ∈ M_full') ∧
          (∀ y, y ∈ M_full' →
             y ∈ M_full_after_call ∨
             (∃ v_h s_t π_x, (v_h :: s_t, π_x) ∈ M_g ∧
                y = (s_t, <[τ:=(Pop, #(),
                                 Some (encode_response (NonEmpty v_h)))]>
                           (<[τ:=(Pop, #(), None)]>π_x))))).
  { intros (M_full' & Hsteps_lp & Hsubset_after & Hwitnesses & Hupper).
    exists M_full'. split_and!.
    - replace [(τ, Call Pop #())]
        with ([(τ, Call Pop #())] ++ ([] : list (positive*trace)))
        by apply app_nil_r.
      eapply mcfg_steps_app; first exact Hstep_call. exact Hsteps_lp.
    - exact Hwitnesses.
    - intros x Hx_in_g.
      apply Hsubset_after. exact (Hcall_in x Hx_in_g).
    - intros y Hy. destruct (Hupper y Hy) as [Hin_call | Hin_lp].
      + left. apply (Hcall_upper y Hin_call).
      + right. exact Hin_lp. }
  (* Now prove the cut: chain LPs over M_g. *)
  clear Hτ_fresh Hsub Hstep_call.
  induction M_g as [|x M_g' Hnotin IH] using set_ind_L.
  - exists M_full_after_call. split_and!.
    + apply mcfg_steps_nil.
    + reflexivity.
    + intros v_h s_t π_x Hin. set_solver.
    + intros y Hy. left. exact Hy.
  - assert (Hcall_in' : ∀ y : single_config_q,
               y ∈ M_g' →
               (y.1, <[τ:=(Pop, #(), None)]>y.2) ∈ M_full_after_call).
    { intros y Hy. apply Hcall_in. set_solver. }
    destruct (IH Hcall_in') as (M_full' & Hsteps & Hsubset & Hwitnesses & Hupper).
    destruct x as [s π].
    destruct s as [|v_h s_t].
    + (* x has empty stack: nothing to LP. *)
      exists M_full'. split_and!; try assumption.
      * intros v_h s_t π_x Hin.
        apply elem_of_union in Hin as [Hin_singleton | Hin_M_g'].
        -- apply elem_of_singleton in Hin_singleton. discriminate.
        -- exact (Hwitnesses v_h s_t π_x Hin_M_g').
      * intros y Hy. destruct (Hupper y Hy) as [Hin_call | (v_h' & s_t' & π_x' & Hin' & ->)].
        -- left. exact Hin_call.
        -- right. exists v_h', s_t', π_x'. split; last reflexivity.
           apply elem_of_union. right. exact Hin'.
    + (* x = (v_h :: s_t, π): LP this Pop. *)
      pose (π_call := <[τ:=(Pop, #(), None)]>π).
      pose (π_lp := <[τ:=(Pop, #(),
                          Some (encode_response (NonEmpty v_h)))]>π_call).
      pose (new_config := (s_t, π_lp) : single_config_q).
      exists ({[new_config]} ∪ M_full').
      assert (Hx_call_in_full' : (v_h :: s_t, π_call) ∈ M_full').
      { apply Hsubset.
        change (v_h :: s_t, π_call)
          with ((v_h :: s_t, π).1, <[τ:=(Pop, #(), None)]>(v_h :: s_t, π).2).
        apply Hcall_in. set_solver. }
      assert (Hπ_call_τ : π_call !! τ = Some (Pop, #(), None)).
      { unfold π_call. apply lookup_insert_eq. }
      split_and!.
      * replace ([] : list (positive * trace)) with
          (([] : list (positive * trace)) ++ ([] : list (positive * trace)))
          by reflexivity.
        eapply mcfg_steps_app; first exact Hsteps.
        apply mcfg_steps_singleton.
        apply (mcfg_step_interm M_full' (v_h :: s_t) π_call τ
                 Pop #() s_t
                 (encode_response (NonEmpty v_h))).
        -- exact Hx_call_in_full'.
        -- exact Hπ_call_τ.
        -- split; reflexivity.
      * intros y Hy. apply elem_of_union. right. by apply Hsubset.
      * intros v_h' s_t' π_x' Hin.
        apply elem_of_union in Hin as [Hin_singleton | Hin_M_g'].
        -- apply elem_of_singleton in Hin_singleton.
           injection Hin_singleton as -> -> ->.
           apply elem_of_union. left. apply elem_of_singleton.
           unfold new_config, π_lp, π_call. reflexivity.
        -- apply elem_of_union. right.
           exact (Hwitnesses v_h' s_t' π_x' Hin_M_g').
      * intros y Hy. apply elem_of_union in Hy as [Hy_new | Hy_M_full'].
        -- apply elem_of_singleton in Hy_new. subst y.
           right. exists v_h, s_t, π. split.
           ++ apply elem_of_union. left. apply elem_of_singleton. reflexivity.
           ++ unfold new_config, π_lp, π_call. reflexivity.
        -- destruct (Hupper y Hy_M_full') as [Hin_call | (v_h'' & s_t'' & π_x'' & Hin'' & ->)].
           ++ left. exact Hin_call.
           ++ right. exists v_h'', s_t'', π_x''. split; last reflexivity.
              apply elem_of_union. right. exact Hin''.
Qed.

(* ====================================================================== *)
(* Pop chain LP for a specific head value v_h (e.g. v_right at Phase 4 LP).

   Unlike [mcfg_steps_chain_lp_pop_all], this lemma does NOT prepend a Call
   step: τ is already at OpDeqPending in π_x. Also it is parameterised by a
   single head value v_h, so we only need to LP configurations whose stack
   begins with v_h AND whose π already has τ at (Pop, None). *)
Lemma mcfg_steps_chain_lp_pop_at_head
    (M_full : @meta_config hwq_model)
    (M_g : gset single_config_q)
    (τ : positive) (v_h : val) :
  set_to_propset M_g ⊆ M_full →
  ∃ (M_full' : @meta_config hwq_model),
    mcfg_steps M_full M_full' [] ∧
    M_full ⊆ M_full' ∧
    (∀ s_t π,
        (v_h :: s_t, π) ∈ M_g →
        π !! τ = Some (Pop, #(), None) →
        (s_t,
         <[τ:=(Pop, #(),
                Some (encode_response (NonEmpty v_h)))]>π) ∈ M_full') ∧
    (∀ y, y ∈ M_full' → y ∈ M_full ∨
       ∃ s_t π, (v_h :: s_t, π) ∈ M_g ∧
                π !! τ = Some (Pop, #(), None) ∧
                y = (s_t,
                     <[τ:=(Pop, #(),
                            Some (encode_response (NonEmpty v_h)))]>π)).
Proof.
  intros Hsub.
  induction M_g as [|x M_g' Hnotin IH] using set_ind_L.
  - exists M_full. split_and!.
    + apply mcfg_steps_nil.
    + reflexivity.
    + intros s_t π Hin. set_solver.
    + intros y Hy. left. exact Hy.
  - assert (Hsub' : (set_to_propset M_g' : @meta_config hwq_model) ⊆ M_full).
    { intros y Hy. apply Hsub. apply elem_of_set_to_propset.
      rewrite elem_of_set_to_propset in Hy. set_solver. }
    destruct (IH Hsub') as (M_full' & Hsteps' & Hsubset' & Hwit' & Hupper').
    destruct x as [s π].
    destruct s as [|w s_t].
    + exists M_full'. split_and!; try assumption.
      * intros s_t π_x Hin Hπτ.
        apply elem_of_union in Hin as [Hin_sing | Hin_g].
        -- apply elem_of_singleton in Hin_sing. discriminate.
        -- exact (Hwit' s_t π_x Hin_g Hπτ).
      * intros y Hy. destruct (Hupper' y Hy) as
          [Hin_full | (s_t' & π' & Hin' & Hπτ' & Heq')].
        -- left. exact Hin_full.
        -- right. exists s_t', π'. split_and!; try assumption.
           apply elem_of_union. right. exact Hin'.
    + destruct (decide (w = v_h)) as [-> | Hne_w].
      * destruct (decide (π !! τ = Some (Pop, #(), None))) as
          [Hπτ_yes | Hπτ_no].
        -- pose (π_lp := <[τ:=(Pop, #(),
                               Some (encode_response (NonEmpty v_h)))]>π).
          pose (new_config := (s_t, π_lp) : single_config_q).
          exists ({[new_config]} ∪ M_full').
          assert (Hx_in_M_full' : (v_h :: s_t, π) ∈ M_full').
          { apply Hsubset'. apply Hsub.
            apply elem_of_set_to_propset. set_solver. }
          split_and!.
          ++ replace ([] : list (positive * trace)) with
               (([] : list (positive * trace)) ++
                ([] : list (positive * trace))) by reflexivity.
            eapply mcfg_steps_app; first exact Hsteps'.
            apply mcfg_steps_singleton.
            apply (mcfg_step_interm M_full' (v_h :: s_t) π τ
                     Pop #() s_t
                     (encode_response (NonEmpty v_h))).
            ** exact Hx_in_M_full'.
            ** exact Hπτ_yes.
            ** split; reflexivity.
          ++ intros y Hy. apply elem_of_union. right.
            by apply Hsubset'.
          ++ intros s_t' π' Hin Hπτ'.
            apply elem_of_union in Hin as [Hin_sing | Hin_g].
            ** apply elem_of_singleton in Hin_sing.
              injection Hin_sing as -> ->.
              apply elem_of_union. left. apply elem_of_singleton.
              unfold new_config, π_lp. reflexivity.
            ** apply elem_of_union. right.
              exact (Hwit' s_t' π' Hin_g Hπτ').
          ++ intros y Hy.
            apply elem_of_union in Hy as [Hy_new | Hy_old].
            ** apply elem_of_singleton in Hy_new. subst y.
              right. exists s_t, π. split_and!.
              { apply elem_of_union. left. apply elem_of_singleton.
                reflexivity. }
              { exact Hπτ_yes. }
              { unfold new_config, π_lp. reflexivity. }
            ** destruct (Hupper' y Hy_old) as
                [Hin_full | (s_t' & π' & Hin' & Hπτ' & ->)].
              { left. exact Hin_full. }
              { right. exists s_t', π'. split_and!.
                - apply elem_of_union. right. exact Hin'.
                - exact Hπτ'.
                - reflexivity. }
        -- exists M_full'. split_and!; try assumption.
          ++ intros s_t' π' Hin Hπτ'.
            apply elem_of_union in Hin as [Hin_sing | Hin_g].
            ** apply elem_of_singleton in Hin_sing.
              injection Hin_sing as -> ->.
              exfalso. apply Hπτ_no. exact Hπτ'.
            ** exact (Hwit' s_t' π' Hin_g Hπτ').
          ++ intros y Hy. destruct (Hupper' y Hy) as
              [Hin_full | (s_t' & π' & Hin' & Hπτ' & Heq')].
            ** left. exact Hin_full.
            ** right. exists s_t', π'. split_and!.
              { apply elem_of_union. right. exact Hin'. }
              { exact Hπτ'. }
              { exact Heq'. }
      * exists M_full'. split_and!; try assumption.
        -- intros s_t' π' Hin Hπτ'.
          apply elem_of_union in Hin as [Hin_sing | Hin_g].
          ++ apply elem_of_singleton in Hin_sing.
            inversion Hin_sing.
            exfalso. by apply Hne_w.
          ++ exact (Hwit' s_t' π' Hin_g Hπτ').
        -- intros y Hy. destruct (Hupper' y Hy) as
            [Hin_full | (s_t' & π' & Hin' & Hπτ' & Heq')].
          ++ left. exact Hin_full.
          ++ right. exists s_t', π'. split_and!; try assumption.
            apply elem_of_union. right. exact Hin'.
Qed.

(* ====================================================================== *)
(* Helper: pending_push_of_config contains (τ, v) iff cfg.2[τ] = Pending Push v. *)
Lemma pending_push_of_config_lookup
    (cfg : single_config_q) (τ : positive) (v : val) :
  cfg.2 !! τ = Some (Push, v, None) →
  (τ, v) ∈ pending_push_of_config cfg.
Proof.
  intros Hπτ.
  unfold pending_push_of_config.
  apply list_elem_of_omap.
  exists (τ, (Push, v, None)). split.
  - apply elem_of_map_to_list. exact Hπτ.
  - simpl. reflexivity.
Qed.

(* Helper: lineraize_pending_push for a singleton list reduces to insert. *)
Lemma lineraize_pending_push_singleton
    (cfg : single_config_q) (τ : positive) (v : val) :
  cfg.2 !! τ = Some (Push, v, None) →
  lineraize_pending_push [(τ, v)] cfg =
  (cfg.1 ++ [v], <[τ:=(Push, v, Some #())]>cfg.2).
Proof.
  intros Hπτ.
  unfold lineraize_pending_push. simpl.
  f_equal.
  apply map_eq. intros τ'.
  rewrite map_lookup_imap.
  destruct (decide (τ' = τ)) as [-> | Hne].
  - rewrite Hπτ /=.
    rewrite bool_decide_eq_true_2; last (apply list_elem_of_singleton; reflexivity).
    rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne; last (intros ?; apply Hne; congruence).
    destruct (cfg.2 !! τ') as [x|] eqn:Hπτ'; rewrite Hπτ' /=; last reflexivity.
    rewrite bool_decide_eq_false_2; first reflexivity.
    intros Hin. apply list_elem_of_singleton in Hin. apply Hne. congruence.
Qed.

(* Single-LP corollary of closure_push (TLA+ big-step), stat-conditioned. *)
Lemma closure_push_single
    (M_g : gset single_config_q) (stat : gmap positive op_status_t)
    (cfg : single_config_q) (τ : positive) (v : val) (i : nat) :
  closure_push M_g stat →
  cfg ∈ M_g →
  cfg.2 !! τ = Some (Push, v, None) →
  (stat !! τ = Some (OpEnqReserved v i) ∨ stat !! τ = Some (OpEnqStored v i)) →
  (cfg.1 ++ [v], <[τ:=(Push, v, Some #())]>cfg.2) ∈ M_g.
Proof.
  intros Hcl Hin Hπτ Hstat.
  rewrite -(lineraize_pending_push_singleton cfg τ v Hπτ).
  apply (Hcl cfg [(τ, v)] Hin).
  - apply NoDup_singleton.
  - intros pv Hpv. apply list_elem_of_singleton in Hpv. subst pv.
    by apply pending_push_of_config_lookup.
  - intros pv Hpv. apply list_elem_of_singleton in Hpv. subst pv.
    simpl. exists v, i. exact Hstat.
Qed.

(* ====================================================================== *)
(* Sortedness helpers: filter of List.seq is strictly increasing.
   Used to discharge the "no internal inversions" obligation in JInvSeq. *)

Lemma seq_StronglySorted (start len : nat) :
  StronglySorted lt (List.seq start len).
Proof.
  revert start.
  induction len as [|len IH]; intros start; simpl.
  - constructor.
  - constructor.
    + apply IH.
    + apply Forall_forall.
      intros x Hx.
      apply list_elem_of_In, List.in_seq in Hx. lia.
Qed.

Lemma StronglySorted_filter
    (P : nat → Prop) `{∀ x, Decision (P x)} (l : list nat) :
  StronglySorted lt l →
  StronglySorted lt (filter P l).
Proof.
  intros HSS.
  induction l as [|a l IH].
  - rewrite filter_nil. constructor.
  - rewrite filter_cons.
    inversion HSS as [|? ? HSS_l HF]; subst.
    case_decide as Hp.
    + constructor; first by apply IH.
      apply Forall_forall.
      rewrite Forall_forall in HF.
      intros x Hx. apply list_elem_of_filter in Hx as [_ Hx].
      by apply HF.
    + by apply IH.
Qed.

Lemma StronglySorted_lookup_lt (l : list nat) (n m k_n k_m : nat) :
  StronglySorted lt l →
  (n < m)%nat →
  l !! n = Some k_n →
  l !! m = Some k_m →
  (k_n < k_m)%nat.
Proof.
  revert n m.
  induction l as [|a l IH]; intros n m HSS Hnm Hn Hm.
  - by destruct n.
  - inversion HSS as [|? ? HSS_l HF]; subst.
    destruct n as [| n']; destruct m as [| m'].
    + lia.
    + simpl in Hn, Hm. injection Hn as <-.
      rewrite Forall_forall in HF.
      apply HF, list_elem_of_lookup_2 with m'. exact Hm.
    + lia.
    + simpl in Hn, Hm.
      eapply IH.
      * exact HSS_l.
      * apply Nat.succ_lt_mono in Hnm. exact Hnm.
      * exact Hn.
      * exact Hm.
Qed.

(* ====================================================================== *)
(* DROPPED-SHORTCUT DEFINITIONS AND DERIVATION LEMMAS

   The following definitions used to be conjuncts in hwq_inv_body but were
   identified as consequences of the remaining clauses (lin_witness_seq,
   slots_consistent, stat_consistent, mcfg_steps + trace_stat_consistent).
   They are kept as definitions and derivation lemmas here so that proof
   sites can locally re-derive them when needed via pose proof. *)

(* items match slots when stored: for each k with slots[k] = Some v AND
   items[k] = SOMEV v (i.e., slot is currently live, not popped), we have
   the value match. This is essentially a STRONGER form of
   slots_consistent's direction-1 — it eliminates the NONEV alternative
   when items[k] is actually SOMEV. *)
Definition items_match_when_stored
    (items : list val) (slots : gmap nat val) : Prop :=
  ∀ k v v_i,
    slots !! k = Some v →
    items !! k = Some (SOMEV v_i) →
    v_i = v.

(* TRIVIAL derivation of items_match_when_stored from slots_consistent. *)
Lemma items_match_when_stored_derive items slots :
  slots_consistent items slots →
  items_match_when_stored items slots.
Proof.
  intros [Hsc_1 _] k v v_i Hslot Hitem.
  destruct (Hsc_1 k v Hslot) as [_ [Hsc | Hsc]].
  - rewrite Hitem in Hsc. injection Hsc as <-. reflexivity.
  - rewrite Hitem in Hsc. discriminate.
Qed.

(* STRONG linearization witness — TLA+-aligned "v at tail" form with
   JInvSeq_for_tail. *)
Definition lin_witness
    (M_g : gset single_config_q)
    (items : list val) (slots : gmap nat val)
    (stat : gmap positive op_status_t)
    (scan_map : gmap positive (nat * nat))
    : Prop :=
  ∀ i v, slots !! i = Some v →
         items !! i = Some (SOMEV v) →
         JInvSeq_for_tail i slots stat scan_map →
    ∃ s π s',
      (s, π) ∈ M_g ∧
      s = s' ++ [v] ∧
      (∀ τ_d v_d i_d, stat !! τ_d = Some (OpEnqDone v_d i_d) →
        π !! τ_d = Some (Push, v_d, Some #())) ∧
      (∀ τ_d v_d, stat !! τ_d = Some (OpDeqLinearized v_d) →
        π !! τ_d = Some (Pop, #(),
                         Some (encode_response (NonEmpty v_d)))) ∧
      (∀ τ_d v_d, stat !! τ_d = Some (OpDeqDone v_d) →
        π !! τ_d = Some (Pop, #(),
                         Some (encode_response (NonEmpty v_d)))) ∧
      (∀ τ_d, stat !! τ_d = Some OpDeqPending →
        π !! τ_d = Some (Pop, #(), None)) ∧
      (∀ τ_e_s v_e_s i_e_s,
         stat !! τ_e_s = Some (OpEnqStored v_e_s i_e_s) →
         i_e_s ≠ i →
         π !! τ_e_s = Some (Push, v_e_s, None) ∨
         π !! τ_e_s = Some (Push, v_e_s, Some #())).

(* lin_witness is the "v-at-tail" specialization of lin_witness_seq:
   apply lin_witness_seq with seq = sorted_others ++ [i].
   JInvSeq is discharged from JInvSeq_for_tail (witnesses for k > i) plus
   sortedness of sorted_others (no internal inversions). *)
Lemma lin_witness_derive M_g items slots stat scan_map :
  slots_consistent items slots →
  lin_witness_seq M_g items slots stat scan_map →
  lin_witness M_g items slots stat scan_map.
Proof.
  intros [Hsc_1 Hsc_2] Hlinw_seq i v Hslot_i Hitem_i Hjinvseq_tail.
  (* Build sorted_rest := indices ≠ i of stored slots. *)
  pose (P := λ k, k ≠ i ∧
                  match items !! k with
                  | Some (InjRV _) => True
                  | _ => False
                  end).
  assert (HPdec : ∀ k, Decision (P k)).
  { intros k. apply and_dec; first apply _.
    destruct (items !! k) as [u|] eqn:Hk; simpl;
      [destruct u; try (right; intros []; done); left; done | right; intros []; done]. }
  pose (sorted_rest := @filter _ _ (@list_filter _) P HPdec (List.seq 0 (length items))).
  pose (seq_l := sorted_rest ++ [i]).
  pose (A := (list_to_set seq_l : gset nat)).

  (* Sortedness of sorted_rest. *)
  assert (HSS_rest : StronglySorted lt sorted_rest).
  { apply StronglySorted_filter, seq_StronglySorted. }

  (* Characterization of membership in sorted_rest. *)
  assert (Hin_rest : ∀ k, k ∈ sorted_rest ↔
            (k ≠ i ∧ (k < length items)%nat ∧
             ∃ v', items !! k = Some (SOMEV v'))).
  { intros k. unfold sorted_rest. rewrite list_elem_of_filter.
    split.
    - intros [[Hne Hmatch] Hkseq].
      apply list_elem_of_In, List.in_seq in Hkseq. split_and!; [done | lia |].
      destruct (items !! k) as [u|] eqn:Hk; try contradiction.
      destruct u; try contradiction. eexists; reflexivity.
    - intros (Hne & Hkbd & v' & Hk). split.
      + split; first done. by rewrite Hk.
      + apply list_elem_of_In, List.in_seq. lia. }

  assert (Hbd_i : (i < length items)%nat).
  { destruct (Hsc_1 i v Hslot_i) as [Hbd _]. exact Hbd. }

  (* GoodEnqSet A items stat. *)
  assert (Hgood : GoodEnqSet A items stat).
  { split.
    - intros k v0 Hitem_k.
      unfold A. rewrite elem_of_list_to_set. unfold seq_l.
      rewrite elem_of_app.
      destruct (decide (k = i)) as [-> | Hne].
      + right. apply list_elem_of_singleton. reflexivity.
      + left. apply Hin_rest. split_and!; [done | | by exists v0].
        apply lookup_lt_Some in Hitem_k. exact Hitem_k.
    - intros k Hin_A. unfold A in Hin_A.
      apply elem_of_list_to_set in Hin_A. unfold seq_l in Hin_A.
      apply elem_of_app in Hin_A as [Hin | Hin].
      + left. apply Hin_rest in Hin as (_ & _ & v' & Hk). by exists v'.
      + left. apply list_elem_of_singleton in Hin as ->. by exists v. }

  (* NoDup seq_l. *)
  assert (Hnodup_rest : NoDup sorted_rest).
  { apply NoDup_filter, NoDup_seq. }
  assert (Hnodup : NoDup seq_l).
  { unfold seq_l. apply NoDup_app. split_and!.
    - exact Hnodup_rest.
    - intros k Hk_in_rest Hin.
      apply elem_of_cons in Hin as [-> | Habs].
      + apply Hin_rest in Hk_in_rest as (Hne & _ & _). by apply Hne.
      + by apply not_elem_of_nil in Habs.
    - apply NoDup_singleton. }

  (* list_to_set seq_l = A. *)
  assert (Hsetof : list_to_set seq_l = A) by reflexivity.

  (* JInvSeq seq_l slots stat scan_map. *)
  assert (Hjinvseq : JInvSeq seq_l slots stat scan_map).
  { intros n m k_n k_m Hnm Hn Hm Hkn_gt Hsome_km.
    (* The last index in seq_l is length sorted_rest; seq_l has length |sorted_rest|+1. *)
    unfold seq_l in Hn, Hm.
    (* Two cases for m: either m < length sorted_rest, or m = length sorted_rest. *)
    destruct (decide (m = length sorted_rest)) as [Heq_m | Hne_m].
    - (* m points to the last cell, so k_m = i. *)
      subst m. rewrite lookup_app_r in Hm; last lia.
      rewrite Nat.sub_diag in Hm. simpl in Hm.
      injection Hm as ->.
      (* n < length sorted_rest, so seq_l !! n = sorted_rest !! n. *)
      rewrite lookup_app_l in Hn; last lia.
      assert (Hkn_in : k_n ∈ sorted_rest).
      { by eapply list_elem_of_lookup_2. }
      apply Hin_rest in Hkn_in as (Hkn_ne & _ & v_n & Hitem_kn).
      assert (Hslot_kn : slots !! k_n = Some v_n).
      { by apply Hsc_2. }
      apply (Hjinvseq_tail k_n Hkn_gt). by exists v_n.
    - (* m < length sorted_rest. *)
      assert (Hm_bd : (m < length sorted_rest)%nat).
      { (* m ≠ length sorted_rest, and m < length sorted_rest + 1, so m < length sorted_rest. *)
        assert (Hm_bd' : (m < length sorted_rest + 1)%nat).
        { apply lookup_lt_Some in Hm. rewrite length_app /= in Hm. lia. }
        lia. }
      assert (Hn_bd : (n < length sorted_rest)%nat) by lia.
      rewrite lookup_app_l in Hn; last lia.
      rewrite lookup_app_l in Hm; last lia.
      assert (Hkn_lt_km : (k_n < k_m)%nat).
      { eapply (StronglySorted_lookup_lt sorted_rest n m); try eassumption. }
      exfalso. lia. }

  destruct (Hlinw_seq A seq_l Hgood Hnodup Hsetof Hjinvseq)
    as (s & π & Hin & Hlen & Hsmatch & Hsmatch_case & Henq & Hlin & Hdone & Hpending & Hstored & _).

  (* Length s = length seq_l. The last element of seq_l is i (at index length sorted_rest).
     By Hsmatch, s !! length sorted_rest = Some v. So s = s' ++ [v]. *)
  assert (Hseq_last : seq_l !! (length sorted_rest) = Some i).
  { unfold seq_l. rewrite lookup_app_r; last lia.
    rewrite Nat.sub_diag. reflexivity. }
  assert (Hs_last : s !! (length sorted_rest) = Some v).
  { eapply Hsmatch; eauto. }
  assert (Hlen_eq : length s = length sorted_rest + 1).
  { rewrite Hlen. unfold seq_l. rewrite length_app. simpl. reflexivity. }

  (* Decompose s = s_front ++ [v]. Use rev_ind: signature (x, l, IH). *)
  destruct s as [|s_back s_front _] using rev_ind;
    first by destruct (length sorted_rest); simpl in Hs_last; discriminate.
  rewrite length_app /= in Hlen_eq.
  assert (Hlen_s_front : length s_front = length sorted_rest) by lia.
  rewrite lookup_app_r in Hs_last; last lia.
  rewrite Hlen_s_front Nat.sub_diag in Hs_last. simpl in Hs_last.
  injection Hs_last as ->.

  exists (s_front ++ [v]), π, s_front. split_and!; try done.
  - intros τ_e_s v_e_s i_e_s Hstat_e Hne.
    right. by apply (Hstored τ_e_s v_e_s i_e_s Hstat_e).
Qed.

(* Init witness: ∃ config in M_g with lin_witness-style clauses.
   The s component is allowed to be non-empty — captures the "residue" of
   pushed-but-not-yet-popped values. *)
Definition init_witness
    (M_g : gset single_config_q)
    (stat : gmap positive op_status_t) : Prop :=
  ∃ (s : list val) (π : gmap positive proc_status),
    (s, π) ∈ M_g ∧
    (∀ τ_d v_d i_d, stat !! τ_d = Some (OpEnqDone v_d i_d) →
      π !! τ_d = Some (Push, v_d, Some #())) ∧
    (∀ τ_d v_d, stat !! τ_d = Some (OpDeqLinearized v_d) →
      π !! τ_d = Some (Pop, #(),
                       Some (encode_response (NonEmpty v_d)))) ∧
    (∀ τ_d v_d, stat !! τ_d = Some (OpDeqDone v_d) →
      π !! τ_d = Some (Pop, #(),
                       Some (encode_response (NonEmpty v_d)))) ∧
    (∀ τ_d, stat !! τ_d = Some OpDeqPending →
      π !! τ_d = Some (Pop, #(), None)) ∧
    (∀ τ_e v_e i_e, stat !! τ_e = Some (OpEnqStored v_e i_e) →
      π !! τ_e = Some (Push, v_e, None) ∨
      π !! τ_e = Some (Push, v_e, Some #())).

(* init_witness from lin_witness_seq: apply lin_witness_seq with A = currently
   stored slots (sorted seq). JInvSeq holds vacuously (no inversions in sorted). *)
Lemma init_witness_derive M_g items slots stat scan_map :
  slots_consistent items slots →
  lin_witness_seq M_g items slots stat scan_map →
  init_witness M_g stat.
Proof.
  intros [Hsc_1 Hsc_2] Hlinw_seq.
  (* Sorted seq of currently-stored slots. *)
  pose (P := λ k, match items !! k with
                  | Some (InjRV _) => True
                  | _ => False
                  end).
  assert (HPdec : ∀ k, Decision (P k)).
  { intros k. unfold P.
    destruct (items !! k) as [u|]; last (right; intros []).
    destruct u; try (right; intros []; done). left; exact I. }
  pose (seq_l := @filter _ _ (@list_filter _) P HPdec (List.seq 0 (length items))).
  pose (A := (list_to_set seq_l : gset nat)).

  assert (HSS : StronglySorted lt seq_l).
  { apply StronglySorted_filter, seq_StronglySorted. }

  assert (Hin_seq : ∀ k, k ∈ seq_l ↔
            ((k < length items)%nat ∧ ∃ v', items !! k = Some (SOMEV v'))).
  { intros k. unfold seq_l. rewrite list_elem_of_filter.
    split.
    - intros [Hmatch Hkseq].
      apply list_elem_of_In, List.in_seq in Hkseq. split; first lia.
      unfold P in Hmatch.
      destruct (items !! k) as [u|] eqn:Hk; try contradiction.
      destruct u; try contradiction. eexists; reflexivity.
    - intros (Hkbd & v' & Hk). split.
      + unfold P. by rewrite Hk.
      + apply list_elem_of_In, List.in_seq. lia. }

  assert (Hgood : GoodEnqSet A items stat).
  { split.
    - intros k v0 Hitem_k.
      unfold A. rewrite elem_of_list_to_set.
      apply Hin_seq. split.
      + apply lookup_lt_Some in Hitem_k. exact Hitem_k.
      + by exists v0.
    - intros k Hin_A. unfold A in Hin_A.
      apply elem_of_list_to_set in Hin_A.
      left. apply Hin_seq in Hin_A as (_ & v' & Hk). by exists v'. }

  assert (Hnodup : NoDup seq_l).
  { apply NoDup_filter, NoDup_seq. }

  assert (Hsetof : list_to_set seq_l = A) by reflexivity.

  assert (Hjinvseq : JInvSeq seq_l slots stat scan_map).
  { intros n m k_n k_m Hnm Hn Hm Hkn_gt _.
    exfalso.
    assert (Hkn_lt_km : (k_n < k_m)%nat).
    { eapply (StronglySorted_lookup_lt seq_l n m); try eassumption. }
    lia. }

  destruct (Hlinw_seq A seq_l Hgood Hnodup Hsetof Hjinvseq)
    as (s & π & Hin & _ & _ & _ & Henq & Hlin & Hdone & Hpending & Hstored & _).
  exists s, π. split_and!; try assumption.
  intros τ_e v_e i_e Hstat_e.
  right. by apply (Hstored τ_e v_e i_e Hstat_e).
Qed.

(* Pop universal witness: a SINGLE config in M_g where every currently-
   OpDeqLinearized or OpDeqDone τ_p has π[τ_p] = Some response. *)
Definition pop_universal_witness
    (M_g : gset single_config_q)
    (stat : gmap positive op_status_t) : Prop :=
  ∃ s π, (s, π) ∈ M_g ∧
    (∀ τ v, stat !! τ = Some (OpDeqLinearized v) →
       π !! τ = Some (Pop, #(), Some (encode_response (NonEmpty v)))) ∧
    (∀ τ v, stat !! τ = Some (OpDeqDone v) →
       π !! τ = Some (Pop, #(), Some (encode_response (NonEmpty v)))).

(* pop_universal_witness from lin_witness_seq + slots_consistent: choose
   A = currently stored slots, seq = sorted. JInvSeq holds (no inversions). *)
Lemma pop_universal_witness_derive M_g items slots stat scan_map :
  slots_consistent items slots →
  lin_witness_seq M_g items slots stat scan_map →
  pop_universal_witness M_g stat.
Proof.
  intros Hsc Hlinw_seq.
  destruct (init_witness_derive M_g items slots stat scan_map Hsc Hlinw_seq)
    as (s & π & Hin & _ & Hlin & Hdone & _ & _).
  exists s, π. split_and!; assumption.
Qed.

(* For any currently-stored slot (j, v) AND any popper τ_p at OpDeqPending
   whose scan cursor j_p has progressed AT LEAST to slot j (i.e., j ≤ j_p)
   AND whose scan bound l strictly exceeds j (j < l), there exists a config
   in M_g with v at the HEAD of the queue state AND τ_p at (Pop, None) in π.
   This corresponds to TLA+ D3 SOMEV semantics: at the LP we have just loaded
   arr[j] and not yet incremented j (so j_p = j), but the bound has been set
   to l = range_z at the read of back. *)
Definition pop_universal_v_at_head
    (M_g : gset single_config_q)
    (items : list val) (slots : gmap nat val)
    (stat : gmap positive op_status_t)
    (scan_map : gmap positive (nat * nat)) : Prop :=
  ∀ j v τ_p l j_p,
    slots !! j = Some v →
    items !! j = Some (SOMEV v) →
    stat !! τ_p = Some OpDeqPending →
    scan_map !! τ_p = Some (l, j_p) →
    (j ≤ j_p)%nat →
    (j < l)%nat →
    ∃ s_rest π,
      (v :: s_rest, π) ∈ M_g ∧
      π !! τ_p = Some (Pop, #(), None) ∧
      (∀ τ_d v_d i_d, stat !! τ_d = Some (OpEnqDone v_d i_d) →
         π !! τ_d = Some (Push, v_d, Some #())) ∧
      (∀ τ_d v_d, stat !! τ_d = Some (OpDeqLinearized v_d) →
         π !! τ_d = Some (Pop, #(),
                          Some (encode_response (NonEmpty v_d)))) ∧
      (∀ τ_d v_d, stat !! τ_d = Some (OpDeqDone v_d) →
         π !! τ_d = Some (Pop, #(),
                          Some (encode_response (NonEmpty v_d)))) ∧
      (∀ τ_d, stat !! τ_d = Some OpDeqPending →
         π !! τ_d = Some (Pop, #(), None)) ∧
      (∀ τ_e v_e i_e, stat !! τ_e = Some (OpEnqStored v_e i_e) →
         i_e ≠ j →
         π !! τ_e = Some (Push, v_e, None) ∨
         π !! τ_e = Some (Push, v_e, Some #())).

(* pop_universal_v_at_head from lin_witness_seq: apply with seq = j :: sorted_rest,
   where sorted_rest includes ALL stored slots ≠ j (sorted in increasing order).
   JInvSeq inversions: (0, m, j, k_m) with j > k_m uses τ_p as witness;
   to obtain k_n=j < l, we use the local scan-progress fact j_p ≤ l (passed at
   call site). (n>0, m, _, _) handled by sortedness of sorted_rest. *)
Lemma pop_universal_v_at_head_derive M_g items slots stat scan_map :
  slots_consistent items slots →
  lin_witness_seq M_g items slots stat scan_map →
  pop_universal_v_at_head M_g items slots stat scan_map.
Proof.
  intros [Hsc_1 Hsc_2] Hlinw_seq j v τ_p l j_p Hslot_j Hitem_j Hstat_τp Hscan_τp Hj_le_jp Hj_lt_l.
  (* Sorted seq of stored slots ≠ j (all stored except j). *)
  pose (P := λ k, k ≠ j ∧
                  match items !! k with
                  | Some (InjRV _) => True
                  | _ => False
                  end).
  assert (HPdec : ∀ k, Decision (P k)).
  { intros k. apply and_dec; first apply _.
    destruct (items !! k) as [u|]; last (right; intros []).
    destruct u; try (right; intros []; done). left; exact I. }
  pose (sorted_rest := @filter _ _ (@list_filter _) P HPdec
                                (List.seq 0 (length items))).
  pose (seq_l := j :: sorted_rest).
  pose (A := (list_to_set seq_l : gset nat)).

  assert (HSS_rest : StronglySorted lt sorted_rest).
  { apply StronglySorted_filter, seq_StronglySorted. }

  assert (Hin_rest : ∀ k, k ∈ sorted_rest ↔
            (k ≠ j ∧ (k < length items)%nat ∧
             ∃ v', items !! k = Some (SOMEV v'))).
  { intros k. unfold sorted_rest. rewrite list_elem_of_filter.
    split.
    - intros [[Hne_kj Hmatch] Hkseq].
      apply list_elem_of_In, List.in_seq in Hkseq. split_and!; [done | lia |].
      destruct (items !! k) as [u|] eqn:Hk; try contradiction.
      destruct u; try contradiction. eexists; reflexivity.
    - intros (Hne_kj & Hkbd & v' & Hk). split.
      + split; first done. by rewrite Hk.
      + apply list_elem_of_In, List.in_seq. lia. }

  assert (Hbd_j : (j < length items)%nat).
  { destruct (Hsc_1 j v Hslot_j) as [Hbd _]. exact Hbd. }

  (* GoodEnqSet A items stat. *)
  assert (Hgood : GoodEnqSet A items stat).
  { split.
    - intros k v0 Hitem_k.
      unfold A. rewrite elem_of_list_to_set.
      unfold seq_l. apply elem_of_cons.
      destruct (decide (k = j)) as [-> | Hne].
      + left. reflexivity.
      + right. apply Hin_rest. split_and!;
          [done | by apply lookup_lt_Some in Hitem_k | by exists v0].
    - intros k Hin_A. unfold A in Hin_A.
      apply elem_of_list_to_set in Hin_A. unfold seq_l in Hin_A.
      apply elem_of_cons in Hin_A as [-> | Hin].
      + left. by exists v.
      + left. apply Hin_rest in Hin as (_ & _ & v' & Hk). by exists v'. }

  (* NoDup seq_l. *)
  assert (Hnodup_rest : NoDup sorted_rest).
  { apply NoDup_filter, NoDup_seq. }
  assert (Hnodup : NoDup seq_l).
  { unfold seq_l. apply NoDup_cons. split.
    - intros Hj_in. apply Hin_rest in Hj_in as (Hne & _). by apply Hne.
    - exact Hnodup_rest. }

  (* list_to_set seq_l = A. *)
  assert (Hsetof : list_to_set seq_l = A) by reflexivity.

  (* JInvSeq seq_l slots stat scan_map. *)
  assert (Hjinvseq : JInvSeq seq_l slots stat scan_map).
  { intros n m k_n k_m Hnm Hn Hm Hkn_gt Hsome_km.
    unfold seq_l in Hn, Hm.
    destruct n as [| n'].
    - (* n = 0: seq_l[0] = j, so k_n = j. *)
      simpl in Hn. injection Hn as ->.
      destruct m as [| m']; first lia.
      simpl in Hm.
      (* k_m ∈ sorted_rest by Hm. *)
      assert (Hkm_in : k_m ∈ sorted_rest).
      { by eapply list_elem_of_lookup_2. }
      apply Hin_rest in Hkm_in as (Hne_km & _ & _ & _).
      (* Witness: τ_p with l, j_p. Need k_n < l = j < l (from premise), and
         k_m < j_p: k_m < j (from k_n > k_m) ≤ j_p (premise). *)
      exists τ_p, l, j_p. split_and!.
      + exact Hstat_τp.
      + exact Hscan_τp.
      + (* j < l: direct from premise. *) exact Hj_lt_l.
      + (* k_m < j_p. k_m < j (= k_n) ≤ j_p. *) lia.
    - (* n > 0: both seq[n] and seq[m] in sorted_rest. *)
      destruct m as [| m']; first lia.
      simpl in Hn, Hm.
      assert (Hkn_lt_km : (k_n < k_m)%nat).
      { eapply (StronglySorted_lookup_lt sorted_rest n' m'); try eassumption.
        apply Nat.succ_lt_mono in Hnm. exact Hnm. }
      exfalso. lia. }

  destruct (Hlinw_seq A seq_l Hgood Hnodup Hsetof Hjinvseq)
    as (s & π & Hin & Hlen & Hsmatch & _ & Henq & Hlin & Hdone & Hpending & Hstored & _).

  (* seq[0] = j; by Hsmatch, s !! 0 = Some v. *)
  assert (Hs_first : s !! 0 = Some v).
  { eapply Hsmatch.
    - reflexivity.
    - exact Hslot_j. }

  destruct s as [| v_h s_rest].
  { simpl in Hs_first. discriminate. }
  simpl in Hs_first. injection Hs_first as ->.

  exists s_rest, π. split_and!; try assumption.
  - apply Hpending, Hstat_τp.
  - intros τ_e v_e i_e Hstat_e Hne.
    right. by apply (Hstored τ_e v_e i_e Hstat_e).
Qed.

(* M_full freshness for OpEnqPending: for τ at OpEnqPending, the
   meta-config M_full has τ at Pending Push v in EVERY config.
   (OpEnqReserved now disjunctive per TLA+ CFTypeOK, no longer ∀-Pending.) *)
Definition stat_M_full_pending
    (stat : gmap positive op_status_t)
    (M_full : @meta_config hwq_model) : Prop :=
  ∀ τ v,
    stat !! τ = Some (OpEnqPending v) →
    ∀ s π, (s, π) ∈ M_full →
      π !! τ = Some (Push, v, None).

(* With hwq_inv_body folding M_full := set_to_propset M_g,
   `stat_M_full_pending` follows directly from `stat_consistent`. *)
Lemma stat_M_full_pending_from_consistent_propset
    M_g stat ts :
  stat_consistent stat M_g ts →
  stat_M_full_pending stat (set_to_propset M_g).
Proof.
  intros Hsc τ v Hstat s π Hin_full.
  apply elem_of_set_to_propset in Hin_full.
  pose proof (Hsc τ) as Hsc_τ. rewrite Hstat in Hsc_τ.
  apply (Hsc_τ s π Hin_full).
Qed.

(* ====================================================================== *)
(* Structural widening lemmas for lin_witness_seq under scan_map updates  *)
(* ====================================================================== *)

(* Lemma 1: When τ's scan_map has j_p = 0, widening l doesn't admit new
   inversions for τ (since k_m < 0 is impossible for nat). So
   lin_witness_seq is preserved trivially.

   Useful for DEQ_P2_OUTER_LIN_SEQ: scan_map[τ] := (range_z, 0) from (0, 0). *)
Lemma lin_witness_seq_widen_l_at_zero
    (M_g : gset single_config_q) items slots stat scan_map τ l_old l_new :
  scan_map !! τ = Some (l_old, 0%nat) →
  lin_witness_seq M_g items slots stat scan_map →
  lin_witness_seq M_g items slots stat (<[τ:=(l_new, 0%nat)]> scan_map).
Proof.
  intros Hscan_τ Hlinw_seq A seq HgoodA HnodupSeq Hsetof HJInvSeq.
  assert (HJInvSeq_old : JInvSeq seq slots stat scan_map).
  { intros n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km.
    destruct (HJInvSeq n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km)
      as (τ_d & l & j_d & Hstat_d & Hscan_d & Hkl & Hkj).
    destruct (decide (τ_d = τ)) as [-> | Hne_τd].
    - rewrite lookup_insert_eq in Hscan_d.
      injection Hscan_d as _ <-.
      inversion Hkj.
    - exists τ_d, l, j_d. split_and!; try assumption.
      rewrite lookup_insert_ne in Hscan_d;
        last (intros ?; apply Hne_τd; congruence).
      exact Hscan_d. }
  apply (Hlinw_seq A seq HgoodA HnodupSeq Hsetof HJInvSeq_old).
Qed.

(* Lemma 2: When the slot just scanned (j_p_old) has items = NONEV, no new
   seqs are admitted by widening j_p_old → Nat.succ j_p_old (since seqs with
   k_m = j_p_old in A would require items[j_p_old] = SOMEV by GoodEnqSet).
   So lin_witness_seq is preserved.

   Useful for the NONEV branch of DEQ_P3_INNER_LIN_SEQ. *)
Lemma lin_witness_seq_widen_τ_scan_nonev
    (M_g : gset single_config_q) items slots stat scan_map back_val τ l j_p_old :
  scan_map !! τ = Some (l, j_p_old) →
  items !! j_p_old = Some NONEV →
  slots_stat_iff stat slots back_val →
  lin_witness_seq M_g items slots stat scan_map →
  lin_witness_seq M_g items slots stat (<[τ:=(l, Nat.succ j_p_old)]> scan_map).
Proof.
  intros Hscan_τ Hitem_jp Hssi Hlinw_seq A seq HgoodA HnodupSeq Hsetof HJInvSeq.
  assert (HJInvSeq_old : JInvSeq seq slots stat scan_map).
  { intros n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km.
    destruct (HJInvSeq n m k_n k_m Hn_lt_m Hseq_n Hseq_m Hkn_gt_km Hsome_km)
      as (τ_d & l' & j_d & Hstat_d & Hscan_d & Hkl & Hkj).
    destruct (decide (τ_d = τ)) as [-> | Hne_τd].
    - rewrite lookup_insert_eq in Hscan_d.
      injection Hscan_d as <- <-.
      destruct (decide (k_m < j_p_old)%nat) as [Hlt | Hge].
      + exists τ, l, j_p_old. split_and!; try assumption.
      + unfold Nat.succ in Hkj.
        assert (k_m = j_p_old) as -> by lia.
        exfalso.
        destruct HgoodA as [_ Hgood_to].
        assert (j_p_old ∈ A) as Hjp_in_A.
        { rewrite <- Hsetof. apply elem_of_list_to_set. apply list_elem_of_lookup_2 with m. exact Hseq_m. }
        destruct (Hgood_to j_p_old Hjp_in_A) as [(v & Hitems_v) | (τ_e & v_e & Hres)].
        * rewrite Hitem_jp in Hitems_v. discriminate.
        * (* OpEnqReserved τ_e at j_p_old means slot j_p_old has been FAA'd but
             not yet stored. By slots_stat_iff's FAA-uniqueness, τ_e is the
             UNIQUE process with stat_faad at j_p_old. Now Hsome_km says
             ∃ v_some, slots[j_p_old] = Some v_some. By slots_stat_iff's
             direction 1 (slot → stat_owns), ∃ τ_other at Stored/Done with
             slots[j_p_old] = Some v at j_p_old. By FAA-uniqueness applied to
             τ_e (Reserved) and τ_other (Stored/Done), τ_e = τ_other. But
             OpEnqReserved ≠ OpEnqStored/Done. Contradiction. *)
          destruct Hsome_km as (v_some & Hslot_some).
          destruct Hssi as (_ & Hssi_b & Hssi_c & _).
          destruct (Hssi_b j_p_old v_some Hslot_some) as (τ_other & Hstat_other).
          (* Hstat_other : stat_owns stat τ_other v_some j_p_old, i.e.,
             τ_other at OpEnqStored or OpEnqDone with v_some at j_p_old. *)
          assert (Hτ_eq : τ_e = τ_other).
          { eapply Hssi_c.
            - left. exact Hres.  (* τ_e at OpEnqReserved *)
            - destruct Hstat_other as [Hown | Hown].
              + right. left. exact Hown.   (* τ_other at OpEnqStored *)
              + right. right. exact Hown. (* τ_other at OpEnqDone *) }
          subst τ_other.
          destruct Hstat_other as [Hown | Hown];
            rewrite Hres in Hown; discriminate.
    - exists τ_d, l', j_d. split_and!; try assumption.
      rewrite lookup_insert_ne in Hscan_d;
        last (intros ?; apply Hne_τd; congruence).
      exact Hscan_d. }
  apply (Hlinw_seq A seq HgoodA HnodupSeq Hsetof HJInvSeq_old).
Qed.
