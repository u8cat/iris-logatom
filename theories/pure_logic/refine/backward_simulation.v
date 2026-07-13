(* backward_simulation.v: backward simulations as a proof technique for
  trace refinement between labeled transition systems, based on
  Definition 6 of Bouajjani et al. [2017] (arXiv:1702.02705) and the
  classical presentation of Lynch-Vaandrager. *)

From stdpp Require Import base list.

(* ========================================== *)
(* Labeled transition systems *)

(** The reflexive-transitive closure of a labeled step relation. [AbsQ]
  and [AbsQ0] in [absq.v] each define their own copy of this relation
  specialized to their state and label types; the form below is generic. *)
Inductive lts_steps {Q L : Type} (step : Q → L → Q → Prop)
  : Q → list L → Q → Prop :=
  | lts_steps_nil s :
    lts_steps step s [] s
  | lts_steps_cons s0 s1 s2 l ls :
    step s0 l s1 →
    lts_steps step s1 ls s2 →
    lts_steps step s0 (l :: ls) s2.

Lemma lts_steps_app {Q L : Type} (step : Q → L → Q → Prop) s0 s1 s2 ls1 ls2 :
  lts_steps step s0 ls1 s1 →
  lts_steps step s1 ls2 s2 →
  lts_steps step s0 (ls1 ++ ls2) s2.
Proof.
  intros Hsteps1.
  induction Hsteps1 as [|??????? IH]; intros Hsteps2; first done.
  simpl. eapply lts_steps_cons; first eassumption. by apply IH.
Qed.

(** Inverse of [lts_steps_app]: an [lts_steps] over a concatenated
  label list splits into a prefix run and a suffix run with an
  intermediate state. *)
Lemma lts_steps_app_inv {Q L : Type} (step : Q → L → Q → Prop) s0 s2 ls1 ls2 :
  lts_steps step s0 (ls1 ++ ls2) s2 →
  ∃ s1, lts_steps step s0 ls1 s1 ∧ lts_steps step s1 ls2 s2.
Proof.
  revert s0. induction ls1 as [|l ls1' IH]; intros s0 Hsteps.
  - exists s0. split; [apply lts_steps_nil|exact Hsteps].
  - simpl in Hsteps. inversion Hsteps as [|? s_mid ? ? ? Hstep1 Hsteps_rest]; subst.
    destruct (IH s_mid Hsteps_rest) as (s1 & Hpre & Hpost).
    exists s1. split; [|exact Hpost].
    eapply lts_steps_cons; eassumption.
Qed.

(* ========================================== *)
(* Γ-refinement *)

Section refinement.
  Context {Q1 Q2 L : Type}.
  Context (init1 : Q1) (step1 : Q1 → L → Q1 → Prop).
  Context (init2 : Q2) (step2 : Q2 → L → Q2 → Prop).
  (** A decidable predicate picking out the observable labels. *)
  Context (Γ : L → Prop) `{!∀ l, Decision (Γ l)}.

  (** The Γ-projection of a label sequence: keep only the observable
    labels. *)
  Definition project_labels : list L → list L := filter Γ.

  Lemma project_labels_nil : project_labels [] = [].
  Proof. done. Qed.

  Lemma project_labels_cons l ls :
    project_labels (l :: ls) =
      (if decide (Γ l) then [l] else []) ++ project_labels ls.
  Proof. unfold project_labels. rewrite filter_cons. by case_decide. Qed.

  Lemma project_labels_app ls1 ls2 :
    project_labels (ls1 ++ ls2) = project_labels ls1 ++ project_labels ls2.
  Proof. apply filter_app. Qed.

  (** Γ-refinement of [L1] by [L2]: every trace of [L1] is matched, up to
    Γ-projection, by some trace of [L2]. *)
  Definition Γ_refines : Prop :=
    ∀ ls s, lts_steps step1 init1 ls s →
    ∃ ls' u, lts_steps step2 init2 ls' u ∧
             project_labels ls = project_labels ls'.

  (** A Γ-backward simulation from [L1] to [L2]. This formulation is
    equivalent to the "normal" Γ-backward simulation of Definition 6 of
    the paper: the four separate conditions (ii-a)–(ii-d) there, which
    treat call, return, observable non-call-return, and non-observable
    actions with positional constraints on where the observable label
    appears in the matching [L2] sequence, all imply the single
    Γ-projection-equality condition [bs_step] below. *)
  Record backward_simulation (bs : Q1 → Q2 → Prop) : Prop := {
    (** (i) [bs[init1] = {init2}]. *)
    bs_init_fwd : bs init1 init2;
    bs_init_only : ∀ u, bs init1 u → u = init2;
    (** [bs] is total on [L1]-reachable states. *)
    bs_total : ∀ s ls,
      lts_steps step1 init1 ls s → ∃ u, bs s u;
    (** Every step of [L1] is matched backwards by an [L2] sequence with
      the same Γ-projection. *)
    bs_step : ∀ s l s' u',
      step1 s l s' → bs s' u' →
      ∃ u ls, bs s u ∧ lts_steps step2 u ls u' ∧
              project_labels [l] = project_labels ls;
  }.

  Lemma backward_simulation_backward_steps bs :
    backward_simulation bs →
    ∀ s s_end ls, lts_steps step1 s ls s_end →
    ∀ u_end, bs s_end u_end →
    ∃ u ls', bs s u ∧ lts_steps step2 u ls' u_end ∧
             project_labels ls = project_labels ls'.
  Proof.
    intros Hbs s s_end ls Hsteps1.
    induction Hsteps1 as [s0 | s0 s1 s2 l ls_mid Hstep1 _ IH];
      intros u_end Hbs_end.
    - exists u_end, []. split_and!; [done|constructor|done].
    - destruct (IH u_end Hbs_end)
        as (u_mid & lp & Hbs_mid & Hsteps_mid & Hproj).
      destruct (bs_step _ Hbs _ _ _ _ Hstep1 Hbs_mid)
        as (u & lq & Hbs_u & Hsteps_q & Hproj_q).
      exists u, (lq ++ lp). split_and!.
      + done.
      + by eapply lts_steps_app.
      + change (l :: ls_mid) with ([l] ++ ls_mid).
        rewrite !project_labels_app.
        rewrite Hproj_q. rewrite Hproj. done.
  Qed.

  Theorem backward_simulation_refines bs :
    backward_simulation bs → Γ_refines.
  Proof.
    intros Hbs ls s Hsteps1.
    destruct (bs_total _ Hbs _ _ Hsteps1) as [u Hbs_end].
    destruct (backward_simulation_backward_steps bs Hbs init1 s ls Hsteps1 u Hbs_end)
      as (u0 & ls' & Hbs_init & Hsteps2 & Hproj).
    apply (bs_init_only _ Hbs) in Hbs_init as ->.
    by exists ls', u.
  Qed.

  (** A variant that lets [bs_step] assume a forward [L1]-invariant [P]
    on the pre-state. Since [P] holds at [init1] and is preserved by
    every [L1]-step, every pre-state in the forward chain
    [init1 →* s_end] that drives the backward induction satisfies [P],
    so no precondition leaks into [Γ_refines]. *)
  Record backward_simulation_with_inv
    (bs : Q1 → Q2 → Prop) (P : Q1 → Prop) : Prop := {
    bsi_init_fwd : bs init1 init2;
    bsi_init_only : ∀ u, bs init1 u → u = init2;
    bsi_inv_init : P init1;
    bsi_inv_step : ∀ s l s', step1 s l s' → P s → P s';
    bsi_total : ∀ s ls,
      lts_steps step1 init1 ls s → ∃ u, bs s u;
    bsi_step : ∀ s l s' u',
      P s → step1 s l s' → bs s' u' →
      ∃ u ls, bs s u ∧ lts_steps step2 u ls u' ∧
              project_labels [l] = project_labels ls;
  }.

  Lemma backward_simulation_with_inv_backward_steps bs P :
    backward_simulation_with_inv bs P →
    ∀ s s_end ls, lts_steps step1 s ls s_end →
    P s →
    ∀ u_end, bs s_end u_end →
    ∃ u ls', bs s u ∧ lts_steps step2 u ls' u_end ∧
             project_labels ls = project_labels ls'.
  Proof.
    intros Hbs s s_end ls Hsteps1.
    induction Hsteps1 as [s0 | s0 s1 s2 l ls_mid Hstep1 _ IH];
      intros HP u_end Hbs_end.
    - exists u_end, []. split_and!; [done|constructor|done].
    - assert (P s1) as HP1 by (by eapply (bsi_inv_step _ _ Hbs)).
      destruct (IH HP1 u_end Hbs_end)
        as (u_mid & lp & Hbs_mid & Hsteps_mid & Hproj).
      destruct (bsi_step _ _ Hbs _ _ _ _ HP Hstep1 Hbs_mid)
        as (u & lq & Hbs_u & Hsteps_q & Hproj_q).
      exists u, (lq ++ lp). split_and!.
      + done.
      + by eapply lts_steps_app.
      + change (l :: ls_mid) with ([l] ++ ls_mid).
        rewrite !project_labels_app.
        rewrite Hproj_q. rewrite Hproj. done.
  Qed.

  Theorem backward_simulation_with_inv_refines bs P :
    backward_simulation_with_inv bs P → Γ_refines.
  Proof.
    intros Hbs ls s Hsteps1.
    destruct (bsi_total _ _ Hbs _ _ Hsteps1) as [u Hbs_end].
    destruct (backward_simulation_with_inv_backward_steps bs P Hbs
                init1 s ls Hsteps1 (bsi_inv_init _ _ Hbs) u Hbs_end)
      as (u0 & ls' & Hbs_init & Hsteps2 & Hproj).
    apply (bsi_init_only _ _ Hbs) in Hbs_init as ->.
    by exists ls', u.
  Qed.
End refinement.
