(* adequacy.v *)
(* Non-standard variants of adequate. *)

From iris.program_logic Require Export adequacy.
From iris_logatom.pure_logic Require Import steps.

Section adequate_tp.
  Context {Λ : language}.
  Implicit Types (e : expr Λ) (t : list (expr Λ)) (σ : state Λ).
  Implicit Types (κ κs : list (observation Λ)).

  Record adequate_tp s t1 σ1 (φ : val Λ → state Λ → Prop) := {
    adequate_tp_length : length t1 ≠ 0;
    adequate_tp_result t2 σ2 v2 :
      rtc erased_step (t1, σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
    adequate_tp_not_stuck t2 σ2 e2 :
      s = NotStuck →
      rtc erased_step (t1, σ1) (t2, σ2) →
      e2 ∈ t2 → not_stuck e2 σ2
  }.

  Lemma adequate_tp_adequate s e1 σ1 φ :
    adequate_tp s [e1] σ1 φ ↔ adequate s e1 σ1 φ.
  Proof. by split; intros [??]; split. Qed.

  Lemma adequate_tp_app_l s t1 t2 σ Q :
    t1 ≠ [] → adequate_tp s (t1++t2) σ Q → adequate_tp s t1 σ Q.
  Proof.
    intros Ht1_not_nil [_ Hresult Hnot_stuck].
    split.
    - by destruct t1.
    - intros t3 σ3 v3 Hsteps.
      destruct t1 as [|e1 t1]; first done.
      assert (∃ t3a t3b, t3 = t3a++t3b ∧ length t1 = length t3a) as
        (t3a & t3b & -> & Hlent3a).
      { exists (take (length t1) t3), (drop (length t1) t3).
        split.
        - rewrite take_drop //.
        - pose proof (erased_steps_grow _ _ _ _ Hsteps) as Hlen.
          simpl in Hlen. rewrite length_take. lia. }
      apply (Hresult (t3a++t2++t3b)).
      replace (of_val v3 :: t3a ++ t2 ++ t3b) with ((of_val v3 :: t3a) ++ t2 ++ t3b) by rewrite !app_comm_cons //.
      apply erased_steps_app_r.
      + rewrite !length_cons. lia.
      + rewrite -!app_comm_cons //.
    - intros t3 σ3 e3 -> Hsteps Hint3.
      assert (∃ t3a t3b, t3 = t3a++t3b ∧ length t1 = length t3a) as
        (t3a & t3b & -> & Hlent3a).
      { exists (take (length t1) t3), (drop (length t1) t3).
        split.
        - rewrite take_drop //.
        - pose proof (erased_steps_grow _ _ _ _ Hsteps) as Hlen.
          simpl in Hlen. rewrite length_take. lia. }
      eapply Hnot_stuck; first reflexivity.
      + eapply erased_steps_app_r; [exact Hlent3a|exact Hsteps].
      + set_solver.
  Qed.

  Lemma adequate_tp_erased_step t1 σ1 t2 σ2 s Q :
    erased_step (t1,σ1) (t2,σ2) →
    adequate_tp s t1 σ1 Q →
    adequate_tp s t2 σ2 Q.
  Proof.
    intros Hstep [Hlen Hresult Hnot_stuck].
    split.
    - apply erased_step_grow in Hstep. lia.
    - intros t3 σ3 v3 Hsteps.
      eapply Hresult.
      eapply rtc_l; eassumption.
    - intros t3 σ3 e_t3 -> Hsteps.
      eapply Hnot_stuck; first reflexivity.
      eapply rtc_l; first exact Hstep.
      exact Hsteps.
  Qed.
End adequate_tp.

Section adequate.
  Context {Λ : language}.
  Implicit Types (e : expr Λ) (t : list (expr Λ)) (σ : state Λ).
  Implicit Types (κ κs : list (observation Λ)).
  Lemma adequate_erased_step e1 σ1 e2 σ2 efs s Q :
    erased_step ([e1],σ1) (e2::efs,σ2) →
    adequate s e1 σ1 Q →
    adequate s e2 σ2 Q.
  Proof.
    intros Hstep.
    rewrite -!adequate_tp_adequate.
    intros Hadq.
    eapply adequate_tp_app_l; first done.
    eapply adequate_tp_erased_step; [exact Hstep|exact Hadq].
  Qed.

  Lemma adequate_prim_step e1 σ1 κ e2 σ2 efs s Q :
    prim_step e1 σ1 κ e2 σ2 efs →
    adequate s e1 σ1 Q →
    adequate s e2 σ2 Q.
  Proof.
    intros Hprim_step. eapply adequate_erased_step.
    exists κ.
    by apply (step_atomic e1 σ1 e2 σ2 efs [] []).
  Qed.

  (** Strengthening: an [adequate] postcondition can be enriched with a
    witnessing trace showing how the value was reached from [([e], σ0)]. *)
  Lemma adequate_strengthen_reach s e σ0 (φ : val Λ → state Λ → Prop) :
    adequate s e σ0 φ →
    adequate s e σ0
      (λ v σ, φ v σ ∧ ∃ efs, rtc erased_step ([e], σ0) (of_val v :: efs, σ)).
  Proof.
    intros [Hresult Hnot_stuck]. split.
    - intros t2 σ2 v2 Hrtc. split.
      + by eapply Hresult.
      + by exists t2.
    - intros t2 σ2 e2. by apply Hnot_stuck.
  Qed.

  (** Weakening: if [φ] pointwise implies [φ'], then [adequate s e σ φ]
    entails [adequate s e σ φ']. *)
  Lemma adequate_weaken s e σ (φ φ' : val Λ → state Λ → Prop) :
    (∀ v σ', φ v σ' → φ' v σ') →
    adequate s e σ φ →
    adequate s e σ φ'.
  Proof.
    intros Himpl [Hresult Hnot_stuck]. split.
    - intros t2 σ2 v2 Hrtc. apply Himpl. by eapply Hresult.
    - intros t2 σ2 e2. by apply Hnot_stuck.
  Qed.
End adequate.

Section nofork.
  Context {Λ : language}.
  Implicit Types (e : expr Λ) (t : list (expr Λ)) (σ : state Λ).
  Implicit Types (κ κs : list (observation Λ)).

  Definition sequential e1 σ1 :=
    ∀ t2 σ2, rtc erased_step ([e1], σ1) (t2, σ2) → length t2 = 1.

  Lemma sequential_erased_step e1 σ1 e2 σ2 :
    erased_step ([e1],σ1) ([e2],σ2) →
    sequential e1 σ1 →
    sequential e2 σ2.
  Proof.
    intros Hstep Hnofork t3 σ3 Hsteps.
    eapply Hnofork.
    by eapply rtc_l.
  Qed.

  Lemma sequential_prim_step e1 σ1 κ e2 σ2 :
    prim_step e1 σ1 κ e2 σ2 [] →
    sequential e1 σ1 →
    sequential e2 σ2.
  Proof.
    intros Hprim_step. eapply sequential_erased_step.
    exists κ.
    by apply (step_atomic e1 σ1 e2 σ2 [] [] []).
  Qed.

  Lemma sequential_prim_step_nofork e1 σ1 κ e2 σ2 efs :
    sequential e1 σ1 → prim_step e1 σ1 κ e2 σ2 efs →
    efs = [].
  Proof.
    intros Hseq Hprim.
    opose proof (Hseq (e2::efs) σ2 _) as Hlen.
    - apply rtc_once.
      exists κ.
      by apply (step_atomic e1 σ1 e2 σ2 efs [] []).
    - simpl in Hlen.
      apply nil_length_inv.
      lia.
  Qed.
End nofork.
