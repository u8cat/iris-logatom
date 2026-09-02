From iris_logatom.lib Require Import relation.
From iris.program_logic Require Export ectx_language language.

(* TODO:rename "erased_steps" to "rtc_erased_step"
        rename "cfg" to "ρ"*)
Section steps_lang.
  Context {Λ : language}.
  Implicit Types (e : expr Λ) (t : list (expr Λ)) (σ : state Λ).
  Implicit Types (κ κs : list (observation Λ)).

  Lemma erased_step_grow t1 σ1 t2 σ2 :
    erased_step (t1,σ1) (t2,σ2) → length t1 ≤ length t2.
  Proof.
    intros [κ Hstep].
    destruct Hstep. simplify_eq.
    rewrite !length_app !length_cons length_app.
    lia.
  Qed.

  Lemma erased_steps_grow t1 σ1 t2 σ2 :
    rtc erased_step (t1,σ1) (t2,σ2) → length t1 ≤ length t2.
  Proof.
    apply (rtc_ind erased_step (λ cfg1 cfg2, length cfg1.1 ≤ length cfg2.1)); clear.
    - intros [t1 σ1]; simpl. reflexivity.
    - intros [t1 σ1] [t2 σ2] [t3 σ3] Hstep _ Hlen. simpl in *.
      etrans; last eassumption.
      by eapply erased_step_grow.
  Qed.

  Lemma erased_step_app_r t1 σ1 t2 t3 σ2 efs :
    length t1 = length t2 →
    erased_step (t1,σ1) (t2++t3,σ2) →
    erased_step (t1++efs,σ1) (t2++efs++t3,σ2).
  Proof.
    intros Hlen [κ Hstep]. exists κ.
    destruct Hstep as [e1 σ1' e2 σ2' t2' thd ttl Heq1 Heq2 Hprim_step].
    simplify_eq. rename σ1' into σ1. rename σ2' into σ2.
    rename select (t2++t3 = _) into Heq.
    assert (t2 = thd ++ e2 :: ttl ∧ t3 = t2') as [-> <-].
    { apply app_inj_1.
      - rewrite -Hlen !length_app !length_cons //.
      - rewrite Heq app_comm_cons assoc //. }
    apply (step_atomic e1 σ1 e2 σ2 t3 thd (ttl++efs)).
    - rewrite app_comm_cons assoc //.
    - rewrite -!assoc -app_comm_cons //.
    - assumption.
  Qed.

  Lemma erased_step_app_l t1 σ1 t2 t3 σ2 :
    erased_step (t1,σ1) (t2,σ2) →
    erased_step (t3++t1,σ1) (t3++t2,σ2).
  Proof.
    intros [κ Hstep]. exists κ.
    destruct Hstep as [e1 σ1' e2 σ2' t2' thd ttl Heq1 Heq2 Hprim_step].
    simplify_eq. rename σ1' into σ1. rename σ2' into σ2.
    replace (t3++thd++e1::ttl) with ((t3++thd)++e1::ttl) by rewrite !assoc //.
    replace (t3++thd++e2::ttl++t2') with ((t3++thd)++e2::ttl++t2') by rewrite !assoc //.
    by eapply step_atomic.
  Qed.

  Lemma erased_nsteps_app_r n t1 σ1 t2 t3 σ2 efs :
    length t1 = length t2 →
    relations.nsteps erased_step n (t1,σ1) (t2++t3,σ2) →
    relations.nsteps erased_step n (t1++efs,σ1) (t2++efs++t3,σ2).
  Proof.
    intros Hlen Hsteps.
    remember (t1,σ1) as cfg1 eqn:Heqcfg1.
    remember (t2 ++ t3, σ2) as cfg2 eqn:Heqcfg2.
    revert cfg2 Hsteps efs t1 σ1 t2 t3 σ2 Heqcfg1 Heqcfg2 Hlen.

    apply (nsteps_ind_r (λ n cfg2, ∀ efs t1 σ1 t2 t3 σ2,
      cfg1 = (t1,σ1) → cfg2 = (t2++t3,σ2) → length t1 = length t2 →
      relations.nsteps erased_step n (t1++efs,σ1) (t2++efs++t3,σ2))).
    - intros efs t1 σ1 t2 t3 σ2 -> Heq Hlen.
      simplify_eq.
      rewrite length_app in Hlen.
      assert (t3=[]) as ->. { apply nil_length_inv. lia. }
      rewrite !right_id //. apply nsteps_O.
    - intros m [t_mid σ_mid] cfg3 Hsteps Hstep Hind.
      intros efs t1 σ1 t2 t3 σ2 -> -> Hlen.
      pose proof (erased_steps_grow t1 σ1 t_mid σ_mid ltac:(by eapply rtc_nsteps_2)) as Hlen_le.
      rewrite -(take_drop (length t1) t_mid) in Hsteps.
      remember (take (length t1) t_mid) as t_mid1 eqn:Heqt_mid1.
      remember (drop (length t1) t_mid) as t_mid2 eqn:Heqt_mid2.
      assert (Hlen_t_mid1: length t1 = length t_mid1).
      { rewrite Heqt_mid1 length_take. lia. }
      assert (Heq_tmid: t_mid = t_mid1 ++ t_mid2).
      { rewrite Heqt_mid1 Heqt_mid2 take_drop //. }
      apply (nsteps_r _ _ (t_mid1++efs++t_mid2,σ_mid)).
      + apply Hind; simplify_eq; done.
      + (*      Hstep:
            -------------------
            | t_mid1 | t_mid2 |
            -------------------
                     ↓
            ----------------------
            |  t2    |     t3    |
            ----------------------

                goal:
            ----------=====----------
            | t_mid1 | efs | t_mid2 |
            ----------=====----------
                     ↓
            ----------=====-------------
            |  t2    | efs |     t3    |
            ----------=====------------- *)
        rewrite Hlen_t_mid1 in Hlen.
        destruct Hstep as [κ Hstep].
        exists κ. subst t_mid.
        destruct Hstep as [e1 σ_mid' e2 σ2' efs' thd ttl Heq1 Heq2 Hprim_step].
        simplify_eq. rename σ2' into σ2. rename σ_mid' into σ_mid.
        rename select (t_mid1 ++ t_mid2 = thd ++ e1 :: ttl) into Heq1.
        rename select (t2 ++ t3 = thd ++ e2 :: ttl ++ efs') into Heq2.
        destruct (decide ((length thd) < length t_mid1)) as [Hlen_thd_t_mid1|Hlen_thd_t_mid1].
        * (* Case1:
                      Heq1
            ----------------------------
            |    t_mid1      |  t_mid2 |
            |--------------------------|
            | thd | e1 |     ttl       |
            |--------------------------|
            | thd | e1 |  Δ  |  t_mid2 |
            ---------------------------- *)
          assert (∃ Δ, t_mid1 = thd++e1::Δ ∧ ttl = Δ++t_mid2) as (Δ & -> & ->).
          { exists (drop (S (length thd)) t_mid1). split.
            - apply (f_equal (take (S (length thd)))) in Heq1.
              rewrite (take_app_le t_mid1 t_mid2) in Heq1; last lia.
              replace (thd++e1::ttl) with ((thd++[e1])++ttl) in Heq1 by rewrite -assoc //.
              replace (S (length thd)) with (length (thd++[e1])) in Heq1 by rewrite length_app (comm (Nat.add)) //.
              rewrite take_app_length in Heq1.
              rewrite length_app (comm (Nat.add)) /= in Heq1.
              trans ((thd ++ [e1]) ++ drop (S (length thd)) t_mid1).
              + rewrite -Heq1 take_drop //.
              + rewrite -assoc //.
            - apply (f_equal (drop (S (length thd)))) in Heq1.
              rewrite (drop_app_le t_mid1 t_mid2) in Heq1; last lia.
              rewrite Heq1.
              replace (thd++e1::ttl) with ((thd++[e1])++ttl) by rewrite -assoc //.
              replace (S (length thd)) with (length (thd++[e1])) by rewrite length_app (comm (Nat.add)) //.
              rewrite drop_app_length //. }
          (*            Heq2
            -----------------------------------
            |    t2          |        t3       |
            |----------------------------------|
            | thd | e2 |    ttl       |  efs'  |
            |----------------------------------|
            | thd | e2 |  Δ  | t_mid2 |  efs'  |
            ------------------------------------ *)
          replace (thd ++ e2 :: (Δ ++ t_mid2) ++ efs') with ((thd ++ e2 :: Δ) ++ t_mid2 ++ efs') in Heq2
            by rewrite -!assoc -app_comm_cons //.
          apply app_inj_1 in Heq2 as [-> ->]; last rewrite -Hlen !length_app !length_cons //.

          apply (step_atomic e1 σ_mid e2 σ2 efs' thd (Δ ++ efs++t_mid2));
            [rewrite -!assoc -app_comm_cons //..|done].

        * (* Case2:
                      Heq1
            ----------------------------
            | t_mid1 |    t_mid2       |
            |--------------------------|
            |   thd        | e1 | ttl  |
            |--------------------------|
            | t_mid1 |  Δ  | e1 | ttl  |
            ---------------------------- *)
          assert (∃ Δ, thd = t_mid1++Δ ∧ t_mid2 = Δ++e1::ttl) as (Δ & -> & ->).
          { exists (drop (length t_mid1) thd). split.
            - apply (f_equal (take (length t_mid1))) in Heq1.
              rewrite take_app_length take_app_le in Heq1; last lia.
              rewrite {1}Heq1 take_drop //.
            - apply (f_equal (drop (length t_mid1))) in Heq1.
              rewrite drop_app_length drop_app_le in Heq1; last lia.
              done. }
          (*            Heq2
            ------------------------------------
            |    t2      |          t3         |
            |----------------------------------|
            |     thd        | e2 | ttl | efs' |
            |----------------------------------|
            |   t_mid1   | Δ | e2 | ttl | efs' |
            ------------------------------------ *)
          rewrite -assoc in Heq2.
          apply app_inj_1 in Heq2 as [-> ->]; last rewrite Hlen //.

          apply (step_atomic e1 σ_mid e2 σ2 efs' (t_mid1++efs++Δ) ttl);
            [rewrite -!assoc //..|done].
  Qed.

  Lemma erased_steps_app_r t1 σ1 t2 t3 σ2 efs :
    length t1 = length t2 →
    rtc erased_step (t1,σ1) (t2++t3,σ2) →
    rtc erased_step (t1++efs,σ1) (t2++efs++t3,σ2).
  Proof.
    intros Hlen [n Hsteps]%rtc_nsteps_1.
    eapply rtc_nsteps_2.
    by apply erased_nsteps_app_r.
  Qed.

  Lemma erased_step_cons_r e1 t1 σ1 e2 t2 σ2 :
    erased_step ([e1],σ1) (e2::t2,σ2) →
    erased_step (e1::t1,σ1) (e2::t1++t2,σ2).
  Proof.
    change (e2::t2) with ([e2]++t2).
    change (e1::t1) with ([e1]++t1).
    change (e2::t1++t2) with ([e2]++t1++t2).
    by apply erased_step_app_r.
  Qed.

  Lemma erased_nsteps_cons_r n e1 t1 σ1 e2 t2 σ2 :
    relations.nsteps erased_step n ([e1],σ1) (e2::t2,σ2) →
    relations.nsteps erased_step n (e1::t1,σ1) (e2::t1++t2,σ2).
  Proof.
    change (e2::t2) with ([e2]++t2).
    change (e1::t1) with ([e1]++t1).
    change (e2::t1++t2) with ([e2]++t1++t2).
    by apply erased_nsteps_app_r.
  Qed.

  Lemma erased_steps_cons_r e1 t1 σ1 e2 t2 σ2 :
    rtc erased_step ([e1],σ1) (e2::t2,σ2) →
    rtc erased_step (e1::t1,σ1) (e2::t1++t2,σ2).
  Proof.
    change (e2::t2) with ([e2]++t2).
    change (e1::t1) with ([e1]++t1).
    change (e2::t1++t2) with ([e2]++t1++t2).
    by apply erased_steps_app_r.
  Qed.

  Lemma erased_step_cons_r_nofork e1 t1 σ1 e2 σ2 :
    erased_step ([e1],σ1) ([e2],σ2) →
    erased_step (e1::t1,σ1) (e2::t1,σ2).
  Proof.
    replace (e2::t1) with (e2::t1++[]) by rewrite right_id //.
    by apply erased_step_cons_r.
  Qed.

  Lemma erased_nsteps_cons_r_nofork n e1 t1 σ1 e2 σ2 :
    relations.nsteps erased_step n ([e1],σ1) ([e2],σ2) →
    relations.nsteps erased_step n (e1::t1,σ1) (e2::t1,σ2).
  Proof.
    replace (e2::t1) with (e2::t1++[]) by rewrite right_id //.
    by apply erased_nsteps_cons_r.
  Qed.

  Lemma erased_steps_cons_r_nofork e1 t1 σ1 e2 σ2 :
    rtc erased_step ([e1],σ1) ([e2],σ2) →
    rtc erased_step (e1::t1,σ1) (e2::t1,σ2).
  Proof.
    replace (e2::t1) with (e2::t1++[]) by rewrite right_id //.
    by apply erased_steps_cons_r.
  Qed.

  Lemma erased_nsteps_app_l n t1 σ1 t2 t3 σ2 :
    relations.nsteps erased_step n (t1,σ1) (t2,σ2) →
    relations.nsteps erased_step n (t3++t1,σ1) (t3++t2,σ2).
  Proof.
    remember (t1,σ1) as cfg1 eqn:Hcfg1.
    remember (t2,σ2) as cfg2 eqn:Hcfg2.
    replace t1 with cfg1.1 by by simplify_eq.
    replace σ1 with cfg1.2 by by simplify_eq.
    replace t2 with cfg2.1 by by simplify_eq.
    replace σ2 with cfg2.2 by by simplify_eq.
    clear t1 t2 σ1 σ2 Hcfg1 Hcfg2.
    intros Hsteps. induction Hsteps; first apply nsteps_O.
    eapply relations.nsteps_l; last eassumption.
    apply erased_step_app_l. rewrite -!surjective_pairing //.
  Qed.

  Lemma erased_steps_app_l t1 σ1 t2 t3 σ2 :
    rtc erased_step (t1,σ1) (t2,σ2) →
    rtc erased_step (t3++t1,σ1) (t3++t2,σ2).
  Proof.
    intros [n Hsteps]%rtc_nsteps_1.
    eapply rtc_nsteps_2.
    by apply erased_nsteps_app_l.
  Qed.

  Lemma erased_step_cons_l e1 t1 σ1 t2 σ2 :
    erased_step (t1,σ1) (t2,σ2) →
    erased_step (e1::t1,σ1) (e1::t2,σ2).
  Proof.
    change (e1::t2) with ([e1]++t2).
    change (e1::t1) with ([e1]++t1).
    by apply erased_step_app_l.
  Qed.

  Lemma erased_nsteps_cons_l n e1 t1 σ1 t2 σ2 :
    relations.nsteps erased_step n (t1,σ1) (t2,σ2) →
    relations.nsteps erased_step n (e1::t1,σ1) (e1::t2,σ2).
  Proof.
    change (e1::t2) with ([e1]++t2).
    change (e1::t1) with ([e1]++t1).
    by apply erased_nsteps_app_l.
  Qed.

  Lemma erased_steps_cons_l e1 t1 σ1 t2 σ2 :
    rtc erased_step (t1,σ1) (t2,σ2) →
    rtc erased_step (e1::t1,σ1) (e1::t2,σ2).
  Proof.
    change (e1::t2) with ([e1]++t2).
    change (e1::t1) with ([e1]++t1).
    by apply erased_steps_app_l.
  Qed.

  (* Decomposition of a no-fork [erased_step] on a 2-thread pool: either
     the first thread stepped (and the second is unchanged), or the
     second thread stepped (and the first is unchanged). *)
  Lemma erased_step_2_split e1 e2 σ1 a b σ2 :
    erased_step ([e1; e2], σ1) ([a; b], σ2) →
    (a = e1 ∧ erased_step ([e2], σ1) ([b], σ2)) ∨
    (b = e2 ∧ erased_step ([e1], σ1) ([a], σ2)).
  Proof.
    intros [κ Hstep].
    destruct Hstep as [e_src σ1' e_tgt σ2' efs t_pre t_post Heq1 Heq2 Hprim].
    injection Heq1 as Heq1_t Heq1_s. subst σ1'.
    injection Heq2 as Heq2_t Heq2_s. subst σ2'.
    (* Establish efs = []. *)
    assert (Hefs_nil : efs = []).
    { pose proof Heq1_t as Hlen1.
      apply (f_equal (length (A:=expr Λ))) in Hlen1.
      pose proof Heq2_t as Hlen2.
      apply (f_equal (length (A:=expr Λ))) in Hlen2.
      assert (Hlen1' : length t_pre + S (length t_post) = 2) by
        (rewrite length_app in Hlen1; simpl in Hlen1; lia).
      assert (Hlen2' : length t_pre + S (length t_post + length efs) = 2).
      { rewrite !length_app in Hlen2. simpl in Hlen2.
        rewrite length_app in Hlen2. lia. }
      destruct efs as [|? ?]; first reflexivity.
      simpl in Hlen2'. exfalso. lia. }
    subst efs. rewrite app_nil_r in Heq2_t.
    (* length t_pre ≤ 1 since pool size is 2. *)
    pose proof Heq1_t as Hlen_pre.
    apply (f_equal (length (A:=expr Λ))) in Hlen_pre.
    simpl in Hlen_pre. rewrite length_app in Hlen_pre. simpl in Hlen_pre.
    destruct t_pre as [|x1 [|x2 t_pre_rest]]; simpl in Heq1_t, Heq2_t;
      last (exfalso; simpl in Hlen_pre; lia).
    - injection Heq1_t as Heq1_src Heq1_post. subst e_src.
      destruct t_post as [|y1 [|y2 t_post_rest]]; try discriminate Heq1_post.
      injection Heq1_post as Heq1_y1. subst y1.
      injection Heq2_t as Heq2_a Heq2_b. subst a. subst b.
      right. split; first done.
      exists κ. by eapply (step_atomic e1 σ1 e_tgt σ2 [] [] []).
    - injection Heq1_t as Heq1_x1 Heq1_src Hpost. subst x1.
      symmetry in Hpost. subst t_post. subst e_src.
      injection Heq2_t as Heq2_a Heq2_b. subst a. subst b.
      left. split; first done.
      exists κ. by eapply (step_atomic e2 σ1 e_tgt σ2 [] [] []).
  Qed.

  (* 2-thread surgery: a no-fork derivation on a 2-thread pool can be
     lifted to a larger pool where the two threads sit at index 0 and at
     index [1 + length pre]. *)
  Lemma erased_steps_cons_r_cons_nofork e_bg main pre tail σ1 σ2 e_bg' main' :
    rtc erased_step ([e_bg; main], σ1) ([e_bg'; main'], σ2) →
    rtc erased_step (e_bg :: pre ++ main :: tail, σ1)
                    (e_bg' :: pre ++ main' :: tail, σ2).
  Proof.
    intros [n Hns]%rtc_nsteps_1.
    revert e_bg main σ1 e_bg' main' σ2 Hns.
    induction n as [|n IH]; intros e_bg main σ1 e_bg' main' σ2 Hns.
    { inversion Hns. simplify_eq. apply rtc_refl. }
    inversion Hns. simplify_eq.
    rename select (cfg _) into ρ_mid.
    destruct ρ_mid as [t_mid σ_mid].
    rename select (erased_step _ _) into Hstep_first.
    rename select (relations.nsteps erased_step _ _ _) into Hns_rest.
    pose proof (erased_step_grow _ _ _ _ Hstep_first) as Hlen_lo.
    pose proof (erased_steps_grow _ _ _ _ (rtc_nsteps_2 _ _ _ Hns_rest)) as Hlen_hi.
    simpl in Hlen_lo, Hlen_hi.
    assert (Hlen_mid : length t_mid = 2) by lia.
    destruct t_mid as [|m1 [|m2 [|? ?]]]; simpl in Hlen_mid; try lia.
    apply erased_step_2_split in Hstep_first as [[Heq_m1 Hstep_m2]|[Heq_m2 Hstep_m1]].
    - subst m1. apply (rtc_l _ _ (e_bg :: pre ++ m2 :: tail, σ_mid));
        last by apply IH.
      apply erased_step_cons_l, erased_step_app_l.
      by apply erased_step_cons_r_nofork.
    - subst m2. apply (rtc_l _ _ (m1 :: pre ++ main :: tail, σ_mid));
        last by apply IH.
      by apply erased_step_cons_r_nofork.
  Qed.

  Lemma erased_step_val v1 t1 σ1 t2 σ2 :
    erased_step (of_val v1::t1, σ1) (t2,σ2) →
    head t2 = Some (of_val v1).
  Proof.
    intros Hstep.
    destruct t2 as [|e2 t2].
    { apply erased_step_grow in Hstep. simpl in Hstep. lia. }
    simpl. f_equal.
    destruct Hstep as [κ Hstep].
    destruct Hstep as [e1' σ1' e2' σ2' efs t1a t1b Hρ1 Hρ2 Hprim_step].
    destruct t1a as [|v1' ?].
    - rewrite !left_id in Hρ1, Hρ2.
      simplify_eq.
      assert (Hred: reducible (of_val v1) σ1') by by do 4 eexists.
      apply reducible_not_val in Hred. rewrite to_of_val in Hred. done.
    - rewrite -!app_comm_cons in Hρ1, Hρ2. simplify_eq. done.
  Qed.

  Lemma erased_steps_val v1 t1 σ1 t2 σ2 :
    rtc erased_step (of_val v1::t1, σ1) (t2,σ2) →
    head t2 = Some (of_val v1).
  Proof.
    remember (t2,σ2) as ρ2 eqn:Hρ2.
    replace t2 with ρ2.1 by rewrite Hρ2 //.
    clear Hρ2. revert ρ2.
    apply (rtc_ind_r (λ ρ2, head ρ2.1 = Some (of_val v1))); first done.
    clear. intros [t2 σ2] [t3 σ3] Hsteps Hstep Hhead. simpl in *.
    destruct t2 as [|v2 t2]; first done.
    simpl in Hhead. injection Hhead as ->.
    by eapply erased_step_val.
  Qed.

  Lemma erased_step_eq_or_red t1a e1 t1b σ1 t2 σ2:
    erased_step (t1a++e1::t1b,σ1) (t2,σ2) →
    t2!!length t1a = Some e1 ∨ reducible e1 σ1.
  Proof.
    intros [κ Hstep].
    destruct Hstep as [e1' σ1' e2' σ2' efs' t1' t2' Heq1 Heq2 Hprim_step].
    destruct (decide (length t1a = length t1')) as [Hlen|Hlen].
    - right. injection Heq1 as Heq1 <-.
      apply app_inj_1 in Heq1 as [_ Heq1]; last done.
      injection Heq1 as <- _.
      by do 4 eexists.
    - left. injection Heq1 as Heq1 <-. injection Heq2 as Heq2 <-.
      apply (f_equal (λ x, x!!(length t1a))) in Heq1.
      apply (f_equal (λ x, x!!(length t1a))) in Heq2.
      rewrite {1}list_lookup_middle // in Heq1.
      (* rewrite {1}list_lookup_middle // in Heq2. *)
      destruct (decide (length t1a < length t1')).
      + rewrite !lookup_app_l in Heq1,Heq2; [|lia..].
        rewrite Heq1 Heq2 //.
      + rewrite !cons_middle in Heq1, Heq2.
        rewrite assoc in Heq1. rewrite assoc in Heq2.
        rewrite lookup_app_r in Heq1; last by rewrite length_app /=; lia.
        rewrite lookup_app_r in Heq2; last by rewrite length_app /=; lia.
        rewrite lookup_app_l in Heq2; last first.
        { symmetry in Heq1. apply lookup_lt_Some in Heq1.
          rewrite length_app /=.
          rewrite length_app /= in Heq1. done. }
        rewrite !length_app /= in Heq1,Heq2.
        rewrite Heq1 Heq2 //.
  Qed.

  Lemma erased_steps_eq_or_red t1a e1 t1b σ1 t2 σ2:
    rtc erased_step (t1a++e1::t1b,σ1) (t2,σ2) →
    t2!!length t1a = Some e1 ∨ reducible e1 σ1.
  Proof.
    intros Hsteps.
    remember (t2, σ2) as ρ eqn:Heqρ.
    replace t2 with ρ.1 by rewrite Heqρ //.
    clear -Hsteps. revert Hsteps.
    apply (rtc_ind_r (λ ρ, ρ.1 !! length t1a = Some e1 ∨ reducible e1 σ1)).
    - left.
      rewrite list_lookup_middle //.
    - intros [t2 σ2] [t3 σ3] Hsteps Hstep [Heq|]; last by right.
      simpl in *.
      destruct (list_elem_of_split_length _ _ _ Heq) as (t2a & t2b & -> & Hlen_eq2).
      apply erased_step_eq_or_red in Hstep.
      destruct Hstep as [Hred|]; first by left; rewrite Hlen_eq2.
      right.
  Abort.
End steps_lang.

Section steps_ectx_lang.
  Context {Λ : ectxLanguage}.
  Implicit Types (e : ectx_language.expr Λ) (t : list (ectx_language.expr Λ)) (σ : ectx_language.state Λ).
  Implicit Types (κ κs : list (ectx_language.observation Λ)).
  Implicit Types (v : ectx_language.val Λ).

  Lemma fill_erased_step K e1 σ1 e2 σ2 ts0 ts1 ts2 ts3 :
    length ts0 = length ts2 →
    erased_step (ts0 ++ e1 :: ts1, σ1) (ts2 ++ e2 :: ts3, σ2) →
    erased_step (ts0 ++ fill K e1 :: ts1, σ1) (ts2 ++ fill K e2 :: ts3, σ2).
  Proof.
    intros Hlen [κ Hstep]. exists κ.
    destruct Hstep as [e1' σ1' e2' σ2' efs' t1' t2' Heq1 Heq2 Hprim_step].
    injection Heq1 as Heq1 <-.
    injection Heq2 as Heq2 <-.
    simpl in *.
    destruct (decide (length ts0 < length t1')) as [Hlt | Hge];
    last destruct (decide (length ts0 = length t1')) as [Heq | Hne].
    - (* length ts0 < length t1' --- e1' is part of ts1 *)
      (* ---------------------------
         |    t1'     | e1' |  t2' |
         ---------------------------
         | ts0 | e1 |    ts1       |
         -------------------------------
         | ts2 | e2 |        ts3       |
         ------------------------------- *)
      apply (step_atomic e1' σ1 e2' σ2 efs'
        (ts0++fill K e1::take (length t1'-length ts0-1) ts1)
        (drop (S(length t1'-length ts0-1)) ts1)); [f_equal..|done].
      + rewrite -assoc -app_comm_cons. do 2 f_equal.
        symmetry. apply take_drop_middle.
        rewrite -Nat.sub_add_distr.
        change 1 with (length [e1]).
        rewrite -length_app -lookup_app_r; last first.
        { rewrite length_app /=. lia. }
        rewrite -assoc -cons_middle Heq1 lookup_app_r // Nat.sub_diag.
        done.
      + rewrite -assoc -app_comm_cons. f_equal; last f_equal.
        * apply (f_equal (take (length ts0))) in Heq1.
          do 2 (rewrite take_app_le in Heq1; last lia).
          rewrite take_ge in Heq1; last lia.
          apply (f_equal (take (length ts0))) in Heq2.
          do 2 (rewrite take_app_le in Heq2; last lia).
          rewrite take_ge in Heq2; last lia.
          by rewrite Heq1 Heq2.
        * f_equal.
          apply (f_equal (λ x, x !! length ts0)) in Heq1.
          rewrite lookup_app_r in Heq1; last lia.
          rewrite lookup_app_l in Heq1; last lia.
          rewrite Nat.sub_diag lookup_cons in Heq1.
          apply (f_equal (λ x, x !! length ts0)) in Heq2.
          rewrite lookup_app_r in Heq2; last lia.
          rewrite lookup_app_l in Heq2; last lia.
          rewrite -!Hlen Nat.sub_diag lookup_cons in Heq2.
          rewrite -Heq2 in Heq1.
          by injection Heq1.
        * rewrite -(take_drop_middle ts3 (length t1' - length ts0 - 1) e2'); first (f_equal;[|f_equal]).
          --apply (f_equal (take (length t1'))) in Heq1.
            rewrite cons_middle assoc in Heq1.
            rewrite take_app_ge in Heq1; last (rewrite length_app /=; lia).
            rewrite take_app_le in Heq1; last lia.
            rewrite (take_ge t1') in Heq1; last lia.
            rewrite length_app /= Nat.sub_add_distr in Heq1.
            apply (f_equal (take (length t1'))) in Heq2.
            rewrite cons_middle assoc in Heq2.
            rewrite take_app_ge in Heq2; last (rewrite length_app /=; lia).
            rewrite take_app_le in Heq2; last lia.
            rewrite (take_ge t1') in Heq2; last lia.
            rewrite length_app /= Nat.sub_add_distr in Heq2.
            rewrite -{2}Heq1 in Heq2.
            apply app_inj_1 in Heq2 as [_ Heq2]; last (rewrite !length_app /=; lia).
            by rewrite -Heq2 Hlen.
          --replace (S (length t1' - length ts0 - 1)) with (length t1' + 1 - (length ts0 + 1)) by lia.
            apply (f_equal (drop (length t1' + 1))) in Heq1.
            rewrite !cons_middle 2!assoc in Heq1.
            rewrite drop_app_ge in Heq1; last (rewrite length_app /=; lia).
            rewrite drop_app_ge in Heq1; last (rewrite length_app /=; lia).
            rewrite !length_app /= Nat.sub_diag drop_0 in Heq1.
            apply (f_equal (drop (length t1' + 1))) in Heq2.
            rewrite !cons_middle 2!assoc in Heq2.
            rewrite drop_app_ge in Heq2; last (rewrite length_app /=; lia).
            rewrite drop_app_ge in Heq2; last (rewrite length_app /=; lia).
            rewrite !length_app /= Nat.sub_diag drop_0 -Hlen in Heq2.
            by rewrite Heq1 Heq2.
          --apply (f_equal (λ x, x!!length t1')) in Heq2.
            rewrite cons_middle assoc in Heq2.
            rewrite lookup_app_r in Heq2; last (rewrite length_app /=; lia).
            rewrite lookup_app_r in Heq2; last lia.
            rewrite length_app Nat.sub_diag Nat.sub_add_distr /= -Hlen in Heq2.
            done.
    - (* length ts0 = length t1' --- e1' = e1 *)
      apply app_inj_1 in Heq1 as [<- Heq1]; last done.
      injection Heq1 as <- <-.
      apply app_inj_1 in Heq2 as [<- Heq2]; last done.
      injection Heq2 as <- ->.
      eapply step_atomic; [reflexivity..|].
      by apply fill_prim_step.
    - (* length ts0 > length t1' --- e1' is part of ts0 *)
      (* ---------------------------
         |  t1' | e1' |      t2'    |
         ---------------------------
         |     ts0      | e1 | ts1  |
         -------------------------------
         |     ts2      | e2 |   ts3   |
         ------------------------------- *)
      apply (step_atomic e1' σ1 e2' σ2 efs'
        (take (length t1') ts0)
        (drop (S (length t1')) ts0++fill K e1::ts1)); [f_equal..|done].
      + rewrite !cons_middle !assoc. do 2 f_equal.
        rewrite -assoc -cons_middle.
        symmetry. apply take_drop_middle.
        apply (f_equal (λ x, x!!length t1')) in Heq1.
        rewrite lookup_app_l in Heq1; last lia.
        rewrite lookup_app_r in Heq1; last lia.
        rewrite Nat.sub_diag lookup_cons in Heq1.
        done.
      (**********************************************************)
      (* Begin LLM-generated code. *)
      (* tool: Claude Code 2.1.77
         model: Claude Opus 4.6 with 1M context (claude-opus-4-6)
         parameters:
            effort = high
            context window = 1000000
            max output tokens = 128000 *)
      + rewrite -(take_drop_middle ts2 (length t1') e2'); first last.
        { apply (f_equal (λ x, x!!length t1')) in Heq2.
          rewrite lookup_app_l in Heq2; last lia.
          rewrite lookup_app_r in Heq2; last lia.
          rewrite Nat.sub_diag lookup_cons in Heq2.
          done. }
        rewrite -app_assoc !app_comm_cons -[(_ ++ _) ++ efs']app_assoc. f_equal; [|f_equal].
        * apply (f_equal (take (length t1'))) in Heq1.
          do 2 (rewrite take_app_le in Heq1; last lia).
          rewrite firstn_all in Heq1.
          apply (f_equal (take (length t1'))) in Heq2.
          do 2 (rewrite take_app_le in Heq2; last lia).
          rewrite firstn_all in Heq2.
          by rewrite Heq1 Heq2.
        * (* e2' :: drop .. ts2 = e2' :: drop .. ts0 *)
          f_equal.
          pose proof Heq1 as H1. pose proof Heq2 as H2.
          apply (f_equal (drop (S (length t1')))) in H1.
          rewrite drop_app_le in H1; [|lia].
          rewrite drop_app_ge in H1; [|lia].
          replace (S (length t1') - length t1') with 1 in H1 by lia.
          change (drop 1 (?x :: ?y)) with y in H1.
          apply (f_equal (take (length ts0 - length t1' - 1))) in H1.
          rewrite firstn_app in H1.
          replace (length ts0 - length t1' - 1 - length (drop (S (length t1')) ts0))
            with 0 in H1 by (rewrite length_drop; lia).
          rewrite /= app_nil_r in H1.
          apply (f_equal (drop (S (length t1')))) in H2.
          rewrite drop_app_le in H2; [|lia].
          rewrite drop_app_ge in H2; [|lia].
          replace (S (length t1') - length t1') with 1 in H2 by lia.
          change (drop 1 (?x :: ?y)) with y in H2.
          assert (Ht2'_len: length ts0 - length t1' - 1 ≤ length t2').
          { apply (f_equal length) in Heq1.
            rewrite !length_app /= in Heq1. lia. }
          apply (f_equal (take (length ts0 - length t1' - 1))) in H2.
          rewrite firstn_app in H2.
          replace (length ts0 - length t1' - 1 - length (drop (S (length t1')) ts2))
            with 0 in H2 by (rewrite length_drop; lia).
          rewrite /= app_nil_r in H2.
          rewrite firstn_app in H2.
          replace (length ts0 - length t1' - 1 - length t2')
            with 0 in H2 by lia.
          rewrite /= app_nil_r in H2.
          rewrite take_ge in H1; last (rewrite length_drop; lia).
          rewrite take_ge in H2; last (rewrite length_drop; lia).
          by rewrite H1.
        * (* fill K e2 :: ts3 = (fill K e1 :: ts1) ++ efs' *)
          f_equal; last f_equal.
          --pose proof Heq1 as H1. pose proof Heq2 as H2.
            apply (f_equal (drop (S (length t1')))) in H1.
            rewrite drop_app_le in H1; [|lia].
            rewrite drop_app_ge in H1; [|lia].
            replace (S (length t1') - length t1') with 1 in H1 by lia.
            change (drop 1 (?x :: ?y)) with y in H1.
            apply (f_equal (drop (S (length t1')))) in H2.
            rewrite drop_app_le in H2; [|lia].
            rewrite drop_app_ge in H2; [|lia].
            replace (S (length t1') - length t1') with 1 in H2 by lia.
            change (drop 1 (?x :: ?y)) with y in H2.
            (* H1: drop .. ts0 ++ e1 :: ts1 = t2' *)
            (* H2: drop .. ts2 ++ e2 :: ts3 = t2' ++ efs' *)
            rewrite -H1 -app_assoc /= in H2.
            apply app_inj_1 in H2 as [_ H2].
            2:{ do 2 rewrite length_drop. lia. }
            injection H2 as <- ->. done.
      (* End LLM-generated code. *)
      (**********************************************************)
  Qed.

  Lemma fill_erased_nsteps K n e1 σ1 e2 σ2 ts0 ts1 ts2 ts3 :
    length ts0 = length ts2 →
    relations.nsteps erased_step n (ts0 ++ e1 :: ts1,σ1) (ts2 ++ e2 :: ts3,σ2) →
    relations.nsteps erased_step n (ts0 ++ fill K e1 :: ts1,σ1) (ts2 ++ fill K e2 :: ts3,σ2).
  Proof.
    revert e1 σ1 e2 σ2 ts0 ts1 ts2 ts3.
    induction n as [|n IH] => e1 σ1 e2 σ2 ts0 ts1 ts2 ts3 Hlen.
    { inversion 1.
      rename select (_++_::_ = _++_::_) into Heq.
      apply app_inj_1 in Heq as [-> Heq]; last done.
      simplify_eq. apply nsteps_O. }
    inversion 1. simplify_eq.
    rename select (erased_step _ _) into Hstep.
    rename select (relations.nsteps erased_step n _ _) into Hsteps.
    rename select (cfg Λ) into ρ.
    destruct ρ as [ts_mid σ_mid].
    apply erased_step_grow in Hstep as Hlen'.
    rewrite length_app length_cons in Hlen'.
    simpl in *.
    pose proof (lookup_lt_is_Some_2 ts_mid (length ts0) ltac:(lia))
      as [e_mid Hlookup].
    pose proof (Hts_mid_eq := take_drop_middle ts_mid _ _ Hlookup).
    rewrite -Hts_mid_eq in Hstep.
    rewrite -Hts_mid_eq in Hsteps.
    apply (fill_erased_step K) in Hstep; last (rewrite length_take; lia).
    apply IH in Hsteps; last (rewrite length_take; lia).
    eapply relations.nsteps_l; eassumption.
  Qed.

  Lemma fill_erased_steps K e1 σ1 e2 σ2 ts0 ts1 ts2 ts3 :
    length ts0 = length ts2 →
    rtc erased_step (ts0 ++ e1 :: ts1,σ1) (ts2 ++ e2 :: ts3,σ2) →
    rtc erased_step (ts0 ++ fill K e1 :: ts1,σ1) (ts2 ++ fill K e2 :: ts3,σ2).
  Proof.
    intros Hlen [n Hsteps]%rtc_nsteps_1.
    eapply rtc_nsteps_2.
    by apply fill_erased_nsteps.
  Qed.

  Lemma fill_erased_step_head K e1 σ1 e2 σ2 ts1 ts2 :
    erased_step (e1::ts1, σ1) (e2 :: ts2, σ2) →
    erased_step (fill K e1::ts1, σ1) (fill K e2 :: ts2, σ2).
  Proof.
    pose proof (H := fill_erased_step K e1 σ1 e2 σ2 [] ts1 [] ts2 eq_refl).
    rewrite !left_id_L in H. done.
  Qed.

  Lemma fill_erased_nsteps_head K n e1 σ1 e2 σ2 ts1 ts2 :
    relations.nsteps erased_step n (e1::ts1, σ1) (e2 :: ts2, σ2) →
    relations.nsteps erased_step n (fill K e1::ts1, σ1) (fill K e2 :: ts2, σ2).
  Proof.
    pose proof (H := fill_erased_nsteps K n e1 σ1 e2 σ2 [] ts1 [] ts2 eq_refl).
    rewrite !left_id_L in H. done.
  Qed.

  Lemma fill_erased_steps_head K e1 σ1 e2 σ2 ts1 ts2 :
    rtc erased_step (e1::ts1, σ1) (e2 :: ts2, σ2) →
    rtc erased_step (fill K e1::ts1, σ1) (fill K e2 :: ts2, σ2).
  Proof.
    pose proof (H := fill_erased_steps K e1 σ1 e2 σ2 [] ts1 [] ts2 eq_refl).
    rewrite !left_id_L in H. done.
  Qed.

  Lemma fill_erased_step_head_nofork K e1 σ1 e2 σ2 ts1 :
    erased_step ([e1], σ1) ([e2], σ2) →
    erased_step (fill K e1::ts1, σ1) (fill K e2 :: ts1, σ2).
  Proof.
    intros ?.
    apply fill_erased_step_head.
    by apply erased_step_cons_r_nofork.
  Qed.

  Lemma fill_erased_nsteps_head_nofork K n e1 σ1 e2 σ2 ts1 :
    relations.nsteps erased_step n ([e1], σ1) ([e2], σ2) →
    relations.nsteps erased_step n (fill K e1::ts1, σ1) (fill K e2 :: ts1, σ2).
  Proof.
    intros ?.
    apply fill_erased_nsteps_head.
    by apply erased_nsteps_cons_r_nofork.
  Qed.

  Lemma fill_erased_steps_head_nofork K e1 σ1 e2 σ2 ts1 :
    rtc erased_step ([e1], σ1) ([e2], σ2) →
    rtc erased_step (fill K e1::ts1, σ1) (fill K e2 :: ts1, σ2).
  Proof.
    intros ?.
    apply fill_erased_steps_head.
    by apply erased_steps_cons_r_nofork.
  Qed.

  Lemma erased_steps_pure_steps e1 e2 K σ1 σ2 ts0 ts1 ts2 :
    rtc pure_step e1 e2 →
    rtc erased_step (ts0++fill K e2::ts1, σ1) (ts2,σ2) →
    rtc erased_step (ts0++fill K e1::ts1, σ1) (ts2,σ2).
  Proof.
    intros [n Hnsteps]%rtc_nsteps_1 Hsteps.
    etrans; last exact Hsteps.
    apply fill_erased_steps; first reflexivity.
    clear -Hnsteps. induction Hnsteps as [|n e1 e2 e3 Hstep Hnsteps IH].
    { reflexivity. }
    eapply rtc_l; last exact IH.
    destruct Hstep as [Hstep Hdet].
    destruct (Hstep σ1) as (e2' & σ' & efs' & Hprim_step).
    destruct (Hdet _ _ _ _ _ Hprim_step) as (_ & -> & -> & ->).
    exists [].
    eapply (step_atomic e1 σ1 e2 σ1 [] ts0 ts1); rewrite ?left_id_L ?right_id_L; [reflexivity..|].
    done.
  Qed.

  Lemma erased_steps_pure_exec φ n e1 e2 K σ1 σ2 ts0 ts1 ts2 :
    PureExec φ n e1 e2 →
    φ →
    rtc erased_step (ts0++fill K e2::ts1, σ1) (ts2,σ2) →
    rtc erased_step (ts0++fill K e1::ts1, σ1) (ts2,σ2).
  Proof.
    intros Hpures Hφ.
    rewrite /PureExec in Hpures.
    apply Hpures,rtc_nsteps_2 in Hφ as Hsteps.
    by apply erased_steps_pure_steps.
  Qed.

  Lemma erased_steps_pure_exec_head φ n e1 e2 K σ1 σ2 ts1 ts2 :
    PureExec φ n e1 e2 →
    φ →
    rtc erased_step (fill K e2::ts1, σ1) (ts2,σ2) →
    rtc erased_step (fill K e1::ts1, σ1) (ts2,σ2).
  Proof.
    exact (erased_steps_pure_exec φ n e1 e2 K σ1 σ2 [] ts1 ts2).
  Qed.

  Lemma erased_steps_apply K ts1 e1 σ1 efs1 ts2 e2 σ2 efs2 t3 σ3 :
    length ts1 = length ts2 →
    rtc erased_step (ts1++e1::efs1,σ1) (ts2++e2::efs2,σ2) →
    rtc erased_step (ts2++fill K e2::efs2,σ2) (t3,σ3) →
    rtc erased_step (ts1++fill K e1::efs1,σ1) (t3,σ3).
  Proof.
    intros Hlen Hs1 Hs2.
    etrans; last exact Hs2.
    by apply fill_erased_steps.
  Qed.

  Lemma erased_steps_apply_head K e1 σ1 efs1 e2 σ2 efs2 t3 σ3 :
    rtc erased_step (e1::efs1,σ1) (e2::efs2,σ2) →
    rtc erased_step (fill K e2::efs2,σ2) (t3,σ3) →
    rtc erased_step (fill K e1::efs1,σ1) (t3,σ3).
  Proof.
    intros Hs1 Hs2.
    etrans; last exact Hs2.
    by apply fill_erased_steps_head.
  Qed.

  Lemma erased_steps_apply_head_nofork K e1 σ1 efs1 e2 σ2 t3 σ3 :
    rtc erased_step ([e1],σ1) ([e2],σ2) →
    rtc erased_step (fill K e2::efs1,σ2) (t3,σ3) →
    rtc erased_step (fill K e1::efs1,σ1) (t3,σ3).
  Proof.
    intros Hs1 Hs2.
    etrans; last exact Hs2.
    by apply fill_erased_steps_head_nofork.
  Qed.

  Lemma erased_steps_apply_once K ts1 e1 σ1 efs1 ts2 e2 σ2 efs2 t3 σ3 :
    length ts1 = length ts2 →
    erased_step (ts1++e1::efs1,σ1) (ts2++e2::efs2,σ2) →
    rtc erased_step (ts2++fill K e2::efs2,σ2) (t3,σ3) →
    rtc erased_step (ts1++fill K e1::efs1,σ1) (t3,σ3).
  Proof.
    intros Hlen Hs1 Hs2.
    eapply rtc_l; last exact Hs2.
    by apply fill_erased_step.
  Qed.

  Lemma erased_steps_apply_once_head K e1 σ1 efs1 e2 σ2 efs2 t3 σ3 :
    erased_step (e1::efs1,σ1) (e2::efs2,σ2) →
    rtc erased_step (fill K e2::efs2,σ2) (t3,σ3) →
    rtc erased_step (fill K e1::efs1,σ1) (t3,σ3).
  Proof.
    intros Hs1 Hs2.
    eapply rtc_l; last exact Hs2.
    by apply fill_erased_step_head.
  Qed.

  Lemma erased_steps_apply_once_head_nofork K e1 σ1 efs1 e2 σ2 t3 σ3 :
    erased_step ([e1],σ1) ([e2],σ2) →
    rtc erased_step (fill K e2::efs1,σ2) (t3,σ3) →
    rtc erased_step (fill K e1::efs1,σ1) (t3,σ3).
  Proof.
    intros Hs1 Hs2.
    eapply rtc_l; last exact Hs2.
    by apply fill_erased_step_head_nofork.
  Qed.

  (*************** Begin LLM-generated code. ****************)
  (* Claude Opus 4.7 (1M context, xhigh effort, v2.1.111) *)
  Local Lemma nsteps_O_eq {A} (R : relation A) (x y : A) :
    relations.nsteps R 0 x y → x = y.
  Proof. by inversion 1. Qed.

  Lemma erased_nsteps_bind_inv n K e1 σ1 v3 t3a t3 σ3 :
    relations.nsteps erased_step n (fill K e1 :: t3a, σ1) (of_val v3 :: t3, σ3) →
    ∃ v2 t2 σ2,
      rtc erased_step (e1 :: t3a, σ1) (of_val v2 :: t2, σ2)
    ∧ rtc erased_step (fill K (of_val v2) :: t2, σ2) (of_val v3 :: t3, σ3).
  Proof.
    revert e1 σ1 v3 t3a t3 σ3.
    induction n as [|n IH]; intros e1 σ1 v3 t3a t3 σ3 Hsteps.
    - (* n = 0: configurations are equal *)
      apply nsteps_O_eq in Hsteps.
      pose proof (f_equal fst Hsteps) as Hcfg_l. cbn in Hcfg_l.
      pose proof (f_equal snd Hsteps) as Hcfg_s. cbn in Hcfg_s.
      clear Hsteps.
      pose proof (f_equal (@head (expr Λ)) Hcfg_l) as Hcfg_hopt.
      pose proof (f_equal (@tail (expr Λ)) Hcfg_l) as Hcfg_tail.
      cbn in Hcfg_hopt, Hcfg_tail.
      clear Hcfg_l.
      injection Hcfg_hopt as Hcfg_h.
      assert (Hisv : is_Some (to_val e1)).
      { apply (fill_val K). rewrite Hcfg_h to_of_val. by eexists. }
      destruct Hisv as [vk Htv].
      pose proof (of_to_val _ _ Htv) as Hve1.
      exists vk, t3, σ3. split.
      + rewrite -Hve1 Hcfg_tail Hcfg_s. apply rtc_refl.
      + rewrite Hve1 Hcfg_h. apply rtc_refl.
    - (* n + 1 steps *)
      inversion Hsteps. simplify_eq.
      rename select (cfg Λ) into ρmid.
      rename select (erased_step _ _) into Hstep.
      rename select (relations.nsteps erased_step _ _ _) into Hsteps_rest.
      destruct ρmid as [tmid σmid].
      destruct Hstep as [κ Hstep_atomic].
      destruct Hstep_atomic as [eA σ1' eA' σmid' efsV t1V t2V Heq1 Heq2 Hprim_step].
      apply pair_eq in Heq1 as [Heq1_l <-].
      apply pair_eq in Heq2 as [-> <-].
      destruct t1V as [|eHd t1Vrest].
      + (* main thread step *)
        cbn [app] in Heq1_l.
        injection Heq1_l as <- <-.
        cbn [app] in Hsteps_rest.
        destruct (to_val e1) as [vE1|] eqn:Hto_e1.
        * (* e1 is already a value *)
          pose proof (of_to_val _ _ Hto_e1) as He1eq.
          exists vE1, t3a, σ1. split.
          -- rewrite -He1eq. apply rtc_refl.
          -- rewrite He1eq.
             eapply rtc_l.
             ++ exists κ.
                apply (step_atomic (fill K e1) σ1 eA' σmid efsV [] t3a); done.
             ++ by eapply rtc_nsteps_2.
        * (* e1 is not a value: invert via fill_step_inv *)
          destruct (fill_step_inv e1 σ1 κ eA' σmid efsV Hto_e1 Hprim_step)
            as (eA'' & Heq_eA' & Hprim_step').
          subst eA'.
          apply IH in Hsteps_rest as (vTwo & tTwo & sigTwo & Hrtc1 & Hrtc2).
          exists vTwo, tTwo, sigTwo. split; last exact Hrtc2.
          eapply rtc_l; last exact Hrtc1.
          exists κ.
          apply (step_atomic e1 σ1 eA'' σmid efsV [] t3a); done.
      + (* other thread step *)
        cbn [app] in Heq1_l.
        injection Heq1_l as Heq1_h Heq1_t.
        subst eHd t3a.
        cbn [app] in Hsteps_rest.
        apply IH in Hsteps_rest as (vTwo & tTwo & sigTwo & Hrtc1 & Hrtc2).
        exists vTwo, tTwo, sigTwo. split; last exact Hrtc2.
        eapply rtc_l; last exact Hrtc1.
        exists κ.
        apply (step_atomic eA σ1 eA' σmid efsV (e1 :: t1Vrest) t2V); done.
  Qed.

  Lemma erased_steps_bind_inv K e1 σ1 v3 t3a t3 σ3 :
    rtc erased_step (fill K e1::t3a,σ1) (of_val v3::t3,σ3) →
    ∃ v2 t2 σ2,
      rtc erased_step (e1::t3a, σ1) (of_val v2::t2, σ2)
    ∧ rtc erased_step (fill K (of_val v2)::t2, σ2) (of_val v3::t3, σ3).
  Proof.
    intros [n Hsteps]%rtc_nsteps_1.
    by apply (erased_nsteps_bind_inv n K e1 σ1 v3 t3a).
  Qed.
  (**************** End LLM-generated code. *****************)

  (* Two-thread variant of [erased_steps_bind_inv]: the initial pool is
     [fill K e1 :: e_bg], where [e_bg] is a fixed sibling thread (e.g.
     the background thread spawned by [new_trace]). Extracts that [e1]
     terminates to some [Val v2], together with the residual derivation
     starting from [fill K (Val v2) :: t2]. *)
  Lemma erased_steps_bind_inv_two K e1 e_bg σ1 v3 t3 σ3 :
    rtc erased_step ([fill K e1; e_bg], σ1) (of_val v3 :: t3, σ3) →
    ∃ v2 t2 σ2,
      rtc erased_step ([e1; e_bg], σ1) (of_val v2 :: t2, σ2)
    ∧ rtc erased_step (fill K (of_val v2) :: t2, σ2) (of_val v3 :: t3, σ3).
  Proof.
    intros [n Hsteps]%rtc_nsteps_1.
    by apply (erased_nsteps_bind_inv n K e1 σ1 v3 [e_bg]).
  Qed.
End steps_ectx_lang.
