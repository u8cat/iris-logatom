From iris_logatom.pure_logic Require Import encodable steps tactics.
From iris.heap_lang Require Import primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import lang_wf.

Notation NIL := NONE (only parsing).
Notation NILV := NONEV (only parsing).
Notation CONS x xs := (SOME (x,xs)) (only parsing).
Notation CONSV x xs := (SOMEV (x,xs)) (only parsing).

Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' x xs => e2 'end'" :=
  (Match e0 BAnon e1 "tmp_101b8214" (let: x := Fst "tmp_101b8214" in let: xs := Snd "tmp_101b8214" in e2))
  (e0, e1, xs, e2 at level 200, x at level 1, only parsing) : expr_scope.
Notation "'match:' e0 'with' 'CONS' x xs => e2 | 'NIL' => e1 'end'" :=
  (Match e0 BAnon e1 "tmp_101b8214" (let: x := Fst "tmp_101b8214" in let: xs := Snd "tmp_101b8214" in e2))
  (e0, e1, xs, e2 at level 200, x at level 1, only parsing) : expr_scope.

Definition list_nth: val := rec: "nth" "n" "xs" :=
  match: "xs" with
    NIL => (inhabitant: val)
  | CONS "x" "xs" =>
    if: "n" = #0 then "x"
    else "nth" ("n"-#1) "xs"
  end.

Fixpoint encode_list xs :=
  match xs with
  | [] => NILV
  | x::xs => CONSV x (encode_list xs)
  end.

Fixpoint decode_list xs :=
  match xs with
  | NILV => Some []
  | CONSV x xs =>
    decode_list xs ≫= λ XS, Some (x::XS)
  | _ => None
  end.

Global Program Instance list_encodable : Encodable (list val) := {
  encode_val := encode_list;
  decode_val := decode_list;
}.
Next Obligation.
  intros xs; induction xs as [|x xs IH]; first done.
  by rewrite /= IH.
Qed.
Next Obligation.
  intros v.
  induction v as [v IH] using (well_founded_ind val_lt_wf) => xs.
  destruct v; simpl; try congruence.
  - rename select val into v.
    do 2 (case_match; try done).
    intros ?. by simplify_eq.
  - rename select val into v.
    destruct v as [ | | v1 v2 | | ]; try congruence.
    opose proof (IH v2 _) as Hdec; first solve_val_lt.
    destruct (decode_list v2) as [ys |]; simpl; last congruence.
    rewrite (Hdec ys eq_refl).
    intros ?. by simplify_eq.
Qed.

(* returns an expression that evaluates to an object-level list *)
Fixpoint dynamic_encode_list (xs : list expr) : expr :=
  match xs with
  | [] => NIL
  | x::xs => CONS x (dynamic_encode_list xs)
  end.

Lemma erased_steps_dynamic_encode_list_val (xs : list val) σ :
  rtc erased_step ([dynamic_encode_list (Val <$> xs)],σ)
                  ([Val (encode_val xs)],σ).
Proof.
  induction xs as [|x xs IH]; simpl.
  - erased_steps_pure. reflexivity.
  - erased_steps_apply IH.
    repeat erased_steps_pure.
    reflexivity.
Qed.

Lemma pure_steps_dynamic_encode_list_val (xs : list val) :
  rtc pure_step (dynamic_encode_list (Val <$> xs))
                (Val (encode_val xs)).
Proof.
  induction xs as [|x xs IH].
  - rewrite /encode_val /=.
    eapply rtc_nsteps_2.
    by apply pure_exec.
  - simpl.
    etrans.
    { apply (rtc_pure_step_ctx (fill [PairRCtx x; InjRCtx])).
      exact IH. }
    simpl.
    etrans.
    { apply (rtc_pure_step_ctx (fill [InjRCtx])).
      eapply rtc_nsteps_2.
      by apply pure_exec. }
    simpl.
    etrans.
    { eapply rtc_nsteps_2.
      by apply pure_exec. }
    reflexivity.
Qed.

Lemma erased_steps_list_nth (n : nat) (xs : list val) σ :
  rtc erased_step ([list_nth #n (encode_val xs)], σ)
                  ([Val (xs!!!n)], σ).
Proof.
  revert n. induction xs as [|x xs IH] => n; rewrite /list_nth.
  - rewrite lookup_total_nil. repeat erased_steps_pure. reflexivity.
  - erased_steps_pure. rewrite -/list_nth.
    destruct n as [|n]; repeat erased_steps_pure; [by left|reflexivity|by left|].
    replace (S n - 1)%Z with (Z.of_nat n) by lia.
    apply IH.
Qed.

Section proof.
  Context `{!heapGS Σ}.
  Lemma list_nth_spec (n : nat) (xs : list val) s E Φ:
    Φ (xs!!!n) -∗
    WP list_nth #n (encode_val xs) @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iInduction xs as [|x xs] "IH" forall (n); wp_rec; wp_pures.
    - rewrite lookup_total_nil. iApply "HΦ".
    - destruct n as [|n]; simpl; wp_pures; first auto.
      replace (S n - 1)%Z with (Z.of_nat n) by lia.
      iApply ("IH" with "HΦ").
  Qed.

  Lemma dynamic_encode_list_spec (xse : list expr) s E Φs:
    {{{ ([∗ list] xe; Φ ∈ xse; Φs, WP xe @ s; E {{ Φ }}) }}}
      dynamic_encode_list xse @ s; E
    {{{ xsv, RET (encode_val xsv : val); [∗ list] xv; Φ ∈ xsv; Φs, Φ xv }}}.
  Proof.
    revert Φs. induction xse as [|xe xse IH] => Φs.
    - iIntros (Φ) "Hnil HΦ".
      iDestruct (big_sepL2_length with "Hnil") as %Hlen.
      destruct Φs; last by simpl in Hlen.
      wp_pures. iModIntro.
      by iApply ("HΦ" $! []).
    - iIntros (Φ') "HΦs HΦ'".
      iDestruct (big_sepL2_length with "HΦs") as %Hlen.
      destruct Φs as [|Φ Φs]; first by simpl in Hlen.
      rewrite big_sepL2_cons.
      iDestruct "HΦs" as "[HΦ HΦs]".
      wp_pures.
      wp_apply (IH with "HΦs") as (xsv) "HΦs".
      wp_bind xe.
      wp_apply (wp_wand with "HΦ") as (xv) "HΦ".
      wp_pures. iModIntro.
      iApply ("HΦ'" $! (xv::xsv)).
      rewrite big_sepL2_cons.
      iFrame.
  Qed.
End proof.
