From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic Require Import encodable.
From iris_logatom.heap_lang.rel_logic Require Import model properness rel_tactics spec_tactics.
From iris_logatom.heap_lang.lib Require Export list.

Section refine_rules.
  Context `{!relocGS Σ}.
  (* [list_nth #n] evaluates purely to the [n]-th element on either side, so a
    refinement of the elements lifts to a refinement of the lookups. *)
  Lemma refines_list_nth_l C (n : nat) (xs : list val) e' :
    (REL (xs!!!n : val) << e' : C) -∗
    REL list_nth #n (encode_val xs) << e' : C.
  Proof.
    iInduction xs as [|x xs] "IH" forall (n); iIntros "H"; rel_rec_l; rel_pures_l.
    - done.
    - destruct n as [|n]; rel_pures_l; first done.
      replace (Datatypes.S n - 1)%Z with (Z.of_nat n) by lia.
      by iApply "IH".
  Qed.

  Lemma refines_list_nth_r C (n : nat) (xs' : list val) e :
    (REL e << (xs'!!!n : val) : C) -∗
    REL e << list_nth #n (encode_val xs') : C.
  Proof.
    iInduction xs' as [|x' xs'] "IH" forall (n); iIntros "H"; rel_rec_r; rel_pures_r.
    - done.
    - destruct n as [|n]; rel_pures_r; first done.
      replace (Datatypes.S n - 1)%Z with (Z.of_nat n) by lia.
      by iApply "IH".
  Qed.

  Definition lrel_hlist (Cs : list (lrel Σ)) : lrel Σ := LRel (λ v v',
    ∃ xs xs', ⌜length xs = length Cs⌝ ∗ ⌜length xs' = length Cs⌝
      ∗ ⌜v = encode_val xs⌝ ∗ ⌜v' = encode_val xs'⌝
      ∗ [∗ list] n ↦ (C : lrel Σ) ∈ Cs, C (xs!!!n) (xs'!!!n))%I.

  Lemma refines_encode_list (Cs : list (lrel Σ)) (xs xs' : list expr) :
    length xs = length Cs → length xs' = length Cs →
    ([∗ list] n ↦ C ∈ Cs, REL (xs!!!n : expr) << (xs'!!!n : expr) : C) ⊢
    REL dynamic_encode_list xs << dynamic_encode_list xs' : lrel_hlist Cs.
  Proof.
    revert xs xs'.
    induction Cs as [|C Cs IH] => xs xs' Hlen Hlen'.
    - iIntros "_".
      destruct xs; last done.
      destruct xs'; last done.
      rel_pures_l. rel_pures_r.
      rel_values.
      iModIntro. iExists [], []. auto.
    - iIntros "Hrefines".
      destruct xs as [|x xs]; first done.
      destruct xs' as [|x' xs']; first done.
      simplify_eq.
      rewrite big_sepL_cons.
      iDestruct "Hrefines" as "[Hrefine Hrefines]".
      (* Finished transaction in 2.453 secs (2.437u,0.015s) *)
      setoid_rewrite lookup_total_cons.
      simpl.
      rel_bind_l (dynamic_encode_list xs).
      rel_bind_r (dynamic_encode_list xs').
      iApply (refines_bind with "[Hrefines]").
      { by iApply (IH with "Hrefines"). }
      iIntros (xsv xsv') "Hrefines".
      simpl.
      rel_bind_l x. rel_bind_r x'.
      iApply (refines_bind with "Hrefine").
      iIntros (xv xv') "Hrefine".
      simpl. rel_pures_l. rel_pures_r.
      rel_values. iModIntro.
      iDestruct "Hrefines" as (xs_meta xs_meta')
        "(%Hlen_meta & %Hlen_meta' & %Hencode & %Hencode' & Hrefines)".
      iExists (xv::xs_meta), (xv'::xs_meta').
      subst.
      do 4 (iSplit; first by simpl; auto).
      rewrite big_sepL_cons.
      setoid_rewrite lookup_total_cons.
      iFrame.
  Qed.

  Lemma refines_list_nth Cs (n : nat) (e e' : expr) :
    (REL e << e' : lrel_hlist Cs) -∗
    REL list_nth #n e << list_nth #n e' : (Cs!!!n).
  Proof.
    iIntros "He".
    rel_bind_l e; rel_bind_r e'.
    iApply (refines_bind with "He").
    iIntros (v v') "(%xs & %xs' & %Hlen & %Hlen' & -> & -> & Hxs) /=".
    iApply refines_list_nth_l. iApply refines_list_nth_r.
    rel_values. iModIntro.
    destruct (Cs !! n) as [C|] eqn:HC.
    - rewrite (list_lookup_total_correct _ _ _ HC).
      by iApply (big_sepL_lookup _ _ _ _ HC with "Hxs").
    - rewrite list_lookup_total_alt HC /=. done.
  Qed.
End refine_rules.
