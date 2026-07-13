From stdpp Require Export ssreflect namespaces.

Definition fresh_namespace (N : namespace) :=
  match N.(namespace_car) with
  | [] => Namespace []
  | p::ps => Namespace ((p+1)%positive::ps)
  end.

Lemma ndot_ne `{Countable A} N (x : A) : N.@x ≠ N.
Proof.
  rewrite namespaces.ndot_unseal /namespaces.ndot_def.
  destruct N as [xs].
  simpl. intros HFalse. injection HFalse as HFalse.
  apply (f_equal length) in HFalse.
  rewrite length_cons in HFalse.
  lia.
Qed.

Lemma fresh_namespace_disjoint N :
  N ≠ nroot → N ## fresh_namespace N.
Proof.
  destruct N as [ [|x xs]]; first done.
  intros _ ?.
  rewrite /up_close namespaces.nclose_unseal /namespaces.nclose_def /=.
  rewrite !elem_coPset_suffixes.
  intros [qx ->] [qy Hqy].
  apply positives_flatten_suffix_eq in Hqy; last by simpl.
  injection Hqy as ?. lia.
Qed.

Definition fresh_namespace2 (N1 N2 : namespace) :=
  match last (N1.(namespace_car)), last (N2.(namespace_car)) with
  | Some p1, Some p2 => Namespace [(p1+p2)%positive]
  | _,_ => Namespace []
  end.

Lemma fresh_namespace2_disjoint N1 N2 :
  N1 ## N2 → N1 ## fresh_namespace2 N1 N2 ∧ N2 ## fresh_namespace2 N1 N2.
Proof.
  intros Hdisj.
  destruct N1 as [xs1]. destruct xs1 as [|x1 xs1 _] using rev_ind.
  { exfalso.
    rewrite -/nroot /disjoint /ndisjoint
      -/(@up_close namespace coPset nclose) nclose_nroot in Hdisj.
    apply disjoint_top_l_L in Hdisj.
    revert Hdisj.
    apply nclose_non_empty. }
  destruct N2 as [xs2]. destruct xs2 as [|x2 xs2 _] using rev_ind.
  { exfalso.
    rewrite -/nroot /disjoint /ndisjoint
      -/(@up_close namespace coPset nclose) nclose_nroot in Hdisj.
    apply disjoint_top_r_L in Hdisj.
    revert Hdisj.
    apply nclose_non_empty. }
  rewrite /fresh_namespace2 /= !last_snoc /=. split.
  - intros ?.
    rewrite /up_close namespaces.nclose_unseal /namespaces.nclose_def /=.
    rewrite !elem_coPset_suffixes.
    intros [qx ->] [qy Hqy].
    rewrite positives_flatten_app assoc in Hqy.
    apply positives_flatten_suffix_eq in Hqy; last by simpl.
    injection Hqy as ?. lia.
  - intros ?.
    rewrite /up_close namespaces.nclose_unseal /namespaces.nclose_def /=.
    rewrite !elem_coPset_suffixes.
    intros [qx ->] [qy Hqy].
    rewrite positives_flatten_app assoc in Hqy.
    apply positives_flatten_suffix_eq in Hqy; last by simpl.
    injection Hqy as ?. lia.
Qed.
