From stdpp Require Import ssreflect.
From stdpp Require Export list gmap.

Section facts.
  Context {A : Type}.
  Implicit Types (i j : nat) (l m n : list A) (x y : A).

  Definition list_to_imap i l : gmap nat A :=
  list_to_map (imap (λ j x, (i+j, x)) l).

  Lemma list_to_imap_nil i : list_to_imap i [] = ∅.
  Proof. rewrite /list_to_imap imap_nil list_to_map_nil //. Qed.

  Lemma list_to_imap_cons i x l :
    list_to_imap i (x::l) = <[i:=x]> (list_to_imap (S i) l).
  Proof.
    rewrite /list_to_imap imap_cons list_to_map_cons right_id_L.
    do 2 f_equal. apply imap_ext => j1 j2 _ /=.
    f_equal. lia.
  Qed.

  Lemma list_to_imap_snoc i x l :
    list_to_imap i (l++[x]) = <[i + length l := x]> (list_to_imap i l).
  Proof.
    rewrite /list_to_imap imap_app /= list_to_map_snoc.
    - rewrite right_id_L //.
    - rewrite right_id_L fmap_imap.
      rewrite (imap_ext _ (λ (n : nat) _, id (i + n))) //.
      rewrite imap_seq list_fmap_id.
      rewrite elem_of_seq.
      lia.
  Qed.

  Lemma list_to_imap_0_snoc x l :
    list_to_imap 0 (l++[x]) = <[length l := x]> (list_to_imap 0 l).
  Proof.
    change (length l) with (0 + length l).
    apply list_to_imap_snoc.
  Qed.

  Lemma list_to_imap_app i l1 l2 :
    list_to_imap i (l1++l2) = list_to_imap i l1 ∪ list_to_imap (length l1 + i) l2.
  Proof.
    rewrite /list_to_imap imap_app list_to_map_app.
    do 2 f_equal. apply imap_ext => j1 j2 _ /=.
    f_equal. lia.
  Qed.

  Lemma lookup_list_to_imap i l j :
    list_to_imap i l !! (i + j) = l !! j.
  Proof.
    rewrite /list_to_imap.
    destruct (l !! j) as [x|] eqn:Hlookup.
    - apply elem_of_list_to_map_1.
      + rewrite fmap_imap.
        rewrite (imap_ext _ (λ (n : nat) _, id (i + n))) //.
        rewrite imap_seq list_fmap_id.
        apply NoDup_seq.
      + apply (list_elem_of_lookup_2 _ j).
        rewrite list_lookup_imap Hlookup //.
    - apply not_elem_of_list_to_map_1.
      rewrite fmap_imap.
      rewrite (imap_ext _ (λ (n : nat) _, id (i + n))) //.
      rewrite imap_seq list_fmap_id.
      rewrite elem_of_seq.
      apply lookup_ge_None_1 in Hlookup.
      lia.
  Qed.

  Lemma lookup_list_to_imap_0 l i :
    list_to_imap 0 l !! i = l !! i.
  Proof. by rewrite -(lookup_list_to_imap 0 l i) left_id_L. Qed.
End facts.
