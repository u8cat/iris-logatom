From stdpp Require Import prelude gmap ssreflect.

Section bdmap.
  Context {V : Type}.

  Definition seqM (v : V) (m len : nat) : gmap nat V :=
    list_to_map ((λ i, (i, v)) <$> seq m len).

  Lemma size_seqM v m len : size (seqM v m len) = len.
  Proof.
    rewrite /seqM map_size_list_to_map.
    - rewrite length_fmap. apply length_seq.
    - rewrite -list_fmap_compose.
      apply NoDup_fmap; [by intros x y | apply NoDup_seq].
  Qed.

  Lemma seqM_empty v m : seqM v m 0 = ∅.
  Proof. rewrite /seqM /seq //. Qed.

  Lemma seqM_insert v m len : seqM v m (S len) = <[m:=v]> (seqM v (S m) (len)).
  Proof.
    rewrite /seqM -cons_seq.
    rewrite fmap_cons list_to_map_cons //.
  Qed.

  Lemma lookup_seqM_Some v m len i : seqM v m len !! i = Some v ↔ m ≤ i < m + len.
  Proof.
    rewrite /seqM.
    rewrite -elem_of_list_to_map. 2: {
      rewrite -list_fmap_compose.
      apply NoDup_fmap; [by intros x y | apply NoDup_seq].
    }
    rewrite list_elem_of_fmap.
    rewrite -elem_of_seq.
    split.
    - intros (i' & Heq & Helem_of).
      by simplify_eq.
    - intros Helem_of. by exists i.
  Qed.

  Lemma lookup_seqM_Some_eq v v' m len i : seqM v m len !! i = Some v' → v = v'.
  Proof.
    intros Hlookup.
    rewrite /seqM in Hlookup.
    apply elem_of_list_to_map_2 in Hlookup.
    apply list_elem_of_fmap in Hlookup as (y & Heq & _).
    by simplify_eq.
  Qed.

  Lemma lookup_seqM_None v m len i : seqM v m len !! i = None ↔ i< m ∨ m + len ≤ i.
  Proof.
    assert (i < m ∨ m + len ≤ i ↔ ¬ (m≤i<m+len)) as -> by lia.
    assert (seqM v m len !! i = None ↔ (seqM v m len !! i ≠ Some v)) as ->. {
      split.
      - by intros ->.
      - intros Hneq.
        destruct (seqM v m len !! i) eqn:Hlookup; last done.
        by apply lookup_seqM_Some_eq in Hlookup as ->.
    }
    apply not_iff_compat.
    apply lookup_seqM_Some.
  Qed.

  Lemma seqM_union v m len1 len2 : 0 ≤ len1 → 0 ≤ len2 →
    seqM v m (len1 + len2) = seqM v m len1 ∪ seqM v (m + len1) len2.
  Proof.
    intros Hlen1 Hlen2.
    rewrite /seqM.
    rewrite seq_app; [|assumption..].
    by rewrite fmap_app list_to_map_app.
  Qed.

  Lemma seqM_S v m i : seqM v m (S i) = <[m + i := v]> (seqM v m i).
  Proof.
    rewrite /seqM.
    rewrite seq_S fmap_app list_to_map_app.
    rewrite list_to_map_cons list_to_map_nil insert_empty.
    rewrite insert_union_singleton_r; first done.
    apply not_elem_of_list_to_map.
    rewrite -list_fmap_compose.
    rewrite list_elem_of_fmap.
    intros (y & Heq & Hfalse).
    simpl in Heq. subst y.
    apply elem_of_seq in Hfalse.
    lia.
  Qed.

  Lemma Forall_seqM P v m len: map_Forall P (seqM v m len) ↔ (∀ i, m ≤ i < m+len → P i v).
  Proof.
    induction len as [| len IHlen].
    - rewrite seqM_empty.
      split.
      + intros _??. lia.
      + intros _. apply map_Forall_empty.
    - rewrite seqM_S.
      rewrite map_Forall_insert. 2: {
        apply lookup_seqM_None. lia.
      }
      split.
      + intros [Htail Hfront] i Hi.
        destruct (decide (i=m+len)) as [-> | Hi_ne]; first assumption.
        eapply map_Forall_lookup_1; first exact Hfront.
        apply lookup_seqM_Some. lia.
      + intros Hforall.
        split; first auto with lia.
        apply IHlen => i Hi.
        auto with lia.
  Qed.
End bdmap.
