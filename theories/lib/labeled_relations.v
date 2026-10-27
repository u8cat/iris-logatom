From stdpp Require Import ssreflect.

(** A labeled relation: a relation on [A], but each pair (a₁,a₂) is marked by
an optional label of type [B]. This is typically used from transition
relations (e.g., a step in an operational semantics), and the extra label is
used to record the side-effect of a transition. *)
Definition relationL A B := A → A → list B → Prop.

Class SingletonRelationL {A B} (R : relationL A B) :=
  SingletonRelationL_length : ∀ x y l, R x y l → length l = 1.

Class OptionRelationL {A B} (R : relationL A B) :=
  OptionRelationL_length : ∀ x y l, R x y l → length l ≤ 1.

Global Instance singleton_option_relationL {A B} (R : relationL A B) :
  SingletonRelationL R → OptionRelationL R.
Proof.
  intros ? x y l HR.
  pose proof (SingletonRelationL_length x y l HR).
  lia.
Qed.

Section definitions.
  Context `(R : relationL A B).
  Implicit Types (x y z : A) (l m : list B) (n : nat).

  (** labeled [red] *)
  Definition redL x := ∃ y l, R x y l.

  (** labeled [nf] *)
  Definition nfL x := ¬redL x.

  (*** labeled [rtc] *)
  Inductive rtcL : relationL A B :=
    | rtcL_refl x : rtcL x x []
    | rtcL_l x y z l m : R x y l → rtcL y z m → rtcL x z (l++m).

  (** labeled [nsteps] *)
  Inductive nstepsL : nat → relationL A B :=
    | nstepsL_O x : nstepsL 0 x x []
    | nstepsL_l n x y z l m : R x y l → nstepsL n y z m → nstepsL (S n) x z (l++m).

  (** labeled [bsteps] *)
  Inductive bstepsL : nat → relationL A B :=
    | bstepsL_refl n x : bstepsL n x x []
    | bstepsL_l n x y z l m : R x y l → bstepsL n y z m → bstepsL (S n) x z (l++m).

  (** labeled [tc] *)
  Inductive tcL : relationL A B :=
    | tcL_once x y l : R x y l → tcL x y l
    | tcL_l x y z l m : R x y l → tcL y z m → tcL x z (l++m).
End definitions.

Global Hint Unfold nfL redL : core.

(** * General theorems *)
Section general.
  Context `{R : relationL A B}.
  Implicit Types (x y z : A) (l : list B) (n : nat).

  Local Hint Constructors rtcL nstepsL bstepsL tcL : core.

  (** ** Results about the labeled reflexive-transitive closure [rtcL] *)
  Lemma rtcL_trans x y z l m : rtcL R x y l → rtcL R y z m → rtcL R x z (l++m).
  Proof. induction 1; [|rewrite -assoc]; eauto. Qed.

  Lemma rtcL_once x y l : R x y l → rtcL R x y l.
  Proof. rewrite -{2}(right_id [] (++) l). eauto. Qed.
  Lemma rtcL_cons x y z b l : R x y [b] → rtcL R y z l → rtcL R x z (b::l).
  Proof. apply (rtcL_l _ _ _ _ [b]). Qed.
  Lemma rtcL_r x y z l m : rtcL R x y l → R y z m → rtcL R x z (l++m).
  Proof.
    intros.
    eapply rtcL_trans; first done.
    by eapply rtcL_once.
  Qed.
  Lemma rtcL_inv x z l : rtcL R x z l →
    x = z ∧ l = [] ∨ ∃ y l1 l2, R x y l1 ∧ rtcL R y z l2 ∧ l = l1++l2.
  Proof. inv 1; eauto 7. Qed.
  Lemma rtcL_ind_l (P : A → list B → Prop) z
    (Prefl : P z []) (Pstep : ∀ x y l m, R x y l → rtcL R y z m → P y m → P x (l++m)) :
    ∀ x l, rtcL R x z l → P x l.
  Proof. induction 1; eauto. Qed.

  Local Lemma rtcL_ind_r_weak (P : A → A → list B → Prop)
      (Prefl : ∀ x, P x x [])
      (Pstep : ∀ x y z l m, rtcL R x y l → R y z m → P x y l → P x z (l++m)) :
    ∀ x z l, rtcL R x z l → P x z l.
  Proof.
    cut (∀ y z m, rtcL R y z m → ∀ x l, rtcL R x y l → P x y l → P x z (l++m)).
    { intros ??? l. change l with ([] ++ l). eauto using rtcL_refl. }
    induction 1.
    - intros ??. rewrite right_id. eauto.
    - intros ??. rewrite assoc. eauto using rtcL_r.
  Qed.
  Lemma rtcL_ind_r (P : A → list B → Prop) (x : A)
    (Prefl : P x []) (Pstep : ∀ y z l m, rtcL R x y l → R y z m → P y l → P z (l++m)) :
    ∀ z l, rtcL R x z l → P z l.
  Proof.
    intros z l p. revert x z l p Prefl Pstep. refine (rtcL_ind_r_weak _ _ _); eauto.
  Qed.
  Lemma rtcL_inv_r x z l : rtcL R x z l →
    x = z ∧ l = [] ∨ ∃ y l1 l2, rtcL R x y l1 ∧ R y z l2 ∧ l = l1++l2.
  Proof. revert z l. apply rtcL_ind_r; eauto 7. Qed.

  Lemma rtcL_nfL x y l : rtcL R x y l → nfL R x → x = y ∧ l = [].
  Proof. destruct 1 as [x|x y1 y2]; [done|]. intros []; eauto. Qed.

  Lemma rtcL_congruence {C} (f : A → C) (R' : relationL C B) x y l :
    (∀ x y l, R x y l → R' (f x) (f y) l) → rtcL R x y l → rtcL R' (f x) (f y) l.
  Proof. induction 2; econstructor; eauto. Qed.

  (** ** Results about [nstepsL] *)
  Lemma nstepsL_once x y l : R x y l → nstepsL R 1 x y l.
  Proof. rewrite -{2}(right_id [] (++) l). eauto. Qed.
  Lemma nstepsL_cons n x y z b l : R x y [b] → nstepsL R n y z l → nstepsL R (S n) x z (b::l).
  Proof. apply (nstepsL_l _ _ _ _ _ [b]). Qed.
  Lemma nstepsL_once_inv x y l : nstepsL R 1 x y l → R x y l.
  Proof. inv 1 as [|?????? Hhead Htail]; inv Htail; by rewrite right_id. Qed.
  Lemma nstepsL_trans n1 n2 x y z l m :
    nstepsL R n1 x y l → nstepsL R n2 y z m → nstepsL R (n1 + n2) x z (l++m).
  Proof. induction 1; simpl; [|rewrite -assoc]; eauto. Qed.
  Lemma nstepsL_r n x y z l m : nstepsL R n x y l → R y z m → nstepsL R (S n) x z (l++m).
  Proof. induction 1; [|rewrite -assoc]; eauto using nstepsL_once. Qed.
  Lemma nstepsL_inv n x z l : nstepsL R (S n) x z l →
    ∃ y l1 l2, R x y l1 ∧ nstepsL R n y z l2 ∧ l = l1++l2.
  Proof. inv 1; eauto 6. Qed.

  Lemma nstepsL_add_inv n m x z l :
    nstepsL R (n + m) x z l → ∃ y l1 l2, nstepsL R n x y l1 ∧ nstepsL R m y z l2 ∧ l = l1++l2.
  Proof.
    revert x l.
    induction n as [|n IH]; intros x l Hx; simpl; [by eauto 7|].
    inv Hx as [|???? l1 l2 ? Hm]. apply IH in Hm as (y'&l3&l4&?&?&->).
    exists y', (l1++l3), l4. rewrite -assoc. eauto.
  Qed.

  Lemma nstepsL_inv_r n x z l : nstepsL R (S n) x z l →
    ∃ y l1 l2, nstepsL R n x y l1 ∧ R y z l2 ∧ l = l1++l2.
  Proof.
    rewrite <- PeanoNat.Nat.add_1_r.
    intros (?&?&?&?&?%nstepsL_once_inv&?)%nstepsL_add_inv; eauto 7.
  Qed.

  Lemma nstepsL_congruence {C} (f : A → C) (R' : relationL C B) n x y l :
    (∀ x y l, R x y l → R' (f x) (f y) l) → nstepsL R n x y l → nstepsL R' n (f x) (f y) l.
  Proof. induction 2; econstructor; eauto. Qed.

  (** ** Results about [bstepsL] *)
  Lemma bstepsL_once n x y l : R x y l → bstepsL R (S n) x y l.
  Proof. rewrite -{2}(right_id [] (++) l). eauto. Qed.
  Lemma bstepsL_cons n x y z b l : R x y [b] → bstepsL R n y z l → bstepsL R (S n) x z (b::l).
  Proof. apply (bstepsL_l _ _ _ _ _ [b]). Qed.
  Lemma bstepsL_add_r n m x y l :
    bstepsL R n x y l → bstepsL R (n + m) x y l.
  Proof. induction 1; simpl; eauto. Qed.
  Lemma bstepsL_weaken n m x y l :
    n ≤ m → bstepsL R n x y l → bstepsL R m x y l.
  Proof.
    intros. rewrite (Nat.le_add_sub n m); auto using bstepsL_add_r.
  Qed.
  Lemma bstepsL_add_l n m x y l :
    bstepsL R n x y l → bstepsL R (m + n) x y l.
  Proof. apply bstepsL_weaken. auto with arith. Qed.
  Lemma bstepsL_S n x y l :  bstepsL R n x y l → bstepsL R (S n) x y l.
  Proof. apply bstepsL_weaken. lia. Qed.
  Lemma bstepsL_trans n1 n2 x y z l m :
    bstepsL R n1 x y l → bstepsL R n2 y z m → bstepsL R (n1 + n2) x z (l++m).
  Proof. induction 1; simpl; [|rewrite -assoc]; eauto using bstepsL_add_l. Qed.
  Lemma bstepsL_r n x y z l m : bstepsL R n x y l → R y z m → bstepsL R (S n) x z (l++m).
  Proof. induction 1; [|rewrite -assoc]; eauto using bstepsL_once. Qed.

  Lemma bstepsL_ind_r (P : nat → A → list B → Prop) (x : A)
    (Prefl : ∀ n, P n x [])
    (Pstep : ∀ n y z l m, bstepsL R n x y l → R y z m → P n y l → P (S n) z (l++m)) :
    ∀ n z l, bstepsL R n x z l → P n z l.
  Proof.
    cut (∀ m y z l2, bstepsL R m y z l2 → ∀ n l1,
      bstepsL R n x y l1 → (∀ m', n ≤ m' ∧ m' ≤ n + m → P m' y l1) → P (n + m) z (l1++l2)).
    { intros help n z l. change n with (0 + n). change l with ([] ++ l). eauto. }
    induction 1 as [|m x' y z l1 m1 p2 p3 IH];
      [intros; rewrite right_id; by eauto with arith|].
    intros n l p1 H. rewrite -plus_n_Sm assoc.
    apply (IH (S n)); [by eauto using bstepsL_r |].
    intros [|k'] [??]; [lia |]. apply Pstep with x'.
    - apply bstepsL_weaken with n; intuition lia.
    - done.
    - apply H; intuition lia.
  Qed.

  Lemma bstepsL_congruence {C} (f : A → C) (R' : relationL C B) n x y l :
    (∀ x y l, R x y l → R' (f x) (f y) l) → bstepsL R n x y l → bstepsL R' n (f x) (f y) l.
  Proof. induction 2; econstructor; eauto. Qed.

  (** ** Results about the labeled transitive closure [tcL] *)
  Lemma tcL_trans x y z l m : tcL R x y l → tcL R y z m → tcL R x z (l++m).
  Proof. induction 1; [|rewrite -assoc]; eauto. Qed.

  Lemma tcL_cons x y z b l : R x y [b] → tcL R y z l → tcL R x z (b::l).
  Proof. apply (tcL_l _ _ _ _ [b]). Qed.
  Lemma tcL_r x y z l m : tcL R x y l → R y z m → tcL R x z (l++m).
  Proof.
    intros.
    eapply tcL_trans; first done.
    by eapply tcL_once.
  Qed.
  Lemma tcL_rtcL_l x y z l m : rtcL R x y l → tcL R y z m → tcL R x z (l++m).
  Proof. induction 1; [|rewrite -assoc]; eauto. Qed.
  Lemma tcL_rtcL_r x y z l m : tcL R x y l → rtcL R y z m → tcL R x z (l++m).
  Proof.
    intros Hxy Hyz. revert x l Hxy.
    induction Hyz.
    - intros ??. rewrite right_id. eauto.
    - intros ??. rewrite assoc. eauto using tcL_r.
  Qed.
  Lemma tcL_rtcL x y l : tcL R x y l → rtcL R x y l.
  Proof. induction 1; eauto using rtcL_once. Qed.

  Local Lemma tcL_ind_r_weak (P : A → A → list B → Prop)
      (Ponce : ∀ x y l, R x y l → P x y l)
      (Pstep : ∀ x y z l m, tcL R x y l → R y z m → P x y l → P x z (l++m)) :
    ∀ x z l, tcL R x z l → P x z l.
  Proof.
    cut (∀ y z m, tcL R y z m →
      ∀ x l, x = y ∧ l = [] ∨ (tcL R x y l ∧ P x y l) → P x z (l++m)).
    { intros ??? l. change l with ([] ++ l). by eauto. }
    induction 1; intros; [|rewrite assoc]; naive_solver eauto using tcL_r.
  Qed.
  Lemma tcL_ind_r (P : A → list B → Prop) (x : A)
    (Prefl : ∀ z l, R x z l → P z l)
    (Pstep : ∀ y z l m, tcL R x y l → R y z m → P y l → P z (l++m)) :
    ∀ z l, tcL R x z l → P z l.
  Proof.
    intros z l p. revert x z l p Prefl Pstep. refine (tcL_ind_r_weak _ _ _); eauto.
  Qed.

  Lemma redL_tcL x : redL (tcL R) x ↔ redL R x.
  Proof.
    split.
    - intros [y [l []]]; eexists; eauto.
    - intros [y [l HR]]. exists y, l. by apply tcL_once.
  Qed.
  Lemma nfL_tcL x : nfL (tcL R) x ↔ nfL R x.
  Proof. unfold nfL. by rewrite redL_tcL. Qed.

  Lemma tcL_congruence {C} (f : A → C) (R' : relationL C B) x y l :
    (∀ x y l, R x y l → R' (f x) (f y) l) → tcL R x y l → tcL R' (f x) (f y) l.
  Proof. induction 2; econstructor; by eauto. Qed.

  (** ** Equivalences between closure operators *)
  Lemma bstepsL_nstepsL n x y l : bstepsL R n x y l ↔ ∃ n', n' ≤ n ∧ nstepsL R n' x y l.
  Proof.
    split.
    - induction 1 as [|n x1 x2 y l1 l2 ?? (n'&?&?)].
      + exists 0; naive_solver eauto with lia.
      + exists (S n'); naive_solver eauto with lia.
    - intros (n'&Hn'&Hsteps). apply bstepsL_weaken with n'; [done|].
      clear Hn'. induction Hsteps; eauto.
  Qed.

  Lemma tcL_nstepsL x y l : tcL R x y l ↔ ∃ n, 0 < n ∧ nstepsL R n x y l.
  Proof.
    split.
    - induction 1 as [|x1 x2 y l1 l2 ?? (n&?&?)].
      { exists 1. eauto using nstepsL_once with lia. }
      exists (S n); eauto using nstepsL_l.
    - intros (n & ? & Hstep). induction Hstep as [|n x1 x2 y l1 l2 ? Hstep]; [lia|].
      destruct Hstep; [rewrite right_id|]; eauto with lia.
  Qed.

  Lemma rtcL_tcL x y l : rtcL R x y l ↔ x = y ∧ l = [] ∨ tcL R x y l.
  Proof.
    split; [|naive_solver eauto using tcL_rtcL].
    induction 1 as [|x y z l m ?? [[-> ->]|?]]; [|rewrite right_id|]; naive_solver.
  Qed.

  Lemma rtcL_nstepsL x y l : rtcL R x y l ↔ ∃ n, nstepsL R n x y l.
  Proof.
    split.
    - induction 1; naive_solver.
    - intros [n Hsteps]. induction Hsteps; naive_solver.
  Qed.
  Lemma rtcL_nstepsL_1 x y l : rtcL R x y l → ∃ n, nstepsL R n x y l.
  Proof. rewrite rtcL_nstepsL. naive_solver. Qed.
  Lemma rtcL_nstepsL_2 n x y l : nstepsL R n x y l → rtcL R x y l.
  Proof. rewrite rtcL_nstepsL. naive_solver. Qed.

  Lemma rtcL_bstepsL x y l : rtcL R x y l ↔ ∃ n, bstepsL R n x y l.
  Proof. rewrite rtcL_nstepsL. setoid_rewrite bstepsL_nstepsL. naive_solver. Qed.
  Lemma rtcL_bstepsL_1 x y l : rtcL R x y l → ∃ n, bstepsL R n x y l.
  Proof. rewrite rtcL_bstepsL. naive_solver. Qed.
  Lemma rtcL_bstepsL_2 n x y l : bstepsL R n x y l → rtcL R x y l.
  Proof. rewrite rtcL_bstepsL. naive_solver. Qed.

End general.

Section option_rel.
  Context `{OptionRelationL A B R}.

  Local Lemma nstepsL_app_inv_aux n x z b l :
    nstepsL R n x z (b::l) → ∃ n1 n2 y, nstepsL R n1 x y [b] ∧ nstepsL R n2 y z l ∧ n = n1 + n2.
  Proof.
    revert x. induction n as [|n IH] => x Hxz.
    - inv Hxz.
    - inv Hxz as [|?? y ? l' m' Hxy Hyz].
      rename select (_ ++ _ = _ :: _) into Heq.
      destruct l' as [|b' [|b'' l']].
      + rewrite left_id in Heq. subst m'.
        destruct (IH  _ Hyz) as (n1 & n2 & w & Hxw & Hwz & Heq).
        exists (S n1), n2, w. split_and!.
        * change [b] with ([]++[b]). by eapply nstepsL_l.
        * assumption.
        * lia.
      + simpl in Heq. injection Heq as -> ->.
        exists 1, n, y. split_and!.
        * by apply nstepsL_once.
        * assumption.
        * lia.
      + exfalso.
        apply OptionRelationL_length in Hxy.
        simpl in Hxy. lia.
  Qed.

  Lemma nstepsL_app_inv n x z l m :
    nstepsL R n x z (l++m) → ∃ n1 n2 y, nstepsL R n1 x y l ∧ nstepsL R n2 y z m ∧ n = n1 + n2.
  Proof.
    revert x l. induction n as [n IH] using (well_founded_ind lt_wf) => x l Hxz.
    destruct l as [|b l].
    - rewrite left_id in Hxz.
      exists 0, n, x. split_and!; auto using nstepsL_O.
    - rewrite -app_comm_cons in Hxz.
      destruct (nstepsL_app_inv_aux _ _ _ _ _ Hxz) as (n1 & n2 & y & Hxy & Hyz & ->).
      destruct n1 as [|n1]; first by inv Hxy.
      destruct (IH n2 (ltac:(lia)) _ _ Hyz) as (n3 & n4 & w & Hyw & Hwz & ->).
      exists (S n1 + n3), n4, w. split_and!.
      + change (b::l) with ([b]++l).
        by eapply nstepsL_trans.
      + assumption.
      + lia.
  Qed.

  Lemma rtcL_app_inv x z l m :
    rtcL R x z (l++m) → ∃ y, rtcL R x y l ∧ rtcL R y z m.
  Proof.
    intros [n Hxz]%rtcL_nstepsL.
    destruct (nstepsL_app_inv _ _ _ _ _ Hxz) as (?&? & y & Hxy & Hyz & _).
    eauto using rtcL_nstepsL_2.
  Qed.

  Lemma nstepsL_length_le n x y l:
    nstepsL R n x y l → length l ≤ n.
  Proof.
    revert x y l. induction n as [|n IH] => x y l HnstepsL; first by inv HnstepsL.
    inv HnstepsL as [|?????? HR HnstepsL'].
    apply OptionRelationL_length in HR.
    apply IH in HnstepsL'.
    rewrite length_app. lia.
  Qed.

  Lemma bstepsL_app_inv n x z l m :
    bstepsL R n x z (l++m) → ∃ n1 n2 y, bstepsL R n1 x y l ∧ bstepsL R n2 y z m ∧ n = n1 + n2.
  Proof.
    intros (n' & Hlt & Hxz)%bstepsL_nstepsL.
    destruct (nstepsL_app_inv _ _ _ _ _ Hxz) as (n1 & n2 & y & Hxy & Hyz & Heq).
    exists n1, (n2 + n-n'), y.
    split_and!.
    - apply bstepsL_nstepsL. eauto.
    - apply bstepsL_nstepsL.
      exists n2; auto with lia.
    - lia.
  Qed.

  Lemma bstepsL_length_le n x y l:
    bstepsL R n x y l → length l ≤ n.
  Proof.
    intros (? & ? & ?%nstepsL_length_le)%bstepsL_nstepsL.
    lia.
  Qed.
End option_rel.

Section singleton_rel.
  Context `{SingletonRelationL A B R}.

  Lemma rtcL_nil_inv x y :
    rtcL R x y [] → x = y.
  Proof.
    intros [[-> _]|(? & l1 & l2 & HR & _ & Hfalse)]%rtcL_inv; first done.
    apply SingletonRelationL_length in HR.
    destruct l1; first done.
    apply (f_equal length) in Hfalse.
    simpl in Hfalse. lia.
  Qed.

  Lemma rtcL_singleton_inv x y b :
    rtcL R x y [b] → R x y [b].
  Proof.
    intros [[-> Hfalse]|(? & l1 & l2 & HR & HrtcL & Heq)]%rtcL_inv; first done.
    apply SingletonRelationL_length in HR as Hlen.
    destruct l1 as [|b' l1]; first done.
    rewrite -app_comm_cons in Heq.
    injection Heq as <- Hnil.
    symmetry in Hnil.
    apply app_eq_nil in Hnil as [-> ->].
    apply rtcL_nil_inv in HrtcL as ->.
    assumption.
  Qed.

  Lemma rtcL_cons_inv x z b l :
    rtcL R x z (b::l) → ∃ y, R x y [b] ∧ rtcL R y z l.
  Proof.
    change (b::l) with ([b]++l).
    intros (y & Hxy & Hyz)%rtcL_app_inv.
    exists y. split; last assumption.
    by apply rtcL_singleton_inv.
  Qed.

  Lemma rtcL_snoc_inv x z b l :
    rtcL R x z (l++[b]) → ∃ y, rtcL R x y l ∧ R y z [b].
  Proof.
    intros (y & Hxy & Hyz)%rtcL_app_inv.
    exists y. split; first assumption.
    by apply rtcL_singleton_inv.
  Qed.

  Lemma nstepsL_length_eq n x y l :
    nstepsL R n x y l → length l = n.
  Proof.
    revert x y l. induction n as [|n IH] => x y l HnstepsL; first by inv HnstepsL.
    inv HnstepsL as [|?????? HR HnstepsL'].
    apply SingletonRelationL_length in HR.
    apply IH in HnstepsL'.
    rewrite length_app. lia.
  Qed.

  Lemma nstepsL_nil_inv n x y :
    nstepsL R n x y [] → x = y.
  Proof.
    intros HnstepsL.
    apply nstepsL_length_eq in HnstepsL as Hlen.
    simpl in Hlen; subst n.
    by inv HnstepsL.
  Qed.

  Lemma nstepsL_singleton_inv n x y b :
    nstepsL R n x y [b] → R x y [b].
  Proof.
    intros HnstepsL.
    apply nstepsL_length_eq in HnstepsL as Hlen.
    simpl in Hlen; subst n.
    inv HnstepsL.
    rename select (nstepsL _ _ _ _ _) into HnstepsL.
    inv HnstepsL. by rewrite right_id.
  Qed.

  Lemma nstepsL_cons_inv n x z b l :
    nstepsL R (S n) x z (b::l) → ∃ y, R x y [b] ∧ nstepsL R n y z l.
  Proof.
    change (b::l) with ([b]++l).
    intros (n1 & n2 & y & Hxy & Hyz & Heq)%nstepsL_app_inv.
    apply nstepsL_length_eq in Hxy as Hlen.
    simpl in Hlen; subst n1.
    apply nstepsL_singleton_inv in Hxy.
    assert (n2 = n) as -> by lia.
    eauto.
  Qed.

  Lemma nstepsL_snoc_inv n x z b l :
    nstepsL R (S n) x z (l++[b]) → ∃ y, nstepsL R n x y l ∧ R y z [b].
  Proof.
    intros (n1 & n2 & y & Hxy & Hyz & Heq)%nstepsL_app_inv.
    apply nstepsL_length_eq in Hyz as Hlen.
    simpl in Hlen; subst n2.
    apply nstepsL_singleton_inv in Hyz.
    assert (n1 = n) as -> by lia.
    eauto.
  Qed.

  Lemma bstepsL_nil_inv n x y :
    bstepsL R n x y [] → x = y.
  Proof.
    intros (? & _ & HnstepsL)%bstepsL_nstepsL.
    by eapply nstepsL_nil_inv.
  Qed.

  Lemma bstepsL_singleton_inv n x y b :
    bstepsL R n x y [b] → R x y [b].
  Proof.
    intros (? & _ & HnstepsL)%bstepsL_nstepsL.
    by eapply nstepsL_singleton_inv.
  Qed.

  Lemma bstepsL_cons_inv n x z b l :
    bstepsL R (S n) x z (b::l) → ∃ y, R x y [b] ∧ bstepsL R n y z l.
  Proof.
    change (b::l) with ([b]++l).
    intros (n1 & n2 & y & Hxy & Hyz & Heq)%bstepsL_app_inv.
    apply bstepsL_length_le in Hxy as Hlen.
    simpl in Hlen.
    apply bstepsL_singleton_inv in Hxy.
    exists y. split; first done.
    eapply bstepsL_weaken; last done.
    lia.
  Qed.

  Lemma bstepsL_snoc_inv n x z b l :
    bstepsL R (S n) x z (l++[b]) → ∃ y, bstepsL R n x y l ∧ R y z [b].
  Proof.
    intros (n1 & n2 & y & Hxy & Hyz & Heq)%bstepsL_app_inv.
    apply bstepsL_length_le in Hyz as Hlen.
    simpl in Hlen.
    apply bstepsL_singleton_inv in Hyz.
    exists y. split; last done.
    eapply bstepsL_weaken; last done.
    lia.
  Qed.
End singleton_rel.
