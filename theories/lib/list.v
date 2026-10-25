(* list_relations.v: addtional relations on list *)
(* TODO: prove more properties and upstream to stdpp. *)

From stdpp Require Import ssreflect.
From stdpp Require Export list.

Definition substr {A} : relation (list A) := λ l1 l2, ∃ k1 k2, l2 = k1 ++ l1 ++ k2.
Infix "`substr_of`" := substr (at level 70) : stdpp_scope.
Global Hint Extern 0 (_ `substr_of` _) => reflexivity : core.

(* Takes the longest prefix of l satisfying P, returns the prefix and the reminder of the list. *)
Fixpoint take_while {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) : list A * list A :=
  match l with
  | [] => ([], [])
  | x::l =>
    if decide (P x) then
      let (p,np) := take_while P l in (x::p,np)
    else
      ([],x::l)
  end.

Definition BeginWith {A} (P : A → Prop) (l : list A) :=
  match l with
  | [] => False
  | x::_ => P x
  end.

Lemma zip_cons {A B} (a : A) (l : list A) (b : B) (k : list B) :
  zip (a::l) (b::k) = (a,b)::zip l k.
Proof. done. Qed.
Lemma zip_app {A B} (l1 l2 : list A) (k1 k2 : list B) :
  length l1 = length k1 → zip (l1++l2) (k1++k2) = zip l1 k1 ++ zip l2 k2.
Proof.
  intros Hlen.
  pose (f:= (λ (a : A)(b : B), (a,b))).
  assert (Hidf: ∀ (l : list A) (k : list B), zip l k = uncurry f <$> zip l k).
  { intros l k. apply list_eq => i.
    rewrite list_lookup_fmap. by destruct (zip l k !! i) as [[??]|]. }
  rewrite {1}Hidf -zip_with_zip zip_with_app //.
Qed.
(* TODO: use [replicate] instread *)
Lemma repeat_S {A} (a : A) n :
  repeat a (S n) = a::repeat a n.
Proof. done. Qed.

Section general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

Lemma singleton_length_inv l : length l = 1 → ∃ x, l = [x].
Proof. destruct l as [|x [|??]]; naive_solver. Qed.

Lemma filter_False_nil (P : A → Prop) `{∀ x, Decision (P x)} l :
  Forall (λ x, ¬ P x) l → filter P l = [].
Proof.
  induction l as [|x l IHl].
  - intros _. rewrite filter_nil //.
  - intros HnP. rewrite Forall_cons in HnP.
    destruct HnP as [HnPx HnPl].
    rewrite filter_cons_False; auto.
Qed.

Lemma filter_False_nil' (P : A → Prop) `{∀ x, Decision (P x)} l :
  Forall P l → filter (λ x, ¬ P x) l = [].
Proof.
  induction l as [|x l IHl].
  - intros _. rewrite filter_nil //.
  - intros HnP. rewrite Forall_cons in HnP.
    destruct HnP as [HnPx HnPl].
    rewrite filter_cons_False; auto.
Qed.

Lemma list_filter_comm (P1 P2 : A → Prop) `{∀ x, Decision (P1 x)} `{∀ x, Decision (P2 x)} l :
  filter P1 (filter P2 l) = filter P2 (filter P1 l).
Proof.
  rewrite !list_filter_filter.
  apply list_filter_iff => x.
  naive_solver.
Qed.

(* Useful lemma found by Claude Opus 4.7 (1M context, xhigh effort, v2.1.111) *)
Lemma list_filter_ext (P1 P2 : A → Prop) `{!∀ x, Decision (P1 x)} `{!∀ x, Decision (P2 x)} l :
  (∀ x, x ∈ l → (P1 x ↔ P2 x)) → filter P1 l = filter P2 l.
Proof.
  induction l as [|a l IH]; first done.
  intros Hiff.
  assert (HPQ : P1 a ↔ P2 a) by (apply Hiff; set_solver).
  destruct (decide (P1 a)), (decide (P2 a)).
  - rewrite !filter_cons_True //. f_equal. apply IH. intros x Hx. apply Hiff. set_solver.
  - exfalso. tauto.
  - exfalso. tauto.
  - rewrite !filter_cons_False //. apply IH. intros x Hx. apply Hiff. set_solver.
Qed.

Lemma prefix_filter (P : A → Prop) `{∀ x, Decision (P x)} l1 l2 :
  l1 `prefix_of` l2 →
  filter P l1 `prefix_of` filter P l2.
Proof.
  intros [k ->]. rewrite !filter_app.
  by exists (filter P k).
Qed.

Lemma filter_app_inv (P : A → Prop) `{∀ x, Decision (P x)} l1a l1b l2 :
  l1a ++ l1b = filter P l2 →
  ∃ l2a l2b, l2 = l2a ++ l2b ∧ l1a = filter P l2a ∧ l1b = filter P l2b.
Proof.
  revert l1a l1b. induction l2 as [|y l2 IH] => l1a l1b Hfilter.
  - exists [], []. rewrite filter_nil in Hfilter. rewrite filter_nil.
    eauto using app_nil_l_inv, app_nil_r_inv.
  - rewrite filter_cons in Hfilter. case_decide.
    + destruct l1a as [|x l1a].
      * exists [], (y::l2).
        rewrite left_id_L filter_nil.
        do 2 (split; first done).
        rewrite left_id_L in Hfilter.
        rewrite filter_cons_True //.
      * rewrite -app_comm_cons in Hfilter.
        injection Hfilter as -> Hfilter.
        destruct (IH _ _ Hfilter) as (l2a & l2b & -> & -> & ->).
        exists (y::l2a), l2b.
        rewrite -app_comm_cons filter_cons_True //.
    + destruct (IH _ _ Hfilter) as (l2a & l2b & -> & -> & ->).
      exists (y::l2a), l2b.
      rewrite -app_comm_cons filter_cons_False //.
Qed.

Lemma prefix_substr l1 l2 : l1 `prefix_of` l2 → l1 `substr_of` l2.
Proof. intros [k2 ->]. exists [], k2. done. Qed.

Lemma substr_nil l : [] `substr_of` l.
Proof. by exists [], l. Qed.

Lemma substr_app_l l1 l2 l : (l1++l2) `substr_of` l → l1 `substr_of` l.
Proof. intros (k1 & k2 & ->). exists k1, (l2++k2). rewrite -!assoc //. Qed.

Lemma substr_app_r l1 l2 l : (l1++l2) `substr_of` l → l2 `substr_of` l.
Proof. intros (k1 & k2 & ->). exists (k1++l1), k2. rewrite -!assoc //. Qed.

Lemma substr_filter (P : A → Prop) `{∀ x, Decision (P x)} l1 l2 :
  l1 `substr_of` l2 → filter P l1 `substr_of` filter P l2.
Proof.
  intros (k1 & k2 & ->). rewrite !filter_app.
  by exists (filter P k1), (filter P k2).
Qed.

Lemma substr_length l1 l2 :
  l1 `substr_of` l2 → length l1 ≤ length l2.
Proof. intros (k1 & k2 & ->). rewrite !length_app. lia. Qed.

Lemma elem_of_substr l1 l2 x :
  x ∈ l1 → l1 `substr_of` l2 → x ∈ l2.
Proof. intros Hin (la & lb & ->). set_solver. Qed.

Lemma take_while_app_1_2 (P : A → Prop) `{∀ x, Decision (P x)} l :
  l = (take_while P l).1 ++ (take_while P l).2.
Proof.
  induction l as [|x l IHl]; first done.
  simpl. destruct (decide (P x)); last done.
  replace ((let (p, np) := take_while P l in (x :: p, np)).1) with (x::(take_while P l).1)
    by by destruct (take_while P l).
  replace ((let (p, np) := take_while P l in (x :: p, np)).2) with (take_while P l).2
    by by destruct (take_while P l).
  rewrite -app_comm_cons -IHl //.
Qed.

Lemma take_while_1_Forall (P : A → Prop) `{∀ x, Decision (P x)} l :
  Forall P ((take_while P l).1).
Proof.
  induction l as [|x l IHl]; first done.
  simpl. destruct (decide (P x)); last done.
  replace ((let (p, np) := take_while P l in (x :: p, np)).1) with (x::(take_while P l).1)
    by by destruct (take_while P l).
  rewrite Forall_cons //.
Qed.

Lemma take_while_2_not_BeginWith (P : A → Prop) `{∀ x, Decision (P x)} l :
  ¬ BeginWith P ((take_while P l).2).
Proof.
  induction l as [|x l IHl]; first auto.
  simpl. destruct (decide (P x)); last done.
  replace ((let (p, np) := take_while P l in (x :: p, np)).2) with (take_while P l).2
    by by destruct (take_while P l).
  done.
Qed.

Lemma list_elem_of_weaken x l1 l2 :
  x ∈ l1 → l1 ⊆ l2 → x ∈ l2.
Proof.
  intros Hin Hsubset.
  by apply Hsubset.
Qed.

Lemma list_elem_of_filter_1 (P : A → Prop) `{∀ x, Decision (P x)} l x :
  x ∈ filter P l → x ∈ l.
Proof. by intros [??]%list_elem_of_filter. Qed.

Lemma list_elem_of_filter_2 (P : A → Prop) `{∀ x, Decision (P x)} l x :
  P x → x ∈ l → x ∈ filter P l.
Proof. intros ??. apply list_elem_of_filter. split; done. Qed.

Local Lemma list_find_exists_Some_ind i (P : A → Prop) `{∀ x, Decision (P x)} l :
  (∃ x, x ∈ l ∧ P x) →
  (∀ j x, l !! j = Some x → j < (length l - i) → ¬ P x) →
  ∃ i y, list_find P l = Some (i, y).
Proof.
  intro Hex.
  induction i as [|i IH].
  { intros HFalse. exfalso.
    destruct Hex as (x & [j Hin]%list_elem_of_lookup_1 & HPx).
    refine (HFalse _ _ Hin _ HPx).
    apply lookup_lt_Some in Hin.
    lia. }
  intros HnotP.
  assert (length l ≠ 0).
  { intros HFalse. destruct Hex as (? & ? & _).
    destruct l; first set_solver.
    simpl in HFalse. lia. }
  clear Hex.
  opose proof (lookup_lt_is_Some_2 l (length l - S i) _) as (x & Hlookup); first lia.
  destruct (decide (P x)) as [HPx | HnotPx].
  - exists (length l - S i), x.
    apply list_find_Some.
    split_and!; done.
  - apply IH. intros j y Hlookup' Hk_gt.
    destruct (decide (j = length l - S i)).
    + simplify_eq. done.
    + refine (HnotP _ _ Hlookup' _).
      lia.
Qed.

Lemma list_find_exists_Some (P : A → Prop) `{∀ x, Decision (P x)} l :
  (∃ x, x ∈ l ∧ P x) → ∃ i y, list_find P l = Some (i, y).
Proof.
  intros Hex.
  apply (list_find_exists_Some_ind (length l)); first done.
  intros ????.
  lia.
Qed.
End general_properties.

Section omap.
  Context {A B : Type} (f : A → option B).
  Implicit Types l : list A.

  Lemma omap_nil :
    omap f [] = [].
  Proof. by simpl. Qed.

  Lemma omap_cons a l :
    omap f (a::l) = match f a with
      | Some b => b::omap f l
      | None => omap f l
      end.
  Proof. by simpl. Qed.

  Lemma omap_cons_Some a b l :
    f a = Some b →
    omap f (a::l) = b::omap f l.
  Proof. intros Hf. rewrite omap_cons Hf //. Qed.

  Lemma omap_cons_None a l :
    f a = None →
    omap f (a::l) = omap f l.
  Proof. intros Hf. rewrite omap_cons Hf //. Qed.
End omap.

Section total_lookup.
  Context `{!Inhabited A}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.

  Lemma lookup_total_cons x l i :
    (x::l)!!!i = match i with
                 | 0 => x
                 | S i => l!!!i
                 end.
  Proof.
    destruct i; first done.
    rewrite lookup_total_cons_ne_0 //.
  Qed.
End total_lookup.
