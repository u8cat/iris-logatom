From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Export bag.base.
From iris_logatom.pure_logic.aspect.stack Require Import base.

(* The premise of the trace-level stack theorem in the style of the TS-stack proof (Dodds,
   Haas, and Kirsch, POPL'15, Section 5.2), an alternative to the insert-remove relation of
   stack/base.v.

   Besides the match [m] (push, pop) of the bag theory, whose order is the remove order rr,
   the prover records points [pts] in the order they happen: the moment a push becomes
   visible (TS stack: its SP-pool insertion) and the moment a pop starts looking for an
   element (TS stack: getStart). A push is visible to a pop (vis) if its point is before
   the pop's point; a started pop is before every push without an earlier point. Points
   and calls/returns need no side condition; the LIFO condition (Lemma 3, condition 2) is
   checked once, when a pop commits, because everything it mentions has its point before
   the pop's point. *)

Definition pt_before (pts : list positive) : relation positive := λ a b,
  ∃ i j, i < j ∧ pts !! i = Some a ∧ pts !! j = Some b.

Section relations.
  Context (ts : list (positive * trace)) (pts : list positive).

  Definition vis_tr : relation positive := λ a b,
    (a ∈ push_of_trace ts ∧ b ∈ pop_of_trace ts ∧ pt_before pts a b) ∨
    (a ∈ pop_of_trace ts ∧ a ∈ pts ∧ b ∈ push_of_trace ts ∧ ¬ pt_before pts b a).

  (* the derived order ts, Definition 6 of the paper *)
  Definition ts_tr : relation positive := λ a b,
    pre_of_trace ts a b ∨ (∃ c, pre_of_trace ts a c ∧ vis_tr c b) ∨
    (∃ d c, pre_of_trace ts a d ∧ vis_tr d c ∧ vis_tr c b).
End relations.

Record I_stack_vis_pre ts m pts : Prop := {
  isv_valid : valid_match ts m;
  isv_empty : per_tag_pop_empty_sound ts m;
  isv_nodup : NoDup pts;
  isv_called τ : τ ∈ pts → τ ∈ ts.*1;
  (* points are inside the operations' intervals *)
  isv_pre a b : pre_of_trace ts a b → a ∈ pts → b ∈ pts → pt_before pts a b;
  isv_push_ret x : x ∈ push_of_trace ts → x ∈ (filter (is_ret ∘ snd) ts).*1 → x ∈ pts;
  isv_pop_pt p : p ∈ m.*2 → p ∈ pts;
  (* rr, the order of [m], extends precedence *)
  isv_rr i j b p a q : m !! i = Some (b, p) → m !! j = Some (a, q) → pre_of_trace ts p q → i < j;
  (* condition 2 of Lemma 3: a push that is ts-after a and visible to a's pop is popped
     earlier *)
  isv_lifo j a pa b : m !! j = Some (a, pa) → pre_of_trace ts a pa → ts_tr ts pts a b →
    b ∈ push_of_trace ts → pt_before pts b pa → ∃ i pb, i < j ∧ m !! i = Some (b, pb);
}.

Definition I_stack_vis ts := ∃ m pts, I_stack_vis_pre ts m pts.

(* ====================================================================== *)
(* Points.                                                                *)
(* ====================================================================== *)

Lemma pt_before_elem pts a b : pt_before pts a b → a ∈ pts ∧ b ∈ pts.
Proof. intros (i & j & _ & Hi & Hj). split; by eapply list_elem_of_lookup_2. Qed.

Lemma pt_before_irrefl pts a : NoDup pts → ¬ pt_before pts a a.
Proof.
  intros Hnd (i & j & Hij & Hi & Hj). pose proof (NoDup_lookup pts i j a Hnd Hi Hj). lia.
Qed.

Lemma pt_before_trans pts a b c :
  NoDup pts → pt_before pts a b → pt_before pts b c → pt_before pts a c.
Proof.
  intros Hnd (i & j & Hij & Hi & Hj) (j' & k & Hjk & Hj' & Hk).
  pose proof (NoDup_lookup pts j j' b Hnd Hj Hj') as ->.
  exists i, k. split_and!; [lia|done|done].
Qed.

Lemma pt_before_total pts a b :
  a ∈ pts → b ∈ pts → a ≠ b → pt_before pts a b ∨ pt_before pts b a.
Proof.
  intros [i Hi]%list_elem_of_lookup [j Hj]%list_elem_of_lookup Hne.
  destruct (lt_eq_lt_dec i j) as [[Hlt| ->]|Hlt]; [left; by exists i, j|congruence|].
  right. by exists j, i.
Qed.

Lemma pt_before_snoc pts τ a b :
  τ ∉ pts → pt_before (pts ++ [τ]) a b ↔ pt_before pts a b ∨ (b = τ ∧ a ∈ pts).
Proof.
  intros Hτ. split.
  - intros (i & j & Hij & Hi & Hj).
    apply lookup_app_Some in Hi as [Hi|(Hlen & Hi)], Hj as [Hj|(Hlen' & Hj)].
    + left. by exists i, j.
    + right. apply list_lookup_singleton_Some in Hj as [_ ->].
      split; [done|by eapply list_elem_of_lookup_2].
    + exfalso. apply lookup_lt_Some in Hj. lia.
    + exfalso. apply list_lookup_singleton_Some in Hi as [Hi0 _], Hj as [Hj0 _]. lia.
  - intros [(i & j & Hij & Hi & Hj)|(-> & Ha)].
    + exists i, j. split_and!; [done|by apply lookup_app_l_Some|by apply lookup_app_l_Some].
    + apply list_elem_of_lookup in Ha as [i Hi]. exists i, (length pts). split_and!.
      * by apply lookup_lt_Some in Hi.
      * by apply lookup_app_l_Some.
      * by rewrite lookup_app_r // Nat.sub_diag.
Qed.

Lemma vis_tr_pt ts pts a b : vis_tr ts pts a b → a ∈ pts.
Proof. intros [(_ & _ & Hab)|(_ & Ha & _)]; [by destruct (pt_before_elem _ _ _ Hab)|done]. Qed.

(* ====================================================================== *)
(* Appending events to the trace.                                         *)
(* ====================================================================== *)

Local Lemma pop_of_trace_snoc_ret ts τ r :
  pop_of_trace (ts ++ [(τ, Ret r)]) = pop_of_trace ts.
Proof.
  rewrite /pop_of_trace filter_app filter_cons_False; last by intros Heq; inversion Heq.
  by rewrite filter_nil right_id_L.
Qed.

Local Lemma pop_of_trace_snoc_call_sub ts τ n v x :
  x ∈ pop_of_trace ts → x ∈ pop_of_trace (ts ++ [(τ, Call n v)]).
Proof. rewrite /pop_of_trace filter_app fmap_app elem_of_app. by left. Qed.

Local Lemma pop_of_trace_snoc_call_inv ts τ n v x :
  x ∈ pop_of_trace (ts ++ [(τ, Call n v)]) → x ∈ pop_of_trace ts ∨ x = τ.
Proof.
  rewrite /pop_of_trace filter_app fmap_app elem_of_app.
  intros [Hx|Hx]; [by left|right].
  apply list_elem_of_fmap_1 in Hx as ([y e] & -> & Hy).
  apply list_elem_of_filter in Hy as [_ Hy].
  apply list_elem_of_singleton in Hy. by simplify_eq.
Qed.

Local Lemma ret_tags_snoc_call (ts : list (positive * trace)) τ n v :
  (filter (is_ret ∘ snd) (ts ++ [(τ, Call n v)])).*1 = (filter (is_ret ∘ snd) ts).*1.
Proof. rewrite filter_app filter_cons_False; last by intros []. by rewrite filter_nil right_id_L. Qed.

Local Lemma ret_tags_snoc_ret (ts : list (positive * trace)) τ r x :
  x ∈ (filter (is_ret ∘ snd) (ts ++ [(τ, Ret r)])).*1 →
  x ∈ (filter (is_ret ∘ snd) ts).*1 ∨ x = τ.
Proof.
  rewrite filter_app fmap_app elem_of_app. intros [Hx|Hx]; [by left|right].
  rewrite filter_cons_True in Hx; last exact I.
  rewrite filter_nil /= in Hx. by apply list_elem_of_singleton in Hx.
Qed.

Local Lemma ts_tr_iff ts ts' pts a b :
  (∀ x y, pre_of_trace ts' x y ↔ pre_of_trace ts x y) →
  (∀ x y, vis_tr ts' pts x y ↔ vis_tr ts pts x y) →
  ts_tr ts' pts a b ↔ ts_tr ts pts a b.
Proof. intros Hpre Hvis. rewrite /ts_tr. setoid_rewrite Hpre. by setoid_rewrite Hvis. Qed.

(* Everything that the premise mentions stays the same; only the bag part changes. *)
Local Lemma I_stack_vis_pre_transfer ts ts' m pts :
  I_stack_vis_pre ts m pts →
  valid_match ts' m → per_tag_pop_empty_sound ts' m →
  (∀ τ, τ ∈ ts.*1 → τ ∈ ts'.*1) →
  (∀ x y, pre_of_trace ts' x y ↔ pre_of_trace ts x y) →
  push_of_trace ts' = push_of_trace ts → pop_of_trace ts' = pop_of_trace ts →
  (∀ x, x ∈ push_of_trace ts → x ∈ (filter (is_ret ∘ snd) ts').*1 → x ∈ pts) →
  I_stack_vis_pre ts' m pts.
Proof.
  intros HI Hvm Hps Hcalled Hpre Hpush Hpop Hret.
  assert (Hvis : ∀ x y, vis_tr ts' pts x y ↔ vis_tr ts pts x y).
  { intros x y. by rewrite /vis_tr Hpush Hpop. }
  constructor.
  - done.
  - done.
  - apply HI.
  - intros τ Hτ. by apply Hcalled, (isv_called _ _ _ HI).
  - intros a b Hab. apply Hpre in Hab. by apply (isv_pre _ _ _ HI).
  - rewrite Hpush. done.
  - apply HI.
  - intros i j b p a q Hi Hj Hpq. apply Hpre in Hpq. by eapply (isv_rr _ _ _ HI).
  - intros j a pa b Hj Hapa Hts Hb Hbpa. rewrite Hpush in Hb. apply Hpre in Hapa.
    apply (ts_tr_iff _ _ _ _ _ Hpre Hvis) in Hts. by eapply (isv_lifo _ _ _ HI).
Qed.

Lemma I_stack_vis_pre_nil : I_stack_vis_pre [] [] [].
Proof.
  constructor.
  - apply valid_match_nil.
  - apply per_tag_pop_empty_sound_nil.
  - apply NoDup_nil_2.
  - by intros ? ?%elem_of_nil.
  - intros a b Hab. by apply pre_of_trace_ret in Hab as [? ?%elem_of_nil].
  - by intros ? ?%elem_of_nil.
  - by intros ? ?%elem_of_nil.
  - by intros ??????.
  - by intros ????.
Qed.

Lemma I_stack_vis_nil : I_stack_vis [].
Proof. exists [], []. apply I_stack_vis_pre_nil. Qed.

(* A fresh call has no point, so it changes nothing that a commit has checked. *)
Local Lemma I_stack_vis_pre_snoc_call ts m pts τ n v :
  I_stack_vis_pre ts m pts → τ ∉ ts.*1 →
  valid_match (ts ++ [(τ, Call n v)]) m → per_tag_pop_empty_sound (ts ++ [(τ, Call n v)]) m →
  I_stack_vis_pre (ts ++ [(τ, Call n v)]) m pts.
Proof.
  intros HI Hfresh Hvm Hps.
  set (ts' := ts ++ [(τ, Call n v)]).
  assert (Hτpts : τ ∉ pts) by (intros Hin; by apply Hfresh, (isv_called _ _ _ HI)).
  assert (Hm2 : ∀ q, q ∈ m.*2 → q ≠ τ).
  { intros q ([x y] & Heq & Hin)%list_elem_of_fmap_1 ->. simpl in Heq. subst y.
    apply Hfresh. apply (list_elem_of_fmap_2 fst _ (τ, Call Pop #())).
    exact (valid_match_call_pop _ _ _ _ (isv_valid _ _ _ HI) Hin). }
  assert (Hvis : ∀ x y, x ≠ τ → y ≠ τ → vis_tr ts' pts x y ↔ vis_tr ts pts x y).
  { intros x y Hx Hy. rewrite /vis_tr. split.
    - intros [(Hpx & Hpy & Hxy)|(Hpx & Hxp & Hpy & Hyx)].
      + left. split_and!; [|by destruct (pop_of_trace_snoc_call_inv ts τ n v y Hpy)|done].
        by destruct (push_of_trace_snoc_call_inv ts τ n v x Hpx).
      + right. split_and!; [|done| |done].
        * by destruct (pop_of_trace_snoc_call_inv ts τ n v x Hpx).
        * by destruct (push_of_trace_snoc_call_inv ts τ n v y Hpy).
    - intros [(Hpx & Hpy & Hxy)|(Hpx & Hxp & Hpy & Hyx)].
      + left. split_and!; [by apply push_of_trace_snoc_call_sub|by apply pop_of_trace_snoc_call_sub|done].
      + right. split_and!; [by apply pop_of_trace_snoc_call_sub|done|
                            by apply push_of_trace_snoc_call_sub|done]. }
  assert (Hne : ∀ x, x ∈ pts → x ≠ τ) by (intros x Hx ->; done).
  assert (Hts : ∀ a b, b ∈ pts → ts_tr ts' pts a b → ts_tr ts pts a b).
  { intros a b Hb [Hab|[(c & Hac & Hcb)|(d & c & Had & Hdc & Hcb)]].
    - left. by apply (pre_snoc_call_old ts τ n v) in Hab; [|apply Hne].
    - pose proof (vis_tr_pt _ _ _ _ Hcb) as Hc.
      right; left. exists c. split.
      + by apply (pre_snoc_call_old ts τ n v) in Hac; [|apply Hne].
      + apply Hvis in Hcb; [done|by apply Hne|by apply Hne].
    - pose proof (vis_tr_pt _ _ _ _ Hcb) as Hc. pose proof (vis_tr_pt _ _ _ _ Hdc) as Hd.
      right; right. exists d, c. split_and!.
      + by apply (pre_snoc_call_old ts τ n v) in Had; [|apply Hne].
      + apply Hvis in Hdc; [done|by apply Hne|by apply Hne].
      + apply Hvis in Hcb; [done|by apply Hne|by apply Hne]. }
  constructor.
  - done.
  - done.
  - apply HI.
  - intros x Hx. rewrite /ts' fmap_app elem_of_app. left. by apply (isv_called _ _ _ HI).
  - intros a b Hab Ha Hb. apply (pre_snoc_call_old ts τ n v) in Hab; last by apply Hne.
    by apply (isv_pre _ _ _ HI).
  - intros x Hx. rewrite ret_tags_snoc_call. intros Hret.
    destruct (push_of_trace_snoc_call_inv ts τ n v x Hx) as [Hx'| ->].
    { by apply (isv_push_ret _ _ _ HI). }
    exfalso. apply Hfresh. apply list_elem_of_fmap_1 in Hret as ([y e] & -> & Hin).
    apply list_elem_of_filter in Hin as [_ Hin]. by apply (list_elem_of_fmap_2 fst _ (y, e)).
  - apply HI.
  - intros i j b p a q Hi Hj Hpq. apply (pre_snoc_call_old ts τ n v) in Hpq.
    + by eapply (isv_rr _ _ _ HI).
    + apply Hm2. by apply (list_elem_of_fmap_2 snd _ (a, q)), list_elem_of_lookup_2 with j.
  - intros j a pa b Hj Hapa Hab Hb Hbpa.
    assert (Hpa : pa ≠ τ).
    { apply Hm2. by apply (list_elem_of_fmap_2 snd _ (a, pa)), list_elem_of_lookup_2 with j. }
    destruct (pt_before_elem _ _ _ Hbpa) as [Hbp _].
    apply (pre_snoc_call_old ts τ n v) in Hapa; last done.
    apply (isv_lifo _ _ _ HI j a pa b); [done|done|by apply Hts|..|done].
    by destruct (push_of_trace_snoc_call_inv ts τ n v b Hb) as [?| ->]; [|destruct (Hne τ Hbp)].
Qed.

Lemma I_stack_vis_pre_snoc_call_push ts m pts τ v :
  I_stack_vis_pre ts m pts → τ ∉ ts.*1 →
  I_stack_vis_pre (ts ++ [(τ, Call Push v)]) m pts.
Proof.
  intros HI Hfresh. apply I_stack_vis_pre_snoc_call; [done|done|..].
  - exact (valid_match_snoc_call_push ts m τ v (isv_valid _ _ _ HI) Hfresh).
  - exact (per_tag_pop_empty_sound_snoc_call_push ts m τ v (isv_valid _ _ _ HI)
             (isv_empty _ _ _ HI) Hfresh).
Qed.

Lemma I_stack_vis_pre_snoc_call_pop ts m pts τ :
  I_stack_vis_pre ts m pts → τ ∉ ts.*1 →
  I_stack_vis_pre (ts ++ [(τ, Call Pop #())]) m pts.
Proof.
  intros HI Hfresh. apply I_stack_vis_pre_snoc_call; [done|done|..].
  - exact (valid_match_snoc_call_pop ts m τ (isv_valid _ _ _ HI) Hfresh).
  - exact (per_tag_pop_empty_sound_snoc_call_pop ts m τ (isv_valid _ _ _ HI)
             (isv_empty _ _ _ HI) Hfresh).
Qed.

Local Lemma I_stack_vis_pre_snoc_ret ts m pts τ r :
  I_stack_vis_pre ts m pts →
  (τ ∈ push_of_trace ts → τ ∈ pts) →
  valid_match (ts ++ [(τ, Ret r)]) m → per_tag_pop_empty_sound (ts ++ [(τ, Ret r)]) m →
  I_stack_vis_pre (ts ++ [(τ, Ret r)]) m pts.
Proof.
  intros HI Hτ Hvm Hps. eapply I_stack_vis_pre_transfer; [done|done|done| | | | |].
  - intros x Hx. rewrite fmap_app elem_of_app. by left.
  - intros x y. apply pre_snoc_ret_iff.
  - apply push_of_trace_snoc_ret.
  - apply pop_of_trace_snoc_ret.
  - intros x Hx Hret. destruct (ret_tags_snoc_ret ts τ r x Hret) as [Hret'| ->].
    + by apply (isv_push_ret _ _ _ HI).
    + by apply Hτ.
Qed.

(* A push returns only after its point. *)
Lemma I_stack_vis_pre_snoc_ret_push ts m pts τ v :
  I_stack_vis_pre ts m pts →
  filter (λ x, x.1 = τ) ts = [(τ, Call Push v)] →
  τ ∈ pts →
  I_stack_vis_pre (ts ++ [(τ, Ret #())]) m pts.
Proof.
  intros HI Hfilter Hτ. apply I_stack_vis_pre_snoc_ret; [done|done|..].
  - exact (valid_match_snoc_ret_push ts m τ v (isv_valid _ _ _ HI) Hfilter).
  - exact (per_tag_pop_empty_sound_snoc_ret_push ts m τ v (isv_valid _ _ _ HI)
             (isv_empty _ _ _ HI) Hfilter).
Qed.

Local Lemma pop_not_push ts τ x :
  filter (λ x, x.1 = τ) ts = [(τ, Call Pop #())] → x ∈ push_of_trace ts → x ≠ τ.
Proof.
  intros Hfilter Hx ->. apply push_tag_in_trace in Hx as [w Hw].
  assert (Hin : (τ, Call Push w) ∈ filter (λ x, x.1 = τ) ts) by (by apply list_elem_of_filter).
  rewrite Hfilter in Hin. apply list_elem_of_singleton in Hin. discriminate.
Qed.

Lemma I_stack_vis_pre_snoc_ret_pop_empty ts m pts τ icall i :
  I_stack_vis_pre ts m pts →
  τ ∉ m.*2 →
  filter (λ x, x.1 = τ) ts = [(τ, Call Pop #())] →
  ts !! icall = Some (τ, Call Pop #()) →
  icall ≤ i ≤ length ts →
  (∀ τ1 τ2, (τ1, τ2) ∈ m → ¬ push_pop_covers ts τ1 τ2 i) →
  (∀ τ1, τ1 ∈ push_of_trace ts ∧ τ1 ∉ m.*1 → ¬ dangling_push_covers ts τ1 i) →
  I_stack_vis_pre (ts ++ [(τ, Ret (encode_response IsEmpty))]) m pts.
Proof.
  intros HI Hτm Hfilter Hicall Hi Hmatch Hdangle.
  apply I_stack_vis_pre_snoc_ret; [done| |..].
  - intros Hx. by destruct (pop_not_push ts τ τ Hfilter Hx).
  - exact (valid_match_snoc_ret_pop_empty ts m τ (isv_valid _ _ _ HI) Hτm Hfilter).
  - exact (per_tag_pop_empty_sound_snoc_ret_pop_empty ts m τ icall i (isv_valid _ _ _ HI)
             (isv_empty _ _ _ HI) Hfilter Hicall Hi Hmatch Hdangle).
Qed.

Lemma I_stack_vis_pre_snoc_ret_pop_val rme valid_value ts m pts τ1 τ2 v :
  per_tag_wellformed_bag rme valid_value ts →
  I_stack_vis_pre ts m pts →
  (τ1, τ2) ∈ m →
  (τ1, Call Push v) ∈ ts →
  filter (λ x, x.1 = τ2) ts = [(τ2, Call Pop #())] →
  I_stack_vis_pre (ts ++ [(τ2, Ret (encode_response (NonEmpty v)))]) m pts.
Proof.
  intros Hwf HI Hin Hcall Hfilter.
  apply I_stack_vis_pre_snoc_ret; [done| |..].
  - intros Hx. by destruct (pop_not_push ts τ2 τ2 Hfilter Hx).
  - exact (valid_match_snoc_ret_pop_val rme valid_value ts m τ1 τ2 v Hwf (isv_valid _ _ _ HI)
             Hin Hcall Hfilter).
  - exact (per_tag_pop_empty_sound_snoc_ret_pop_val ts m τ2 v (isv_valid _ _ _ HI)
             (isv_empty _ _ _ HI) Hfilter).
Qed.

(* A point is added for an operation that has been called and has not returned. *)
Lemma I_stack_vis_pre_snoc_point ts m pts τ :
  I_stack_vis_pre ts m pts →
  τ ∈ ts.*1 → τ ∉ (filter (is_ret ∘ snd) ts).*1 → τ ∉ pts →
  I_stack_vis_pre ts m (pts ++ [τ]).
Proof.
  intros HI Hcalled Hnret Hτ.
  assert (Hpre_τ : ∀ y, ¬ pre_of_trace ts τ y).
  { intros y Hpre. destruct (pre_of_trace_ret _ _ _ Hpre) as [r Hr].
    apply Hnret. apply (list_elem_of_fmap_2 fst _ (τ, Ret r)). by apply list_elem_of_filter_2. }
  assert (Hpts : ∀ x, x ∈ pts ++ [τ] ↔ x ∈ pts ∨ x = τ).
  { intros x. by rewrite elem_of_app list_elem_of_singleton. }
  (* relations into pointed tags are unchanged *)
  assert (Hvis : ∀ x y, y ∈ pts → vis_tr ts (pts ++ [τ]) x y → vis_tr ts pts x y ∧ x ∈ pts).
  { intros x y Hy [(Hpx & Hpy & Hxy)|(Hpx & Hxp & Hpy & Hyx)].
    - apply (pt_before_snoc _ _ _ _ Hτ) in Hxy as [Hxy|[-> _]]; [|done].
      split; [by left|by destruct (pt_before_elem _ _ _ Hxy)].
    - apply Hpts in Hxp as [Hxp| ->].
      + split; [right|done]. split_and!; [done|done|done|].
        intros Hyx'. apply Hyx, (pt_before_snoc _ _ _ _ Hτ). by left.
      + exfalso. apply Hyx, (pt_before_snoc _ _ _ _ Hτ). by right. }
  constructor.
  - apply HI.
  - apply HI.
  - apply NoDup_app. split_and!; [apply HI|by intros x Hx ->%list_elem_of_singleton|apply NoDup_singleton].
  - intros x [Hx| ->]%Hpts; [by apply (isv_called _ _ _ HI)|done].
  - intros a b Hab [Ha| ->]%Hpts [Hb| ->]%Hpts.
    + apply (pt_before_snoc _ _ _ _ Hτ). left. by apply (isv_pre _ _ _ HI).
    + apply (pt_before_snoc _ _ _ _ Hτ). by right.
    + by destruct (Hpre_τ b).
    + by destruct (Hpre_τ τ).
  - intros x Hx Hret. apply Hpts. left. by apply (isv_push_ret _ _ _ HI).
  - intros p Hp. apply Hpts. left. by apply (isv_pop_pt _ _ _ HI).
  - apply HI.
  - intros j a pa b Hj Hapa Hab Hb Hbpa.
    assert (Hpa : pa ∈ pts).
    { apply (isv_pop_pt _ _ _ HI).
      by apply (list_elem_of_fmap_2 snd _ (a, pa)), list_elem_of_lookup_2 with j. }
    apply (pt_before_snoc _ _ _ _ Hτ) in Hbpa as [Hbpa|[-> _]]; last done.
    destruct (pt_before_elem _ _ _ Hbpa) as [Hbp _].
    apply (isv_lifo _ _ _ HI j a pa b); [done|done| |done|done].
    destruct Hab as [Hab|[(c & Hac & Hcb)|(d & c & Had & Hdc & Hcb)]].
    + by left.
    + right; left. exists c. split; [done|]. by apply Hvis in Hcb as [? _].
    + apply Hvis in Hcb as [Hcb Hc]; last done.
      right; right. exists d, c. split_and!; [done| |done]. by apply Hvis in Hdc as [? _].
Qed.

(* A push is not ts-after itself. *)
Local Lemma ts_tr_irrefl rme valid_value ts m pts b :
  per_tag_wellformed_bag rme valid_value ts → I_stack_vis_pre ts m pts →
  b ∈ push_of_trace ts → ¬ ts_tr ts pts b b.
Proof.
  intros Hwf HI Hb.
  assert (Hret_pt : ∀ y, pre_of_trace ts b y → b ∈ pts).
  { intros y Hpre. destruct (pre_of_trace_ret _ _ _ Hpre) as [r Hr].
    apply (isv_push_ret _ _ _ HI); [done|].
    apply (list_elem_of_fmap_2 fst _ (b, Ret r)). by apply list_elem_of_filter_2. }
  assert (Hnpop : b ∉ pop_of_trace ts) by (intros Hp; by eapply push_xor_pop_of_trace).
  intros [Hbb|[(c & Hbc & Hcb)|(d & c & Hbd & Hdc & Hcb)]].
  - eapply pt_before_irrefl; [apply (isv_nodup _ _ _ HI)|].
    by apply (isv_pre _ _ _ HI); [|apply (Hret_pt b)..].
  - destruct Hcb as [(_ & ? & _)|(_ & Hc & _ & Hbc')]; first done.
    apply Hbc', (isv_pre _ _ _ HI); [done|by apply (Hret_pt c)|done].
  - destruct Hcb as [(_ & ? & _)|(Hcpop & Hc & _ & Hbc')]; first done.
    destruct Hdc as [(_ & _ & Hdc)|(_ & _ & Hcpush & _)]; last by eapply push_xor_pop_of_trace.
    apply Hbc'. eapply pt_before_trans; [apply (isv_nodup _ _ _ HI)| |exact Hdc].
    apply (isv_pre _ _ _ HI); [done|by apply (Hret_pt d)|by destruct (pt_before_elem _ _ _ Hdc)].
Qed.

(* Committing the pending pop [p] with the push [b]: [p] must have its point, and every
   push that is ts-after b and visible to p must be popped already (Lemma 3,
   condition 2, for the new pair). *)
Lemma I_stack_vis_pre_snoc_match rme valid_value ts m pts b p v :
  per_tag_wellformed_bag rme valid_value ts →
  I_stack_vis_pre ts m pts →
  b ∉ m.*1 → p ∉ m.*2 →
  (b, Call Push v) ∈ ts → (p, Call Pop #()) ∈ ts →
  p ∉ (filter (is_ret ∘ snd) ts).*1 →
  p ∈ pts →
  (pre_of_trace ts b p → ∀ c, c ≠ b → ts_tr ts pts b c → c ∈ push_of_trace ts →
     pt_before pts c p → c ∈ m.*1) →
  I_stack_vis_pre ts (m ++ [(b, p)]) pts.
Proof.
  intros Hwf HI Hb_nm Hp_nm Hcall_b Hcall_p Hp_noret Hp Hlifo.
  assert (Hpre_p : ∀ y, ¬ pre_of_trace ts p y).
  { intros y Hpre. destruct (pre_of_trace_ret _ _ _ Hpre) as [r Hr].
    apply Hp_noret. apply (list_elem_of_fmap_2 fst _ (p, Ret r)). by apply list_elem_of_filter_2. }
  assert (Hlk : ∀ k e, (m ++ [(b, p)]) !! k = Some e →
            (k < length m ∧ m !! k = Some e) ∨ (k = length m ∧ e = (b, p))).
  { intros k e Hk. apply lookup_app_Some in Hk as [Hk|(Hlen & Hk)].
    - left. split; [by apply lookup_lt_Some in Hk|done].
    - right. apply list_lookup_singleton_Some in Hk as [Hk ->]. split; [lia|done]. }
  constructor.
  - exact (valid_match_snoc_match ts m b p v (isv_valid _ _ _ HI) Hb_nm Hp_nm Hcall_b Hcall_p
             Hp_noret).
  - exact (per_tag_pop_empty_sound_snoc_match ts m b p v (isv_empty _ _ _ HI) Hb_nm Hp_nm Hcall_b).
  - apply HI.
  - apply HI.
  - apply HI.
  - apply HI.
  - intros q. rewrite fmap_app elem_of_app list_elem_of_singleton.
    intros [Hq| ->]; [by apply (isv_pop_pt _ _ _ HI)|done].
  - intros i j b' p' a q Hi Hj Hpq.
    apply Hlk in Hi as [(Hi & Hi')|(-> & Heq)], Hj as [(Hj & Hj')|(-> & Heq')].
    + by eapply (isv_rr _ _ _ HI).
    + done.
    + simplify_eq. by destruct (Hpre_p q).
    + simplify_eq. by destruct (Hpre_p p).
  - intros j a pa c Hj Hapa Hac Hc Hcpa.
    apply Hlk in Hj as [(Hj & Hj')|(-> & Heq)].
    + destruct (isv_lifo _ _ _ HI j a pa c Hj' Hapa Hac Hc Hcpa) as (i & pc & Hij & Hi).
      exists i, pc. split; [done|by apply lookup_app_l_Some].
    + simplify_eq.
      assert (Hcb : c ≠ b) by (intros ->; by eapply ts_tr_irrefl).
      pose proof (Hlifo Hapa c Hcb Hac Hc Hcpa) as Hcm.
      apply list_elem_of_fmap_1 in Hcm as ([c' pc] & Heq & Hin).
      simpl in Heq. subst c'. apply list_elem_of_lookup in Hin as [i Hi].
      exists i, pc. split; [by apply lookup_lt_Some in Hi|by apply lookup_app_l_Some].
Qed.

(* ====================================================================== *)
(* The premise on a closed trace, with the points as a rank function.     *)
(* ====================================================================== *)

Section closed.
  Context (ts : list (positive * trace)) (m : list (positive * positive))
    (f r : positive → nat).

  (* the operations of the closed history: pushes and matched pops *)
  Definition vis_op (a : positive) := a ∈ push_of_trace ts ∨ a ∈ m.*2.

  Definition vis_rk : relation positive := λ a b,
    (a ∈ push_of_trace ts ∧ b ∈ m.*2 ∧ f a < f b) ∨
    (a ∈ m.*2 ∧ b ∈ push_of_trace ts ∧ f a < f b).

  Definition ts_rk : relation positive := λ a b,
    pre_of_trace ts a b ∨ (∃ c, pre_of_trace ts a c ∧ vis_rk c b) ∨
    (∃ d c, pre_of_trace ts a d ∧ vis_rk d c ∧ vis_rk c b).

  Record closed_vis : Prop := {
    cv_inj a b : vis_op a → vis_op b → a ≠ b → f a ≠ f b;
    cv_pre a b : pre_of_trace ts a b → vis_op a → vis_op b → f a < f b;
    cv_rr_inj p q : p ∈ m.*2 → q ∈ m.*2 → p ≠ q → r p ≠ r q;
    cv_rr_pre p q : p ∈ m.*2 → q ∈ m.*2 → pre_of_trace ts p q → r p < r q;
    cv_lifo a pa b : (a, pa) ∈ m → pre_of_trace ts a pa → ts_rk a b →
      b ∈ push_of_trace ts → f b < f pa → ∃ pb, (b, pb) ∈ m ∧ r pb < r pa;
  }.
End closed.
