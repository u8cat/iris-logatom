From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Import bag.close queue.base.

(**********************************************************)
(* Begin LLM-generated code. *)
(* tool: Claude Code 2.1.91
    model: Claude Opus 4.6 (claude-opus-4-6)
    parameters:
      effort = high
      context window = 1000000
      max output tokens = 128000 *)
(* Public lemma types in this block are written by human. Only proofs
  and private lemmas are LLM-generated. *)
(* If x appears before y in l (= l1 ++ x :: l2 with y ∈ l2),
   and both pass P, then x appears before y in filter P l. *)
Local Lemma filter_before {A} (P : A → Prop) `{!∀ x, Decision (P x)}
  (l1 l2 : list A) (x y : A) :
  P x → y ∈ filter P l2 →
  y ∈ filter P (l1 ++ x :: l2).
Proof.
  intros HP Hy. rewrite filter_app filter_cons_True //. set_solver.
Qed.

(* NoDup push_of_trace from wellformedness: each tag has at most one Call Push *)
Local Lemma list_filter_lookup_pred {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (i : nat) (x : A) :
  filter P l !! i = Some x → P x.
Proof. by intros [??]%list_elem_of_lookup_2%list_elem_of_filter. Qed.

Local Lemma list_filter_lookup_orig {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (i : nat) (x : A) :
  filter P l !! i = Some x → x ∈ l.
Proof. by intros [??]%list_elem_of_lookup_2%list_elem_of_filter. Qed.

Local Lemma filter_NoDup_at {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (x : A) (i j : nat) :
  filter P l !! i = Some x → filter P l !! j = Some x → P x →
  (∀ i' j', l !! i' = Some x → l !! j' = Some x → i' = j') →
  i = j.
Proof.
  revert i j. induction l as [|a l IH]; intros i j Hi Hj HP Huniq.
  { rewrite filter_nil in Hi. done. }
  destruct (decide (P a)) as [HPa|HnPa].
  - rewrite filter_cons_True // in Hi, Hj.
    destruct i as [|i'], j as [|j']; simpl in Hi, Hj; [done| | |].
    + (* i=0, j=S j': a=x. x in filter P l at j'. x ∈ l at some position k.
         Huniq: (a::l) !! 0 = Some x and (a::l) !! (S k) = Some x → 0 = S k. ⊥ *)
      simplify_eq.
      assert (Hin : x ∈ l).
      { eapply list_elem_of_filter_1, list_elem_of_lookup_2. exact Hj. }
      apply list_elem_of_lookup_1 in Hin as [k_pos Hk_pos].
      enough (0 = Datatypes.S k_pos) by lia. apply Huniq; [done|exact Hk_pos].
    + simplify_eq.
      assert (Hin : x ∈ l).
      { eapply list_elem_of_filter_1, list_elem_of_lookup_2. exact Hi. }
      apply list_elem_of_lookup_1 in Hin as [k_pos Hk_pos].
      enough (Datatypes.S k_pos = 0) by lia. apply Huniq; [exact Hk_pos|done].
    + f_equal. eapply IH; [exact Hi|exact Hj|exact HP|].
      intros i'' j'' Hi'' Hj''.
      assert (Datatypes.S i'' = Datatypes.S j'') by (apply Huniq; done). lia.
  - rewrite filter_cons_False // in Hi, Hj.
    eapply IH; [exact Hi|exact Hj|exact HP|].
    intros i'' j'' Hi'' Hj''.
    assert (Datatypes.S i'' = Datatypes.S j'') by (apply Huniq; done). lia.
Qed.

Local Lemma filter_at_most_once {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (l : list A) (x : A) :
  P x →
  (∀ k1 k2, filter P l !! k1 = Some x → filter P l !! k2 = Some x → k1 = k2) →
  ∀ i j, l !! i = Some x → l !! j = Some x → i = j.
Proof.
  intros HP Hfuniq. induction l as [|a l IH]; intros i j Hi Hj.
  { done. }
  destruct (decide (P a)) as [HPa|HnPa].
  - destruct i as [|i'], j as [|j']; simpl in Hi, Hj; [done| | |].
    + simplify_eq. exfalso.
      assert (Hin : x ∈ filter P l).
      { apply list_elem_of_filter_2; [exact HP|]. eapply list_elem_of_lookup_2. exact Hj. }
      apply list_elem_of_lookup_1 in Hin as [k_filt Hk_filt].
      enough (Datatypes.S k_filt = (0:nat)) by discriminate.
      apply (Hfuniq (Datatypes.S k_filt) 0);
        rewrite filter_cons_True; try exact HP; done.
    + simplify_eq. exfalso.
      assert (Hin : x ∈ filter P l).
      { apply list_elem_of_filter_2; [exact HP|]. eapply list_elem_of_lookup_2. exact Hi. }
      apply list_elem_of_lookup_1 in Hin as [k_filt Hk_filt].
      enough ((0:nat) = Datatypes.S k_filt) by discriminate.
      apply (Hfuniq 0 (Datatypes.S k_filt));
        rewrite filter_cons_True; try exact HP; done.
    + f_equal. eapply IH; [|exact Hi|exact Hj].
      intros k1 k2 Hk1 Hk2.
      enough (Datatypes.S k1 = Datatypes.S k2) by lia.
      apply (Hfuniq (Datatypes.S k1) (Datatypes.S k2));
        rewrite filter_cons_True; try exact HP; done.
  - destruct i as [|i'], j as [|j']; simpl in Hi, Hj; [done| | |].
    + simplify_eq. exfalso. apply HnPa. exact HP.
    + simplify_eq. exfalso. apply HnPa. exact HP.
    + f_equal. eapply IH; [|exact Hi|exact Hj].
      intros k1 k2 Hk1 Hk2.
      apply Hfuniq; rewrite filter_cons_False //.
Qed.

(* If NoDup l and l = l1 ++ x :: l2 = l1' ++ x :: l2' with x ∉ l1 and x ∉ l1',
   then l1 = l1'. *)
Local Lemma NoDup_split_unique {A} (l l1 l2 l1' l2' : list A) (x : A) :
  NoDup l → l = l1 ++ x :: l2 → l = l1' ++ x :: l2' →
  x ∉ l1 → x ∉ l1' → l1 = l1'.
Proof.
  intros Hnd Heq1 Heq2 Hnotin1 Hnotin2.
  (* x at position |l1| in l and position |l1'| in l. NoDup → |l1| = |l1'|. *)
  assert (Hlen_eq : length l1 = length l1').
  { assert (Hpos1 : l !! length l1 = Some x).
    { rewrite Heq1 lookup_app_r // Nat.sub_diag //. }
    assert (Hpos2 : l !! length l1' = Some x).
    { rewrite Heq2 lookup_app_r // Nat.sub_diag //. }
    eapply NoDup_lookup; eassumption. }
  subst l. apply app_inj_1 in Heq2 as [? _]; [done|lia].
Qed.

Local Lemma NoDup_push_of_trace rme valid_value ts0 :
  per_tag_wellformed_bag rme valid_value ts0 → NoDup (push_of_trace ts0).
Proof.
  intros Hwf0. rewrite /push_of_trace. apply NoDup_alt.
  intros i j τ Hi Hj.
  rewrite list_lookup_fmap in Hi. rewrite list_lookup_fmap in Hj.
  destruct (filter (is_call_push ∘ snd) ts0 !! i) as [[τ_i ti]|] eqn:Hfi; [|done].
  destruct (filter (is_call_push ∘ snd) ts0 !! j) as [[τ_j tj]|] eqn:Hfj; [|done].
  simpl in Hi, Hj. injection Hi as ->. injection Hj as ->.
  assert (Hpi : (is_call_push ∘ snd) (τ, ti)) by (eapply list_filter_lookup_pred; exact Hfi).
  assert (Hpj : (is_call_push ∘ snd) (τ, tj)) by (eapply list_filter_lookup_pred; exact Hfj).
  simpl in Hpi, Hpj.
  destruct Hpi as [vi Hvi]. subst ti. destruct Hpj as [vj Hvj]. subst tj.
  (* Both in ts0 *)
  assert (Hin_i : (τ, Call Push vi) ∈ ts0)
    by (eapply list_filter_lookup_orig; eassumption).
  assert (Hin_j : (τ, Call Push vj) ∈ ts0)
    by (eapply list_filter_lookup_orig; eassumption).
  (* By wellformedness *)
  destruct (Hwf0 τ) as [(vpush & _ & Hprefix)|(rpop & _ & Hprefix)].
  - (* Push pattern *)
    assert (Hfi' : (τ, Call Push vi) ∈ filter (λ x, x.1 = τ) ts0).
    { apply list_elem_of_filter_2; done. }
    assert (Hfj' : (τ, Call Push vj) ∈ filter (λ x, x.1 = τ) ts0).
    { apply list_elem_of_filter_2; done. }
    pose proof (elem_of_prefix _ _ _ Hfi' Hprefix) as Hpi'.
    pose proof (elem_of_prefix _ _ _ Hfj' Hprefix) as Hpj'.
    rewrite !elem_of_cons !elem_of_nil !right_id in Hpi', Hpj'.
    destruct Hpi' as [Hpi'|]; last simplify_eq.
    destruct Hpj' as [Hpj'|]; last simplify_eq.
    simplify_eq.
    (* Step 1: (τ, Call Push vpush) appears at most once in ts0 *)
    assert (Honce_ts : ∀ i' j',
      ts0 !! i' = Some (τ, Call Push vpush) →
      ts0 !! j' = Some (τ, Call Push vpush) → i' = j').
    { apply (filter_at_most_once (λ x : positive * trace, x.1 = τ) ts0
        (τ, Call Push vpush) eq_refl).
      intros k1 k2 Hk1 Hk2.
      assert (Hk1_0 : k1 = 0).
      { pose proof (prefix_lookup_Some _ _ _ _ Hk1 Hprefix) as Hk1'.
        destruct k1 as [|[|]]; simpl in Hk1'; by simplify_eq. }
      assert (Hk2_0 : k2 = 0).
      { pose proof (prefix_lookup_Some _ _ _ _ Hk2 Hprefix) as Hk2'.
        destruct k2 as [|[|]]; simpl in Hk2'; by simplify_eq. }
      congruence. }
    (* Step 2: uniqueness in ts0 → uniqueness in filter(is_call_push) *)
    eapply (filter_NoDup_at (is_call_push ∘ snd) ts0
      (τ, Call Push vpush) i j Hfi Hfj).
    { simpl. eexists. done. }
    exact Honce_ts.
  - exfalso.
    assert (Hfi' : (τ, Call Push vi) ∈ filter (λ x, x.1 = τ) ts0)
      by (apply list_elem_of_filter_2; done).
    pose proof (elem_of_prefix _ _ _ Hfi' Hprefix) as Hp.
    rewrite !elem_of_cons elem_of_nil in Hp.
    destruct Hp as [Hp|[Hp|[]]]; simplify_eq.
Qed.

(* Key ordering lemma: pre_of_trace ts e1 e2 → e1 before e2 in push_of_trace ts.
   "before" = ∃ l1 l2, push_of_trace ts = l1 ++ e1 :: l2 ∧ e2 ∈ l2. *)
Local Lemma pre_push_order rme valid_value ts0 e1 e2 :
  per_tag_wellformed_bag rme valid_value ts0 →
  e1 ∈ push_of_trace ts0 → e2 ∈ push_of_trace ts0 →
  pre_of_trace ts0 e1 e2 →
  ∃ l1 l2, push_of_trace ts0 = l1 ++ e1 :: l2 ∧ e2 ∈ l2.
Proof.
  intros Hwf0 He1 He2 Hpre.
  (* Extract lookup positions *)
  rewrite /push_of_trace in He1.
  apply list_elem_of_fmap_1 in He1 as ([τ_1 t1] & Heq1 & Hin1).
  simpl in Heq1. subst τ_1.
  apply list_elem_of_filter in Hin1 as [[v1 Hv1] Hin1_ts]. simpl in Hv1. subst t1.
  apply list_elem_of_lookup_1 in Hin1_ts as [i1 Hi1].
  rewrite /push_of_trace in He2.
  apply list_elem_of_fmap_1 in He2 as ([τ_2 t2] & Heq2 & Hin2).
  simpl in Heq2. subst τ_2.
  apply list_elem_of_filter in Hin2 as [[v2 Hv2] Hin2_ts]. simpl in Hv2. subst t2.
  apply list_elem_of_lookup_1 in Hin2_ts as [i2 Hi2].
  (* From pre: ret(e1) < call(e2). By wf: call(e1) < ret(e1). So i1 < i2. *)
  (* call_of_tag ts0 e2 finds e2's Call Push (only Call by wf). *)
  assert (Hi1_lt_i2 : i1 < i2).
  { rewrite /pre_of_trace in Hpre.
    destruct (ret_of_tag ts0 e1) as [[ir xr]|] eqn:Hret; simpl in Hpre; [|done].
    destruct (call_of_tag ts0 e2) as [[ic xc]|] eqn:Hcall; simpl in Hpre; [|done].
    apply list_find_Some in Hret as (Hret_lookup & [Hret_tag Hret_is_ret] & Hret_min).
    apply list_find_Some in Hcall as (Hcall_lookup & [Htag _] & Hcall_min). simpl in Htag.
    assert (Hic_le_i2 : ic ≤ i2).
    { destruct (decide (ic ≤ i2)) as [|Hgt]; [lia|].
      assert (Hi2_lt_ic : i2 < ic) by lia.
      exfalso. apply (Hcall_min i2 _ Hi2 Hi2_lt_ic). simpl. rewrite -Htag. split; done. }
    assert (Hi1_le_ir : i1 ≤ ir).
    { destruct (decide (i1 ≤ ir)); [lia|].
      exfalso.
      (* ir < i1. By wellformedness: filter (tag=e1) ts0 is a prefix of
         [(e1, Call Push v); (e1, Ret #())]. The Call is first, Ret second.
         But (e1, Ret ...) at ir < i1 = index of (e1, Call Push v1).
         So in filter (tag=e1), Ret appears before Call. This contradicts
         the prefix ordering. *)
      (* Split ts0 at i1 using take_drop_middle *)
      pose proof (take_drop_middle _ _ _ Hi1) as Hts_eq.
      (* xr is at position ir < i1, so xr ∈ take i1 ts0 *)
      assert (Hxr_take : xr ∈ take i1 ts0).
      { eapply list_elem_of_lookup_2. rewrite lookup_take_lt; [exact Hret_lookup|lia]. }
      (* xr.1 = e1, so xr ∈ filter (tag=e1) ts0 *)
      simpl in Hret_tag.
      assert (Hxr_filt : xr ∈ filter (λ x, x.1 = e1) ts0).
      { apply list_elem_of_filter_2; [exact Hret_tag|].
        eapply list_elem_of_lookup_2. exact Hret_lookup. }
      (* (e1, Call Push v1) ∈ filter (tag=e1) ts0 *)
      assert (Hcall1_filt : (e1, Call Push v1) ∈ filter (λ x, x.1 = e1) ts0).
      { apply list_elem_of_filter_2; [done|]. eapply list_elem_of_lookup_2. exact Hi1. }
      destruct (Hwf0 e1) as [(vpush & _ & Hprefix)|(rpop & _ & Hprefix)].
      - (* push pattern: filter = prefix of [Call Push vpush; Ret #()] *)
        pose proof (elem_of_prefix _ _ _ Hxr_filt Hprefix) as Hxr_in_pref.
        pose proof (elem_of_prefix _ _ _ Hcall1_filt Hprefix) as Hcall1_in_pref.
        rewrite !elem_of_cons elem_of_nil in Hxr_in_pref, Hcall1_in_pref.
        destruct Hxr_in_pref as [Hxr_eq|[Hxr_eq|[]]].
        + (* xr = (e1, Call Push vpush). But is_ret xr.2 = is_ret (Call Push vpush) = False *)
          rewrite Hxr_eq /= in Hret_is_ret. done.
        + (* xr = (e1, Ret #()). OK, xr is Ret. *)
          destruct Hcall1_in_pref as [Hcall1_eq|[Hcall1_eq|Hcall1_abs]];
            [| |by apply not_elem_of_nil in Hcall1_abs].
          * (* (e1, Call Push v1) = (e1, Call Push vpush) → v1 = vpush *)
            simplify_eq.
            apply (f_equal (filter (λ x, x.1 = e1))) in Hts_eq.
            rewrite !filter_app filter_cons_True // in Hts_eq.
            assert (Hxr_filt_take : (e1, Ret #()) ∈ filter (λ x, x.1 = e1) (take i1 ts0)).
            { apply list_elem_of_filter_2; [done|]. exact Hxr_take. }
            destruct (filter (λ x, x.1 = e1) (take i1 ts0)) as [|hd_take tl_take] eqn:Hfilt_take.
            { set_solver. }
            (* filter(take) = hd_take :: tl_take. filter(ts0) starts with hd_take.
               But prefix starts with (e1, Call Push vpush). So hd_take = (e1, Call Push vpush). *)
            rewrite -Hts_eq in Hprefix.
            pose proof (prefix_cons_inv_1 _ _ _ _ Hprefix) as Hhd_eq.
            pose proof (prefix_cons_inv_2 _ _ _ _ Hprefix) as Hprefix_tl.
            rewrite Hhd_eq in Hxr_filt_take.
            rewrite elem_of_cons in Hxr_filt_take.
            destruct Hxr_filt_take as [Habs|Hxr_tl]; [simplify_eq|].
            (* (e1, Ret #()) ∈ tl_take. tl_take ++ ... `prefix_of` [Ret #()]. *)
            destruct tl_take as [|hd2 tl2]; [set_solver|].
            exfalso.
            apply prefix_length in Hprefix_tl.
            rewrite length_cons length_app /= in Hprefix_tl. lia.
          * (* Hcall1_eq : Call Push v1 = Ret #() — discriminate *)
            simplify_eq.
      - (* pop pattern: e1 is a push but wf says pop pattern → contradiction *)
        pose proof (elem_of_prefix _ _ _ Hcall1_filt Hprefix) as Hp.
        rewrite !elem_of_cons elem_of_nil in Hp.
        destruct Hp as [Hp|[Hp|[]]]; simplify_eq. }
    assert (Hi1_ne_ir : i1 ≠ ir).
    { intros Heq_pos. subst ir.
      (* ts0 !! i1 = Some (e1, Call Push v1) (from Hi1)
         ts0 !! i1 = Some xr (from Hret_lookup, with i1 = ir)
         So xr = (e1, Call Push v1). But is_ret xr.2 = is_ret (Call Push v1) = False. *)
      rewrite Hi1 in Hret_lookup.
      destruct xr as [xr_tag xr_tr]. simpl in Hret_lookup. injection Hret_lookup as _ <-.
      simpl in Hret_is_ret. done. }
    lia. }
  (* Split ts0 at position i1 using take_drop_middle *)
  pose proof (take_drop_middle _ _ _ Hi1) as Hts_split.
  (* e2's Call Push is at position i2 > i1, so it's in drop (S i1) ts0 *)
  assert (He2_drop : (e2, Call Push v2) ∈ drop (Datatypes.S i1) ts0).
  { eapply list_elem_of_lookup_2 with (i := i2 - Datatypes.S i1).
    rewrite lookup_drop. replace (Datatypes.S i1 + (i2 - Datatypes.S i1)) with i2 by lia.
    exact Hi2. }
  (* push_of_trace ts0 = push(take i1 ts0) ++ e1 :: push(drop (S i1) ts0) *)
  rewrite /push_of_trace -Hts_split !filter_app !fmap_app.
  rewrite filter_cons_True; last by (simpl; eexists; done). simpl.
  eexists _, _. split; [done|].
  apply (list_elem_of_fmap_2 fst _ (e2, Call Push v2)).
  apply list_elem_of_filter_2; [simpl; eexists; done | exact He2_drop].
Qed.

(* Before-after lemma: if x appears before y in l (l = l1 ++ x :: l2 with y ∈ l2),
   and both are not in l3, then x appears before y in list_difference l l3 *)
Local Lemma list_difference_before {A} `{!EqDecision A}
  (l1 l2 l3 : list A) (x y : A) :
  x ∉ l3 → y ∈ list_difference l2 l3 →
  y ∈ list_difference (l1 ++ x :: l2) l3.
Proof.
  intros Hx Hy.
  apply list_elem_of_difference in Hy as [Hy_in Hy_notin].
  apply list_elem_of_difference. split; [|exact Hy_notin].
  apply elem_of_app. right. apply elem_of_cons. right. exact Hy_in.
Qed.

(* If NoDup (l1 ++ l2), x ∈ l1, y ∈ l2, then y ∉ l1 and x ∉ l2 *)
Local Lemma NoDup_app_disjoint_l {A} (l1 l2 : list A) (x : A) :
  NoDup (l1 ++ l2) → x ∈ l2 → x ∉ l1.
Proof.
  intros Hnd Hin2 Hin1.
  apply NoDup_app in Hnd as (_ & Hdisj & _).
  exact (Hdisj x Hin1 Hin2).
Qed.

(* The nm2×nm1 and nm2×nm2 cases need: if pre_of_trace ts e1 e2 holds,
   and both e1, e2 are push tags with e1 ∈ ump' (remaining) and
   e2 ∈ nm1.*1 (consumed), contradiction.

   Key idea: push_of_trace ts = ... ++ e1 :: ... ++ e2 :: ... (e1 before e2
   because pre → call(e1) < call(e2)). list_difference preserves this order.
   So in ump = nm1.*1 ++ ump': e1 is "before" e2 but e1 ∈ ump' (suffix)
   and e2 ∈ nm1.*1 (prefix). With NoDup: e1 ∈ suffix ∧ e2 ∈ prefix ∧
   e2 ∈ suffix_of_ump_after_e1 → e2 ∈ suffix → e2 ∉ prefix (NoDup).
   Contradiction. *)
(* Proof: use pre_push_order to get e1 before e2 in push_of_trace.
   Then list_difference_before gives e2 after e1 in ump = prefix ++ suffix.
   Since e1 ∈ suffix and NoDup: e2 ∈ suffix too. But e2 ∈ prefix ∧ NoDup → ⊥. *)
Local Lemma ump_ordering_contradiction rme valid_value ts0 (m0 : list (positive * positive)) e1 e2
  (prefix suffix : list positive) :
  per_tag_wellformed_bag rme valid_value ts0 →
  NoDup (prefix ++ suffix) →
  e1 ∈ suffix → e2 ∈ prefix →
  e1 ∉ m0.*1 → e2 ∉ m0.*1 →
  prefix ++ suffix = list_difference (push_of_trace ts0) (m0.*1) →
  pre_of_trace ts0 e1 e2 → False.
Proof.
  intros Hwf0 Hnd He1_suf He2_pre He1_nm He2_nm Hump_eq Hpre_ts.
  (* Step 1: e1 ∈ push_of_trace ts0 and e2 ∈ push_of_trace ts0 *)
  assert (He1_push : e1 ∈ push_of_trace ts0).
  { assert (He1_ump : e1 ∈ prefix ++ suffix) by (apply elem_of_app; right; done).
    rewrite Hump_eq in He1_ump. apply list_elem_of_difference in He1_ump. tauto. }
  assert (He2_push : e2 ∈ push_of_trace ts0).
  { assert (He2_ump : e2 ∈ prefix ++ suffix) by (apply elem_of_app; left; done).
    rewrite Hump_eq in He2_ump. apply list_elem_of_difference in He2_ump. tauto. }
  (* Step 2: e1 before e2 in push_of_trace *)
  destruct (pre_push_order _ _ ts0 e1 e2 Hwf0 He1_push He2_push Hpre_ts)
    as (l1 & l2 & Hpush_split & He2_in_l2).
  (* Step 3: e2 after e1 in list_difference (push_of_trace) m0.*1 *)
  assert (He2_diff_after : e2 ∈ list_difference l2 m0.*1).
  { apply list_elem_of_difference. done. }
  (* Step 4: e1 ∈ list_difference (push_of_trace) m0.*1 via list_difference_before *)
  assert (He1_ump : e1 ∈ prefix ++ suffix).
  { rewrite Hump_eq. apply list_elem_of_difference. done. }
  destruct (list_elem_of_split _ _ He1_ump) as (ump1 & ump2 & Hump_split).
  (* e2 ∈ ump2: because e2 is after e1 in ump *)
  (* Key fact: list_difference distributes over ++ and :: *)
  assert (Hump_eq2 : prefix ++ suffix =
    list_difference l1 m0.*1 ++ e1 :: list_difference l2 m0.*1).
  { rewrite Hump_eq Hpush_split.
    assert (Hdist : ∀ (la lb : list positive) (x : positive) (k : list positive),
      x ∉ k → list_difference (la ++ x :: lb) k =
        list_difference la k ++ x :: list_difference lb k).
    { clear. intros la lb x k Hx. induction la as [|a la IH]; simpl.
      - destruct (decide_rel (∈) x k); [contradiction|done].
      - destruct (decide_rel (∈) a k); [exact IH|simpl; f_equal; exact IH]. }
    apply Hdist. exact He1_nm. }
  (* From NoDup and two splits of the same list at e1, ump2 = list_difference l2 *)
  assert (He2_ump2 : e2 ∈ ump2).
  { rewrite Hump_split in Hump_eq2.
    assert (Hnd2 : NoDup (ump1 ++ e1 :: ump2)) by (rewrite -Hump_split; exact Hnd).
    apply NoDup_app in Hnd2 as (Hnd_ump1 & Hdisj1 & Hnd_e1_ump2).
    apply NoDup_cons in Hnd_e1_ump2 as [He1_notin_ump2 Hnd_ump2].
    (* e1 ∉ ump1 *)
    assert (He1_notin_ump1 : e1 ∉ ump1).
    { intros Hin. apply (Hdisj1 e1 Hin). apply elem_of_cons. left. done. }
    (* From ump1 ++ e1 :: ump2 = list_difference l1 m0.*1 ++ e1 :: list_difference l2 m0.*1
       and NoDup, the split at e1 is unique: ump2 = list_difference l2 m0.*1 *)
    (* Prove by induction: if x ∉ l1, x ∉ l1', NoDup(l1 ++ x :: l2),
       l1 ++ x :: l2 = l1' ++ x :: l2', then l2 = l2'. *)
    assert (He1_notin_diff_l1 : e1 ∉ list_difference l1 m0.*1).
    { rewrite -Hump_split in Hump_eq2.
      rewrite Hump_eq2 in Hnd.
      eapply (NoDup_app_disjoint_l _ _ e1 Hnd).
      apply elem_of_cons. left. done. }
    set (dl := list_difference l1 m0.*1) in Hump_eq2.
    fold dl in He1_notin_diff_l1.
    clearbody dl.
    clear -Hump_eq2 He1_notin_ump1 He1_notin_diff_l1 He2_diff_after.
    rename He1_notin_diff_l1 into He1_notin_dl.
    revert dl ump2 He1_notin_ump1 He1_notin_dl Hump_eq2.
    induction ump1 as [|a ump1 IH]; intros dl ump2 He1_notin_ump1 He1_notin_dl Hump_eq2.
    - simpl in Hump_eq2.
      destruct dl as [|b dl']; simpl in Hump_eq2.
      + injection Hump_eq2 as ->. exact He2_diff_after.
      + injection Hump_eq2 as Hb_eq. exfalso. apply He1_notin_dl.
        apply elem_of_cons. left. done.
    - destruct dl as [|b dl']; simpl in Hump_eq2.
      + injection Hump_eq2 as <-. exfalso. apply He1_notin_ump1.
        apply elem_of_cons. left. done.
      + injection Hump_eq2 as _ Hump_eq2.
        eapply (IH dl'); [| |exact Hump_eq2].
        * intros Hin. apply He1_notin_ump1. apply elem_of_cons. right. exact Hin.
        * intros Hin. apply He1_notin_dl. apply elem_of_cons. right. exact Hin. }
  assert (He2_suf : e2 ∈ suffix).
  { (* e2 ∈ ump2 and ump1 ++ e1 :: ump2 = prefix ++ suffix.
       e1 ∈ suffix → e1 ∉ prefix (NoDup). Use lookup to show e2 is in suffix. *)
    apply list_elem_of_lookup_1 in He2_ump2 as [k Hk].
    (* e2 at position |ump1| + 1 + k in prefix ++ suffix *)
    assert (Hpos : (prefix ++ suffix) !! (length ump1 + 1 + k) = Some e2).
    { rewrite Hump_split lookup_app_r; [|lia].
      replace (length ump1 + 1 + k - length ump1) with (Datatypes.S k) by lia.
      simpl. exact Hk. }
    (* |ump1| ≥ |prefix| because e1 ∉ prefix *)
    assert (Hump1_ge : length ump1 ≥ length prefix).
    { assert (He1_notin_pre : e1 ∉ prefix).
      { eapply NoDup_app_disjoint_l; eassumption. }
      destruct (decide (length ump1 < length prefix)) as [Hlt|]; [|lia].
      exfalso. apply He1_notin_pre.
      assert (Hpos_e1 : (prefix ++ suffix) !! (length ump1) = Some e1).
      { rewrite Hump_split lookup_app_r; [|lia].
        replace (length ump1 - length ump1) with 0 by lia. done. }
      rewrite lookup_app_l in Hpos_e1; [|lia].
      eapply list_elem_of_lookup_2. exact Hpos_e1. }
    (* e2 at position ≥ |prefix| → e2 ∈ suffix *)
    rewrite lookup_app_r in Hpos; [|lia].
    eapply list_elem_of_lookup_2. exact Hpos. }
  eapply NoDup_app_disjoint_l; [exact Hnd | exact He2_suf | exact He2_pre].
Qed.

Local Lemma close_trace_add_match_snd_nodup ump_arg next :
  NoDup (bag.close.close_trace_add_match ump_arg next).*2.
Proof.
  revert next. induction ump_arg as [|τ1 ump_arg IH]; intros next.
  - simpl. constructor.
  - simpl. apply NoDup_cons. split.
    + (* next ∉ (close_trace_add_match ump_arg (next+1)).*2.
         All tags in the rest are ≥ next+1. *)
      intros Hin.
      apply list_elem_of_fmap_1 in Hin as ([τ_e τ_d] & Heq & Hin').
      simpl in Heq. subst τ_d.
      pose proof (bag.close.close_trace_add_match_tags_fresh _ _ _ _ Hin').
      lia.
    + apply IH.
Qed.

(* Fresh nm2 tags have no events in ts, np, or npop1 *)
Local Lemma nm2_tag_no_event_in_prefix rme valid_value ts0 m0 up0 upop0 ump0 nm1_0 ump0'
    (np0 npop1_0 : list (positive * trace)) calls0
    (τ_e τ_d : positive) :
  per_tag_wellformed_bag rme valid_value ts0 →
  np0 = bag.close.complete_trace_add_push up0 →
  npop1_0 = bag.close.complete_trace_remove_pop upop0 calls0 (m0 ++ nm1_0) →
  (up0, upop0, ump0) = bag.close.unpaired_operations ts0 m0 →
  (τ_e, τ_d) ∈ bag.close.close_trace_add_match ump0' (bag.close.max_tag ts0.*1 + 1) →
  ∀ ev : trace, (τ_d, ev) ∉ ts0 ++ np0 ++ npop1_0.
Proof.
  intros Hwf0 Hnp Hnpop1 Hops Hin_nm2 ev Hin_ev.
  (* τ_d ≥ max_tag + 1 *)
  assert (Hfresh : (bag.close.max_tag ts0.*1 + 1 ≤ τ_d)%positive).
  { eapply bag.close.close_trace_add_match_tags_fresh. exact Hin_nm2. }
  (* All tags in ts0 ++ np0 ++ npop1_0 are ≤ max_tag *)
  apply elem_of_app in Hin_ev as [Hin_ts|Hin_np_npop1].
  - (* (τ_d, ev) ∈ ts0: τ_d ≤ max_tag *)
    assert (Hle : (τ_d ≤ bag.close.max_tag ts0.*1)%positive).
    { eapply bag.close.tag_in_ts_le_max_tag. exact Hin_ts. }
    lia.
  - (* (τ_d, ev) ∈ np0 ++ npop1_0 *)
    apply elem_of_app in Hin_np_npop1 as [Hin_np|Hin_npop1].
    + (* (τ_d, ev) ∈ np0: tags from up0 ⊆ ts0.*1 *)
      subst np0. rewrite /bag.close.complete_trace_add_push in Hin_np.
      apply list_elem_of_fmap_1 in Hin_np as (τ' & Heq & Hin_up).
      injection Heq as <- _.
      assert (Hup_is : up0 = (bag.close.unpaired_operations ts0 m0).1.1).
      { unfold bag.close.unpaired_operations in Hops. by simplify_eq. }
      rewrite Hup_is in Hin_up.
      pose proof (bag.close.unpaired_push_is_push ts0 m0 τ_d Hin_up) as Hpush.
      destruct (push_tag_in_trace ts0 τ_d Hpush) as [vpush Hcall].
      pose proof (bag.close.tag_in_ts_le_max_tag ts0 τ_d _ Hcall). lia.
    + (* (τ_d, ev) ∈ npop1_0: tags from upop0 ⊆ ts0.*1 *)
      subst npop1_0. rewrite /bag.close.complete_trace_remove_pop in Hin_npop1.
      apply list_elem_of_omap in Hin_npop1 as (τ2' & Hin_upop & Heq).
      assert (Hupop_is' : upop0 = (bag.close.unpaired_operations ts0 m0).1.2).
      { unfold bag.close.unpaired_operations in Hops. by simplify_eq. }
      destruct (find _ _) as [[τ1' ?]|]; last discriminate.
      injection Heq as Hτ_eq _. subst τ2'.
      rewrite Hupop_is' in Hin_upop.
      pose proof (bag.close.unpaired_pop_is_pop ts0 m0 τ_d Hin_upop) as Hpop.
      pose proof (pop_tag_in_trace ts0 τ_d Hpop) as Hcall.
      pose proof (bag.close.tag_in_ts_le_max_tag ts0 τ_d _ Hcall).
      lia.
Qed.

(* If (e1,d1) before (e2,d2) in nm (formalized: nm = l1 ++ (e1,d1) :: l2 ∧ (e2,d2) ∈ l2),
   and d1, d2 have no events in prefix, then
   ¬ pre_of_trace (prefix ++ close_trace_add_pop calls nm) d2 d1.
   close_trace_add_pop generates [(d,Call);(d,Ret)] for each (e,d) in nm IN ORDER.
   So d1's events come before d2's, meaning ret(d2) ≥ call(d1). *)
(* If (e1,d1) before (e2,d2) in nm (= l1 ++ (e1,d1) :: l2 with (e2,d2) ∈ l2),
   d1 and d2 have no events in prefix, and NoDup nm.*2,
   then ¬ pre_of_trace (prefix ++ close_trace_add_pop calls nm) d2 d1. *)
(* d has no events in close_trace_add_pop calls nm if d ∉ nm.*2 *)
Local Lemma close_trace_add_pop_not_in calls0 nm0 (d : positive) :
  d ∉ nm0.*2 →
  ∀ ev : trace, (d, ev) ∉ bag.close.close_trace_add_pop calls0 nm0.
Proof.
  intros Hnotin ev Hin.
  rewrite /bag.close.close_trace_add_pop elem_of_app in Hin.
  destruct Hin as [Hin_c | Hin_r].
  - apply list_elem_of_fmap_1 in Hin_c as ([e' d'] & Heq & Hin_nm).
    injection Heq as <- _. apply Hnotin.
    apply (list_elem_of_fmap_2 snd _ (e', d)). exact Hin_nm.
  - apply list_elem_of_fmap_1 in Hin_r as ([e' d'] & Heq & Hin_nm).
    injection Heq as <- _. apply Hnotin.
    apply (list_elem_of_fmap_2 snd _ (e', d)). exact Hin_nm.
Qed.

(* d's Call is in close_trace_add_pop calls [(e,d)] *)
Local Lemma close_trace_add_pop_call_in calls0 (e_tag d_tag : positive) :
  (d_tag, Call Pop #()) ∈ bag.close.close_trace_add_pop calls0 [(e_tag, d_tag)].
Proof.
  rewrite /bag.close.close_trace_add_pop /=. set_solver.
Qed.

Local Lemma close_trace_add_pop_ordered
    (prefix : list (positive * trace)) (calls : gmap positive (nat*val))
    (nm : list (positive * positive))
    (e1 d1 e2 d2 : positive) :
  (∀ ev : trace, (d1, ev) ∉ prefix) →
  (∀ ev : trace, (d2, ev) ∉ prefix) →
  (∃ nm_before nm_after,
    nm = nm_before ++ (e1, d1) :: nm_after ∧ (e2, d2) ∈ nm_after) →
  NoDup nm.*2 →
  ¬ pre_of_trace (prefix ++ bag.close.close_trace_add_pop calls nm) d2 d1.
Proof.
  intros Hd1_notin_pre Hd2_notin_pre (nm_before & nm_after & Hnm_split & He2d2_after) Hnd Hpre.
  (* With the new [close_trace_add_pop calls nm = Calls(nm) ++ Rets(nm)], we have:
     - d1's Call is at position [length(prefix) + i1] where i1 = length nm_before.
     - d2's Ret is at position [length(prefix) + length(nm) + i2] where
       i2 = length nm_before + 1 + j and j is the position of (e2, d2) in nm_after.
     Thus d2's Ret position > d1's Call position. *)
  apply list_elem_of_lookup_1 in He2d2_after as [j Hj].
  set (ts_close := prefix ++ bag.close.close_trace_add_pop calls nm).
  set (i1 := length nm_before).
  set (i2 := length nm_before + Datatypes.S j).
  assert (Hnm_lkp_d1 : nm !! i1 = Some (e1, d1)).
  { rewrite Hnm_split lookup_app_r; last by subst i1; lia.
    subst i1. rewrite Nat.sub_diag //. }
  assert (Hnm_lkp_d2 : nm !! i2 = Some (e2, d2)).
  { rewrite Hnm_split lookup_app_r; last by subst i2; lia.
    subst i2.
    replace (length nm_before + Datatypes.S j - length nm_before)
      with (Datatypes.S j) by lia.
    simpl. exact Hj. }
  pose proof (bag.close.close_trace_add_pop_lookup_call calls nm i1 e1 d1 Hnm_lkp_d1) as Hd1_call.
  pose proof (bag.close.close_trace_add_pop_lookup_ret calls nm i2 e2 d2 Hnm_lkp_d2) as Hd2_ret.
  pose proof (bag.close.close_trace_add_pop_length calls nm) as Hlen.
  assert (Hd1_call_close : ts_close !! (length prefix + i1)
                          = Some (d1, Call Pop #())).
  { subst ts_close. rewrite lookup_app_r; last lia.
    replace (length prefix + i1 - length prefix) with i1 by lia. exact Hd1_call. }
  assert (Hd2_ret_close : ts_close !! (length prefix + length nm + i2)
                         = Some (d2, Ret (bag.close.ret_val_of_call (calls !!! e2)))).
  { subst ts_close. rewrite lookup_app_r; last lia.
    replace (length prefix + length nm + i2 - length prefix)
      with (length nm + i2) by lia.
    exact Hd2_ret. }
  rewrite /pre_of_trace in Hpre.
  destruct (ret_of_tag ts_close d2) as [[p_r [τ_r ev_r]]|] eqn:Hret_d2.
  2: { unfold ts_close in Hret_d2. rewrite Hret_d2 /= in Hpre. exact Hpre. }
  unfold ts_close in Hret_d2 at 1.
  rewrite Hret_d2 /= in Hpre.
  destruct (call_of_tag ts_close d1) as [[p_c [τ_c ev_c]]|] eqn:Hcall_d1.
  2: { unfold ts_close in Hcall_d1. rewrite Hcall_d1 /= in Hpre. exact Hpre. }
  unfold ts_close in Hcall_d1 at 1.
  rewrite Hcall_d1 /= in Hpre.
  (* Hpre : p_r < p_c *)
  rewrite /ret_of_tag in Hret_d2.
  apply list_find_Some in Hret_d2 as (Hret_lkp & [Hτ_r His_ret] & Hret_min).
  simpl in Hτ_r. subst τ_r.
  rewrite /call_of_tag in Hcall_d1.
  apply list_find_Some in Hcall_d1 as (Hcall_lkp & [Hτ_c His_call] & Hcall_min).
  simpl in Hτ_c. subst τ_c.
  (* The first Ret of d2 in ts_close is at p_r. We have Hd2_ret_close: a Ret of d2 at
     (length prefix + length nm + i2). So p_r ≤ length prefix + length nm + i2. *)
  assert (Hp_r_lt : length prefix ≤ p_r).
  { destruct (decide (length prefix ≤ p_r)) as [|Hlt]; first done.
    exfalso. apply (Hd2_notin_pre ev_r).
    apply list_elem_of_lookup_2 with p_r. subst ts_close.
    rewrite lookup_app_l in Hret_lkp; first exact Hret_lkp. lia. }
  (* The first Call of d1 in ts_close is at p_c. We have Hd1_call_close: a Call of d1 at
     (length prefix + i1). So p_c ≤ length prefix + i1. *)
  assert (Hp_c_le : p_c ≤ length prefix + i1).
  { destruct (decide (p_c ≤ length prefix + i1)) as [|Hgt]; first done.
    exfalso. apply (Hcall_min (length prefix + i1) _ Hd1_call_close); first lia.
    simpl. split; done. }
  (* p_r is a Ret of d2 in ts_close. But p_r might be a different Ret event with
     same tag d2. Let's use NoDup to show p_r = length prefix + length nm + i2. *)
  (* Actually, since prefix has no d2 events and ctap has unique d2 events,
     we just need to bound p_r above by some Ret position. *)
  assert (Hp_r_in_ctap : length prefix + length nm ≤ p_r).
  { (* p_r is the first Ret of d2. Calls of d2 are in the [length prefix, length prefix + length nm)
       range. So any Ret of d2 (which has is_ret) must be at p_r ≥ length prefix + length nm. *)
    destruct (decide (p_r < length prefix + length nm)) as [Hlt|]; last lia.
    exfalso.
    (* p_r is at position ∈ [length prefix, length prefix + length nm), i.e., in Calls section. *)
    unfold ts_close in Hret_lkp.
    rewrite lookup_app_r in Hret_lkp; last lia.
    rewrite /bag.close.close_trace_add_pop in Hret_lkp.
    rewrite lookup_app_l in Hret_lkp; last by rewrite length_fmap; lia.
    rewrite list_lookup_fmap in Hret_lkp.
    destruct (nm !! (p_r - length prefix)) as [[τ_a τ_b]|] eqn:Hnm_lkp_pr;
      simpl in Hret_lkp; last discriminate.
    simplify_eq.
    simpl in His_ret. done. }
  subst i1 i2.
  rewrite Hnm_split length_app /= in Hp_r_in_ctap.
  lia.
Qed.


Local Lemma close_trace_add_match_fst_eq ump n :
  (bag.close.close_trace_add_match ump n).*1 = ump.
Proof.
  revert n. induction ump as [|τ1 ump IH]; first done.
  intros n. simpl. f_equal. apply IH.
Qed.

Local Lemma complete_trace_add_match_cover upop m0 ump τ :
  τ ∈ ump →
  τ ∈ (bag.close.complete_trace_add_match upop m0 ump).1.*1 ∨
  τ ∈ (bag.close.complete_trace_add_match upop m0 ump).2.
Proof.
  revert ump. induction upop as [|τ2 upop IH].
  - intros ump Hin. right. done.
  - intros ump Hin. simpl.
    destruct (find _ m0) as [?|].
    + exact (IH ump Hin).
    + destruct ump as [|τ1 ump'].
      * exact (IH [] Hin).
      * destruct (bag.close.complete_trace_add_match upop m0 ump') as [nm1_rest remaining] eqn:Hrec.
        apply elem_of_cons in Hin as [-> | Hin].
        -- left. simpl. apply elem_of_cons. left. done.
        -- destruct (IH ump' Hin) as [Hl | Hr].
           ++ left. simpl. apply elem_of_cons. right.
              rewrite Hrec /= in Hl. done.
           ++ right. simpl. rewrite Hrec /= in Hr. done.
Qed.

Local Lemma close_trace_push_sub ts m :
  push_of_trace (close_trace ts m).1 ⊆ (close_trace ts m).2.*1.
Proof.
  unfold close_trace.
  destruct (bag.close.unpaired_operations ts m) as [[up upop] ump_init] eqn:Hops.
  destruct (bag.close.complete_trace_add_match upop m ump_init) as [nm1 ump'] eqn:Hmatch.
  set (calls := bag.close.extract_calls ts).
  set (np := bag.close.complete_trace_add_push up).
  set (npop1 := bag.close.complete_trace_remove_pop upop calls (m ++ nm1)).
  set (U := list_difference upop (m ++ nm1).*2).
  set (ts' := filter (λ x : positive * trace, x.1 ∉ U) ts).
  set (nm2 := bag.close.close_trace_add_match ump' (bag.close.max_tag ts.*1 + 1)).
  set (npop2 := bag.close.close_trace_add_pop calls nm2).
  simpl.
  rewrite /push_of_trace !filter_app !fmap_app.
  assert (Hnp : filter (is_call_push ∘ snd) np = []).
  { subst np. apply filter_False_nil. rewrite Forall_forall.
    intros [τ' t'] Hin. unfold bag.close.complete_trace_add_push in Hin.
    apply list_elem_of_fmap_1 in Hin as (τ'' & Heq & _).
    injection Heq as -> ->. simpl. intros [? Habs]. discriminate. }
  assert (Hnpop1 : filter (is_call_push ∘ snd) npop1 = []).
  { subst npop1. apply filter_False_nil. rewrite Forall_forall.
    intros [τ' t'] Hin. unfold bag.close.complete_trace_remove_pop in Hin.
    apply list_elem_of_omap in Hin as (τ2' & _ & Heq).
    destruct (find _ _) as [[τ1' ?]|]; last discriminate.
    injection Heq as Hτ Ht. subst τ' t'.
    simpl. intros [? Habs]; discriminate. }
  assert (Hnpop2 : filter (is_call_push ∘ snd) npop2 = []).
  { subst npop2. apply filter_False_nil. rewrite Forall_forall.
    intros [τ' t'] Hin. unfold bag.close.close_trace_add_pop in Hin.
    apply elem_of_app in Hin as [Hin_c | Hin_r].
    - apply list_elem_of_fmap_1 in Hin_c as ([τ1' τ2'] & Heq & _).
      injection Heq as -> ->.
      simpl. intros [? Habs]; discriminate.
    - apply list_elem_of_fmap_1 in Hin_r as ([τ1' τ2'] & Heq & _).
      injection Heq as -> ->.
      simpl. intros [? Habs]; discriminate. }
  rewrite /npop2 /bag.close.close_trace_add_pop filter_app in Hnpop2.
  apply app_eq_nil in Hnpop2 as [HnpC HnpR].
  rewrite Hnp Hnpop1 HnpC HnpR !fmap_nil !app_nil_r.
  intros τ Hin.
  (* τ has a push event in ts'. ts' = filter (∉ U) ts, so τ has Call Push in ts. *)
  assert (Hin_ts : τ ∈ (filter (is_call_push ∘ snd) ts).*1).
  { apply list_elem_of_fmap_1 in Hin as ([τ' t'] & Heq & Hin_filt). simpl in Heq. subst τ'.
    apply list_elem_of_filter in Hin_filt as [Hpush Hin_ts'].
    rewrite /ts' in Hin_ts'.
    apply list_elem_of_filter in Hin_ts' as [_ Hin_orig].
    apply (list_elem_of_fmap_2 fst _ (τ, t')).
    apply list_elem_of_filter_2; done. }
  rewrite !elem_of_app.
  destruct (decide (τ ∈ m.*1)) as [Hm | Hnm].
  - left. done.
  - right.
    assert (Hump : τ ∈ ump_init).
    { unfold bag.close.unpaired_operations in Hops.
      injection Hops as _ _ <-.
      apply list_elem_of_difference. done. }
    destruct (complete_trace_add_match_cover upop m ump_init τ Hump) as [Hnm1 | Hump'].
    + left. rewrite Hmatch /= in Hnm1. done.
    + right. rewrite Hmatch /= in Hump'.
      rewrite close_trace_add_match_fst_eq. done.
Qed.

(* nm1.*1 ++ remaining = ump *)
Local Lemma complete_trace_add_match_split upop m0 ump :
  (bag.close.complete_trace_add_match upop m0 ump).1.*1
    ++ (bag.close.complete_trace_add_match upop m0 ump).2 = ump.
Proof.
  revert ump. induction upop as [|τ2 upop IH]; first done.
  intros ump. simpl.
  destruct (find _ m0) as [?|]; first by apply IH.
  destruct ump as [|τ1 ump']; first by apply IH.
  destruct (bag.close.complete_trace_add_match upop m0 ump') as [nm1_rest rem] eqn:Hrec.
  simpl. f_equal. specialize (IH ump'). rewrite Hrec /= in IH. exact IH.
Qed.

(* If e1 appears before e2 in ump, and e2 is consumed, then e1 is consumed.
   Formalized: if ump = l1 ++ e1 :: l2 and e2 ∈ l2 and e2 ∈ nm1.*1,
   then e1 ∈ nm1.*1. But this is equivalent to: nm1.*1 is a prefix of ump. *)
Local Lemma complete_trace_add_match_prefix upop m0 ump :
  (bag.close.complete_trace_add_match upop m0 ump).1.*1 `prefix_of` ump.
Proof.
  exists (bag.close.complete_trace_add_match upop m0 ump).2.
  symmetry. apply complete_trace_add_match_split.
Qed.

(* TODO: uses bag.pre_of_trace_app_not *)
Local Lemma pre_of_trace_app_not_queue ts0 rest τ1 τ2 :
  (∃ nc v, (τ1, Call nc v) ∈ ts0) →
  ¬ pre_of_trace ts0 τ2 τ1 →
  ¬ pre_of_trace (ts0 ++ rest) τ2 τ1.
Proof. apply not_pre_of_trace_app. Qed.

Local Lemma pre_of_trace_no_ret ts0 τ1 τ2 :
  ret_of_tag ts0 τ1 = None →
  ¬ pre_of_trace ts0 τ1 τ2.
Proof.
  intros Hret Hpre. rewrite /pre_of_trace Hret /= in Hpre. done.
Qed.

(*** Helper lemmas for close_preserves_order_correct_matched ***)

(* For τ with a Call event in ts0 (sublist of close_trace), call_of_tag close
   returns position in ts0 with index < length ts0. *)
Local Lemma call_in_prefix_lt ts0 rest τ nev ev :
  (τ, Call nev ev) ∈ ts0 →
  ∃ i x, call_of_tag (ts0 ++ rest) τ = Some (i, x) ∧ i < length ts0.
Proof.
  intros Hin.
  apply list_elem_of_lookup_1 in Hin as [k Hlk_k].
  pose proof (lookup_lt_Some _ _ _ Hlk_k) as Hk_lt.
  destruct (list_find (λ t : positive * trace, t.1 = τ ∧ is_call t.2) ts0)
    as [[i x]|] eqn:Hf.
  - rewrite /call_of_tag.
    pose proof Hf as Hf_copy.
    apply list_find_Some in Hf as (Hlk & Hpx & Hbef).
    pose proof (lookup_lt_Some _ _ _ Hlk) as Hi_lt.
    exists i, x. split; last done.
    apply list_find_Some.
    split; first by rewrite (lookup_app_l _ _ _ Hi_lt).
    split; first done.
    intros j y Hlk_j Hj_lt.
    rewrite lookup_app_l in Hlk_j; last lia.
    exact (Hbef j y Hlk_j Hj_lt).
  - exfalso. apply list_find_None in Hf. rewrite Forall_forall in Hf.
    specialize (Hf _ (list_elem_of_lookup_2 _ _ _ Hlk_k)). simpl in Hf.
    apply Hf. done.
Qed.

(* For τ that has no Ret in ts0 but has Ret in (ts0 ++ rest), the position of
   the Ret in close is ≥ length ts0. *)
Local Lemma ret_after_prefix ts0 rest τ i x :
  ret_of_tag ts0 τ = None →
  ret_of_tag (ts0 ++ rest) τ = Some (i, x) →
  i ≥ length ts0.
Proof.
  intros Hno Hsome.
  rewrite /ret_of_tag list_find_app_Some in Hsome.
  destruct Hsome as [Hin|[Hge _]]; last done.
  rewrite /ret_of_tag in Hno. rewrite Hin in Hno. discriminate.
Qed.

(* Lift pre from close_trace = filter ts ++ rest to ts. Convention: pre ts τ1 τ2 = ret(τ1) < call(τ2). *)
Local Lemma pre_close_to_pre_ts (U : list positive) ts rest τ1 τ2 nv_call v_call :
  τ1 ∉ U →
  τ2 ∉ U →
  (τ2, Call nv_call v_call) ∈ ts →
  pre_of_trace (filter (λ x : positive * trace, x.1 ∉ U) ts ++ rest) τ1 τ2 →
  pre_of_trace ts τ1 τ2.
Proof.
  intros HU1 HU2 Hcall Hpre.
  apply pre_of_trace_app_inv in Hpre.
  - by apply (bag.close.pre_of_trace_filter_iff U ts τ2 τ1 HU2 HU1).
  - do 2 eexists. apply list_elem_of_filter_2; done.
Qed.

(* Lift ¬pre from ts to close_trace. *)
Local Lemma not_pre_ts_to_not_pre_close (U : list positive) ts rest τ1 τ2 nv_call v_call :
  τ1 ∉ U →
  τ2 ∉ U →
  (τ2, Call nv_call v_call) ∈ ts →
  ¬ pre_of_trace ts τ1 τ2 →
  ¬ pre_of_trace (filter (λ x : positive * trace, x.1 ∉ U) ts ++ rest) τ1 τ2.
Proof.
  intros HU1 HU2 Hcall Hno.
  rewrite <-(bag.close.pre_of_trace_filter_iff U ts τ2 τ1 HU2 HU1) in Hno.
  apply not_pre_of_trace_app; last exact Hno.
  do 2 eexists. apply list_elem_of_filter_2; done.
Qed.

(* Helper 1: Call Push position is unique per τ in well-formed ts. *)
Local Lemma push_call_pos_unique rme valid_value ts τ p1 p2 v1 v2 :
  per_tag_wellformed_bag rme valid_value ts →
  ts !! p1 = Some (τ, Call Push v1) →
  ts !! p2 = Some (τ, Call Push v2) →
  p1 = p2.
Proof.
  intros Hwf Hp1 Hp2.
  assert (Hsym : ∀ q1 q2 w1 w2,
    ts !! q1 = Some (τ, Call Push w1) →
    ts !! q2 = Some (τ, Call Push w2) →
    q1 < q2 → False).
  { intros q1 q2 w1 w2 Hq1 Hq2 Hlt.
    destruct (Hwf τ) as [(v' & _ & Hpfx)|(r' & _ & Hpfx)]; cycle 1.
    - apply list_elem_of_lookup_2 in Hq1 as Hin_q1.
      assert (Hin : (τ, Call Push w1) ∈ filter (λ x : positive * trace, x.1 = τ) ts).
      { apply list_elem_of_filter; done. }
      eapply elem_of_prefix in Hin; last exact Hpfx.
      apply elem_of_cons in Hin as [Habs|Hin].
      + injection Habs as Habs. discriminate.
      + apply elem_of_cons in Hin as [Habs|?]; [discriminate|by set_solver].
    - assert (Hfilt_eq : filter (λ x : positive * trace, x.1 = τ) ts =
        filter (λ x : positive * trace, x.1 = τ) (take q1 ts) ++
        [(τ, Call Push w1)] ++
        filter (λ x : positive * trace, x.1 = τ) (drop (Datatypes.S q1) ts)).
      { rewrite -{1}(take_drop_middle ts q1 _ Hq1).
        rewrite filter_app filter_cons_True //. }
      assert (Hin_drop : (τ, Call Push w2) ∈
                filter (λ x : positive * trace, x.1 = τ) (drop (Datatypes.S q1) ts)).
      { apply list_elem_of_filter; split; [done|].
        apply list_elem_of_lookup_2 with (i := q2 - Datatypes.S q1).
        rewrite lookup_drop.
        replace (Datatypes.S q1 + (q2 - Datatypes.S q1)) with q2 by lia.
        exact Hq2. }
      apply list_elem_of_lookup_1 in Hin_drop as [k Hk_drop].
      pose proof (lookup_lt_Some _ _ _ Hk_drop) as Hk_lt_len.
      pose proof (prefix_length _ _ Hpfx) as Hpfx_len. simpl in Hpfx_len.
      rewrite Hfilt_eq !length_app /= in Hpfx_len.
      assert (Hlen_take_zero : length (filter (λ x : positive * trace, x.1 = τ) (take q1 ts)) = 0) by lia.
      assert (Hk_zero : k = 0) by lia. subst k.
      apply length_zero_iff_nil in Hlen_take_zero.
      assert (Hfilt_lookup : filter (λ x : positive * trace, x.1 = τ) ts !! 1 =
        Some (τ, Call Push w2)).
      { rewrite Hfilt_eq Hlen_take_zero /=. exact Hk_drop. }
      assert (Hpfx_lookup : [(τ, Call Push v'); (τ, Ret #())] !! 1 =
        Some (τ, Call Push w2)).
      { eapply prefix_lookup_Some; [exact Hfilt_lookup|exact Hpfx]. }
      simpl in Hpfx_lookup. inversion Hpfx_lookup. }
  destruct (Nat.lt_total p1 p2) as [Hlt|[->|Hgt]]; [|done|].
  - exfalso. exact (Hsym p1 p2 v1 v2 Hp1 Hp2 Hlt).
  - exfalso. exact (Hsym p2 p1 v2 v1 Hp2 Hp1 Hgt).
Qed.

(* Helper 2: filter preserves strict ordering of positions. *)
Local Lemma filter_lookup_pos_lt {A} (P : A → Prop) `{!∀ x : A, Decision (P x)}
    (l : list A) (i j : nat) (x y : A) :
  filter P l !! i = Some x →
  filter P l !! j = Some y →
  i < j →
  ∃ ki kj, l !! ki = Some x ∧ l !! kj = Some y ∧ ki < kj.
Proof.
  revert i j. induction l as [|a l IH]; intros i j Hi Hj Hlt.
  { rewrite filter_nil in Hi. discriminate. }
  rewrite filter_cons in Hi, Hj.
  destruct (decide (P a)) as [HPa|HnPa].
  - destruct i as [|i'], j as [|j']; simpl in Hi, Hj.
    + lia.
    + injection Hi as <-.
      apply list_elem_of_lookup_2 in Hj as Hj_in.
      apply list_elem_of_filter in Hj_in as [_ Hj_in_l].
      apply list_elem_of_lookup_1 in Hj_in_l as [k Hk].
      exists 0, (Datatypes.S k). split_and!; [done|done|lia].
    + lia.
    + destruct (IH i' j' Hi Hj) as (ki & kj & Hki & Hkj & Hlt'); first lia.
      exists (Datatypes.S ki), (Datatypes.S kj). split_and!; [done|done|lia].
  - destruct (IH i j Hi Hj) as (ki & kj & Hki & Hkj & Hlt'); first done.
    exists (Datatypes.S ki), (Datatypes.S kj). split_and!; [done|done|lia].
Qed.

(* Helper 3: push_of_trace ts is sorted by call positions in ts. *)
Local Lemma push_of_trace_order_sorted rme valid_value ts τ_a τ_b va vb i_a i_b p_a p_b :
  per_tag_wellformed_bag rme valid_value ts →
  push_of_trace ts !! i_a = Some τ_a →
  push_of_trace ts !! i_b = Some τ_b →
  ts !! p_a = Some (τ_a, Call Push va) →
  ts !! p_b = Some (τ_b, Call Push vb) →
  i_a < i_b →
  p_a < p_b.
Proof.
  intros Hwf Hi_a Hi_b Hp_a Hp_b Hlt.
  rewrite /push_of_trace in Hi_a, Hi_b.
  rewrite list_lookup_fmap in Hi_a.
  rewrite list_lookup_fmap in Hi_b.
  apply fmap_Some_1 in Hi_a as ([τ_a' x_a] & Hf_a & ->).
  apply fmap_Some_1 in Hi_b as ([τ_b' x_b] & Hf_b & ->).
  apply list_elem_of_lookup_2 in Hf_a as Ha_in.
  apply list_elem_of_filter in Ha_in as [[w_a Hev_a] _]. simpl in Hev_a. subst x_a.
  apply list_elem_of_lookup_2 in Hf_b as Hb_in.
  apply list_elem_of_filter in Hb_in as [[w_b Hev_b] _]. simpl in Hev_b. subst x_b.
  destruct (filter_lookup_pos_lt _ ts i_a i_b _ _ Hf_a Hf_b Hlt)
    as (k_a & k_b & Hk_a & Hk_b & Hk_lt).
  pose proof (push_call_pos_unique _ _ _ _ _ _ _ _ Hwf Hk_a Hp_a) as ->.
  pose proof (push_call_pos_unique _ _ _ _ _ _ _ _ Hwf Hk_b Hp_b) as ->.
  exact Hk_lt.
Qed.

(* Helper: list_difference equals filter (∉ k). *)
Local Lemma list_difference_eq_filter {A} `{!EqDecision A} (l k : list A) :
  list_difference l k = filter (λ x, x ∉ k) l.
Proof.
  induction l as [|a l IH]; first by rewrite filter_nil.
  simpl. case_decide as Hmem.
  - rewrite filter_cons_False; [exact IH|by intros H; apply H].
  - rewrite filter_cons_True //. by f_equal.
Qed.

(* Helper 4: Inverse of push_of_trace_order_sorted: smaller call position → smaller index. *)
Local Lemma push_of_trace_index_lt rme valid_value ts τ_a τ_b va vb i_a i_b p_a p_b :
  per_tag_wellformed_bag rme valid_value ts →
  τ_a ≠ τ_b →
  push_of_trace ts !! i_a = Some τ_a →
  push_of_trace ts !! i_b = Some τ_b →
  ts !! p_a = Some (τ_a, Call Push va) →
  ts !! p_b = Some (τ_b, Call Push vb) →
  p_a < p_b →
  i_a < i_b.
Proof.
  intros Hwf Hne Hi_a Hi_b Hp_a Hp_b Hp_lt.
  destruct (Nat.lt_total i_a i_b) as [Hlt|[Heq|Hgt]]; first done.
  - exfalso. rewrite Heq Hi_b in Hi_a. injection Hi_a as ?. by apply Hne.
  - exfalso.
    pose proof (push_of_trace_order_sorted _ _ _ _ _ _ _ _ _ _ _ Hwf Hi_b Hi_a Hp_b Hp_a Hgt). lia.
Qed.

(* Helper 5: pre_of_trace ts e1 e2 + Hwf + e1, e2 push tags →
   p_e1c < p_e2c (call positions in ts). *)
Local Lemma pre_of_trace_push_call_lt rme valid_value ts e1 e2 v1 v2 :
  per_tag_wellformed_bag rme valid_value ts →
  pre_of_trace ts e1 e2 →
  (e1, Call Push v1) ∈ ts →
  (e2, Call Push v2) ∈ ts →
  ∃ p1 p2, ts !! p1 = Some (e1, Call Push v1) ∧
           ts !! p2 = Some (e2, Call Push v2) ∧
           p1 < p2.
Proof.
  intros Hwf Hpre He1c He2c.
  rewrite /pre_of_trace in Hpre.
  destruct (ret_of_tag ts e1) as [[p_e1r [τ_e1r ev_e1r]]|] eqn:He1r;
    simpl in Hpre; last done.
  destruct (call_of_tag ts e2) as [[p_e2c [τ_e2c ev_e2c]]|] eqn:He2c_lk;
    simpl in Hpre; last done.
  apply list_find_Some in He1r as (Hlk_e1r & [Hτ_e1r Hev_e1r] & Hbef_e1r).
  simpl in Hτ_e1r, Hev_e1r. subst τ_e1r.
  destruct ev_e1r as [?|? ?|r1]; try done.
  apply list_find_Some in He2c_lk as (Hlk_e2c & [Hτ_e2c Hev_e2c] & Hbef_e2c).
  simpl in Hτ_e2c, Hev_e2c. subst τ_e2c.
  destruct ev_e2c as [v_e2c|? ?|?]; try done.
  (* From Hwf at e1, push branch: filter τ=e1 ts contains both Call (Push v1) and Ret r1. *)
  destruct (Hwf e1) as [(v1' & _ & Hpfx_e1)|(r1' & _ & Hpfx_e1)]; cycle 1.
  { exfalso.
    assert (Hin : (e1, Call Push v1) ∈ filter (λ x : positive * trace, x.1 = e1) ts).
    { apply list_elem_of_filter; done. }
    eapply elem_of_prefix in Hin; last exact Hpfx_e1.
    apply elem_of_cons in Hin as [Habs|Hin].
    - injection Habs as Habs. discriminate.
    - apply elem_of_cons in Hin as [Habs|?]; [discriminate|by set_solver]. }
  apply list_elem_of_lookup_1 in He1c as [p_e1c Hlk_e1c].
  apply list_elem_of_lookup_1 in He2c as [p_e2c' Hlk_e2c'].
  exists p_e1c, p_e2c'.
  split; first done.
  split; first done.
  (* Need p_e1c < p_e2c'. *)
  (* p_e1c is some Call position of e1. Hlk_e2c says p_e2c is FIRST Call of e2.
     p_e2c' is some Call position of e2.
     By per_tag_wellformed at e2, e2 has unique Call position. So p_e2c = p_e2c'. *)
  assert (Hp_e1c_lt_p_e1r : p_e1c < p_e1r).
  { destruct (Nat.lt_total p_e1c p_e1r) as [Hlt|[Heq|Hgt]]; first done.
    - rewrite Heq Hlk_e1r in Hlk_e1c. injection Hlk_e1c as Habs. discriminate.
    - exfalso.
      assert (Hfilt_eq : filter (λ x : positive * trace, x.1 = e1) ts =
        filter (λ x : positive * trace, x.1 = e1) (take p_e1r ts) ++
        [(e1, Ret r1)] ++
        filter (λ x : positive * trace, x.1 = e1) (drop (Datatypes.S p_e1r) ts)).
      { rewrite -{1}(take_drop_middle ts p_e1r _ Hlk_e1r).
        rewrite filter_app filter_cons_True //. }
      assert (Hin_drop : (e1, Call Push v1) ∈
                filter (λ x : positive * trace, x.1 = e1) (drop (Datatypes.S p_e1r) ts)).
      { apply list_elem_of_filter; split; [done|].
        apply list_elem_of_lookup_2 with (i := p_e1c - Datatypes.S p_e1r).
        rewrite lookup_drop.
        replace (Datatypes.S p_e1r + (p_e1c - Datatypes.S p_e1r)) with p_e1c by lia.
        exact Hlk_e1c. }
      apply list_elem_of_lookup_1 in Hin_drop as [k Hk].
      pose proof (lookup_lt_Some _ _ _ Hk) as Hk_lt.
      pose proof (prefix_length _ _ Hpfx_e1) as Hpfx_len. simpl in Hpfx_len.
      rewrite Hfilt_eq !length_app /= in Hpfx_len.
      assert (Hlen_take_z : length (filter (λ x : positive * trace, x.1 = e1) (take p_e1r ts)) = 0) by lia.
      apply length_zero_iff_nil in Hlen_take_z.
      assert (Hk_z : k = 0) by lia. subst k.
      assert (Hfilt_lookup : filter (λ x : positive * trace, x.1 = e1) ts !! 1 =
        Some (e1, Call Push v1)).
      { rewrite Hfilt_eq Hlen_take_z /=. exact Hk. }
      assert (Hpfx_lookup : [(e1, Call Push v1'); (e1, Ret #())] !! 1 =
        Some (e1, Call Push v1)).
      { eapply prefix_lookup_Some; [exact Hfilt_lookup|exact Hpfx_e1]. }
      simpl in Hpfx_lookup. inversion Hpfx_lookup. }
  (* Now p_e1r < p_e2c (from Hpre). Need p_e2c ≤ p_e2c'. *)
  pose proof (push_call_pos_unique _ _ _ _ _ _ _ _ Hwf Hlk_e2c' Hlk_e2c') as _.
  (* Either p_e2c = p_e2c' (good), or p_e2c < p_e2c' or p_e2c > p_e2c'. *)
  destruct (Nat.lt_total p_e2c p_e2c') as [Hlt|[<-|Hgt]]; first lia.
  - lia.
  - exfalso. apply (Hbef_e2c p_e2c' (e2, Call Push v2) Hlk_e2c' Hgt).
    split; [done|by eexists].
Qed.

(* Helper 6: For e1, e2 in list_difference (push_of_trace ts) excluded at indices j1 < j2,
   call positions in ts are p1 < p2. *)
Local Lemma ump_init_index_lt_call_pos_lt rme valid_value ts (excluded : list positive)
    e1 e2 p1 p2 v1 v2 j1 j2 :
  per_tag_wellformed_bag rme valid_value ts →
  ts !! p1 = Some (e1, Call Push v1) →
  ts !! p2 = Some (e2, Call Push v2) →
  list_difference (push_of_trace ts) excluded !! j1 = Some e1 →
  list_difference (push_of_trace ts) excluded !! j2 = Some e2 →
  j1 < j2 →
  p1 < p2.
Proof.
  intros Hwf Hp1 Hp2 Hj1 Hj2 Hj_lt.
  rewrite list_difference_eq_filter in Hj1 Hj2.
  destruct (filter_lookup_pos_lt _ _ j1 j2 _ _ Hj1 Hj2 Hj_lt) as (i_a & i_b & Hi_a & Hi_b & Hi_lt).
  rewrite /push_of_trace in Hi_a, Hi_b.
  rewrite list_lookup_fmap in Hi_a.
  rewrite list_lookup_fmap in Hi_b.
  apply fmap_Some_1 in Hi_a as ([τ_a ev_a] & Hf_a & ?). simpl in *. subst τ_a.
  apply fmap_Some_1 in Hi_b as ([τ_b ev_b] & Hf_b & ?). simpl in *. subst τ_b.
  destruct (filter_lookup_pos_lt _ ts i_a i_b _ _ Hf_a Hf_b Hi_lt)
    as (q_a & q_b & Hq_a & Hq_b & Hq_lt).
  apply list_elem_of_lookup_2 in Hf_a as Hin_a.
  apply list_elem_of_filter in Hin_a as [[w_a Hev_a] _]. simpl in Hev_a. subst ev_a.
  apply list_elem_of_lookup_2 in Hf_b as Hin_b.
  apply list_elem_of_filter in Hin_b as [[w_b Hev_b] _]. simpl in Hev_b. subst ev_b.
  pose proof (push_call_pos_unique _ _ _ _ _ _ _ _ Hwf Hq_a Hp1) as ->.
  pose proof (push_call_pos_unique _ _ _ _ _ _ _ _ Hwf Hq_b Hp2) as ->.
  exact Hq_lt.
Qed.

(* Helper 7: For e1, e2 in list_difference (push_of_trace ts) excluded, if call positions
   p1 < p2 then j1 < j2. *)
Local Lemma ump_init_call_pos_lt_index_lt rme valid_value ts (excluded : list positive)
    e1 e2 p1 p2 v1 v2 j1 j2 :
  per_tag_wellformed_bag rme valid_value ts →
  ts !! p1 = Some (e1, Call Push v1) →
  ts !! p2 = Some (e2, Call Push v2) →
  list_difference (push_of_trace ts) excluded !! j1 = Some e1 →
  list_difference (push_of_trace ts) excluded !! j2 = Some e2 →
  p1 < p2 →
  j1 < j2.
Proof.
  intros Hwf Hp1 Hp2 Hj1 Hj2 Hp_lt.
  destruct (Nat.lt_total j1 j2) as [Hlt|[Heq|Hgt]]; first done.
  - exfalso. subst j2. rewrite Hj1 in Hj2. injection Hj2 as ->.
    pose proof (push_call_pos_unique _ _ _ _ _ _ _ _ Hwf Hp1 Hp2) as ->. lia.
  - exfalso.
    pose proof (ump_init_index_lt_call_pos_lt _ _ _ _ _ _ _ _ _ _ _ _ Hwf Hp2 Hp1 Hj2 Hj1 Hgt). lia.
Qed.


Lemma close_preserves_order_correct_matched rme valid_value ts m :
  per_tag_wellformed_bag rme valid_value ts →
  I_queue_pre ts m →
  order_correct_matched (close_trace ts m).1 (close_trace ts m).2.
Proof.
  intros Hwf HIqp e1 e2 d1 d2 Hpre_close He1d1 He2d2 Hpre_close_d.
  destruct HIqp as (Hvalid & _ & Hocm & Hocum).
  pose proof Hvalid as Hvalid'.
  destruct Hvalid as (Hcov & [Hnd_m1 Hnd_m2] & Hforall).
  revert Hpre_close He1d1 He2d2 Hpre_close_d.
  unfold close_trace.
  destruct (bag.close.unpaired_operations ts m) as [[up upop] ump_init] eqn:Hops.
  destruct (bag.close.complete_trace_add_match upop m ump_init) as [nm1 ump'] eqn:Hmatch.
  set (calls := bag.close.extract_calls ts).
  set (np := bag.close.complete_trace_add_push up).
  set (npop1 := bag.close.complete_trace_remove_pop upop calls (m ++ nm1)).
  set (U := list_difference upop (m ++ nm1).*2).
  set (ts' := filter (λ x : positive * trace, x.1 ∉ U) ts).
  set (nm2 := bag.close.close_trace_add_match ump' (bag.close.max_tag ts.*1 + 1)).
  set (npop2_calls := bag.close.close_trace_add_pop_calls nm2).
  set (npop2_rets := bag.close.close_trace_add_pop_rets calls nm2).
  set (npop2 := bag.close.close_trace_add_pop calls nm2).
  simpl.
  intros Hpre_close He1d1 He2d2 Hpre_close_d.
  (* Useful facts *)
  assert (Hupop_is : upop = (bag.close.unpaired_operations ts m).1.2)
    by (rewrite /bag.close.unpaired_operations in Hops; by injection Hops as _ <- _).
  assert (Hump_init_is : ump_init = (bag.close.unpaired_operations ts m).2)
    by (rewrite /bag.close.unpaired_operations in Hops; by injection Hops as _ _ <-).
  assert (Hupop_nd : NoDup upop)
    by (rewrite Hupop_is; eapply bag.close.unpaired_pops_nodup; exact Hwf).
  assert (Hupop_sub_pop : upop ⊆ pop_of_trace ts).
  { rewrite Hupop_is. intros τ Hin. by eapply bag.close.unpaired_pop_is_pop. }
  assert (Hnm1_eq : nm1 = (bag.close.complete_trace_add_match upop m ump_init).1)
    by (rewrite Hmatch; done).
  assert (Hnm1_snd_sub_upop : nm1.*2 ⊆ upop)
    by (rewrite Hnm1_eq; apply bag.close.complete_trace_add_match_snd_sub).
  (* Key: e1, e2 are push tags in ts; they have Call Push in ts. *)
  assert (Hpush_in_ts : ∀ e d, (e, d) ∈ m ∨ (e, d) ∈ nm1 ∨ (e, d) ∈ nm2 →
    ∃ v, (e, Call Push v) ∈ ts).
  { intros e d [Hin | [Hin | Hin]].
    - destruct (valid_match_call_push _ _ _ _ Hvalid' Hin) as [v ?]. by exists v.
    - assert (Hin' : e ∈ nm1.*1).
      { apply (list_elem_of_fmap_2 fst _ (e, d)). exact Hin. }
      rewrite Hnm1_eq in Hin'.
      apply bag.close.complete_trace_add_match_fst_sub in Hin'.
      rewrite Hump_init_is /bag.close.unpaired_operations /= in Hin'.
      apply list_elem_of_difference in Hin' as [Hin_push _].
      apply (list_elem_of_fmap_1 fst) in Hin_push as ([τ' ev] & Heq & Hin_filt).
      simpl in Heq. subst τ'.
      apply list_elem_of_filter in Hin_filt as [[v Hev] Hin_ts]. simpl in Hev. subst ev.
      by exists v.
    - assert (Hin' : e ∈ nm2.*1).
      { apply (list_elem_of_fmap_2 fst _ (e, d)). exact Hin. }
      rewrite /nm2 close_trace_add_match_fst_eq in Hin'.
      assert (Hsub : ump' ⊆ ump_init).
      { assert (Heq : ump' = (bag.close.complete_trace_add_match upop m ump_init).2)
          by (rewrite Hmatch; done).
        rewrite Heq. apply bag.close.complete_trace_add_match_remaining_sub. }
      apply Hsub in Hin'.
      rewrite Hump_init_is /bag.close.unpaired_operations /= in Hin'.
      apply list_elem_of_difference in Hin' as [Hin_push _].
      apply (list_elem_of_fmap_1 fst) in Hin_push as ([τ' ev] & Heq & Hin_filt).
      simpl in Heq. subst τ'.
      apply list_elem_of_filter in Hin_filt as [[v Hev] Hin_ts]. simpl in Hev. subst ev.
      by exists v. }
  (* Some additional facts we'll use throughout. *)
  assert (Hpush_not_U : ∀ τ, τ ∈ push_of_trace ts → τ ∉ U).
  { intros τ Hin Hni. apply list_elem_of_difference in Hni as [Hin_upop _].
    apply (push_xor_pop_of_trace ts rme valid_value τ Hwf Hin).
    by apply Hupop_sub_pop. }
  assert (Hd_in_m_or_nm1_not_U : ∀ d, d ∈ m.*2 ∨ d ∈ nm1.*2 → d ∉ U).
  { intros d Hin Hin_U.
    apply list_elem_of_difference in Hin_U as [_ Hni]. apply Hni.
    rewrite fmap_app elem_of_app. destruct Hin; by [left|right]. }
  assert (Hump_init_disj_m1 : ∀ τ, τ ∈ ump_init → τ ∉ m.*1).
  { rewrite Hump_init_is /bag.close.unpaired_operations /=.
    intros τ Hin Hin_m1.
    apply list_elem_of_difference in Hin as [_ Hni]. by apply Hni. }
  assert (Hump'_sub : ump' ⊆ ump_init).
  { assert (Heq : ump' = (bag.close.complete_trace_add_match upop m ump_init).2)
      by (rewrite Hmatch; done).
    rewrite Heq. apply bag.close.complete_trace_add_match_remaining_sub. }
  assert (Hpush_not_in_m1 : ∀ e, e ∈ nm1.*1 ∨ e ∈ nm2.*1 → e ∉ m.*1).
  { intros e [Hin|Hin] Hin_m1.
    - apply (Hump_init_disj_m1 e).
      + rewrite Hnm1_eq in Hin.
        apply bag.close.complete_trace_add_match_fst_sub in Hin. exact Hin.
      + exact Hin_m1.
    - apply (Hump_init_disj_m1 e); last exact Hin_m1.
      apply Hump'_sub.
      rewrite /nm2 close_trace_add_match_fst_eq in Hin. exact Hin. }
  assert (Hd_in_m_or_nm1_call_pop : ∀ d, d ∈ m.*2 ∨ d ∈ nm1.*2 → (d, Call Pop #()) ∈ ts).
  { intros d [Hin|Hin].
    - apply list_elem_of_fmap_1 in Hin as ([τ1' τ2'] & -> & Hin).
      exact (valid_match_call_pop _ _ _ _ Hvalid' Hin).
    - apply Hnm1_snd_sub_upop in Hin.
      apply Hupop_sub_pop, pop_tag_in_trace in Hin. exact Hin. }
  destruct (Hpush_in_ts e1 d1) as [v1 He1_in_ts].
  { rewrite !elem_of_app in He1d1. by destruct He1d1 as [|[|]]; tauto. }
  destruct (Hpush_in_ts e2 d2) as [v2 He2_in_ts].
  { rewrite !elem_of_app in He2d2. by destruct He2d2 as [|[|]]; tauto. }
  assert (He1_push : e1 ∈ push_of_trace ts).
  { apply (list_elem_of_fmap_2 fst _ (e1, Call Push v1)).
    apply list_elem_of_filter; split; [eexists; reflexivity|exact He1_in_ts]. }
  assert (He2_push : e2 ∈ push_of_trace ts).
  { apply (list_elem_of_fmap_2 fst _ (e2, Call Push v2)).
    apply list_elem_of_filter; split; [eexists; reflexivity|exact He2_in_ts]. }
  assert (He1_not_U : e1 ∉ U) by exact (Hpush_not_U _ He1_push).
  assert (He2_not_U : e2 ∉ U) by exact (Hpush_not_U _ He2_push).
  (* Case split on (e2, d2). *)
  apply elem_of_app in He2d2 as [He2d2_m | He2d2_rest].
  - (* Case A: (e2, d2) ∈ m. Apply Hocum to derive (e1, d1) ∈ m. Then Hocm. *)
    assert (He2_in_m1 : e2 ∈ m.*1).
    { apply (list_elem_of_fmap_2 fst _ (e2, d2)). exact He2d2_m. }
    assert (Hd2_in_m2 : d2 ∈ m.*2).
    { apply (list_elem_of_fmap_2 snd _ (e2, d2)). exact He2d2_m. }
    assert (Hd2_not_U : d2 ∉ U) by exact (Hd_in_m_or_nm1_not_U _ (or_introl Hd2_in_m2)).
    assert (Hd2_call_pop_ts : (d2, Call Pop #()) ∈ ts)
      by exact (Hd_in_m_or_nm1_call_pop _ (or_introl Hd2_in_m2)).
    (* Lift pre_close e1 e2 to pre_ts e1 e2. *)
    assert (Hpre_ts : pre_of_trace ts e1 e2).
    { exact (pre_close_to_pre_ts U ts (np ++ npop2_calls ++ npop1 ++ npop2_rets) e1 e2 _ _
              He1_not_U He2_not_U He2_in_ts Hpre_close). }
    (* Apply Hocum to get e1 ∈ m.*1. *)
    assert (He1_in_m1 : e1 ∈ m.*1) by exact (Hocum _ _ Hpre_ts He1_push He2_in_m1).
    (* So (e1, d1) ∈ m_close + e1 ∈ m.*1 → (e1, d1) ∈ m (by NoDup m.*1). *)
    assert (He1d1_m : (e1, d1) ∈ m).
    { rewrite !elem_of_app in He1d1.
      destruct He1d1 as [Hin_m | [Hin_nm1 | Hin_nm2]]; first done.
      - exfalso.
        assert (He1_in_nm1 : e1 ∈ nm1.*1)
          by (apply (list_elem_of_fmap_2 fst _ (e1, d1)); exact Hin_nm1).
        exact (Hpush_not_in_m1 e1 (or_introl He1_in_nm1) He1_in_m1).
      - exfalso.
        assert (He1_in_nm2 : e1 ∈ nm2.*1)
          by (apply (list_elem_of_fmap_2 fst _ (e1, d1)); exact Hin_nm2).
        exact (Hpush_not_in_m1 e1 (or_intror He1_in_nm2) He1_in_m1). }
    assert (Hd1_in_m2 : d1 ∈ m.*2).
    { apply (list_elem_of_fmap_2 snd _ (e1, d1)). exact He1d1_m. }
    assert (Hd1_not_U : d1 ∉ U) by exact (Hd_in_m_or_nm1_not_U _ (or_introl Hd1_in_m2)).
    assert (Hd1_call_pop_ts : (d1, Call Pop #()) ∈ ts)
      by exact (Hd_in_m_or_nm1_call_pop _ (or_introl Hd1_in_m2)).
    (* Apply Hocm: ¬pre_ts d2 d1. *)
    assert (Hno_pre_ts : ¬ pre_of_trace ts d2 d1)
      by exact (Hocm _ _ _ _ Hpre_ts He1d1_m He2d2_m).
    (* Lift back to ¬pre_close d2 d1. *)
    revert Hpre_close_d.
    apply (not_pre_ts_to_not_pre_close U ts (np ++ npop2_calls ++ npop1 ++ npop2_rets) d2 d1 _ _
            Hd2_not_U Hd1_not_U Hd1_call_pop_ts Hno_pre_ts).
  - (* Cases B and C: d2 has no Ret in ts (d2 ∈ nm1.*2 ⊆ upop or d2 ∈ nm2.*2 fresh).
       In all such cases, d2's first Ret in close is at position ≥ length ts'.
       For (e1, d1) ∈ m or nm1, d1's call is in ts' (position < length ts'),
       so ¬pre_close d2 d1 holds by position. The remaining sub-cases (e1, d1) ∈ nm2
       require more delicate arguments. *)
    assert (Hd2_no_ret_in_ts : ret_of_tag ts d2 = None).
    { destruct (ret_of_tag ts d2) as [[i x]|] eqn:Hret; last done.
      exfalso.
      apply elem_of_app in He2d2_rest as [Hin_nm1|Hin_nm2].
      - (* d2 ∈ nm1.*2 ⊆ upop, so no Ret in ts. *)
        assert (Hd2_in_upop : d2 ∈ upop).
        { apply Hnm1_snd_sub_upop.
          apply (list_elem_of_fmap_2 snd _ (e2, d2)). exact Hin_nm1. }
        rewrite Hupop_is /bag.close.unpaired_operations /= in Hd2_in_upop.
        apply list_elem_of_difference in Hd2_in_upop as [_ Hno_ret].
        apply Hno_ret.
        destruct x as [τ_x ev_x].
        apply list_find_Some in Hret as (Hlk_ret & [Hτ Hev] & _).
        simpl in Hτ, Hev. subst τ_x.
        destruct ev_x as [|? ?|w]; simpl in Hev; try done.
        assert (Hd2_call_pop : (d2, Call Pop #()) ∈ ts).
        { apply Hd_in_m_or_nm1_call_pop. right.
          apply (list_elem_of_fmap_2 snd _ (e2, d2)). exact Hin_nm1. }
        apply list_elem_of_lookup_2 in Hlk_ret as Hin_ts_ret.
        apply (list_elem_of_fmap_2 fst _ (d2, Ret w)).
        apply list_elem_of_filter; split; [|exact Hin_ts_ret].
        (* Hwf says w = encode_response r for some r (d2 is pop tag). *)
        destruct (Hwf d2) as [(v' & _ & Hpfx)|(r' & _ & Hpfx)].
        + exfalso.
          assert (Hin_call : (d2, Call Pop #()) ∈ filter (λ x, x.1 = d2) ts).
          { apply list_elem_of_filter; done. }
          eapply elem_of_prefix in Hin_call; last exact Hpfx.
          apply elem_of_cons in Hin_call as [Habs|Hin_call].
          * injection Habs as Habs. discriminate.
          * apply elem_of_cons in Hin_call as [Habs|?]; [discriminate|by set_solver].
        + assert (Hin_filt : (d2, Ret w) ∈ filter (λ x, x.1 = d2) ts).
          { apply list_elem_of_filter; done. }
          eapply elem_of_prefix in Hin_filt; last exact Hpfx.
          apply elem_of_cons in Hin_filt as [Habs|Hin_filt].
          * injection Habs as Habs. discriminate.
          * apply elem_of_cons in Hin_filt as [Heq|?]; last by set_solver.
            injection Heq as ->. by eexists.
      - (* d2 ∈ nm2.*2 is fresh (> max_tag), but we have ts !! i = (d2, Ret w). *)
        destruct x as [τ_x ev_x].
        apply list_find_Some in Hret as (Hlk_ret & [Hτ_eq _] & _).
        simpl in Hτ_eq. subst τ_x.
        apply list_elem_of_lookup_2 in Hlk_ret.
        apply bag.close.tag_in_ts_le_max_tag in Hlk_ret.
        assert (Hd2_in_nm2_2 : d2 ∈ nm2.*2)
          by (apply (list_elem_of_fmap_2 snd _ (e2, d2)); exact Hin_nm2).
        apply list_elem_of_fmap_1 in Hd2_in_nm2_2 as ([τ1' τ2'] & Heq & Hin).
        simpl in Heq. subst τ2'.
        apply bag.close.close_trace_add_match_tags_fresh in Hin. lia. }
    (* From d2 having no Ret in ts, derive d2 having no Ret in ts' (since ts' ⊆ ts). *)
    assert (Hd2_no_ret_in_ts' : ret_of_tag ts' d2 = None).
    { destruct (ret_of_tag ts' d2) as [[i x]|] eqn:Hret_ts'; last done.
      exfalso.
      apply list_find_Some in Hret_ts' as (Hlk & [Hτ Hev] & _).
      simpl in Hτ. destruct x as [τ_x ev_x]. simpl in Hτ, Hev. subst τ_x.
      destruct ev_x as [|? ?|w]; simpl in Hev; try done.
      apply list_elem_of_lookup_2 in Hlk.
      rewrite /ts' in Hlk.
      apply list_elem_of_filter in Hlk as [_ Hin_ts].
      rewrite /ret_of_tag in Hd2_no_ret_in_ts.
      apply list_find_None in Hd2_no_ret_in_ts.
      rewrite Forall_forall in Hd2_no_ret_in_ts.
      apply (Hd2_no_ret_in_ts (d2, Ret w) Hin_ts).
      split; [done|by eexists]. }
    (* Now: d2's first Ret in close = ts' ++ rest is at position ≥ length ts'. *)
    assert (Hd2_ret_close_late : ∀ ir x, ret_of_tag (ts' ++ np ++ npop2_calls ++ npop1 ++ npop2_rets) d2 = Some (ir, x) → ir ≥ length ts').
    { intros ir x. exact (ret_after_prefix ts' (np ++ npop2_calls ++ npop1 ++ npop2_rets) d2 ir x Hd2_no_ret_in_ts'). }
    (* d2 ∉ U: d2 has Ret in close (in npop1 or npop2). For nm1.*2, d2 ∈ upop ⊆ list_difference call_pops ret_pops. d2 ∉ ret_pops in ts (Hd2_no_ret_in_ts). For nm2.*2, d2 fresh.
       For both, d2 ∉ upop only when it's in nm2 (fresh, not in ts). For nm1, d2 ∈ nm1.*2 ⊆ (m++nm1).*2, so d2 ∉ U. For nm2, d2 fresh; not in upop (upop tags are in ts), so d2 ∉ U. *)
    assert (Hd2_not_U : d2 ∉ U).
    { intros Hin_U. apply list_elem_of_difference in Hin_U as [Hin_upop Hni].
      apply elem_of_app in He2d2_rest as [Hin_nm1|Hin_nm2].
      - apply Hni. rewrite fmap_app elem_of_app. right.
        apply (list_elem_of_fmap_2 snd _ (e2, d2)). exact Hin_nm1.
      - assert (Hd2_in_nm2_2 : d2 ∈ nm2.*2)
          by (apply (list_elem_of_fmap_2 snd _ (e2, d2)); exact Hin_nm2).
        apply Hupop_sub_pop in Hin_upop.
        apply pop_tag_in_trace in Hin_upop.
        pose proof (bag.close.tag_in_ts_le_max_tag _ _ _ Hin_upop) as Hk_le.
        apply list_elem_of_fmap_1 in Hd2_in_nm2_2 as ([τ1' τ2'] & Heq & Hin_nm2_pair).
        simpl in Heq. subst τ2'.
        apply bag.close.close_trace_add_match_tags_fresh in Hin_nm2_pair. lia. }
    (* Now case split on (e1, d1). *)
    rewrite !elem_of_app in He1d1.
    destruct He1d1 as [He1d1_m | [He1d1_nm1 | He1d1_nm2]].
    + (* Sub-case: (e1, d1) ∈ m. d1 ∈ m.*2, has Call in ts'. ¬pre_close by position. *)
      assert (Hd1_in_m2 : d1 ∈ m.*2)
        by (apply (list_elem_of_fmap_2 snd _ (e1, d1)); exact He1d1_m).
      assert (Hd1_not_U : d1 ∉ U)
        by exact (Hd_in_m_or_nm1_not_U _ (or_introl Hd1_in_m2)).
      assert (Hd1_call_pop_ts : (d1, Call Pop #()) ∈ ts)
        by exact (Hd_in_m_or_nm1_call_pop _ (or_introl Hd1_in_m2)).
      assert (Hd1_call_in_ts' : (d1, Call Pop #()) ∈ ts')
        by (apply list_elem_of_filter_2; done).
      destruct (call_in_prefix_lt ts' (np ++ npop2_calls ++ npop1 ++ npop2_rets) d1 _ _ Hd1_call_in_ts')
        as (i_c & x_c & Hcall_close & Hi_c_lt).
      apply (pre_close_to_pre_ts U ts (np ++ npop2_calls ++ npop1 ++ npop2_rets) d2 d1 _ _
              Hd2_not_U Hd1_not_U Hd1_call_pop_ts) in Hpre_close_d.
      apply (pre_of_trace_no_ret ts d2 d1 Hd2_no_ret_in_ts Hpre_close_d).
    + (* Sub-case: (e1, d1) ∈ nm1. d1 ∈ nm1.*2, has Call in ts'. *)
      assert (Hd1_in_nm1_2 : d1 ∈ nm1.*2)
        by (apply (list_elem_of_fmap_2 snd _ (e1, d1)); exact He1d1_nm1).
      assert (Hd1_not_U : d1 ∉ U)
        by exact (Hd_in_m_or_nm1_not_U _ (or_intror Hd1_in_nm1_2)).
      assert (Hd1_call_pop_ts : (d1, Call Pop #()) ∈ ts)
        by exact (Hd_in_m_or_nm1_call_pop _ (or_intror Hd1_in_nm1_2)).
      assert (Hd1_call_in_ts' : (d1, Call Pop #()) ∈ ts')
        by (apply list_elem_of_filter_2; done).
      apply (pre_close_to_pre_ts U ts (np ++ npop2_calls ++ npop1 ++ npop2_rets) d2 d1 _ _
              Hd2_not_U Hd1_not_U Hd1_call_pop_ts) in Hpre_close_d.
      apply (pre_of_trace_no_ret ts d2 d1 Hd2_no_ret_in_ts Hpre_close_d).
    + (* Sub-case: (e1, d1) ∈ nm2. *)
      exfalso.
      assert (He1_in_nm2_1 : e1 ∈ nm2.*1)
        by (apply (list_elem_of_fmap_2 fst _ (e1, d1)); exact He1d1_nm2).
      rewrite /nm2 close_trace_add_match_fst_eq in He1_in_nm2_1.
      rename He1_in_nm2_1 into He1_in_ump'.
      assert (He1_in_ump_init : e1 ∈ ump_init) by exact (Hump'_sub _ He1_in_ump').
      rewrite Hump_init_is /bag.close.unpaired_operations /= in He1_in_ump_init.
      apply list_elem_of_difference in He1_in_ump_init as [_ He1_not_in_m1].
      destruct (ret_of_tag ts e1) as [[p_e1r [τ_e1r ev_e1r]]|] eqn:He1_ret_ts;
        cycle 1.
      * (* e1 has no Ret in ts. *)
        assert (He1_no_ret_in_ts : ret_of_tag ts e1 = None) by exact He1_ret_ts.
        assert (He1_no_ret_in_ts' : ret_of_tag ts' e1 = None).
        { destruct (ret_of_tag ts' e1) as [[i [τ_x ev_x]]|] eqn:Hret_ts'; last done.
          exfalso.
          apply list_find_Some in Hret_ts' as (Hlk & [Hτ Hev] & _).
          simpl in Hτ, Hev. subst τ_x.
          destruct ev_x as [?|? ?|r]; try done.
          apply list_elem_of_lookup_2 in Hlk. rewrite /ts' in Hlk.
          apply list_elem_of_filter in Hlk as [_ Hin_ts].
          rewrite /ret_of_tag in He1_no_ret_in_ts.
          apply list_find_None in He1_no_ret_in_ts.
          rewrite Forall_forall in He1_no_ret_in_ts.
          apply (He1_no_ret_in_ts (e1, Ret r) Hin_ts). split; [done|by eexists]. }
        assert (He2_call_in_ts' : (e2, Call Push v2) ∈ ts')
          by (apply list_elem_of_filter_2; done).
        rewrite /pre_of_trace in Hpre_close.
        destruct (ret_of_tag (ts' ++ np ++ npop2_calls ++ npop1 ++ npop2_rets) e1)
          as [[i_ret x_ret]|] eqn:Hret_close; last done.
        pose proof (ret_after_prefix _ _ _ _ _ He1_no_ret_in_ts' Hret_close) as Hret_ge.
        destruct (call_in_prefix_lt ts' (np ++ npop2_calls ++ npop1 ++ npop2_rets) e2 _ _ He2_call_in_ts')
          as (i_call & x_call & Hcall_close & Hi_call_lt).
        rewrite Hcall_close /= in Hpre_close. lia.
      * (* e1 has Ret in ts. Lift Hpre_close to Hpre_ts. *)
        apply list_find_Some in He1_ret_ts as (Hlk_e1r & [Hτ_e1r Hev_e1r] & _).
        simpl in Hτ_e1r, Hev_e1r. subst τ_e1r.
        destruct ev_e1r as [?|? ?|r1]; try done.
        assert (Hpre_ts : pre_of_trace ts e1 e2).
        { exact (pre_close_to_pre_ts U ts (np ++ npop2_calls ++ npop1 ++ npop2_rets) e1 e2 _ _
                  He1_not_U He2_not_U He2_in_ts Hpre_close). }
        destruct (pre_of_trace_push_call_lt _ _ _ _ _ _ _ Hwf Hpre_ts He1_in_ts He2_in_ts)
          as (p_e1c & p_e2c & Hp_e1c & Hp_e2c & Hp_lt).
        (* Bridge ump_init to list_difference (push_of_trace ts) m.*1. *)
        assert (Hump_init_eq : ump_init = list_difference (push_of_trace ts) m.*1).
        { rewrite Hump_init_is /bag.close.unpaired_operations /=. done. }
        (* e1 ∈ ump_init at some index j_e1. *)
        apply list_elem_of_lookup_1 in He1_in_ump' as [k1 Hk1_ump'].
        pose proof (bag.close.complete_trace_add_match_split upop m ump_init) as Hsplit.
        rewrite Hmatch /= in Hsplit.
        assert (Hk1_init : ump_init !! (length nm1.*1 + k1) = Some e1).
        { rewrite Hsplit lookup_app_r; last lia.
          replace (length nm1.*1 + k1 - length nm1.*1) with k1 by lia. exact Hk1_ump'. }
        rewrite Hump_init_eq in Hk1_init.
        (* Now case-split on (e2, d2). *)
        apply elem_of_app in He2d2_rest as [He2d2_nm1 | He2d2_nm2].
        -- (* Sub-case (a): (e2, d2) ∈ nm1. *)
           assert (He2_in_nm1_1 : e2 ∈ nm1.*1)
             by (apply (list_elem_of_fmap_2 fst _ (e2, d2)); exact He2d2_nm1).
           apply list_elem_of_lookup_1 in He2_in_nm1_1 as [k2 Hk2].
           pose proof (lookup_lt_Some _ _ _ Hk2) as Hk2_lt.
           assert (Hk2_init : ump_init !! k2 = Some e2).
           { rewrite Hsplit lookup_app_l; first exact Hk2. by eapply lookup_lt_Some. }
           rewrite Hump_init_eq in Hk2_init.
           pose proof (ump_init_index_lt_call_pos_lt _ _ _ _ _ _ _ _ _ _ _ _ Hwf
                         Hp_e2c Hp_e1c Hk2_init Hk1_init) as Hcall_lt.
           assert (Hk2_lt' : k2 < length nm1.*1 + k1) by lia.
           specialize (Hcall_lt Hk2_lt'). lia.
        -- (* Sub-case (b): (e2, d2) ∈ nm2. *)
           assert (He2_in_nm2_1 : e2 ∈ nm2.*1)
             by (apply (list_elem_of_fmap_2 fst _ (e2, d2)); exact He2d2_nm2).
           rewrite /nm2 close_trace_add_match_fst_eq in He2_in_nm2_1.
           apply list_elem_of_lookup_1 in He2_in_nm2_1 as [k2 Hk2_ump'].
           pose proof (bag.close.complete_trace_add_match_split upop m ump_init) as Hsplit2.
           rewrite Hmatch /= in Hsplit2.
           assert (Hk2_init : ump_init !! (length nm1.*1 + k2) = Some e2).
           { rewrite Hsplit2 lookup_app_r; last lia.
             replace (length nm1.*1 + k2 - length nm1.*1) with k2 by lia. exact Hk2_ump'. }
           rewrite Hump_init_eq in Hk2_init.
           pose proof (ump_init_call_pos_lt_index_lt _ _ _ _ _ _ _ _ _ _ _ _ Hwf
                         Hp_e1c Hp_e2c Hk1_init Hk2_init Hp_lt) as Hidx_lt.
           assert (Hk_lt : k1 < k2) by lia.
           (* Get the lookups of (e1, d1) and (e2, d2) in nm2. *)
           apply list_elem_of_lookup_1 in He1d1_nm2 as [k1' Hk1'_nm2].
           apply list_elem_of_lookup_1 in He2d2_nm2 as [k2' Hk2'_nm2].
           pose proof (bag.close.close_trace_add_match_lookup_inv _ _ _ _ _ Hk1'_nm2) as Hk1'_ump'.
           pose proof (bag.close.close_trace_add_match_lookup_inv _ _ _ _ _ Hk2'_nm2) as Hk2'_ump'.
           (* NoDup ump' to identify k1 = k1', k2 = k2'. *)
           assert (Hnd_ump_init : NoDup ump_init).
           { rewrite Hump_init_eq. apply NoDup_list_difference.
             apply (bag.close.call_push_tags_nodup _ _ _ Hwf). }
           assert (Hnd_ump' : NoDup ump').
           { pose proof (bag.close.complete_trace_add_match_remaining_nodup
               upop m ump_init Hnd_ump_init) as H.
             rewrite Hmatch /= in H. exact H. }
           assert (Hk1_eq : k1 = k1')
             by (eapply NoDup_lookup; [exact Hnd_ump'|exact Hk1_ump'|exact Hk1'_ump']).
           assert (Hk2_eq : k2 = k2')
             by (eapply NoDup_lookup; [exact Hnd_ump'|exact Hk2_ump'|exact Hk2'_ump']).
           subst k1' k2'.
           (* Compute positions of d1's Call and d2's Ret in close_trace.
              In the new layout, npop2_calls comes before npop1, and npop2_rets
              comes after npop1. So d1's Call sits at offset_calls + k1, and
              d2's Ret sits at offset_rets + k2. *)
           pose proof (lookup_lt_Some _ _ _ Hk1'_nm2) as Hk1_lt_nm2.
           pose proof (lookup_lt_Some _ _ _ Hk2'_nm2) as Hk2_lt_nm2.
           assert (Hlen_calls : length npop2_calls = length nm2)
             by (rewrite /npop2_calls /bag.close.close_trace_add_pop_calls length_fmap; reflexivity).
           assert (Hlen_rets : length npop2_rets = length nm2)
             by (rewrite /npop2_rets /bag.close.close_trace_add_pop_rets length_fmap; reflexivity).
           set (offset_calls := length ts' + length np).
           set (offset_rets := length ts' + length np + length npop2_calls + length npop1).
           assert (Hd1_call_close : (ts' ++ np ++ npop2_calls ++ npop1 ++ npop2_rets) !!
                                    (offset_calls + k1) = Some (d1, Call Pop #())).
           { rewrite /offset_calls.
             rewrite (lookup_app_r ts'); last lia.
             replace (length ts' + length np + k1 - length ts')
               with (length np + k1) by lia.
             rewrite (lookup_app_r np); last lia.
             replace (length np + k1 - length np) with k1 by lia.
             rewrite lookup_app_l; last (rewrite Hlen_calls; lia).
             rewrite /npop2_calls /bag.close.close_trace_add_pop_calls list_lookup_fmap.
             rewrite Hk1'_nm2 //. }
           assert (Hd2_ret_close : (ts' ++ np ++ npop2_calls ++ npop1 ++ npop2_rets) !!
                                   (offset_rets + k2) = Some (d2, Ret (bag.close.ret_val_of_call (calls !!! e2)))).
           { rewrite /offset_rets.
             rewrite (lookup_app_r ts'); last lia.
             replace (length ts' + length np + length npop2_calls + length npop1 + k2 - length ts')
               with (length np + length npop2_calls + length npop1 + k2) by lia.
             rewrite (lookup_app_r np); last lia.
             replace (length np + length npop2_calls + length npop1 + k2 - length np)
               with (length npop2_calls + length npop1 + k2) by lia.
             rewrite (lookup_app_r npop2_calls); last lia.
             replace (length npop2_calls + length npop1 + k2 - length npop2_calls)
               with (length npop1 + k2) by lia.
             rewrite (lookup_app_r npop1); last lia.
             replace (length npop1 + k2 - length npop1) with k2 by lia.
             rewrite /npop2_rets /bag.close.close_trace_add_pop_rets list_lookup_fmap.
             rewrite Hk2'_nm2 //. }
           (* d1, d2 are fresh tags > max_tag. *)
           assert (Hd1_fresh : (bag.close.max_tag ts.*1 < d1)%positive).
           { pose proof (bag.close.close_trace_add_match_tags_fresh _ _ _ _
               (list_elem_of_lookup_2 _ _ _ Hk1'_nm2)). lia. }
           assert (Hd2_fresh : (bag.close.max_tag ts.*1 < d2)%positive).
           { pose proof (bag.close.close_trace_add_match_tags_fresh _ _ _ _
               (list_elem_of_lookup_2 _ _ _ Hk2'_nm2)). lia. }
           (* Hpre_close_d says ret(d2) < call(d1).
              Since d1, d2 fresh, their Call/Ret are in npop2_calls/npop2_rets.
              We have d1's Call at offset_calls + k1 and d2's Ret at offset_rets + k2.
              By uniqueness (call_of_tag finds first Call), these are THE positions
              of d1's first Call and d2's first Ret in close_trace. *)
           rewrite /pre_of_trace in Hpre_close_d.
           destruct (ret_of_tag (ts' ++ np ++ npop2_calls ++ npop1 ++ npop2_rets) d2)
             as [[i_d2_ret [τ_d2r ev_d2r]]|] eqn:Hd2_ret_q; last done.
           destruct (call_of_tag (ts' ++ np ++ npop2_calls ++ npop1 ++ npop2_rets) d1)
             as [[i_d1_call [τ_d1c ev_d1c]]|] eqn:Hd1_call_q; last done.
           simpl in Hpre_close_d.
           apply list_find_Some in Hd2_ret_q as (Hlk_d2r & [Hτ_d2r Hev_d2r] & Hbef_d2r).
           apply list_find_Some in Hd1_call_q as (Hlk_d1c & [Hτ_d1c Hev_d1c] & Hbef_d1c).
           simpl in Hτ_d2r, Hτ_d1c. subst τ_d2r τ_d1c.
           (* call_of_tag is FIRST Call; we have Call at offset_calls + k1. So i_d1_call ≤ offset_calls + k1. *)
           assert (Hd1_le : i_d1_call ≤ offset_calls + k1).
           { destruct (decide (i_d1_call ≤ offset_calls + k1)) as [|Hgt]; first done.
             exfalso. apply (Hbef_d1c (offset_calls + k1) _ Hd1_call_close); first lia.
             simpl. by split. }
           (* ret_of_tag is FIRST Ret; we have Ret at offset_rets + k2. *)
           assert (Hd2_le : i_d2_ret ≤ offset_rets + k2).
           { destruct (decide (i_d2_ret ≤ offset_rets + k2)) as [|Hgt]; first done.
             exfalso. apply (Hbef_d2r (offset_rets + k2) _ Hd2_ret_close); first lia.
             simpl. split; done. }
           (* But Hpre_close_d says i_d2_ret < i_d1_call. With i_d1_call ≤ offset_calls + k1
              and i_d2_ret needs to be < i_d1_call ≤ offset_calls + k1.
              But i_d2_ret is the position of a Ret of d2 (fresh), which can only appear in
              npop2_rets (positions ≥ offset_rets). So i_d2_ret ≥ offset_rets =
              length ts' + length np + length npop2_calls + length npop1.
              Combined: offset_rets ≤ i_d2_ret < i_d1_call ≤ offset_calls + k1 < offset_rets. Contradiction. *)
           assert (Hd2_ge : i_d2_ret ≥ offset_rets).
           { (* d2 is fresh, so its event at i_d2_ret can only be in npop2_calls or npop2_rets.
                But it's a Ret, and npop2_calls only has Call events. So in npop2_rets. *)
             rewrite lookup_app_Some in Hlk_d2r.
             destruct Hlk_d2r as [Hin_ts'|[Hge_ts' Hlk]].
             { exfalso. apply list_elem_of_lookup_2 in Hin_ts'.
               rewrite /ts' in Hin_ts'.
               apply list_elem_of_filter in Hin_ts' as [_ Hin_ts].
               apply bag.close.tag_in_ts_le_max_tag in Hin_ts. lia. }
             rewrite lookup_app_Some in Hlk.
             destruct Hlk as [Hin_np|[Hge_np Hlk]].
             { exfalso. apply list_elem_of_lookup_2 in Hin_np.
               rewrite /np /bag.close.complete_trace_add_push in Hin_np.
               apply list_elem_of_fmap_1 in Hin_np as (τ' & Heq & Hin_up).
               injection Heq as -> _.
               assert (Hup_eq : up = (bag.close.unpaired_operations ts m).1.1)
                 by (rewrite Hops; done).
               rewrite Hup_eq /bag.close.unpaired_operations /= in Hin_up.
               apply list_elem_of_difference in Hin_up as [Hin_call _].
               apply list_elem_of_fmap_1 in Hin_call as ([τ_a x_a] & -> & Hin_filt). simpl in *.
               apply list_elem_of_filter in Hin_filt as [_ Hin_ts].
               apply bag.close.tag_in_ts_le_max_tag in Hin_ts. lia. }
             rewrite lookup_app_Some in Hlk.
             destruct Hlk as [Hin_calls|[Hge_calls Hlk]].
             { exfalso.
               rewrite /npop2_calls /bag.close.close_trace_add_pop_calls list_lookup_fmap in Hin_calls.
               apply fmap_Some in Hin_calls as ([τ1' τ2'] & _ & Heq).
               injection Heq as _ Habs. by destruct ev_d2r. }
             rewrite lookup_app_Some in Hlk.
             destruct Hlk as [Hin_npop1|[Hge_npop1 _]].
             { exfalso. apply list_elem_of_lookup_2 in Hin_npop1.
               rewrite /npop1 in Hin_npop1.
               apply bag.close.complete_trace_remove_pop_elem in Hin_npop1
                 as [_ Hin_upop].
               rewrite Hupop_is /bag.close.unpaired_operations /= in Hin_upop.
               apply list_elem_of_difference in Hin_upop as [Hin_call _].
               apply list_elem_of_fmap_1 in Hin_call as ([τ_a x_a] & -> & Hin_filt). simpl in *.
               apply list_elem_of_filter in Hin_filt as [_ Hin_ts].
               apply bag.close.tag_in_ts_le_max_tag in Hin_ts. lia. }
             rewrite /offset_rets. lia. }
           assert (Hk1_lt : k1 < length npop2_calls) by (rewrite Hlen_calls; lia).
           rewrite /offset_calls /offset_rets in Hd1_le Hd2_ge.
           lia.
Qed.

Lemma close_preserves_order_correct_unmatched ts m :
  I_queue_pre ts m →
  order_correct_unmatched (close_trace ts m).1 (close_trace ts m).2.
Proof.
  intros HIQ e1 e2 Hpre He1_push He2_in_m'.
  by apply close_trace_push_sub.
Qed.
(* End LLM-generated code. *)
(**********************************************************)

Lemma close_preserves_I_queue_pre rme valid_value ts m :
  per_tag_wellformed_bag rme valid_value ts →
  I_queue_pre ts m →
  I_queue_pre (close_trace ts m).1 (close_trace ts m).2.
Proof.
  intros ? IH.
  split_and!.
  - destruct IH.
    by apply (close_preserves_validity rme valid_value).
  - destruct IH as (?&?&_).
    by apply (close_preserves_pop_empty_sound rme valid_value).
  - by apply (close_preserves_order_correct_matched rme valid_value).
  - by apply close_preserves_order_correct_unmatched.
Qed.
