From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.bag Require Import close.
From iris_logatom.pure_logic.aspect.stack Require Import base vis.

(* Closing a trace (bag/close.v) completes pending pushes, drops unmatched pending pops,
   and adds pops for the remaining unmatched pushes. Every pop added to the match by the
   closing returns after all calls, so it is ordered after all pushes: the closing adds
   the edges (x, q) for every push x and every new pop q, and the premise is preserved. *)

(* The pops matched by the closing. *)
Definition close_new_pops ts m : list positive :=
  (drop (length m) (close_trace ts m).2).*2.

Definition close_ir ts m ir : list (positive * positive) :=
  ir ++ (close_new_pops ts m ≫= λ q, (λ x, (x, q)) <$> push_of_trace (close_trace ts m).1).

Lemma close_trace_match ts m :
  (close_trace ts m).2 = m ++ drop (length m) (close_trace ts m).2.
Proof.
  rewrite /close_trace.
  destruct (bag.close.unpaired_operations ts m) as [[up upop] ump].
  destruct (bag.close.complete_trace_add_match upop m ump) as [nm1 ump'].
  simpl. by rewrite drop_app_length.
Qed.

Local Lemma elem_of_close_ir ts m ir x q :
  (x, q) ∈ close_ir ts m ir ↔
  (x, q) ∈ ir ∨ (q ∈ close_new_pops ts m ∧ x ∈ push_of_trace (close_trace ts m).1).
Proof.
  rewrite /close_ir elem_of_app list_elem_of_bind. split.
  - intros [H|(q' & Hin & Hq')]; [by left|right].
    apply list_elem_of_fmap in Hin as (x' & Heq & Hx'). by simplify_eq.
  - intros [H|[Hq Hx]]; [by left|right].
    exists q. split; [apply list_elem_of_fmap; by exists x|done].
Qed.

(* A tag whose Ret only occurs in a suffix without calls precedes nothing. *)
Local Lemma no_pre_late_ret (P R : list (positive * trace)) q y :
  (∀ t, (q, t) ∈ P → ¬ is_ret t) →
  (∀ τ t, (τ, t) ∈ R → ¬ is_call t) →
  ¬ pre_of_trace (P ++ R) q y.
Proof.
  intros HP HR Hpre. rewrite /pre_of_trace in Hpre.
  destruct (ret_of_tag (P ++ R) q) as [[i x]|] eqn:Hr; simpl in Hpre; [|done].
  destruct (call_of_tag (P ++ R) y) as [[j z]|] eqn:Hc; simpl in Hpre; [|done].
  rewrite /ret_of_tag list_find_app_Some in Hr.
  destruct Hr as [Hr|(Hi & _ & _)].
  - apply list_find_Some in Hr as (Hlk & [Htag Hret] & _).
    destruct x as [τ t]. simpl in Htag, Hret. subst τ.
    exfalso. eapply HP; [by eapply list_elem_of_lookup_2|done].
  - rewrite /call_of_tag list_find_app_Some in Hc.
    destruct Hc as [Hc|(_ & _ & Hc)].
    + apply list_find_Some in Hc as (Hlk & _ & _). apply lookup_lt_Some in Hlk. lia.
    + apply list_find_Some in Hc as (Hlk & [_ Hcall] & _).
      destruct z as [τ t]. exfalso. eapply HR; [by eapply list_elem_of_lookup_2|done].
Qed.

Local Lemma call_not_in_suffix (P R : list (positive * trace)) y n v :
  (∀ τ t, (τ, t) ∈ R → ¬ is_call t) →
  (y, Call n v) ∈ P ++ R → (y, Call n v) ∈ P.
Proof.
  intros HR [Hin|Hin]%elem_of_app; first done.
  exfalso. by eapply HR.
Qed.

Local Lemma close_trace_structure rme valid_value ts m :
  per_tag_wellformed_bag rme valid_value ts → valid_match ts m →
  (∀ x, x ∈ push_of_trace (close_trace ts m).1 ↔ x ∈ push_of_trace ts) ∧
  (∀ q y, q ∈ close_new_pops ts m → ¬ pre_of_trace (close_trace ts m).1 q y) ∧
  (∀ a b, b ∉ close_new_pops ts m →
     pre_of_trace (close_trace ts m).1 a b → pre_of_trace ts a b).
Proof.
  intros Hwf Hvm.
  rewrite /close_new_pops /close_trace.
  destruct (bag.close.unpaired_operations ts m) as [[up upop] ump] eqn:Hop.
  destruct (bag.close.complete_trace_add_match upop m ump) as [nm1 ump'] eqn:Hmatch.
  set (calls := bag.close.extract_calls ts).
  set (np := bag.close.complete_trace_add_push up).
  set (npop1 := bag.close.complete_trace_remove_pop upop calls (m ++ nm1)).
  set (U := list_difference upop (m ++ nm1).*2).
  set (tsf := filter (λ x : positive * trace, x.1 ∉ U) ts).
  set (nm2 := bag.close.close_trace_add_match ump' (bag.close.max_tag ts.*1 + 1)).
  set (c2 := bag.close.close_trace_add_pop_calls nm2).
  set (r2 := bag.close.close_trace_add_pop_rets calls nm2).
  simpl. rewrite drop_app_length.
  assert (Hts' : tsf ++ np ++ c2 ++ npop1 ++ r2 = (tsf ++ np ++ c2) ++ (npop1 ++ r2))
    by by rewrite -!app_assoc.
  rewrite Hts'.
  assert (Hup : ∀ τ, τ ∈ up → τ ∈ push_of_trace ts).
  { intros τ Hτ. apply (bag.close.unpaired_push_is_push ts m). by rewrite Hop. }
  assert (Hupop : ∀ τ, τ ∈ upop → τ ∈ pop_of_trace ts).
  { intros τ Hτ. apply (bag.close.unpaired_pop_is_pop ts m). by rewrite Hop. }
  (* the suffix npop1 ++ r2 contains only returns *)
  assert (HR : ∀ τ t, (τ, t) ∈ npop1 ++ r2 → ¬ is_call t).
  { intros τ t [Hin|Hin]%elem_of_app.
    - apply bag.close.complete_trace_remove_pop_elem in Hin as [Hret _].
      destruct t; simpl in *; tauto.
    - rewrite /r2 /bag.close.close_trace_add_pop_rets in Hin.
      apply list_elem_of_fmap_1 in Hin as ([τ1 τ2] & Heq & _).
      simpl in Heq. simplify_eq. intros Hc. exact Hc. }
  assert (Hnp : ∀ τ t, (τ, t) ∈ np → t = Ret #() ∧ τ ∈ up).
  { intros τ t Hin. by apply bag.close.complete_trace_add_push_elem in Hin. }
  assert (Hc2 : ∀ τ t, (τ, t) ∈ c2 → t = Call Pop #() ∧ τ ∈ nm2.*2).
  { intros τ t Hin. rewrite /c2 /bag.close.close_trace_add_pop_calls in Hin.
    apply list_elem_of_fmap_1 in Hin as ([τ1 τ2] & Heq & Hin). simplify_eq.
    split; [done|]. by apply (list_elem_of_fmap_2 snd _ (τ1, τ2)). }
  assert (Htsf : ∀ τ t, (τ, t) ∈ tsf → τ ∉ U ∧ (τ, t) ∈ ts).
  { intros τ t Hin. by apply list_elem_of_filter in Hin. }
  (* the new pops are pops *)
  assert (HN : ∀ q, q ∈ (nm1 ++ nm2).*2 →
            (q ∈ upop ∧ q ∈ nm1.*2) ∨ (∃ τ1, (τ1, q) ∈ nm2)).
  { intros q. rewrite fmap_app elem_of_app. intros [Hq|Hq].
    - left. split; [|done].
      pose proof (bag.close.complete_trace_add_match_snd_sub upop m ump) as Hsub.
      rewrite Hmatch /= in Hsub. by apply Hsub.
    - right. apply list_elem_of_fmap_1 in Hq as ([τ1 τ2] & -> & Hin). by exists τ1. }
  split_and!.
  - (* pushes are preserved *)
    intros x. rewrite /push_of_trace. split.
    + intros ([τ t] & -> & Hin)%list_elem_of_fmap_1.
      apply list_elem_of_filter in Hin as [[w Hw] Hin]. simpl in Hw. subst t.
      apply call_not_in_suffix in Hin; last done.
      apply (list_elem_of_fmap_2 fst _ (τ, Call Push w)).
      apply list_elem_of_filter_2; [by exists w|].
      apply elem_of_app in Hin as [Hin|[Hin|Hin]%elem_of_app].
      * by apply Htsf in Hin as [_ Hin].
      * by apply Hnp in Hin as [? _].
      * apply Hc2 in Hin as [Heq _]. discriminate.
    + intros ([τ t] & -> & Hin)%list_elem_of_fmap_1.
      apply list_elem_of_filter in Hin as [[w Hw] Hin]. simpl in Hw. subst t.
      apply (list_elem_of_fmap_2 fst _ (τ, Call Push w)).
      apply list_elem_of_filter_2; [by exists w|].
      rewrite -app_assoc. apply elem_of_app. left.
      apply list_elem_of_filter_2; [|done]. simpl.
      intros [Hupop_τ _]%list_elem_of_difference.
      eapply (bag.close.push_tag_not_upop rme valid_value ts m τ Hwf); last by rewrite Hop.
      apply (list_elem_of_fmap_2 fst _ (τ, Call Push w)).
      apply list_elem_of_filter_2; [by exists w|done].
  - (* new pops precede nothing *)
    intros q y Hq. apply no_pre_late_ret; last done.
    intros t Hin Hret.
    apply elem_of_app in Hin as [Hin|[Hin|Hin]%elem_of_app].
    + apply Htsf in Hin as [_ Hin].
      destruct (HN q Hq) as [[Hq_upop _]|(τ1 & Hτ1)].
      * pose proof (Hupop q Hq_upop) as Hpop.
        assert (Hf : (q, t) ∈ filter (λ x : positive * trace, x.1 = q) ts)
          by (apply list_elem_of_filter; done).
        rewrite (bag.close.incomplete_pop_filter rme valid_value ts m q Hwf) in Hf.
        -- apply list_elem_of_singleton in Hf. simplify_eq. done.
        -- by apply pop_tag_in_trace.
        -- by rewrite Hop.
      * eapply (bag.close.npop2_tag_not_in_ts ts q (Call Pop #()) calls ump'); [|exact Hin].
        rewrite /bag.close.close_trace_add_pop /bag.close.close_trace_add_pop_calls elem_of_app.
        left. apply list_elem_of_fmap. by exists (τ1, q).
    + apply Hnp in Hin as [_ Hq_up].
      destruct (HN q Hq) as [[Hq_upop _]|(τ1 & Hτ1)].
      * apply (push_xor_pop_of_trace ts rme valid_value q Hwf); [by apply Hup|by apply Hupop].
      * eapply (bag.close.npop2_tag_not_in_up ts m q ump'); [by exists τ1|by rewrite Hop].
    + apply Hc2 in Hin as [-> _]. done.
  - (* pre between old tags is preserved *)
    intros a b Hb Hpre.
    destruct (pre_of_trace_call _ _ _ Hpre) as (n & v & Hcall).
    apply call_not_in_suffix in Hcall; last done.
    apply elem_of_app in Hcall as [Hcall|[Hcall|Hcall]%elem_of_app].
    + rewrite -!app_assoc in Hpre.
      apply (pre_of_trace_app_inv tsf) in Hpre; last by eauto.
      destruct (pre_of_trace_ret _ _ _ Hpre) as [r Hret].
      apply Htsf in Hret as [Ha _]. apply Htsf in Hcall as [Hb' _].
      by apply (bag.close.pre_of_trace_filter_iff U ts b a Hb' Ha).
    + by apply Hnp in Hcall as [? _].
    + apply Hc2 in Hcall as [_ Hcall]. exfalso. apply Hb.
      rewrite fmap_app elem_of_app. by right.
Qed.

(* A path in [R'] that ends outside the sinks [S] of [R'] is a path in [R]. *)
Local Lemma tc_avoid_sinks {A} (R R' : relation A) (S : A → Prop) :
  (∀ a b, R' a b → ¬ S b → R a b) →
  (∀ s b, S s → ¬ R' s b) →
  ∀ x y, tc R' x y → ¬ S y → tc R x y.
Proof.
  intros Hsub Hsink x y Hxy. induction Hxy as [x y Hxy|x z y Hxz Hzy IH]; intros Hy.
  - apply tc_once. by apply Hsub.
  - assert (Hz : ¬ S z).
    { intros Hz. destruct Hzy as [? ? H|? ? ? H _]; by eapply Hsink. }
    eapply tc_l; [by apply Hsub | by apply IH].
Qed.

Lemma close_preserves_I_stack_pre rme valid_value ts m ir :
  per_tag_wellformed_bag rme valid_value ts →
  I_stack_pre ts m ir →
  I_stack_pre (close_trace ts m).1 (close_trace ts m).2 (close_ir ts m ir).
Proof.
  intros Hwf (Hvm & Hps & Hirwf & Hacyc & Hlifo).
  set (ts' := (close_trace ts m).1).
  set (m' := (close_trace ts m).2).
  set (N := close_new_pops ts m).
  set (ir' := close_ir ts m ir).
  destruct (close_trace_structure rme valid_value ts m Hwf Hvm) as (Hpush & Hsink & Hpre).
  pose proof (close_preserves_validity rme valid_value ts m Hwf Hvm) as Hvm'.
  pose proof (close_preserves_wellformed rme valid_value ts m Hwf Hvm) as Hwf'.
  pose proof (close_closed rme valid_value ts m Hwf Hvm) as [Hclosed _].
  assert (Hm' : m' = m ++ drop (length m) m') by apply close_trace_match.
  assert (Hm'2 : ∀ q, q ∈ m'.*2 ↔ q ∈ m.*2 ∨ q ∈ N).
  { intros q. rewrite {1}Hm' fmap_app elem_of_app. done. }
  assert (HN_m : ∀ q, q ∈ N → q ∉ m.*2).
  { destruct Hvm' as (_ & [_ Hnd] & _). fold m' in Hnd. rewrite Hm' fmap_app in Hnd.
    intros q HqN Hqm. apply NoDup_app in Hnd as (_ & Hdisj & _). by apply (Hdisj q Hqm). }
  assert (Hm'2_npush : ∀ q, q ∈ m'.*2 → q ∉ push_of_trace ts').
  { intros q ([x y] & Heq & Hin)%list_elem_of_fmap_1 Hq. simpl in Heq. subst y.
    eapply (push_xor_pop_of_trace ts' rme valid_value q Hwf' Hq).
    apply (list_elem_of_fmap_2 fst _ (q, Call Pop #())).
    apply list_elem_of_filter_2; [done|exact (valid_match_call_pop _ _ _ _ Hvm' Hin)]. }
  assert (HN_npush : ∀ q, q ∈ N → q ∉ push_of_trace ts').
  { intros q Hq. apply Hm'2_npush, Hm'2. by right. }
  assert (Hir'_N : ∀ x q, q ∈ N → x ∈ push_of_trace ts' → (x, q) ∈ ir').
  { intros x q Hq Hx. apply elem_of_close_ir. by right. }
  assert (Hir'_old : ∀ x y, y ∉ N → (x, y) ∈ ir' → (x, y) ∈ ir).
  { intros x y Hy [Hin|[Hin _]]%elem_of_close_ir; [done|by destruct Hy]. }
  assert (Hir_ir' : ∀ x y, (x, y) ∈ ir → (x, y) ∈ ir').
  { intros x y Hin. apply elem_of_close_ir. by left. }
  (* the new pops are sinks *)
  assert (Hsink_rel : ∀ q y, q ∈ N → ¬ stk_rel ts' m' ir' q y).
  { intros q y Hq [Hp|[Hin|(_ & Hy & Hn)]].
    - by eapply Hsink.
    - apply elem_of_close_ir in Hin as [Hin|[_ Hqp]]; [|by eapply HN_npush].
      apply (HN_npush q Hq), Hpush. by destruct (Hirwf q y Hin).
    - by apply Hn, Hir'_N. }
  (* edges into old tags are old edges *)
  assert (Hrel_old : ∀ a b, b ∉ N → ir_rel ts' m' ir' a b → ir_rel ts m ir a b).
  { intros a b Hb [Hin|(Ha & Hbp & Hn)]; [left; by apply Hir'_old|right].
    apply Hm'2 in Ha as [Ha|Ha]; last by destruct Hn; apply Hir'_N.
    split_and!; [done|by apply Hpush|]. intros Hin. by apply Hn, Hir_ir'. }
  assert (Hstk_old : ∀ a b, stk_rel ts' m' ir' a b → b ∉ N → stk_rel ts m ir a b).
  { intros a b [Hp|Hr] Hb; [left; by apply Hpre|right; by apply Hrel_old]. }
  split_and!.
  - exact Hvm'.
  - exact (close_preserves_pop_empty_sound rme valid_value ts m Hwf Hps Hvm).
  - intros x y [Hin|[Hy Hx]]%elem_of_close_ir.
    + destruct (Hirwf x y Hin). split; [by apply Hpush|apply Hm'2; by left].
    + split; [done|apply Hm'2; by right].
  - intros x Hx.
    destruct (decide (x ∈ N)) as [HxN|HxN].
    + inversion Hx as [? ? H|? ? ? H _]; by eapply Hsink_rel.
    + eapply (Hacyc x), (tc_avoid_sinks _ _ (λ q, q ∈ N)); [done|done|exact Hx|done].
  - intros a pa c Ham' Hpre_apa (Ha & Hc & Hor) Hir.
    assert (Hpa : pa ∈ m'.*2) by (by apply (list_elem_of_fmap_2 snd _ (a, pa))).
    apply Hm'2 in Hpa as [Hpa|HpaN].
    + (* an old pair *)
      assert (HpaN : pa ∉ N) by (intros HpaN; by apply (HN_m pa HpaN)).
      assert (Ham : (a, pa) ∈ m).
      { rewrite Hm' in Ham'. apply elem_of_app in Ham' as [?|Hin]; [done|].
        exfalso. apply HpaN. by apply (list_elem_of_fmap_2 snd _ (a, pa)). }
      apply Hpre in Hpre_apa; last done.
      apply Hir'_old in Hir; last done.
      assert (HcN : c ∉ N) by (intros HcN; by apply (HN_npush c HcN)).
      assert (Hins : ins_tr ts m ir a c).
      { split_and!; [by apply Hpush|by apply Hpush|].
        destruct Hor as [Hp|(q & Hp & Hq)]; [left; by apply Hpre|right].
        assert (HqN : q ∉ N) by (intros HqN; by eapply (Hsink_rel q c HqN); right).
        exists q. split; [by apply Hpre|by apply Hrel_old]. }
      destruct (Hlifo a pa c Ham Hpre_apa Hins Hir) as (pc & Hpc & Hn).
      exists pc. split; [rewrite Hm'; by apply elem_of_app; left|].
      assert (HpcN : pc ∉ N).
      { intros HpcN. apply (HN_m pc HpcN). by apply (list_elem_of_fmap_2 snd _ (c, pc)). }
      intros [Hp|(e & H1 & H2)]; apply Hn; [left; by apply Hpre|right].
      assert (He : e ∈ push_of_trace ts').
      { destruct H1 as [Hin|(_ & He & _)]; [|done].
        apply elem_of_close_ir in Hin as [Hin|[_ Hpap]].
        - exfalso. apply (Hm'2_npush pa); [apply Hm'2; by left|].
          apply Hpush. by destruct (Hirwf pa e Hin).
        - exfalso. apply (Hm'2_npush pa); [apply Hm'2; by left|done]. }
      assert (HeN : e ∉ N) by (intros HeN; by apply (HN_npush e HeN)).
      exists e. split; by apply Hrel_old.
    + (* a pair added by the closing *)
      pose proof (Hclosed c Hc) as Hcm.
      apply list_elem_of_fmap_1 in Hcm as ([c' pc] & Heq & Hpc).
      simpl in Heq. subst c'.
      exists pc. split; [done|].
      intros [Hp|(e & H1 & _)]; [by eapply Hsink|].
      by apply (Hsink_rel pa e HpaN); right.
Qed.

(* ====================================================================== *)
(* Closing for the vis/rr premise (stack/vis.v).                          *)
(* ====================================================================== *)

(* The closed history ranks its operations by points: the old points of pushes and
   matched pops, then fresh points for the pushes without one, then the pops added by the
   closing (which return after all calls). The remove order puts the added pops after the
   old ones, in reverse point order of their pushes. *)

Local Definition idx (l : list positive) (τ : positive) : nat :=
  default 0 (fst <$> list_find (λ x, x = τ) l).

Local Lemma idx_lookup l τ : τ ∈ l → l !! idx l τ = Some τ.
Proof.
  intros Hin. destruct (list_find_elem_of (λ x, x = τ) l τ Hin eq_refl) as [[i x] Hf].
  rewrite /idx Hf /=. by apply list_find_Some in Hf as (Hi & -> & _).
Qed.

Local Lemma idx_of_lookup l i τ : NoDup l → l !! i = Some τ → idx l τ = i.
Proof.
  intros Hnd Hi. pose proof (idx_lookup l τ (list_elem_of_lookup_2 _ _ _ Hi)) as Hj.
  by eapply NoDup_lookup.
Qed.

Local Lemma idx_lt l τ : τ ∈ l → idx l τ < length l.
Proof. intros Hin. eapply lookup_lt_Some, idx_lookup, Hin. Qed.

Local Lemma idx_inj l a b : a ∈ l → b ∈ l → idx l a = idx l b → a = b.
Proof.
  intros Ha Hb Heq. pose proof (idx_lookup l a Ha) as Ha'. pose proof (idx_lookup l b Hb) as Hb'.
  rewrite Heq Hb' in Ha'. by injection Ha'.
Qed.

(* pushes without a point *)
Local Definition close_unpointed ts pts : list positive :=
  list_difference (remove_dups (push_of_trace ts)) pts.

Definition close_rank ts m pts (τ : positive) : nat :=
  if decide (τ ∈ close_new_pops ts m) then
    length pts + length (close_unpointed ts pts) + idx (close_new_pops ts m) τ
  else if decide (τ ∈ pts) then idx pts τ
  else length pts + idx (close_unpointed ts pts) τ.

Local Definition push_of_pop (M : list (positive * positive)) (q : positive) : positive :=
  default q (fst <$> (snd <$> list_find (λ e, e.2 = q) M)).

Local Lemma push_of_pop_spec M x q : NoDup M.*2 → (x, q) ∈ M → push_of_pop M q = x.
Proof.
  intros Hnd Hin. apply list_elem_of_lookup in Hin as [k Hk].
  destruct (list_find_elem_of (λ e : positive * positive, e.2 = q) M (x, q)) as [[i [y q']] Hf];
    [by eapply list_elem_of_lookup_2|done|].
  rewrite /push_of_pop Hf /=. apply list_find_Some in Hf as (Hi & Hq' & _). simpl in Hq'. subst q'.
  assert (i = k) as ->.
  { eapply (NoDup_lookup M.*2); [done| |]; rewrite list_lookup_fmap; [rewrite Hi|rewrite Hk]; done. }
  rewrite Hk in Hi. by injection Hi.
Qed.

Definition close_rr_rank ts m pts (τ : positive) : nat :=
  if decide (τ ∈ close_new_pops ts m) then
    length m + (length pts + length (close_unpointed ts pts) -
      close_rank ts m pts (push_of_pop (drop (length m) (close_trace ts m).2) τ))
  else idx m.*2 τ.

Lemma close_preserves_I_stack_vis_pre rme valid_value ts m pts :
  per_tag_wellformed_bag rme valid_value ts →
  I_stack_vis_pre ts m pts →
  closed_vis (close_trace ts m).1 (close_trace ts m).2 (close_rank ts m pts) (close_rr_rank ts m pts).
Proof.
  intros Hwf HI.
  pose proof (isv_valid _ _ _ HI) as Hvm.
  set (ts' := (close_trace ts m).1).
  set (m' := (close_trace ts m).2).
  set (N := close_new_pops ts m).
  set (M := drop (length m) m').
  set (U := close_unpointed ts pts).
  set (K := length pts + length U).
  set (f := close_rank ts m pts).
  set (r := close_rr_rank ts m pts).
  destruct (close_trace_structure rme valid_value ts m Hwf Hvm) as (Hpush & Hsink & Hpre).
  pose proof (close_preserves_validity rme valid_value ts m Hwf Hvm) as Hvm'.
  pose proof (close_preserves_wellformed rme valid_value ts m Hwf Hvm) as Hwf'.
  pose proof (close_closed rme valid_value ts m Hwf Hvm) as [Hclosed _].
  assert (Hm' : m' = m ++ M) by apply close_trace_match.
  assert (HNM : N = M.*2) by done.
  assert (Hm'2 : ∀ q, q ∈ m'.*2 ↔ q ∈ m.*2 ∨ q ∈ N).
  { intros q. rewrite {1}Hm' fmap_app elem_of_app. done. }
  assert (Hnd' : NoDup m.*2 ∧ NoDup N ∧ ∀ q, q ∈ m.*2 → q ∉ N).
  { destruct Hvm' as (_ & [_ Hnd] & _). fold m' in Hnd. rewrite Hm' fmap_app in Hnd.
    apply NoDup_app in Hnd as (? & Hdisj & ?). split_and!; [done|by rewrite HNM|].
    intros q Hq HqN. apply (Hdisj q Hq). by rewrite -HNM. }
  destruct Hnd' as (Hm2nd & HNnd & HN_m).
  assert (Hm'2_npush : ∀ q, q ∈ m'.*2 → q ∉ push_of_trace ts').
  { intros q ([x y] & Heq & Hin)%list_elem_of_fmap_1 Hq. simpl in Heq. subst y.
    eapply (push_xor_pop_of_trace ts' rme valid_value q Hwf' Hq).
    apply (list_elem_of_fmap_2 fst _ (q, Call Pop #())).
    apply list_elem_of_filter_2; [done|exact (valid_match_call_pop _ _ _ _ Hvm' Hin)]. }
  assert (Hm2_pts : ∀ q, q ∈ m.*2 → q ∈ pts) by apply (isv_pop_pt _ _ _ HI).
  assert (HU : ∀ x, x ∈ U ↔ x ∈ push_of_trace ts ∧ x ∉ pts).
  { intros x. by rewrite list_elem_of_difference elem_of_remove_dups. }
  (* the three regions of the rank *)
  assert (FN : ∀ τ, τ ∈ N → f τ = K + idx N τ).
  { intros τ Hτ. rewrite /f /close_rank decide_True //. }
  assert (Fpts : ∀ τ, τ ∉ N → τ ∈ pts → f τ = idx pts τ).
  { intros τ Hτ Hτ'. rewrite /f /close_rank decide_False // decide_True //. }
  assert (FU : ∀ τ, τ ∉ N → τ ∉ pts → f τ = length pts + idx U τ).
  { intros τ Hτ Hτ'. rewrite /f /close_rank decide_False // decide_False //. }
  assert (Hpush_N : ∀ x, x ∈ push_of_trace ts' → x ∉ N).
  { intros x Hx HxN. apply (Hm'2_npush x); [apply Hm'2; by right|done]. }
  (* pushes and old pops are ranked below K *)
  assert (Fop : ∀ τ, vis_op ts' m' τ → τ ∉ N → f τ < K ∧ (τ ∈ pts → f τ = idx pts τ) ∧
            (τ ∉ pts → length pts ≤ f τ)).
  { intros τ [Hτ|Hτ] HτN.
    - destruct (decide (τ ∈ pts)) as [Hin|Hnin].
      + rewrite Fpts //. pose proof (idx_lt _ _ Hin). split_and!; [lia|done|done].
      + rewrite FU //. assert (HτU : τ ∈ U) by (apply HU; split; [by apply Hpush|done]).
        pose proof (idx_lt _ _ HτU). split_and!; [lia|done|lia].
    - apply Hm'2 in Hτ as [Hτ|?]; last done.
      pose proof (Hm2_pts τ Hτ) as Hin. rewrite Fpts //.
      pose proof (idx_lt _ _ Hin). split_and!; [lia|done|done]. }
  assert (FNK : ∀ τ, τ ∈ N → K ≤ f τ) by (intros τ Hτ; rewrite FN //; lia).
  assert (Hret_pts : ∀ a b, pre_of_trace ts a b → vis_op ts' m' a → a ∉ N → a ∈ pts).
  { intros a b Hab [Ha|Ha] HaN.
    - destruct (pre_of_trace_ret _ _ _ Hab) as [ret Hret].
      apply (isv_push_ret _ _ _ HI); [by apply Hpush|].
      apply (list_elem_of_fmap_2 fst _ (a, Ret ret)). by apply list_elem_of_filter_2.
    - apply Hm2_pts. by apply Hm'2 in Ha as [?|?]. }
  assert (Hidx_pre : ∀ a b, pt_before pts a b → idx pts a < idx pts b).
  { intros a b (i & j & Hij & Hi & Hj).
    rewrite (idx_of_lookup _ _ _ (isv_nodup _ _ _ HI) Hi) (idx_of_lookup _ _ _ (isv_nodup _ _ _ HI) Hj).
    done. }
  assert (Hcv_pre : ∀ a b, pre_of_trace ts' a b → vis_op ts' m' a → vis_op ts' m' b → f a < f b).
  { intros a b Hab Ha Hb.
    assert (HaN : a ∉ N) by (intros HaN; by eapply Hsink).
    destruct (Fop a Ha HaN) as (HaK & Ha_pts & _).
    destruct (decide (b ∈ N)) as [HbN|HbN]; first (pose proof (FNK b HbN); lia).
    apply Hpre in Hab; last done.
    pose proof (Hret_pts a b Hab Ha HaN) as Hapts.
    destruct (Fop b Hb HbN) as (_ & Hb_pts & Hb_npts).
    destruct (decide (b ∈ pts)) as [Hbpts|Hbpts].
    - rewrite Ha_pts // Hb_pts //. by apply Hidx_pre, (isv_pre _ _ _ HI).
    - pose proof (Hb_npts Hbpts). pose proof (idx_lt _ _ Hapts). rewrite Ha_pts //. lia. }
  assert (Hvis_rk : ∀ x y, vis_rk ts' m' f x y → vis_op ts' m' x ∧ vis_op ts' m' y ∧ f x < f y).
  { intros x y [(Hx & Hy & Hxy)|(Hx & Hy & Hxy)]; split_and!; try done; by [left|right]. }
  assert (Hts_rk : ∀ a b, a ∈ push_of_trace ts' → b ∈ push_of_trace ts' →
            ts_rk ts' m' f a b → f a < f b).
  { intros a b Ha Hb [Hab|[(c & Hac & Hcb)|(d & c & Had & Hdc & Hcb)]].
    - apply Hcv_pre; [done|by left|by left].
    - destruct (Hvis_rk c b Hcb) as (Hc & _ & Hcb'). pose proof (Hcv_pre a c Hac (or_introl Ha) Hc). lia.
    - destruct (Hvis_rk c b Hcb) as (Hc & _ & Hcb'). destruct (Hvis_rk d c Hdc) as (Hd & _ & Hdc').
      pose proof (Hcv_pre a d Had (or_introl Ha) Hd). lia. }
  (* the remove order *)
  assert (RN : ∀ x q, (x, q) ∈ M → r q = length m + (K - f x)).
  { intros x q Hin.
    assert (HqN : q ∈ N) by (rewrite HNM; by apply (list_elem_of_fmap_2 snd _ (x, q))).
    rewrite /r /close_rr_rank decide_True //. fold M f. by rewrite (push_of_pop_spec M x q). }
  assert (Rold : ∀ q, q ∉ N → r q = idx m.*2 q).
  { intros q HqN. rewrite /r /close_rr_rank decide_False //. }
  assert (HM_push : ∀ x q, (x, q) ∈ M → x ∈ push_of_trace ts').
  { intros x q Hin. assert (Hin' : (x, q) ∈ m') by (rewrite Hm'; apply elem_of_app; by right).
    destruct (valid_match_call_push _ _ _ _ Hvm' Hin') as [w Hw].
    apply (list_elem_of_fmap_2 fst _ (x, Call Push w)). apply list_elem_of_filter_2; [by exists w|done]. }
  assert (HN_pair : ∀ q, q ∈ N → ∃ x, (x, q) ∈ M).
  { intros q Hq. rewrite HNM in Hq. apply list_elem_of_fmap_1 in Hq as ([x q'] & -> & Hin). by exists x. }
  assert (Hm_idx : ∀ j a q, m !! j = Some (a, q) → idx m.*2 q = j).
  { intros j a q Hj. apply (idx_of_lookup _ _ _ Hm2nd). by rewrite list_lookup_fmap Hj. }
  assert (Hm2_lookup : ∀ q, q ∈ m.*2 → ∃ a, m !! idx m.*2 q = Some (a, q)).
  { intros q Hq. pose proof (idx_lookup _ _ Hq) as Hl. rewrite list_lookup_fmap in Hl.
    destruct (m !! idx m.*2 q) as [[a q']|] eqn:Hlk; simpl in Hl; simplify_eq. by exists a. }
  assert (Hold_lt : ∀ q, q ∈ m.*2 → idx m.*2 q < length m).
  { intros q Hq. rewrite -(length_fmap snd m). by apply idx_lt. }
  assert (Hinj : ∀ a b, vis_op ts' m' a → vis_op ts' m' b → a ≠ b → f a ≠ f b).
  { intros a b Ha Hb Hne Heq.
    destruct (decide (a ∈ N)) as [HaN|HaN], (decide (b ∈ N)) as [HbN|HbN].
    - apply Hne, (idx_inj N); [done|done|]. rewrite FN // FN // in Heq. lia.
    - pose proof (FNK a HaN). destruct (Fop b Hb HbN). lia.
    - pose proof (FNK b HbN). destruct (Fop a Ha HaN). lia.
    - destruct (Fop a Ha HaN) as (_ & Hapts & Hanpts), (Fop b Hb HbN) as (_ & Hbpts & Hbnpts).
      assert (Hpush_U : ∀ x, vis_op ts' m' x → x ∉ N → x ∉ pts → x ∈ U).
      { intros x [Hx|Hx] HxN Hxpts; apply HU; split; try done; first by apply Hpush.
        apply Hm'2 in Hx as [Hx|?]; [by destruct Hxpts; apply Hm2_pts|done]. }
      destruct (decide (a ∈ pts)) as [Ha'|Ha'], (decide (b ∈ pts)) as [Hb'|Hb'].
      + apply Hne, (idx_inj pts); [done|done|]. by rewrite -Hapts // -Hbpts.
      + pose proof (Hbnpts Hb'). pose proof (idx_lt _ _ Ha'). rewrite Hapts // in Heq. lia.
      + pose proof (Hanpts Ha'). pose proof (idx_lt _ _ Hb'). rewrite Hbpts // in Heq. lia.
      + rewrite FU // FU // in Heq. apply Hne, (idx_inj U); [by apply Hpush_U|by apply Hpush_U|lia]. }
  (* points of old operations: rank order is point order *)
  assert (Hpt_of_f : ∀ x y, x ∈ pts → y ∈ pts → x ∉ N → y ∉ N → f x < f y →
            pt_before pts x y).
  { intros x y Hx Hy HxN HyN Hxy. rewrite Fpts // Fpts // in Hxy.
    exists (idx pts x), (idx pts y). split_and!; [done|by apply idx_lookup|by apply idx_lookup]. }
  assert (Hpop_old : ∀ c y, vis_rk ts' m' f c y → y ∈ push_of_trace ts' → f y < length pts →
            c ∈ m.*2 ∧ c ∉ N ∧ f c < f y).
  { intros c y [(_ & Hy & _)|(Hc & _ & Hcy)] Hy' Hfy; first by destruct (Hm'2_npush y Hy).
    assert (HcN : c ∉ N) by (intros HcN; pose proof (FNK c HcN); lia).
    apply Hm'2 in Hc as [Hc|?]; [done|done]. }
  assert (Hpush_old : ∀ d c, vis_rk ts' m' f d c → c ∈ m'.*2 → f c < length pts →
            d ∈ push_of_trace ts' ∧ d ∉ N ∧ d ∈ pts ∧ f d < f c).
  { intros d c [(Hd & _ & Hdc)|(_ & Hc & _)] Hc' Hfc; last by destruct (Hm'2_npush c Hc').
    pose proof (Hpush_N d Hd) as HdN. split_and!; [done|done| |done].
    destruct (decide (d ∈ pts)) as [|Hn]; [done|]. destruct (Fop d (or_introl Hd) HdN) as (_ & _ & Hle).
    pose proof (Hle Hn). lia. }
  assert (Hpop_tr : ∀ c, c ∈ m.*2 → c ∈ pop_of_trace ts).
  { intros c ([x y] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst y.
    apply (list_elem_of_fmap_2 fst _ (c, Call Pop #())).
    apply list_elem_of_filter_2; [done|exact (valid_match_call_pop _ _ _ _ Hvm Hin)]. }
  assert (HM_old : ∀ x q, (x, q) ∈ m' → q ∉ N → (x, q) ∈ m).
  { intros x q Hin HqN. rewrite Hm' in Hin. apply elem_of_app in Hin as [?|Hin]; [done|].
    exfalso. apply HqN. rewrite HNM. by apply (list_elem_of_fmap_2 snd _ (x, q)). }
  assert (HM_new : ∀ x q, (x, q) ∈ m' → q ∈ N → (x, q) ∈ M).
  { intros x q Hin HqN. rewrite Hm' in Hin. apply elem_of_app in Hin as [Hin|?]; [|done].
    exfalso. apply (HN_m q); [by apply (list_elem_of_fmap_2 snd _ (x, q))|done]. }
  constructor.
  - exact Hinj.
  - exact Hcv_pre.
  - (* the remove order is injective *)
    intros p q Hp Hq Hne Heq.
    destruct (decide (p ∈ N)) as [HpN|HpN], (decide (q ∈ N)) as [HqN|HqN].
    + destruct (HN_pair p HpN) as [x Hx], (HN_pair q HqN) as [y Hy].
      rewrite (RN x p Hx) (RN y q Hy) in Heq.
      assert (Hxy : x ≠ y).
      { intros ->. apply Hne. eapply (valid_match_inj_ret ts' m' y); [done|..];
          rewrite Hm'; apply elem_of_app; by right. }
      pose proof (HM_push x p Hx) as Hxp. pose proof (HM_push y q Hy) as Hyp.
      destruct (Fop x (or_introl Hxp) (Hpush_N x Hxp)) as [HxK _].
      destruct (Fop y (or_introl Hyp) (Hpush_N y Hyp)) as [HyK _].
      apply (Hinj x y (or_introl Hxp) (or_introl Hyp) Hxy). lia.
    + apply Hm'2 in Hq as [Hq|?]; last done.
      destruct (HN_pair p HpN) as [x Hx]. rewrite (RN x p Hx) (Rold q HqN) in Heq.
      pose proof (Hold_lt q Hq). lia.
    + apply Hm'2 in Hp as [Hp|?]; last done.
      destruct (HN_pair q HqN) as [y Hy]. rewrite (RN y q Hy) (Rold p HpN) in Heq.
      pose proof (Hold_lt p Hp). lia.
    + apply Hm'2 in Hp as [Hp|?], Hq as [Hq|?]; try done.
      rewrite (Rold p HpN) (Rold q HqN) in Heq. by apply Hne, (idx_inj m.*2).
  - (* the remove order extends precedence *)
    intros p q Hp Hq Hpq.
    assert (HpN : p ∉ N) by (intros HpN; by eapply Hsink).
    apply Hm'2 in Hp as [Hp|?]; last done.
    rewrite (Rold p HpN).
    destruct (decide (q ∈ N)) as [HqN|HqN].
    + destruct (HN_pair q HqN) as [x Hx]. rewrite (RN x q Hx). pose proof (Hold_lt p Hp). lia.
    + apply Hm'2 in Hq as [Hq|?]; last done. rewrite (Rold q HqN).
      apply Hpre in Hpq; last done.
      destruct (Hm2_lookup p Hp) as [b Hb], (Hm2_lookup q Hq) as [a Ha].
      exact (isv_rr _ _ _ HI _ _ _ _ _ _ Hb Ha Hpq).
  - (* condition 2 of Lemma 3 *)
    intros a pa b Hapa Hpre_apa Hts Hb Hbpa.
    assert (Ha : a ∈ push_of_trace ts').
    { destruct (valid_match_call_push _ _ _ _ Hvm' Hapa) as [w Hw].
      apply (list_elem_of_fmap_2 fst _ (a, Call Push w)). apply list_elem_of_filter_2; [by exists w|done]. }
    pose proof (Hclosed b Hb) as Hbm.
    apply list_elem_of_fmap_1 in Hbm as ([b' pb] & Heq & Hbpb). simpl in Heq. subst b'.
    destruct (decide (pa ∈ N)) as [HpaN|HpaN].
    + (* a pair added by the closing: its push is ts-before b *)
      exists pb. split; [done|]. rewrite (RN a pa (HM_new a pa Hapa HpaN)).
      pose proof (Hts_rk a b Ha Hb Hts) as Hab.
      destruct (Fop b (or_introl Hb) (Hpush_N b Hb)) as [HbK _].
      destruct (decide (pb ∈ N)) as [HpbN|HpbN].
      * rewrite (RN b pb (HM_new b pb Hbpb HpbN)). lia.
      * rewrite (Rold pb HpbN).
        assert (Hpb : pb ∈ m.*2) by (by apply (list_elem_of_fmap_2 snd _ (b, pb)), HM_old).
        pose proof (Hold_lt pb Hpb). lia.
    + (* an old pair: the instance is one that the commit of pa has checked *)
      pose proof (HM_old a pa Hapa HpaN) as Ham.
      assert (Hpa : pa ∈ m.*2) by (by apply (list_elem_of_fmap_2 snd _ (a, pa))).
      pose proof (Hm2_pts pa Hpa) as Hpapts.
      apply Hpre in Hpre_apa; last done.
      assert (HbN : b ∉ N) by (by apply Hpush_N).
      assert (Hfpa : f pa < length pts) by (rewrite Fpts //; by apply idx_lt).
      assert (Hbpts : b ∈ pts).
      { destruct (decide (b ∈ pts)) as [|Hn]; [done|].
        destruct (Fop b (or_introl Hb) HbN) as (_ & _ & Hle). pose proof (Hle Hn). lia. }
      assert (Hfb : f b < length pts) by lia.
      assert (Hbpa' : pt_before pts b pa) by (by apply Hpt_of_f).
      assert (Hts' : ts_tr ts pts a b).
      { destruct Hts as [Hab|[(c & Hac & Hcb)|(d & c & Had & Hdc & Hcb)]].
        - left. by apply Hpre.
        - destruct (Hpop_old c b Hcb Hb Hfb) as (Hc & HcN & Hfcb).
          right; left. exists c. split; [by apply Hpre|].
          right. split_and!; [by apply Hpop_tr|by apply Hm2_pts|by apply Hpush|].
          intros Hbc. apply (pt_before_irrefl pts b (isv_nodup _ _ _ HI)).
          eapply pt_before_trans; [apply (isv_nodup _ _ _ HI)|exact Hbc|].
          apply Hpt_of_f; [by apply Hm2_pts|done|done|done|done].
        - destruct (Hpop_old c b Hcb Hb Hfb) as (Hc & HcN & Hfcb).
          destruct (Hpush_old d c Hdc) as (Hd & HdN & Hdpts & Hfdc);
            [apply Hm'2; by left|lia|].
          right; right. exists d, c. split_and!; [by apply Hpre| |].
          + left. split_and!; [by apply Hpush|by apply Hpop_tr|].
            apply Hpt_of_f; [done|by apply Hm2_pts|done|done|done].
          + right. split_and!; [by apply Hpop_tr|by apply Hm2_pts|by apply Hpush|].
            intros Hbc. apply (pt_before_irrefl pts b (isv_nodup _ _ _ HI)).
            eapply pt_before_trans; [apply (isv_nodup _ _ _ HI)|exact Hbc|].
            apply Hpt_of_f; [by apply Hm2_pts|done|done|done|done]. }
      destruct (Hm2_lookup pa Hpa) as [a' Ha'].
      assert (a' = a) as ->.
      { eapply (valid_match_inj_call ts m); [done|by eapply list_elem_of_lookup_2|done]. }
      destruct (isv_lifo _ _ _ HI _ a pa b Ha' Hpre_apa Hts' (proj1 (Hpush b) Hb) Hbpa')
        as (i & pb' & Hij & Hi).
      exists pb'. split.
      * rewrite Hm'. apply elem_of_app. left. by eapply list_elem_of_lookup_2.
      * assert (Hpb' : pb' ∈ m.*2).
        { by apply (list_elem_of_fmap_2 snd _ (b, pb')), list_elem_of_lookup_2 with i. }
        rewrite (Rold pb' (HN_m pb' Hpb')) (Rold pa HpaN) (Hm_idx i b pb' Hi). done.
Qed.
