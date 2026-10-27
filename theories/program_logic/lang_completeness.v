(* The file is ported from johannes/iris-completeness at MPI GitLab

Copyright (C) 2026, Johannes Hostert, Zichen Zhang, Puming Liu, Simon
Gregersen, Ralf Jung, and Joseph Tassarotti

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation
   and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its
   contributors may be used to endorse or promote products derived from
   this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

From iris_logatom.lib Require Import list.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic Require Export invariants ghost_map cancelable_invariants.
From iris.program_logic Require Export language.
From iris_logatom.pure_logic Require Export adequacy.
From iris_logatom.program_logic Require Import weakestpre.

Class lang_completeness_gen hlc Λ Σ `{!irisGS_gen hlc Λ Σ} := LangCompleteness {
  own_state : state Λ → iProp Σ;
  #[global] own_state_timeless :: ∀ σ, Timeless (own_state σ);
  lang_completeness :
  ∀ e1 σ E,
    reducible e1 σ →
    own_state σ ={E}=∗
    ((∃ K e1', ⌜LanguageCtx K⌝ ∗ ⌜e1 = K e1'⌝ ∗ ⌜to_val e1' = None⌝ ∗ ⌜Atomic WeaklyAtomic e1'⌝ ∗
      ∀ Φ, (▷(£ 1 -∗ ∀ κ v2 σ' efs,
      ⌜prim_step e1' σ κ (of_val v2) σ' efs⌝ ==∗
      (own_state σ' -∗ Φ v2) ∗ ([∗ list] n↦etp ∈ efs, WP etp {{ v, True}})) -∗
      WP e1' @E {{ Φ }})) ∨
      (own_state σ ∗ ∀ Φ,
        ▷(£ 1 -∗ ∀ e2 efs,
            (∀ σ1, own_state σ1 ={E}=∗
             ∃ κ σ1', ⌜prim_step e1 σ1 κ e2 σ1' efs⌝ ∗ own_state σ1') ={⊤}=∗
          WP e2 {{ Φ }} ∗ [∗ list] n↦etp ∈ efs, WP etp {{ v, True}}) -∗
      WP e1 {{ Φ }}))
}.

Class completenessG Λ Σ := CompletenessG {
  #[local] completenessG_tp :: ghost_mapG Σ nat (expr Λ);
  #[local] completenessG_cinv :: cinvG Σ;
}.

Definition completenessΣ Λ := #[ghost_mapΣ nat (expr Λ); cinvΣ].
Global Instance completenessG_subG Λ Σ : subG (completenessΣ Λ) Σ → completenessG Λ Σ.
Proof. solve_inG. Qed.

Local Lemma zip_elem_of_lookup {A} (i : nat) (a : A) (l : list A) :
  (i, a) ∈ zip (seq 0 (length l)) l → l !! i = Some a.
Proof.
  intros Hinl.
  enough (lemma: ∀ j, (i,a) ∈ zip (seq j (length l)) l → j≤i ∧ l !! (i-j) = Some a).
  { destruct (lemma 0 Hinl) as [_ H].
    replace (i-0) with i in H by lia.
    done. }
  clear. induction l as [|a0 l IH] => j Hinl; first set_solver.
  rewrite /= elem_of_cons in Hinl. destruct Hinl as [Hinl|Hinl].
  - simplify_eq. replace (j-j) with 0 by lia. set_solver.
  - destruct (IH _ Hinl) as [Hle Hlookupl].
    split; first lia.
    apply lookup_cons_Some. right. split; first lia.
    replace (i-j-1) with (i - S j) by lia.
    exact Hlookupl.
Qed.

Local Lemma insert_middle {A} (a b: A) (l1 l2 : list A) :
  <[length l1:=b]> (l1++a::l2) = (l1++b::l2).
Proof.
  rewrite insert_take_drop; last (rewrite length_app length_cons; lia).
  rewrite take_app_le //.
  rewrite drop_app_ge; last lia.
  replace (S (length l1) - length l1) with 1 by lia.
  rewrite take_ge //.
Qed.

Local Lemma threadpool_update {A} (i : nat) (a : A) (l : list A) :
  i < length l →
  <[i:=a]> (list_to_map (M:=gmap nat A) (zip (seq 0 (length l)) l)) =
  list_to_map (zip (seq 0 (length (<[i:=a]> l))) (<[i:=a]> l)).
Proof.
  intros [b Hlookup]%lookup_lt_is_Some_2.
  destruct (list_elem_of_split_length _ _ _ Hlookup) as (l1 & l2 & -> & ->).
  clear Hlookup.
  rewrite !insert_middle.
  rewrite !length_app !seq_app !zip_app; [|apply length_seq..].
  rewrite !length_cons -!cons_seq !zip_cons.
  simpl.
  rewrite !list_to_map_app !list_to_map_cons.
  rewrite insert_union_r; last first.
  { apply not_elem_of_list_to_map_1.
    rewrite fst_zip.
    - rewrite elem_of_seq. lia.
    - rewrite length_seq. lia. }
  by rewrite insert_insert_eq.
Qed.

Local Lemma threadpool_merge {A} (l1 l2 : list A) :
  list_to_map (M:=gmap nat A) (zip (seq (length l1) (length l2)) l2)
    ∪ list_to_map (zip (seq 0 (length l1)) l1)
  = list_to_map (zip (seq 0 (length (l1++l2))) (l1++l2)).
Proof.
  rewrite map_union_comm.
  - rewrite -list_to_map_app -zip_app; last by apply length_seq.
    by rewrite -seq_app -length_app.
  - apply map_disjoint_dom.
    rewrite !dom_list_to_map_L !fst_zip; first last.
    { rewrite length_seq. lia. }
    { rewrite length_seq. lia. }
    rewrite !list_to_set_seq.
    apply elem_of_disjoint => tid Hin1 Hin2.
    apply elem_of_set_seq in Hin1,Hin2.
    lia.
Qed.

Local Lemma threadpool_update_merge {A} (i : nat) (a : A) (l1 l2 : list A) :
  i < length l1 →
  list_to_map (M:=gmap nat A) (zip (seq (length l1) (length l2)) l2)
    ∪ <[i:=a]> (list_to_map (zip (seq 0 (length l1)) l1))
  = list_to_map (zip (seq 0 (length (<[i:=a]> l1++l2))) (<[i:=a]> l1++l2)).
Proof.
  intros Hi.
  rewrite threadpool_update //.
  replace (length l1) with (length (<[i:=a]> l1)) by apply length_insert.
  apply threadpool_merge.
Qed.

Local Lemma fractional_divide_n {Σ} (Q : Qp → iProp Σ) (Hf : Fractional Q) (p : positive) q :
  Q q -∗
  [∗ list] _ ∈ seq 0 (Pos.to_nat p), Q (q / pos_to_Qp p)%Qp.
Proof.
  revert q. induction p as [|p IHp] using Pos.peano_ind; intros q.
  - rewrite /= Qp.div_1. by iIntros "$".
  - iIntros "Hq".
    assert ((q / pos_to_Qp (Pos.succ p))%Qp + ((q * pos_to_Qp p) / pos_to_Qp (Pos.succ p))%Qp = q)%Qp as Heq.
    { rewrite -Qp.div_add_distr -{1}(Qp.mul_1_r q) -Qp.mul_add_distr_l pos_to_Qp_add Pos.add_1_l.
      rewrite -{2}(Qp.mul_1_l (pos_to_Qp (Pos.succ p))) Qp.div_mul_cancel_r Qp.div_1 //. }
    rewrite -{1}Heq Hf Pos2Nat.inj_succ seq_S /= big_sepL_snoc.
    iDestruct "Hq" as "[$ Hq]". iPoseProof (IHp with "Hq") as "Hres".
    iApply (big_sepL_wand with "Hres").
    iApply big_sepL_intro. iIntros "!>" (???) "H".
    iStopProof. f_equiv.
    rewrite Qp.div_div Qp.div_mul_cancel_r //.
Qed.

Section completeness.
  Context `{lang_completeness_gen hlc Λ Σ, !completenessG Λ Σ}.

  Let N := nroot .@ "iris_logatom.program_logic.lang_completeness".
  Context (γt : gname) (ϕ: val Λ → state Λ → Prop) (is_seq: Prop).

  Local Definition completeness_inv : iProp Σ :=
    ∃ t σ, own_state σ
    ∗ ghost_map_auth γt 1 (list_to_map (zip (seq 0 (length t)) t))
    ∗ ⌜adequate_tp NotStuck t σ ϕ⌝
    ∗ ⌜is_seq → ∃ e, t = [e] ∧ sequential e σ ⌝.

  Local Lemma wp_completeness_inv γ q n (e : expr Λ) Φ :
    cinv N γ completeness_inv -∗
    cinv_own γ q -∗
    n ↪[γt] e -∗
    ▷?(if (to_val e) then false else true)
      (∀ v q', n ↪[γt] (of_val v) ∗ cinv_own γ q' ∗ ⌜is_seq → q = q'⌝
        -∗ Φ v) -∗
    WP e {{ Φ }}.
  Proof.
    iIntros "#Hinv".
    iLöb as "IH" forall (q n e Φ).
    iIntros "Hq He◯ HΦ".
    iApply wp_inv_open_maybe.
    iMod (cinv_acc with "Hinv Hq") as "(>Hinv2&Hq&Hclose)"; first done.
    iDestruct "Hinv2" as (t σ) "(Hstate & Ht● & %Hadq & %Hseq)".
    iCombine "Ht● He◯" gives %Hlookup%elem_of_list_to_map_2%zip_elem_of_lookup.

    pose proof Hadq as [_ _ Hnot_stuck].
    opose proof (Hnot_stuck t σ e _ _ _) as [[v Hv]|Hred]; try reflexivity.
    { by eapply list_elem_of_lookup_2. }
    { eapply of_to_val in Hv. subst e. iModIntro. iLeft.
      iExists id, _. iSplit; first (iPureIntro; apply _).
      iSplit; first done.
      iSplit. { iPureIntro. apply val_atomic. }
      simpl. iApply wp_value'.
      iMod ("Hclose" with "[$Ht● $Hstate //]") as "_".
      iModIntro. iApply wp_value'.
      rewrite to_of_val. simpl.
      iApply "HΦ". iFrame "He◯ Hq". done. }
    iMod (lang_completeness with "Hstate") as "[H|H]"; first done.

    - iDestruct "H" as (K e1 ? Heq Hnotval Hatomic) "H". iModIntro.
      iLeft. iExists K, e1. do 3 (iSplit; first done).
      iApply "H". iIntros "!> _" (κ v2 σ2 efs Hbase).

      (* update ghost resources *)
      iMod (ghost_map_update (K (of_val v2)) with "Ht● He◯") as "[Ht● He◯]".
      iMod (ghost_map_insert_big (list_to_map (zip (seq (length t) (length efs)) efs)) with "Ht●") as "[Ht● Hefs◯]".
      { apply map_disjoint_dom.
        rewrite dom_insert_L !dom_list_to_map_L !fst_zip; first last.
        { rewrite length_seq. lia. }
        { rewrite length_seq. lia. }
        rewrite !list_to_set_seq.
        assert (n ∈ (set_seq 0 (length t) : gset nat)).
        { eapply elem_of_set_seq. apply lookup_lt_Some in Hlookup. lia. }
        replace ({[n]} ∪ set_seq 0 (length t) : gset nat)
          with (set_seq 0 (length t) : gset nat) by set_solver.
        symmetry. apply set_seq_add_disjoint. }
      rewrite threadpool_update_merge; last by eapply lookup_lt_Some.
      iModIntro.
      iPoseProof (fractional_divide_n _ _ (Pos.of_nat (S (length efs))) with "Hq") as "Hx".
      rewrite Nat2Pos.id // seq_S big_sepL_snoc /=.
      iDestruct "Hx" as "[Hefsfrac Hq]".

      iSplitR "Hefs◯ Hefsfrac"; last first.
      + rewrite big_sepM_list_to_map; last first.
        { rewrite fst_zip; first apply NoDup_seq.
          rewrite length_seq //. }
        iPoseProof (big_sepL2_sepL_2 with "Hefs◯ Hefsfrac") as "Hefsfracs".
        { rewrite length_zip !length_seq. lia. }
        rewrite big_sepL2_const_sepL_l. iDestruct "Hefsfracs" as "[_ Hefs]".
        rewrite big_sepL_zip_seq //.
        iApply (big_sepL_wand with "Hefs").
        iApply big_sepL_intro. iIntros "!>" (n' e' Hefs) "[He Hq]".
        iApply ("IH" with "Hq He").
        iIntros "!>" (??) "_". done.
      + subst e. iIntros "Hstate".
        eapply fill_step in Hbase as Hprim.
        eapply (adequate_tp_erased_step _ _ (<[n:=K (of_val v2)]> t ++ efs) σ2) in Hadq; last first.
        { clear -Hlookup Hprim.
          destruct (list_elem_of_split_length _ _ _ Hlookup) as (t1 & t2 & -> & ->).
          rewrite insert_middle -!assoc.
          exists κ. eapply step_atomic; [reflexivity..|assumption]. }

        iMod ("Hclose" with "[$Ht● $Hstate]") as "_".
        { iPureIntro. split; first done.
          intros His_seq. destruct (Hseq His_seq) as (e & -> & Hseq').
          apply lookup_lt_Some in Hlookup as Hn0.
          simpl in Hn0. assert (n=0) as -> by lia. clear Hn0.
          simpl in Hlookup. injection Hlookup as ->.
          pose proof (sequential_prim_step_nofork _ _ _ _ _ _ Hseq' Hprim) as ->.
          rewrite right_id_L /=.
          eexists. split; first reflexivity.
          eapply sequential_prim_step; eassumption. }
        iModIntro.
        iApply ("IH" with "Hq He◯").
        iIntros "!>" (v q') "(? & ? & %Hfork)".
        iApply "HΦ". iFrame. iPureIntro. intros His_seq.
        destruct (Hseq His_seq) as (e & -> & Hseq').
        specialize (Hfork His_seq).
        apply lookup_lt_Some in Hlookup as Hn0.
        simpl in Hn0. assert (n=0) as -> by lia. clear Hn0.
        simpl in Hlookup. injection Hlookup as ->.
        pose proof (sequential_prim_step_nofork _ _ _ _ _ _ Hseq' Hprim) as ->.
        rewrite -Hfork // -Pos.of_nat_succ /= Qp.div_1 //.

    - iDestruct "H" as "[Hstate H]". iModIntro. iRight.
      iMod ("Hclose" with "[$Hstate $Ht● //]") as "_".
      clear.
      iModIntro. iApply "H".
      iIntros "!> _" (e2 efs) "H".
      iMod (cinv_acc with "Hinv Hq") as "(>Hinv2&Hq&Hclose)"; first done.
      iDestruct "Hinv2" as (t σ) "(Hstate & Ht● & %Hadq & %Hseq)".
      iCombine "Ht● He◯" gives %Hlookup%elem_of_list_to_map_2%zip_elem_of_lookup.
      iMod ("H" with "[$Hstate]") as (κ σ2 Hprim) "Hstate".

      (* update ghost resources *)
      iMod (ghost_map_update e2 with "Ht● He◯") as "[Ht● He◯]".
      iMod (ghost_map_insert_big (list_to_map (zip (seq (length t) (length efs)) efs)) with "Ht●") as "[Ht● Hefs◯]".
      { apply map_disjoint_dom.
        rewrite dom_insert_L !dom_list_to_map_L !fst_zip; first last.
        { rewrite length_seq. lia. }
        { rewrite length_seq. lia. }
        rewrite !list_to_set_seq.
        assert (n ∈ (set_seq 0 (length t) : gset nat)).
        { eapply elem_of_set_seq. apply lookup_lt_Some in Hlookup. lia. }
        replace ({[n]} ∪ set_seq 0 (length t) : gset nat)
          with (set_seq 0 (length t) : gset nat) by set_solver.
        symmetry. apply set_seq_add_disjoint. }
      rewrite threadpool_update_merge; last by eapply lookup_lt_Some.
      iPoseProof (fractional_divide_n _ _ (Pos.of_nat (S (length efs))) with "Hq") as "Hx".
      rewrite Nat2Pos.id // seq_S big_sepL_snoc /=.
      iDestruct "Hx" as "[Hefsfrac Hq]".

      (* close the invariant *)
      eapply (adequate_tp_erased_step _ _ (<[n:=e2]> t ++ efs) σ2) in Hadq; last first.
      { clear -Hlookup Hprim.
        destruct (list_elem_of_split_length _ _ _ Hlookup) as (t1 & t2 & -> & ->).
        rewrite insert_middle -!assoc.
        exists κ. eapply step_atomic; [reflexivity..|assumption]. }
      iMod ("Hclose" with "[$Hstate $Ht●]") as "_".
      { iPureIntro. split; first done.
        intros His_seq. destruct (Hseq His_seq) as (e' & -> & Hseq').
        apply lookup_lt_Some in Hlookup as Hn0.
        simpl in Hn0. assert (n=0) as -> by lia. clear Hn0.
        simpl in Hlookup. injection Hlookup as ->.
        pose proof (sequential_prim_step_nofork _ _ _ _ _ _ Hseq' Hprim) as ->.
        rewrite right_id_L /=.
        eexists. split; first reflexivity.
        eapply sequential_prim_step; eassumption. }
      iModIntro.

      iSplitR "Hefs◯ Hefsfrac"; last first.
      + rewrite big_sepM_list_to_map; last first.
        { rewrite fst_zip; first apply NoDup_seq.
          rewrite length_seq //. }
        iPoseProof (big_sepL2_sepL_2 with "Hefs◯ Hefsfrac") as "Hefsfracs".
        { rewrite length_zip !length_seq. lia. }
        rewrite big_sepL2_const_sepL_l. iDestruct "Hefsfracs" as "[_ Hefs]".
        rewrite big_sepL_zip_seq //.
        iApply (big_sepL_wand with "Hefs").
        iApply big_sepL_intro. iIntros "!>" (n' e' Hefs) "[He Hq]".
        iApply ("IH" with "Hq He").
        iIntros "!>" (??) "_". done.
      + iApply ("IH" with "Hq He◯").
        iIntros "!>" (v q') "(? & ? & %Hfork)".
        iApply "HΦ". iFrame. iPureIntro. intros His_seq.
        destruct (Hseq His_seq) as (e' & -> & Hseq').
        specialize (Hfork His_seq).
        apply lookup_lt_Some in Hlookup as Hn0.
        simpl in Hn0. assert (n=0) as -> by lia. clear Hn0.
        simpl in Hlookup. injection Hlookup as ->.
        pose proof (sequential_prim_step_nofork _ _ _ _ _ _ Hseq' Hprim) as ->.
        rewrite -Hfork // -Pos.of_nat_succ /= Qp.div_1 //.
  Qed.
End completeness.

Lemma wp_completeness `{lang_completeness_gen hlc Λ Σ, !completenessG Λ Σ} e σ φ :
  adequate NotStuck e σ (λ v _, φ v) →
  own_state σ  ⊢ WP e {{ v, ⌜φ v⌝}}.
Proof.
  iIntros (Hadq) "Hstate".
  iMod (ghost_map_alloc (list_to_map (zip (seq 0 (length [e])) [e]))) as (γt) "[Ht● He◯]".
  iMod (cinv_alloc ⊤ _ (completeness_inv γt (λ v _, φ v) False) with "[$Ht● $Hstate]") as (γ) "[#Hinv Hq]".
  { iPureIntro. split; last done. by apply adequate_tp_adequate. }
  clear Hadq.

  rewrite big_sepM_singleton /=.
  iApply wp_fupd.
  iApply (wp_completeness_inv with "Hinv Hq He◯").
  iIntros "!>" (v q') "(He◯ & Hq & _)".

  iMod (cinv_acc with "Hinv Hq") as "(>Hinv2&Hq&Hclose)"; first done.
  iDestruct "Hinv2" as (t1 ?) "(Hstate & Ht● & %Hadq & %Hnofork)".
  iCombine "Ht● He◯" gives %Hlookup.
  iMod ("Hclose" with "[$Hstate $Ht● //]") as "_".

  iPureIntro.
  destruct t1 as [|e1 t1]; first set_solver.
  rewrite /= lookup_insert_eq in Hlookup.
  injection Hlookup as ->.
  destruct Hadq as [_ Hresult _].
  eapply Hresult. reflexivity.
Qed.

Lemma wp_completeness_nofork `{lang_completeness_gen hlc Λ Σ, !completenessG Λ Σ} e σ ϕ :
  adequate NotStuck e σ ϕ → sequential e σ →
  own_state σ  ⊢ WP e {{ v, ∃ σ', own_state σ' ∗ ⌜ϕ v σ'⌝}}.
Proof.
  iIntros (Hadq Hseq) "Hstate".
  iMod (ghost_map_alloc (list_to_map (zip (seq 0 (length [e])) [e]))) as (γt) "[Ht● He◯]".
  iMod (cinv_alloc ⊤ _ (completeness_inv γt ϕ True) with "[$Ht● $Hstate]") as (γ) "[#Hinv Hq]".
  { iPureIntro. split.
    - by apply adequate_tp_adequate.
    - intros _. exists e. auto. }
  clear Hadq Hseq.

  rewrite big_sepM_singleton /=.
  iApply wp_fupd.
  iApply (wp_completeness_inv with "Hinv Hq He◯").
  iIntros "!>" (v q') "(He◯ & Hq & %Hseq)".
  pose proof (Hseq I) as <-. clear Hseq.

  iMod (cinv_cancel with "Hinv Hq") as ">Hinv2"; first done.
  iDestruct "Hinv2" as (t1 ?) "($ & Ht● & %Hadq & %Hnofork)".
  iCombine "Ht● He◯" gives %Hlookup.

  iPureIntro.
  destruct t1 as [|e1 t1]; first set_solver.
  rewrite /= lookup_insert_eq in Hlookup.
  injection Hlookup as ->.
  destruct Hadq as [_ Hresult _].
  eapply Hresult. reflexivity.
Qed.

Lemma hoare_completeness `{lang_completeness_gen hlc Λ Σ, !completenessG Λ Σ} e σ φ :
  to_val e = None → adequate NotStuck e σ (λ v _, φ v) →
  {{{ own_state σ }}} e {{{ v, RET v; ⌜φ v⌝ }}}.
Proof.
  iIntros (Hnv Hadq Φ) "Hstate HΦ".
  iMod (ghost_map_alloc (list_to_map (zip (seq 0 (length [e])) [e]))) as (γt) "[Ht● He◯]".
  iMod (cinv_alloc ⊤ _ (completeness_inv γt (λ v _, φ v) False) with "[$Ht● $Hstate]") as (γ) "[#Hinv Hq]".
  { iPureIntro. split; last done. by apply adequate_tp_adequate. }
  clear Hadq.

  rewrite big_sepM_singleton /=.
  iApply wp_fupd.
  iApply (wp_completeness_inv with "Hinv Hq He◯").
  rewrite Hnv. iIntros "!>" (v q') "(He◯ & Hq & _)".

  iMod (cinv_acc with "Hinv Hq") as "(>Hinv2&Hq&Hclose)"; first done.
  iDestruct "Hinv2" as (t1 ?) "(Hstate & Ht● & %Hadq & %Hnofork)".
  iCombine "Ht● He◯" gives %Hlookup.
  iMod ("Hclose" with "[$Hstate $Ht● //]") as "_".

  iApply "HΦ". iPureIntro.
  destruct t1 as [|e1 t1]; first set_solver.
  rewrite /= lookup_insert_eq in Hlookup.
  injection Hlookup as ->.
  destruct Hadq as [_ Hresult _].
  eapply Hresult. reflexivity.
Qed.

Lemma hoare_completeness_nofork `{lang_completeness_gen hlc Λ Σ, !completenessG Λ Σ} e σ ϕ :
  to_val e = None → adequate NotStuck e σ ϕ → sequential e σ →
  {{{ own_state σ }}} e {{{ v σ', RET v; own_state σ' ∗ ⌜ϕ v σ'⌝ }}}.
Proof.
  iIntros (Hnv Hadq Hseq HΦ) "Hstate HΦ".
  iMod (ghost_map_alloc (list_to_map (zip (seq 0 (length [e])) [e]))) as (γt) "[Ht● He◯]".
  iMod (cinv_alloc ⊤ _ (completeness_inv γt ϕ True) with "[$Ht● $Hstate]") as (γ) "[#Hinv Hq]".
  { iPureIntro. split.
    - by apply adequate_tp_adequate.
    - intros _. exists e. auto. }
  clear Hadq Hseq.

  rewrite big_sepM_singleton /=.
  iApply wp_fupd.
  iApply (wp_completeness_inv with "Hinv Hq He◯").
  rewrite Hnv. iIntros "!>" (v q') "(He◯ & Hq & %Hseq)".
  pose proof (Hseq I) as <-. clear Hseq.

  iMod (cinv_cancel with "Hinv Hq") as ">Hinv2"; first done.
  iDestruct "Hinv2" as (t1 ?) "(Hstate & Ht● & %Hadq & %Hnofork)".
  iCombine "Ht● He◯" gives %Hlookup.

  iApply "HΦ". iFrame. iPureIntro.
  destruct t1 as [|e1 t1]; first set_solver.
  rewrite /= lookup_insert_eq in Hlookup.
  injection Hlookup as ->.
  destruct Hadq as [_ Hresult _].
  eapply Hresult. reflexivity.
Qed.
