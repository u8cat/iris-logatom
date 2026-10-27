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

From iris.proofmode Require Import proofmode.
From iris_logatom.pure_logic Require Import state_set.
From iris_logatom.program_logic Require Export ectx_lang_completeness.
From iris.heap_lang Require Export proofmode notation.
From iris_logatom.heap_lang Require Import primitive_laws.

Local Lemma base_step_to_val_always_to_val e1 σ1a κsa (v2a : val) σ2a efsa σ1b κsb e2b σ2b efsb :
  base_step e1 σ1a κsa (Val v2a) σ2a efsa →
  base_step e1 σ1b κsb e2b σ2b efsb →
  is_Some (to_val e2b).
Proof.
  intros H1 H2. eapply base_step_to_val. 1: exact H1. 2: done. done.
Qed.

Local Lemma prim_step_to_val_always_to_val e1 σ1a κsa (v2a : val) σ2a efsa σ1b κsb e2b σ2b efsb :
  prim_step e1 σ1a κsa (Val v2a) σ2a efsa →
  prim_step e1 σ1b κsb e2b σ2b efsb →
  is_Some (to_val e2b).
Proof.
  intros [K e1' e2' -> Hv2a Hbase].
  edestruct (to_val_fill_some K e2') as [??].
  1: rewrite -Hv2a //.
  subst K e2'. clear Hv2a.
  intros [K' e1'' e2' Hx Hv2a Hbase'].
  simpl in Hx. subst e1' e2b.
  eapply ectx_language.base_ctx_step_val in Hbase as Hx.
  erewrite val_base_stuck in Hx; last done.
  destruct Hx as [[? [=]]|Hx].
  subst K'. simpl in Hbase.
  eapply base_step_to_val_always_to_val; done.
Qed.

Local Lemma base_step_to_val_atomic e1 σ1 κs v2 σ2 efs a :
  base_step e1 σ1 κs (Val v2) σ2 efs →
  Atomic a e1.
Proof.
  intros Hx. eapply strongly_atomic_atomic. intros ????? Hprim.
  eapply prim_step_to_val_always_to_val; last done.
  by eapply base_prim_step.
Qed.

Local Lemma base_step_more_proph_ids e σ κs e' σ' efs :
  base_step e σ κs e' σ' efs →
  σ.(used_proph_id) ⊆ σ'.(used_proph_id).
Proof.
  induction 1; simplify_eq; try set_solver.
  destruct bool_decide; set_solver.
Qed.

Local Hint Extern 4 (Atomic _ _) => by eapply base_step_to_val_atomic : typeclass_instances.

Section lemmas.
  Context `{!heapGS_gen hlc Σ}.
  Implicit Types (e : expr) (σ : state) (κ κs : list observation) (efs : list expr).

  (* The ownership of a fragment of the program state. *)
  Definition own_state (σ : state) : iProp Σ :=
    ([∗ map] l↦ov ∈ σ.(heap), from_option (λ v, l↦v) True ov ∗ meta_token l ⊤) ∗
    ([∗ set] p ∈ σ.(used_proph_id), ∃ vs, proph p vs).

  Local Lemma heap_lang_completeness_ind e1 σ E :
    base_reducible e1 σ →
    own_state σ ={E}=∗
    ((⌜Atomic WeaklyAtomic e1⌝ ∗ (∀ Φ, (▷(£ 1 -∗ ∀ κ v2 σ' efs,
      ⌜base_step e1 σ κ (of_val v2) σ' efs⌝  ==∗
      (own_state σ' -∗ Φ v2) ∗ [∗ list] n↦etp ∈ efs, WP etp {{ v, True }})) -∗
      WP e1 @E {{ Φ }})) ∨
    (own_state σ ∗ ∀ Φ E',
      ▷(£ 1 -∗ ∀ e2 efs,
        (∀ σ1, own_state σ1 ={E}=∗
        ∃ κ σ1', ⌜base_step e1 σ1 κ e2 σ1' efs⌝ ∗ own_state σ1') ={E'}=∗
      WP e2 @ E' {{ Φ }} ∗ [∗ list] n↦etp ∈ efs, WP etp {{ v, True }}) -∗
    WP e1 @ E' {{ Φ }})).
  Proof.
    iIntros ((κred&e2red&σ2red&efsred&Hstepred)) "Hstate".
    iInduction Hstepred as [] "IH"; simplify_eq.
    all: try (iRight; iModIntro; iFrame; iIntros (Φ ?) "H"; wp_pure credit:"Hlc";
      iSpecialize ("H" with "Hlc");
      iMod ("H" $! _ nil with "[]") as "[Hv _]";
      [ iIntros (?) "$ !>"; iExists _; iPureIntro; by econstructor
      | first [by rewrite wp_value_fupd'|done]]).

    1-7,9-10: iModIntro; iLeft; iSplit; first (iPureIntro; by apply _); iDestruct "Hstate" as "[Hheap Hproph]"; iIntros (Φ) "Hstep"; iApply wp_fupd.

    - iMod steps_lb_0 as "Hstep_lb".
      wp_apply (wp_allocN_seq_lc with "Hstep_lb") as (l2) "[Hmap Hlc]"; first done.
      rewrite big_sepL_sep. iDestruct "Hmap" as "[Hl2 Hmetas2]".
      rename select Z into n. rename select state into σ.
      iAssert (⌜∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l2 +ₗ i) = None⌝)%I as "%Hfresh".
      { iIntros (i Hi1 Hi2). destruct (heap σ !! (l2 +ₗ i)) as [vo|] eqn:Hvo. 2: done.
        iPoseProof (big_sepM_lookup_acc with "Hheap") as "((_&Hmeta1)&Hheap)". 1: done.
        iPoseProof (big_sepL_lookup_acc with "Hmetas2") as "(Hmeta2&_)".
        { eapply lookup_seq_lt with (i := Z.to_nat i). lia. }
        rewrite !Z2Nat.id //.
        iPoseProof (meta_token_ne with "Hmeta1 Hmeta2") as "%Hne"; done. }
      iMod ("Hstep" with "Hlc []") as "[Hx _]".
      { iPureIntro. by econstructor. }
      iModIntro; iApply "Hx".
      rewrite /state_init_heap /=. iFrame "Hproph".
      iApply big_sepM_union.
      { eapply heap_array_map_disjoint. rewrite length_replicate. intros ???. eapply Hfresh; lia. }
      iFrame "Hheap". clear Hfresh.
      iInduction (Z.to_nat n) as [|nx] "IH" forall (l2).
      { simpl. by iApply big_sepM_empty. }
      simpl. iApply big_sepM_union.
      { symmetry. eapply heap_array_map_disjoint. rewrite length_replicate.
        intros i Hi1 Hi2. rewrite lookup_singleton_ne //.
        intros Heq. rewrite -(Loc.add_0 l2) !Loc.add_assoc in Heq.
        eapply Loc.add_inj in Heq. lia. }
      rewrite big_sepM_singleton /=. rewrite Loc.add_0.
      iDestruct "Hl2" as "[$ Hl2]". iDestruct "Hmetas2" as "[$ Hmetas2]".
      rewrite -!fmap_S_seq !big_sepL_fmap.
      iApply ("IH" with "[Hl2]"); iClear "IH".
      all: iApply (big_sepL_wand with "[$]").
      all: iApply big_sepL_intro; iIntros "!>" (???); rewrite Loc.add_assoc.
      all: iIntros "?"; iStopProof; f_equiv; f_equal; lia.
    - iPoseProof (big_sepM_insert_acc with "Hheap") as "((Hacc&Hmeta)&Hheap)"; first done.
      simpl.
      iMod steps_lb_0 as "Hstep_lb".
      wp_apply (wp_free_lc with "[$]") as "Hlc".
      iPoseProof ("Hheap" $! None with "[$Hmeta //]") as "Hheap".
      iMod ("Hstep" with "Hlc []") as "(Hx &_)".
      { iPureIntro. by econstructor. }
      iModIntro. iApply "Hx". by iFrame.
    - iPoseProof (big_sepM_lookup_acc with "Hheap") as "((Hacc&Hmeta)&Hheap)". 1: done.
      simpl.
      iMod steps_lb_0 as "Hstep_lb".
      wp_apply (wp_load_lc with "[$]") as "[Hacc Hlc]".
      iPoseProof ("Hheap" with "[$Hacc $Hmeta]") as "Hheap".
      iMod ("Hstep" with "Hlc []") as "(Hx&_)".
      { iPureIntro. by econstructor. }
      simpl. iApply "Hx". by iFrame.
    - iPoseProof (big_sepM_insert_acc with "Hheap") as "((Hacc&Hmeta)&Hheap)". 1: done.
      simpl.
      iMod steps_lb_0 as "Hstep_lb".
      wp_apply (wp_store_lc with "[$]") as "[Hacc Hlc]".
      iPoseProof ("Hheap" $! (Some _) with "[$Hacc $Hmeta]") as "Hheap".
      iMod ("Hstep" with "Hlc []") as "(Hx&_)".
      { iPureIntro. by econstructor. }
      simpl. iApply "Hx". by iFrame.
    - iPoseProof (big_sepM_insert_acc with "Hheap") as "((Hacc&Hmeta)&Hheap)". 1: done.
      simpl.
      iMod steps_lb_0 as "Hstep_lb".
      wp_apply (wp_xchg_lc with "[$]") as "[Hacc Hlc]".
      iPoseProof ("Hheap" $! (Some _) with "[$Hacc $Hmeta]") as "Hheap".
      iMod ("Hstep" with "Hlc []") as "(Hx&_)".
      { iPureIntro. by econstructor. }
      iModIntro. iApply "Hx". by iFrame.
    - iPoseProof (big_sepM_insert_acc with "Hheap") as "((Hacc&Hmeta)&Hheap)". 1: done.
      simpl.
      iMod steps_lb_0 as "Hstep_lb".
      lazymatch goal with H: vals_compare_safe ?vl_ ?v1_ |- _ =>
        rename vl_ into vl;
        rename v1_ into v1
      end.
      destruct (decide (v1 = vl)) as [-> | Hne].
      1: wp_apply (wp_cmpxchg_suc_lc with "[$]") as "[Hacc Hlc]"; [done|done|..].
      2: wp_apply (wp_cmpxchg_fail_lc with "[$]") as "[Hacc Hlc]"; [done|done|..].
      all: iPoseProof ("Hheap" $! (Some _) with "[$Hacc $Hmeta]") as "Hheap".
      all: iMod ("Hstep" with "Hlc []") as "(Hx&_)";
       [|iModIntro; iApply "Hx"]; [iPureIntro; econstructor; [naive_solver..|]|iFrame].
      + symmetry. by eapply bool_decide_eq_true_2.
      + symmetry. by eapply bool_decide_eq_false_2.
      + rewrite insert_id //.
    - iPoseProof (big_sepM_insert_acc with "Hheap") as "((Hacc&Hmeta)&Hheap)". 1: done.
      simpl.
      iMod steps_lb_0 as "Hstep_lb".
      wp_apply (wp_faa_lc with "[$]") as "[Hacc Hlb]".
      iPoseProof ("Hheap" $! (Some _) with "[$Hacc $Hmeta]") as "Hheap".
      iMod ("Hstep" with "Hlb []") as "(Hx&_)".
      { iPureIntro. by econstructor. }
      iModIntro. iApply "Hx". by iFrame.
    - iMod steps_lb_0 as "Hstep_lb".
      wp_apply (wp_new_proph_lc with "Hstep_lb") as (pvs pid) "[Hidnew Hlc]".
      rename select state into σ.
      iAssert (⌜pid ∉ σ.(used_proph_id)⌝)%I as "%Hfresh".
      { iIntros (Hc). iPoseProof (big_sepS_elem_of_acc with "Hproph") as "[(%X & HH) _]".
        1: done. iApply (proph_exclusive with "Hidnew HH"). }
      iMod ("Hstep" with "Hlc []") as "(Hx&_)".
      { iPureIntro. by econstructor. }
      iModIntro. iApply "Hx". iFrame "Hheap". iApply big_sepS_union. 1: set_solver.
      rewrite big_sepS_singleton. iFrame "Hproph". iExists _. done.
    - rename select proph_id into p.
      rename select (base_step _ _ _ _ _ _) into Hstepred.
      match goal with H: (base_step _ ?σx _ _ ?σx' _) |- _ => rename σx into σ; rename σx' into σ' end.
      iPoseProof (big_sepS_elem_of_acc with "Hproph") as "((%pvs&Hele)&Hproph)". 1: done.
      iApply (wp_resolve_strong with "Hele").
      { eapply val_stuck, base_prim_step; done. }
      iIntros "Hele". iSpecialize ("Hproph" with "[$Hele]").
      iMod ("IH" with "[$Hheap $Hproph]") as "[H|H]".
      + iDestruct "H" as (Hatom) "Hrst".
        iApply ("Hrst"). iNext.
        iIntros "Hlc" (κ v2 σ2' efs Hbase).
        iSpecialize ("Hstep" with "Hlc").
        iMod ("Hstep" $! _ _ _ _ with "[%]") as "[Hwp $]".
        { by econstructor. }
        iModIntro. iIntros "[Hheap Hproph]".
        iPoseProof (big_sepS_elem_of_acc with "Hproph") as "((%pvs2&Hele)&Hproph)".
        { eapply base_step_more_proph_ids; done. }
        iFrame "Hele". iIntros (pvs'' ->) "Hele". iApply "Hwp".
        iFrame "Hheap". iApply "Hproph". by iFrame "Hele".
      + iDestruct "H" as "(Hheap&Hrst)".
        iApply "Hrst".
        iNext. iIntros "Hlc" (e2 efs) "H".
        iMod ("H" $! σ with "Hheap") as (κ σ1' Hbase) "H".
        pose proof Hbase as Hbase'.
        eapply base_step_to_val_always_to_val in Hbase' as [v2 Hto_val]; last exact Hstepred.
        apply of_to_val in Hto_val. subst e2. clear Hstepred.
        iSpecialize ("Hstep" with "Hlc").
        iMod ("Hstep" $! _ _ _ _ with "[%]") as "[Hwp Hff]".
        { by econstructor. }
        iModIntro. iSplitR "Hff"; last first.
        { iApply (big_sepL_wand with "Hff"). iClear "IH". iApply big_sepL_intro.
          iIntros "!>" (???) "H". iApply (wp_wand with "H"). iIntros (?) "_". done. }
        iDestruct "H" as "[Hheap Hproph]". iApply wp_value.
        iPoseProof (big_sepS_elem_of_acc with "Hproph") as "((%pvs2&Hele)&Hproph)".
        { eapply base_step_more_proph_ids; done. }
        iFrame "Hele". iIntros (pvs'' ->) "Hele". iApply "Hwp".
        iFrame "Hheap". iApply "Hproph". by iFrame "Hele".
    - iRight. iModIntro. iFrame. iIntros (??) "H".
      iMod steps_lb_0 as "Hstep_lb".
      iApply (wp_fork_fupd_lc with "Hstep_lb").
      iIntros "!> Hlc". iSpecialize ("H" with "Hlc").
      iMod ("H" $! _ [_] with "[]") as "(H1&H)".
      { iIntros (?) "$ !>". iPureIntro. eexists. by econstructor. }
      rewrite big_sepL_singleton. iFrame.
      rewrite wp_value_fupd'. done.
  Qed.

  Local Lemma heap_lang_completeness e1 σ E :
    base_reducible e1 σ →
    own_state σ ={E}=∗
    ((⌜Atomic WeaklyAtomic e1⌝ ∗ (∀ Φ, (▷(£ 1 -∗ ∀ κ v2 σ' efs,
      ⌜base_step e1 σ κ (of_val v2) σ' efs⌝  ==∗
      (own_state σ' -∗ Φ v2) ∗ [∗ list] n↦etp ∈ efs, WP etp {{ v, True }})) -∗
      WP e1 @E {{ Φ }})) ∨
    (own_state σ ∗ ∀ Φ,
      ▷(£ 1 -∗ ∀ e2 efs,
        (∀ σ1, own_state σ1 ={E}=∗
        ∃ κ σ1', ⌜base_step e1 σ1 κ e2 σ1' efs⌝ ∗ own_state σ1') ={⊤}=∗
      WP e2 {{ Φ }} ∗ [∗ list] n↦etp ∈ efs, WP etp {{ v, True }}) -∗
    WP e1 {{ Φ }})).
  Proof.
    iIntros (Hred) "Hstate".
    iMod (heap_lang_completeness_ind with "Hstate") as "[H|H]"; first done.
    - iModIntro. iLeft. iExact "H".
    - iModIntro. iRight. iDestruct "H" as "[$ H]".
      iIntros (Φ). iApply "H".
  Qed.
End lemmas.

Global Instance heap_lang_ectx_lang_completeness `{heapGS_gen hlc Σ} :
  ectx_lang_completeness_gen hlc heap_ectx_lang Σ := {
  own_state := own_state;
  ectx_lang_completeness := heap_lang_completeness;
}.

Section proof.
  Context `{!heapGS Σ, !completenessG heap_lang Σ}.
  Implicit Types (e : expr) (σ : state) (φ : val → Prop) (ϕ : val → state → Prop).

  Lemma own_state_empty :
    ⊢ own_state ∅.
  Proof.
    rewrite /own_state big_sepM_empty big_sepS_empty. auto.
  Qed.

  Lemma wp_completeness e σ φ :
    adequate NotStuck e σ (λ v _, φ v) →
    own_state σ ⊢ WP e {{ v, ⌜φ v⌝}}.
  Proof.
    pose proof wp_completeness as H.
    apply H.
  Qed.

  Lemma wp_completeness_nofork e σ ϕ :
    adequate NotStuck e σ ϕ → sequential e σ →
    own_state σ ⊢ WP e {{ v, ∃ σ', own_state σ' ∗ ⌜ϕ v σ'⌝ }}.
  Proof.
    pose proof wp_completeness_nofork as H.
    apply H.
  Qed.

  Lemma hoare_completeness_nofork e σ ϕ :
    to_val e = None →
    adequate NotStuck e σ ϕ → sequential e σ →
    {{{ own_state σ }}} e {{{ v σ', RET v; own_state σ' ∗ ⌜ϕ v σ'⌝ }}}.
  Proof.
    pose proof hoare_completeness_nofork as H.
    apply H.
  Qed.
End proof.
