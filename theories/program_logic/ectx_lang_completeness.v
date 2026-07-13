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
From iris.program_logic Require Import ectx_language.
From iris_logatom.program_logic Require Export lang_completeness.

Class ectx_lang_completeness_gen hlc (Λ : ectxLanguage) Σ `{!irisGS_gen hlc Λ Σ} := EctxLangCompleteness {
  own_state : state Λ → iProp Σ;
  #[global] own_state_timeless :: ∀ σ, Timeless (own_state σ);
  ectx_lang_completeness :
  ∀ e1 σ E,
    base_reducible e1 σ →
    own_state σ ={E}=∗
    ((⌜Atomic WeaklyAtomic e1⌝ ∗ (∀ Φ, ((▷ ∀ κ v2 σ' efs,
      ⌜base_step e1 σ κ (of_val v2) σ' efs⌝  ==∗
      (own_state σ' -∗ Φ v2) ∗ [∗ list] n↦etp ∈ efs, WP etp {{ v, True }})) -∗
      WP e1 @E {{ Φ }})) ∨
    (own_state σ ∗ ∀ Φ,
      (▷ ∀ e2 efs,
        (∀ σ1, own_state σ1 ={E}=∗
        ∃ κ σ1', ⌜base_step e1 σ1 κ e2 σ1' efs⌝ ∗ own_state σ1') ={⊤}=∗
      WP e2 {{ Φ }} ∗ [∗ list] n↦etp ∈ efs, WP etp {{ v, True }}) -∗
    WP e1 {{ Φ }}))
}.

Section proof.
  Context `{ectx_lang_completeness_gen hlc Λ Σ}.

  Local Lemma lang_completeness e1 σ E :
    reducible e1 σ →
    own_state σ ={E}=∗
    ((∃ K e1', ⌜LanguageCtx K⌝ ∗ ⌜e1 = K e1'⌝ ∗ ⌜to_val e1' = None⌝ ∗ ⌜Atomic WeaklyAtomic e1'⌝ ∗
      ∀ Φ, ((▷ ∀ κ v2 σ' efs,
      ⌜prim_step e1' σ κ (of_val v2) σ' efs⌝ ==∗
      (own_state σ' -∗ Φ v2) ∗ ([∗ list] n↦etp ∈ efs, WP etp {{ v, True}})) -∗
      WP e1' @E {{ Φ }})) ∨
      (own_state σ ∗ ∀ Φ,
        (▷ ∀ e2 efs,
            (∀ σ1, own_state σ1 ={E}=∗
             ∃ κ σ1', ⌜prim_step e1 σ1 κ e2 σ1' efs⌝ ∗ own_state σ1') ={⊤}=∗
          WP e2 {{ Φ }} ∗ [∗ list] n↦etp ∈ efs, WP etp {{ v, True}}) -∗
      WP e1 {{ Φ }})).
  Proof.
    iIntros ((κ&?&σ'&efs&Hprim)) "Hstate".
    simpl in Hprim. inversion Hprim as [K e1' e2' ?? Hbase]; simplify_eq; simpl in *.
    iMod (ectx_lang_completeness e1' σ E with "Hstate") as "[HH|HH]".
    - exists κ, e2', σ', efs. done.
    - iModIntro. iLeft. iExists (fill K), e1'.
      iSplit; first (iPureIntro; apply _). iSplit; first done.
      iSplit. { iPureIntro. by eapply val_base_stuck. }
      iDestruct "HH" as (Hatom) "HH". iSplit; first done.
      iIntros (Φ) "H".
      iApply "HH".
      iNext. iIntros (κ' v2 σ'' efs' HH).
      iApply "H".
      iPureIntro. by apply base_prim_step.
    - iModIntro. iRight. iDestruct "HH" as "[$ HH]".
      iIntros (Φ) "Hc". iApply wp_bind. simpl.
      iApply "HH".
      iNext. iIntros (??) "H".
      iMod ("Hc" with "[H]") as "Hc".
      + iIntros (?) "Hstate".
        iMod ("H" with "[$]") as (???) "H". iFrame.
        iPureIntro. eexists. econstructor; eauto.
      + rewrite wp_bind_inv. iModIntro. done.
  Qed.
End proof.

Global Program Instance ectx_lang_completeness_lang_completeness `{ectx_lang_completeness_gen hlc Λ Σ} :
  lang_completeness_gen hlc (ectx_lang Λ) Σ := {
  own_state σ := own_state σ;
}.
Next Obligation.
  intros ????????. simpl.
  eapply lang_completeness.
Qed.
