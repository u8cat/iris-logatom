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
From iris.program_logic Require Export weakestpre.

Lemma prim_val_stuck Λ v σ κ e2 σ' efs :
  @prim_step Λ (of_val v) σ κ e2 σ' efs → False.
Proof.
  intros HH%val_stuck. by rewrite to_of_val in HH.
Qed.

Lemma val_atomic Λ a (v : val Λ) : Atomic a (of_val v).
Proof.
  intros ????? []%prim_val_stuck.
Qed.

Section magic.
  Context `{irisGS_gen hlc Λ Σ}.

  Lemma wp_inv_open_maybe_help1 (e : expr Λ) E1 E2 Φ :
    to_val e = None →
    (|={E1,E2}=>
      (∃ K e', ⌜LanguageCtx K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜(Atomic WeaklyAtomic e')⌝
        ∗ WP e' @ E2 {{ v, |={E2,E1}=> WP K (of_val v) @ E1 {{ Φ }} }})
      ∨ |={E2,E1}=> WP e @ E1 {{ Φ }})
    -∗ WP e @ E1 {{ Φ }}.
  Proof.
    iIntros (Hnv) "H".
    rewrite wp_unfold /wp_pre Hnv.
    iMod "H" as "[H|>$]".
    iDestruct "H" as "(%K & %e' & % & -> & %Hato & Hwp)".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e') as [?|] eqn:Heq.
    { eapply of_to_val in Heq. rewrite Heq.
      do 2 iMod "Hwp". rewrite wp_unfold /wp_pre Hnv. done. }
    iIntros (σ n κ κs n2) "Hσ".
    iMod ("Hwp" with "Hσ") as "[%Hred Hc]".
    iModIntro. iSplit.
    { iPureIntro. by eapply reducible_fill. }
    iIntros (x σ2 efs (e2&->&Hprim)%fill_step_inv); last done.
    iIntros "H£". iSpecialize ("Hc" $! _ _ _ Hprim with "H£").
    iApply (step_fupdN_mono with "Hc").
    iIntros "Hc". iMod "Hc" as "(Hσ & Hc & $)".
    eapply Hato in Hprim.
    rewrite wp_unfold /wp_pre.
    destruct (to_val e2) eqn:Hve2.
    { iMod "Hc" as ">Hc". iFrame "Hσ". eapply of_to_val in Hve2. by subst. }
    iMod ("Hc" with "[Hσ]") as "[%Hredu _]".
    { by erewrite app_nil_r. }
    by eapply not_reducible in Hredu.
  Qed.

  Lemma wp_inv_open_maybe (e : expr Λ) E1 E2 Φ :
    (|={E1,E2}=>
      (∃ K e', ⌜LanguageCtx K⌝ ∗ ⌜e = K e'⌝ ∗ ⌜(Atomic WeaklyAtomic e')⌝
        ∗ WP e' @ E2 {{ v, |={E2,E1}=> WP K (of_val v) @ E1 {{ Φ }} }})
      ∨ |={E2,E1}=> WP e @ E1 {{ Φ }})
    -∗ WP e @ E1 {{ Φ }}.
  Proof.
    iIntros "H".
    destruct (to_val e) as [v|] eqn:Hev; last by iApply wp_inv_open_maybe_help1.
    eapply of_to_val in Hev. subst e. iApply (wp_atomic).
    1: eapply val_atomic.
    iMod "H" as "[H|H]"; last first.
    { iModIntro. rewrite !wp_value_fupd'.
      iModIntro. iMod "H". done. }
    iDestruct "H" as "(%K & %e' & % & %Hvke & %Hato & Hwp)".
    destruct (to_val e') as [v'|] eqn:Hev'.
    { eapply of_to_val in Hev'. subst e'. rewrite !wp_value_fupd'.
      iMod "Hwp". do 2 iModIntro. rewrite -Hvke wp_value_fupd'. by iMod "Hwp". }
    eapply of_to_val_flip in Hvke.
    eapply fill_not_val in Hev'. congruence.
  Qed.
End magic.
