(* Two additional primitive laws with later credits. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.heap_lang Require Export primitive_laws.
From iris.heap_lang Require Import tactics notation.

Local Notation steps_auth_update_S := primitive_laws.steps_auth_update_S.
Local Notation steps_lb_valid := primitive_laws.steps_lb_valid.

Section lifting.
Context `{!heapGS_gen hlc Σ}.

Lemma wp_fork_fupd_lc s E e Φ n :
  steps_lb n -∗
  ▷ (£ (S n) -∗ |={E}=> WP e @ s; ⊤ {{ _, True }} ∗ Φ (LitV LitUnit)) -∗
  WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "Hlb HeΦ". iApply lifting.wp_lift_step_fupdN; [done|].
  iIntros (σ1 ns κ κs nt) "(?&?&Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %?.
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
  { iPureIntro. destruct s; [|done]. apply base_prim_reducible.
    by eauto with base_step. }
  iIntros (e2 σ2 efs Hstep) "Hlc".
  iApply step_fupdN_intro; [done|]. iIntros "!> !>". iMod "Hclose" as "_".
  apply base_reducible_prim_step in Hstep; [|by eauto with base_step].
  inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iDestruct (lc_weaken (S n) with "Hlc") as "Hlc"; [lia|].
  iMod ("HeΦ" with "Hlc") as "[He HΦ]".
  iModIntro. iFrame. by iApply wp_value.
Qed.

Lemma twp_new_proph s E :
  [[{ True }]]
    NewProph @ s; E
  [[{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & HR & Hsteps) !>".
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  rename select proph_id into p.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro. do 2 (iSplit; first done). iFrame. by iApply "HΦ".
Qed.
Lemma wp_new_proph_lc s E n :
  {{{ steps_lb n }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs ∗ £ (S n) }}}.
Proof.
  iIntros (Φ) "#? HΦ". iApply (twp_wp_step_lc_texan with "[$] HΦ").
  iApply twp_new_proph; [by auto..|]; iIntros (pvs p) "Hp HΦ ? !>".
  iApply "HΦ"; iFrame.
Qed.
End lifting.
