From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

Lemma au_fire `{!heapGS Σ} e P (Q : val → iProp Σ) Φ :
  Atomic WeaklyAtomic e →
  {{{ P }}} e @ ∅ {{{ v, RET v; Q v }}} →
  {{{ AU <{ P }> @ ⊤, ∅ <{ ∀∀ v, Q v, COMM Φ v }> }}} e {{{ v, RET v; Φ v }}}.
Proof.
  iIntros (Hatomic He Φ') "AU HΦ'".
  iMod "AU" as "[HP [_ HΦ]]".
  wp_apply (He with "HP") as (v) "HQ".
  iMod ("HΦ" with "HQ") as "HΦ".
  iModIntro.
  iApply ("HΦ'" with "HΦ").
Qed.
