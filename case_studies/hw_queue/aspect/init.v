(* Initialization. *)
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Import bag queue.
From iris_logatom.pure_logic Require Import encodable linear.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gset agree mono_list mono_nat.
From iris.base_logic Require Import invariants ghost_map.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy lang notation tactics unwrap.
From iris_logatom.heap_lang Require Import mgc fork_free.

From case_studies.hw_queue Require Import impl.
From case_studies.hw_queue.aspect Require Import defs.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !hwqG Σ}.

  Lemma init_spec sz : (0 < sz)%Z → init_spec_type repr_queue NotStuck (new_queue #sz).
  Proof.
    iIntros (Hsz Φ) "_ HΦ".
    wp_lam.
    wp_apply (wp_allocN with "[//]") as (l_ar) "[Har _]"; first done.
    wp_pures.
    wp_alloc l_back as "Hback".
    wp_pures.

    iMod (own_alloc (●MN 0)) as (γ_back) "Hback●".
    { apply mono_nat_auth_valid. }
    iMod (ghost_map_alloc_empty (K:=nat) (V:=array_state)) as (γ_ar) "Har●".
    iMod (ghost_map_alloc_empty (K:=positive) (V:=operation_state)) as (γ_op) "Hop●".
    iMod (ghost_map_alloc_empty (K:=positive) (V:=nat)) as (γ_tkn) "Htkn●".
    iMod (own_alloc (●ML [])) as (γ_match) "Hmatch●".
    { apply mono_list_auth_valid. }
    iMod (ghost_map_alloc_empty (K:=nat) (V:=positive)) as (γ_slot) "Hslot●".
    iMod (own_alloc (to_agree (γ_back,γ_ar,γ_op,γ_tkn,γ_match,γ_slot))) as (γ) "Hmeta"; first done.
    iModIntro.
    iApply "HΦ". iIntros (tracer) "Htrace".

    iApply (inv_alloc queueN  _ (is_hwq_inv γ (#sz, #l_ar, #l_back) tracer)).
    iNext.
    iExists (Z.to_nat sz), l_ar, l_back, (replicate (Z.to_nat sz) NONEV), 0, [], [].
    iExists γ_back, γ_ar, γ_op, γ_tkn, γ_match, γ_slot, ∅, ∅, ∅, ∅.
    iFrame.
    rewrite !big_sepL_nil !big_sepM_empty !right_id left_id.
    iPureIntro. split_and!; try done.
    - rewrite Z2Nat.id; [done|lia].
    - apply per_tag_wellformed_bag_nil.
    - apply I_queue_pre_nil.
    - apply length_replicate.
    - rewrite drop_0. apply Forall_forall => a Hin.
      by eapply elem_of_replicate_inv.
  Qed.
End proof.
