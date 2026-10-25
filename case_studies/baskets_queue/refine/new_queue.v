(* refine_new_queue.v: proof of [new_queue_spec] for the
  Baskets Queue.  Mirrors [hw_queue/refine_new_queue.v]: allocates
  the dummy node, the head/tail references, and the three ghost
  authorities, then closes the [Nbq] invariant under the empty AbsQ
  state via [bq_sim_init]. *)

From iris.algebra Require Import auth excl gmap gset agree mono_nat mono_list.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy primitive_laws notation proofmode.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import trace.
From iris_logatom.pure_logic Require Import linear adequacy.
From iris_logatom.pure_logic.refine Require Import absq absq_refines_absq0
                                                    absq0_linearizable
                                                    backward_simulation.

From case_studies.baskets_queue Require Import impl refine.defs.

Section bq_skeleton_new_queue.
  Context `{!traceG Σ, !bqG Σ}.

  Local Notation Nbq := Nbq.
  Local Notation bq_inv_body := bq_inv_body.
  Local Notation is_bq := is_bq.
  Local Notation bq_repr := bq_repr.
  Local Notation init_bq := init_bq.

  Lemma new_queue_spec :
    ∀ `(!heapGS Σ), init_spec_type bq_repr NotStuck init_bq.
  Proof.
    iIntros (Hheap Φ) "_ HΦ".
    rewrite /init_bq.
    rewrite /new_queue. wp_pures.
    (* Allocate the dummy node — a 2-cell block. *)
    rewrite /new_node. wp_pures.
    wp_alloc dummy as "Hdummy"; first lia.
    rewrite array_cons array_cons array_nil.
    iDestruct "Hdummy" as "(Hd0 & Hd1 & _)".
    wp_pures.
    (* value field <- #() ; already #() from AllocN, but the program writes it. *)
    wp_store.
    wp_pures.
    (* next field <- InjL #() *)
    wp_store.
    wp_pures.
    wp_alloc head as "Hhead".
    wp_pures.
    wp_alloc tail as "Htail".
    wp_pures.
    (* Allocate the three ghost authorities. *)
    iMod (own_alloc (● (to_opmap ∅) : authR opmapUR)) as (γ_op) "Hauth_op".
    { rewrite /to_opmap fmap_empty. apply auth_auth_valid. done. }
    iMod (own_alloc (● (to_nodemap {[dummy := (None, #()) : node_info]})
                       ⋅ ◯ (to_nodemap {[dummy := (None, #()) : node_info]})
                       : authR nodemapUR))
      as (γ_nm) "[Hauth_nm Hfrag_nm]".
    { apply auth_both_valid_discrete. split; [done|].
      rewrite /to_nodemap map_fmap_singleton.
      apply: (proj2 (singleton_valid _ _)). done. }
    iMod (own_alloc (● (to_dqmap ∅) ⋅ ◯ (to_dqmap ∅) : authR dqmapUR))
      as (γ_dq) "[Hauth_dq Hfrag_dq]".
    { rewrite /to_dqmap fmap_empty. apply auth_both_valid_discrete.
      split; [done|done]. }
    iMod (own_alloc (mono_nat_auth (DfracOwn 1) 0)) as (γ_del) "Hauth_del".
    { apply mono_nat_auth_valid. }
    iMod (own_alloc (● (∅ : gset positive) : authR (gsetUR positive)))
      as (γ_calls) "Hauth_calls".
    { apply auth_auth_valid. done. }
    iMod (own_alloc (● (∅ : gset positive) : authR (gsetUR positive)))
      as (γ_no_O) "Hauth_no_O".
    { apply auth_auth_valid. done. }
    iMod (own_alloc (●ML ([] : list (leibnizO (positive * absq_action)))))
      as (γ_ls) "Hauth_ls".
    { apply mono_list_auth_valid. }
    iMod (own_alloc (● (to_witnessmap ∅) ⋅ ◯ (to_witnessmap ∅) : authR witnessmapUR))
      as (γ_w) "[Hauth_w Hfrag_w]".
    { rewrite /to_witnessmap fmap_empty. apply auth_both_valid_discrete. done. }
    iApply ("HΦ" $! γ_op (#head, #tail)%V).
    iIntros "!>" (l) "Htrace".
    iMod (inv_alloc Nbq _ (bq_inv_body γ_op γ_nm γ_dq γ_del γ_calls γ_no_O γ_ls γ_w head tail l)
            with "[Hd0 Hd1 Hhead Htail Htrace Hauth_op Hauth_nm Hfrag_nm Hauth_dq Hfrag_dq Hauth_del Hauth_calls Hauth_no_O Hauth_ls Hauth_w Hfrag_w]") as "#Hinv".
    { iNext. rewrite /bq_inv_body.
      iExists [(dummy, None, #())], 0%nat, dummy, dummy, dummy, [],
              absq_init, [], ∅, {[dummy := (None, #()) : node_info]}, ∅, ∅, ∅.
      iFrame "Hhead Htail Htrace Hauth_op Hauth_nm Hfrag_nm Hauth_dq Hfrag_dq Hauth_del Hauth_ls Hauth_no_O Hauth_w Hfrag_w".
      rewrite /absq_init /= dom_empty_L. iFrame "Hauth_calls".
      iSplitL "Hd0 Hd1".
      { rewrite /bq_chain /=.
        rewrite /next_value_of /mark_at /succ_at /=. iFrame. }
      iPureIntro. split_and!.
      - apply rtcL_refl.
      - by rewrite /trace_of_absq_labels /= filter_nil.
      - apply bq_sim_init.
      - reflexivity.
      - split.
        + intros l' τ d Hlk.
          destruct (decide (l' = dummy)) as [->|Hne].
          { rewrite lookup_singleton_eq in Hlk. injection Hlk as Habs _. discriminate. }
          rewrite lookup_singleton_ne in Hlk; [discriminate|done].
        + intros l1 l2 τ d1 d2 H1 H2.
          destruct (decide (l1 = dummy)) as [->|Hne1].
          { rewrite lookup_singleton_eq in H1. injection H1 as Habs _. discriminate. }
          rewrite lookup_singleton_ne in H1; [discriminate|done].
      - intros τ v Hlk. rewrite lookup_empty in Hlk. discriminate.
      - simpl. set_solver.
      - simpl. set_solver.
      - (* chain_op_inv: vacuous, chain has only the dummy at position 0 *)
        intros i lk τ d Hpos Hlk info Hop_lk.
        apply lookup_lt_Some in Hlk. simpl in Hlk. lia.
      - (* chain_witness_inv: vacuous, witness_map is empty *)
        split.
        { rewrite dom_empty_L. intros k Hk. set_solver. }
        intros τ tail_loc snap Hlk. rewrite lookup_empty in Hlk. discriminate. }
    iModIntro. iExists head, tail, γ_nm, γ_dq, γ_del, γ_calls, γ_no_O, γ_ls, γ_w. by iFrame "Hinv".
  Qed.

End bq_skeleton_new_queue.
