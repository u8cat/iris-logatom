(* The emptiness check of tryRem: after a scan in which every pool was empty, no top has
   changed since. *)

From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Import bag stack.
From iris_logatom.pure_logic Require Import encodable linear.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import agree mono_list mono_nat.
From iris.base_logic Require Import invariants ghost_map ghost_var.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy lang notation tactics unwrap proofmode.
From iris.heap_lang.lib Require Import array.
From iris_logatom.heap_lang Require Import mgc fork_free.
From iris_logatom.heap_lang.lib Require Import thread_id.
From case_studies.ts_stack Require Import impl.
From case_studies.ts_stack.aspect Require Import pure defs resources.

(* the second loop of tsstack_tryRem, after the substitution of its free variables *)
Definition check_loop (pools empty : loc) (n : nat) : val :=
  rec: "loop" "ID" :=
    if: "ID" ≠ #n then
      let: "current" := #pools +ₗ "ID" in
      if: ! "current" ≠ ! (#empty +ₗ "ID") then NONE else "loop" ("ID" + #1)
    else SOME NONE.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  (* (tsT, mT, pT) is the end of a scan in which the walk of every pool j saw the whole pool
     taken, with top A = es !! j *)
  Lemma check_loop_spec γs n pools ctr sents tracer p (empty : loc) (es : list val)
      (tsT : list (positive * trace)) (mT : list (positive * positive)) (pT : list pt_entry) (i : nat) :
    length sents = n →
    (∀ j, j < n → ∃ A : loc, es !! j = Some #A ∧ ∃ pS pTw mTw, pS `prefix_of` pT ∧
       pTw `prefix_of` pT ∧ mTw `prefix_of` mT ∧ walk_res sents pS pTw mTw j A None) →
    (p, Call Pop #()) ∈ tsT ∧
      (∀ τ1 r v, (τ1, Ret r) ∈ tsT → (τ1, Call Push v) ∈ tsT → ∃ c x j, (τ1, c, Some (x, j)) ∈ pT) ∧
      (∀ τ2, τ2 ∈ mT.*2 → (τ2, Call Pop #()) ∈ tsT) ∧
      (∀ τ c x j, (τ, c, Some (x, j)) ∈ pT → j < n) →
    i ≤ n →
    {{{ inv tsN (ts_inv γs n pools ctr sents tracer) ∗ hist tracer tsT ∗ view γs pT mT ∗
        empty ↦∗ es ∗ p ↪[γ_os γs] PopStarted ∗ [∗ list] j ∈ seq 0 i, check_wit γs sents pT mT j }}}
      check_loop pools empty n #i
    {{{ w, RET w; tryRem_post γs tracer sents n p w }}}.
  Proof.
    iIntros (Hlen Hall HwT Hi Φ) "(#Hinv & #HhT & #HvT & Hes & Hp & #Hcs) HΦ".
    iLöb as "IH" forall (i Hi) "Hcs".
    wp_rec. wp_pures.
    destruct (decide (i = n)) as [->|Hin].
    - rewrite bool_decide_eq_true_2 //. wp_pures. iModIntro. iApply "HΦ". iRight. iRight.
      iFrame "Hp". iSplit; [done|]. iExists tsT, mT, pT. iFrame "HhT Hcs".
      iDestruct "HvT" as "[$ $]". done.
    - rewrite bool_decide_eq_false_2; last (intros [= ?]; lia). wp_pures.
      destruct (Hall i ltac:(lia)) as (A & HesA & pS & pTw & mTw & HpST & HpTwT & HmTwT & HpSTw & ia & HA & Hwalk).
      wp_apply (wp_load_offset with "Hes") as "Hes"; first done.
      wp_bind (! _)%E.
      iInv "Hinv" as (σj) "(>[%HIj %Hsentj] & >Htr & >Hrest)" "Hclose".
      destruct (ti_len _ _ HIj) as (Hlsj & Hltj & _).
      destruct (lookup_lt_is_Some_2 (s_top σj) i) as [t Ht]; first lia.
      iDestruct (rest_view_valid with "Hrest HvT") as %[HpTj HmTj].
      iDestruct (rest_view_get with "Hrest") as "[Hrest #Hvj]".
      iDestruct (rest_top_acc with "Hrest") as "[Htop [Hback _]]"; first done.
      wp_load.
      iMod ("Hclose" with "[Htr Htop Hback]") as "_".
      { iNext. iExists σj. iFrame "Htr". iSplit; [done|]. by iApply "Hback". }
      iModIntro. wp_pures.
      destruct (decide (t = A)) as [->|Hne]; last first.
      { rewrite bool_decide_eq_false_2; last by intros [= ?]. wp_pures.
        iModIntro. iApply "HΦ". iLeft. by iFrame. }
      rewrite bool_decide_eq_true_2 //. wp_pure (If _ _ _). wp_pure (BinOp _ _ _).
      replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1)) by lia.
      iApply ("IH" $! (i + 1) with "[%] Hes Hp HΦ"); first lia.
      iModIntro. rewrite Nat.add_1_r seq_S big_sepL_app big_sepL_singleton /=. iFrame "Hcs".
      (* the check of pool i *)
      destruct (lookup_lt_is_Some_2 sents i) as [s Hs]; first lia.
      assert (HL0 : pool_list_l sents pS i `prefix_of` pool_list σj i).
      { apply pool_list_snap; [done|]. exact (transitivity HpST HpTj). }
      pose proof (check_ok n σj i A (pool_list_l sents pS i) ia pTw mTw mT HIj ltac:(lia) Ht HL0 HA
                    (transitivity HpTwT HpTj) HmTwT HmTj ltac:(by rewrite Hsentj)) as Hck.
      iExists (s_pts σj). iDestruct "Hvj" as "[$ _]". iPureIntro. split; [done|].
      intros x Hx. rewrite -Hsentj. apply Hck. rewrite /pool_list.
      apply (pnodes_in_pool_list _ _ _ _ s); [by rewrite Hsentj|].
      eapply elem_of_prefix; [exact Hx|]. by apply pnodes_prefix.
  Qed.
End proof.
