From iris_logatom.lib Require Import sequence_map.
From iris.algebra Require Import gmap_view.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import primitive_laws notation proofmode.
From iris.prelude Require Import options.

(* A model of thread ID. *)
(* This theory models a threadpool with at most [max_threads] threads.
  Each thread (a worker) in the threadpool can “claim” a thread ID for
  itself before starting its work, provided that it “releases” the ID
  after finishing its work. By claiming a thread ID, the thread obtains
  a unique ID from the threadpool, which can be used to identify some
  thread-local resources that can only be accessed by the thread.
  Unlike a realworld thread ID, this claimed ID does not ties to a thread
  in HeapLang — any function may claim a thread ID at anytime, even if
  the thread executing the function has claimed a thread ID before, and
  a thread may release its thread ID far before it terminates and claim
  another ID later. Another difference is a threadpool must be explicitly
  allocated, and there can be multiple threadpools in the system, each
  has its own thread ID system. The behaviors of this thread ID model
  is a strict superset of realworld thread ID functions, but this is enough
  to verify soundness. *)

(* A threadpool is a boolean array. Each element indicates whether the tid
  at that index has been claimed. *)
Definition new_threadpool : val := λ: "max_threads",
  (AllocN "max_threads" #false, "max_threads").

Local Definition claim_tid_go : val :=
rec: "go" "available" "i" "n" :=
  if: CAS ("available" +ₗ "i") #false #true then
    "i"
  else
    "go" "available" (("i" + #1) `rem` "n") "n".

Definition claim_tid : val := λ: "tp",
  claim_tid_go (Fst "tp") #0 (Snd "tp").

Definition release_tid : val := λ: "tp" "tid",
  Fst "tp" +ₗ "tid" <- #false.

Class threadIDG Σ := ThreadIDG {
  #[local] threadIDG_inG :: inG Σ (gmap_viewR nat unitR);
}.

Definition threadIDΣ := #[GFunctor (gmap_viewR nat unitR)].

Global Instance subG_threadIDG Σ : subG threadIDΣ Σ → threadIDG Σ.
Proof. solve_inG. Qed.

(* ghost theory *)
Section def.
  Context `{!threadIDG Σ}.

  Definition own_threadpool_def γ (max_threads : nat) : iProp Σ := own γ (gmap_view_auth DfracDiscarded (seqM () 0 max_threads)).
  Definition own_threadpool_aux : seal own_threadpool_def. Proof. by eexists. Qed.
  Definition own_threadpool := own_threadpool_aux.(unseal).
  Definition own_threadpool_unseal : own_threadpool = own_threadpool_def := own_threadpool_aux.(seal_eq).

  Definition own_tid_def γ (tid : nat) : iProp Σ := own γ (gmap_view_frag tid (DfracOwn 1) ()).
  Definition own_tid_aux : seal own_tid_def. Proof. by eexists. Qed.
  Definition own_tid := own_tid_aux.(unseal).
  Definition own_tid_unseal : own_tid = own_tid_def := own_tid_aux.(seal_eq).

  Global Instance own_threadpool_persistent γ max_threads : Persistent (own_threadpool γ max_threads).
  Proof.
    rewrite own_threadpool_unseal /own_threadpool_def /gmap_view_auth.
    apply _.
  Qed.

  Global Instance own_threadpool_timeless γ max_threads : Timeless (own_threadpool γ max_threads).
  Proof.
    rewrite own_threadpool_unseal /own_threadpool_def. apply _.
  Qed.

  Global Instance own_tid_timeless γ tid : Timeless (own_tid γ tid).
  Proof.
    rewrite own_tid_unseal /own_tid_def. apply _.
  Qed.

  Lemma threadpool_tid_bounded γ max_threads tid :
    own_threadpool γ max_threads -∗ own_tid γ tid -∗ ⌜tid < max_threads⌝.
  Proof.
    rewrite own_threadpool_unseal /own_threadpool_def own_tid_unseal /own_tid_def.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[_ [_ Hlookup%leibniz_equiv]]%gmap_view_both_valid.
    apply lookup_seqM_Some in Hlookup. iPureIntro. lia.
  Qed.

  Lemma own_tid_exclusive γ tid1 tid2 :
    own_tid γ tid1 -∗ own_tid γ tid2 -∗ ⌜tid1 ≠ tid2⌝.
  Proof.
    rewrite own_tid_unseal /own_tid_def.
    iIntros "H1 H2" (->).
    iCombine "H1 H2" gives %[H _]%gmap_view_frag_op_valid. done.
  Qed.

  Lemma threadpool_tid_alloc max_threads :
    ⊢ |==> ∃ γ, own_threadpool γ max_threads ∗ [∗ list] i ∈ seq 0 max_threads, own_tid γ i.
  Proof.
    rewrite own_threadpool_unseal /own_threadpool_def own_tid_unseal /own_tid_def.
    iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γ) "H●".
    { apply gmap_view_auth_valid. }
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (gmap_view_alloc_big ∅ (seqM () 0 max_threads) (DfracOwn 1)); [set_solver|done..]. }
    rewrite right_id_L. iDestruct (big_opM_own_1 with "H◯") as "H◯".
    iMod (own_update with "H●") as "H●"; first apply gmap_view_auth_persist.
    iModIntro. iFrame "H●".
    iInduction max_threads as [|max_threads] "IH"; first done.
    rewrite seq_S left_id_L big_sepL_app big_sepL_cons big_sepL_nil right_id.
    rewrite seqM_S left_id_L big_sepM_insert; last (apply lookup_seqM_None; right; lia).
    iDestruct "H◯" as "[$ H◯]".
    by iApply "IH".
  Qed.
End def.

Section spec.
  Context `{!heapGS Σ, !threadIDG Σ}.

  Definition threadIDN := nroot .@ "heap_lang" .@ "thread_id".

  Local Definition threadpool_Inv γ l max_threads : iProp Σ :=
    [∗ list] (i : nat) ∈ seq 0 max_threads, ((l +ₗ i) ↦ #false ∗ own_tid γ i) ∨ (l +ₗ i) ↦ #true.

  Definition is_threadpool γ tp (max_threads : nat) : iProp Σ :=
    ∃ l : loc, ⌜tp = (#l, #max_threads)%V ∧ max_threads ≠ 0⌝ ∗
      own_threadpool γ max_threads ∗
      inv threadIDN (threadpool_Inv γ l max_threads).

  Lemma is_threadpool_tid_bounded γ tp max_threads tid :
    is_threadpool γ tp max_threads -∗ own_tid γ tid -∗ ⌜tid < max_threads⌝.
  Proof.
    iDestruct 1 as (?) "(_ & #H● & _)". iIntros "H◯".
    iDestruct (threadpool_tid_bounded with "H● H◯") as "$".
  Qed.

  Lemma new_threadpool_spec (max_threads : nat) :
    {{{ ⌜ max_threads ≠ 0 ⌝ }}}
      new_threadpool #max_threads
    {{{ γ tp, RET tp; is_threadpool γ tp max_threads }}}.
  Proof.
    iIntros (Φ) "%Hnz HΦ".
    wp_lam.
    wp_alloc l as "Hls"; first lia.
    replace (Z.to_nat max_threads) with max_threads by lia.
    wp_pures.
    iMod (threadpool_tid_alloc max_threads) as (γ) "[Htp Htids]".
    iMod (inv_alloc threadIDN ⊤ (threadpool_Inv γ l max_threads) with "[Hls Htids]") as "Inv".
    { iNext. rewrite /threadpool_Inv.
      clear Hnz.
      iInduction max_threads as [|max_threads] "IH".
      - simpl. done.
      - rewrite seq_S 2!big_sepL_app left_id_L 2!big_sepL_cons 2!big_sepL_nil 2!right_id.
        rewrite replicate_S_end /array big_sepL_app big_sepL_cons big_sepL_nil right_id.
        iDestruct "Hls" as "[Hls Hl]".
        iDestruct "Htids" as "[Htids Htid]".
        iDestruct ("IH" with "Hls Htids") as "$".
        iLeft. rewrite right_id length_replicate.
        iFrame. }
    iModIntro. iApply "HΦ". by iFrame.
  Qed.

  Lemma claim_tid_spec γ tp max_threads :
    {{{ is_threadpool γ tp max_threads }}}
      claim_tid tp
    {{{ tid, RET #tid; own_tid γ tid }}}.
  Proof.
    iIntros (Φ) "(%l & [-> %Hnz] & #Htp & #Inv) HΦ".
    wp_lam. wp_pures.
    remember 0 as i eqn:Heq.
    replace 0%Z with (Z.of_nat i) by lia.
    assert (Hi: i < max_threads) by lia.
    clear Heq Hnz.
    iLöb as "IH" forall (i Hi).
    wp_rec. wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv "Inv" as ">Hls" "Hclose".
    assert (Hmax_threads_destruct: max_threads = i + S (max_threads - i - 1)) by lia.
    iEval (rewrite /threadpool_Inv {1}Hmax_threads_destruct) in "Hls".
    rewrite seq_app left_id_L -cons_seq big_sepL_app big_sepL_cons.
    iDestruct "Hls" as "(Hls1 & [[Hl Htid]| Hl] & Hls2)".
    - wp_cmpxchg_suc.
      iMod ("Hclose" with "[Hls1 Hl Hls2]") as "_".
      { iNext.
        iEval (rewrite /threadpool_Inv {1}Hmax_threads_destruct).
        rewrite seq_app left_id_L -cons_seq big_sepL_app big_sepL_cons.
        iFrame "Hls1 Hls2". iRight. iFrame. }
      iModIntro. wp_pures. iModIntro.
      by iApply "HΦ".
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[Hls1 Hl Hls2]") as "_".
      { iNext.
        iEval (rewrite /threadpool_Inv {1}Hmax_threads_destruct).
        rewrite seq_app left_id_L -cons_seq big_sepL_app big_sepL_cons.
        iFrame "Hls1 Hls2". iRight. iFrame. }
      iModIntro. wp_pures.
      replace ((i+1) `rem` max_threads)%Z with (Z.of_nat ((i+1) `mod` max_threads)); last first.
      { rewrite -(Nat2N.id ((i + 1) `mod` max_threads)).
        rewrite -[in ((i+1) `rem` _)%Z](Nat2N.id i).
        replace (N.to_nat (N.of_nat i) + 1)%Z with (N.to_nat (N.of_nat (i+1)) : Z) by lia.
        rewrite -[in (_ `rem` max_threads)%Z](Nat2N.id max_threads).
        rewrite !N_nat_Z.
        rewrite -N2Z.inj_rem -Nat2N.inj_mod //. }
      wp_apply "IH"; last done.
      iPureIntro. apply Nat.mod_upper_bound. lia.
  Qed.

  Lemma release_tid_spec γ tp max_threads tid :
    {{{ is_threadpool γ tp max_threads ∗ own_tid γ tid }}}
      release_tid tp #tid
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[(%l & [-> %Hnz] & #Htp & #Inv) Htid] HΦ".
    wp_lam. wp_pures.
    iDestruct (threadpool_tid_bounded with "Htp Htid") as %Hbounded.
    iInv "Inv" as ">Hls" "Hclose".
    assert (Hmax_threads_destruct: max_threads = tid + S (max_threads - tid - 1)) by lia.
    iEval (rewrite /threadpool_Inv {1}Hmax_threads_destruct) in "Hls".
    rewrite seq_app left_id_L -cons_seq big_sepL_app big_sepL_cons.
    iDestruct "Hls" as "(Hls1 & [[Hl Htid']| Hl] & Hls2)".
    { iDestruct (own_tid_exclusive with "Htid Htid'") as %Hfalse. done. }
    wp_store.
    iMod ("Hclose" with "[-HΦ]") as "_".
    { iNext.
      iEval (rewrite /threadpool_Inv {1}Hmax_threads_destruct).
      rewrite seq_app left_id_L -cons_seq big_sepL_app big_sepL_cons.
      iFrame "Hls1 Hls2". iLeft. iFrame. }
    by iApply "HΦ".
  Qed.
End spec.
