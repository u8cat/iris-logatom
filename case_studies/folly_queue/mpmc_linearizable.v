From iris_logatom.pure_logic Require Import linear.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris.program_logic Require Import atomic.
From iris_logatom.program_logic Require Import atomic_sound atomic_complete.
From iris_logatom.heap_lang Require Import reloc refines_linearizable trace fork_free.
From iris.heap_lang Require Import unwrap.
From case_studies.folly_queue Require Import lock set list turnSequencer CG_queue mpmcqueue refinement.

(** * Wrappers for the CG queue,  *)
Definition CG_init : val :=
  λ: <>,
    (newlock #(), ref NIL).

Definition CG_enqueue' : val :=
  λ: "q" "x",
    let: "lock" := Fst "q" in
    let: "head" := Snd "q" in
    CG_enqueue "lock" "head" "x".

Definition CG_dequeue' : val :=
  λ: "q" <>,
    let: "lock" := Fst "q" in
    let: "head" := Snd "q" in
    SOME (CG_dequeue "lock" "head" #()).

Definition CG_ops : list val := [CG_enqueue'; CG_dequeue'].

(** * Wrappers for the folly queue  *)
Definition MPMC_init : val :=
  λ: "size",
    let: "slots" := array_init "size" newSQueue in
    let: "pushTicket" := ref #0 in
    let: "popTicket"  := ref #0 in
    ("slots", "size", "pushTicket", "popTicket").

Definition MPMC_enqueue : val :=
  λ: "q" "x",
    let: "slots" := Fst (Fst (Fst "q")) in
    let: "size" := Snd (Fst (Fst "q")) in
    let: "pushTicket" := Snd (Fst "q") in
    let: "popTicket" := Snd "q" in
    enqueue "slots" "size" "pushTicket" "x".

Definition MPMC_dequeue : val :=
  λ: "q" <>,
    let: "slots" := Fst (Fst (Fst "q")) in
    let: "size" := Snd (Fst (Fst "q")) in
    let: "pushTicket" := Snd (Fst "q") in
    let: "popTicket" := Snd "q" in
    SOME (dequeue "slots" "size" "popTicket").

Definition MPMC_ops : list val := [MPMC_enqueue; MPMC_dequeue].


(** * Lifting of refineent to wrappers  *)
Section queue_refinement.
  Context `{!relocGS Σ, !TSG Σ, !queueG Σ}.

  Definition rel_queue (A : lrel Σ) : lrel Σ := LRel (λ v1 v2,
    ∃ γt γm γl (q : nat) (ℓpop ℓpush ℓarr : loc) SEQs (list : loc) l,
      ⌜v1 = (#ℓarr, #q, #ℓpush, #ℓpop)%V⌝ ∗ ⌜v2 = (l, #list)%V⌝ ∗ ⌜q > 0⌝ ∗
      inv queueN (I A γt γm γl q ℓpop ℓpush ℓarr SEQs list l))%I.

  Lemma init_refinement (q : nat) (A : lrel Σ) :
    q > 0 →
    ⊢ REL MPMC_init #q << CG_init #() : rel_queue A.
  Proof.
    intros Hqgt.

    rel_rec_l. rel_rec_r.

    iMod ghost_list_alloc as (γl) "Hlist".

    (* Step through implementation. *)
    rel_bind_l (array_init _ _).
    rel_apply_l refines_wp_l.
    wp_apply (makeArray_newSQueue γl); first done.
    iIntros (ℓarr SEQs) "(%Htsslen & arrPts & Hseqs)".
    rel_alloc_l ℓpush as "pushts".
    rel_alloc_l ℓpop as "popPts".
    do 3 rel_pure_l.

    (* Step through specification. *)
    rel_alloc_r list as "listPts".
    rel_apply_r refines_newlock_r. iIntros (l) "lofal".
    rel_pure_r.

    (* Establish the invariant. *)
    iMod (own_alloc (set_above 0)) as (γt) "Htok"; first done.
    iMod (own_alloc (● ∅ : requestRegR)) as (γm) "Hdec"; first by apply auth_auth_valid.
    iMod (inv_alloc queueN _ (I A γt γm γl q ℓpop ℓpush ℓarr SEQs _ _) with "[-]") as "#Hinv".
    { iNext. iExists [], []. simpl. iFrame.
      rewrite !dom_empty_L !big_sepS_empty. iFrame. done. }

    rel_pures_l. rel_pures_r.
    rel_values.
    by iFrame "#".
  Qed.

  Definition mpmc_valid_value : val → Prop :=
    λ v, val_is_unboxed (SOMEV v).

  Definition mpmc_model : model :=
    queue_model NeverEmpty mpmc_valid_value.

  Lemma op_refinement (n : nat) lrel_req :
    lrel_reqs (M := mpmc_model) !! n = Some lrel_req →
    ⊢ REL (MPMC_ops !!! n : val) << (CG_ops !!! n : val) :
      rel_queue lrel_eq → lrel_req → (() + lrel_eq) ∪ ().
  Proof.
    destruct n as [|[|n]]; simpl; intros Hn; simplify_eq.
    - (* Push *)
      rel_values.

      iIntros "!# !# %q1 %q2 Hq".
      iDestruct "Hq" as (?????????? -> -> ?) "#Hq".
      rel_rec_l; rel_pures_l; rel_rec_r; rel_pures_r.
      rel_values.

      iIntros "!# !# %req % [<- %Hreq]".
      rel_rec_l; rel_pures_l; rel_rec_r; rel_pures_r.

      rel_bind_l (enqueue _ _ _ _).
      rel_bind_r (CG_enqueue _ _ _).
      iApply refines_bind.
      { by iApply (enqueue_refinement with "Hq"). }
      iIntros (?? [-> ->]) "/=".
      rel_pures_l. rel_pures_r.
      rel_values.
    - (* Pop *)
      rel_values.

      iIntros "!# !# %q1 %q2 Hq".
      iDestruct "Hq" as (?????????? -> -> ?) "#Hq".
      rel_rec_l; rel_pures_l; rel_rec_r; rel_pures_r.
      rel_values.

      iIntros "!# !# %req % [<- %Hreq]".
      rel_rec_l; rel_pures_l; rel_rec_r; rel_pures_r.

      rel_bind_l (dequeue _ _ _).
      rel_bind_r (CG_dequeue _ _ _).
      iApply refines_bind; [by iApply (dequeue_refinement with "Hq")|].
      iIntros (?? ->) "/=".
      rel_pures_l; rel_pures_r.
      rel_values.
      iModIntro. iLeft. iExists _, _. eauto.
  Qed.

End queue_refinement.

Section cg_logatom.
  Context `{!heapGS Σ, !CGQueueG Σ}.
  (* any namespace disjoint with traceN should work *)
  Definition CGqueueN := nroot.@"case_studies.folly_queue.mpmc_linearizable.cg_logatom".

  Definition is_CG_queue γ v : iProp Σ :=
    ∃ lk (ℓ : loc), ⌜v=(lk,#ℓ)%V⌝ ∗ cgQueueInv γ lk ℓ.

  Lemma CG_init_spec :
    {{{ True }}}
      CG_init #()
    {{{ γ v, RET v; is_CG_queue γ v ∗ cgQueueState γ [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_alloc ℓ as "Hl".
    wp_apply (newlock_spec_strong with "[//]") as (lk γl) "Hlock".
    wp_pures.
    change NILV with (isCGQueue_go []).
    iMod (cgQueueInv_alloc with "Hlock Hl") as (γ) "[Hinv Hstate]".
    iApply "HΦ". iModIntro. iFrame "Hstate".
    iExists #lk, ℓ. by iFrame.
  Qed.

  Lemma CG_ops_spec n γ q x :
    default default_vr (mpmc_model.(valid_requests) !! n) x →
    is_CG_queue γ q ⊢
    <<{ ∀∀ xs, cgQueueState γ xs }>>
      (CG_ops !!! n : val) q x @ ↑CGqueueN
    <<{ ∃∃ xs' x', cgQueueState γ xs' ∗
          ⌜default (@default_rr mpmc_model) (mpmc_model.(request_responses) !! n) xs x xs' x'⌝
        | RET x'}>>.
  Proof.
    iIntros (Hvr) "(%lk & %ℓ & -> & #Inv) %Φ AU".
    destruct n as [|[|n]]; simpl in Hvr |- *; last by destruct Hvr.
    - wp_lam. wp_pures.
      awp_apply (CG_enqueue_spec with "Inv").
      iApply (aacc_aupd_commit with "AU"); first done.
      iIntros (xs) "Hst".
      iAaccIntro with "Hst"; first auto with iFrame.
      iIntros "Hst !>".
      iFrame "Hst". iExists #(). iSplit; first by iPureIntro.
      auto.
    - subst x. wp_lam. wp_pures.
      awp_apply (CG_dequeue_spec with "Inv").
      iApply (aacc_aupd_commit with "AU"); first done.
      iIntros (xs) "Hst".
      iAaccIntro with "Hst"; first auto with iFrame.
      iIntros (x xs') "[-> Hst] !>".
      iFrame "Hst". iExists (SOMEV x). iSplit; first by iPureIntro.
      iIntros "HΦ !>". wp_pures. auto.
  Qed.
End cg_logatom.

Section mpmc_logatom.
  Context `{!heapGS Σ}.
  Context `{!linearizabilityG (M:=mpmc_model) Σ}.
  Context `{!relocPreG Σ, !logicatomicityG Σ, !traceG Σ}.
  Context `{!TSG Σ, !queueG Σ, !CGQueueG Σ}.

  Definition is_mpmc γ q := is_P (M:=mpmc_model) MPMC_ops γ q.
  Definition mpmc_content γ (ls : list val) := P_state (M:=mpmc_model) γ ls.

  Definition MPMC_init_wrapper: val := λ: "sz", wrap_init (MPMC_init "sz").
  Definition MPMC_enqueue_wrapper: val := λ: "q" "v", wrap_op Push (MPMC_ops !!! Push : val) "q" "v".
  Definition MPMC_dequeue_wrapper: val := λ: "q", unwrap (wrap_op Pop (MPMC_ops !!! Pop : val) "q" #()).

  Lemma MPMC_init_spec size :
    size > 0 →
    {{{ True }}}
      MPMC_init_wrapper #size
    {{{ γ q, RET q; is_mpmc γ q ∗ mpmc_content γ [] }}}.
  Proof.
    intros Hsize.
    opose proof (logatom_refines_init mpmc_model
              (λ H, rel_queue lrel_eq) (λ H, (() + lrel_eq) ∪ ())%lrel
              (MPMC_init #size) (CG_init #()) MPMC_ops CG_ops CGqueueN
              (λ H : heapGS Σ, @is_CG_queue Σ H _)
              (λ H : heapGS Σ, @cgQueueState Σ H _)
              _ _ _ _ _ _ _ _ _ _ _ _)
              as init_spec.
    - done.
    - done.
    - intros ?. apply fork_free_sequential. compute_done.
    - intros ?. apply fork_free_sequential. compute_done.
    - done.
    - done.
    - solve_ndisj.
    - by iIntros (??? [(?&?&[(->&->&->&->) | (->&->&->)]) | [-> ->]]).
    - intros ?. exact CG_init_spec.
    - intros ?. exact CG_ops_spec.
    - intros. by eapply init_refinement.
    - intros. by apply op_refinement.
    - iIntros (Φ) "HT HΦ".
      wp_lam. iApply (init_spec with "HT HΦ").
  Qed.

  Lemma MPMC_op_spec (n : nat) γ (q y : val) :
    default default_vr (mpmc_model.(valid_requests) !! n) y →
    is_mpmc γ q ⊢
    <<{ ∀∀ s, mpmc_content γ s }>>
      wrap_op n (MPMC_ops !!! n : val) q y @ ↑Nlogatom
    <<{ ∃∃ s' y', mpmc_content γ s' ∗
          ⌜default (@default_rr mpmc_model) (mpmc_model.(request_responses) !! n) s y s' y'⌝
        | RET y' }>>.
  Proof.
    eapply (logatom_refines_op mpmc_model
              (λ H, rel_queue lrel_eq) (λ H, (() + lrel_eq) ∪ ())%lrel
              (MPMC_init #(Z.of_nat 1)) (CG_init #()) MPMC_ops CG_ops CGqueueN
              (λ H : heapGS Σ, @is_CG_queue Σ H _)
              (λ H : heapGS Σ, @cgQueueState Σ H _)).
    - done.
    - done.
    - intros ?. apply fork_free_sequential. compute_done.
    - intros ?. apply fork_free_sequential. compute_done.
    - done.
    - done.
    - solve_ndisj.
    - by iIntros (??? [(?&?&[(->&->&->&->) | (->&->&->)]) | [-> ->]]).
    - intros ?. exact CG_init_spec.
    - intros ?. exact CG_ops_spec.
    - intros. eapply init_refinement. lia.
    - intros. by apply op_refinement.
  Qed.

  Lemma MPMC_enqueue_spec γ (q v : val) :
    val_is_unboxed (SOMEV v) →
    is_mpmc γ q ⊢
    <<{ ∀∀ ls, mpmc_content γ ls }>>
      MPMC_enqueue_wrapper q v @ ↑Nlogatom
    <<{ mpmc_content γ (ls++[v]) | RET #() }>>.
  Proof.
    iIntros (Hunboxed) "#His_mpmc %Φ AU".
    wp_lam. wp_pures.
    opose proof (MPMC_op_spec Push γ q v _) as op_spec.
    { exact Hunboxed. }
    awp_apply (op_spec with "His_mpmc").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (s) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
    destruct Hrr as [-> ->].
    iFrame "Hcontent". auto.
  Qed.

  Lemma MPMC_dequeue_spec γ (q v : val) :
    is_mpmc γ q ⊢
    <<{ ∀∀ ls, mpmc_content γ ls }>>
      MPMC_dequeue_wrapper q @ ↑Nlogatom
    <<{ ∃∃ l ls', ⌜ls = l :: ls'⌝ ∗ mpmc_content γ ls' | RET l }>>.
  Proof.
    iIntros "#His_mpmc %Φ AU".
    wp_lam.
    opose proof (MPMC_op_spec Pop γ q #() _) as op_spec.
    { done. }
    awp_apply (op_spec with "His_mpmc").
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (ls) "Hcontent".
    iAaccIntro with "Hcontent"; first by iIntros "$ !>"; auto.
    iIntros (ls' y) "[Hcontent %Hrr] !>".
    destruct ls as [|l ls].
    { destruct Hrr. }
    destruct Hrr as [-> ->].
    iExists l, ls.
    iFrame "Hcontent". iSplit; first done.
    iIntros "HΦ !>".
    simpl.
    by wp_apply unwrap_spec.
  Qed.
End mpmc_logatom.
