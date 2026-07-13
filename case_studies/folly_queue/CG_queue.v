From iris.algebra Require Import agree excl_auth.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import diverge.
From iris_logatom.heap_lang Require Import reloc.
From case_studies.folly_queue Require Import lock list.

(* The course-grained queue is implemented as a linked list guarded by a
   lock. *)

Definition CG_dequeue_go : val := λ: "head",
  match: !"head" with
    (* diverging is legitimate because CG_queue is only for proof *)
    NONE => diverge #()
  | SOME "p" => "head" <- (Snd "p");; Fst "p"
  end.

Definition CG_dequeue : val := λ: "lock" "head" <>,
  acquire "lock" ;;
  let: "v" := CG_dequeue_go "head" in
  release "lock" ;;
  "v".

Definition CG_enqueue_go : val := rec: "enqueue" "x" "head" :=
  match: "head" with
    NONE => CONS "x" NIL
  | SOME "p" => CONS (Fst "p") ("enqueue" "x" (Snd "p"))
  end.

Definition CG_enqueue : val := λ: "lock" "head" "x",
  acquire "lock" ;;
  "head" <- CG_enqueue_go "x" (! "head") ;;
  release "lock".

Definition CG_queue : val := Λ:
  let: "head" := ref NIL in
  let: "lock" := newlock #() in
  ((λ: "x", CG_enqueue "lock" "head" "x"),
   (λ: "x", CG_dequeue "lock" "head" "x")).

Class CGQueueG Σ := {
  #[local] CGQueueG_meta :: inG Σ (agreeR (prodO gnameO gnameO));
  #[local] CGQueueG_content :: inG Σ (excl_authR (listO valO)); 
  #[local] CGQueueG_lockG :: lockG Σ;
}.

Definition CGQueueΣ := #[
  GFunctor (agreeRF (prodOF gnameO gnameO));
  GFunctor (excl_authRF (listOF valO));
  lockΣ].

Global Instance subG_CGQueueG Σ : subG CGQueueΣ Σ → CGQueueG Σ.
Proof. solve_inG. Qed.

(* Representation predicate for the course grained queue. *)
Fixpoint isCGQueue_go (xs : list val) : val :=
  match xs with
  | nil => NILV
  | x :: xs' => (CONSV x (isCGQueue_go xs'))
  end.

Definition cgQueueInv `{!heapGS Σ, !CGQueueG Σ} γ lk (ℓ : loc) : iProp Σ :=
  ∃ γl γq, own γ (to_agree (γl,γq)) ∗
    is_lock γl lk (∃ xs, ℓ ↦ (isCGQueue_go xs) ∗ own γq (●E xs)).

Definition cgQueueState `{!heapGS Σ, !CGQueueG Σ} γ (xs : list val) : iProp Σ :=
  ∃ γl γq, own γ (to_agree (γl,γq)) ∗ own γq (◯E xs).

Definition cgQueueInv_r `{!cfgGS Σ} lk (ℓ : loc) (xs : list val) : iProp Σ :=
  ℓ ↦ₛ (isCGQueue_go xs) ∗ is_locked_r lk false.

Section CG_queue_wp.
  Context `{!heapGS Σ, !CGQueueG Σ}.

  Lemma cgQueueInv_alloc γl lk ℓ xs:
    (∀ R : iProp Σ, R ={⊤}=∗ is_lock γl lk R) -∗
    ℓ ↦ isCGQueue_go xs ={⊤}=∗
    ∃ γ, cgQueueInv γ lk ℓ ∗ cgQueueState γ xs.
  Proof.
    iIntros "Hlk Hl".
    iMod (own_alloc (●E xs ⋅ ◯E xs)) as (γq) "[Hxs● Hxs◯]".
    { apply excl_auth_valid. }
    iMod (own_alloc (to_agree (γl, γq))) as (γ) "#Hmeta"; first done.
    iMod ("Hlk" with "[Hxs● Hl]"); last first.
    - iExists γ. iFrame "#∗". done.
    - iFrame "#∗".
  Qed.

  Lemma CG_enqueue_body_spec x xs Φ :
    ▷ Φ (isCGQueue_go (xs++[x])) -∗
    WP CG_enqueue_go x (isCGQueue_go xs) {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iInduction xs as [|x' xs'] "IH" forall (Φ); wp_rec; wp_pures; first by auto.
    wp_apply "IH".
    wp_pures. auto.
  Qed.

  Lemma CG_enqueue_spec γ lk ℓ (x : val) :
    cgQueueInv γ lk ℓ ⊢
    <<{ ∀∀ xs, cgQueueState γ xs }>>
      CG_enqueue lk #ℓ x @ ∅
    <<{ cgQueueState γ (xs++[x]) | RET #() }>>.
  Proof.
    iIntros "#Inv" (Φ) "AU".
    iDestruct "Inv" as (γl γq) "[Hmeta Hlock]".
    wp_lam. wp_pures.
    wp_apply (acquire_spec with "[$]") as "[Hlocked (%xs & Hl & Hxs●)]".
    wp_pures.
    wp_load.
    wp_apply CG_enqueue_body_spec.
    wp_store.

    iApply fupd_wp.
    iMod "AU" as (xs') "[Hst [_ Hcomm]]".
    iDestruct "Hst" as (γl' γq') "[Hmeta' Hxs◯]".
    iCombine "Hmeta Hmeta'" gives %Heq%to_agree_op_inv_L.
    injection Heq as <- <-. iClear "Hmeta'".
    iCombine "Hxs● Hxs◯" gives %<-%excl_auth_agree_L.
    iMod (own_update_2 with "Hxs● Hxs◯") as "[Hxs● Hxs◯]".
    { apply excl_auth_update. }
    iMod ("Hcomm" with "[$]") as "HΦ".
    iModIntro.

    wp_apply (release_spec with "[-HΦ]"); first iFrame "#∗".
    auto.
  Qed.

  Lemma CG_dequeue_body_spec ℓ xs :
    {{{ ℓ ↦ isCGQueue_go xs }}}
      CG_dequeue_go #ℓ
    {{{ (x : val) xs', RET x; ⌜xs=x::xs'⌝ ∗ ℓ ↦ isCGQueue_go xs' }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_lam. wp_load.
    destruct xs as [|x xs']; wp_pures.
    { wp_apply wp_diverge. }
    wp_store. wp_pures. iModIntro.
    iApply "HΦ". auto.
  Qed.

  Lemma CG_dequeue_spec γ lk ℓ :
    cgQueueInv γ lk ℓ ⊢
    <<{ ∀∀ xs, cgQueueState γ xs }>>
      CG_dequeue lk #ℓ #() @ ∅
    <<{ ∃∃ x xs', ⌜xs=x::xs'⌝ ∗ cgQueueState γ xs' | RET x }>>.
  Proof.
    iIntros "#Inv" (Φ) "AU".
    iDestruct "Inv" as (γl γq) "[Hmeta Hlock]".
    wp_lam. wp_pures.
    wp_apply (acquire_spec with "[$]") as "[Hlocked (%xs & Hl & Hxs●)]".
    wp_pures.
    wp_apply (CG_dequeue_body_spec with "Hl") as (x xs') "[-> Hl]".
    wp_pures.

    iApply fupd_wp.
    iMod "AU" as (xs_) "[Hst [_ Hcomm]]".
    iDestruct "Hst" as (γl' γq') "[Hmeta' Hxs◯]".
    iCombine "Hmeta Hmeta'" gives %Heq%to_agree_op_inv_L.
    injection Heq as <- <-. iClear "Hmeta'".
    iCombine "Hxs● Hxs◯" gives %<-%excl_auth_agree_L.
    iMod (own_update_2 with "Hxs● Hxs◯") as "[Hxs● Hxs◯]".
    { apply excl_auth_update. }
    iMod ("Hcomm" with "[Hxs◯]") as "HΦ".
    { iFrame "#∗". iPureIntro. reflexivity. }
    iModIntro.

    wp_apply (release_spec with "[-HΦ]") as "_"; first iFrame "#∗".
    wp_pures. auto.
  Qed.
End CG_queue_wp.

Section CG_queue_sec.
  Context `{!relocGS Σ}.

  Lemma refines_CG_enqueue_body_r E t (K : list ectx_item) A x xs :
    nclose relocN ⊆ E →
    (REL t << fill K (isCGQueue_go (xs ++ [x])) @ E : A) -∗
    (REL t << fill K (CG_enqueue_go x (isCGQueue_go xs)) @ E : A).
  Proof.
    iIntros (HNE) "H".
    iInduction xs as [|x' xs'] "IH" forall (K); simpl.
    - rel_rec_r. rel_pures_r. rel_pures_r.
      iApply "H".
    - simpl.
      rel_rec_r. rel_pures_r. rel_pures_r. rel_apply_r ("IH").
      rel_pures_r. done.
  Qed.

  Lemma refines_CG_enqueue_r lk ℓ E t A x xs :
    nclose relocN ⊆ E →
    cgQueueInv_r lk ℓ xs -∗
    (cgQueueInv_r lk ℓ (xs ++ [x]) -∗ REL t << #() @ E : A) -∗
    REL t << (CG_enqueue lk #ℓ x) @ E : A.
  Proof.
    iIntros (HNE) "[pts lofal] H".
    rewrite /CG_enqueue.
    rel_pures_r.
    rel_apply_r (refines_acquire_r with "lofal"). iIntros "lotru".
    rel_pures_r.
    rel_load_r.
    rel_apply_r (refines_CG_enqueue_body_r).
    rel_pures_r.
    rel_store_r.
    rel_pures_r.
    rel_apply_r (refines_release_r with "lotru"). iIntros "lofal".
    iApply "H".
    iFrame.
  Qed.

  Lemma refines_right_CG_dequeue lk ℓ E k x xs :
    nclose relocN ⊆ E →
    cgQueueInv_r lk ℓ (x :: xs) -∗
    refines_right k (CG_dequeue lk #ℓ #()) ={E}=∗
    cgQueueInv_r lk ℓ (xs) ∗ refines_right k (of_val x).
  Proof.
    iIntros (HNE) "[pts lofal] H". simpl.
    rewrite /CG_dequeue /CG_dequeue_go /is_locked_r.
    iDestruct "lofal" as (ℓk ->)  "Hlk".
    tp_pures k.
    tp_rec k.
    tp_cmpxchg_suc k.
    tp_pures k.
    tp_load k.
    tp_pures k.
    tp_store k.
    tp_pures k.
    tp_rec k.
    tp_store k.
    tp_pures k.
    iModIntro. iFrame "H". rewrite /cgQueueInv_r. iFrame "pts".
    iExists _. by iFrame.
  Qed.

  Lemma refines_CG_dequeue_cons_r lk ℓ E t A x xs :
    nclose relocN ⊆ E →
    cgQueueInv_r lk ℓ (x :: xs) -∗
    (cgQueueInv_r lk ℓ xs -∗ REL t << x @ E : A) -∗
    REL t << (CG_dequeue lk #ℓ #()) @ E : A.
  Proof.
    iIntros (HNE) "H1 H2".
    iApply refines_split. iIntros (k) "Hk".
    iMod (refines_right_CG_dequeue with "H1 Hk") as "[H1 Hk]"; first done.
    iSpecialize ("H2" with "H1").
    iApply (refines_combine with "H2 Hk").
  Qed.

End CG_queue_sec.
