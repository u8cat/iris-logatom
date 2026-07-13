From iris.algebra Require Import excl.
From iris_logatom.heap_lang Require Export reloc.
Set Default Proof Using "Type".

Definition newlock : val := λ: <>, ref #false.

Definition acquire : val := rec: "acquire" "x" :=
  if: CAS "x" #false #true
  then #()
  else "acquire" "x".

Definition release : val := λ: "x", "x" <- #false.

(* Definition with_lock : val := λ: "e" "l" "x",
  acquire "l";;
  let: "v" := "e" "x" in
  release "l";; "v". *)

Class lockG Σ := LockG { lock_tokG :: inG Σ (exclR unitO) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section def.
  Context `{!lockG Σ, !heapGS Σ}.
  Definition lockN := nroot.@"case_studies.folly_queue.lock".

  Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜lk = #l⌝ ∧ inv lockN (lock_inv γ l R))%I.

  Definition locked (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.

  Global Instance lock_inv_ne γ l : NonExpansive (lock_inv γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne γ l : NonExpansive (is_lock γ l).
  Proof. solve_proper. Qed.

  Global Instance is_lock_persistent γ l R : Persistent (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : Timeless (locked γ).
  Proof. apply _. Qed.
End def.

Section lockG_rules_wp.
  Context `{!lockG Σ, !heapGS Σ}.
  
  Lemma newlock_spec_strong :
    {{{ True }}} newlock #()
    {{{ (lk : loc) γ, RET #lk; ∀ R : iProp Σ, R ={⊤}=∗ is_lock γ #lk R }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iApply "HΦ". iIntros "!>" (R) "HR".
    iMod (inv_alloc lockN _ (lock_inv γ l R) with "[-]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iExists l. eauto.
  Qed.
  
  Lemma release_spec R lk γ :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}}
      release lk
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l) "[% #?]"; simplify_eq.
    wp_lam.
    iInv lockN as (b) "[Hl _]" "Hclose".
    wp_store. 
    iMod ("Hclose" with "[-HΦ]").
    { iNext. iExists false. by iFrame. }
    iApply "HΦ". auto.
  Qed.

  Lemma acquire_spec R lk γ :
    {{{ is_lock γ lk R }}}
      acquire lk
    {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hlock HΦ".
    iLöb as "IH".
    wp_lam.
    iDestruct "Hlock" as (l) "[% #?]". simplify_eq.
    wp_bind (CmpXchg _ _ _).
    iInv lockN as (b) "[Hl HR]" "Hclose".
    wp_cmpxchg as Heq | Hne.
    - assert (b = false) as ->. { destruct b; congruence. }
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iDestruct "HR" as "[Hlocked HR]".
      iModIntro. wp_pures.
      iApply ("HΦ" with "[$Hlocked $HR]").
    - assert (b = true) as ->. { destruct b; congruence. }
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. wp_pures.
      by iApply "IH".
  Qed.
End lockG_rules_wp.

Section lockG_rules_l.
  Context `{!lockG Σ, !relocGS Σ}.

  Lemma refines_newlock_l (R : iProp Σ) K t A :
    R -∗
    ▷(∀ (lk : loc) γ, is_lock γ #lk R
      -∗ (REL fill K (of_val #lk) << t: A)) -∗
    REL fill K (newlock #()) << t: A.
  Proof.
    iIntros "HR Hlog".
    rel_rec_l.
    rel_alloc_l l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc lockN _ (lock_inv γ l R) with "[-Hlog]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iApply "Hlog". iExists l. eauto.
  Qed.

  Lemma refines_release_l (R : iProp Σ) (lk : val) γ K t A :
    is_lock γ lk R -∗
    locked γ -∗
    R -∗
    ▷(REL fill K (#() : expr) << t : A) -∗
    REL fill K (release lk) << t: A.
  Proof.
    iIntros "Hlock Hlocked HR Hlog".
    iDestruct "Hlock" as (l) "[% #?]"; simplify_eq.
    rel_rec_l. rel_store_l_atomic.
    iInv lockN as (b) "[Hl _]" "Hclose".
    iModIntro. iExists _. iFrame.
    iNext. iIntros "Hl".
    iMod ("Hclose" with "[-Hlog]").
    { iNext. iExists false. by iFrame. }
    iApply "Hlog".
  Qed.

  Lemma refines_acquire_l (R : iProp Σ) (lk : val) γ K t A :
    is_lock γ lk R -∗
    ▷(locked γ -∗ R -∗ REL fill K (of_val #()) << t: A) -∗
    REL fill K (acquire lk) << t: A.
  Proof.
    iIntros "#Hlock Hlog".
    iLöb as "IH".
    rel_rec_l.
    iDestruct "Hlock" as (l) "[% #?]". simplify_eq.
    rel_cmpxchg_l_atomic.
    iInv lockN as (b) "[Hl HR]" "Hclose".
    iModIntro. iExists _. iFrame. simpl.
    iSplit.
    - iIntros (?). iNext. iIntros "Hl".
      assert (b = true) as ->. { destruct b; congruence. }
      rel_pures_l.
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      by iApply "IH".
    - iIntros (?). simplify_eq.
      iNext. iIntros "Hl".
      rel_pures_l.
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iDestruct "HR" as "[Hlocked HR]".
      iApply ("Hlog" with "Hlocked HR").
  Qed.

End lockG_rules_l.

Definition is_locked_r `{!cfgGS Σ} v (b : bool) :=
  (∃ lk : loc, ⌜v = #lk⌝ ∗ lk ↦ₛ #b)%I.

Section lock_rules_r.
  Context `{!relocGS Σ}.
  Variable (E : coPset).

  Lemma refines_newlock_r K t A
    (Hcl : nclose specN ⊆ E) :
    (∀ v, is_locked_r v false -∗ REL t << fill K (of_val v) @ E : A) -∗
    REL t << fill K (newlock #()) @ E : A.
  Proof.
    iIntros "Hlog".
    rel_rec_r.
    rel_alloc_r l as "Hl".
    iApply ("Hlog" with "[Hl]").
    iExists _. by iFrame.
  Qed.

  Lemma refines_acquire_r K v t A
    (Hcl : nclose specN ⊆ E) :
    is_locked_r v false -∗
    (is_locked_r v true -∗ REL t << fill K (of_val #()) @ E : A) -∗
    REL t << fill K (acquire v) @ E : A.
  Proof.
    iIntros "Hl Hlog".
    iDestruct "Hl" as (lk ->) "Hl".
    rel_rec_r.
    rel_cmpxchg_suc_r.
    rel_pures_r.
    iApply "Hlog". iExists _. by iFrame.
  Qed.

  Lemma refines_release_r K v t A st
    (Hcl : nclose specN ⊆ E) :
    is_locked_r v st -∗
    (is_locked_r v false -∗ REL t << fill K (of_val #()) @ E : A) -∗
    REL t << fill K (release v) @ E : A.
  Proof.
    iIntros "Hl Hlog".
    iDestruct "Hl" as (lk ->) "Hl".
    rel_rec_r.
    rel_store_r.
    iApply "Hlog". iExists _. by iFrame.
  Qed.

End lock_rules_r.

Opaque acquire release newlock.
