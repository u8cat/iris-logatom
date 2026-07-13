From iris.base_logic.lib Require Import mono_nat.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic Require Import linear encodable not_stuck_restrict.
From iris_logatom.program_logic Require Import atomic_sound atomic_complete.
From iris_logatom.heap_lang Require Import mgc lib.trace lib.nondet_int_prealloc.
From iris_logatom.heap_lang.rel_logic Require Import model properness adequacy rel_tactics spec_tactics.
From iris_logatom.heap_lang.typing Require Import contextual_refinement tychk.

Section mgc_of_trace_refines.
  Context `{!relocGS Σ}.

  Implicit Type t : list (positive * trace).

  Definition lrel_trace : lrel Σ :=
    LRel (λ v v', ⌜∃ t, v = encode_trace t ∧ v' = encode_trace t⌝)%I.

  Definition lrel_eq : lrel Σ :=
    LRel (λ v v', ⌜v = v'⌝)%I.

  Definition rel_trace (l : loc) : iProp Σ :=
    ∃ t, l ↦{#1/3} encode_trace t ∗ l ↦ₛ{#1/3} encode_trace t.
  Definition rel_nondet_bool_prealloc (l : loc) : iProp Σ :=
    ∃ b : bool, (l +ₗ 2) ↦ #b ∗ (l +ₗ 2) ↦ₛ #b.
  Definition rel_lock (l : loc) : iProp Σ :=
    ((l +ₗ 1) ↦ NONEV ∗ (l +ₗ 1) ↦ₛ NONEV ∗ (∃ t, l ↦{#2/3} (encode_trace t) ∗ l ↦ₛ{#2/3} (encode_trace t)))
    ∨ ((l +ₗ 1) ↦ SOMEV #() ∗ (l +ₗ 1) ↦ₛ SOMEV #()).

  Definition rel_trace_inv (l : loc) : iProp Σ :=
    inv trace.invN (rel_trace l) ∗
    inv trace.lockN (rel_lock l) ∗
    inv nondet_bool_prealloc_N (rel_nondet_bool_prealloc l).

  Lemma refines_trace_peak (l : loc) :
    rel_trace_inv l
    ⊢ REL trace_peak #l << trace_peak #l : lrel_trace.
  Proof.
    iIntros "(Htr & _)".
    rel_rec_l; rel_rec_r.
    rel_load_l_atomic.
    iInv trace.invN as (t) "(Hl & Hl')" "Hclose".
    iIntros "!#". iFrame. iIntros "!# Hl".
    rel_load_r.
    iMod ("Hclose" with "[$]") as "_".
    rel_values.
  Qed.

  Lemma refines_trace_acquire l j K :
    {{{ rel_trace_inv l ∗ refines_right j (fill K (trace.acquire #(l +ₗ 1))) }}}
       trace.acquire #(l +ₗ 1)
    {{{ t, RET #(); l ↦{#2/3} (encode_trace t) ∗ l ↦ₛ{#2/3} (encode_trace t) ∗ refines_right j (fill K #()) }}}.
  Proof.
    iIntros (Φ) "[(_ & #Hlock & _) Hj] HΦ".
    iLöb as "IH".
    wp_rec; tp_rec j.
    wp_rec; tp_rec j.
    wp_bind (CmpXchg _ _ _).
    iInv trace.lockN as "[>(Hl & Hl' & (%t & Htrace)) | >(Hl & Hl') ]" "Hclose".
    - wp_cmpxchg_suc. tp_cmpxchg_suc j.
      iMod ("Hclose" with "[Hl Hl']") as "_".
      { iModIntro. iRight. iFrame. }
      iModIntro.
      wp_pures. tp_pures j.
      iApply ("HΦ" with "[$Hj $Htrace]").
    - wp_cmpxchg_fail. tp_cmpxchg_fail j.
      iMod ("Hclose" with "[Hl Hl']") as "_".
      { iModIntro. iRight. iFrame. }
      iModIntro.
      wp_pures. tp_pures j.
      iApply ("IH" with "Hj HΦ").
  Qed.

  Lemma refines_trace_release l t :
    rel_trace_inv l -∗
    l ↦{#2 / 3} encode_trace t -∗
    l ↦ₛ{#2 / 3} encode_trace t -∗
    REL (trace.release #(l +ₗ 1)) << (trace.release #(l +ₗ 1)) : ().
  Proof.
    iIntros "(_ & #Hlock & _) Ht Ht'".
    rel_rec_l; rel_rec_r.
    rel_store_l_atomic.
    iInv trace.lockN as "[>(Hl & Hl' & (%t' & Htrace)) | >(Hl & Hl') ]" "Hclose".
    - iModIntro. iFrame. iModIntro. iIntros "Hl".
      rel_store_r. rel_values.
      iMod ("Hclose" with "[Hl Hl' Ht Ht']") as "_"; [|done].
      iLeft. iFrame.
    - iModIntro. iFrame. iModIntro. iIntros "Hl".
      rel_store_r. rel_values.
      iMod ("Hclose" with "[Hl Hl' Ht Ht']") as "_"; [|done].
      iLeft. iFrame.
  Qed.

  Definition lrel_pos : lrel Σ := LRel (λ v1 v2,
    ∃ (p : positive), ⌜v1 = #(Z.pos p)⌝ ∗ ⌜v2 = #(Z.pos p)⌝)%I.

  Lemma refines_nondet_bool_pralloc l :
    rel_trace_inv l
    ⊢ REL nondet_bool_prealloc #(l +ₗ 2) << nondet_bool_prealloc #(l +ₗ 2) : lrel_bool.
  Proof.
    iIntros "#(_ & _ & Hl)".
    rel_rec_l; rel_rec_r; rel_pures_l; rel_pures_r.
    rel_store_l_atomic.
    iInv nondet_bool_prealloc_N as (b) "[Hb Hb']" "Hclose".
    iModIntro. iFrame. iModIntro. iIntros "Hb".
    rel_store_r.
    iMod ("Hclose" with "[$]") as "_".
    rel_pures_l; rel_pures_r.
    rel_load_l_atomic.
    iInv nondet_bool_prealloc_N as (b') "[Hb Hb']" "Hclose".
    iModIntro. iFrame. iModIntro. iIntros "Hb".
    rel_load_r.
    iMod ("Hclose" with "[$]") as "_".
    rel_values.
  Qed.

  (* REL for the background thread.  Used by [mgc_of_trace_refines_adequacy_two]
    to pair the LHS bg thread with the RHS bg thread under the same
    relational invariant.  Never terminates, so the unit return is
    discharged by [iLöb]. *)
  (*************** Begin LLM-generated code. ****************)
  (*  Claude Opus 4.7 (1M context, xhigh effort, v2.1.111)  *)
  Lemma refines_nondet_bool_prealloc_bg l :
    rel_trace_inv l
    ⊢ REL nondet_bool_prealloc_bg #(l +ₗ 2) << nondet_bool_prealloc_bg #(l +ₗ 2) : ().
  Proof.
    iIntros "#(_ & _ & Hl)".
    iLöb as "IH".
    rel_rec_l; rel_rec_r.
    rel_store_l_atomic.
    iInv nondet_bool_prealloc_N as (b) "[Hb Hb']" "Hclose".
    iModIntro. iFrame. iModIntro. iIntros "Hb".
    rel_store_r.
    iMod ("Hclose" with "[$]") as "_".
    rel_pures_l; rel_pures_r.
    iApply "IH".
  Qed.
  (**************** End LLM-generated code. *****************)

  Definition lrel_nat : lrel Σ := LRel (λ v1 v2,
    ∃ (n : nat), ⌜v1 = #n⌝ ∗ ⌜v2 = #n⌝)%I.

  Lemma refines_nondet_nat_unbounded_prealloc l :
    rel_trace_inv l
    ⊢ REL nondet_nat_unbounded_prealloc #(l +ₗ 2) << nondet_nat_unbounded_prealloc #(l +ₗ 2) : lrel_nat.
  Proof.
    iIntros "#Htrace".
    iLöb as "IH".
    rel_rec_l; rel_rec_r; rel_pures_l; rel_pures_r.
    rel_bind_l (nondet_bool_prealloc _); rel_bind_r (nondet_bool_prealloc _).
    iApply refines_bind.
    { by iApply refines_nondet_bool_pralloc. }
    iIntros (?? (b & -> & ->)) "/=".
    destruct b; rel_pures_l; rel_pures_r.
    { rel_values. iModIntro. iExists 0. done. }
    rel_bind_l (nondet_nat_unbounded_prealloc _); rel_bind_r (nondet_nat_unbounded_prealloc _).
    iApply refines_bind; [done|].
    iIntros (?? (x&->&->)) "/=".
    rel_pures_l; rel_pures_r.
    rel_bind_l (nondet_bool_prealloc _); rel_bind_r (nondet_bool_prealloc _).
    iApply refines_bind.
    { by iApply refines_nondet_bool_pralloc. }
    iIntros (?? (b & -> & ->)) "/=".
    destruct b; rel_pures_l; rel_pures_r; rel_values; iModIntro.
    - iExists (1 + x * 2). rewrite !Nat2Z.inj_add !Nat2Z.inj_mul //.
    - iExists (0 + x * 2). rewrite !Nat2Z.inj_add !Nat2Z.inj_mul //.
  Qed.

  Lemma refines_nondet_bits_prealloc l :
    rel_trace_inv l
    ⊢ REL nondet_pos_unbounded_prealloc #(l +ₗ 2) << nondet_pos_unbounded_prealloc #(l +ₗ 2) : lrel_pos.
  Proof.
    iIntros "#Htrace".
    rel_rec_l; rel_rec_r; rel_pures_l; rel_pures_r.
    rel_bind_l (nondet_nat_unbounded_prealloc _); rel_bind_r (nondet_nat_unbounded_prealloc _).
    iApply refines_bind.
    { by iApply refines_nondet_nat_unbounded_prealloc. }
    iIntros (?? (b & -> & ->)) "/=".
    rel_pures_l; rel_pures_r.
    replace (1+b)%Z with (Z.pos (Z.to_pos (1+b))).
    rel_values. lia.
  Qed.

  Lemma refines_trace_is_fresh t p :
    ⊢ REL trace.is_fresh (encode_trace t) #(Z.pos p) << trace.is_fresh (encode_trace t) #(Z.pos p) : lrel_bool.
  Proof.
    induction t as [|[τ' x] t IH] using rev_ind; last rewrite encode_trace_snoc.
    - rel_rec_l; rel_rec_r; rel_pures_l; rel_pures_r. rel_values.
    - rel_rec_l; rel_rec_r; rel_pures_l; rel_pures_r.
      case_bool_decide as Hτ; rel_pures_l; rel_pures_r.
      { rel_values. }
      iApply refines_wand; [iApply IH|].
      auto.
  Qed.

  Lemma refines_trace_max_id t :
    ⊢ REL trace.max_id (encode_trace t) << trace.max_id (encode_trace t) : lrel_pos.
  Proof.
    induction t as [|[τ' x] t IH] using rev_ind; last rewrite encode_trace_snoc.
    - rel_rec_l; rel_rec_r; rel_pures_l; rel_pures_r. rel_values.
    - rel_rec_l; rel_rec_r; rel_pures_l; rel_pures_r.
      rel_bind_l (trace.max_id _); rel_bind_r (trace.max_id _).
      iApply refines_bind; [done|].
      iIntros (?? (?&->&->)) "/=".
      rel_rec_l; rel_rec_r; rel_pures_l; rel_pures_r.
      case_bool_decide; rel_pures_l; rel_pures_r; rel_values.
  Qed.

  Lemma refines_trace_fresh l v (a : trace) :
    decode_val v = Some a →
    rel_trace_inv l
    ⊢ REL trace_fresh #l v << trace_fresh #l v : lrel_pos.
  Proof.
    iIntros (->%encode_decode_val) "#(Ht & Hlock & Hb)".
    rel_rec_l; rel_rec_r.
    rel_pures_l; rel_pures_r.
    rel_bind_l (trace.acquire _); rel_bind_r (trace.acquire _).
    iApply refines_bind_unfold.
    iIntros (?) "Hj".
    iApply (refines_trace_acquire with "[$]").
    iModIntro. iIntros (t) "(Htr & Htr' & $) /=".
    rel_pures_l; rel_pures_r.
    rel_load_l; rel_load_r.
    rel_pures_l; rel_pures_r.
    rel_bind_l (nondet_pos_unbounded_prealloc _); rel_bind_r (nondet_pos_unbounded_prealloc _).
    iApply refines_bind.
    { iApply (refines_nondet_bits_prealloc with "[$]"). }
    iIntros (??) "(%p & -> & ->) /=".
    rel_pures_l; rel_pures_r.
    rel_bind_l (trace.is_fresh _ _); rel_bind_r (trace.is_fresh _ _).
    iApply refines_bind.
    { iApply refines_trace_is_fresh. }
    iIntros (?? (b &->&->)) "/=".
    destruct b; rel_pures_l; rel_pures_r.
    - rel_store_l_atomic.
      iInv trace.invN as (?) ">[Htr2 Htr2']" "Hclose".
      iModIntro.
      iDestruct (pointsto_agree with "Htr Htr2") as %<-.
      iCombine "Htr Htr2" as "Htr".
      iCombine "Htr' Htr2'" as "Htr'".
      assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
      iFrame.
      iIntros "!> Htr".
      rel_pures_l.
      rel_store_r.
      rel_pures_r.
      assert (2/3 + 1/3 = 1)%Qp as <- by compute_done.
      iDestruct "Htr" as "[Htr1 Htr2]".
      iDestruct "Htr'" as "[Htr1' Htr2']".
      rewrite -(encode_trace_snoc p a t).
      iMod ("Hclose" with "[$Htr2 $Htr2']") as "_".
      rel_bind_l (trace.release _); rel_bind_r (trace.release _).
      iApply (refines_bind with "[Htr1 Htr1']").
      { iApply (refines_trace_release with "[$] Htr1 Htr1'"). }
      iIntros (???) "/=".
      rel_pures_l; rel_pures_r.
      rel_values.
    - rel_bind_l (trace.max_id _); rel_bind_r (trace.max_id _).
      iApply refines_bind.
      { iApply refines_trace_max_id. }
      iIntros (?? (?&->&->)) "/=".
      rel_pures_l; rel_pures_r.
      rel_store_l_atomic.
      iInv trace.invN as (?) ">[Htr2 Htr2']" "Hclose".
      iModIntro.
      iDestruct (pointsto_agree with "Htr Htr2") as %<-.
      iCombine "Htr Htr2" as "Htr".
      iCombine "Htr' Htr2'" as "Htr'".
      assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
      iFrame.
      iIntros "!> Htr".
      rel_pures_l.
      rel_store_r.
      rel_pures_r.
      assert (2/3 + 1/3 = 1)%Qp as <- by compute_done.
      iDestruct "Htr" as "[Htr1 Htr2]".
      iDestruct "Htr'" as "[Htr1' Htr2']".
      rewrite -(encode_trace_snoc _ _ t).
      iMod ("Hclose" with "[$Htr2 $Htr2']") as "_".
      rel_bind_l (trace.release _); rel_bind_r (trace.release _).
      iApply (refines_bind with "[Htr1 Htr1']").
      { iApply (refines_trace_release with "[$] Htr1 Htr1'"). }
      iIntros (???) "/=".
      rel_pures_l; rel_pures_r.
      rel_values.
  Qed.

  Lemma refines_trace_emit l p (w : val) (a : trace) :
    decode_val w = Some a →
    rel_trace_inv l
    ⊢ REL trace_emit #l #(Z.pos p) w << trace_emit #l #(Z.pos p) w : ().
  Proof.
    iIntros (->%encode_decode_val) "#(Ht & Hlock & Hb)".
    rel_rec_l; rel_rec_r.
    rel_pures_l; rel_pures_r.
    rel_bind_l (trace.acquire _); rel_bind_r (trace.acquire _).
    iApply refines_bind_unfold.
    iIntros (?) "Hj".
    iApply (refines_trace_acquire with "[$]").
    iModIntro. iIntros (t) "(Htr & Htr' & $) /=".
    rel_pures_l; rel_pures_r.
    rel_load_l; rel_load_r.
    rel_pures_l; rel_pures_r.
    rel_store_l_atomic.
    iInv trace.invN as (?) ">[Htr2 Htr2']" "Hclose".
    iModIntro.
    iDestruct (pointsto_agree with "Htr Htr2") as %<-.
    iCombine "Htr Htr2" as "Htr".
    iCombine "Htr' Htr2'" as "Htr'".
    assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
    iFrame.
    iIntros "!> Htr".
    rel_pures_l.
    rel_store_r.
    rel_pures_r.
    assert (2/3 + 1/3 = 1)%Qp as <- by compute_done.
    iDestruct "Htr" as "[Htr1 Htr2]".
    iDestruct "Htr'" as "[Htr1' Htr2']".
    rewrite -(encode_trace_snoc _ _ t).
    iMod ("Hclose" with "[$Htr2 $Htr2']") as "_".
    iApply (refines_trace_release with "[$] Htr1 Htr1'").
  Qed.

  Context `{M : !model}.

  Definition lrel_req : lrel Σ :=
    LRel (λ v1 v2, ⌜v1 = v2⌝ ∗ ⌜valid_request v1⌝)%I.

  Lemma refines_op_mgc (A B : lrel Σ) (op op' obj obj' : expr) ts l :
    call_valid ts →
    □ (∀ b b', B b b' -∗ ⌜b = b'⌝) -∗
    (REL obj << obj' : A) -∗
    (REL op << op' : A → lrel_req → B) -∗
    rel_trace_inv l -∗
    REL mgc_of_trace l ts op obj << mgc_of_trace l ts op' obj' : lrel_trace.
  Proof.
    iIntros "%Hreq #HBeq Hobj Hop #Hinv".
    iApply (refines_app with "[Hop] Hobj").
    iApply (refines_app with "[] Hop").
    rel_values. iModIntro.
    iIntros (o o') "!# #Hop".
    rewrite /mgc_of_trace.
    rel_pures_l; rel_pures_r.
    rel_values. iModIntro.
    iIntros (a a') "!# #HA".
    iSpecialize ("Hop" with "HA").
    rel_pures_l; rel_pures_r.
    rewrite 2!concurrent_call_subst.
    iInduction ts as [|[τ [req| |]] ts IH] "IH"; simpl.
    - (* empty *)
      by iApply refines_trace_peak.
    - (* Call *)
      rewrite /concurrent_call.
      rel_bind_l (Fork _); rel_bind_r (Fork _).
      iApply refines_bind.
      + iApply refines_fork.
        rel_rec_l; rel_rec_r.
        rel_pures_l; rel_pures_r.
        rel_bind_l (trace_fresh _ _); rel_bind_r (trace_fresh _ _).
        iApply refines_bind.
        { by iApply refines_trace_fresh. }
        iIntros (?? (?&->&->)) "/=".
        rel_pures_l; rel_pures_r.
        rel_bind_l (o _ _); rel_bind_r (o' _ _).
        iApply refines_bind.
        { iApply refines_app; [done|]. rel_values.
          inversion Hreq; simplify_eq/=. eauto. }
        iIntros (??) "HB /=".
        rel_pures_l; rel_pures_r.
        iDestruct ("HBeq" with "HB") as %->.
        rel_bind_l (trace_emit _ _ _); rel_bind_r (trace_emit _ _ _).
        iApply refines_bind.
        { by iApply refines_trace_emit. }
        iIntros (?? [-> ->]) "/=".
        rel_pures_l. rel_pures_r.
        rel_values.
      + iIntros (??) "[-> ->] /=".
        rel_pures_l; rel_pures_r.
        iApply "IH". by inversion Hreq.
    - (* Lin *) iApply "IH"; by inversion Hreq.
    - (* Ret *) iApply "IH"; by inversion Hreq.
  Qed.

End mgc_of_trace_refines.

Lemma mgc_of_trace_refines_adequacy `{!relocPreG Σ} (M : model) (op op' obj obj' : expr) (A B : ∀ `{relocGS Σ}, lrel Σ) ts tracer σ :
  call_valid ts →
  (∀ `{!relocGS Σ} b b', B b b' -∗ ⌜b = b'⌝) →
  (∀ `{!relocGS Σ}, ⊢ REL obj << obj' : A) →
  (∀ `{!relocGS Σ}, ⊢ REL op << op' : A → lrel_req → B) →
  {[tracer; tracer +ₗ 1; tracer +ₗ 2]} ## dom (σ.(heap)) →
  adequate NotStuck (mgc_of_trace tracer ts op obj) (compose_state tracer σ [])
    (λ v _, ∃ thp' h v', rtc erased_step ([mgc_of_trace tracer ts op' obj'], (compose_state tracer σ [])) (of_val v' :: thp', h)
            ∧ (∃ (t : list (positive * trace)), v = encode_trace t ∧ v = v')).
Proof.
  intros Hvalid HB Hobj Hop Hdom.
  eapply (refines_adequate_strong Σ (λ _, lrel_trace) _ _ _ (compose_state tracer σ [])); [auto|].
  { iIntros (??? (?& -> & ->)). eauto. }
  iIntros (?) "Hpts Hpts'".
  rewrite /compose_state.
  iEval (rewrite big_sepM_union /=; [|set_solver]) in "Hpts".
  iDestruct "Hpts" as "[_ Hpts]".
  rewrite big_sepM_insert /=; last first.
  { apply lookup_insert_None. rewrite Loc.eq_spec /=. split; [|lia].
    apply lookup_insert_None. rewrite Loc.eq_spec /=. split; [done|lia]. }
  rewrite big_sepM_insert /=; last first.
  { apply lookup_insert_None. rewrite Loc.eq_spec /=. split; [done|lia]. }
  rewrite big_sepM_singleton /=.
  iDestruct "Hpts" as "(Htr & Hlock & Hbool)".
  assert (1 = (1/3) + (2/3))%Qp as Hsplit by compute_done.
  iEval (rewrite Hsplit) in "Htr".
  iDestruct "Htr" as "[Htr1 Htr2]".
  iEval (rewrite big_sepM_union /=; [|set_solver]) in "Hpts'".
  iDestruct "Hpts'" as "[_ Hpts']".
  rewrite big_sepM_insert /=; last first.
  { apply lookup_insert_None. rewrite Loc.eq_spec /=. split; [|lia].
    apply lookup_insert_None. rewrite Loc.eq_spec /=. split; [done|lia]. }
  rewrite big_sepM_insert /=; last first.
  { apply lookup_insert_None. rewrite Loc.eq_spec /=. split; [done|lia]. }
  rewrite big_sepM_singleton /=.
  iDestruct "Hpts'" as "(Htr' & Hlock' & Hbool')".
  iEval (rewrite Hsplit) in "Htr'".
  iDestruct "Htr'" as "[Htr1' Htr2']".

  iMod (inv_alloc trace.invN ⊤ (rel_trace tracer) with "[$Htr1 $Htr1']") as "Htrace".
  iMod (inv_alloc trace.lockN ⊤ (rel_lock tracer) with "[Hlock Hlock' Htr2 Htr2']") as "Hlock".
  { iLeft. iFrame. }
  iMod (inv_alloc nondet_bool_prealloc_N ⊤ (rel_nondet_bool_prealloc tracer) with "[$Hbool $Hbool']") as "Hbool".

  iApply (refines_op_mgc (A _) (B _)).
  - done.
  - iIntros "!#" (??) "H". by iApply HB.
  - iApply Hobj.
  - iApply Hop.
  - iFrame.
Qed.

(*************** Begin LLM-generated code. ****************)
(*  Claude Opus 4.7 (1M context, xhigh effort, v2.1.111)  *)
(* Two-thread variant of [mgc_of_trace_refines_adequacy].  The initial
  pool pairs the wrapped LHS expression with the fixed background
  thread, and the conclusion gives (i) an RHS-side derivation reaching
  the same encoded trace from the analogous 2-thread initial pool, and
  (ii) per-thread [not_stuck] for every reachable LHS thread. *)
Lemma mgc_of_trace_refines_adequacy_two `{!relocPreG Σ}
    (M : model) (op op' obj obj' : expr) (A B : ∀ `{relocGS Σ}, lrel Σ) ts (tracer : loc) σ
    (v : val) (thp : list expr) (σ' : state) :
  call_valid ts →
  (∀ `{!relocGS Σ} b b', B b b' -∗ ⌜b = b'⌝) →
  (∀ `{!relocGS Σ}, ⊢ REL obj << obj' : A) →
  (∀ `{!relocGS Σ}, ⊢ REL op << op' : A → lrel_req → B) →
  {[tracer; tracer +ₗ 1; tracer +ₗ 2]} ## dom (σ.(heap)) →
  rtc erased_step
    ([mgc_of_trace tracer ts op obj;
      nondet_bool_prealloc_bg #(tracer +ₗ 2)],
     compose_state tracer σ [])
    (Val v :: thp, σ') →
  (∃ thp_rhs h_rhs v_rhs,
      rtc erased_step
        ([mgc_of_trace tracer ts op' obj';
          nondet_bool_prealloc_bg #(tracer +ₗ 2)],
         compose_state tracer σ [])
        (Val v_rhs :: thp_rhs, h_rhs)
      ∧ ∃ (t : list (positive * trace)),
            v = encode_trace t ∧ v = v_rhs)
  ∧ (∀ e2, e2 ∈ Val v :: thp → not_stuck e2 σ').
Proof.
  intros Hvalid HB Hobj Hop Hdom [n [κs Hnsteps]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ heap_lang NotStuck); last exact Hnsteps.
  iIntros (Hinv).
  iMod (gen_heap_init (compose_state tracer σ []).(heap)) as (Hgh) "[Hh [Hls _]]".
  iMod (inv_heap_init loc (option val)) as (Hih) ">Hi".
  iMod (proph_map_init κs (compose_state tracer σ []).(used_proph_id)) as (Hpm) "Hp".
  iMod (mono_nat_own_alloc 0) as (γn) "[Hsteps_n _]".
  set (HheapGS := HeapGS HasLc Σ _ _ _ _ γn _).
  iMod (ghost_map_alloc (map_seq 0 [mgc_of_trace tracer ts op' obj';
                                    nondet_bool_prealloc_bg #(tracer +ₗ 2)]))
       as (γtp) "[Htp Hpts_tp]".
  iEval (cbn) in "Hpts_tp".
  iEval (rewrite big_sepM_insert; last by rewrite lookup_insert_ne)
        in "Hpts_tp".
  iEval (rewrite big_sepM_insert; last by rewrite lookup_empty)
        in "Hpts_tp".
  iEval (rewrite big_sepM_empty) in "Hpts_tp".
  iDestruct "Hpts_tp" as "[Hmain_pts [Hbg_pts _]]".
  iMod (ghost_map_alloc (compose_state tracer σ []).(heap))
       as (γst) "[Hσ_spec Hpts_spec]".
  iMod (prophS_alloc (compose_state tracer σ [])) as (γp) "Hps_spec".
  set (Hcfg := RelocGS _ _ (CFGGS _ _ _ _ γtp γst γp)).
  iMod (inv_alloc specN _
          (spec_inv ([mgc_of_trace tracer ts op' obj';
                      nondet_bool_prealloc_bg #(tracer +ₗ 2)],
                     compose_state tracer σ []))
        with "[Htp Hσ_spec Hps_spec]") as "#Hspec".
  { iNext. iExists _, _. iFrame "Htp Hσ_spec Hps_spec".
    iPureIntro. apply rtc_refl. }
  iAssert ([∗ map] l↦ov ∈ (compose_state tracer σ []).(heap),
              from_option (λ v, l ↦ v) True ov)%I with "[Hls]" as "Hpts_l".
  { iApply (big_sepM_mono with "Hls").
    iIntros (k [v_l|] Hk) "Hp /=";
      [rewrite primitive_laws.pointsto_unseal //|done]. }
  iAssert ([∗ map] l↦ov ∈ (compose_state tracer σ []).(heap),
              from_option (λ v, l ↦ₛ v) True ov)%I with "[Hpts_spec]" as "Hpts_r".
  { iApply (big_sepM_mono with "Hpts_spec").
    iIntros (k [v_r|] Hk) "Hp //=". }
  assert (Hne_t1 : tracer +ₗ 1 ≠ tracer).
  { intros Heq. apply (f_equal loc_car) in Heq. cbn in Heq. lia. }
  assert (Hne_t2 : tracer +ₗ 2 ≠ tracer).
  { intros Heq. apply (f_equal loc_car) in Heq. cbn in Heq. lia. }
  assert (Hne_t21 : tracer +ₗ 2 ≠ tracer +ₗ 1).
  { intros Heq. apply (f_equal loc_car) in Heq. cbn in Heq. lia. }
  rewrite /compose_state.
  iEval (rewrite big_sepM_union /=; [|set_solver]) in "Hpts_l".
  iDestruct "Hpts_l" as "[_ Hpts_l]".
  rewrite big_sepM_insert /=; last first.
  { apply lookup_insert_None. split; [|exact Hne_t1].
    apply lookup_insert_None. split; [apply lookup_empty|exact Hne_t2]. }
  rewrite big_sepM_insert /=; last first.
  { apply lookup_insert_None. split; [apply lookup_empty|exact Hne_t21]. }
  rewrite big_sepM_singleton /=.
  iDestruct "Hpts_l" as "(Htr & Hlock & Hbool)".
  assert (1 = (1/3) + (2/3))%Qp as Hsplit by compute_done.
  iEval (rewrite Hsplit) in "Htr".
  iDestruct "Htr" as "[Htr1 Htr2]".
  iEval (rewrite big_sepM_union /=; [|set_solver]) in "Hpts_r".
  iDestruct "Hpts_r" as "[_ Hpts_r]".
  rewrite big_sepM_insert /=; last first.
  { apply lookup_insert_None. split; [|exact Hne_t1].
    apply lookup_insert_None. split; [apply lookup_empty|exact Hne_t2]. }
  rewrite big_sepM_insert /=; last first.
  { apply lookup_insert_None. split; [apply lookup_empty|exact Hne_t21]. }
  rewrite big_sepM_singleton /=.
  iDestruct "Hpts_r" as "(Htr' & Hlock' & Hbool')".
  iEval (rewrite Hsplit) in "Htr'".
  iDestruct "Htr'" as "[Htr1' Htr2']".
  iMod (inv_alloc trace.invN ⊤ (rel_trace tracer)
          with "[Htr1 Htr1']") as "#Htrace_inv".
  { iNext. iExists []. iFrame. }
  iMod (inv_alloc trace.lockN ⊤ (rel_lock tracer)
          with "[Hlock Hlock' Htr2 Htr2']") as "#Hlock_inv".
  { iNext. iLeft. iFrame "Hlock Hlock'". iExists []. iFrame. }
  iMod (inv_alloc nondet_bool_prealloc_N ⊤ (rel_nondet_bool_prealloc tracer)
          with "[Hbool Hbool']") as "#Hbool_inv".
  { iNext. iExists false. iFrame. }
  iAssert (rel_trace_inv tracer) as "#Hrel_inv".
  { iFrame "Htrace_inv Hlock_inv Hbool_inv". }
  iAssert (REL mgc_of_trace tracer ts op obj
              << mgc_of_trace tracer ts op' obj' : lrel_trace)%I as "Hmain_rel".
  { iApply (refines_op_mgc (A _ ) (B _ )); [done| | | |iFrame "Hrel_inv"].
    - iIntros "!#" (??) "H". by iApply HB.
    - iApply Hobj.
    - iApply Hop. }
  iAssert (REL nondet_bool_prealloc_bg #(tracer +ₗ 2)
              << nondet_bool_prealloc_bg #(tracer +ₗ 2) : ())%I as "Hbg_rel".
  { iApply refines_nondet_bool_prealloc_bg. iFrame "Hrel_inv". }
  rewrite refines_eq /refines_def.
  iSpecialize ("Hmain_rel" $! (RefId 0 []) with "[Hmain_pts]").
  { rewrite /refines_right /=. iFrame "Hspec Hmain_pts". }
  iSpecialize ("Hbg_rel" $! (RefId 1 []) with "[Hbg_pts]").
  { rewrite /refines_right /=. iFrame "Hspec Hbg_pts". }
  iMod "Hmain_rel" as "Hwp_main".
  iMod "Hbg_rel" as "Hwp_bg".
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own γn 1 ns))%I.
  iExists [
    (λ vm, ∃ v', refines_right (RefId 0 []) (of_val v')
                 ∗ lrel_trace vm v')%I;
    (λ _, True)%I
  ], (λ _, True)%I, _.
  simpl. iFrame "Hh Hp Hsteps_n".
  iSplitL "Hwp_main Hwp_bg".
  { iFrame "Hwp_main". simpl. iSplitL; [|done].
    iApply (wp_mono with "Hwp_bg"). by iIntros (?) "_". }
  iIntros (es' t2' Heq Hlen Hns) "_ HΦs _".
  destruct es' as [|e_main_final [|e_bg_final [|? ?]]]; try by simpl in Hlen.
  simpl in Heq. injection Heq as Heq_emain Heq_es. subst e_main_final.
  iDestruct "HΦs" as "[Hφ_main [_ _]]".
  rewrite to_of_val. simpl.
  iDestruct "Hφ_main" as (v_rhs) "[Hj %Hlrel]".
  destruct Hlrel as (t & Hv_eq & Hv_rhs_eq).
  iInv specN as (tp σ_spec) ">(Hown & Hheap_spec & Hps_specI & %Hsteps_spec)" "Hclose".
  rewrite /refines_right /=.
  iDestruct "Hj" as "[_ Hj]".
  iDestruct (ghost_map_lookup with "Hown Hj") as %Htp_lookup.
  iMod ("Hclose" with "[Hown Hheap_spec Hps_specI]") as "_".
  { iNext. iExists tp, σ_spec. iFrame "Hown Hheap_spec Hps_specI". done. }
  iApply fupd_mask_intro_discard; [done|].
  iPureIntro.
  destruct tp as [|tp_head tp_tail]; first done.
  cbn in Htp_lookup.
  rewrite lookup_insert in Htp_lookup.
  injection Htp_lookup as Heq_head.
  subst tp_head.
  split.
  - exists tp_tail, σ_spec, v_rhs.
    split; [exact Hsteps_spec|].
    exists t. split; [exact Hv_eq|by rewrite Hv_eq Hv_rhs_eq].
  - intros e2 Hin. by apply (Hns _ ltac:(done)).
Qed.

(* [compose_state σ ts] is the same heap as [σ] extended with the
  three tracer cells at [tracer]; phrasing this as an [σ_ext] makes it
  directly usable with [not_stuck_heap_restrict]. *)
Local Lemma compose_state_is_σ_ext (tracer : loc) σ ts :
  composable_state tracer σ →
  compose_state tracer σ ts =
  state_upd_heap
    (λ h, heap_array tracer [encode_trace ts; NONEV; #false] ∪ h) σ.
Proof.
  intros Hcomp.
  assert (Hheap_arr :
    heap_array tracer [encode_trace ts; NONEV; #false] =
    {[tracer := Some (encode_trace ts);
      (tracer +ₗ 1) := Some NONEV;
      (tracer +ₗ 2) := Some #false]}).
  { simpl. rewrite (Loc.add_assoc tracer 1 1) /=.
    rewrite right_id_L. by rewrite -!insert_union_singleton_l. }
  rewrite /compose_state /trace_to_state Hheap_arr.
  rewrite /(union (A:=state)) /state_union /state_upd_heap /=.
  f_equal.
  - apply map_union_comm, map_disjoint_dom.
    rewrite /composable_state in Hcomp.
    rewrite !dom_insert_L dom_empty_L. set_solver.
  - apply right_id_L, _.
Qed.

(* [not_stuck] commutes with stripping a [fill] wrapper. *)
Local Lemma not_stuck_fill_inv (K : list ectx_item) (e : expr) σ :
  not_stuck (fill K e) σ → not_stuck e σ.
Proof.
  intros [[v Hv]|Hr].
  - apply to_val_fill_some in Hv as [-> ->]. left. by exists v.
  - destruct (to_val e) as [v|] eqn:Hv; first by left; exists v.
    right. by eapply (reducible_fill_inv (K := fill K)).
Qed.
(**************** End LLM-generated code. *****************)

Lemma refines_init_l_initializable `{!relocPreG Σ} (init : val) (e : expr) (A : ∀ `{relocGS Σ}, lrel Σ) :
  (∀ `{!relocGS Σ}, ⊢ REL init #() << e : A) →
  library_initializable init (λ _ _, True).
Proof.
  intros Hrel σ.
  eapply (refines_adequate Σ _ (λ _ _, True) _ _ σ) in Hrel; [|eauto].
  by eapply adequate_weaken.
Qed.

Lemma library_initializable_linearizable_refines `{!relocPreG Σ} (M : model) (A B : ∀ `{relocGS Σ}, lrel Σ)
  (init init' op op' : val) :
  (∀ σ, sequential (init #()) σ) →
  (∀ σ, sequential (init' #()) σ) →
  (∀ `{!relocGS Σ} b b', B b b' -∗ ⌜b = b'⌝) →
  library_initializable_linearizable init' op' →
  (∀ `{!relocGS Σ}, ⊢ REL init #() << init' #() : A) →
  (∀ `{!relocGS Σ}, ⊢ REL op << op' : A → lrel_req → B) →
  library_initializable_linearizable init op.
Proof.
  intros Hfree Hfree' HB [Hlin1 Hlin2] Hinit Hop.
  split.
  - intros ?. by eapply refines_init_l_initializable.
  - intros obj σ0 t σ cfg ts Hinit_steps Hobj.

    set (tracer := Loc.fresh (dom (heap (config_state cfg)))).
    assert (Htracer_disj: {[tracer; tracer+ₗ1; tracer+ₗ2]} ## dom (heap (config_state cfg))).
    { rewrite !disjoint_union_l !disjoint_singleton_l. split_and!.
      - rewrite -(Loc.add_0 tracer). eapply Loc.fresh_fresh. lia.
      - eapply Loc.fresh_fresh. lia.
      - eapply Loc.fresh_fresh. lia. }

    pose proof (Hfree _ _ _ Hinit_steps) as Heq_pool.
    destruct t; last by simpl in Heq_pool; lia.
    clear Heq_pool.
    (*************** Begin LLM-generated code. ****************)
    (*  Claude Opus 4.7 (1M context, xhigh effort, v2.1.111)  *)
    pose proof (mgc_match_adv_steps _ _ _ _ cfg ts tracer Htracer_disj Hobj)
      as Hsteps.
    assert (Hcall_valid : call_valid ts)
      by by eapply adv_steps_trace_valid_req.
    assert (Hcomposable : composable_state tracer σ).
    { destruct cfg => /=. by eapply adv_steps_composable_state. }
    assert (Hcomposable' : composable_state tracer σ0).
    { eapply erased_steps_composable_state;
        [apply inhabitant|apply inhabitant|done|done]. }

    (* Lift the source-level [init #()] derivation into compose_state. *)
    pose proof (simulate_erased_steps op valid_request tracer
                  [init #()] σ0 [Val obj] σ [] Hinit_steps Hcomposable)
      as Hinit_compose.
    (* Adjoin the bg thread on the right, matching the position used by
       [mgc_match_adv_steps]. *)
    apply (erased_steps_app_r [init #()] _ [Val obj] [] _
             [nondet_bool_prealloc_bg #(tracer +ₗ 2)] eq_refl)
      in Hinit_compose.
    simpl in Hinit_compose.
    (* Wrap the [init #()] call with the [mgc_of_trace tracer ts op _]
       outer context, so both endpoints have the [mgc_of_trace] shape. *)
    change (mgc_of_trace tracer ts op (init #()))
      with (fill [AppRCtx (mgc_of_trace tracer ts op)] (init #())) in *.
    change (mgc_of_trace tracer ts op (Val obj))
      with (fill [AppRCtx (mgc_of_trace tracer ts op)] (Val obj)) in *.
    apply (fill_erased_steps_head [AppRCtx (mgc_of_trace tracer ts op)]
             (init #()) _ (Val obj) _ [_] [_]) in Hinit_compose.
    (* Combine with [Hsteps] to get the full LHS run. *)
    assert (Hsteps_with_init :
      rtc erased_step
        ([fill [AppRCtx (mgc_of_trace tracer ts op)] (init #());
          nondet_bool_prealloc_bg #(tracer +ₗ 2)],
         compose_state tracer σ0 [])
        (Val (encode_trace ts) ::
           nondet_bool_prealloc_bg #(tracer +ₗ 2) ::
           (pending_to_simulated tracer <$> cfg.(config_pendingOp)) ++
           cfg.(config_childThread),
         compose_state tracer (config_state cfg) ts)).
    { etrans; [exact Hinit_compose|]. exact Hsteps. }
    clear Hinit_compose Hsteps.

    (* Apply the 2-thread refines adequacy. *)
    pose proof (mgc_of_trace_refines_adequacy_two M op op' (init #()) (init' #())
                  A B ts tracer σ0 (encode_trace ts) _ _
                  Hcall_valid HB Hinit Hop Hcomposable' Hsteps_with_init)
      as [(thp_rhs & h_rhs & v_rhs & Hres_rhs & t & Hv_eq & Hv_rhs_eq)
          Hthreads].
    assert (t = ts) as -> by by symmetry; apply (inj encode_trace).
    rewrite -Hv_rhs_eq in Hres_rhs.
    clear Hsteps_with_init Hv_eq Hv_rhs_eq v_rhs.

    (* Reverse-engineer the RHS source-level run. *)
    change (fill [AppRCtx (mgc_of_trace tracer ts op')] (init' #()))
      with (mgc_of_trace tracer ts op' (init' #())) in Hres_rhs.
    eapply adv_match_mgc_steps in Hres_rhs
      as (ts' & Heq_ts' & obj' & efs_rhs & σ_rhs & cfg' & Hinit_rhs & Hadv_rhs);
      [|exact Hfree'|exact Hlin1
       |by intros **; eapply Hlin2|done|done].
    apply (inj encode_trace) in Heq_ts' as <-.
    pose proof (Hfree' _ _ _ Hinit_rhs) as Heq_pool.
    destruct efs_rhs; last by simpl in Heq_pool; lia. clear Heq_pool.
    destruct (Hlin2 _ _ _ _ _ _ Hinit_rhs Hadv_rhs) as [Hns_cfg' Hlin_ts].
    split; last exact Hlin_ts.

    clear Hthreads Hns_cfg' Hinit_rhs Hadv_rhs cfg' obj' σ_rhs.

    (* Local helper: at every fresh location [l], the per-thread
       not_stuck guarantees of [mgc_of_trace_refines_adequacy_two]
       transfer back to [(config_state cfg)] via
       [not_stuck_heap_restrict]. *)
    assert (Hns_at_l :
      ∀ (l : loc),
        {[l; l +ₗ 1; l +ₗ 2]} ## dom (heap (config_state cfg)) →
        ∀ e2, e2 ∈ Val (encode_trace ts) ::
                    nondet_bool_prealloc_bg #(l +ₗ 2) ::
                    (pending_to_simulated l <$> cfg.(config_pendingOp)) ++
                    cfg.(config_childThread) →
          not_stuck e2 (compose_state l (config_state cfg) ts)).
    { intros l Hl_disj e2 Hin.
      assert (Hcomp_l : composable_state l σ).
      { destruct cfg => /=. by eapply adv_steps_composable_state. }
      assert (Hcomp_l0 : composable_state l σ0).
      { eapply erased_steps_composable_state;
          [apply inhabitant|apply inhabitant|done|done]. }
      pose proof (mgc_match_adv_steps _ _ _ _ cfg ts l Hl_disj Hobj)
        as Hsteps_l.
      pose proof (simulate_erased_steps op valid_request l
                    [init #()] σ0 [Val obj] σ [] Hinit_steps Hcomp_l)
        as Hinit_compose_l.
      apply (erased_steps_app_r [init #()] _ [Val obj] [] _
               [nondet_bool_prealloc_bg #(l +ₗ 2)] eq_refl)
        in Hinit_compose_l.
      simpl in Hinit_compose_l.
      change (mgc_of_trace l ts op (init #()))
        with (fill [AppRCtx (mgc_of_trace l ts op)] (init #())) in *.
      change (mgc_of_trace l ts op (Val obj))
        with (fill [AppRCtx (mgc_of_trace l ts op)] (Val obj)) in *.
      apply (fill_erased_steps_head [AppRCtx (mgc_of_trace l ts op)]
               (init #()) _ (Val obj) _ [_] [_]) in Hinit_compose_l.
      assert (Hsteps_full :
        rtc erased_step
          ([fill [AppRCtx (mgc_of_trace l ts op)] (init #());
            nondet_bool_prealloc_bg #(l +ₗ 2)],
           compose_state l σ0 [])
          (Val (encode_trace ts) ::
             nondet_bool_prealloc_bg #(l +ₗ 2) ::
             (pending_to_simulated l <$> cfg.(config_pendingOp)) ++
             cfg.(config_childThread),
           compose_state l (config_state cfg) ts)).
      { etrans; [exact Hinit_compose_l|]. exact Hsteps_l. }
      pose proof (mgc_of_trace_refines_adequacy_two M op op'
                    (init #()) (init' #()) A B ts l σ0
                    (encode_trace ts) _ _
                    Hcall_valid HB Hinit Hop Hcomp_l0 Hsteps_full)
        as [_ Hthreads_l].
      by apply Hthreads_l. }

    (* Helper to convert per-l fresh-disjointness from
       [not_stuck_heap_restrict]'s premise into the form expected by
       [Hns_at_l]. *)
    assert (Hdisj_of_fresh :
      ∀ l, (∀ i : nat, i < 3 → l +ₗ i ∉ dom (heap (config_state cfg))) →
           {[l; l +ₗ 1; l +ₗ 2]} ## dom (heap (config_state cfg))).
    { intros l Hl_fresh.
      pose proof (Hl_fresh 0 ltac:(lia)) as Hl0.
      pose proof (Hl_fresh 1 ltac:(lia)) as Hl1.
      pose proof (Hl_fresh 2 ltac:(lia)) as Hl2.
      change (l +ₗ 0%nat) with (l +ₗ 0%Z) in Hl0.
      change (l +ₗ 1%nat) with (l +ₗ 1%Z) in Hl1.
      change (l +ₗ 2%nat) with (l +ₗ 2%Z) in Hl2.
      rewrite Loc.add_0 in Hl0.
      set_solver. }

    split.
    + apply Forall_forall. intros [τ [e_p|]] Hin_pending; last done.
      apply (not_stuck_heap_restrict _ _ 3).
      intros l Hl_fresh.
      pose proof (Hdisj_of_fresh l Hl_fresh) as Hl_disj.
      pose proof (compose_state_is_σ_ext l (config_state cfg) ts
                    (Hdisj_of_fresh l Hl_fresh)) as Heq_compose.
      exists [encode_trace ts; NONEV; #false].
      split; first reflexivity.
      rewrite -Heq_compose.
      apply (not_stuck_fill_inv (simulatedOp_pending_ctx l τ)).
      apply (Hns_at_l _ Hl_disj).
      rewrite elem_of_cons. right.
      rewrite elem_of_cons. right.
      rewrite !elem_of_app. left.
      by apply (list_elem_of_fmap_2
                 (pending_to_simulated l) _ (τ, Some e_p)).
    + apply Forall_forall. intros e_child Hin_child.
      apply (not_stuck_heap_restrict _ _ 3).
      intros l Hl_fresh.
      pose proof (Hdisj_of_fresh l Hl_fresh) as Hl_disj.
      pose proof (compose_state_is_σ_ext l (config_state cfg) ts
                    (Hdisj_of_fresh l Hl_fresh)) as Heq_compose.
      exists [encode_trace ts; NONEV; #false].
      split; first reflexivity.
      rewrite -Heq_compose.
      apply (Hns_at_l _ Hl_disj).
      rewrite elem_of_cons. right.
      rewrite elem_of_cons. right.
      rewrite !elem_of_app. by right.
    (**************** End LLM-generated code. *****************)
Qed.

Theorem logatom_refines (M : model) `{!relocPreG Σ, !linearizabilityG Σ, !logicatomicityG Σ, !traceG Σ} (A B : ∀ `{relocGS Σ}, lrel Σ)
  (init init' op op' : val) N
  (is_P' : heapGS Σ → gname → val → iProp Σ) (P_state' : heapGS Σ → gname → S → iProp Σ)
  `{!∀ H γ v, Persistent (is_P' H γ v)} `{!∀ H γ s, Timeless (P_state' H γ s)} :
  (∀ σ, sequential (init #()) σ) →
  (∀ σ, sequential (init' #()) σ) →
  N ## traceN →
  (∀ `{!relocGS Σ} b b', B b b' -∗ ⌜b = b'⌝) →
  (* logatom of (init',op') *)
  (∀ `(!heapGS Σ), {{{ True }}} init' #() {{{ γ r, RET r; is_P' _ γ r ∗ P_state' _ γ s_init }}}) →
    (∀ `(!heapGS Σ) γ (x y: val), valid_request y → is_P' _ γ x ⊢
      <<{ ∀∀ s, P_state' _ γ s }>>
        op' x y @ ↑N
      <<{ ∃∃ s' y', P_state' _ γ s' ∗ ⌜request_response s y s' y'⌝ | RET y' }>>) →
  (* refinement *)
  (∀ `{!relocGS Σ}, ⊢ REL init #() << init' #() : A) →
  (∀ `{!relocGS Σ}, ⊢ REL op << op' : A → lrel_req → B) →
  (* logatom of (init,op) *)
  ∀ `{!heapGS Σ}, ({{{ True }}} wrap_init init #() {{{ γ r, RET r; is_P op γ r ∗ P_state γ s_init }}})
  ∧
  (∀ γ (x y: val), valid_request y → is_P op γ x ⊢
    <<{ ∀∀ s, P_state γ s }>>
      wrap_op op x y @ ↑Nlogatom
    <<{ ∃∃ s' y', P_state γ s' ∗ ⌜request_response s y s' y'⌝ | RET y' }>>).
Proof.
  intros Hnf Hnf' HN HB Hinit'_spec Hop'_spec Hinit_refine Hop_refine ?.
  apply logatom_complete; first done.
  eapply library_initializable_linearizable_refines; try eassumption.
  eapply (logatom_sound (Σ:=Σ)); try eassumption.
Qed.

Corollary logatom_refines_init (M : model) `{!relocPreG Σ, !linearizabilityG Σ, !logicatomicityG Σ, !traceG Σ} (A B : ∀ `{relocGS Σ}, lrel Σ)
  (init init' op op' : val) N
  (is_P' : heapGS Σ → gname → val → iProp Σ) (P_state' : heapGS Σ → gname → S → iProp Σ)
  `{!∀ H γ v, Persistent (is_P' H γ v)} `{!∀ H γ s, Timeless (P_state' H γ s)} :
  (∀ σ, sequential (init #()) σ) →
  (∀ σ, sequential (init' #()) σ) →
  N ## traceN →
  (∀ `{!relocGS Σ} b b', B b b' -∗ ⌜b = b'⌝) →
  (* logatom of (init',op') *)
  (∀ `(!heapGS Σ), {{{ True }}} init' #() {{{ γ r, RET r; is_P' _ γ r ∗ P_state' _ γ s_init }}}) →
    (∀ `(!heapGS Σ) γ (x y: val), valid_request y → is_P' _ γ x ⊢
      <<{ ∀∀ s, P_state' _ γ s }>>
        op' x y @ ↑N
      <<{ ∃∃ s' y', P_state' _ γ s' ∗ ⌜request_response s y s' y'⌝ | RET y' }>>) →
  (* refinement *)
  (∀ `{!relocGS Σ}, ⊢ REL init #() << init' #() : A) →
  (∀ `{!relocGS Σ}, ⊢ REL op << op' : A → lrel_req → B) →
  (* logatom of (init,op) *)
  ∀ `{!heapGS Σ}, ({{{ True }}} wrap_init init #() {{{ γ r, RET r; is_P op γ r ∗ P_state γ s_init }}}).
Proof.
  intros Hnf Hnf' HN HB Hinit'_spec Hop'_spec Hinit_refine Hop_refine Hheap.
  eapply proj1.
  revert Hnf Hnf' HN HB Hinit'_spec Hop'_spec Hinit_refine Hop_refine Hheap.
  apply logatom_refines; eassumption.
Qed.

Corollary logatom_refines_op (M : model) `{!relocPreG Σ, !linearizabilityG Σ, !logicatomicityG Σ, !traceG Σ} (A B : ∀ `{relocGS Σ}, lrel Σ)
  (init init' op op' : val) N
  (is_P' : heapGS Σ → gname → val → iProp Σ) (P_state' : heapGS Σ → gname → S → iProp Σ)
  `{!∀ H γ v, Persistent (is_P' H γ v)} `{!∀ H γ s, Timeless (P_state' H γ s)} :
  (∀ σ, sequential (init #()) σ) →
  (∀ σ, sequential (init' #()) σ) →
  N ## traceN →
  (∀ `{!relocGS Σ} b b', B b b' -∗ ⌜b = b'⌝) →
  (* logatom of (init',op') *)
  (∀ `(!heapGS Σ), {{{ True }}} init' #() {{{ γ r, RET r; is_P' _ γ r ∗ P_state' _ γ s_init }}}) →
    (∀ `(!heapGS Σ) γ (x y: val), valid_request y → is_P' _ γ x ⊢
      <<{ ∀∀ s, P_state' _ γ s }>>
        op' x y @ ↑N
      <<{ ∃∃ s' y', P_state' _ γ s' ∗ ⌜request_response s y s' y'⌝ | RET y' }>>) →
  (* refinement *)
  (∀ `{!relocGS Σ}, ⊢ REL init #() << init' #() : A) →
  (∀ `{!relocGS Σ}, ⊢ REL op << op' : A → lrel_req → B) →
  (* logatom of (init,op) *)
  ∀ `{!heapGS Σ},
  (∀ γ (x y: val), valid_request y → is_P op γ x ⊢
    <<{ ∀∀ s, P_state γ s }>>
      wrap_op op x y @ ↑Nlogatom
    <<{ ∃∃ s' y', P_state γ s' ∗ ⌜request_response s y s' y'⌝ | RET y' }>>).
Proof.
  intros Hnf Hnf' HN HB Hinit'_spec Hop'_spec Hinit_refine Hop_refine Hheap.
  eapply proj2.
  revert Hnf Hnf' HN HB Hinit'_spec Hop'_spec Hinit_refine Hop_refine Hheap.
  apply logatom_refines; eassumption.
Qed.
