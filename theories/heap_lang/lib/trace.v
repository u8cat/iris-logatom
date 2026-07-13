From iris_logatom.lib Require Import list.
From iris.algebra Require Import mono_list.
From iris.base_logic Require Import invariants mono_nat ghost_map.
From iris_logatom.lib Require Import proph_map.
From iris.program_logic Require Export atomic.
From iris_logatom.pure_logic Require Import state_set steps step_laws encodable tactics.
From iris.heap_lang Require Import adequacy.
From iris.heap_lang Require Export primitive_laws notation proofmode.
From iris.heap_lang.lib Require Import arith.
From iris_logatom.heap_lang.lib Require Import nondet_int_prealloc.

Section encode.
  Context `{!Encodable A}.
(* A trace is reprented as a reversed list. *)
Local Fixpoint encode_trace_aux TS (ts : list (positive*A)) :=
  match ts with
  | [] => TS
  | (τ,v)::ts => encode_trace_aux (SOMEV (#(Z.pos τ),encode_val v,TS)) ts
  end.

Definition encode_trace := encode_trace_aux NONEV.

Local Lemma encode_trace_aux_snoc TS τ v ts :
  encode_trace_aux TS (ts++[(τ,v)]) = SOMEV (#(Z.pos τ), encode_val v, encode_trace_aux TS ts).
Proof.
  revert TS.
  induction ts as [|[τ₀ v₀] ts IH] => TS; first reflexivity.
  rewrite -app_comm_cons. simpl.
  rewrite IH. done.
Qed.

Lemma encode_trace_snoc τ v ts :
  encode_trace (ts++[(τ,v)]) = SOMEV (#(Z.pos τ), encode_val v, encode_trace ts).
Proof. apply encode_trace_aux_snoc. Qed.

(**********************************************************)
(* Begin LLM-generated code. *)
(* tool: Claude Code 2.1.81
   model: Claude Opus 4.6 with 1M context (claude-opus-4-6)
   parameters:
      effort = high
      context window = 1000000
      max output tokens = 128000 *)
(* The type of [encode_trace_inj] is written by human, other
  code are LLM-generated. *)
Local Lemma encode_trace_aux_ne_NONEV TS ts :
  TS ≠ NONEV → encode_trace_aux TS ts ≠ NONEV.
Proof.
  revert TS. induction ts as [|[τ₀ v₀] ts IH] => TS HTS; first done.
  simpl. apply IH. done.
Qed.

Local Lemma encode_trace_SOMEV_inv ts τ v inner :
  encode_trace ts = SOMEV (#(Z.pos τ), encode_val v, inner) →
  ∃ ts', ts = ts' ++ [(τ, v)] ∧ inner = encode_trace ts'.
Proof.
  induction ts as [|[τ₀ v₀] ts _] using rev_ind; first done.
  rewrite encode_trace_snoc. intros Heq. simplify_eq.
  by exists ts.
Qed.

Global Instance encode_trace_inj : Inj (=) (=) encode_trace.
Proof.
  intros t1. induction t1 as [|[τ₁ v₁] t1 IH] using rev_ind.
  - intros t2 Heq. destruct t2 as [|[τ₀ v₀] t2]; first done.
    exfalso. rewrite /encode_trace /= in Heq.
    symmetry in Heq. revert Heq. apply encode_trace_aux_ne_NONEV. done.
  - intros t2 Heq. rewrite encode_trace_snoc in Heq. symmetry in Heq.
    destruct (encode_trace_SOMEV_inv _ _ _ _ Heq) as (t2' & -> & Heq').
    rewrite (IH _ Heq'). done.
Qed.
(* End LLM-generated code. *)
(**********************************************************)
End encode.

(* A lightweight spin lock. *)
(* Uses NONE for unlock and SOME for locked because we want to initialize the lock by AllocN. *)
Local Definition try_acquire : val := λ: "l", CAS "l" NONEV (SOMEV #()).
Local Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Local Definition release : val := λ: "l", "l" <- NONEV.

Local Definition is_fresh : val := rec: "is_fresh" "t" "id" :=
  match: "t" with
    NONE => #true
  | SOME "x" =>
    let: "τ" := Fst (Fst "x") in
    let: "t" := Snd "x" in
    ("τ" ≠ "id") && "is_fresh" "t" "id"
  end.

Local Definition max_id : val := rec: "max_id" "t" :=
  match: "t" with
    NONE => #1
  | SOME "x" =>
    let: "τ" := Fst (Fst "x") in
    let: "t" := Snd "x" in
    maximum "τ" ("max_id" "t")
  end.

Definition new_trace : val := λ: <>,
  let: "l" := AllocN #3 NONEV in
  "l" +ₗ #2 <- #false;;
  let: "l2" := "l" +ₗ #2 in
  Fork (nondet_bool_prealloc_bg "l2");;
  "l".

Definition trace_emit : val := λ: "l" "τ" "v",
  acquire ("l" +ₗ #1);;
  "l" <- SOME ("τ", "v", !"l");;
  release ("l" +ₗ #1).

Definition trace_fresh : val := λ: "l" "v",
  acquire ("l" +ₗ #1);;
  let: "t" := !"l" in
  let: "τ" := nondet_pos_unbounded_prealloc ("l" +ₗ #2) in
  if: is_fresh "t" "τ" then
    "l" <- SOME ("τ", "v", "t");;
    release ("l" +ₗ #1);;
    "τ"
  else
    let: "τ" := max_id "t" + #1 in
    "l" <- SOME ("τ", "v", "t");;
    release ("l" +ₗ #1);;
    "τ".

Definition trace_peak : val := λ: "l", !"l".

Class traceG Σ := TraceG {
  #[local] traceG_inG :: inG Σ (mono_listR (prodO positiveO valO));
}.
Definition traceΣ  := #[GFunctor (mono_listR (prodO positiveO valO))].
Global Instance subG_traceG Σ : subG traceΣ Σ → traceG Σ.
Proof. solve_inG. Qed.

Section def.
  Context `{!heapGS Σ, !traceG Σ}.
  Definition traceN := nroot .@ "iris_logatom.heap_lang.lib.trace".
  Local Definition metaN := traceN .@ "meta".
  Local Definition invN := traceN .@ "inv".
  Local Definition lockN := traceN .@ "lock".
  Context `{!Encodable A}.

  Local Definition encode_trace_A (t : positive * A) : positive * val :=
    (t.1, encode_val t.2).

  Local Definition decode_trace_A (t : positive * val) : option (positive * A) :=
    a ← decode_val t.2; mret (t.1,a).

  Local Lemma decode_encode_trace_A t : decode_trace_A (encode_trace_A t) = Some t.
  Proof.
    destruct t. rewrite /encode_trace_A /decode_trace_A /=.
    rewrite decode_encode_val. reflexivity.
  Qed.

  Local Lemma decode_encode_trace_A_fmap (ts : list (positive*A)) :
    omap decode_trace_A (encode_trace_A <$> ts) = ts.
  Proof.
    induction ts as [|t ts IH]; first reflexivity.
    rewrite fmap_cons omap_cons decode_encode_trace_A IH.
    reflexivity.
  Qed.

  Local Instance encode_trace_A_inj : Inj (=) (=) encode_trace_A.
  Proof.
    rewrite /encode_trace_A.
    intros [] [] Heq. simpl in Heq.
    injection Heq as -> ->%(inj encode_val).
    done.
  Qed.

  Local Instance encode_trace_A_fmap_inj : Inj (=) (=) (fmap (M:=list) encode_trace_A).
  Proof.
    intros ts1. induction ts1 as [|t1 ts1 IH] => ts2 Heq.
    - simpl in Heq. symmetry. eapply fmap_nil_inv. done.
    - destruct ts2 as [|t2 ts2].
      { rewrite fmap_nil in Heq. apply fmap_nil_inv in Heq. discriminate Heq. }
      rewrite !fmap_cons in Heq.
      (* TODO: how to prevent injection from destructing t1 and t2? *)
      injection Heq as Heq1 Heq2%(inj encode_val) Heq3%IH.
      destruct t1, t2. simpl in Heq1,Heq2. subst. done.
  Qed.

  Definition hist_def (l : loc) (t : list (positive*A)) : iProp Σ :=
    ∃ γ : gname, meta l metaN γ ∗ own γ (◯ML (encode_trace_A<$>t)).
  Definition hist_aux : seal hist_def. Proof. by eexists. Qed.
  Definition hist := hist_aux.(unseal).
  Definition hist_unseal : hist = hist_def := hist_aux.(seal_eq).

  Definition trace_is_def (l : loc) (t : list (positive*A)) : iProp Σ :=
    ∃ γ : gname, meta l metaN γ ∗ own γ (●ML{#1/3} (encode_trace_A<$>t)).
  Definition trace_is_aux : seal trace_is_def. Proof. by eexists. Qed.
  Definition trace_is := trace_is_aux.(unseal).
  Definition trace_is_unseal : trace_is = trace_is_def := trace_is_aux.(seal_eq).

  (* Rinv owns l so as to [extract I (heap σ !! l)] by adequacy  *)
  Local Definition Rinv (l : loc) (I : list (positive*A) → Prop) : iProp Σ :=
    ∃ t, l ↦{#1/3} (encode_trace t) ∗ trace_is_def l t ∗ ⌜I t⌝.
  (* Rlock owns more than half of l to derive contradition in release_spec *)
  Local Definition Rlock (l : loc) : iProp Σ :=
    (l +ₗ 1) ↦ NONEV ∗ ((∃ t, l ↦{#2/3} (encode_trace t) ∗ trace_is_def l t)) ∨ (l +ₗ 1) ↦ SOMEV #().

  Definition trace_inv_def (l : loc) (I : list (positive*A) → Prop) : iProp Σ :=
    inv invN (Rinv l I) ∗ inv lockN (Rlock l) ∗ nondet_bool_prealloc_inv (l +ₗ 2).
  Definition trace_inv_aux : seal trace_inv_def. Proof. by eexists. Qed.
  Definition trace_inv := trace_inv_aux.(unseal).
  Definition trace_inv_unseal : trace_inv = trace_inv_def := trace_inv_aux.(seal_eq).

  Global Instance hist_persistent l t : Persistent (hist l t).
  Proof. rewrite hist_unseal /hist_def. apply _. Qed.
  Global Instance trace_inv_persistent l I : Persistent (trace_inv l I).
  Proof. rewrite trace_inv_unseal /trace_inv_def. apply _. Qed.

  Global Instance trace_is_timeless l t : Timeless (trace_is l t).
  Proof. rewrite trace_is_unseal /trace_is_def. apply _. Qed.
  Global Instance hist_timeless l t : Timeless (hist l t).
  Proof. rewrite hist_unseal /hist_def. apply _. Qed.

  Lemma alloc_hist l t: trace_is l t ⊢ trace_is l t ∗ hist l t.
  Proof.
    rewrite hist_unseal /hist_def trace_is_unseal /trace_is_def.
    iDestruct 1 as (γ) "[#Hmeta H●]".
    iEval (rewrite mono_list_auth_lb_op) in "H●".
    iDestruct "H●" as "[$ $]".
    iFrame "Hmeta".
  Qed.

  Lemma hist_trace_is_prefix l t h :
    trace_is l t -∗ hist l h -∗ ⌜h `prefix_of` t⌝.
  Proof.
    rewrite hist_unseal /hist_def trace_is_unseal /trace_is_def.
    iDestruct 1 as (γ) "[#Hmeta H●]".
    iDestruct 1 as (γ') "[#Hmeta' H◯]".
    iDestruct (meta_agree with "Hmeta Hmeta'") as %<-.
    iDestruct (own_valid_2 with "H● H◯") as %[_ Hprefix]%mono_list_both_dfrac_valid_L.
    iPureIntro.
    destruct Hprefix as [tail Heq].
    apply (f_equal (omap decode_trace_A)) in Heq.
    rewrite omap_app !decode_encode_trace_A_fmap in Heq.
    eexists. done.
  Qed.

  Lemma trace_is_inv l t I :
    trace_inv l I -∗ trace_is l t ={⊤}=∗ trace_is l t ∗ ⌜I t⌝.
  Proof.
    rewrite trace_inv_unseal /trace_inv_def trace_is_unseal /trace_is_def.
    iIntros "#[Hi _] (%γ & #Hmeta & H●)".
    iInv invN as (t') ">(Hl' & (%γ' & #Hmeta' & H●') & %HI)" "Hclose".
    iDestruct (meta_agree with "Hmeta Hmeta'") as %<-.
    iDestruct (own_valid_2 with "H● H●'") as %[_ <-%(inj (fmap encode_trace_A))]%mono_list_auth_dfrac_op_valid_L.
    iMod ("Hclose" with "[$Hl' $Hmeta' $H●' //]") as "_". iModIntro.
    by iFrame "Hmeta H●".
  Qed.

  Local Lemma dfrac_3third : (1 / 3 + (1 / 3 + 1 / 3))%Qp = 1%Qp.
  Proof. compute_done. Qed.

  Local Lemma dfrac_2third_1third : (2 / 3 + 1 / 3)%Qp = 1%Qp.
  Proof. compute_done. Qed.
End def.

Local Existing Instances encode_trace_A_inj encode_trace_A_fmap_inj.

Section spec.
  Context `{!heapGS Σ, !traceG Σ, !Encodable A}.

  Local Lemma is_fresh_spec t τ :
    {{{ True }}}
      is_fresh (encode_trace (A:=A) t) #(Z.pos τ)
    {{{ (b : bool), RET #b; ⌜b → τ ∉ t.*1⌝ }}}.
  Proof.
    induction t as [|[τ' x] t IH] using rev_ind; last rewrite encode_trace_snoc;
      iIntros (Φ) "_ HΦ"; wp_rec; wp_pures.
    { iApply "HΦ". iPureIntro. intros _. set_solver. }
    case_bool_decide as Hτ; wp_pures.
    { iApply "HΦ". iPureIntro. done. }
    wp_apply (IH with "[//]") as (b Hisfresh) "".
    iApply "HΦ". iPureIntro. intros b'. specialize (Hisfresh b').
    set_solver.
  Qed.

  Local Lemma max_id_spec t :
    {{{ True }}}
      max_id (encode_trace (A:=A) t)
    {{{ (τ : positive), RET #(Z.pos τ); ⌜Forall (λ x, x ≤ τ)%positive t.*1⌝ }}}.
  Proof.
    induction t as [|[τ x] t IH] using rev_ind; last rewrite encode_trace_snoc;
      iIntros (Φ) "_ HΦ"; wp_rec; wp_pures; first by iApply "HΦ".
    wp_apply (IH with "[//]") as (τ_max Hmax) "".
    wp_apply maximum_spec.
    replace (Z.pos τ `max` Z.pos τ_max)%Z with (Z.pos (τ `max` τ_max)) by lia.
    iApply "HΦ". iPureIntro.
    rewrite fmap_snoc Forall_app Forall_cons Forall_nil right_id.
    split; last (simpl; lia).
    apply (Forall_impl _ _ t.*1 Hmax) => ??. lia.
  Qed.

  Local Lemma try_acquire_spec l :
    {{{ inv lockN (Rlock (A:=A) l) }}} try_acquire #(l+ₗ1)
    {{{ (b : bool), RET #b; if b then (∃ t, l ↦{#2/3} (encode_trace (A:=A) t) ∗ trace_is_def (A:=A) l t) else True }}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ".
    wp_lam. wp_bind (CmpXchg _ _ _). iInv lockN as "[[Hl HR] | Hl]".
    - wp_cmpxchg_suc. iModIntro. iSplitL "Hl". { iNext. iRight. done. }
      wp_pures. by iApply ("HΦ" $! true with "HR").
    - wp_cmpxchg_fail. iModIntro. iSplitL "Hl". { iNext. iRight. done. }
      wp_pures. by iApply ("HΦ" $! false with "[//]").
  Qed.

  Local Lemma acquire_spec l :
    {{{ inv lockN (Rlock (A:=A) l) }}} acquire #(l+ₗ1)
    {{{ t, RET #(); l ↦{#2/3} (encode_trace (A:=A)t) ∗ trace_is_def (A:=A) l t }}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hinv") as ([]) "H"; wp_pures.
    - iDestruct "H" as (t) "H". by iApply "HΦ".
    - iApply ("IH" with "HΦ").
  Qed.

  Local Lemma release_spec l t :
    {{{ inv lockN (Rlock (A:=A) l) ∗ l ↦{#2/3} (encode_trace (A:=A) t) ∗ trace_is_def (A:=A) l t }}} release #(l+ₗ1)
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#Hinv [Hl Ht]] HΦ".
    wp_lam. iInv lockN as "[[_ (% & >Hl' & _)]| Hlk]".
    { iCombine "Hl Hl'" gives %[Hfalse _]. done. }
    wp_store. iModIntro. iSplitL "Hl Ht Hlk".
    { iNext. iLeft. iFrame. }
    by iApply "HΦ".
  Qed.

  Lemma new_trace_spec (I : list (positive*A) → Prop) :
    I [] →
    {{{ True }}}
      new_trace #()
    {{{ (l : loc), RET #l; trace_is (A:=A) l [] ∗ trace_inv l I }}}.
  Proof.
    rewrite trace_inv_unseal /trace_inv_def trace_is_unseal /trace_is_def.
    iIntros (HI Φ) "_ HΦ".
    wp_lam.
    wp_apply (wp_allocN_seq with "[//]") as (l) "Hcells"; first lia.
    iEval (simpl) in "Hcells".
    iDestruct "Hcells" as "([Hl Hmeta] & [Hlock _] & [Hscratch _] & _)".
    rewrite Loc.add_0.
    wp_pures.
    wp_store.
    wp_pures.
    iMod (nondet_bool_prealloc_inv_alloc (l +ₗ 2) false with "Hscratch") as "#Hscratch".
    wp_apply wp_fork.
    { by iApply nondet_bool_prealloc_bg_spec. }

    iMod (own_alloc (●ML (encode_trace_A (A:=A) <$> []))) as (γ) "H●"; first apply mono_list_auth_valid.
    iMod (meta_set ⊤ l γ metaN with "Hmeta") as "#Hmeta"; first set_solver.

    iEval (change (NONEV) with (encode_trace (A:=A) [])) in "Hl".
    iEval (rewrite -dfrac_2third_1third) in "Hl".
    iEval (rewrite -dfrac_3third) in "H●".
    iDestruct "Hl" as "[Hl Hl']".
    iDestruct "H●" as "(H● & H●' & H●'')".
    iMod (inv_alloc invN ⊤ (Rinv l I) with "[$Hmeta $Hl' $H●' //]") as "#Hinv".
    iMod (inv_alloc lockN ⊤ (Rlock (A:=A) l) with "[Hlock Hl H●'']") as "#Hlock".
    { iNext. iLeft. iFrame "#∗". }
    wp_pures. iModIntro. iApply "HΦ".
    iFrame "#∗".
  Qed.

  Lemma trace_emit_spec l τ (a : A) (v : val) (I : list (positive*A) → Prop) :
    decode_val v = Some a →
    trace_inv l I ⊢
    <<{ ∀∀ t, trace_is l t ∗ ⌜I (t++[(τ,a)])⌝ }>>
      trace_emit #l #(Z.pos τ) v @ ↑traceN
    <<{ trace_is l (t++[(τ,a)]) | RET #() }>>.
  Proof.
    intros ->%encode_decode_val.
    rewrite trace_inv_unseal /trace_inv_def trace_is_unseal /trace_is_def.
    iIntros "#(Hinv & Hlock & _)" (Φ) "AU".

    wp_lam. wp_pures.
    wp_apply (acquire_spec with "Hlock") as (t) "(Hl & %γ & #Hmeta & H●)".
    wp_pures. wp_load.
    wp_pures.

    (* Linearization point (we could typically linearize anytime while holding
      the lock, but it is most natural to open the invariant and commit at the
      same step) *)
    wp_bind (_ <- _)%E.
    iInv invN as (t') ">(Hl' & (%γ' & Hmeta' & H●') & _)" "Hclose0".
    iMod "AU" as (t'') "[[(%γ'' & Hmeta'' & H●'') HI''] [_ Hclose1]]".
    iDestruct (meta_agree with "Hmeta Hmeta'") as %<-.
    iDestruct (own_valid_2 with "H● H●'") as %[_ <-%(inj (fmap encode_trace_A))]%mono_list_auth_dfrac_op_valid_L.
    iDestruct (meta_agree with "Hmeta Hmeta''") as %<-.
    iDestruct (own_valid_2 with "H● H●''") as %[_ <-%(inj (fmap encode_trace_A))]%mono_list_auth_dfrac_op_valid_L.
    iCombine "Hl Hl'" as "Hl". rewrite dfrac_2third_1third.
    iCombine "H● H●' H●''" as "H●". rewrite dfrac_3third.
    wp_store.
    iMod (own_update with "H●") as "H●".
    { apply (mono_list_update (encode_trace_A <$> t++[(τ,a)])).
      rewrite fmap_app.
      by apply prefix_app_r. }
    iEval (rewrite -encode_trace_snoc -dfrac_2third_1third) in "Hl".
    iDestruct "Hl" as "[Hl Hl']".
    iEval (rewrite -dfrac_3third) in "H●".
    iDestruct "H●" as "(H● & H●' & H●'')".
    iMod ("Hclose1" with "[$Hmeta'' $H●'']") as "HΦ". iModIntro.
    iMod ("Hclose0" with "[$Hl' $Hmeta' $H●' $HI'']") as "_". iModIntro.

    wp_pures.
    wp_apply (release_spec with "[$Hlock $Hl $Hmeta $H●]") as "_".
    done.
  Qed.

  Lemma trace_fresh_spec l (a : A) (v : val) (I : list (positive*A) → Prop) :
    decode_val v = Some a →
    trace_inv l I ⊢
    <<{ ∀∀ t, trace_is l t ∗ ⌜∀ τ, τ ∉ t.*1 → I (t++[(τ,a)])⌝ }>>
      trace_fresh #l v @ ↑traceN
    <<{ ∃∃ τ, trace_is l (t++[(τ,a)]) ∗ ⌜τ ∉ t.*1⌝ | RET #(Z.pos τ) }>>.
  Proof.
    intros ->%encode_decode_val.
    rewrite trace_inv_unseal /trace_inv_def trace_is_unseal /trace_is_def.
    iIntros "#(Hinv & Hlock & Hscratch)" (Φ) "AU".

    wp_lam. wp_pures.
    wp_apply (acquire_spec with "Hlock") as (t) "(Hl & %γ & #Hmeta & H●)".
    wp_pures. wp_load.
    wp_pures. wp_apply (nondet_pos_unbounded_prealloc_spec_pos with "Hscratch") as (τ) "_".
    wp_pures. wp_apply (is_fresh_spec with "[//]") as ([|]) "%His_fresh"; wp_pures.
    - (* τ is already fresh *)
      specialize (His_fresh (ltac:(done))).
      wp_bind (_ <- _)%E.
      iInv invN as (t') ">(Hl' & (%γ' & Hmeta' & H●') & _)" "Hclose0".
      iMod "AU" as (t'') "[[(%γ'' & Hmeta'' & H●'') %HI''] [_ Hclose1]]".
      iDestruct (meta_agree with "Hmeta Hmeta'") as %<-.
      iDestruct (own_valid_2 with "H● H●'") as %[_ <-%(inj (fmap encode_trace_A))]%mono_list_auth_dfrac_op_valid_L.
      iDestruct (meta_agree with "Hmeta Hmeta''") as %<-.
      iDestruct (own_valid_2 with "H● H●''") as %[_ <-%(inj (fmap encode_trace_A))]%mono_list_auth_dfrac_op_valid_L.
      iCombine "Hl Hl'" as "Hl". rewrite dfrac_2third_1third.
      iCombine "H● H●' H●''" as "H●". rewrite dfrac_3third.
      wp_store.
      iMod (own_update with "H●") as "H●".
      { apply (mono_list_update (encode_trace_A <$> t++[(τ,a)])).
        rewrite fmap_app.
        by apply prefix_app_r. }
      iEval (rewrite -encode_trace_snoc -dfrac_2third_1third) in "Hl".
      iDestruct "Hl" as "[Hl Hl']".
      iEval (rewrite -dfrac_3third) in "H●".
      iDestruct "H●" as "(H● & H●' & H●'')".
      iMod ("Hclose1" with "[$Hmeta'' $H●'' //]") as "HΦ". iModIntro.
      iMod ("Hclose0" with "[$Hl' $Hmeta' $H●']") as "_"; first by auto. iModIntro.

      wp_pures.
      wp_apply (release_spec with "[$Hlock $Hl $Hmeta $H●]") as "_".
      by wp_pures.

    - (* fallback to max_id + 1 *)
      clear τ His_fresh.
      wp_apply (max_id_spec with "[//]") as (τ Hmax) "".
      assert (Hfresh': (τ+1)%positive ∉ t.*1).
      { intros HFalse. rewrite Forall_forall in Hmax.
        specialize (Hmax _ HFalse). lia. }
      wp_pures.
      wp_bind (_ <- _)%E.
      iInv invN as (t') ">(Hl' & (%γ' & Hmeta' & H●') & _)" "Hclose0".
      iMod "AU" as (t'') "[[(%γ'' & Hmeta'' & H●'') %HI''] [_ Hclose1]]".
      iDestruct (meta_agree with "Hmeta Hmeta'") as %<-.
      iDestruct (own_valid_2 with "H● H●'") as %[_ <-%(inj (fmap encode_trace_A))]%mono_list_auth_dfrac_op_valid_L.
      iDestruct (meta_agree with "Hmeta Hmeta''") as %<-.
      iDestruct (own_valid_2 with "H● H●''") as %[_ <-%(inj (fmap encode_trace_A))]%mono_list_auth_dfrac_op_valid_L.
      iCombine "Hl Hl'" as "Hl". rewrite dfrac_2third_1third.
      iCombine "H● H●' H●''" as "H●". rewrite dfrac_3third.
      wp_store.
      iMod (own_update with "H●") as "H●".
      { apply (mono_list_update (encode_trace_A <$> t++[((τ+1)%positive,a)])).
        rewrite fmap_app.
        by apply prefix_app_r. }
      iEval (rewrite -encode_trace_snoc -dfrac_2third_1third) in "Hl".
      iDestruct "Hl" as "[Hl Hl']".
      iEval (rewrite -dfrac_3third) in "H●".
      iDestruct "H●" as "(H● & H●' & H●'')".
      iMod ("Hclose1" with "[$Hmeta'' $H●'' //]") as "HΦ". iModIntro.
      iMod ("Hclose0" with "[$Hl' $Hmeta' $H●']") as "_"; first by auto. iModIntro.

      wp_pures.
      wp_apply (release_spec with "[$Hlock $Hl $Hmeta $H●]") as "_".
      by wp_pures.
  Qed.

   Lemma trace_peak_spec l (I : list (positive*A) → Prop) :
    {{{ trace_inv l I }}}
      trace_peak #l
    {{{ t, RET (encode_trace (A:=A) t); ⌜I t⌝ }}}.
  Proof.
    rewrite trace_inv_unseal /trace_inv_def.
    iIntros (Φ) "#(Hinv & Hlock & Hscratch) HΦ".
    wp_lam.
    iInv invN as (t) ">(Hl & (%γ & Hmeta & H●) & %HI)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[$Hl $Hmeta $H●]") as "_"; first by auto.
    iModIntro. iApply "HΦ".
    done.
  Qed.
End spec.

Local Lemma erased_steps_is_fresh `{!Encodable A} τ ts σ :
  τ ∉ ts.*1 →
  rtc erased_step ([is_fresh (encode_trace (A:=A) ts) #(Z.pos τ)],σ)
                  ([Val #true],σ).
Proof.
  intros Hfresh. induction ts as [|[τ₀ v₀] ts IH] using rev_ind.
  { rewrite /is_fresh. repeat erased_steps_pure. reflexivity. }
  rewrite /is_fresh. erased_steps_pure. rewrite -/is_fresh.
  rewrite encode_trace_snoc.
  repeat erased_steps_pure.
  { by constructor. }
  rewrite bool_decide_eq_false_2; last first.
  { intros Heq. injection Heq as ->.
    contradict Hfresh. rewrite fmap_app /=. set_solver. }
  simpl.
  repeat erased_steps_pure.
  apply IH.
  rewrite fmap_app in Hfresh. set_solver.
Qed.

Local Lemma erased_step_acquire (l : loc) σ :
  σ.(heap) !! l = Some (Some NONEV) →
  rtc erased_step ([acquire #l], σ) ([Val #()], state_upd_heap <[l:=Some (SOMEV #())]> σ).
Proof.
  intros Hlock.
  rewrite /acquire /try_acquire.
  repeat erased_steps_pure.
  erased_steps_apply erased_step_cmpxchg_suc; [by constructor|done|].
  repeat erased_steps_pure.
  reflexivity.
Qed.

Local Lemma erased_step_release (l : loc) σ :
  σ.(heap) !! l = Some (Some (SOMEV #())) →
  rtc erased_step ([release #l], σ) ([Val #()], state_upd_heap <[l:=Some (NONEV)]> σ).
Proof.
  intros Hlock.
  rewrite /release.
  repeat erased_steps_pure.
  erased_steps_apply erased_step_store; first done.
  reflexivity.
Qed.

Lemma erased_steps_trace_emit `{!Encodable A} τ (a : A) (v : val) (l : loc) ts σ :
  decode_val v = Some a →
  σ.(heap) !! l = Some (Some (encode_trace ts)) →
  σ.(heap) !! (l +ₗ 1) = Some (Some NONEV) →
  rtc erased_step ([trace_emit #l #(Z.pos τ) v],σ)
                  ([Val #()], state_upd_heap <[l:=Some (encode_trace (ts++[(τ,a)]))]> σ).
Proof.
  intros ->%encode_decode_val.
  assert (l +ₗ 1 ≠ l).
  { destruct l as [l]. rewrite /Loc.add. intros HFalse. injection HFalse. lia. }
  intros Hheap Hlock.
  rewrite /trace_emit.
  repeat erased_steps_pure.
  erased_steps_apply erased_step_acquire; first done.
  repeat erased_steps_pure.
  erased_steps_apply erased_step_load.
  { destruct σ. simpl in *. rewrite lookup_insert_ne; done. }
  repeat erased_steps_pure.
  erased_steps_apply erased_step_store.
  { destruct σ. simpl in *. rewrite lookup_insert_ne; done. }
  repeat erased_steps_pure.
  erased_steps_apply erased_step_release.
  { simpl. rewrite lookup_insert_ne // lookup_insert_eq //. }

  destruct σ. simpl in *.
  rewrite insert_insert_ne //.
  rewrite insert_insert_eq (insert_id _ (l +ₗ 1)) //.
  rewrite encode_trace_snoc. reflexivity.
Qed.

Lemma erased_steps_trace_fresh `{!Encodable A} τ (a : A) (v : val) (l : loc) ts σ :
  decode_val v = Some a →
  τ ∉ ts.*1 →
  σ.(heap) !! l = Some (Some (encode_trace ts)) →
  σ.(heap) !! (l +ₗ 1) = Some (Some NONEV) →
  σ.(heap) !! (l +ₗ 2) = Some (Some #false) →
  rtc erased_step ([nondet_bool_prealloc_bg #(l +ₗ 2); trace_fresh #l v], σ)
    ([nondet_bool_prealloc_bg #(l +ₗ 2); Val #(Z.pos τ)],
     state_upd_heap <[l := Some (encode_trace (ts++[(τ,a)]))]> σ).
Proof.
  intros ->%encode_decode_val.
  assert (Hne1 : l +ₗ 1 ≠ l).
  { destruct l as [l]. rewrite /Loc.add. intros HFalse. injection HFalse. lia. }
  assert (Hne2 : l +ₗ 2 ≠ l).
  { destruct l as [l]. rewrite /Loc.add. intros HFalse. injection HFalse. lia. }
  assert (Hne12 : l +ₗ 2 ≠ l +ₗ 1).
  { destruct l as [l]. rewrite /Loc.add. intros HFalse. injection HFalse. lia. }
  intros Hfresh Hlookup Hlock Hscratch.
  pose (σ_acq := state_upd_heap <[l +ₗ 1 := Some (SOMEV #())]> σ).
  assert (Hscratch_acq : heap σ_acq !! (l +ₗ 2) = Some (Some #false)).
  { subst σ_acq. simpl. rewrite lookup_insert_ne //. }
  pose proof (erased_steps_nondet_pos_unbounded_prealloc τ (l +ₗ 2) σ_acq Hscratch_acq)
    as Hsteps_nondet.
  rewrite /trace_fresh.
  repeat erased_steps_pure2.
  erased_steps_apply2 erased_step_acquire; first done.
  repeat erased_steps_pure2.
  erased_steps_apply2 erased_step_load.
  { destruct σ. simpl in *. rewrite lookup_insert_ne; done. }
  repeat erased_steps_pure2.
  erased_steps_2apply Hsteps_nondet.
  apply erased_steps_cons_l.
  repeat erased_steps_pure.
  erased_steps_apply erased_steps_is_fresh; first done.
  repeat erased_steps_pure.
  erased_steps_apply erased_step_store.
  { subst σ_acq. simpl. rewrite lookup_insert_ne // lookup_insert_ne //. }
  repeat erased_steps_pure.
  erased_steps_apply erased_step_release.
  { subst σ_acq. simpl.
    rewrite lookup_insert_ne //.
    rewrite lookup_insert_eq //. }
  repeat erased_steps_pure.
  subst σ_acq. destruct σ. simpl in *.
  rewrite (insert_insert_ne _ (l +ₗ 1) l) //.
  rewrite insert_insert_eq.
  rewrite (insert_id _ (l +ₗ 1)) //.
  rewrite encode_trace_snoc. reflexivity.
Qed.

Theorem trace_adequacy `{!heapGpreS Σ, !traceG Σ, !Encodable A} (l : loc) (e : expr) σ (s : stuckness) (I : list (positive*A) → Prop) (φ : val → Prop) :
  I [] →
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ trace_inv l I -∗ trace_is (A:=A) l [] -∗
    ([∗ map] k↦y ∈ delete (l +ₗ 2) (delete (l +ₗ 1) (delete l (heap σ))), from_option (λ v, k ↦ v) True y ∗ meta_token k ⊤) -∗
    ([∗ set] p ∈ used_proph_id σ, ∃ vs, proph p vs) -∗
    WP e @ s;⊤ {{ v, ⌜φ v⌝ }}) →
  (∀ v es σ' (b_init : bool),
    σ.(heap) !! l = Some (Some (encode_trace (A:=A) [])) →
    σ.(heap) !! (l+ₗ1) = Some (Some NONEV) →
    σ.(heap) !! (l+ₗ2) = Some (Some #b_init) →
    rtc erased_step ([e; nondet_bool_prealloc_bg #(l+ₗ2)], σ) (Val v::es,σ') →
    φ v ∧ (∀ e2, s = NotStuck → e2 ∈ (Val v :: es) → not_stuck e2 σ')).
Proof.
  assert (l +ₗ 1 ≠ l).
  { destruct l as [l]. rewrite /Loc.add. intros HFalse. injection HFalse. lia. }
  assert (l +ₗ 2 ≠ l).
  { destruct l as [l]. rewrite /Loc.add. intros HFalse. injection HFalse. lia. }
  assert (l +ₗ 2 ≠ l +ₗ 1).
  { destruct l as [l]. rewrite /Loc.add. intros HFalse. injection HFalse. lia. }

  intros HInil Hwp v es σ' b_init Hinitσ Hlock Hscratch [n [κs Hsteps]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ heap_lang); last exact Hsteps.
  intros ?.

  (* setup HeapLang *)
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh [Hls Hms]]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init_strong κs σ.(used_proph_id)) as (?) "[Hp Hps]".
  iMod (mono_nat_own_alloc) as (γn) "[Hsteps _]".
  pose (HheapGS := (HeapGS HasLc Σ _ _ _ _ γn _)).

  (* setup trace lib *)
  iDestruct (big_sepM_delete _ _ l with "Hls") as "[Hl Hls]"; first done.
  iDestruct (big_sepM_delete _ _ l with "Hms") as "[Hm Hms]"; first done.
  iAssert (l ↦ NONEV)%I with "[Hl]" as "Hl".
  (* TODO: the abstraction of HeapLang poinsto is broke here because we
    have to manually allocate [l] *)
  { rewrite primitive_laws.pointsto_unseal. iFrame. }
  iDestruct (big_sepM_delete _ _ (l+ₗ1) with "Hls") as "[Hlock Hls]".
  { rewrite lookup_delete_ne //. }
  iDestruct (big_sepM_delete _ _ (l+ₗ1) with "Hms") as "[_ Hms]".
  { rewrite lookup_delete_ne //. }
  iAssert ((l+ₗ1) ↦ NONEV)%I with "[Hlock]" as "Hlock".
  { rewrite primitive_laws.pointsto_unseal. iFrame. }
  iDestruct (big_sepM_delete _ _ (l+ₗ2) with "Hls") as "[Hscratch Hls]".
  { rewrite !lookup_delete_ne //. }
  iDestruct (big_sepM_delete _ _ (l+ₗ2) with "Hms") as "[_ Hms]".
  { rewrite !lookup_delete_ne //. }
  iAssert ((l+ₗ2) ↦ #b_init)%I with "[Hscratch]" as "Hscratch".
  { rewrite primitive_laws.pointsto_unseal. iFrame. }
  iMod (own_alloc (●ML (encode_trace_A (A:=A) <$> []))) as (γ) "H●"; first apply mono_list_auth_valid.
  iMod (meta_set ⊤ l γ metaN with "Hm") as "#Hm"; first set_solver.
  iEval (change NONEV with (encode_trace (A:=A) [])) in "Hl".
  iEval (rewrite -dfrac_2third_1third) in "Hl".
  iEval (rewrite -dfrac_3third) in "H●".
  iDestruct "Hl" as "[Hl Hl']".
  iDestruct "H●" as "(H● & H●' & H●'')".
  iMod (inv_alloc invN ⊤ (Rinv l I) with "[$Hl' $Hm $H●' //]") as "Hinv".
  iMod (inv_alloc lockN ⊤ (Rlock (A:=A) l) with "[Hlock Hl H●'']") as "Hlock".
  { iNext. iLeft. iFrame "#∗".  }
  iMod (nondet_bool_prealloc_inv_alloc (l+ₗ2) b_init with "Hscratch") as "#Hscratch".
  iAssert (trace_inv l I) with "[Hinv Hlock]" as "Hti".
  { rewrite trace_inv_unseal. iFrame "#∗". }
  iDestruct "Hti" as "#Hti".
  iAssert (trace_is (A:=A) l []) with "[H●]" as "Hl".
  { rewrite trace_is_unseal. iFrame "#∗". }

  iDestruct (Hwp HheapGS with "Hi Hti Hl [Hls Hms] [Hps]") as "Hwp".
  { rewrite big_sepM_sep. iFrame.
    iApply (big_sepM_mono with "Hls").
    iIntros (? [|] ?) "Hpointsto"; simpl; last done.
    rewrite primitive_laws.pointsto_unseal. iFrame. }
  { iApply (big_sepS_mono with "Hps").
    iIntros (p _) "$". }
  iAssert (WP nondet_bool_prealloc_bg #(l+ₗ2) @ s; ⊤ {{ _, True }})%I as "Hbg".
  { iApply (wp_stuck_mono NotStuck); first done.
    iApply (nondet_bool_prealloc_bg_spec with "Hscratch"). }
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                        proph_map_interp κs σ.(used_proph_id) ∗
                        mono_nat_auth_own γn 1 ns))%I.
  iExists [λ v, ⌜φ v⌝%I; (λ _, True)%I], (λ _, True%I), _ => /=.
  iFrame "Hh Hp Hsteps Hwp Hbg".
  iIntros (es' t2' Heq ? Hns) "[Hh _] HΦs _".
  destruct es' as [|e0 [|e1 [|? ?]]]; try done.
  simpl in Heq. injection Heq as Heq_e0 Heq_es. subst e0. subst es.
  iDestruct "HΦs" as "[%Hφ _]".

  rewrite trace_inv_unseal /trace_inv_def /trace_is_def.
  iDestruct "Hti" as "(Hti & _ & _)".
  iInv "Hti" as (ts) ">(Hl & _ & %HIt)" "_".
  rewrite primitive_laws.pointsto_unseal /primitive_laws.pointsto_def.
  iDestruct (gen_heap_valid with "Hh Hl") as %Hlookup.
  iApply fupd_mask_intro_discard; [set_solver|].
  iPureIntro. split; first done.
  intros e2 Hs He2_in. by apply (Hns e2 Hs).
Qed.
