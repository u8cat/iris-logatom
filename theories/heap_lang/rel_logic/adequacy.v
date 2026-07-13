(** Adequacy statements for the refinement proposition *)
From iris.algebra Require Import auth frac agree gmap.
From iris.base_logic.lib Require Import mono_nat.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Export proofmode notation adequacy.
From iris_logatom.heap_lang.rel_logic Require Export spec_ra model.

Lemma heap_strong_adequacy Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS Σ}, ⊢
    inv_heap_inv -∗
    ([∗ map] l↦ov ∈ heap σ, from_option (λ v, l ↦ v) True ov) -∗
    WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp.
  apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _ s); [|done].

  iIntros (Hinv).
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh [Hσ _]]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (mono_nat_own_alloc 0) as (γ) "[Hsteps _]".
  set (HheapGS := (HeapGS _ _ _ _ _ _ γ _)).
  iDestruct (Hwp with "Hi [Hσ]") as "Hwp".
  { iApply (big_sepM_mono with "Hσ").
    iIntros (? [] ?) "/= Hp //".
    rewrite primitive_laws.pointsto_unseal //. }
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own γ 1 ns))%I.
  iExists [(λ v, ⌜φ v⌝%I)], (λ _, True)%I, _ => /=.
  iFrame.
  iIntros (es' t2' -> ? ?) " _ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Lemma refines_adequate_strong Σ `{relocPreG Σ}
  (A : ∀ `{relocGS Σ}, lrel Σ)
  (P : val → val → Prop) (e e' : expr) σ :
  (∀ `{relocGS Σ}, ∀ v v', A v v' -∗ ⌜P v v'⌝) →
  (∀ `{relocGS Σ},
      ([∗ map] l↦ov ∈ heap σ, from_option (λ v, l ↦ v) True ov) -∗
      ([∗ map] l↦ov ∈ heap σ, from_option (λ v, l ↦ₛ v) True ov)%I -∗
      REL e << e' : A) →
  adequate NotStuck e σ
    (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h)
            ∧ P v v').
Proof.
  intros HA Hlog.
  eapply (heap_strong_adequacy Σ); iIntros (Hinv) "_".
  iIntros "Hpts".
  iMod (ghost_map_alloc {[ 0:= e']}) as (γtp) "[Htp He']".
  rewrite big_sepM_singleton.
  iMod (ghost_map_alloc σ.(heap)) as (γst) "[Hσ Hpts']".
  iMod (prophS_alloc σ) as (γp) "Hps".
  set (Hcfg := RelocGS _ _ (CFGGS _ _ _ _ γtp γst γp)).
  iMod (inv_alloc specN _ (spec_inv ([e'], σ)) with "[Htp Hσ Hps]") as "#Hcfg".
  { iNext. iExists [e'], σ. iFrame. eauto. }
  iApply wp_fupd. iApply wp_wand_r.
  iSplitL.
  - iPoseProof (Hlog _) as "Hrel".
    iSpecialize ("Hrel" with "Hpts [Hpts']").
    { iApply (big_sepM_mono with "Hpts'").
      iIntros (? [] ?) "/= Hp //". }
    rewrite refines_eq /refines_def /spec_ctx.
    iApply fupd_wp.
    iApply ("Hrel" $! (RefId 0 [])).
    iFrame. iExists _. by iFrame.
  - iIntros (v).
    iDestruct 1 as (v') "[Hj Hinterp]".
    iDestruct (HA with "Hinterp") as "Hinterp".
    iDestruct "Hinterp" as %Hinterp.
    iInv specN as (tp σ') ">(Hown & Hheap & Hps & Hsteps)" "Hclose".
    iDestruct "Hsteps" as %Hsteps'.
    iDestruct "Hj" as "[#Hs Hj]".
    iDestruct (ghost_map_lookup with "Hown Hj") as %Htp.
    destruct tp as [|? tp']; simplify_eq/=.
    iMod ("Hclose" with "[-]") as "_".
    { iExists (_ :: tp'), σ'. iFrame. eauto. }
    rewrite lookup_insert_Some in Htp.
    destruct Htp as [[_ ->] | [? _]]; [|done].
    iIntros "!> !%"; eauto.
Qed.

Lemma refines_adequate Σ `{relocPreG Σ}
  (A : ∀ `{relocGS Σ}, lrel Σ)
  (P : val → val → Prop) (e e' : expr) σ :
  (∀ `{relocGS Σ}, ∀ v v', A v v' -∗ ⌜P v v'⌝) →
  (∀ `{relocGS Σ}, ⊢ REL e << e' : A) →
  adequate NotStuck e σ
    (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h)
            ∧ P v v').
Proof.
  intros ? Hlog.
  eapply refines_adequate_strong; [done|done|].
  iIntros (?) "_ _". iApply Hlog.
Qed.

Theorem refines_typesafety Σ `{relocPreG Σ} (e e' : expr) e1
        (A : ∀ `{relocGS Σ}, lrel Σ) thp σ σ' :
  (∀ `{relocGS Σ}, ⊢ REL e << e' : A) →
  rtc erased_step ([e], σ) (thp, σ') → e1 ∈ thp →
  not_stuck e1 σ'.
Proof.
  intros Hlog ??.
  cut (adequate NotStuck e σ (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h) ∧ True)); first (intros [_ ?]; eauto).
  eapply (refines_adequate _ A) ; eauto.
Qed.
