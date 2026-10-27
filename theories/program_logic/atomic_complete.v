(* atomic_complete.v *)

From iris_logatom.lib Require Import list list2map.
From iris.proofmode Require Import base ltac_tactics.
From iris_logatom.lib Require Import derived_laws_later.
From iris.algebra Require Import list excl_auth gmap_view.
From iris.base_logic Require Import invariants ghost_map.
From iris.program_logic Require Import atomic.
From iris_logatom.program_logic Require Import weakestpre.
From iris_logatom.pure_logic Require Export adequacy state_set linear.
From iris.heap_lang Require Import primitive_laws notation proofmode.
From iris_logatom.heap_lang.lib Require Import ghost_id.
From iris_logatom.heap_lang Require Import completeness.
From iris_logatom.pure_logic Require Import adv_step_decide.

Local Notation Sₙ := Datatypes.S.

(* ========================================== *)
(* Main theorem *)

Definition wrap_init (init : expr) : expr := (init, NewProph).
Definition wrap_op (n : nat) (op : val) : val := λ: "obj_p" "arg",
  let: "obj" := Fst "obj_p" in
  let: "p" := Snd "obj_p" in
  let: "ghost_id" := NewGhostID in
  resolve_proph: "p" to: (InjL ("ghost_id",(#n, "arg")));;
  let: "res" := op "obj" "arg" in
  resolve_proph: "p" to: (InjR ("ghost_id","res"));;
  "res".


Class linearizabilityG `{M : model} Σ := {
  #[local] linearG_meta :: inG Σ (agreeR (prodO (prodO (prodO gnameO gnameO) gnameO) gnameO));
  #[local] linearG_pendingOp :: ghost_mapG Σ positive expr;
  #[local] linearG_children :: ghost_mapG Σ nat expr;
  #[local] linearG_receipt :: inG Σ (gmap_viewR positive (agreeR $ laterO (val -d> iPropO Σ)));
  #[local] linearG_state :: inG Σ (excl_authR (leibnizO S));
  #[local] linearG_completeness :: completenessG heap_lang Σ;
}.

Definition linearizabilityΣ `{M : model} := #[
  GFunctor (agreeRF (prodO (prodO (prodO gnameO gnameO) gnameO) gnameO));
  ghost_mapΣ positive expr;
  ghost_mapΣ nat expr;
  GFunctor (gmap_viewRF positive (agreeRF $ laterOF (val -d> idOF)));
  GFunctor (excl_authRF (leibnizO S));
  completenessΣ heap_lang].
Global Instance subG_linearizabilityG `{M : model} Σ : subG linearizabilityΣ Σ → linearizabilityG Σ.
Proof. solve_inG. Qed.

(* ghost theory *)
Section ghost.
  Context `{!heapGS Σ, M : model, !linearizabilityG Σ}.
  Implicit Types (Φ : val → iProp Σ) (Φs : gmap positive (val → iProp Σ)) (τ : positive).

  Definition own_receipt_auth γ Φs :=
    own γ (gmap_view_auth (DfracOwn 1) (to_agree <$> (Next <$> (Φs : gmap positive (val -d> iProp Σ))))).
  Definition own_receipt γ τ Φ :=
    own γ (gmap_view_frag τ (DfracOwn 1) (to_agree $ Next (Φ : val -d> iProp Σ))).

  Lemma own_receipt_alloc_empty :
    ⊢ |==> ∃ γ, own_receipt_auth γ ∅.
  Proof.
    iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γ) "H".
    { apply gmap_view_auth_valid. }
    iModIntro. iExists γ.
    rewrite /own_receipt_auth !fmap_empty //.
  Qed.

  Lemma own_receipt_insert {γ Φs} τ Φ :
    Φs !! τ = None →
    own_receipt_auth γ Φs ⊢ |==> own_receipt_auth γ (<[τ:=Φ]> Φs) ∗ own_receipt γ τ Φ.
  Proof.
    iIntros (Hfresh) "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (gmap_view_alloc _ τ (DfracOwn 1) (to_agree $ Next (Φ : val -d> iProp Σ))); try done.
      rewrite !lookup_fmap Hfresh //. }
    rewrite -!fmap_insert.
    by iFrame.
  Qed.

  Lemma own_receipt_delete {γ Φs τ Φ} :
    own_receipt_auth γ Φs -∗ own_receipt γ τ Φ ==∗ own_receipt_auth γ (delete τ Φs).
  Proof.
    iIntros "H● H◯".
    iMod (own_update_2 with "H● H◯") as "H●"; first apply gmap_view_delete.
    rewrite -!fmap_delete.
    by iFrame.
  Qed.

  Lemma own_receipt_agree {γ Φs τ Φ} :
    own_receipt_auth γ Φs -∗ own_receipt γ τ Φ -∗ ∃ Φ', ⌜Φs !! τ = Some Φ'⌝ ∗ ▷ (Φ' ≡@{val-d> iProp Σ} Φ).
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as "#Hv".
    rewrite gmap_view_both_validI_total.
    iDestruct "Hv" as (Φ') "(_ & _ & HΦ' & Hv & Hincl)".
    rewrite !lookup_fmap.
    case: (Φs !! τ) => [Φ''|] /=; last first.
    { iDestruct "HΦ'" as %?. done. }
    iDestruct "HΦ'" as %[= <-]. iExists Φ''; iSplit; first done.
    rewrite to_agree_includedI internal_eq_sym -later_equivI //.
  Qed.
End ghost.

Section logatom.
  Context `{!heapGS Σ, HModelDecidable : !ModelDecidable M, !linearizabilityG Σ}.
  Context (init : expr) (ops : list val) (valid_obj : val → state → Prop).

  (* we only consider a bounded prefix of execution so that [is_valid_trace] is decidable  *)
  Definition is_valid_trace obj config steps_left (ts : list (positive*trace)) :=
    ∃ config', bstepsL (adv_step ops obj valid_requests) steps_left config config' ts.

  Local Lemma is_valid_trace_decide obj config steps_left ts :
    (is_valid_trace obj config steps_left ts) ∨ ¬(is_valid_trace obj config steps_left ts).
  Proof. apply (adv_steps_emit_decide ops). Qed.

  Lemma is_valid_trace_nil obj config steps_left :
    is_valid_trace obj config steps_left [].
  Proof. exists config. apply bstepsL_refl. Qed.

  Lemma is_valid_trace_snoc obj config steps_left ts t :
    is_valid_trace obj config steps_left (ts++[t]) →
    is_valid_trace obj config steps_left ts.
  Proof.
    intros [config' Hadv_steps].
    apply bstepsL_app_inv in Hadv_steps.
    destruct Hadv_steps as (?&? & config_mid & Hadv_steps' & _ & Heq).
    exists config_mid.
    eapply bstepsL_weaken; last done.
    lia.
  Qed.

  Lemma is_valid_trace_prefix obj config steps_left ts ts' :
    ts' `prefix_of` ts →
    is_valid_trace obj config steps_left ts →
    is_valid_trace obj config steps_left ts'.
  Proof.
    intros [k ->].
    induction k as [|?? IHk] using rev_ind; first by rewrite right_id.
    intros ?. apply IHk.
    eapply is_valid_trace_snoc.
    rewrite -assoc //.
  Qed.

  Lemma is_valid_trace_call obj π efs σ (τ : positive) n (v : val) steps_left (ts : list (positive*trace)) :
    τ ∉ π.*1 → default default_vr (valid_requests!!n) v →
    is_valid_trace obj (Config (π++[(τ, Some ((ops!!!n: val) obj v))]) efs σ) steps_left ts →
    is_valid_trace obj (Config π efs σ) (Sₙ steps_left) ((τ,Call n v)::ts).
  Proof.
    intros Hfresh Hvalid_req [config' Hadv_steps].
    exists config'.
    change ((τ,Call n v) :: ts) with ([(τ,Call n v)] ++ ts).
    eapply bstepsL_l; last eassumption.
    by apply adv_step_call.
  Qed.

  Lemma is_valid_trace_intermediate obj π₁ π₂ efs e₁ e₂ σ₁ σ₂ κ ef (τ : positive) steps_left (ts : list (positive*trace)) :
    prim_step e₁ σ₁ κ e₂ σ₂ ef →
    is_valid_trace obj (Config (π₁++(τ, Some e₂)::π₂) (efs++ef) σ₂) steps_left ts →
    is_valid_trace obj (Config (π₁++(τ, Some e₁)::π₂) efs σ₁) (Sₙ steps_left) ts.
  Proof.
    intros Hprim_step [config' Hadv_steps].
    eexists config'.
    change ts with ([] ++ ts).
    eapply bstepsL_l; last eassumption.
    by eapply adv_step_intermediate.
  Qed.

  Lemma is_valid_trace_child obj π efs1 efs2 e₁ e₂ σ₁ σ₂ κ ef steps_left (ts : list (positive*trace)) :
    prim_step e₁ σ₁ κ e₂ σ₂ ef →
    is_valid_trace obj (Config π (efs1++e₂::efs2++ef) σ₂) steps_left ts →
    is_valid_trace obj (Config π (efs1++e₁::efs2) σ₁) (Sₙ steps_left) ts.
  Proof.
    intros Hprim_step [config' Hadv_steps].
    eexists config'.
    change ts with ([] ++ ts).
    eapply bstepsL_l; last eassumption.
    by eapply adv_step_child.
  Qed.

  Lemma is_valid_trace_return obj π₁ π₂ efs σ (τ : positive) (v : val) steps_left (ts : list (positive*trace)) :
    is_valid_trace obj (Config (π₁++(τ, None)::π₂) efs σ) steps_left ts →
    is_valid_trace obj (Config (π₁++(τ, Some (Val v))::π₂) efs σ) (Sₙ steps_left) ((τ,Ret v)::ts).
  Proof.
    intros [config' Hadv_steps].
    exists config'.
    change ((τ,Ret v) :: ts) with ([(τ,Ret v)] ++ ts).
    eapply bstepsL_l; last eassumption.
    by apply adv_step_return.
  Qed.

  Lemma is_valid_trace_call_inv obj π efs σ (τ : positive) n (v : val) steps_left (ts : list (positive*trace)) :
    default default_vr (valid_requests!!n) v →
    is_valid_trace obj (Config π efs σ) (Sₙ steps_left) ((τ,Call n v)::ts) →
    is_valid_trace obj (Config (π++[(τ, Some ((ops!!!n: val) obj v))]) efs σ) steps_left ts.
  Proof.
    (* The idea is doing an exchange argument:
      If [adv_steps (Config π efs σ) config' (Call τ v::ts)], then there must exist
        an intermediate configuration (Config π' efs' σ') such that
        step0:     [adv_steps (Config π efs σ) (Config π' efs' σ') []] and
        step_call: [adv_step  (Config π' efs' σ') (Config ((τ,op obj v)::π') efs' σ') [Call τ v]]
        step1:     [adv_steps (Config ((τ,op obj v)::π') efs' σ') config' ts)].

      Now if we instead process step_call first, then step0++step1 will be the proof goal. *)

    intros (*Hfresh*) Hvalid_req [config' Hadv_steps].
    exists config'.
    assert (∃ nsteps0 nsteps1 π' efs' σ', bstepsL (adv_step ops obj valid_requests) nsteps0 (Config π efs σ) (Config π' efs' σ') []
      ∧ bstepsL (adv_step ops obj valid_requests) nsteps1 (Config (π'++[(τ,Some ((ops!!!n:val) obj v))]) efs' σ') config' ts
      ∧ steps_left = nsteps0 + nsteps1)
      as (nsteps0 & nsteps1 & π' & efs' & σ' & Hadv_steps0 & (*Hπ &*) Hadv_steps1 & Hsteps_left).
    { remember (Config π efs σ) as config0 eqn:Heq.
      clear Heq.
      remember ((τ,Call n v) :: ts) as ts0 eqn:Heqts0.
      remember (Sₙ steps_left) as steps_left' eqn:Heqsteps_left.
      revert steps_left Heqsteps_left.
      induction Hadv_steps as [|steps_left' config0 config1 config2 ts1 ts2 Hadv_step Hadv_steps IH] => steps_left Heqsteps_left; first done.
      injection Heqsteps_left as ->.
      destruct Hadv_step.
      - (* Call *)
        simpl in Heqts0. injection Heqts0 as -> -> -> ->.
        eexists 0,steps_left,_, _, _. split; [|done].
        apply bstepsL_refl.
      - (* Intermediate *)
        rewrite left_id in Heqts0.
        apply bstepsL_length_le in Hadv_steps as Hlen.
        rewrite Heqts0 /= in Hlen.
        destruct steps_left as [|steps_left]; first lia.
        destruct (IH Heqts0 steps_left eq_refl) as (nsteps1 & nsteps2 & π'0 & efs'0 & σ'0 & Hadv_steps0 & Hadv_steps1 & Hsteps_left).
        exists (Sₙ nsteps1), nsteps2, π'0, efs'0, σ'0. split_and!; [|done|lia].
        rewrite -(right_id [] (++) []).
        eapply bstepsL_l; last eassumption.
        by eapply adv_step_intermediate.
      - (* Child *)
        rewrite left_id in Heqts0.
        apply bstepsL_length_le in Hadv_steps as Hlen.
        rewrite Heqts0 /= in Hlen.
        destruct steps_left as [|steps_left]; first lia.
        destruct (IH Heqts0 steps_left eq_refl) as (nsteps1 & nsteps2 & π'0 & efs'0 & σ'0 & Hadv_steps0 & Hadv_steps1 & Hsteps_left).
        exists (Sₙ nsteps1), nsteps2, π'0, efs'0, σ'0. split_and!; [|done|lia].
        rewrite -(right_id [] (++) []).
        eapply bstepsL_l; last eassumption.
        by eapply adv_step_child.
      - (* Return *)
        injection Heqts0 as _ HFalse. discriminate HFalse. }

    assert (Hadv_steps0' : bstepsL (adv_step ops obj valid_requests) nsteps0 (Config (π++[(τ,Some ((ops!!!n: val) obj v))]) efs σ)
      (Config (π'++[(τ,Some ((ops!!!n: val) obj v))]) efs' σ') []).
    { clear -Hadv_steps0.
      remember (Config π efs σ) as config eqn:Heq.
      remember (Config π' efs' σ') as config' eqn:Heq'.
      replace (Config (π++[(τ,Some ((ops!!!n: val) obj v))]) efs σ)
        with (Config (config.(config_pendingOp)++[(τ,Some ((ops!!!n: val) obj v))]) config.(config_childThread) config.(config_state))
        by by subst config.
      replace (Config (π'++[(τ,Some ((ops!!!n: val) obj v))]) efs' σ')
        with (Config (config'.(config_pendingOp)++[(τ,Some ((ops!!!n: val) obj v))]) config'.(config_childThread) config'.(config_state))
        by by subst config'.
      clear Heq π efs σ Heq' π' efs' σ'.
      assert (∃ ts, ts = (@nil (positive*trace))) as [ts Heqts] by by eexists.
      rewrite -Heqts in Hadv_steps0.
      induction Hadv_steps0 as [|nsteps0 config0 config1 config2 ts1 ts2 Hadv_step Hadv_steps]; first apply bstepsL_refl.
      destruct ts1; last rewrite -app_comm_cons // in Heqts.
      destruct ts2; last discriminate Heqts.
      rewrite -[x in bstepsL (adv_step ops obj valid_requests) _ _ _ x](right_id [] (++) []).
      eapply bstepsL_l; last eauto.
      clear -Hadv_step.
      inversion Hadv_step; subst; simpl.
      - do 2 rewrite -assoc -app_comm_cons.
        by eapply adv_step_intermediate.
      - by eapply adv_step_child. }
    change ts with ([]++ts). subst steps_left.
    eapply bstepsL_trans; eassumption.
  Qed.

  Lemma is_valid_trace_return_inv obj π₁ π₂ efs σ (τ : positive) (v : val) steps_left (ts : list (positive*trace)) :
    NoDup (π₁++(τ, Some (Val v))::π₂).*1 →
    is_valid_trace obj (Config (π₁++(τ, Some (Val v))::π₂) efs σ) (Sₙ steps_left) ((τ,Ret v)::ts) →
    is_valid_trace obj (Config (π₁++(τ, None)::π₂) efs σ) steps_left ts.
  Proof.
    intros Hnodup [config' Hadv_steps].
    exists config'.
    assert (∃ nsteps0 nsteps1 π₁' π₂' efs' σ', bstepsL (adv_step ops obj valid_requests) nsteps0 (Config (π₁++(τ, Some (Val v))::π₂) efs σ) (Config (π₁'++(τ, Some (Val v))::π₂') efs' σ') []
      ∧ bstepsL (adv_step ops obj valid_requests) nsteps1 (Config (π₁'++(τ, None)::π₂') efs' σ') config' ts
      ∧ steps_left = nsteps0 + nsteps1)
      as (nsteps0 & nsteps1 & π₁' & π₂' & efs' & σ' & Hadv_steps0 & Hadv_steps1 & Hsteps_left).
    { remember (Config (π₁++(τ, Some (Val v))::π₂) efs σ) as config0 eqn:Heq.
      clear Heq.
      remember ((τ,Ret v) :: ts) as ts0 eqn:Heqts0.
      remember (Sₙ steps_left) as steps_left' eqn:Heqsteps_left.
      revert steps_left Heqsteps_left.
      induction Hadv_steps as [|steps_left' config0 config1 config2 ts1 ts2 Hadv_step Hadv_steps IH] => steps_left Heqsteps_left; first done.
      injection Heqsteps_left as ->.
      destruct Hadv_step(*; simpl in Hπ*).
      - (* Call *)
        injection Heqts0 as _ HFalse. discriminate HFalse.
      - (* Intermediate *)
        rewrite left_id in Heqts0.
        apply bstepsL_length_le in Hadv_steps as Hlen.
        rewrite Heqts0 /= in Hlen.
        destruct steps_left as [|steps_left]; first lia.
        destruct (IH Heqts0 steps_left eq_refl) as (nsteps1 & nsteps2 & π₁'0 & π₂'0 & efs'0 & σ'0 & Hadv_steps0 & Hadv_steps1 & Hsteps_left).
        exists (Sₙ nsteps1), nsteps2, π₁'0, π₂'0, efs'0, σ'0. split_and!; [|done|lia].
        rewrite -(right_id [] (++) []).
        eapply bstepsL_l; last eassumption.
        by eapply adv_step_intermediate.
      - (* Child *)
        rewrite left_id in Heqts0.
        apply bstepsL_length_le in Hadv_steps as Hlen.
        rewrite Heqts0 /= in Hlen.
        destruct steps_left as [|steps_left]; first lia.
        destruct (IH Heqts0 steps_left eq_refl) as (nsteps1 & nsteps2 & π₁'0 & π₂'0 & efs'0 & σ'0 & Hadv_steps0 & Hadv_steps1 & Hsteps_left).
        exists (Sₙ nsteps1), nsteps2, π₁'0, π₂'0, efs'0, σ'0. split_and!; [|done|lia].
        rewrite -(right_id [] (++) []).
        eapply bstepsL_l; last eassumption.
        by eapply adv_step_child.
      - (* Return *)
        simpl in Heqts0. injection Heqts0 as -> -> ->.
        eexists 0,steps_left,_, _, _, _. split; [|done].
        apply bstepsL_refl. }

    assert (Hadv_steps0' : bstepsL (adv_step ops obj valid_requests) nsteps0 (Config (π₁++(τ,None)::π₂) efs σ)
      (Config (π₁'++(τ,None)::π₂') efs' σ') []).
    { clear -Hnodup Hadv_steps0.
      remember (Config (π₁++(τ,Some (Val v))::π₂) efs σ) as config eqn:Heq.
      remember (Config (π₁'++(τ,Some (Val v))::π₂') efs' σ') as config' eqn:Heq'.
      revert π₁ π₂ efs σ π₁' π₂' efs' σ' Hnodup Heq Heq'.
      assert (∃ ts, ts = (@nil (positive*trace))) as [ts Heqts] by by eexists.
      rewrite -Heqts in Hadv_steps0.
      induction Hadv_steps0 as [|nsteps0 config0 config1 config2 ts1 ts2 Hadv_step Hadv_steps IH]
        => π₁ π₂ efs σ π₁' π₂' efs' σ' Hnodup Heqconfig Heqconfig'; simplify_eq.
      - apply pendingOp_nodup_inj in Heqconfig' as (<- & _ & <-); [|done].
        apply bstepsL_refl.
      - destruct ts1; last rewrite -app_comm_cons // in Heqts.
        destruct ts2; last discriminate Heqts.
        rewrite -(right_id [] (++) []).
        assert (∃ π₁_mid π₂_mid efs_mid σ_mid, NoDup (π₁_mid++(τ,Some (Val v))::π₂_mid).*1 ∧ config1 = Config (π₁_mid++(τ,Some (Val v))::π₂_mid) efs_mid σ_mid)
          as (π₁_mid&π₂_mid&efs_mid&σ_mid&Hnodup_mid&->).
        { inversion Hadv_step; simplify_eq.
          - lazymatch goal with
            | H0: prim_step ?e_p ?σ_p _ ?e_p' ?σ_p' ?efs_p,
              H1: ?π₁0_p++(?τ0_p,Some ?e_p)::?π₂0_p = π₁++(τ,Some (Val v))::π₂ |-_ =>
              rename e_p' into e_mid;
              rename σ_p' into σ_mid;
              rename efs_p into ef;
              rename H0 into Hprim_step;
              rename π₁0_p into π₁0;
              rename τ0_p into τ0;
              rename e_p into e0;
              rename π₂0_p into π₂0;
              rename H1 into Heq
            end.
            exists (take (length π₁) (π₁0++(τ0,Some e_mid)::π₂0)).
            exists (drop (Sₙ (length π₁)) (π₁0++(τ0,Some e_mid)::π₂0)).
            exists (efs++ef), σ_mid.
            assert (Hnodup0: NoDup (π₁0 ++ (τ0, Some e0) :: π₂0).*1) by rewrite Heq //.
            assert (Hnodup_mid: NoDup (π₁0++(τ0,Some e_mid)::π₂0).*1).
            { revert Hnodup0. rewrite !fmap_app !fmap_cons //. }
            rewrite -drop_S; first rewrite take_drop //.
            assert (Hlookup: (π₁0++(τ0,Some e0)::π₂0) !! length π₁ = Some (τ,Some (Val v))).
            { rewrite Heq. apply list_lookup_middle. done. }

            destruct (decide (length π₁ ≤ length π₁0)) as [Hlen_le|Hlen_gt];
            first destruct (decide (length π₁ = length π₁0)) as [Hlen_eq|Hlen_lt].
            + rewrite list_lookup_middle // in Hlookup.
              injection Hlookup as _ ->.
              apply val_stuck in Hprim_step.
              discriminate Hprim_step.
            + rewrite lookup_app_l in Hlookup; last lia.
              by apply lookup_app_l_Some.
            + rewrite cons_middle in Hlookup.
              rewrite cons_middle.
              rewrite assoc in Hlookup. rewrite assoc.
              rewrite lookup_app_r in Hlookup; last (rewrite length_app /=; lia).
              rewrite lookup_app_r; last (rewrite length_app /=; lia).
              rewrite length_app /= in Hlookup.
              rewrite length_app /=.
              assumption.
          - do 4 eexists; eauto. }
        eapply bstepsL_l; last first.
        { eapply IH; [reflexivity|exact Hnodup_mid|done|done]. }
        clear -Hadv_step Hnodup Hnodup_mid.
        inversion Hadv_step; simplify_eq.
        + lazymatch goal with
          | H0: prim_step ?e_p ?σ_p _ ?e_p' ?σ_p' ?efs_p,
            H1: ?π₁0_p++(?τ0_p,Some ?e_p)::?π₂0_p = π₁++(τ,Some (Val v))::π₂,
            H2: ?π₁0_p++(?τ0_p,Some ?e_p')::?π₂0_p = _ |- _ =>
            rename H0 into Hprim_step;
            rename H1 into Heq0;
            rename H2 into Heq_mid;
            rename π₁0_p into π₁0; rename τ0_p into τ0; rename e_p into e;
            rename π₂0_p into π₂0; rename e_p' into e'
          end.
          assert (Hne: length π₁ ≠ length π₁0).
          { intros Heq.
            apply app_inj_1 in Heq0 as [_ Heq0]; last done.
            injection Heq0 as _ ->.
            apply val_stuck in Hprim_step.
            discriminate Hprim_step. }
          assert (∃ π₁0' π₂0', π₁++(τ,None)::π₂ = π₁0' ++ (τ0, Some e) :: π₂0' ∧ π₁_mid++(τ,None)::π₂_mid = π₁0' ++ (τ0, Some e') :: π₂0')
            as (π₁0' & π₂0' & -> & ->).
          { assert (Hlen: length π₁ = length π₁_mid).
            { assert (Hlookup1: (π₁++(τ,Some (Val v))::π₂)!!length π₁ = Some (τ,Some (Val v))).
              { rewrite lookup_app_r // Nat.sub_diag -head_lookup //. }
              assert (Hlookup2: (π₁_mid++(τ,Some (Val v))::π₂_mid)!!length π₁ = Some (τ,Some (Val v))).
              { rewrite -Heq_mid. destruct (decide (length π₁ ≤ length π₁0)) as [Hle|Hgt].
                - assert (length π₁ < length π₁0) by lia.
                  rewrite lookup_app_l // -(lookup_app_l _ ((τ0, Some e) :: π₂0)) //.
                  rewrite Heq0 //.
                - rewrite cons_middle assoc.
                  rewrite lookup_app_r; last (rewrite length_app /=; lia).
                  replace (length (π₁0 ++ [(τ0, Some e')])) with (length (π₁0 ++ [(τ0, Some e)]))
                    by rewrite !length_app //.
                  rewrite -(lookup_app_r (π₁0++[(τ0,Some e)])); last (rewrite length_app /=; lia).
                  rewrite -assoc -cons_middle Heq0 //. }
              destruct (decide (length π₁ ≤ length π₁_mid));
                first destruct (decide (length π₁ = length π₁_mid)); first done.
              (* both cases are impossible *)
              - rewrite lookup_app_l in Hlookup2; last lia.
                apply take_drop_middle in Hlookup2.
                rewrite -Hlookup2 in Hnodup_mid.
                rewrite !fmap_app !fmap_cons /= in Hnodup_mid.
                rewrite NoDup_app in Hnodup_mid. destruct Hnodup_mid as (_&Hnodup_mid&_).
                destruct (Hnodup_mid τ); set_solver.
              - rewrite cons_middle assoc lookup_app_r in Hlookup2; last (rewrite length_app /=; lia).
                apply take_drop_middle in Hlookup2.
                rewrite -Hlookup2 in Hnodup_mid.
                do 2 rewrite fmap_app fmap_cons /= in Hnodup_mid.
                rewrite NoDup_app in Hnodup_mid. destruct Hnodup_mid as (_&_&Hnodup_mid).
                rewrite NoDup_cons in Hnodup_mid. destruct Hnodup_mid as [Hnodup_mid _].
                destruct Hnodup_mid; set_solver. }
            destruct (decide (length π₁ ≤ length π₁0)) as [Hle|Hgt].
            - (* length π₁ < length π₁0, v ∈ π₁0 *)
              (*---------------------------
                |     π₁0    | e |  π₂0   |
                ---------------------------
                |  π₁  | v |     π₂       |
                ---------------------------*)
              exists (take (length π₁) π₁0 ++ (τ, None) :: drop (length π₁+1) π₁0), π₂0.
              split.
              + rewrite -assoc -app_comm_cons.
                f_equal.
                * apply (f_equal (take (length π₁))) in Heq0.
                  rewrite take_app_length take_app_le // in Heq0.
                * rewrite !cons_middle !assoc in Heq0.
                  apply (f_equal (drop (length (π₁++[(τ,Some (Val v))])))) in Heq0.
                  rewrite drop_app_length drop_app_le in Heq0; last (rewrite !length_app /= /pendingOp; lia).
                  rewrite drop_app_le in Heq0; last (rewrite !length_app /= /pendingOp; lia).
                  rewrite -Heq0.
                  rewrite length_app -assoc //.
              + rewrite -assoc -app_comm_cons.
                f_equal.
                * apply (f_equal (take (length π₁_mid))) in Heq_mid.
                  rewrite take_app_length take_app_le in Heq_mid; last by rewrite -Hlen.
                  by rewrite Hlen.
                * rewrite !cons_middle !assoc in Heq_mid.
                  apply (f_equal (drop (length (π₁_mid++[(τ,Some (Val v))])))) in Heq_mid.
                  (* unfold pendingOp for lia *)
                  rewrite drop_app_length drop_app_le in Heq_mid; last (rewrite !length_app /= /pendingOp; lia).
                  rewrite drop_app_le in Heq_mid; last (rewrite !length_app /= /pendingOp; lia).
                  rewrite -Heq_mid.
                  rewrite length_app -assoc /= Hlen //.
            - (* length π₁ > length π₁0, v ∈ π₂0 *)
              (*---------------------------
                |  π₁0  | e |     π₂0     |
                ---------------------------
                |     π₁      | v |  π₂   |
                ---------------------------*)
              exists π₁0, (take (length π₁ - length π₁0 -1) π₂0 ++ (τ, None) :: drop (length π₁ - length π₁0) π₂0).
              split.
              + rewrite app_comm_cons assoc.
                f_equal.
                * apply (f_equal (take (length π₁))) in Heq0.
                  rewrite take_app_length in Heq0.
                  rewrite cons_middle assoc in Heq0.
                  rewrite take_app_ge in Heq0; last (rewrite length_app /= /pendingOp; lia).
                  rewrite -assoc -cons_middle length_app /= in Heq0.
                  rewrite -{1}Heq0. do 3 f_equal.
                  rewrite /pendingOp. lia.
                * apply (f_equal (drop (length π₁+1))) in Heq0.
                  rewrite !cons_middle !assoc in Heq0.
                  replace (length π₁+1) with (length ((π₁ ++ [(τ, Some (Val v))]))) in Heq0 by rewrite length_app //.
                  rewrite drop_app_length in Heq0.
                  rewrite drop_app_ge in Heq0; last (rewrite !length_app /= /pendingOp; lia).
                  rewrite -{1}Heq0. do 2 f_equal.
                  rewrite !length_app /= /pendingOp. lia.
              + rewrite app_comm_cons assoc.
                f_equal.
                * apply (f_equal (take (length π₁_mid))) in Heq_mid.
                  rewrite take_app_length in Heq_mid.
                  rewrite cons_middle assoc in Heq_mid.
                  rewrite take_app_ge in Heq_mid; last (rewrite length_app /= /pendingOp; lia).
                  rewrite -assoc -cons_middle length_app /= in Heq_mid.
                  rewrite -{1}Heq_mid. do 3 f_equal.
                  rewrite /pendingOp. lia.
                * apply (f_equal (drop (length π₁_mid+1))) in Heq_mid.
                  rewrite !cons_middle !assoc in Heq_mid.
                  replace (length π₁_mid+1) with (length ((π₁_mid ++ [(τ, Some (Val v))]))) in Heq_mid by rewrite length_app //.
                  rewrite drop_app_length in Heq_mid.
                  rewrite drop_app_ge in Heq_mid; last (rewrite !length_app /= /pendingOp; lia).
                  rewrite -{1}Heq_mid. do 2 f_equal.
                  rewrite !length_app /= /pendingOp. lia. }
          by eapply adv_step_intermediate.
        + lazymatch goal with
            H0: π₁ ++ (τ, Some (Val v)) :: π₂ = _ |- _ =>
            rename H0 into Heq
          end.
          apply pendingOp_nodup_inj in Heq as (<- & _ & <-); [|done].
          by eapply adv_step_child. }
    change ts with ([]++ts). subst steps_left.
    eapply bstepsL_trans; eassumption.
  Qed.

  Fixpoint trunk_trace (ts_full ts_physical': list (positive*trace)) : list (positive*trace) :=
    match ts_physical' with
    | [] => []
    | hd_physical::ts_physical' =>
      let (ts_full_lin,ts_full_skipped) := take_while (is_lin∘snd) ts_full in
      match ts_full_skipped with
      | [] => [] (* error *)
      | hd_full::ts_full_skipped => (* assert (hd_physical=hd_full) *)
        ts_full_lin++hd_full::trunk_trace ts_full_skipped ts_physical'
      end
    end.

  Lemma trunk_trace_spec (ts_full ts_physical ts_physical': list (positive*trace)) :
    ts_physical = filter (not∘is_lin∘snd) ts_full →
    ts_physical' `prefix_of` ts_physical →
    let ts_full' := trunk_trace ts_full ts_physical' in
    ts_physical' = filter (not∘is_lin∘snd) ts_full' ∧
    ts_full' `prefix_of` ts_full.
  Proof.
    intros ->. revert ts_full.
    induction ts_physical' as [|t ts_physical' IH] => ts_full => Hprefix.
    - rewrite /= filter_nil /=. auto using prefix_nil.
    - set (ts_full_lin := (take_while (is_lin∘snd) ts_full).1).
      set (ts_full_skipped := (take_while (is_lin∘snd) ts_full).2).
       assert (Hnotbegin: ¬ BeginWith (is_lin∘snd) ts_full_skipped) by apply take_while_2_not_BeginWith.

      (* assert (∃ ts_full_skipped', ts_full_skipped = t::ts_full_skipped') as
        [ts_full_skipped' Heq]. *)
      rewrite (take_while_app_1_2 (is_lin∘snd) ts_full) -/ts_full_lin -/ts_full_skipped in Hprefix.
      rewrite filter_app in Hprefix.
      rewrite (filter_False_nil' (is_lin∘snd) ts_full_lin) in Hprefix;
        last apply take_while_1_Forall.
      rewrite left_id in Hprefix.
      destruct (filter (not∘is_lin∘snd) ts_full_skipped) as [|x xs] eqn:Heq';
        first by apply prefix_nil_not in Hprefix.
      pose proof Hprefix as Hprefix'.
      apply prefix_cons_inv_1 in Hprefix' as <-.
      apply prefix_cons_inv_2 in Hprefix.
      destruct ts_full_skipped as [|t' ts_full_skipped'] eqn:Heq; first rewrite filter_nil // in Heq'.
      simpl in Hnotbegin.
      rewrite filter_cons_True // in Heq'.
      injection Heq' as -> <-.

      assert (trunk_trace ts_full (t :: ts_physical') = ts_full_lin++t::trunk_trace ts_full_skipped' ts_physical') as ->.
      { simpl.
        replace (take_while (is_lin∘snd) ts_full) with (ts_full_lin, ts_full_skipped)
          by by destruct (take_while (is_lin∘snd) ts_full).
        rewrite Heq //. }
      simpl.

      destruct (IH _ Hprefix) as [Hfilter_eq Hprefix_full].
      split.
      + rewrite filter_app filter_False_nil'; last apply take_while_1_Forall.
        rewrite left_id filter_cons_True //.
        f_equal. done.
      + rewrite (take_while_app_1_2 (is_lin∘snd) ts_full) -/ts_full_lin -/ts_full_skipped Heq.
        apply prefix_app. apply prefix_cons. assumption.
  Qed.

  (* destruct [pts] into [pts = pts_lin++t::pts'], where [pts_lin] only contains Lin *)
  Lemma obs_cons_inv (pts pts'_filtered : list (positive*trace)) t :
    filter (not ∘ is_lin ∘ snd) pts = t :: pts'_filtered →
    ∃ pts_lin pts', pts = pts_lin++t::pts' ∧ Forall (is_lin ∘ snd) pts_lin
      ∧ pts'_filtered = filter (not ∘ is_lin ∘ snd) pts'.
  Proof.
    intros Hresolve_eq.
    induction pts as [|pt pts IH]; first done.
    rewrite filter_cons in Hresolve_eq.
    case_decide as Hlin.
    - exists [], pts.
      injection Hresolve_eq as -> <-.
      auto.
    - destruct (IH Hresolve_eq) as (pts_lin & pts' & -> & Hall_lin & ->).
      exists (pt::pts_lin), pts'.
      split_and!.
      + by rewrite -app_comm_cons.
      + rewrite Forall_cons. split; last done.
        by apply dec_stable.
      + reflexivity.
  Qed.

  Fixpoint decode_trace (vs : list (val*val)) : list (positive*trace) :=
    match vs with
    | (#(),InjLV (LitV (LitProphecy τ), (#(LitInt opid),arg)))::vs =>
      if bool_decide (0 ≤ opid)%Z then
        (τ,Call (Z.to_nat opid) arg)::decode_trace vs
      else []
    | (#(),InjRV (LitV (LitProphecy τ), res))::vs =>
      (τ,Ret res)::decode_trace vs
    | _ => []
    end.

  Definition is_decode_valid_trace obj config steps_left (ts ts_raw : list (positive*trace)) :=
    is_valid_trace obj config steps_left ts ∧
    (ts = ts_raw ∨ ∃ n, n < length ts_raw ∧ ts = take n ts_raw ∧
        ¬ is_valid_trace obj config steps_left (take (Sₙ n) ts_raw)).

  Lemma decode_valid_trace obj config steps_left (ts_raw : list (positive*trace)) :
    ∃ ts, is_decode_valid_trace obj config steps_left ts ts_raw.
  Proof.
    induction ts_raw as [|t ts_raw IH] using rev_ind.
    { exists []. split;[apply is_valid_trace_nil|by left]. }
    destruct IH as [ts [Hvalid [->|[n (Hn & -> & Hnot_valid_next)]]]].
    - destruct (is_valid_trace_decide obj config steps_left (ts_raw++[t])).
      + exists (ts_raw++[t]).
        split; [done|by left].
      + exists ts_raw.
        split; [done|right].
        exists (length ts_raw). split; [|split].
        * rewrite length_app /=. lia.
        * rewrite take_app_length //.
        * rewrite take_ge //.
          rewrite length_app /=. lia.
    - exists (take n ts_raw).
      split; [done|right].
      exists n. split; [|split].
      + rewrite length_app /=. lia.
      + rewrite take_app_le //. lia.
      + rewrite take_app_le //.
  Qed.

  Lemma decode_valid_trace_call {obj π efs σ} {τ : positive} {n : nat} {v : val} {steps_left : nat} {ts ts_raw' : list (positive*trace)} :
    τ ∉ π.*1 → default default_vr (valid_requests!!n) v →
    is_decode_valid_trace obj (Config π efs σ) (Sₙ steps_left) ts ((τ,Call n v)::ts_raw') →
    ∃ ts', ts = (τ,Call n v)::ts' ∧ is_decode_valid_trace obj (Config (π++[(τ, Some ((ops!!!n: val) obj v))]) efs σ) steps_left ts' ts_raw'.
  Proof.
    intros Hfresh Hvalid_req His_decode.
    destruct His_decode as [Hvalid_trace [-> | Hprefix]].
    - exists ts_raw'. split; first done.
      split; first by eapply is_valid_trace_call_inv.
      by left.
    - destruct Hprefix as [i (Hi & -> & Hnot_valid_next)].
      destruct i as [|i]. (* i ≠ 0*)
      { destruct Hnot_valid_next.
        rewrite /= take_0.
        auto using is_valid_trace_call, is_valid_trace_nil. }
      simpl in *.
      exists (take i ts_raw'). split; first done.
      split; first by eapply is_valid_trace_call_inv.
      right. exists i.
      split; first lia. split; first done.
      simpl. intros Hvalid_trace'. destruct Hnot_valid_next.
      by apply is_valid_trace_call.
  Qed.

  Lemma decode_valid_trace_intermediate {obj π₁ π₂ efs e₁ e₂ σ₁ σ₂ κ ef} {τ : positive} {steps_left : nat} {ts ts_raw : list (positive*trace)} :
    prim_step e₁ σ₁ κ e₂ σ₂ ef →
    is_decode_valid_trace obj (Config (π₁++(τ, Some e₁)::π₂) efs σ₁) (Sₙ steps_left) ts ts_raw →
    ∃ ts', ts' `prefix_of` ts ∧ is_decode_valid_trace obj (Config (π₁++(τ, Some e₂)::π₂) (efs++ef) σ₂) steps_left ts' ts_raw.
  Proof.
    intros Hprim_step His_decode.
    destruct (decode_valid_trace obj (Config (π₁++(τ, Some e₂)::π₂) (efs++ef) σ₂) steps_left ts_raw) as [ts' His_decode'].
    exists ts'. split; last done.
    destruct His_decode as [Hvalid_trace [-> | [n (Hn & -> & Hnot_valid_next)]]];
    destruct His_decode' as [Hvalid_trace' [-> | [n' (Hn' & -> & Hnot_valid_next')]]].
    - done.
    - apply prefix_take.
    - (* ts isn't fully encoded but ts' is -- impossible *)
      destruct Hnot_valid_next.
      eapply is_valid_trace_intermediate; first eassumption.
      eapply is_valid_trace_prefix; last eassumption.
      apply prefix_take.
    - destruct (decide (n' ≤ n)).
      + replace n' with (n' `min` n) by lia.
        rewrite -take_take. apply prefix_take.
      + (* n < n' -- impossible *)
        destruct Hnot_valid_next.
        eapply is_valid_trace_intermediate; first eassumption.
        eapply is_valid_trace_prefix; last eassumption.
        replace (Sₙ n) with ((Sₙ n) `min` n') by lia.
        rewrite -take_take. apply prefix_take.
  Qed.

  Lemma decode_valid_trace_child {obj π efs1 efs2 e₁ e₂ σ₁ σ₂ κ ef}{steps_left : nat} {ts ts_raw : list (positive*trace)} :
    prim_step e₁ σ₁ κ e₂ σ₂ ef →
    is_decode_valid_trace obj (Config π (efs1++e₁::efs2) σ₁) (Sₙ steps_left) ts ts_raw →
    ∃ ts', ts' `prefix_of` ts ∧ is_decode_valid_trace obj (Config π (efs1++e₂::efs2++ef) σ₂) steps_left ts' ts_raw.
  Proof.
    intros Hprim_step His_decode.
    destruct (decode_valid_trace obj (Config π (efs1++e₂::efs2++ef) σ₂) steps_left ts_raw) as [ts' His_decode'].
    exists ts'. split; last done.
    destruct His_decode as [Hvalid_trace [-> | [n (Hn & -> & Hnot_valid_next)]]];
    destruct His_decode' as [Hvalid_trace' [-> | [n' (Hn' & -> & Hnot_valid_next')]]].
    - done.
    - apply prefix_take.
    - destruct Hnot_valid_next.
      eapply is_valid_trace_child; first eassumption.
      eapply is_valid_trace_prefix; last eassumption.
      apply prefix_take.
    - destruct (decide (n' ≤ n)).
      + replace n' with (n' `min` n) by lia.
        rewrite -take_take. apply prefix_take.
      + destruct Hnot_valid_next.
        eapply is_valid_trace_child; first eassumption.
        eapply is_valid_trace_prefix; last eassumption.
        replace (Sₙ n) with ((Sₙ n) `min` n') by lia.
        rewrite -take_take. apply prefix_take.
  Qed.

  Lemma decode_valid_trace_return {obj π₁ π₂ efs σ} {τ : positive} {v : val} {steps_left : nat} {ts ts_raw' : list (positive*trace)} :
    NoDup (π₁++(τ, Some (Val v))::π₂).*1 →
    is_decode_valid_trace obj (Config (π₁++(τ, Some (Val v))::π₂) efs σ) (Sₙ steps_left) ts ((τ,Ret v)::ts_raw') →
    ∃ ts', ts = (τ,Ret v)::ts' ∧ is_decode_valid_trace obj (Config (π₁++(τ, None)::π₂) efs σ) steps_left ts' ts_raw'.
  Proof.
    intros Hnodup His_decode.
    destruct His_decode as [Hvalid_trace [-> | Hprefix]].
    - exists ts_raw'. split; first done.
      split; first by eapply is_valid_trace_return_inv.
      by left.
    - destruct Hprefix as [n (Hn & -> & Hnot_valid_next)].
      destruct n as [|n]. (* n ≠ 0*)
      { destruct Hnot_valid_next.
        rewrite /= take_0.
        auto using is_valid_trace_return, is_valid_trace_nil. }
      simpl in *.
      exists (take n ts_raw'). split; first done.
      split; first by eapply is_valid_trace_return_inv.
      right. exists n.
      split; first lia. split; first done.
      simpl. intros Hvalid_trace'. destruct Hnot_valid_next.
      by apply is_valid_trace_return.
  Qed.

  Definition proph_trace obj config (p : proph_id) (steps_left : nat) (ts : list (positive*trace)) : iProp Σ :=
    ∃ vs, proph p vs ∗ ⌜ is_decode_valid_trace obj config steps_left ts (decode_trace vs) ⌝.

  Lemma proph_trace_valid_trace obj config p steps_left ts :
    proph_trace obj config p steps_left ts ⊢ ⌜is_valid_trace obj config steps_left ts⌝.
  Proof. iDestruct 1 as (v) "[_ [$ _]]". Qed.

  Lemma wp_new_proph_trace s E :
    {{{ True }}}
      NewProph @ s; E
    (* the structure of this lemma allows choosing [obj] after [NewProph] *)
    {{{ p, RET (LitV (LitProphecy p)); ∀ obj config steps_left, ∃ ts, proph_trace obj config p steps_left ts }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_new_proph with "[//]") as (vs p) "Hproph".
    iApply "HΦ". iIntros (obj config steps_left).
    destruct (decode_valid_trace obj config steps_left (decode_trace vs)) as [ts Hts].
    iFrame. iExists ts. done.
  Qed.

  Lemma wp_resolve_proph_trace_call obj π efs σ (p : proph_id) steps_left (τ : positive) (n: nat) (v : val) ts s E :
    τ ∉ π.*1 → default default_vr (valid_requests!!n) v →
    {{{ proph_trace obj (Config π efs σ) p (Sₙ steps_left) ts }}}
      resolve_proph: #p to: InjLV (#(LitProphecy τ),(#n,v)) @ s; E
    {{{ ts', RET #(); ⌜ ts = (τ,Call n v)::ts' ⌝ ∗ proph_trace obj (Config (π++[(τ,Some ((ops!!!n: val) obj v))]) efs σ) p steps_left ts' }}}.
  Proof.
    iIntros (Hfresh Hvalid Φ) "Hproph HΦ".
    iDestruct "Hproph" as (vs) "[Hproph %His_decode]".
    iApply (wp_resolve with "Hproph"); first done.
    wp_pures. iIntros "!>" (vs' ->) "Hproph".
    rewrite /= bool_decide_eq_true_2 in His_decode; last lia.
    rewrite Nat2Z.id in His_decode.
    destruct (decode_valid_trace_call Hfresh Hvalid His_decode) as (ts' & Hresolve & His_decode').
    iApply ("HΦ" $! ts'). by iFrame.
  Qed.

  Lemma wp_resolve_proph_trace_intermediate obj π₁ π₂ efs σ₁ σ₂ κ ef (p : proph_id) steps_left (τ : positive) (e₁ e₂ : expr) ts :
    prim_step e₁ σ₁ κ e₂ σ₂ ef →
    proph_trace obj (Config (π₁++(τ,Some e₁)::π₂) efs σ₁) p (Sₙ steps_left) ts
    ⊢ ∃ ts', ⌜ts' `prefix_of` ts⌝ ∗ proph_trace obj (Config (π₁++(τ,Some e₂)::π₂) (efs++ef) σ₂) p steps_left ts'.
  Proof.
    iIntros (Hprim_step) "Hproph".
    iDestruct "Hproph" as (vs) "[Hproph %His_decode]".
    destruct (decode_valid_trace_intermediate Hprim_step His_decode) as (ts' & Hresolve & His_decode').
    iFrame. iExists ts'. done.
  Qed.

  Lemma wp_resolve_proph_trace_child obj π efs1 efs2 σ₁ σ₂ κ ef (p : proph_id) steps_left (e₁ e₂ : expr) ts :
    prim_step e₁ σ₁ κ e₂ σ₂ ef →
    proph_trace obj (Config π (efs1++e₁::efs2) σ₁) p (Sₙ steps_left) ts
    ⊢ ∃ ts', ⌜ts' `prefix_of` ts⌝ ∗ proph_trace obj (Config π (efs1++e₂::efs2++ef) σ₂) p steps_left ts'.
  Proof.
    iIntros (Hprim_step) "Hproph".
    iDestruct "Hproph" as (vs) "[Hproph %His_decode]".
    destruct (decode_valid_trace_child Hprim_step His_decode) as (ts' & Hresolve & His_decode').
    iFrame. iExists ts'. done.
  Qed.

  Lemma wp_resolve_proph_trace_return obj π₁ π₂ efs σ (p : proph_id) steps_left (τ : positive) (v : val) ts s E :
    NoDup (π₁++(τ,Some (Val v))::π₂).*1 →
    {{{ proph_trace obj (Config (π₁++(τ,Some (Val v))::π₂) efs σ) p (Sₙ steps_left) ts }}}
      resolve_proph: #p to: InjRV (#(LitProphecy τ),v) @ s; E
    {{{ ts', RET #(); ⌜ ts = (τ,Ret v)::ts' ⌝ ∗ proph_trace obj (Config (π₁++(τ,None)::π₂) efs σ) p steps_left ts' }}}.
  Proof.
    iIntros (Hnodup Φ) "Hproph HΦ".
    iDestruct "Hproph" as (vs) "[Hproph %His_decode]".
    iApply (wp_resolve with "Hproph"); first done.
    wp_pures. iIntros "!>" (vs' ->) "Hproph".
    simpl in His_decode.
    destruct (decode_valid_trace_return Hnodup His_decode) as (ts' & Hresolve & His_decode').
    iApply ("HΦ" $! ts'). by iFrame.
  Qed.

  Canonical Structure S0 := leibnizO S.

  Definition Nlogatom := nroot .@ "iris_logatom.program_logic.atomic".

  Definition P_state γ s : iProp Σ :=
    ∃ (γπ γϕ γs γe : gname), own γ (to_agree (γπ,γϕ,γs,γe)) ∗ own γs (◯E s).

  Definition op_au γ n y Φ : iProp Σ :=
    AU <{ ∃∃ s : S, P_state γ s }> @ ⊤ ∖ ↑Nlogatom, ∅
      <{ ∀∀ (s' : S) (y' : val), P_state γ s' ∗ ⌜default default_rr (request_responses!!n) s y s' y'⌝, COMM Φ y' }>.

  (* For each pending operation, if it hasn't linearized, then there is an AU;
     if it has linearized, then there is a receipt. *)
  Local Definition interpret γ (pts : list (positive*trace)) τ Φ : iProp Σ :=
    match filter (λ t, t.1 = τ) pts with
    | [] => True
    | (_,Call _ _)::_ => False
    | (_,Lin n v _) ::_ => op_au γ n v Φ
    | (_,Ret v)::_ => Φ v
    end.

  Definition is_P_inv γ obj p : iProp Σ :=
    (* pts is the full trace consisting of Call, Lin, and Ret *)
    ∃ (γπ γϕ γs γe : gname) (s : S) π Φs (children : list expr) σ pts steps_left,
    (* The prophesied trace is generated by a program *)
    (* Ownerships *)
      proph_trace obj (Config π children σ) p steps_left (filter (not ∘ is_lin ∘ snd) pts)
    ∗ own_state σ ∗ own γ (to_agree (γπ,γϕ,γs,γe))
    ∗ ghost_map_auth γπ 1 (list_to_map (pendingOp_active π))
    ∗ own_receipt_auth γϕ Φs
    ∗ own γs (●E s)
    ∗ ghost_map_auth γe 1 (list_to_imap 0 children)
    ∗ (▷^steps_left False) (* A model-level time receipt *)
    ∗ ⌜dom (list_to_map (pendingOp_active π) : gmap positive expr) = dom Φs⌝
    (* An exclusive token for each pending operation *)
    ∗ ([∗ list] τ ∈ π.*1, ghost_id_token τ)
    (* The interpretation of each pending operation *)
    ∗ ([∗ map] τ ↦ Φ ∈ Φs, interpret γ pts τ Φ)
    (* all pending operations in pts are covered by Φs; Φs may contain more operations
      that trace_pendingOp because some operations may diverge *)
    ∗ ⌜trace_pendingOp pts ⊆ dom Φs⌝
    (* The trace of each operation is valid *)
    ∗ ⌜per_tag_partial_linearized pts⌝
    (* Future operations are linearizable *)
    ∗ ⌜∃ s', rtcL model_step s s' (filter (is_lin ∘ snd) pts)⌝
    (* Configuration is not stuck *)
    ∗ ⌜config_safe ops obj π children σ⌝.

  Definition is_P γ v : iProp Σ :=
    ∃ obj (p : proph_id), ⌜v = (obj,#p)%V⌝ ∗ inv Nlogatom (is_P_inv γ obj p).

  Global Instance is_P_persistent γ v : Persistent (is_P γ v).
  Proof. apply _. Qed.
  Global Instance P_state_timeless γ s : Timeless (P_state γ s).
  Proof. apply _. Qed.

  (* Ghost-id token for a forked child thread: claims that [i] currently maps
     to expression [e] in the children ghost_map of invariant [γ]. *)
  Definition child_token γ (i : nat) (e : expr) : iProp Σ :=
    ∃ (γπ γϕ γs γe : gname),
      own γ (to_agree (γπ, γϕ, γs, γe)) ∗ i ↪[γe] e.

  Lemma child_token_alloc_many γ γπ γϕ γs γe (efs : list expr) :
    ∀ (children : list expr),
      own γ (to_agree (γπ, γϕ, γs, γe)) -∗
      ghost_map_auth γe 1 (list_to_imap 0 children) ==∗
      ghost_map_auth γe 1 (list_to_imap 0 (children ++ efs)) ∗
      [∗ list] i↦e ∈ efs, child_token γ (length children + i) e.
  Proof.
    induction efs as [|e efs IH] using rev_ind; iIntros (children) "#Hγ H●".
    - iModIntro. rewrite app_nil_r /=. iFrame "H●".
    - iMod (IH with "Hγ H●") as "[H● H◯]".
      iMod (ghost_map_insert (length (children ++ efs)) e with "H●") as "[H● He]".
      { rewrite lookup_list_to_imap_0. apply lookup_ge_None_2. done. }

      iModIntro.
      rewrite -list_to_imap_0_snoc -assoc_L. iFrame "H●".
      rewrite big_sepL_snoc -length_app. iFrame "#∗".
  Qed.

  (* A forked child thread, witnessed by [child_token γ τ e], satisfies WP
     with the trivially-true post-condition. The proof is a Löb induction
     on the child's current expression: at each step we open the invariant,
     use [config_safe_child_not_stuck] for reducibility, take a prim_step,
     update children (ghost-map update on [τ] plus fresh tokens for any new
     forks via [child_token_alloc_many]), close the invariant, and recurse
     through IH for both the continuation and each freshly forked thread. *)
  Lemma wp_forked_child γ obj p i e :
    inv Nlogatom (is_P_inv γ obj p) -∗
    child_token γ i e -∗
    WP e {{ _, True }}.
  Proof.
    iIntros "#His_P Htok".
    iLöb as "IH" forall (i e).
    destruct (to_val e) as [v|] eqn:He.
    { rewrite -(of_to_val e v) //. iApply wp_value. done. }

    iApply wp_inv_open_maybe.
    iInv "His_P" as "Hinv" "Hclose".
    iDestruct "Hinv" as (γπ' γϕ' γs' γe' s π Φs children σ1 pts steps_left)
      "(Hproph & >Hown_state & >#Hγ' & Hop● & HΦ● & Hs● & >Hchildren● & Htime_receipt & >%Hdom & >Hfresh & Hinterps & >(%Hpending & %Hper_tag_lin & %Hmsteps & %Hconfig_safe))".
    iDestruct "Htok" as (γπ γϕ γs γe) "[#Hγ Hfrag]".
    iCombine "Hγ Hγ'" gives %Heq%to_agree_op_inv_L.
    inversion Heq. subst γπ' γϕ' γs' γe'. clear Heq. iClear "Hγ'".
    iDestruct (ghost_map_lookup with "Hchildren● Hfrag") as %Hi_lookup.
    rewrite lookup_list_to_imap_0 in Hi_lookup.
    destruct (list_elem_of_split_length _ _ _ Hi_lookup) as (efs1 & efs2 & -> & ->).

    (* reducibility via config_safe_child_not_stuck *)
    apply config_safe_child_not_stuck in Hconfig_safe as Hnot_stuck.
    assert (He_red : reducible e σ1).
    { destruct Hnot_stuck as [Hfalse|]; try done.
      rewrite /= He in Hfalse. by inversion Hfalse. }

    iMod (lang_completeness with "[Hown_state]") as "H".
    { exact He_red. } { iFrame "Hown_state". }
    iModIntro. iDestruct "H" as "[H | H]".

    - (* first redex is atomic *)
      iLeft.
      iDestruct "H" as (K e1 ? Heq Hnotval Hatomic) "H". subst e.
      iExists K, e1. do 3 (iSplit; first done).
      iApply "H". iIntros "!> _" (κ v2 σ2 efs Hbase).
      destruct steps_left as [|steps_left]; first done.

      (* update τ ↦ e to τ ↦ e2 in the children ghost_map *)
      iMod (ghost_map_update (K (Val v2)) with "Hchildren● Hfrag") as "[Hchildren● Hfrag]".
      replace (<[length efs1:=K (Val v2)]> (list_to_imap 0 (efs1 ++ K e1 :: efs2))) with
        (list_to_imap 0 (efs1 ++ K (Val v2) :: efs2)); last first.
      { rewrite !list_to_imap_app !list_to_imap_cons.
        rewrite insert_union_r.
        - rewrite right_id_L insert_insert_eq //.
        - rewrite lookup_list_to_imap_0 lookup_ge_None //. }
      (* allocate fresh child_tokens for each newly forked thread *)
      iMod (child_token_alloc_many _ _ _ _ _ efs with "Hγ Hchildren●") as "[Hchildren● Hnew_tokens]".
      iEval (rewrite -assoc_L -app_comm_cons) in "Hchildren●".
      eapply fill_step in Hbase as Hprim.
      (* extend config_safe over the new forked threads *)
      pose proof (config_safe_child ops obj π efs1 efs2 (K e1) (K (Val v2)) σ1 σ2 κ efs
                    Hprim Hconfig_safe) as Hconfig_safe'.
      (* update proph_trace *)
      iDestruct (wp_resolve_proph_trace_child _ _ efs1 efs2 _ _ _ _ _ _ _ _ _ Hprim with "Hproph") as (pts'_filtered) "[%Hresolve_eq Hproph]".

      iModIntro. iSplitR "Hnew_tokens"; last first.
      { (* child threads *)
        iApply (big_sepL_impl with "Hnew_tokens").
        iIntros "!#" (???) "Htok".
        iApply ("IH" with "Htok"). }

      iIntros "Hown_state".
      iMod ("Hclose" with "[-Hfrag]") as "_".
      { iNext.
        destruct (trunk_trace_spec pts (filter (not ∘ is_lin ∘ snd) pts) pts'_filtered) as [Hfilter Hpts'_prefix_pts].
        { reflexivity. } { apply Hresolve_eq. }
        remember (trunk_trace pts pts'_filtered) as pts'.
        iExists γπ, γϕ, γs, γe, s, π, Φs,
                (efs1 ++ K (Val v2) :: efs2 ++ efs),
                σ2, pts', steps_left.
        iSplitL "Hproph".
        { rewrite Hfilter. done. }
        iFrame "Hown_state Hγ Hop● HΦ● Hs● Hchildren● Htime_receipt".
        iSplit; first done.
        iFrame "Hfresh".
        iSplitL "Hinterps".
        { iApply (big_sepM_mono with "Hinterps").
          iIntros (τ0 Φ0 Hlookup0) "Hinterp".
          rewrite /interpret.
          apply (prefix_filter (λ t, t.1 = τ0)) in Hpts'_prefix_pts.
          destruct (filter (λ t, t.1 = τ0) pts) as [|[? [ | | ]]] eqn:Heqfilter_pts.
          - apply prefix_nil_inv in Hpts'_prefix_pts as ->. done.
          - done.
          - destruct (filter (λ t, t.1 = τ0) pts'); first done.
            apply prefix_cons_inv_1 in Hpts'_prefix_pts as ->. done.
          - destruct (filter (λ t, t.1 = τ0) pts'); first done.
            apply prefix_cons_inv_1 in Hpts'_prefix_pts as ->. done. }
        iSplit. { iPureIntro. etrans; last exact Hpending. by apply trace_pendingOp_prefix. }
        iSplit. { iPureIntro. eauto using per_tag_partial_linearized_prefix. }
        iSplit. { iPureIntro. eauto using model_steps_prefix, prefix_filter. }
        iPureIntro. exact Hconfig_safe'. }

      iModIntro.
      iApply ("IH" $! (length efs1) (K (Val v2))).
      rewrite /child_token. by iFrame "Hγ Hfrag".

    - (* first redex is not atomic *)
      iRight.
      iDestruct "H" as "[Hown_state H]".
      iMod ("Hclose" with "[-H Hfrag]") as "_".
      { iNext. iFrame "∗#". auto. }
      clear -HModelDecidable.
      remember (length efs1) as i eqn:Heq. clear efs1 Heq.
      iModIntro. iApply "H".
      iNext. iIntros "Hlc" (e2 efs) "H".
      iInv "His_P" as "Hinv" "Hclose".
      iDestruct "Hinv" as (γπ' γϕ' γs' γe' s π Φs children σ1 pts steps_left)
        "(>Hproph & >Hown_state & >#Hγ' & Hop● & HΦ● & Hs● & >Hchildren● & Htime_receipt & >%Hdom & >Hfresh & Hinterps & >(%Hpending & %Hper_tag_lin & %Hmsteps & %Hconfig_safe))".
      iCombine "Hγ Hγ'" gives %Heq%to_agree_op_inv_L.
      inversion Heq. subst γπ' γϕ' γs' γe'. clear Heq. iClear "Hγ'".
      iDestruct (ghost_map_lookup with "Hchildren● Hfrag") as %Hi_lookup.
      rewrite lookup_list_to_imap_0 in Hi_lookup.
      destruct (list_elem_of_split_length _ _ _ Hi_lookup) as (efs1 & efs2 & -> & ->).

      iMod ("H" with "Hown_state") as (κ σ2) "[%Hprim Hown_state]".
      (* update τ ↦ e to τ ↦ e2 in the children ghost_map *)
      iMod (ghost_map_update e2 with "Hchildren● Hfrag") as "[Hchildren● Hfrag]".
      replace (<[length efs1:=e2]> (list_to_imap 0 (efs1 ++ e :: efs2))) with
        (list_to_imap 0 (efs1 ++ e2 :: efs2)); last first.
      { rewrite !list_to_imap_app !list_to_imap_cons.
        rewrite insert_union_r.
        - rewrite right_id_L insert_insert_eq //.
        - rewrite lookup_list_to_imap_0 lookup_ge_None //. }
      (* allocate fresh child_tokens for each newly forked thread *)
      iMod (child_token_alloc_many _ _ _ _ _ efs with "Hγ Hchildren●") as "[Hchildren● Hnew_tokens]".
      iEval (rewrite -assoc_L -app_comm_cons) in "Hchildren●".
      (* extend config_safe over the new forked threads *)
      pose proof (config_safe_child ops obj π efs1 efs2 e e2 σ1 σ2 κ efs
                    Hprim Hconfig_safe) as Hconfig_safe'.
      (* update proph_trace, use the later credit to strip a later in "Htime_receipt" *)
      iMod (lc_fupd_elim_later with "Hlc Htime_receipt") as "Htime_receipt".
      destruct steps_left as [|steps_left]; first done.
      iDestruct (wp_resolve_proph_trace_child _ _ efs1 efs2 _ _ _ _ _ _ _ _ _ Hprim with "Hproph") as (pts'_filtered) "[%Hresolve_eq Hproph]".

      iMod ("Hclose" with "[-Hfrag Hnew_tokens]") as "_".
      { iNext.
        destruct (trunk_trace_spec pts (filter (not ∘ is_lin ∘ snd) pts) pts'_filtered) as [Hfilter Hpts'_prefix_pts].
        { reflexivity. } { apply Hresolve_eq. }
        remember (trunk_trace pts pts'_filtered) as pts'.
        iExists γπ, γϕ, γs, γe, s, π, Φs,
                (efs1 ++ e2 :: efs2 ++ efs),
                σ2, pts', steps_left.
        iSplitL "Hproph".
        { rewrite Hfilter. done. }
        iFrame "Hown_state Hγ Hop● HΦ● Hs● Hchildren● Htime_receipt".
        iSplit; first done.
        iFrame "Hfresh".
        iSplitL "Hinterps".
        { iApply (big_sepM_mono with "Hinterps").
          iIntros (τ0 Φ0 Hlookup0) "Hinterp".
          rewrite /interpret.
          apply (prefix_filter (λ t, t.1 = τ0)) in Hpts'_prefix_pts.
          destruct (filter (λ t, t.1 = τ0) pts) as [|[? [ | | ]]] eqn:Heqfilter_pts.
          - apply prefix_nil_inv in Hpts'_prefix_pts as ->. done.
          - done.
          - destruct (filter (λ t, t.1 = τ0) pts'); first done.
            apply prefix_cons_inv_1 in Hpts'_prefix_pts as ->. done.
          - destruct (filter (λ t, t.1 = τ0) pts'); first done.
            apply prefix_cons_inv_1 in Hpts'_prefix_pts as ->. done. }
        iSplit. { iPureIntro. etrans; last exact Hpending. by apply trace_pendingOp_prefix. }
        iSplit. { iPureIntro. eauto using per_tag_partial_linearized_prefix. }
        iSplit. { iPureIntro. eauto using model_steps_prefix, prefix_filter. }
        iPureIntro. exact Hconfig_safe'. }

      iModIntro. iSplitL "Hfrag".
      { iApply ("IH" $! (length efs1) e2).
        rewrite /child_token. by iFrame "Hγ Hfrag". }
      iApply (big_sepL_impl with "Hnew_tokens").
      iIntros "!#" (???) "Htok".
      iApply ("IH" with "Htok").
  Qed.

  Lemma linearize_helping {pts_lin pts' : list (positive*trace)} {γ s} {Φs : gmap positive (val → iProp Σ)} {γπ γϕ γs γe : gname} :
    Forall (is_lin ∘ snd) pts_lin →
    per_tag_partial_linearized (pts_lin ++ pts') →
    (∃ s', rtcL model_step s s' (filter (is_lin ∘ snd) (pts_lin ++ pts'))) →
    Forall (λ t, t.1 ∈ dom Φs) pts_lin →
    own γ (to_agree (γπ, γϕ, γs, γe)) -∗ own γs (●E s) -∗
    ([∗ map] τ0↦Φ0 ∈ Φs, interpret γ (pts_lin ++ pts') τ0 Φ0) -∗
    ∃ s_end, |={⊤ ∖ ↑Nlogatom}=> ∃ s', ⌜rtcL model_step s' s_end (filter (is_lin ∘ snd) pts')⌝ ∗ own γs (●E s') ∗
        ([∗ map] τ ↦ Φ ∈ Φs, interpret γ pts' τ Φ).
  Proof.
    iIntros (Hpts_lin Hper_tag_lin'' Hmsteps'' Hpts_lin_in_dom) "#Hγ Hs● Hinterps".
    destruct Hmsteps'' as [s' Hmsteps]. iExists s'.
    rename Hper_tag_lin'' into Hper_tag_lin.
    iInduction pts_lin as [|pt_lin pts_lin] "IH" forall (s Hmsteps Φs Hpts_lin_in_dom).
    { simpl. iModIntro. by iFrame. }
    (* extract the head of pts_lin *)
    rewrite Forall_cons in Hpts_lin. destruct Hpts_lin as [Hpt_lin Hpts_lin].
    destruct pt_lin as [τ_pt_lin [|n_pt_lin v_pt_lin v'_pt_lin|]]; simpl in Hpt_lin; [done| |done].
    rewrite Forall_cons in Hpts_lin_in_dom.
    destruct Hpts_lin_in_dom as [Hpt_lin_in_dom Hpts_lin_in_dom].
    assert (is_Some (Φs !! τ_pt_lin)) as [Φ_pt_lin Hlookup] by by apply elem_of_dom.
    iEval (rewrite (big_sepM_delete _ Φs (τ_pt_lin)) //) in "Hinterps".
    iDestruct "Hinterps" as "[Hinterp Hinterps]".
    iEval (rewrite /interpret filter_cons_True) in "Hinterp".

    (* linearize the head of pts_lin *)
    rewrite -app_comm_cons filter_cons_True // in Hmsteps.
    apply rtcL_cons_inv in Hmsteps.
    destruct Hmsteps as (s_mid & [_ Hrf]%model_step_inv & Hmsteps).
    rewrite -app_comm_cons in Hper_tag_lin.
    assert (Hτ_pt_lin_unique: Forall (λ t, t.1 ≠ τ_pt_lin) pts_lin).
    { clear - Hpts_lin Hper_tag_lin. apply dec_stable. intros HFalse.
      apply not_Forall_Exists,Exists_exists in HFalse; last apply _.
      destruct HFalse as (t & Hin & Htag).
      apply list_elem_of_split in Hin. apply dec_stable in Htag.
      destruct Hin as (l1 & l2 & ->).
      rewrite Forall_app Forall_cons in Hpts_lin. destruct Hpts_lin as (_&Hpt_lin&_).
      destruct t as [τ [|??|]]; simpl in Hpt_lin; [done| |done].
      simpl in Htag. subst τ.
      destruct (Hper_tag_lin τ_pt_lin) as (? & ? & ? & Hsubstr).
      rewrite filter_cons_True // in Hsubstr.
      rewrite -(assoc (++)) -app_comm_cons filter_app filter_cons_True // in Hsubstr.
      apply (substr_filter (is_lin ∘ snd)) in Hsubstr.
      rewrite {1}filter_cons_True // filter_app {1}filter_cons_True // in Hsubstr.
      rewrite {1}filter_cons_False in Hsubstr; last auto.
      rewrite {1}filter_cons_True // in Hsubstr.
      rewrite {1}filter_cons_False in Hsubstr; last auto.
      rewrite filter_nil in Hsubstr.
      apply substr_length in Hsubstr.
      rewrite length_cons length_app length_cons /= in Hsubstr.
      lia. }
    pose proof (per_tag_partial_linearized_filter_lin _ _ _ _ _ Hper_tag_lin) as Hfilter.
    rewrite !filter_app !(filter_False_nil _ pts_lin) // left_id_L in Hfilter.
    apply per_tag_partial_linearized_cons in Hper_tag_lin.
    iMod "Hinterp" as (x) "[HPstate [_ Hcomm]]".
    iDestruct "HPstate" as (γπ' γϕ' γs' γe') "[#Hγ' Hs◯]".
    iCombine "Hγ Hγ'" gives %Hγ_eq%to_agree_op_inv_L.
    simplify_eq.
    iCombine "Hs● Hs◯" gives %<-%excl_auth_agree_L.
    iMod (own_update_2 with "Hs● Hs◯") as "[Hs● Hs◯]".
    { apply (excl_auth_update _ _ s_mid). }
    iMod ("Hcomm" with "[$Hγ $Hs◯ //]") as "Hinterp".

    (* linearize the tail of pts_lin (using "IH") *)
    iSpecialize ("IH" with "[//] [//] [//]").
    (* FIXME: (Iris bug?) expressions put after [$!] don't trigger typeclass search *)
    set (Φs_delete := (delete τ_pt_lin Φs)).
    iSpecialize ("IH" $! Φs_delete with "[]"); subst Φs_delete.
    { iPureIntro.
      clear - Hpts_lin_in_dom Hτ_pt_lin_unique.
      induction pts_lin as [|pt_lin pts_lin IH]; first done.
      rewrite Forall_cons.
      rewrite !Forall_cons in Hpts_lin_in_dom, Hτ_pt_lin_unique.
      destruct Hpts_lin_in_dom as [? ?].
      destruct Hτ_pt_lin_unique as [? ?].
      split; last auto.
      rewrite dom_delete_L. set_solver. }
    iMod ("IH" with "Hs● [Hinterps]") as (s_end) "(Hmsteps' & Hs● & Hinterps)".
    { iApply (big_sepM_mono with "Hinterps").
      iIntros (τ0 Φ0 Hlookup0) "Hinterp".
      iEval (rewrite /interpret -app_comm_cons) in "Hinterp".
      rewrite /interpret filter_cons_False.
      - iExact "Hinterp".
      - simpl. intros ->. rewrite lookup_delete_eq // in Hlookup0. }

    iModIntro. iFrame "Hmsteps' Hs●".
    iEval (rewrite (big_sepM_delete _ Φs (τ_pt_lin)) //).
    iSplitL "Hinterp".
    - rewrite /interpret. by destruct Hfilter as [-> | ->].
    - iFrame.
  Qed.

  Theorem logatom_init_compelete :
    to_val init = None →
    (∀ σ, sequential init σ) →
    library_initializable init valid_obj → library_linearizable ops valid_obj →
    {{{ True }}} wrap_init init {{{ γ r, RET r; is_P γ r ∗ P_state γ s_init }}}.
  Proof.
    intros Hinit_nv Hnofork Hinit Hlin.
    iIntros (Φ) "_ HΦ". rewrite /wrap_init /=.
    wp_pures. wp_apply (wp_new_proph_trace with "[//]") as (p) "Hproph".
    wp_bind init.
    iApply (hoare_completeness_nofork _ ∅).
    { apply Hinit_nv. } { apply Hinit. } { apply Hnofork. } { iApply own_state_empty. }
    iIntros "!>" (obj σ) "[Hown_state %Hvalid_obj]".
    wp_pures.
    iMod (ghost_map_alloc_empty (K:=positive)) as (γπ) "Hop●".
    iMod (own_receipt_alloc_empty) as (γϕ) "HΦ●".
    iMod (own_alloc (●E s_init ⋅ ◯E s_init)) as (γs) "[Hs● Hs◯]"; first apply excl_auth_valid.
    iMod (ghost_map_alloc_empty (K:=nat)) as (γe) "Hchildren●".
    iDestruct (bi.laterN_False) as (steps_left) "Htime_receipt".
    iMod (own_alloc (to_agree (γπ,γϕ,γs,γe))) as (γ) "#Hγ"; first done.
    iMod (inv_alloc Nlogatom ⊤ (is_P_inv γ obj p)%I with "[Hγ Hop● HΦ● Hs● Hchildren● Hproph Hown_state]") as "His_P".
    { iDestruct ("Hproph" $! obj (Config [] [] σ) steps_left) as (pts_physical) "Hproph".
      iDestruct (proph_trace_valid_trace with "Hproph") as %Hvalid_trace.
      destruct Hvalid_trace as [config' Hadv_steps%rtcL_bstepsL_2].
      destruct (Hlin obj σ config' pts_physical Hvalid_obj Hadv_steps) as (Hnot_stuck & Htrace_lin).
      destruct Htrace_lin as [_ [pts (-> & Hper_tag_lin & Hmsteps)]].
      iNext.
      iExists γπ, γϕ, γs, γe, s_init, [], ∅, [], σ, pts, steps_left.
      iFrame "Hproph Hown_state Hγ Hop● HΦ● Hs● Hchildren● Htime_receipt".
      do 3 (iSplit; first done).
      iSplit. { iPureIntro.
        rewrite dom_empty_L. rewrite per_tag_linearized_trace_pendingOp_empty //. }
      eauto 6 using config_safe_intro, per_tag_linearized_per_tag_partial_linearized. }
    iApply "HΦ". iModIntro.
    rewrite /is_P /P_state. by iFrame "His_P Hγ Hs◯".
  Qed.

  Theorem logatom_op_complete (n : nat) :
    library_linearizable ops valid_obj →
    ∀ γ (x y: val), default default_vr (valid_requests!!n) y →
      is_P γ x ⊢
      <<{ ∀∀ s, P_state γ s }>>
        wrap_op n (ops!!!n) x y @ ↑Nlogatom
      <<{ ∃∃ s' y', P_state γ s' ∗ ⌜default default_rr (request_responses!!n) s y s' y'⌝ | RET y' }>>.
  Proof.
    intros Hlin.
    iIntros (γ x y Hvalid_req_y) "#His_P". simpl.
    iDestruct "His_P" as (obj p) "[-> His_P]".
    iIntros (Φ) "AU".
    wp_lam. wp_pures.

    (* allocate an exclusive token for current operation *)
    wp_apply (wp_new_token with "[//]") as (τ) "Hτ_token".
    wp_pure credit:"Hlc".
    wp_pures.

    (****************************************************)
    (* add a new pending operation to π                 *)
    (****************************************************)

    wp_bind (resolve_proph: _ to: _)%E.
    iInv "His_P" as "Hinv" "Hclose".
    iDestruct "Hinv" as (γπ γϕ γs γe s π Φs children σ pts steps_left)
      "(>Hproph & Hown_state & >#Hγ & Hop● & HΦ● & Hs● & Hchildren● & Htime_receipt & >%Hdom & >Hfresh & Hinterps & >(%Hpending & %Hper_tag_lin & %Hmsteps & %Hconfig_safe))".
    iDestruct (ghost_id_fresh with "Hτ_token Hfresh") as %Hτ_fresh.
    iMod (lc_fupd_elim_later with "Hlc Htime_receipt") as "Htime_receipt".
    destruct steps_left as [|steps_left]; first done.
    wp_apply (wp_resolve_proph_trace_call with "Hproph") as (pts'_filtered) "[%Hresolve_eq Hproph]"; [done..|].

    (* destruct [pts] into [pts = pts_lin++Call::pts'], where [pts_lin] only contains Lin *)
    destruct (obs_cons_inv _ _ _ Hresolve_eq) as (pts_lin & pts' & -> & Hpts_lin & ->).

    (* prime variants of Hpending, Hper_tag_lin, Hmsteps, about (τ, Call y)::pts' *)
    assert (per_tag_partial_linearized ((τ, Call n y)::pts') ∧ trace_pendingOp ((τ, Call n y)::pts') ⊆ dom Φs
        ∧ Forall (λ t, t.1 ∈ dom Φs) pts_lin) as (Hper_tag_lin' & Hpending' & Hpts_lin_in_dom).
    { clear - Hpending Hpts_lin Hper_tag_lin.
      induction pts_lin as [|pt_lin pts_lin IH]; first (simpl in *; auto).
      rewrite Forall_cons in Hpts_lin. destruct Hpts_lin as [Hpt_lin Hpts_lin].
      destruct pt_lin as [τ' [|i v v'|]]; simpl in Hpt_lin; [done| |done].
      rewrite -app_comm_cons in Hpending,Hper_tag_lin.
      pose proof (trace_pendingOp_lin_elem_of τ' i v v' (pts_lin++(τ,Call n y)::pts')) as Hτ'_in.
      eapply elem_of_weaken in Hτ'_in; last exact Hpending.
      assert (Hpending': trace_pendingOp (pts_lin++(τ,Call n y)::pts') ⊆ dom Φs).
      { etrans; last exact Hpending.
        by apply trace_pendingOp_lin. }
      apply per_tag_partial_linearized_cons in Hper_tag_lin.
      destruct IH as (?&?&?); [assumption..|].
      rewrite Forall_cons.
      split_and!; done. }

    (* linearize operations in [pts_lin] *)
    iDestruct (linearize_helping Hpts_lin Hper_tag_lin Hmsteps with "Hγ Hs● Hinterps")
      as (s_end) ">(%s' & %Hmsteps' & Hs● & Hinterps)".
    { exact Hpts_lin_in_dom. }

    (* insert new operation *)
    iMod (ghost_map_insert τ ((ops!!!n: val) obj y) with "Hop●") as "[Hop● Hop◯]"; first by apply not_elem_of_list_to_map, not_elem_of_pendingOp_active_fmap.
    assert (Hτ_fresh': Φs !! τ = None).
    { apply not_elem_of_dom. rewrite -Hdom. apply not_elem_of_dom. by apply not_elem_of_list_to_map, not_elem_of_pendingOp_active_fmap. }
    iMod (own_receipt_insert τ Φ with "HΦ●") as "[HΦ● HΦ◯]"; first done.
    iAssert ([∗ map] τ ↦ Φ ∈ (<[τ:=Φ]> Φs), interpret γ pts' τ Φ)%I with "[AU Hinterps]" as "Hinterps".
    { rewrite big_sepM_insert //.
      iSplitL "AU".
      - apply per_tag_partial_linearized_filter_call in Hper_tag_lin'.
        destruct Hper_tag_lin' as [Heq | (y' & ? & Heq)]; rewrite /interpret Heq; done.
      - iApply (big_sepM_mono with "Hinterps").
        iIntros (τ0 Φ0 Hlookup) "Hinterp".
        rewrite /interpret filter_cons_False //.
        simpl; intros ->.
        rewrite Hτ_fresh' in Hlookup. discriminate Hlookup. }

    (* double-prime variants of Hpending, Hper_tag_lin, Hmsteps, about pts' *)
    assert (Hpending'': trace_pendingOp pts' ⊆ {[τ]} ∪ dom Φs).
    { pose proof (Hpending'' :=  trace_pendingOp_call τ n y pts').
      apply (union_mono_l {[τ]}) in Hpending'.
      etrans; eassumption. }
    assert (Hper_tag_lin'': per_tag_partial_linearized pts').
    { eapply per_tag_partial_linearized_cons. eassumption. }
    assert (Hmsteps'': rtcL model_step s' s_end (filter (is_lin∘snd) pts')).
    { rewrite filter_cons_False in Hmsteps'; auto. }

    iMod ("Hclose" with "[-Hop◯ HΦ◯]") as "_".
    { iNext.
      iExists γπ, γϕ, γs, γe, s', (π++[(τ, Some ((ops!!!n: val) obj y))]), ((<[τ:=Φ]> Φs)), children, σ, pts', steps_left.
      iFrame "Hproph Hown_state Hγ HΦ● Hs● Hchildren● Htime_receipt".
      iSplitL "Hop●". {
        rewrite pendingOp_active_snoc_Some list_to_map_snoc; last by apply not_elem_of_pendingOp_active_fmap.
        iFrame. }
      iSplit. { iPureIntro.
        rewrite pendingOp_active_snoc_Some list_to_map_snoc; last by apply not_elem_of_pendingOp_active_fmap.
        clear -Hdom. set_solver. }
      iSplitL "Hτ_token Hfresh". { rewrite fmap_app big_sepL_snoc. iFrame. }
      iFrame "Hinterps".
      iSplit. { iPureIntro. rewrite dom_insert_L //. }
      eauto 7 using config_safe_call. }

    (****************************************************)

    iModIntro. clear -valid_obj HModelDecidable. wp_pures.
    wp_bind ((ops!!!n: val) obj y).
    remember ((ops!!!n: val) obj y) as e. clear -valid_obj HModelDecidable.
    iLöb as "IH" forall (e).
    destruct (to_val e) as [y'|] eqn:He; last first.

    (****************************************************)
    (* reduce one pending operation for one step        *)
    (****************************************************)

    - iApply wp_inv_open_maybe.
      iInv "His_P" as "Hinv" "Hclose".
      iDestruct "Hinv" as (γπ' γϕ' γs' γe' s π Φs children σ1 pts steps_left)
        "(Hproph & >Hown_state & >#Hγ' & >Hop● & HΦ● & Hs● & Hchildren● & Htime_receipt & >%Hdom & >Hfresh & Hinterps & >(%Hpending & %Hper_tag_lin & %Hmsteps & %Hconfig_safe))".
      iCombine "Hγ Hγ'" gives %Heq%to_agree_op_inv_L.
      inversion Heq. subst γπ' γϕ' γs' γe'. clear Heq. iClear "Hγ'".
      iCombine "Hop● Hop◯" gives %(π₁ & π₂ & ->)%elem_of_list_to_map_2%elem_of_pendingOp_active_split.
      iDestruct (ghost_id_nodup with "Hfresh") as %Hnodup.

      (* reducible *)
      apply config_safe_not_stuck in Hconfig_safe as Hnot_stuck.
      assert (He_red : reducible e σ1). {
        destruct Hnot_stuck as [Hfalse|]; try done.
        rewrite /= He in Hfalse. by inversion Hfalse.
      }

      iMod (lang_completeness with "[Hown_state]") as "H".
      { exact He_red. } { iFrame "Hown_state". }
      iModIntro. iDestruct "H" as "[H | H]".

      + (* first redex is atomic *)
        iLeft.
        iDestruct "H" as (K e1 ? Heq Hnotval Hatomic) "H". subst e.
        iExists K, e1. do 3 (iSplit; first done).
        iApply "H".
        iIntros "!> _" (κ v2 σ2 efs Hbase).
        destruct steps_left as [|steps_left]; first done.

        (* allocate fresh child_tokens for each forked thread *)
        iMod (child_token_alloc_many γ γπ γϕ γs γe efs with "Hγ Hchildren●") as "[Hchildren●  Hnew_tokens]".
        (* extend config_safe by the new forked threads *)
        eapply fill_step in Hbase as Hprim.
        pose proof (config_safe_intermediate ops obj π₁ π₂ children (K e1) (K (Val v2)) σ1 σ2 κ τ efs
                      Hprim Hconfig_safe) as Hconfig_safe'.
        (* update proph *)
        iDestruct (wp_resolve_proph_trace_intermediate with "Hproph") as (pts'_filtered) "[%Hresolve_eq Hproph]".
        { exact Hprim. }
        (* update pendingOp map *)
        iMod (ghost_map_update (K (Val v2)) with "Hop● Hop◯") as "[Hop● Hop◯]".
        replace (<[τ:=K (Val v2)]> (list_to_map (pendingOp_active (π₁ ++ (τ, Some (K e1)) :: π₂))): gmap positive expr)
          with (list_to_map (pendingOp_active (π₁ ++ (τ, Some (K (Val v2))) :: π₂)): gmap positive expr); last first.
        { assert ((list_to_map (pendingOp_active π₁) : gmap _ _)!! τ = None).
          { rewrite cons_middle in Hnodup.
            rewrite assoc fmap_app NoDup_app in Hnodup. destruct Hnodup as [Hnodup _].
            rewrite comm fmap_cons NoDup_cons in Hnodup. destruct Hnodup as [Hnodup _].
            by apply not_elem_of_list_to_map_1, not_elem_of_pendingOp_active_fmap. }
          rewrite !pendingOp_active_app !pendingOp_active_cons_Some !list_to_map_app !list_to_map_cons insert_union_r // insert_insert_eq //. }

        iModIntro. iSplitR "Hnew_tokens"; last first.
        { (* forked threads *)
          iApply (big_sepL_impl with "Hnew_tokens").
          iIntros "!>" (???) "Htok".
          iApply (wp_forked_child with "His_P Htok"). }

        iIntros "Hown_state".
        iMod ("Hclose" with "[-Hop◯ HΦ◯]") as "_".
        { iNext.
          destruct (trunk_trace_spec pts (filter (not ∘ is_lin ∘ snd) pts) pts'_filtered) as [Hfilter Hpts'_prefix_pts].
          { reflexivity. } { apply Hresolve_eq. }
          remember (trunk_trace pts pts'_filtered) as pts'.
          iExists γπ, γϕ, γs, γe, s, (π₁++(τ,Some (K (Val v2)))::π₂), Φs, (children ++ efs), σ2, pts', steps_left.
          iSplitL "Hproph". { rewrite Hfilter //. }
          iFrame "Hown_state Hγ Hop● HΦ● Hs● Hchildren● Htime_receipt".
          iSplit. { iPureIntro. rewrite -Hdom. rewrite !pendingOp_active_app !pendingOp_active_cons_Some !dom_list_to_map_L !fmap_app !fmap_cons //. }
          iSplitL "Hfresh". { rewrite !fmap_app !fmap_cons //. }
          iSplitL "Hinterps".
          { iApply (big_sepM_mono with "Hinterps").
            iIntros (τ0 Φ0 Hlookup0) "Hinterp".
            rewrite /interpret.
            apply (prefix_filter (λ t, t.1 = τ0)) in Hpts'_prefix_pts.
            destruct (filter (λ t, t.1 = τ0) pts) as [|[? [ | | ]]] eqn:Heqfilter_pts.
            - apply prefix_nil_inv in Hpts'_prefix_pts as ->. done.
            - done.
            - destruct (filter (λ t, t.1 = τ0) pts'); first done.
              apply prefix_cons_inv_1 in Hpts'_prefix_pts as ->. done.
            - destruct (filter (λ t, t.1 = τ0) pts'); first done.
              apply prefix_cons_inv_1 in Hpts'_prefix_pts as ->. done. }
          iSplit. { iPureIntro. etrans; last exact Hpending. by apply trace_pendingOp_prefix. }
          iSplit. { iPureIntro. eauto using per_tag_partial_linearized_prefix. }
          iSplit. { iPureIntro. eauto using model_steps_prefix, prefix_filter. }
          iPureIntro. exact Hconfig_safe'. }

          iApply ("IH" with "Hop◯ HΦ◯").

      + (* first redex is non-atomic *)
        iRight.
        iDestruct "H" as "[Hown_state H]".
        iMod ("Hclose" with "[-H Hop◯ HΦ◯]") as "_".
        { iNext. iFrame "∗#". auto. }
        clear -HModelDecidable.
        iModIntro. iApply "H".
        iIntros "!> Hlc" (e2 efs) "H".
        iInv "His_P" as "Hinv" "Hclose".
        iDestruct "Hinv" as (γπ' γϕ' γs' γe' s π Φs children σ1 pts steps_left)
          "(>Hproph & >Hown_state & >#Hγ' & >Hop● & HΦ● & Hs● & >Hchildren● & Htime_receipt & >%Hdom & >Hfresh & Hinterps & >(%Hpending & %Hper_tag_lin & %Hmsteps & %Hconfig_safe))".
        iCombine "Hγ Hγ'" gives %Heq%to_agree_op_inv_L.
        inversion Heq. subst γπ' γϕ' γs' γe'. clear Heq. iClear "Hγ'".
        iCombine "Hop● Hop◯" gives %(π₁ & π₂ & ->)%elem_of_list_to_map_2%elem_of_pendingOp_active_split.
        iDestruct (ghost_id_nodup with "Hfresh") as %Hnodup.

        iMod ("H" with "Hown_state") as (κ σ2) "[%Hprim Hown_state]".
        (* allocate fresh child_tokens for each forked thread *)
        iMod (child_token_alloc_many γ γπ γϕ γs γe efs with "Hγ Hchildren●") as "[Hchildren●  Hnew_tokens]".
        (* extend config_safe by the new forked threads *)
        pose proof (config_safe_intermediate ops obj π₁ π₂ children e e2 σ1 σ2 κ τ efs
                      Hprim Hconfig_safe) as Hconfig_safe'.
        (* update proph *)
        iMod (lc_fupd_elim_later with "Hlc Htime_receipt") as "Htime_receipt".
        destruct steps_left as [|steps_left]; first done.
        iDestruct (wp_resolve_proph_trace_intermediate with "Hproph") as (pts'_filtered) "[%Hresolve_eq Hproph]".
        { exact Hprim. }
        (* update pendingOp map *)
        iMod (ghost_map_update e2 with "Hop● Hop◯") as "[Hop● Hop◯]".
        replace (<[τ:=e2]> (list_to_map (pendingOp_active (π₁ ++ (τ, Some e) :: π₂))): gmap positive expr)
          with (list_to_map (pendingOp_active (π₁ ++ (τ, Some e2) :: π₂)): gmap positive expr); last first.
        { assert ((list_to_map (pendingOp_active π₁) : gmap _ _)!! τ = None).
          { rewrite cons_middle in Hnodup.
            rewrite assoc fmap_app NoDup_app in Hnodup. destruct Hnodup as [Hnodup _].
            rewrite comm fmap_cons NoDup_cons in Hnodup. destruct Hnodup as [Hnodup _].
            by apply not_elem_of_list_to_map_1, not_elem_of_pendingOp_active_fmap. }
          rewrite !pendingOp_active_app !pendingOp_active_cons_Some !list_to_map_app !list_to_map_cons insert_union_r // insert_insert_eq //. }

        iMod ("Hclose" with "[-Hop◯ HΦ◯ Hnew_tokens]") as "_".
        { iNext.
          destruct (trunk_trace_spec pts (filter (not ∘ is_lin ∘ snd) pts) pts'_filtered) as [Hfilter Hpts'_prefix_pts].
          { reflexivity. } { apply Hresolve_eq. }
          remember (trunk_trace pts pts'_filtered) as pts'.
          iExists γπ, γϕ, γs, γe, s, (π₁++(τ,Some e2)::π₂), Φs, (children ++ efs), σ2, pts', steps_left.
          iSplitL "Hproph". { rewrite Hfilter //. }
          iFrame "Hown_state Hγ Hop● HΦ● Hs● Hchildren● Htime_receipt".
          iSplit. { iPureIntro. rewrite -Hdom. rewrite !pendingOp_active_app !pendingOp_active_cons_Some !dom_list_to_map_L !fmap_app !fmap_cons //. }
          iSplitL "Hfresh". { rewrite !fmap_app !fmap_cons //. }
          iSplitL "Hinterps".
          { iApply (big_sepM_mono with "Hinterps").
            iIntros (τ0 Φ0 Hlookup0) "Hinterp".
            rewrite /interpret.
            apply (prefix_filter (λ t, t.1 = τ0)) in Hpts'_prefix_pts.
            destruct (filter (λ t, t.1 = τ0) pts) as [|[? [ | | ]]] eqn:Heqfilter_pts.
            - apply prefix_nil_inv in Hpts'_prefix_pts as ->. done.
            - done.
            - destruct (filter (λ t, t.1 = τ0) pts'); first done.
              apply prefix_cons_inv_1 in Hpts'_prefix_pts as ->. done.
            - destruct (filter (λ t, t.1 = τ0) pts'); first done.
              apply prefix_cons_inv_1 in Hpts'_prefix_pts as ->. done. }
          iSplit. { iPureIntro. etrans; last exact Hpending. by apply trace_pendingOp_prefix. }
          iSplit. { iPureIntro. eauto using per_tag_partial_linearized_prefix. }
          iSplit. { iPureIntro. eauto using model_steps_prefix, prefix_filter. }
          iPureIntro. exact Hconfig_safe'. }

          iModIntro. iSplitR "Hnew_tokens".
          { iApply ("IH" with "Hop◯ HΦ◯"). }
          iApply (big_sepL_impl with "Hnew_tokens").
          iIntros "!>" (???) "Htok".
          iApply (wp_forked_child with "His_P Htok").

    (****************************************************)
    (* remove a finished operation from π               *)
    (****************************************************)
    - rewrite -(of_to_val e y'); last apply He.
      iApply wp_value. wp_pure credit:"Hlc". wp_pures.
      wp_bind (resolve_proph: _ to: _)%E.
      iInv "His_P" as "Hinv" "Hclose".
      iDestruct "Hinv" as (γπ' γϕ' γs' γe' s π Φs children σ pts steps_left)
        "(>Hproph & >Hown_state & >#Hγ' & >Hop● & HΦ● & Hs● & >Hchildren● & Htime_receipt & >%Hdom & >Hfresh & Hinterps & >(%Hpending & %Hper_tag_lin & %Hmsteps & %Hconfig_safe))".
      iCombine "Hγ Hγ'" gives %Heq%to_agree_op_inv_L.
      inversion Heq. subst γπ' γϕ' γs' γe'. clear Heq. iClear "Hγ'".
      iCombine "Hop● Hop◯" gives %(π₁ & π₂ & ->)%elem_of_list_to_map_2%elem_of_pendingOp_active_split.
      iDestruct (ghost_id_nodup with "Hfresh") as %Hnodup.
      iMod (lc_fupd_elim_later with "Hlc Htime_receipt") as "Htime_receipt".
      destruct steps_left as [|steps_left]; first done.
      wp_apply (wp_resolve_proph_trace_return with "Hproph") as (pts'_filtered) "[%Hresolve_eq Hproph]"; first done.

      (* destruct [pts] into [pts = pts_lin++Ret::pts'], where [pts_lin] only contains Lin *)
      destruct (obs_cons_inv _ _ _ Hresolve_eq) as (pts_lin & pts' & -> & Hpts_lin & ->).

      (* prime variants of Hpending, Hper_tag_lin, Hmsteps, about (τ, Ret y')::pts' *)
      assert (per_tag_partial_linearized ((τ, Ret y')::pts') ∧ trace_pendingOp ((τ, Ret y')::pts') ⊆ dom Φs
          ∧ Forall (λ t, t.1 ∈ dom Φs) pts_lin) as (Hper_tag_lin' & Hpending' & Hpts_lin_in_dom).
      { clear - Hpending Hpts_lin Hper_tag_lin.
        induction pts_lin as [|pt_lin pts_lin IH]; first (simpl in *; auto).
        rewrite Forall_cons in Hpts_lin. destruct Hpts_lin as [Hpt_lin Hpts_lin].
        destruct pt_lin as [τ' [|i v v'|]]; simpl in Hpt_lin; [done| |done].
        rewrite -app_comm_cons in Hpending,Hper_tag_lin.
        pose proof (trace_pendingOp_lin_elem_of τ' i v v' (pts_lin++(τ,Ret y')::pts')) as Hτ'_in.
        eapply elem_of_weaken in Hτ'_in; last exact Hpending.
        assert (Hpending': trace_pendingOp (pts_lin++(τ,Ret y')::pts') ⊆ dom Φs).
        { etrans; last exact Hpending.
          by apply trace_pendingOp_lin. }
        apply per_tag_partial_linearized_cons in Hper_tag_lin.
        destruct IH as (?&?&?); [assumption..|].
        rewrite Forall_cons.
        split_and!; done. }

      (* linearize operations in [pts_lin] *)
      iDestruct (linearize_helping Hpts_lin Hper_tag_lin Hmsteps with "Hγ Hs● Hinterps")
        as (s_end) ">(%s' & %Hmsteps' & Hs● & Hinterps)".
      { exact Hpts_lin_in_dom. }

      iDestruct (own_receipt_agree with "HΦ● HΦ◯") as (Φ') "[%HlookupΦ #HeqΦ]".
      (* remove finished operation *)
      iMod (ghost_map_delete with "Hop● Hop◯") as "Hop●".
      iMod (own_receipt_delete with "HΦ● HΦ◯") as "HΦ●".
      iAssert (Φ' y' ∗ [∗ map] τ ↦ Φ ∈ (delete τ Φs), interpret γ pts' τ Φ)%I with "[Hinterps]" as "[HΦ' Hinterps]".
      { rewrite (big_sepM_delete _ Φs τ Φ') //.
        iDestruct "Hinterps" as "[HΦ' Hinterps]".
        iSplitL "HΦ'".
        - rewrite /interpret filter_cons_True //.
        - iApply (big_sepM_mono with "Hinterps").
          iIntros (τ0 Φ0 Hlookup) "Hinterp".
          rewrite /interpret filter_cons_False //.
          simpl; intros ->.
          rewrite lookup_delete_eq in Hlookup. discriminate Hlookup. }

      (* double-prime variants of Hpending, Hper_tag_lin, Hmsteps, about pts' *)
      assert (Hpending'': trace_pendingOp pts' ⊆ dom Φs ∖ {[τ]}).
      { pose proof (Hpending'' :=  trace_pendingOp_ret τ y' pts' Hper_tag_lin').
        apply (difference_mono_r _ _ {[τ]}) in Hpending'.
        etrans; eassumption. }
      assert (Hper_tag_lin'': per_tag_partial_linearized pts').
      { eapply per_tag_partial_linearized_cons. eassumption. }
      assert (Hmsteps'': rtcL model_step s' s_end (filter (is_lin∘snd) pts')).
      { rewrite filter_cons_False in Hmsteps'; auto. }

      iMod ("Hclose" with "[-HΦ']") as "_".
      { iNext.
        iExists γπ, γϕ, γs, γe, s', (π₁++(τ,None)::π₂), (delete τ Φs), children, σ, pts', steps_left.
        iFrame "Hproph Hown_state Hγ HΦ● Hs● Hchildren● Htime_receipt".
        assert ((list_to_map (pendingOp_active π₁) : gmap _ _) !! τ = None) as Hτ_notin_π₁.
        { rewrite cons_middle in Hnodup.
          rewrite assoc fmap_app NoDup_app in Hnodup. destruct Hnodup as [Hnodup _].
          rewrite comm fmap_cons NoDup_cons in Hnodup. destruct Hnodup as [Hnodup _].
          by apply not_elem_of_list_to_map_1, not_elem_of_pendingOp_active_fmap. }
        assert ((list_to_map (pendingOp_active π₂) : gmap _ _) !! τ = None) as Hτ_notin_π₂.
        { rewrite fmap_app NoDup_app in Hnodup. destruct Hnodup as (_ & _ & Hnodup).
          rewrite fmap_cons NoDup_cons in Hnodup. destruct Hnodup as [Hnodup _].
          by apply not_elem_of_list_to_map_1, not_elem_of_pendingOp_active_fmap. }
        iSplitL "Hop●".
        { rewrite !pendingOp_active_app pendingOp_active_cons_Some pendingOp_active_cons_None.
          rewrite !list_to_map_app list_to_map_cons.
          rewrite delete_union delete_insert_eq // !delete_id //. }
        iSplit. { iPureIntro. rewrite dom_delete_L -Hdom.
          rewrite !pendingOp_active_app pendingOp_active_cons_Some pendingOp_active_cons_None.
          rewrite !list_to_map_app list_to_map_cons.
          rewrite !dom_union_L dom_insert_L.
          apply not_elem_of_dom in Hτ_notin_π₁, Hτ_notin_π₂.
          clear -Hτ_notin_π₁ Hτ_notin_π₂. set_solver. }
        iSplitL "Hfresh". { rewrite !fmap_app fmap_cons !big_sepL_app big_sepL_cons //. }
        iFrame "Hinterps".
        iSplit. { iPureIntro. rewrite dom_delete_L //. }
        eauto 7 using config_safe_return. }

      (****************************************************)

      iModIntro. wp_pures. iModIntro.
      rewrite discrete_fun_equivI.
      by iRewrite -("HeqΦ" $! y').
  Qed.
End logatom.

Section logatom'.
  Context `{!heapGS Σ, !ModelDecidable M, !linearizabilityG Σ}.
  Context (init : expr) (ops : list val).

  Corollary logatom_complete (n: nat) :
    to_val init = None →
    (∀ σ, sequential init σ) →
    library_initializable_linearizable init ops →
    ({{{ True }}} wrap_init init {{{ γ r, RET r; is_P ops γ r ∗ P_state γ s_init }}})
    ∧
    (∀ γ (x y: val), default default_vr (valid_requests!!n) y → is_P ops γ x ⊢
      <<{ ∀∀ s, P_state γ s }>>
        wrap_op n (ops!!!n) x y @ ↑Nlogatom
      <<{ ∃∃ s' y', P_state γ s' ∗ ⌜default default_rr (request_responses!!n) s y s' y'⌝ | RET y' }>>).
  Proof.
    intros Hinit_nv Hnofork (valid_obj & Hinit & Hlin)%library_initializable_linearizable_iff.
    split.
    - by eapply logatom_init_compelete.
    - by eapply logatom_op_complete.
  Qed.

  Corollary logatom_complete_init :
    to_val init = None →
    (∀ σ, sequential init σ) →
    library_initializable_linearizable init ops →
    {{{ True }}} wrap_init init {{{ γ r, RET r; is_P ops γ r ∗ P_state γ s_init }}}.
  Proof. intros Hinit_nv Hnofork Hinit_lin. destruct (logatom_complete inhabitant Hinit_nv Hnofork Hinit_lin)=>//. Qed.

  Corollary logatom_complete_op (n: nat) :
    library_initializable_linearizable init ops →
    ∀ γ (x y: val), default default_vr (valid_requests!!n) y →
      is_P ops γ x ⊢
      <<{ ∀∀ s, P_state γ s }>>
        wrap_op n (ops!!!n) x y @ ↑Nlogatom
      <<{ ∃∃ s' y', P_state γ s' ∗ ⌜default default_rr (request_responses!!n) s y s' y'⌝ | RET y' }>>.
  Proof.
    intros (valid_obj & Hinit & Hlin)%library_initializable_linearizable_iff.
    by eapply logatom_op_complete.
  Qed.
End logatom'.
