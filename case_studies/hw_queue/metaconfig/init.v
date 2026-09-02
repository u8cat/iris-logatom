(* init.v — Init spec for [new_queue sz]. *)

From stdpp Require Import base gmap propset.
From iris_logatom.pure_logic Require Import linear.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.metaconfig Require Import tracking.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants ghost_map ghost_var.
From iris.heap_lang Require Import notation proofmode.
From iris_logatom.heap_lang Require Import mgc.

From case_studies.hw_queue Require Import impl.
From case_studies.hw_queue.metaconfig Require Import defs lemmas.
Import HWQMetaConfigNotation.

Section init_spec.
  Context `{!heapGS Σ, !traceG Σ, !hwqMcG Σ}.

  Lemma init_spec sz : (0 < sz)%Z →
    init_spec_type hwq_repr NotStuck (init_hwq sz).
  Proof.
    iIntros (Hsz Φ) "_ HΦ".
    rewrite /init_hwq.
    wp_lam.
    wp_apply (wp_allocN with "[//]") as (ar) "[Har _]"; first done.
    wp_pures.
    wp_alloc back as "Hback".
    wp_pures.
    (* Allocate ghost state. *)
    iMod (ghost_var_alloc
            ({[ (@s_init hwq_model, ∅ : gmap positive proc_status) ]}
             : gset single_config_q)) as (γM) "HγM".
    iMod (ghost_map_alloc (∅ : gmap positive op_status_t)) as (γ_status) "[Hstat _]".
    iMod (ghost_map_alloc (∅ : gmap nat val)) as (γ_slots) "[Hslots _]".
    iMod (ghost_map_alloc (∅ : gmap positive (nat * nat))) as (γ_scan) "[Hscan _]".
    iMod (own_alloc (to_agree ((γM, γ_status, γ_slots, γ_scan) : leibnizO hwq_meta_t)))
      as (γ) "#Hmeta"; first done.
    iModIntro.
    iApply ("HΦ" $! γ).
    iIntros (l) "Hts".
    iMod (inv_alloc hwqN _ (hwq_inv_body γ γM γ_status γ_slots γ_scan sz ar back l)
            with "[-]") as "#Hinv".
    { iNext. iExists (replicate (Z.to_nat sz) NONEV), 0%Z, [],
                     ({[ (@s_init hwq_model, ∅ : gmap positive proc_status) ]}
                      : gset single_config_q),
                     ∅, ∅, ∅.
      iAssert ([∗ map] i ↦ v ∈ (∅ : gmap nat val), i ↪[γ_slots]□ v)%I as "#Hslots_empty".
      { iApply big_sepM_empty. done. }
      iFrame "Hback Har Hts HγM Hstat Hslots Hscan Hslots_empty".
      iPureIntro. split_and!.
      - by rewrite length_replicate.
      - lia.
      - rewrite set_to_propset_singleton. apply mcfg_steps_nil.
      - by apply non_empty_singleton_L.
      - intros τ. exists Push, #(), #(). rewrite filter_nil. apply prefix_nil.
      - intros τ. rewrite lookup_empty.
        intros s π Hin. clear -Hin.
        apply elem_of_set_to_propset in Hin.
        assert ((s, π) = (@s_init hwq_model, ∅)) as Heq by set_solver.
        injection Heq as -> ->. apply lookup_empty.
      - split.
        + intros i v. rewrite lookup_empty. intros [=].
        + intros i v Hi. rewrite lookup_replicate in Hi.
          destruct Hi as [Hv _]. discriminate.
      - apply Forall_replicate. left. reflexivity.
      - intros τ. rewrite lookup_empty. rewrite filter_nil. reflexivity.
      - intros A seq Hgood Hnodup Hsetof Hjinvseq.
        (* Step 1: show A = ∅. *)
        assert (HA_empty : A = ∅).
        { apply set_eq. intros k. split; last by intros []%not_elem_of_empty.
          intros Hk. exfalso.
          destruct Hgood as [_ Hgood2].
          destruct (Hgood2 k Hk) as [[v Hitems_k] | (τ_e & v_e & Hstat_e)].
          - (* items[k] = SOMEV v contradicts items = replicate NONEV *)
            rewrite lookup_replicate in Hitems_k.
            destruct Hitems_k as [Hnv _]. discriminate.
          - (* stat[τ_e] = Some _ contradicts stat = ∅ *)
            rewrite lookup_empty in Hstat_e. discriminate. }
        (* Step 2: show seq = []. *)
        assert (Hseq_empty : seq = []).
        { destruct seq as [|x xs]; first reflexivity.
          exfalso. assert (Hin : x ∈ A).
          { rewrite -Hsetof. apply elem_of_list_to_set, elem_of_cons. by left. }
          rewrite HA_empty in Hin. by apply not_elem_of_empty in Hin. }
        (* Step 3: pick ([], ∅) ∈ M_g. *)
        exists ([] : list val), (∅ : gmap positive proc_status).
        split_and!.
        + apply elem_of_singleton. reflexivity.
        + rewrite Hseq_empty. reflexivity.
        + intros n k Hseq_n. rewrite Hseq_empty in Hseq_n.
          rewrite lookup_nil in Hseq_n. discriminate.
        + intros n k Hseq_n. rewrite Hseq_empty in Hseq_n.
          rewrite lookup_nil in Hseq_n. discriminate.
        + intros τ_d v_d i_d Habs. rewrite lookup_empty in Habs. discriminate.
        + intros τ_d v_d Habs. rewrite lookup_empty in Habs. discriminate.
        + intros τ_d v_d Habs. rewrite lookup_empty in Habs. discriminate.
        + intros τ_d Habs. rewrite lookup_empty in Habs. discriminate.
        + intros τ_e v_e i_e Habs. rewrite lookup_empty in Habs. discriminate.
        + intros τ_e v_e i_e Habs. rewrite lookup_empty in Habs. discriminate.
      - intros i v. rewrite lookup_empty. intros [=].
      - split_and!.
        + intros τ v i [Habs | Habs]; rewrite lookup_empty in Habs; discriminate.
        + intros i v. rewrite lookup_empty. intros [=].
        + intros τ_1 τ_2 v_1 v_2 i Habs.
          destruct Habs as [Habs|[Habs|Habs]]; rewrite lookup_empty in Habs; discriminate.
        + intros τ v i Habs.
          destruct Habs as [Habs|[Habs|Habs]]; rewrite lookup_empty in Habs; discriminate.
      - intros cfg pushes Hin Hnd Hsubset _Hstat.
        apply elem_of_set_to_propset in Hin.
        assert (Heq : cfg = ([] : list val, ∅ : gmap positive proc_status))
          by set_solver.
        subst cfg.
        assert (Hpush_empty : pending_push_of_config ([], ∅ : gmap positive proc_status) = []).
        { unfold pending_push_of_config. simpl.
          rewrite map_to_list_empty. reflexivity. }
        rewrite Hpush_empty in Hsubset.
        assert (pushes = []) as ->.
        { destruct pushes as [|p ps]; first reflexivity.
          exfalso. assert (p ∈ ([] : list (positive * val))) as Habs.
          { apply Hsubset. apply elem_of_cons. left. reflexivity. }
          by apply elem_of_nil in Habs. }
        unfold lineraize_pending_push. simpl.
        apply elem_of_set_to_propset.
        assert (Hmap : map_imap (λ τ x, if bool_decide (τ ∈ ([] : list positive))
                                  then Some (x.1, Some #()) else Some x)
                  (∅ : gmap positive proc_status) = ∅).
        { apply map_eq. intros i.
          rewrite map_lookup_imap lookup_empty /=. reflexivity. }
        rewrite Hmap. set_solver.
      - (* scan_map_dom_in_stat: scan_map = ∅ at init. *)
        intros τ _. apply lookup_empty.
      - (* scan_map_l_bounded: scan_map = ∅ at init. Vacuous. *)
        intros τ l_ j_ Habs. rewrite lookup_empty in Habs. discriminate. }
    iModIntro. iExists γM, γ_status, γ_slots, γ_scan, sz, ar, back.
    iSplit; first done.
    iSplit; first by iPureIntro; lia.
    iFrame "#".
  Qed.

End init_spec.
