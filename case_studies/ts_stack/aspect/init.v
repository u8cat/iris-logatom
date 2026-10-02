(* Initialization. *)

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
From case_studies.ts_stack.aspect Require Import pure defs.

Section proof.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  Lemma new_sppool_spec (i : nat) :
    {{{ True }}}
      new_sppool #i
    {{{ (s : loc), RET #s; s ↦ #() ∗ (s +ₗ 1) ↦ timestamp_val None ∗ (s +ₗ 2) ↦ #s ∗ (s +ₗ 3) ↦ #true }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_lam. wp_pures.
    wp_apply (wp_allocN with "[//]") as (s) "[Hs _]"; first done.
    iEval (rewrite /= array_cons array_cons array_cons array_singleton) in "Hs".
    iDestruct "Hs" as "(H0 & H1 & H2 & H3)".
    iEval (rewrite !Loc.add_assoc /=) in "H2 H3".
    wp_pures. wp_store. wp_store. wp_store. wp_store. wp_pures.
    iModIntro. iApply "HΦ". iFrame.
  Qed.

  Local Lemma sents_nodup (l : list loc) :
    ([∗ list] s ∈ l, (s +ₗ 2) ↦ #s) -∗ ⌜NoDup l⌝.
  Proof.
    iInduction l as [|s l] "IH"; iIntros "Hl"; [iPureIntro; constructor|].
    rewrite big_sepL_cons. iDestruct "Hl" as "[Hs Hl]".
    iAssert (⌜s ∉ l⌝)%I as %Hs.
    { iIntros (Hin). apply list_elem_of_lookup in Hin as [i Hi].
      iDestruct (big_sepL_lookup with "Hl") as "Hs'"; first done.
      by iDestruct (pointsto_valid_2 with "Hs Hs'") as %[? _]. }
    iDestruct ("IH" with "Hl") as %Hnd. iPureIntro. by constructor.
  Qed.

  Local Lemma big_sepL_replicate_seq (Φ : nat → bool → iProp Σ) (m : nat) (b0 : bool) :
    ([∗ list] j ∈ seq 0 m, Φ j b0) ⊣⊢ [∗ list] j ↦ b ∈ replicate m b0, Φ j b.
  Proof.
    assert (Heq : replicate m b0 = (λ _, b0) <$> seq 0 m).
    { rewrite (const_fmap (λ _, b0) (seq 0 m) b0); [by rewrite length_seq|by intros]. }
    rewrite Heq big_sepL_fmap. apply big_sepL_proper. intros k j Hj. by apply lookup_seq in Hj as [-> _].
  Qed.

  Local Lemma owners_alloc (n : nat) :
    ⊢ |==> ∃ γO : list gname, ⌜length γO = n⌝ ∗
      [∗ list] j ∈ seq 0 n, ghost_var (γO !!! j) 1 (false, 1).
  Proof.
    iInduction n as [|n] "IH".
    - iModIntro. iExists []. iSplit; [done|]. simpl. done.
    - iMod "IH" as (γO) "[%Hlen HO]".
      iMod (ghost_var_alloc (false, 1)) as (γ) "Hγ".
      iModIntro. iExists (γO ++ [γ]). rewrite length_app. iSplit; [iPureIntro; simpl; lia|].
      rewrite seq_S big_sepL_app /=. iSplitL "HO".
      + iApply (big_sepL_impl with "HO"). iIntros "!>" (k j Hj) "Hj".
        apply lookup_seq in Hj as [-> Hk]. rewrite lookup_total_app_l; [done|lia].
      + rewrite lookup_total_app_r; [|lia]. rewrite Hlen Nat.sub_diag /=. by iFrame.
  Qed.

  Lemma init_spec (n : nat) : 0 < n → init_spec_type repr_ts NotStuck (new_tsstack #n).
  Proof.
    iIntros (Hn Φ) "_ HΦ". wp_lam. wp_pures.
    wp_apply (new_threadpool_spec n) as (γt tpl) "#Htp"; first (iPureIntro; lia).
    wp_lam. wp_alloc ctr as "Hctr". wp_pures.
    wp_apply (wp_array_init_fmap (λ s : loc, #s)
                (λ _ s, s ↦ #() ∗ (s +ₗ 1) ↦ timestamp_val None ∗ (s +ₗ 2) ↦ #s ∗ (s +ₗ 3) ↦ #true)%I
                with "[]") as (pools sents) "(%Hlen & Hpools & Hsents)"; first lia.
    { iApply big_sepL_intro. iIntros "!>" (k i _).
      wp_apply new_sppool_spec as (s) "Hs"; first done. iExists s. by iFrame. }
    wp_pures.
    iMod (own_alloc (●ML ([] : list (leibnizO (positive * positive))))) as (γm) "Hm";
      first by apply mono_list_auth_valid.
    iMod (own_alloc (●ML ([] : list (leibnizO pt_entry)))) as (γp) "Hp";
      first by apply mono_list_auth_valid.
    iMod (own_alloc (●MN 1)) as (γc) "Hc"; first by apply mono_nat_auth_valid.
    iMod (ghost_map_alloc_empty (K:=positive) (V:=nat * nat)) as (γTS) "HTS".
    iMod (ghost_map_alloc_empty (K:=positive) (V:=nat)) as (γK) "HK".
    iMod (ghost_map_alloc_empty (K:=positive) (V:=op_state)) as (γos) "Hos".
    iMod (owners_alloc (length sents)) as (γO) "[%HγO HO]".
    set (γs := TsNames γm γp γc γTS γK γos γO γt).
    iMod (own_alloc (to_agree (γs : leibnizO ts_names))) as (γ) "#Hγ"; first done.
    iModIntro. iApply "HΦ". iIntros (tracer) "Htr".

    assert (Hlen' : length sents = n) by lia.
    iAssert (⌜NoDup sents⌝)%I as %Hnd.
    { iApply sents_nodup. iApply (big_sepL_impl with "Hsents"). iIntros "!>" (k s _) "(_ & _ & $ & _)". }
    iMod (inv_alloc tsN _ (ts_inv γs n pools ctr sents tracer) with "[-]") as "#Hinv".
    { iNext. iExists (tss_init sents). rewrite /ts_res /=. iFrame.
      iSplit; [iPureIntro; split; [by apply tss_inv_init|done]|].
      iSplitR; [by rewrite big_sepM_empty|]. iSplitR; [by rewrite big_sepM_empty|].
      iSplitL "Hpools".
      { rewrite /array big_sepL_fmap. done. }
      iSplitL "Hsents".
      { rewrite big_sepM_list_to_map; last first.
        { rewrite -list_fmap_compose. rewrite (list_fmap_ext _ id); [by rewrite list_fmap_id|done]. }
        rewrite big_sepL_fmap. iApply (big_sepL_impl with "Hsents"). iIntros "!>" (k s Hs) "(_ & H1 & H2 & H3)".
        rewrite /node_res /takenb /takenb_l /tsfield /tag_of /tag_of_l /=.
        rewrite bool_decide_eq_true_2; [|by eapply list_elem_of_lookup_2]. iFrame. }
      iSplitR; [done|].
      rewrite -big_sepL_replicate_seq -HγO. iApply (big_sepL_impl with "HO"). iIntros "!>" (k j Hj) "Hj".
      apply lookup_seq in Hj as [-> Hk].
      assert (Hpl : length (pool_list (tss_init sents) k) = 1).
      { rewrite /pool_list /pool_list_l /=. destruct (lookup_lt_is_Some_2 sents k) as [s ->]; [lia|]. done. }
      rewrite Hpl /owner_res. iDestruct "Hj" as "[$ $]". }
    iModIntro. iExists γs, pools, ctr, tpl, n, sents. iFrame "#". iPureIntro. split_and!; [done|lia|done].
  Qed.
End proof.
