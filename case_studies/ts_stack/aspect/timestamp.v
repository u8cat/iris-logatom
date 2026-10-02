(* The timestamper, and the comparison of timestamps. *)

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

  Lemma get_timestamp_spec γs n pools ctr sents tracer k :
    {{{ inv tsN (ts_inv γs n pools ctr sents tracer) ∗ own (γ_c γs) (◯MN k) }}}
      get_timestamp #ctr
    {{{ (t1 t2 : nat), RET (#t1, #t2); ⌜k ≤ t1 ≤ t2⌝ ∗ own (γ_c γs) (◯MN (t2 + 1)) }}}.
  Proof.
    iIntros (Φ) "[#Hinv #Hk] HΦ". wp_lam.
    (* first read *)
    wp_bind (! _)%E.
    iInv "Hinv" as (σ) "(>%HI & Htr & Hm & Hpts & >Hc● & >Hctr & Hrest)" "Hclose".
    wp_load.
    iDestruct (own_valid_2 with "Hc● Hk") as %Hk%mono_nat_both_valid.
    iEval (rewrite mono_nat_auth_lb_op) in "Hc●". iDestruct "Hc●" as "[Hc● #Hc1]".
    iMod ("Hclose" with "[$Htr $Hm $Hpts $Hc● $Hctr $Hrest]") as "_"; first done.
    iModIntro. set (c1 := s_c σ) in *. clearbody c1. clear σ HI.
    wp_pures. wp_lam. wp_pures.
    (* second read *)
    wp_bind (! _)%E.
    iInv "Hinv" as (σ) "(>%HI & Htr & Hm & Hpts & >Hc● & >Hctr & Hrest)" "Hclose".
    wp_load.
    iDestruct (own_valid_2 with "Hc● Hc1") as %Hc12%mono_nat_both_valid.
    iEval (rewrite mono_nat_auth_lb_op) in "Hc●". iDestruct "Hc●" as "[Hc● #Hc2]".
    iMod ("Hclose" with "[$Htr $Hm $Hpts $Hc● $Hctr $Hrest]") as "_"; first done.
    iModIntro. set (c2 := s_c σ) in *. clearbody c2. clear σ HI.
    wp_pures.
    destruct (decide (c1 = c2)) as [<-|Hne].
    - rewrite bool_decide_eq_true_2 //. wp_pures.
      (* the CAS *)
      wp_bind (CmpXchg _ _ _).
      iInv "Hinv" as (σ) "(>%HI & Htr & Hm & Hpts & >Hc● & >Hctr & Hrest)" "Hclose".
      iDestruct (own_valid_2 with "Hc● Hc1") as %Hc1σ%mono_nat_both_valid.
      destruct (decide (s_c σ = c1)) as [Heq|Hneq].
      + subst c1. wp_cmpxchg_suc.
        iMod (own_update with "Hc●") as "Hc●"; first by apply (mono_nat_update (1 + s_c σ)); lia.
        iEval (rewrite mono_nat_auth_lb_op) in "Hc●". iDestruct "Hc●" as "[Hc● #Hc3]".
        iMod ("Hclose" with "[Htr Hm Hpts Hc● Hctr Hrest]") as "_".
        { iNext. iExists (ev_inc σ). rewrite /ts_res /=.
          replace (Z.of_nat (s_c σ) + 1)%Z with (Z.of_nat (1 + s_c σ)) by lia.
          iDestruct "Hrest" as "($ & $ & $ & $ & $ & $ & Hnodes & Helems & Howners)".
          iSplit; [iPureIntro; destruct HI; split; [by apply tss_inv_inc|done]|]. iFrame. }
        iModIntro. wp_pures. iModIntro. iApply "HΦ". iSplit; [iPureIntro; lia|].
        by replace (s_c σ + 1) with (1 + s_c σ) by lia.
      + wp_cmpxchg_fail; first (intros [= ?]; lia).
        iEval (rewrite mono_nat_auth_lb_op) in "Hc●". iDestruct "Hc●" as "[Hc● #Hc3]".
        iMod ("Hclose" with "[$Htr $Hm $Hpts $Hc● $Hctr $Hrest]") as "_"; first done.
        iModIntro. set (c3 := s_c σ) in *. clearbody c3. clear σ HI.
        wp_pures.
        wp_bind (! _)%E.
        iInv "Hinv" as (σ) "(>%HI & Htr & Hm & Hpts & >Hc● & >Hctr & Hrest)" "Hclose".
        wp_load.
        iDestruct (own_valid_2 with "Hc● Hc3") as %Hc34%mono_nat_both_valid.
        iEval (rewrite mono_nat_auth_lb_op) in "Hc●". iDestruct "Hc●" as "[Hc● #Hc4]".
        iMod ("Hclose" with "[$Htr $Hm $Hpts $Hc● $Hctr $Hrest]") as "_"; first done.
        iModIntro. wp_pures.
        replace (Z.of_nat (s_c σ) - 1)%Z with (Z.of_nat (s_c σ - 1)) by lia.
        iModIntro. iApply "HΦ". iSplit; [iPureIntro; lia|].
        by replace (s_c σ - 1 + 1) with (s_c σ) by lia.
    - rewrite bool_decide_eq_false_2; last (intros [= ?]; lia). wp_pures.
      replace (Z.of_nat c2 - 1)%Z with (Z.of_nat (c2 - 1)) by lia.
      iModIntro. iApply "HΦ". iSplit; [iPureIntro; lia|].
      by replace (c2 - 1 + 1) with c2 by lia.
  Qed.

  (* comparing an interval with the timestamp of a node: TOP if the node has none yet *)
  Lemma timestamp_lt_top_spec (a1 a2 : nat) :
    {{{ True }}} timestamp_lt (#a1, #a2)%V (timestamp_val None) {{{ RET #true; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_pures.
    rewrite bool_decide_eq_false_2; last (intros [= ?]; lia). wp_pures. by iApply "HΦ".
  Qed.

  Lemma timestamp_lt_spec (a1 a2 t1 t2 : nat) :
    {{{ True }}}
      timestamp_lt (#a1, #a2)%V (timestamp_val (Some (t1, t2)%core))
    {{{ RET #(bool_decide (a2 < t1)%nat); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_pures.
    rewrite (bool_decide_eq_false_2 (#t1 = #(-1))); last (intros [= ?]; lia). wp_pures.
    rewrite (bool_decide_ext (Z.of_nat a2 < Z.of_nat t1)%Z (a2 < t1)); last lia. by iApply "HΦ".
  Qed.
End proof.
