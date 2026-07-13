(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Rules for updating the specification program. *)
From iris.algebra Require Import auth excl frac agree gmap gset list.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Export lang notation tactics.
From iris_logatom.heap_lang.rel_logic Require Export spec_ra.
Import uPred.

Local Set Default Proof Using "Type".

Section rules.
  Context `{relocGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  (** * Aux. lemmas *)
  Lemma step_insert K tp j e σ κ e' σ' efs :
    tp !! j = Some (fill K e) → base_step e σ κ e' σ' efs →
    erased_step (tp, σ) (<[j:=fill K e']> tp ++ efs, σ').
  Proof.
    intros. rewrite -(take_drop_middle tp j (fill K e)) //.
    rewrite insert_app_r_alt length_take_le ?Nat.sub_diag /=;
      eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(assoc_L (++)) /=. eexists.
    eapply step_atomic; eauto. by apply: Ectx_step'.
  Qed.

  Lemma step_insert_no_fork K tp j e σ κ e' σ' :
    tp !! j = Some (fill K e) → base_step e σ κ e' σ' [] →
    erased_step (tp, σ) (<[j:=fill K e']> tp, σ').
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply step_insert. Qed.

  (** * Main rules *)
  (** Pure reductions *)
  Lemma step_pure E j K e e' (P : Prop) n :
    P →
    PureExec P n e e' →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K e ⊢ |={E}=> spec_ctx ∗ j ⤇ fill K e'.
  Proof.
    iIntros (HP Hex ?) "[#Hspec Hj]". iFrame "Hspec".
    iDestruct "Hspec" as (ρ) "Hspec".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & Hrtc)" "Hclose".
    iDestruct "Hrtc" as %Hrtc.
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iApply "Hclose". iNext. iExists (<[j:=fill K e']> tp), σ.
    iFrame.
    rewrite lookup_map_seq_0 in Hj.
    rewrite /tpool_auth.
    rewrite insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    apply rtc_nsteps_1 in Hrtc; destruct Hrtc as [m Hrtc].
    specialize (Hex HP). apply (rtc_nsteps_2 (m + n)).
    eapply nsteps_trans; eauto.
    revert e e' Hj Hex.
    induction n as [|n IHn] => e e' Htpj Hex.
    - inversion Hex; subst.
      rewrite list_insert_id; eauto. econstructor.
    - apply nsteps_inv_r in Hex.
      destruct Hex as [z [Hex1 Hex2]].
      specialize (IHn _ _ Htpj Hex1).
      eapply nsteps_r; eauto.
      replace (<[j:=fill K e']> tp) with
          (<[j:=fill K e']> (<[j:=fill K z]> tp)); last first.
      { clear. revert tp; induction j as [|j IHj]; intros tp.
        - destruct tp; trivial.
        - destruct tp; simpl; auto. by rewrite IHj. }
      destruct Hex2 as [Hexs Hexd].
      specialize (Hexs σ). destruct Hexs as [e'' [σ' [efs Hexs]]].
      specialize (Hexd σ [] e'' σ' efs Hexs); destruct Hexd as [? [? [? ?]]];
        subst.
      inversion Hexs; simpl in *; subst.
      rewrite -!fill_app.
      eapply step_insert_no_fork; eauto.
      { apply list_lookup_insert_eq. apply lookup_lt_is_Some; eauto. }
  Qed.

  (** Prophecy variables (at this point those are just noops) *)
  Lemma step_newproph E j K :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K NewProph ={E}=∗
    ∃ (p : proph_id), spec_ctx ∗ j ⤇ fill K #p ∗ prophS p.
  Proof.
    iIntros (?) "[#Hinv Hj]". iFrame "Hinv".
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    destruct (exist_fresh (used_proph_id σ)) as [p Hp].
    iMod (prophS_insert σ p with "Hprophs") as "[Hprophs $]"; [done|].
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iApply "Hclose". iNext.
    iExists (<[j:=fill K #p]> tp), (state_upd_used_proph_id ({[ p ]} ∪.) σ).
    rewrite insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_resolveproph E j K (p : proph_id) w :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (ResolveProph #p (of_val w)) ∗ prophS p ={E}=∗
    spec_ctx ∗ j ⤇ fill K #().
  Proof.
    iIntros (?) "(#Hinv & Hj & Hp)". iFrame "Hinv".
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    iDestruct (prophS_included with "Hprophs Hp") as %?.
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp), σ.
    rewrite insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    econstructor; last done.
    econstructor; eauto.
  Qed.

  (** Alloc, load, and store *)
  Lemma step_alloc E j K e v :
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (ref e) ⊢ |={E}=> ∃ l, spec_ctx ∗ j ⤇ fill K (#l) ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "[#Hinv Hj]". iFrame "Hinv".
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    destruct (exist_fresh (dom (heap σ))) as [l Hl%not_elem_of_dom].
    iMod (ghost_map_insert with "Hheap") as "[Hheap $]"; [done|].
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iApply "Hclose". iNext.
    iExists (<[j:=fill K (# l)]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    rewrite -state_init_heap_singleton. eapply AllocNS; first by lia.
    intros i ??. assert (i = 0) as -> by lia. by rewrite Loc.add_0.
  Qed.

  Lemma step_load E j K l q v:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ⊢ |={E}=> spec_ctx ∗ j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iFrame. iApply "Hclose". iNext.
    iExists (<[j:=fill K (of_val v)]> tp), σ.
    rewrite insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_store E j K l v' e v:
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ⊢ |={E}=> spec_ctx ∗ j ⤇ fill K #() ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iMod (ghost_map_update with "Hheap Hl") as "[Hheap $]".
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_xchg E j K l e (v v' : val) :
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Xchg #l e) ∗ l ↦ₛ v'
    ⊢ |={E}=> spec_ctx ∗ j ⤇ fill K (of_val v') ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iMod (ghost_map_update with "Hheap Hl") as "[Hheap $]".
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iApply "Hclose". iNext.
    iExists (<[j:=fill K _]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite !insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  (** CmpXchg & FAA *)
  Lemma step_cmpxchg_fail E j K l q v' e1 v1 e2 v2 :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    nclose specN ⊆ E →
    vals_compare_safe v' v1 →
    v' ≠ v1 →
    spec_ctx ∗ j ⤇ fill K (CmpXchg #l e1 e2) ∗ l ↦ₛ{q} v'
    ⊢ |={E}=> spec_ctx ∗ j ⤇ fill K (v', #false)%V ∗ l ↦ₛ{q} v'.
  Proof.
    iIntros (<-<-???) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iFrame.
    iApply "Hclose". iNext.
    iExists (<[j:=fill K _]> tp), σ.
    rewrite !insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
    rewrite bool_decide_false //.
  Qed.

  Lemma step_cmpxchg_suc E j K l e1 v1 v1' e2 v2:
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    nclose specN ⊆ E →
    vals_compare_safe v1' v1 →
    v1' = v1 →
    spec_ctx ∗ j ⤇ fill K (CmpXchg #l e1 e2) ∗ l ↦ₛ v1'
    ⊢ |={E}=> spec_ctx ∗ j ⤇ fill K (v1', #true)%V ∗ l ↦ₛ v2.
  Proof.
    iIntros (<-<-???) "(#Hinv & Hj & Hl)"; subst. iFrame "Hinv".
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iMod (ghost_map_update with "Hheap Hl") as "[Hheap $]".
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iApply "Hclose". iNext.
    iExists (<[j:=fill K _]> tp), (state_upd_heap <[l:=Some _]> σ).
    rewrite !insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
    rewrite bool_decide_true //.
  Qed.

  Lemma step_faa E j K l e1 e2 (i1 i2 : Z) :
    IntoVal e1 #i2 →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (FAA #l e1) ∗ l ↦ₛ #i1
    ⊢ |={E}=> spec_ctx ∗ j ⤇ fill K #i1 ∗ l ↦ₛ #(i1+i2).
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)"; subst. iFrame "Hinv".
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    iDestruct (ghost_map_lookup with "Hheap Hl") as %?.
    iMod (ghost_map_update with "Hheap Hl") as "[Hheap $]".
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iApply "Hclose". iNext.
    iExists (<[j:=fill K _]> tp), (state_upd_heap <[l:=Some _]> σ).
    rewrite !insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  (** Fork *)
  Lemma step_fork E j K e :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Fork e) ⊢ |={E}=>
    ∃ j', (spec_ctx ∗ j ⤇ fill K #()) ∗ (spec_ctx ∗ j' ⤇ e).
  Proof.
    iIntros (?) "[#Hspec Hj]". iFrame "Hspec".
    iDestruct "Hspec" as (ρ) "Hspec".
    iInv specN as (tp σ) ">(Hown & Hheap & Hprophs & %)" "Hclose".
    iDestruct (ghost_map_lookup with "Hown Hj") as %Hj.
    rewrite lookup_map_seq_0 in Hj.
    iMod (ghost_map_update with "Hown Hj") as "[Hown $]".
    iMod (ghost_map_insert (length tp) with "Hown") as "[Hown $]".
    { rewrite insert_map_seq_0; [|by apply lookup_lt_is_Some_1].
      rewrite lookup_map_seq_0. apply lookup_ge_None_2. rewrite length_insert //. }
    iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp ++ [e]), σ.
    rewrite /tpool_auth.
    assert ((map_seq 0 (<[j:=fill K #()]> tp ++ [e])) = (<[length tp:=e]> (<[j:=fill K #()]> (map_seq 0 tp)))) as ->.
    { rewrite map_seq_app.
      rewrite insert_union_singleton_l.
      rewrite length_insert /= insert_empty.
      rewrite map_seq_insert /=; [|by apply lookup_lt_is_Some_1].
      rewrite map_union_comm //.
      apply map_disjoint_singleton_r_2.
      apply lookup_insert_None.
      split.
      - rewrite lookup_map_seq_0. by apply lookup_ge_None_2.
      - intros ->. apply lookup_lt_Some in Hj. lia. }
    iFrame. iPureIntro.
    eapply rtc_r, step_insert; eauto. econstructor; eauto.
  Qed.

End rules.
