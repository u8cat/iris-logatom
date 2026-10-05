(* The Herlihy-Wing queue: the operation and cell states, the ghost state, and the
   invariant. *)
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Import bag queue.
From iris_logatom.pure_logic Require Import encodable linear.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gset agree mono_list mono_nat.
From iris.base_logic Require Import invariants ghost_map.
From iris_logatom.program_logic Require Import atomic_complete.
From iris.heap_lang Require Import adequacy lang notation tactics unwrap.
From iris_logatom.heap_lang Require Import mgc fork_free.

From case_studies.hw_queue Require Import impl.

(* ====================================================================== *)
(* Trace property *)

Inductive array_state := NotStored | StoredNotCAS | CASed.

Inductive operation_state :=
  | PushCalled | PushStored | PushReturned
  | PopCalled  | PopReturned.

#[export] Instance array_state_inhabited : Inhabited array_state := populate NotStored.
#[export] Instance operation_state_inhabited : Inhabited operation_state := populate PushCalled.

(* Distinguish push-stored states. *)
Definition is_push_stored_state (s_op : operation_state) : Prop :=
  s_op = PushStored ∨ s_op = PushReturned.

Class hwqG Σ := {
  #[export] hwqG_meta :: inG Σ (agreeR (prodO (prodO (prodO (prodO (prodO gnameO gnameO) gnameO) gnameO) gnameO) gnameO));
  #[export] hwqG_back :: inG Σ mono_natR;
  #[export] hwqG_array :: ghost_mapG Σ nat array_state;
  #[export] hwqG_operation :: ghost_mapG Σ positive operation_state;
  #[export] hwqG_token :: ghost_mapG Σ positive nat;
  #[export] hwqG_match :: inG Σ (mono_listR (prodO positiveO positiveO));
  #[export] hwqG_slot :: ghost_mapG Σ nat positive;
}.
Definition hwqΣ := #[
  GFunctor (agreeRF (prodO (prodO (prodO (prodO (prodO gnameO gnameO) gnameO) gnameO) gnameO) gnameO));
  GFunctor (mono_natR);
  ghost_mapΣ nat array_state;
  ghost_mapΣ positive operation_state;
  ghost_mapΣ positive nat;
  GFunctor (mono_listR (prodO positiveO positiveO));
  ghost_mapΣ nat positive].
Global Instance subG_hwqG Σ : subG hwqΣ Σ → hwqG Σ.
Proof. solve_inG. Qed.

Definition queueN := nroot .@ "case_studies.hw_queue.aspect".
Section inv.
  Context `{!heapGS Σ, !traceG Σ, !hwqG Σ} (γ : gname) (q : val) (tracer : loc).
  Implicit Types (ts : list (positive * trace)) (m : list (positive * positive)) (τ : positive).

  Definition allocated_ar_inv_core γ_ar γ_tkn γ_slot ts m i a s_arr ts_prefix τ v ɛ : iProp Σ :=
      (* Push must have started *)
      hist tracer (ts_prefix++[(τ,Call Push v)])
      (* The pushed value is unboxed (matches push_wrapper_spec's premise) *)
    ∗ ⌜val_is_unboxed (SOMEV v)⌝
      (* This push locates after any precedence pushes *)
    ∗ ([∗ list] τ' ∈ (filter (is_ret_push∘snd) ts_prefix).*1, ∃ j, τ'↪[γ_tkn]□ j ∗ ⌜j<i⌝)
      (* Persistent slot→tag witness, identifying the cell's push tag at index i *)
    ∗ i ↪[γ_slot]□ τ
    ∗ (match s_arr with
      | NotStored => (* Case 0: push hasn't stored.
                        No γ_ar fragment here: push retains [Har_back◯] externally. *)
        ⌜a = NONEV ∧ (τ,Ret #()) ∉ ts⌝ ∗ τ↪[γ_tkn]{#2/3+ɛ} i
      | StoredNotCAS => (* Case 1: push stored, pop not CAS.
                          γ_ar fragment lives here: pop extracts at CAS commit. *)
        i ↪[γ_ar] StoredNotCAS ∗ ⌜a = SOMEV v⌝ ∗ τ↪[γ_tkn]{#2/3+ɛ} i
      | CASed => (* Case 2: pop CAS-ed. *)
        i ↪[γ_ar] CASed ∗ ⌜a = NONEV ∧ τ ∈ m.*1⌝
      end).

  Definition allocated_ar_inv γ_ar γ_tkn γ_slot ts m i a s_arr : iProp Σ :=
    ∃ ts_prefix τ v ɛ,
      allocated_ar_inv_core γ_ar γ_tkn γ_slot ts m i a s_arr ts_prefix τ v ɛ.

  Definition allocated_ar_inv' γ_ar γ_tkn γ_slot ts m i a s_arr : iProp Σ :=
    ∃ ts_prefix τ v ɛ,
      ⌜ts_prefix++[(τ,Call Push v)] `prefix_of` ts⌝
    ∗ allocated_ar_inv_core γ_ar γ_tkn γ_slot ts m i a s_arr ts_prefix τ v ɛ.

  Definition trace_per_tag_inv ts τ s_op :=
    let ts_τ := filter (λ x, x.1 = τ) ts in
    match s_op with
    | PushCalled => ∃ v, ts_τ = [(τ,Call Push v)]
    | PushStored => ∃ v, ts_τ = [(τ,Call Push v)]
    | PushReturned => ∃ v, ts_τ = [(τ,Call Push v); (τ,Ret #())]
    | PopCalled => ts_τ = [(τ,Call Pop #())]
    | PopReturned => ∃ v, ts_τ = [(τ,Call Pop #()); (τ,Ret (encode_response (NonEmpty v)))]
    end.

  Definition is_hwq_inv : iProp Σ :=
    ∃ sz l_ar l_back ar (back : nat) ts m γ_back γ_ar γ_op γ_tkn γ_match γ_slot
      (M_ar : gmap nat array_state) (M_op : gmap positive operation_state)
      (M_tkn : gmap positive nat) (M_slot : gmap nat positive),
      ⌜ q = (#(Z.of_nat sz), #(LitLoc l_ar), #(LitLoc l_back))%V ⌝
    ∗ ⌜per_tag_wellformed_bag NeverEmpty (λ v, val_is_unboxed (SOMEV v)) ts ∧ I_queue_pre ts m⌝
      (* Physical ownerships *)
    ∗ (trace_is tracer ts ∗ l_ar ↦∗ ar ∗ l_back ↦ #back)
      (* Ghost ownerships *)
    ∗ (own γ (to_agree (γ_back,γ_ar,γ_op,γ_tkn,γ_match,γ_slot)) ∗ own γ_back (●MN back)
      ∗ ghost_map_auth γ_ar 1 M_ar ∗ ghost_map_auth γ_op 1 M_op
      ∗ ghost_map_auth γ_tkn 1 M_tkn ∗ own γ_match (●ML m)
      ∗ ghost_map_auth γ_slot 1 M_slot)
      (* domain contraints; track [length ar = sz] so that bounded FAA stores succeed *)
    ∗ ⌜dom M_tkn = dom M_op ∧ dom M_ar = list_to_set (seq 0 back) ∧ dom M_op = events_of_trace ts
       ∧ length ar = sz ∧ dom M_slot = list_to_set (seq 0 back)⌝
      (* Push stored-state ⇒ slot is stored AND M_slot points back to the tag. *)
    ∗ ⌜∀ τ s_op i, M_op !! τ = Some s_op → is_push_stored_state s_op →
                    M_tkn !! τ = Some i →
                    (M_ar !! i = Some StoredNotCAS ∨ M_ar !! i = Some CASed)
                    ∧ M_slot !! i = Some τ⌝
      (* allocated array *)
    ∗ ([∗ list] i↦a ∈ take back ar, allocated_ar_inv γ_ar γ_tkn γ_slot ts m i a (M_ar!!!i))
      (* unallocated array *)
    ∗ ⌜Forall (λ a, a = NONEV) (drop back ar)⌝
      (* nodup of m *)
    ∗ ([∗ list] '(τ1, τ2) ∈ m, (∃ i, τ1↪[γ_tkn]{#2/3} i) ∗ (∃ i, τ2↪[γ_tkn]{#2/3} i))
      (* trace *)
    ∗ ([∗ map] τ↦s_op ∈ M_op, ⌜trace_per_tag_inv ts τ s_op⌝)
      (* finished push *)
    ∗ ([∗ list] τ ∈ (filter (is_ret_push∘snd) ts).*1, ∃ i j, τ↪[γ_tkn]□ i ∗ own γ_back (◯MN j) ∗ ⌜i<j⌝).

  Definition is_hwq_trace := inv queueN is_hwq_inv.

  Lemma allocated_ar_inv_allocated_ar_inv' γ_ar γ_tkn γ_slot ts m i a s_arr :
    trace_is tracer ts -∗ allocated_ar_inv γ_ar γ_tkn γ_slot ts m i a s_arr -∗
    trace_is tracer ts ∗ allocated_ar_inv' γ_ar γ_tkn γ_slot ts m i a s_arr.
  Proof.
    iIntros "Htrace".
    iDestruct 1 as (ts_prefix τ v ɛ) "[Hhist H]".
    iDestruct (hist_trace_is_prefix with "Htrace Hhist") as %Hprefix.
    iFrame "Htrace Hhist H". iPureIntro. done.
  Qed.

  Lemma big_sepL_allocated_ar_inv_allocated_ar_inv' l (M_ar: gmap nat array_state) γ_ar γ_tkn γ_slot ts m :
    trace_is tracer ts -∗ ([∗ list] i↦a ∈ l, allocated_ar_inv γ_ar γ_tkn γ_slot ts m i a (M_ar!!!i)) -∗
    trace_is tracer ts ∗ ([∗ list] i↦a ∈ l, allocated_ar_inv' γ_ar γ_tkn γ_slot ts m i a (M_ar!!!i)).
  Proof.
    iIntros "Htrace Hs".
    iInduction l as [|a l] "IH" using rev_ind.
    - rewrite !big_sepL_nil. iFrame.
    - rewrite !big_sepL_snoc.
      iDestruct "Hs" as "[H Hs]".
      iDestruct ("IH" with "Htrace H") as "[Htrace $]".
      iApply (allocated_ar_inv_allocated_ar_inv' with "Htrace Hs").
  Qed.

  Lemma allocated_ar_inv'_allocated_ar_inv γ_ar γ_tkn γ_slot ts m i a s_arr :
    allocated_ar_inv' γ_ar γ_tkn γ_slot ts m i a s_arr ⊢
    allocated_ar_inv γ_ar γ_tkn γ_slot ts m i a s_arr.
  Proof. iDestruct 1 as (ts_prefix τ v ɛ) "[_ $]". Qed.

  Lemma big_sepL_allocated_ar_inv'_allocated_ar_inv l (M_ar: gmap nat array_state) γ_ar γ_tkn γ_slot ts m :
    ([∗ list] i↦a ∈ l, allocated_ar_inv' γ_ar γ_tkn γ_slot ts m i a (M_ar!!!i)) ⊢
    ([∗ list] i↦a ∈ l, allocated_ar_inv γ_ar γ_tkn γ_slot ts m i a (M_ar!!!i)).
  Proof. apply big_sepL_mono => ???. apply allocated_ar_inv'_allocated_ar_inv. Qed.

  (**********************************************************)
  (* Begin LLM-generated code. *)
  (* tool: Claude Code 2.1.111
     model: Claude Opus 4.7 with 1M context (claude-opus-4-7)
     parameters:
        effort = max
        context window = 1000000
        max output tokens = 128000 *)

  (* No τ can have 2/3 token AT TWO different fragments simultaneously. Useful
     to derive [τ ∉ m.*1] given the m_nodup invariant + a 2/3 token outside. *)
  Lemma m_nodup_no_dup_push γ_tkn (m : list (positive * positive)) τ i :
    ([∗ list] '(τ1, τ2) ∈ m, (∃ i, τ1 ↪[γ_tkn]{#2/3} i) ∗ (∃ i, τ2 ↪[γ_tkn]{#2/3} i)) -∗
    τ ↪[γ_tkn]{#2/3} i -∗
    ⌜τ ∉ m.*1⌝.
  Proof.
    iIntros "Hm_nodup Htkn".
    iIntros (Hin).
    apply list_elem_of_fmap in Hin as [[τ1 τ2] [Heq Hin]]. simpl in Heq. subst τ1.
    apply list_elem_of_lookup_1 in Hin as [n Hn].
    iDestruct (big_sepL_lookup with "Hm_nodup") as "Hpair"; first exact Hn.
    iDestruct "Hpair" as "[Hex _]".
    iDestruct "Hex" as (i_other) "Htkn_other".
    iDestruct (ghost_map_elem_valid_2 with "Htkn Htkn_other") as %[Hvalid _].
    exfalso. revert Hvalid. rewrite dfrac_op_own dfrac_valid_own. intros Hle.
    apply Qp.le_ngt in Hle. apply Hle. compute_done.
  Qed.

  Lemma m_nodup_no_dup_pop γ_tkn (m : list (positive * positive)) τ i :
    ([∗ list] '(τ1, τ2) ∈ m, (∃ i, τ1 ↪[γ_tkn]{#2/3} i) ∗ (∃ i, τ2 ↪[γ_tkn]{#2/3} i)) -∗
    τ ↪[γ_tkn]{#2/3} i -∗
    ⌜τ ∉ m.*2⌝.
  Proof.
    iIntros "Hm_nodup Htkn".
    iIntros (Hin).
    apply list_elem_of_fmap in Hin as [[τ1 τ2] [Heq Hin]]. simpl in Heq. subst τ2.
    apply list_elem_of_lookup_1 in Hin as [n Hn].
    iDestruct (big_sepL_lookup with "Hm_nodup") as "Hpair"; first exact Hn.
    iDestruct "Hpair" as "[_ Hex]".
    iDestruct "Hex" as (i_other) "Htkn_other".
    iDestruct (ghost_map_elem_valid_2 with "Htkn Htkn_other") as %[Hvalid _].
    exfalso. revert Hvalid. rewrite dfrac_op_own dfrac_valid_own. intros Hle.
    apply Qp.le_ngt in Hle. apply Hle. compute_done.
  Qed.

  (* Cell predicate is monotonic in m: extending m only weakens [τ ∈ m.*1]. *)
  Lemma allocated_ar_inv_mono_m γ_ar γ_tkn γ_slot ts m m_ext i a s_arr :
    allocated_ar_inv γ_ar γ_tkn γ_slot ts m i a s_arr ⊢
    allocated_ar_inv γ_ar γ_tkn γ_slot ts (m ++ m_ext) i a s_arr.
  Proof.
    iDestruct 1 as (ts_prefix τ v ɛ) "(Hcall & %Hub & Hpre & Hslot & Hst)".
    iExists ts_prefix, τ, v, ɛ.
    iFrame "Hcall Hpre Hslot". iSplit; first done.
    destruct s_arr.
    - iExact "Hst".
    - iExact "Hst".
    - iDestruct "Hst" as "[$ %Hpure]".
      iPureIntro. destruct Hpure as [Heq Hin].
      split; first done. rewrite fmap_app /=. apply elem_of_app. left. exact Hin.
  Qed.

  (* Per-tag uniqueness of Push-Call positions: if [ts] has [(τ, Call (Push _))]
     at two positions, they must be the same. Proved via filter+length: the
     filter selects at most 2 elements with at most 1 Call (per_tag_wellformed),
     while two distinct Call positions would force ≥ 2 Calls in the filter. *)
  Lemma per_tag_wellformed_bag_call_push_pos_unique valid_value ts τ v v' i j :
    per_tag_wellformed_bag NeverEmpty valid_value ts →
    ts !! i = Some (τ, Call Push v) →
    ts !! j = Some (τ, Call Push v') →
    i = j.
  Proof.
    intros Hwf Hi Hj.
    eapply per_tag_partial_wellformed_inj_call_index; [|eassumption..].
    eapply per_tag_wellformed_per_tag_partial_wellformed.
    eapply per_tag_wellformed_bag_wellformed.
    eassumption.
  Qed.

  (* Two prefixes of [ts] each ending in the same τ-Call event must be equal. *)
  Lemma per_tag_wellformed_bag_call_push_unique_prefix valid_value ts τ v v' ts1 ts2 :
    per_tag_wellformed_bag NeverEmpty valid_value ts →
    ts1 ++ [(τ, Call Push v)] `prefix_of` ts →
    ts2 ++ [(τ, Call Push v')] `prefix_of` ts →
    ts1 = ts2 ∧ v = v'.
  Proof.
    intros Hwf [k1 Hk1] [k2 Hk2].
    assert (Hpos1 : ts !! length ts1 = Some (τ, Call Push v)).
    { rewrite Hk1 -app_assoc.
      rewrite lookup_app_r; last lia. rewrite Nat.sub_diag. reflexivity. }
    assert (Hpos2 : ts !! length ts2 = Some (τ, Call Push v')).
    { rewrite Hk2 -app_assoc.
      rewrite lookup_app_r; last lia. rewrite Nat.sub_diag. reflexivity. }
    pose proof (per_tag_wellformed_bag_call_push_pos_unique _ _ _ _ _ _ _ Hwf Hpos1 Hpos2)
      as Hlen.
    (* From Hlen: length ts1 = length ts2. Since both have the same length and
       are prefixes of ts ending at the same position, they're equal. *)
    rewrite Hlen in Hpos1.
    rewrite Hpos1 in Hpos2. injection Hpos2 as Heq.
    assert (Hv_eq : v = v').
    { by simplify_eq. }
    subst v'.
    split; last reflexivity.
    (* Two prefixes of ts with the same length are equal. *)
    apply (f_equal (take (length ts1))) in Hk1.
    apply (f_equal (take (length ts2))) in Hk2.
    rewrite take_app3_length in Hk1.
    rewrite take_app3_length in Hk2.
    rewrite -Hlen in Hk2.
    rewrite -Hk1 -Hk2. reflexivity.
  Qed.
  (* End LLM-generated code. *)
  (**********************************************************)
End inv.

Definition I_hwq ts := per_tag_wellformed_bag NeverEmpty (λ v, val_is_unboxed (SOMEV v)) ts ∧ I_queue ts.

Definition repr_queue `{!traceG Σ, !hwqG Σ} : mgc_repr Σ := {|
  I_lang := I_hwq;
  mgc_inv _ tracer γ q := is_hwq_trace γ q tracer;
|}.

Lemma aspect_dfrac_2third_1third : (2/3 + 1/3)%Qp = 1%Qp.
Proof. compute_done. Qed.

Lemma aspect_dfrac_3quarter_1quarter : (3/4 + 1/4)%Qp = 1%Qp.
Proof. compute_done. Qed.

(* For [allocated_ar_inv], the cell predicate has [τ ↪{#2/3+ɛ} i].
   With ɛ = 1/3 * 1/4 = 1/12 we get exactly 3/4. *)
Lemma aspect_dfrac_3quarter_eq : (2/3 + 1/(pos_to_Qp 12))%Qp = (3/4)%Qp.
Proof. compute_done. Qed.

