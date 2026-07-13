(* defs.v — Ghost state, Iris invariant, trace invariant for the
   meta-configuration-tracking proof of the Herlihy-Wing queue.

   The proof maintains, alongside the physical heap, a ghost meta-config
   [M_g : gset single_config]. Each (s, π) ∈ M_g records a possible atomic
   linearization of the trace so far. The headline invariant is

       mcfg_steps mcfg_init (set_to_propset M_g) ts ∧ M_g ≠ ∅

   and the trace invariant exposed to mgc.v is

       I_lang_hwq ts := I_metaconfig ts ∧ per_tag_wellformed ts

   which converts to [trace_linearizable] via
   [metaconfig_tracking_iff_linearizable] (tracking.v). *)

From stdpp Require Import base gmap propset.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic Require Import linear.
From iris_logatom.pure_logic.models Require Import bag_like.
From iris_logatom.pure_logic.metaconfig Require Import tracking.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gset agree.
From iris.base_logic Require Import invariants ghost_map ghost_var.
From iris.heap_lang Require Import notation.
From iris_logatom.heap_lang Require Import mgc.

From case_studies.hw_queue Require Import impl.

(* ====================================================================== *)
(* The queue model. *)

Definition hwq_valid_value : val → Prop :=
  λ v, val_is_unboxed (SOMEV v).

Definition hwq_model : model :=
  queue_model NeverEmpty hwq_valid_value.

(* Concretized single_config for the queue model.
   We use the explicit product type so that Countable instances are
   resolvable without needing the [model] typeclass to be in scope. *)
Module HWQMetaConfigNotation.
Notation single_config_q := (list val * gmap positive proc_status)%type.
End HWQMetaConfigNotation.
Import HWQMetaConfigNotation.

(* ====================================================================== *)
(* Per-process operation status, used to bridge program counters to
   π-entries inside the meta-config gmap. *)

Inductive op_status_t : Set :=
  | OpEnqPending  (v : val)
  | OpEnqReserved (v : val) (i : nat)
  | OpEnqStored   (v : val) (i : nat)
  | OpEnqDone     (v : val) (i : nat)
  | OpDeqPending
  | OpDeqLinearized (v : val)
  | OpDeqDone (v : val).

Global Instance op_status_t_inhabited : Inhabited op_status_t :=
  populate OpDeqPending.

Global Instance op_status_t_eqdec : EqDecision op_status_t.
Proof. solve_decision. Defined.

(* ====================================================================== *)
(* Trace invariant exposed to mgc.v. *)

Definition I_lang_hwq (ts : list (positive*trace)) : Prop :=
  @I_metaconfig hwq_model ts ∧ per_tag_wellformed ts.

Lemma I_lang_hwq_init : I_lang_hwq [].
Proof.
  split.
  - exists mcfg_init, s_init, ∅. split.
    + apply mcfg_steps_nil.
    + rewrite /mcfg_init. apply elem_of_singleton. reflexivity.
  - intros τ. exists #(), #(). rewrite filter_nil. apply prefix_nil.
Qed.

(* ====================================================================== *)
(* CMRA bundle. *)

(* The meta-agreement carrier bundles the four concrete ghost names so
   every process opening the invariant agrees on which γs to use.
   The fourth gname is for JInvSeq-style scan ghost state. *)
Definition hwq_meta_t : Type := (gname * gname * gname * gname)%type.

Class hwqMcG Σ := HwqMcG {
  (* Meta-agreement on the bundled ghost names. *)
  hwqMcG_meta :: inG Σ (agreeR (leibnizO hwq_meta_t));
  (* The gset-form meta-config M_g; exclusive ownership via ghost_var. *)
  hwqMcG_M    :: ghost_varG Σ (gset single_config_q);
  (* Per-process operation status. *)
  hwqMcG_stat :: ghost_mapG Σ positive op_status_t;
  (* Persistent record of stored values at FAA-claimed slots. *)
  hwqMcG_slots :: ghost_mapG Σ nat val;
  (* JInvSeq-style scan position tracker for each pop. Maps τ_p to (l, j)
     where l = scan upper bound (back read at scan start), j = current scan
     position. Tracks pops in OpDeqPending state. *)
  hwqMcG_scan :: ghost_mapG Σ positive (nat * nat);
}.

Definition hwqMcΣ : gFunctors :=
  #[ GFunctor (agreeRF (leibnizO hwq_meta_t));
     ghost_varΣ (gset single_config_q);
     ghost_mapΣ positive op_status_t;
     ghost_mapΣ nat val;
     ghost_mapΣ positive (nat * nat) ].

Global Instance subG_hwqMcΣ Σ : subG hwqMcΣ Σ → hwqMcG Σ.
Proof. solve_inG. Qed.

Definition hwqN : namespace := nroot .@ "case_studies.hw_queue.metaconfig".

(* ====================================================================== *)
(* Iris invariant body and is_hwq. *)

Section inv.
  Context `{!heapGS Σ, !traceG Σ, !hwqMcG Σ}.

  (* Bridge between per-process status and gmap entries inside M_g.
     For each τ ∈ dom stat, every (_, π) ∈ M_g has π !! τ in the form
     prescribed by stat !! τ.

     This is the heart of the partial-tracker bookkeeping. We keep the
     definition here as a placeholder Prop; subsequent passes flesh out
     the precise per-status correspondence. *)
  Definition stat_consistent
      (stat : gmap positive op_status_t)
      (M_g : gset single_config_q)
      (ts : list (positive*trace)) : Prop :=
    ∀ τ, match stat !! τ with
    | None => ∀ s π, (s, π) ∈ M_g → π !! τ = None
    | Some (OpEnqPending v) =>
        (* Before any LP: all configurations agree π[τ] is pending.
           TLA+ CFTypeOK clause E1: c.fres[p] = BOT. *)
        ∀ s π, (s, π) ∈ M_g → π !! τ = Some (encode_request (Push v), None)
    | Some (OpEnqReserved v _) | Some (OpEnqStored v _) =>
        (* Post-FAA (Reserved) and post-Store (Stored): TLA+ CFTypeOK clauses
           E2/E3 say c.fres[p] ∈ {ACK, BOT} — DISJUNCTIVE per config. After
           Phase 2 FAA, the chain helper populates LP'd-τ configs alongside
           Pending-τ configs. After Phase 3 Store, the branching keeps both
           forms. At least one config has τ linearized. *)
        (∀ s π, (s, π) ∈ M_g →
          π !! τ = Some (encode_request (Push v), None)
        ∨ π !! τ = Some (encode_request (Push v), Some #())) ∧
        (∃ s π, (s, π) ∈ M_g ∧
          π !! τ = Some (encode_request (Push v), Some #()))
    | Some (OpEnqDone v _) =>
        ∀ s π, (s, π) ∈ M_g →
          π !! τ = Some (encode_request (Push v), Some #())
    | Some OpDeqPending =>
        (* TLA+ approach: M can have configs with τ_p speculatively LP'd.
           This is essential for D3-style rebuild at Pop's CAS LP. *)
        ∀ s π, (s, π) ∈ M_g →
          π !! τ = Some (encode_request Pop, None) ∨
          ∃ v, π !! τ = Some (encode_request Pop,
                              Some (encode_response (NonEmpty v)))
    | Some (OpDeqLinearized v) =>
        (* After CmpXchg success: SOME configurations have the pop
           linearized, others may still have it pending. The "linearized"
           configurations are those whose queue had v at head. *)
        ∃ s π, (s, π) ∈ M_g ∧
          π !! τ = Some (encode_request Pop, Some (encode_response (NonEmpty v)))
    | Some (OpDeqDone v) =>
        ∀ s π, (s, π) ∈ M_g →
          π !! τ = Some (encode_request Pop, Some (encode_response (NonEmpty v)))
    end.
  (* The shape relating physical array to the slots ghost map. Slots are
     monotonically tracked: a slot recorded as Some v means the slot was
     written to v at some point, even if subsequently overwritten with NONEV.
     Conversely, an array cell containing SOMEV v must have its slot recorded. *)
  Definition slots_consistent
      (items : list val) (slots : gmap nat val) : Prop :=
    (∀ i v, slots !! i = Some v →
           (i < length items)%nat ∧
           (items !! i = Some (SOMEV v) ∨ items !! i = Some NONEV)) ∧
    (∀ i v, items !! i = Some (SOMEV v) → slots !! i = Some v).

  (* Every cell in the items array is either NONEV or [SOMEV w] for some
     value w such that [SOMEV w] is unboxed. Maintained by init (all NONEV)
     and store (SOMEV v_push with [SOMEV v_push] unboxed by spec precondition). *)
  Definition items_well_shaped (items : list val) : Prop :=
    Forall (λ v, v = NONEV ∨ ∃ w, v = SOMEV w ∧ val_is_unboxed (SOMEV w)) items.

  (* Trace-stat consistency: links each entry in [stat] to the per-tag filter
     of the trace [ts]. For pending operations only the Call event is in [ts];
     for done operations both Call and Ret are in [ts]. *)
  Definition trace_stat_consistent
      (stat : gmap positive op_status_t)
      (ts : list (positive*trace)) : Prop :=
    ∀ τ, match stat !! τ with
    | None => filter (λ t, t.1 = τ) ts = []
    | Some (OpEnqPending v) | Some (OpEnqReserved v _) | Some (OpEnqStored v _) =>
        filter (λ t, t.1 = τ) ts = [(τ, Call (encode_request (Push v)))]
    | Some (OpEnqDone v _) =>
        filter (λ t, t.1 = τ) ts =
          [(τ, Call (encode_request (Push v))); (τ, Ret #())]
    | Some OpDeqPending | Some (OpDeqLinearized _) =>
        filter (λ t, t.1 = τ) ts = [(τ, Call (encode_request Pop))]
    | Some (OpDeqDone v) =>
        filter (λ t, t.1 = τ) ts =
          [(τ, Call (encode_request Pop));
           (τ, Ret (encode_response (NonEmpty v)))]
    end.

  (* JInvSeq predicate (TLA+ Inv_Main scaffolding, adapted for this work's
     scan direction).
     For lin_witness for slot i, we need a config with v_i at TAIL.
     JInvSeq requires that for each stored slot k > i, there's a witnessing
     scanning pop τ_d via scan_map. *)
  Definition JInvSeq_for_tail
      (i : nat)
      (slots : gmap nat val)
      (stat : gmap positive op_status_t)
      (scan_map : gmap positive (nat * nat)) : Prop :=
    ∀ k, (k > i)%nat → is_Some (slots !! k) →
      ∃ τ_d l j,
        stat !! τ_d = Some OpDeqPending ∧
        scan_map !! τ_d = Some (l, j) ∧
        (k < l)%nat ∧ (i < j)%nat.

  (* JInvSeq (direction-agnostic, TLA+-parameterized form).
     For a sequence seq (a list of slot indices) representing the LP order
     of pushes, JInvSeq(seq) holds iff: for each inversion (n < m position-wise
     but seq[n] > seq[m] index-wise) where slot seq[m] is stored, there's a
     witnessing scanning pop. This is the TLA+ formulation that supports
     BOTH "v at head" and "v at tail" seq orderings. *)
  Definition JInvSeq
      (seq : list nat)
      (slots : gmap nat val)
      (stat : gmap positive op_status_t)
      (scan_map : gmap positive (nat * nat)) : Prop :=
    ∀ n m k_n k_m,
      (n < m)%nat →
      seq !! n = Some k_n →
      seq !! m = Some k_m →
      (k_n > k_m)%nat →
      is_Some (slots !! k_m) →
      ∃ τ_d l j,
        stat !! τ_d = Some OpDeqPending ∧
        scan_map !! τ_d = Some (l, j) ∧
        (k_n < l)%nat ∧ (k_m < j)%nat.

  (* GoodEnqSet (TLA+-aligned, uses stat fallback):
     A slot k may be in A if either items[k] = SOMEV v (stored), OR there's
     a τ_e at OpEnqReserved with i = k (post-FAA, pre-store).
     This corresponds to TLA+'s GoodEnqSet which allows k ∈ A when Q[k] ≠ BOT
     OR ∃ q : pc[q] = "E2" /\ i[q] = k. *)
  Definition GoodEnqSet
      (A : gset nat) (items : list val)
      (stat : gmap positive op_status_t) : Prop :=
    (∀ k v, items !! k = Some (SOMEV v) → k ∈ A) ∧
    (∀ k, k ∈ A →
      (∃ v, items !! k = Some (SOMEV v)) ∨
      (∃ τ_e v_e, stat !! τ_e = Some (OpEnqReserved v_e k))).

  (* Parameterized linearization witness (TLA+ Inv_Main analog).
     For each valid (A, seq) — a permutation of stored or reserved slots
     satisfying JInvSeq — there's a config in M_g whose state s matches seq's
     entries (via items for stored cells; via OpEnqReserved fallback for
     post-FAA pre-Store cells).

     CORE MATCH (slots-based): s[n] = v when slots[seq[n]] = v. This is
     compatible with all existing derivation lemmas.
     EXTRA MATCH (items + stat): for each (n, k) in seq, EITHER items[k] =
     SOMEV v with s[n] = v, OR ∃ τ_e at OpEnqReserved with i_e = k and
     s[n] = v_e. *)
  Definition lin_witness_seq
      (M_g : gset single_config_q)
      (items : list val) (slots : gmap nat val)
      (stat : gmap positive op_status_t)
      (scan_map : gmap positive (nat * nat))
      : Prop :=
    ∀ (A : gset nat) (seq : list nat),
      GoodEnqSet A items stat →
      NoDup seq →
      list_to_set seq = A →
      JInvSeq seq slots stat scan_map →
      ∃ s π,
        (s, π) ∈ M_g ∧
        length s = length seq ∧
        (* Slots-based match: derived from items_match (stored case) plus
           the OpEnqReserved fallback. *)
        (∀ n k, seq !! n = Some k →
                ∀ v, slots !! k = Some v → s !! n = Some v) ∧
        (* TLA+ items+stat case-style match. *)
        (∀ n k, seq !! n = Some k →
          (∃ v, items !! k = Some (SOMEV v) ∧ s !! n = Some v) ∨
          (∃ τ_e v_e, stat !! τ_e = Some (OpEnqReserved v_e k) ∧ s !! n = Some v_e)) ∧
        (* Conditions on π (GoodRes from TLA+): *)
        (∀ τ_d v_d i_d, stat !! τ_d = Some (OpEnqDone v_d i_d) →
          π !! τ_d = Some (encode_request (Push v_d), Some #())) ∧
        (∀ τ_d v_d, stat !! τ_d = Some (OpDeqLinearized v_d) →
          π !! τ_d = Some (encode_request Pop,
                           Some (encode_response (NonEmpty v_d)))) ∧
        (∀ τ_d v_d, stat !! τ_d = Some (OpDeqDone v_d) →
          π !! τ_d = Some (encode_request Pop,
                           Some (encode_response (NonEmpty v_d)))) ∧
        (∀ τ_d, stat !! τ_d = Some OpDeqPending →
          π !! τ_d = Some (encode_request Pop, None)) ∧
        (∀ τ_e v_e i_e, stat !! τ_e = Some (OpEnqStored v_e i_e) →
          π !! τ_e = Some (encode_request (Push v_e), Some #())) ∧
        (* For OpEnqReserved τ_e at i_e: similar disjunction. *)
        (∀ τ_e v_e i_e, stat !! τ_e = Some (OpEnqReserved v_e i_e) →
          (i_e ∈ A → π !! τ_e = Some (encode_request (Push v_e), Some #())) ∧
          (i_e ∉ A → π !! τ_e = Some (encode_request (Push v_e), None))).

  (* FAA-uniqueness: every stored slot index is strictly less than [back_val],
     so the next FAA result is a fresh index never yet stored. *)
  Definition slots_bounded
      (slots : gmap nat val) (back_val : Z) : Prop :=
    ∀ i v, slots !! i = Some v → (Z.of_nat i < back_val)%Z.

  (* Helper: predicate "τ owns slot (v, i)" — true for Stored or Done. *)
  Definition stat_owns
      (stat : gmap positive op_status_t) (τ : positive) (v : val) (i : nat) : Prop :=
    stat !! τ = Some (OpEnqStored v i) ∨ stat !! τ = Some (OpEnqDone v i).

  (* Helper: predicate "τ has FAA'd index i with value v" — true for Reserved/Stored/Done. *)
  Definition stat_faad
      (stat : gmap positive op_status_t) (τ : positive) (v : val) (i : nat) : Prop :=
    stat !! τ = Some (OpEnqReserved v i) ∨
    stat !! τ = Some (OpEnqStored v i) ∨
    stat !! τ = Some (OpEnqDone v i).

  (* Slot ↔ stat correspondence:
     - Every slot in slots' domain comes from some τ ∈ {Stored, Done} at that index.
     - Conversely, every Stored/Done entry in stat has its slot recorded.
     - FAA-uniqueness: no two ops share a FAA'd index.
     - back_val bound: any FAA-claimed index is strictly less than current back. *)
  Definition slots_stat_iff
      (stat : gmap positive op_status_t) (slots : gmap nat val)
      (back_val : Z) : Prop :=
    (* Stored/Done implies slot recorded. *)
    (∀ τ v i, stat_owns stat τ v i → slots !! i = Some v) ∧
    (* Slot recorded implies some τ owns it. *)
    (∀ i v, slots !! i = Some v → ∃ τ, stat_owns stat τ v i) ∧
    (* FAA-uniqueness: no two Reserved/Stored/Done share an index. *)
    (∀ τ_1 τ_2 v_1 v_2 i,
       stat_faad stat τ_1 v_1 i →
       stat_faad stat τ_2 v_2 i →
       τ_1 = τ_2) ∧
    (* back-bound: every Reserved/Stored/Done index is strictly less than back_val. *)
    (∀ τ v i,
       stat_faad stat τ v i →
       (Z.of_nat i < back_val)%Z).

  (* Extract all (τ, v) pairs where π[τ] = Pending Push v in cfg.
     encode_request (Push v) = SOMEV v = InjRV v (per bag_like.v:17).
     Pending = response field is None. *)
  Definition pending_push_of_config (cfg : single_config_q) : list (positive * val) :=
    omap (λ '(τ, v),
      if v is (InjRV v, None) then Some (τ,v)
      else None) (map_to_list cfg.2).

  Definition lineraize_pending_push (pushes : list (positive*val)) (cfg : single_config_q) : single_config_q :=
    (cfg.1 ++ pushes.*2,
      map_imap (λ τ x,
        if bool_decide (τ ∈ (pushes.*1)) then Some (x.1, Some #())
        else Some x) cfg.2).

  (* Closure invariants — TLA+ Inv_Main big-step form (E1 expansion).

     closure_push corresponds to TLA+'s Inv_Main, which iterates over
     A ⊆ 1..X-1 (slot indices). A slot k is in A only if either Q[k] ≠ BOT
     (post-store) or some process at "E2" reserved it (post-FAA, pre-store).
     A process at "E1" (= Coq's OpEnqPending) has no slot, so it doesn't
     contribute to A.

     Hence closure_push only ranges over Pending pushes whose process has
     ALREADY FAA'd a slot — i.e., stat[τ] ∈ {OpEnqReserved, OpEnqStored}.
     OpEnqDone is excluded too because its π[τ] is always LP'd (no Pending
     to close over). OpEnqPending is excluded because the process has no
     slot yet (corresponds to TLA+'s "E1" stage). *)
  Definition closure_push
      (M_g : gset single_config_q)
      (stat : gmap positive op_status_t) : Prop :=
    ∀ cfg (pushes : list (positive * val)),
      cfg ∈ M_g →
      NoDup pushes.*1 →
      pushes ⊆ pending_push_of_config cfg →
      (∀ pv, pv ∈ pushes → ∃ v i,
         stat !! pv.1 = Some (OpEnqReserved v i) ∨
         stat !! pv.1 = Some (OpEnqStored v i)) →
      lineraize_pending_push pushes cfg ∈ M_g.

  (* All NoDup sublist-permutations of xs. Combines stdpp's powermset
     (which gives all sublists) with permutations (which gives all orderings
     of each sublist). *)
  Definition all_push_lists (xs : list (positive * val)) : list (list (positive * val)) :=
    powermset xs ≫= permutations.

  (* Expanded M_g after Phase 1 Call enq: each (cfg ∈ M_g, pushes-list) pair
     contributes the linearized config. The pushes-list ranges over all
     NoDup sublist-permutations of pending pushes of the post-Call cfg. *)
  Definition expand_M_g_call_enq
      (M_g : gset single_config_q) (τ : positive) (v_push : val)
    : gset single_config_q :=
    let call_cfg := λ cfg : single_config_q,
      (cfg.1, <[τ:=(encode_request (Push v_push), None)]> cfg.2) in
    list_to_set
      (elements M_g ≫= (λ cfg,
         (λ pushes, lineraize_pending_push pushes (call_cfg cfg))
            <$> all_push_lists (pending_push_of_config (call_cfg cfg)))).

  Definition closure_pop (M_g : gset single_config_q) : Prop :=
    ∀ v s π τ,
      (v :: s, π) ∈ M_g →
      π !! τ = Some (encode_request Pop, None) →
      (s, <[τ:=(encode_request Pop, Some (encode_response (NonEmpty v)))]>π) ∈ M_g.

  (* scan_map domain is contained in stat domain: if τ has a scan_map entry,
     then τ exists in stat. Equivalently: stat[τ] = None → scan_map[τ] = None.
     This is needed at Phase 1 Call deq: τ is fresh (stat[τ] = None), so we
     can conclude scan_map[τ] = None. Maintained trivially while scan_map
     isn't updated (scan_map stays empty). *)
  Definition scan_map_dom_in_stat
      (stat : gmap positive op_status_t)
      (scan_map : gmap positive (nat * nat)) : Prop :=
    ∀ τ, stat !! τ = None → scan_map !! τ = None.

  (* scan_map's upper bound l is bounded by back_val. Each scan_map[τ_p] = (l, _)
     records the scan bound l = min(back at scan time, sz). Since back only
     grows, l ≤ current back_val.
     This is the key invariant for the suffix lemma in ENQ_P2_LIN_SEQ's hard
     case: scan_map cursors cannot witness inversions at indices ≥ current
     back_val. *)
  Definition scan_map_l_bounded
      (scan_map : gmap positive (nat * nat))
      (back_val : Z) : Prop :=
    ∀ τ_p l j, scan_map !! τ_p = Some (l, j) → (Z.of_nat l ≤ back_val)%Z.

  Definition hwq_inv_body
      (γ_meta γM γ_status γ_slots γ_scan : gname)
      (sz : Z) (ar back : loc) (l : loc) : iProp Σ :=
    ∃ (items : list val) (back_val : Z)
      (ts : list (positive*trace))
      (M_g : gset single_config_q)
      (stat : gmap positive op_status_t)
      (slots : gmap nat val)
      (scan_map : gmap positive (nat * nat)),
      (* Physical heap *)
      back ↦ #back_val ∗ ar ↦∗ items ∗ trace_is l ts ∗
      (* Length / shape constraints *)
      ⌜length items = Z.to_nat sz⌝ ∗ ⌜(0 ≤ back_val)%Z⌝ ∗
      (* Ghost authority. *)
      ghost_var γM 1 M_g ∗
      ghost_map_auth γ_status 1 stat ∗
      ghost_map_auth γ_slots 1 slots ∗
      ghost_map_auth γ_scan 1 scan_map ∗
      ([∗ map] i ↦ v ∈ slots, i ↪[γ_slots]□ v) ∗
      (* Headline invariant: M_g (viewed as propset) is reachable from
         mcfg_init via the trace, and M_g is non-empty. The previous
         M_full ≡ set_to_propset M_g equivalence is folded in. *)
      ⌜@mcfg_steps hwq_model mcfg_init (set_to_propset M_g) ts⌝ ∗
      ⌜M_g ≠ ∅⌝ ∗
      ⌜per_tag_wellformed ts⌝ ∗
      ⌜stat_consistent stat M_g ts⌝ ∗
      ⌜slots_consistent items slots⌝ ∗
      ⌜items_well_shaped items⌝ ∗
      ⌜trace_stat_consistent stat ts⌝ ∗
      ⌜lin_witness_seq M_g items slots stat scan_map⌝ ∗
      ⌜slots_bounded slots back_val⌝ ∗
      ⌜slots_stat_iff stat slots back_val⌝ ∗
      ⌜closure_push M_g stat⌝ ∗
      ⌜scan_map_dom_in_stat stat scan_map⌝ ∗
      ⌜scan_map_l_bounded scan_map back_val⌝.

  Definition is_hwq (l : loc) (γ : gname) (obj : val) : iProp Σ :=
    ∃ (γM γ_status γ_slots γ_scan : gname) (sz : Z) (ar back : loc),
      ⌜obj = (#sz, #ar, #back)%V⌝ ∗
      ⌜(0 ≤ sz)%Z⌝ ∗
      own γ (to_agree ((γM, γ_status, γ_slots, γ_scan) : leibnizO hwq_meta_t)) ∗
      inv hwqN (hwq_inv_body γ γM γ_status γ_slots γ_scan sz ar back l).

  Global Instance is_hwq_persistent γ obj l : Persistent (is_hwq γ obj l).
  Proof. apply _. Qed.

End inv.

(* ====================================================================== *)
(* The [repr] record for [bdgjst_free]. *)

Definition hwq_repr `{!traceG Σ, !hwqMcG Σ} : mgc_repr Σ := {|
  I_lang  := I_lang_hwq;
  mgc_inv := λ heapGS0, @is_hwq Σ heapGS0 _ _;
|}.

(* The init wrapper expected by [bdgjst_free]: takes [#()]. *)
Definition init_hwq (sz : Z) : val := (λ: <>, new_queue #sz)%V.
