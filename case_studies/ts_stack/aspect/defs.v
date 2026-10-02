(* The TS stack: the ghost state, the invariant, and the witnesses that the proofs of the
   operations pass around. *)

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
From case_studies.ts_stack.aspect Require Import pure.

Record ts_names := TsNames {
  γ_m : gname; γ_pts : gname; γ_c : gname; γ_TS : gname; γ_K : gname; γ_os : gname;
  γ_O : list gname; γ_tid : gname;
}.

Class tsG Σ := {
  #[export] tsG_names :: inG Σ (agreeR (leibnizO ts_names));
  #[export] tsG_m :: inG Σ (mono_listR (leibnizO (positive * positive)));
  #[export] tsG_pts :: inG Σ (mono_listR (leibnizO pt_entry));
  #[export] tsG_c :: inG Σ mono_natR;
  #[export] tsG_TS :: ghost_mapG Σ positive (nat * nat);
  #[export] tsG_K :: ghost_mapG Σ positive nat;
  #[export] tsG_os :: ghost_mapG Σ positive op_state;
  #[export] tsG_owner :: ghost_varG Σ (bool * nat);
  #[export] tsG_tid :: threadIDG Σ;
}.
Definition tsΣ : gFunctors := #[
  GFunctor (agreeR (leibnizO ts_names));
  GFunctor (mono_listR (leibnizO (positive * positive)));
  GFunctor (mono_listR (leibnizO pt_entry));
  GFunctor mono_natR;
  ghost_mapΣ positive (nat * nat);
  ghost_mapΣ positive nat;
  ghost_mapΣ positive op_state;
  ghost_varΣ (bool * nat);
  threadIDΣ].
Global Instance subG_tsG Σ : subG tsΣ Σ → tsG Σ.
Proof. solve_inG. Qed.

Definition tsN := nroot .@ "case_studies.ts_stack.aspect".

#[export] Instance tss_inhabited : Inhabited tss := populate (tss_init []).

(* the nodes strictly between positions lo and hi of pool j are taken *)
Definition taken_between (sents : list loc) (pS : list pt_entry) (mS : list (positive * positive))
    (j lo hi : nat) : Prop :=
  hi ≤ length (pool_list_l sents pS j) ∧
  ∀ i z, lo < i < hi → pool_list_l sents pS j !! i = Some z → takenb_l sents pS mS z = true.

Lemma pool_list_l_prefix sents pS pS' j :
  pS `prefix_of` pS' → pool_list_l sents pS j `prefix_of` pool_list_l sents pS' j.
Proof. intros Hp. rewrite /pool_list_l. destruct (sents !! j); [|done]. by apply prefix_cons, pnodes_prefix. Qed.

Lemma taken_between_mono sents pS pS' mS mS' j lo hi :
  pS `prefix_of` pS' → mS `prefix_of` mS' →
  taken_between sents pS mS j lo hi → taken_between sents pS' mS' j lo hi.
Proof.
  intros Hp Hm [Hlen Hall]. pose proof (pool_list_l_prefix sents _ _ j Hp) as Hpl.
  split; [pose proof (prefix_length _ _ Hpl); lia|].
  intros i z Hi Hz. destruct (lookup_lt_is_Some_2 (pool_list_l sents pS j) i) as [z' Hz']; [lia|].
  rewrite (prefix_lookup_Some _ _ _ _ Hz' Hpl) in Hz. injection Hz as <-.
  by eapply takenb_l_mono; [| |apply (Hall i)].
Qed.

Lemma pool_list_mono σ σ' j :
  s_sent σ = s_sent σ' → s_pts σ `prefix_of` s_pts σ' → pool_list σ j `prefix_of` pool_list σ' j.
Proof. intros Hs Hp. rewrite /pool_list Hs. by apply pool_list_l_prefix. Qed.

Lemma pool_list_snap σ sents pS j :
  s_sent σ = sents → pS `prefix_of` s_pts σ → pool_list_l sents pS j `prefix_of` pool_list σ j.
Proof. intros <- Hp. by apply pool_list_l_prefix. Qed.

(* a pool whose owner has not inserted since a snapshot *)
Lemma pool_list_frozen σ sents pS j :
  s_sent σ = sents → pS `prefix_of` s_pts σ →
  length (pool_list σ j) = length (pool_list_l sents pS j) → pool_list σ j = pool_list_l sents pS j.
Proof. intros Hs Hp Hlen. symmetry. apply prefix_length_eq; [by apply pool_list_snap|lia]. Qed.

(* What a walk of pool j by get_youngest found: pS is the snapshot when it read the top A,
   and (pT, mT) one in which the nodes above the result are taken. *)
Definition walk_res (sents : list loc) (pS pT : list pt_entry) (mT : list (positive * positive))
    (j : nat) (A : loc) (ro : option (loc * nat)) : Prop :=
  pS `prefix_of` pT ∧ ∃ ia, pool_list_l sents pS j !! ia = Some A ∧
  match ro with
  | None => ∀ z, z ∈ pool_list_l sents pS j → takenb_l sents pT mT z = true
  | Some (x, k) => pool_list_l sents pS j !! k = Some x ∧ 1 ≤ k ≤ ia ∧
      ∀ i z, k < i → pool_list_l sents pS j !! i = Some z → takenb_l sents pT mT z = true
  end.

Lemma tags_prefix (pS pS' : list pt_entry) p :
  pS `prefix_of` pS' → p ∈ (λ e : pt_entry, e.1.1) <$> pS → p ∈ (λ e : pt_entry, e.1.1) <$> pS'.
Proof. intros [l ->] Hp. rewrite fmap_app elem_of_app. by left. Qed.

Definition opt_node (ro : option (loc * nat)) : val :=
  match ro with Some (x, _) => SOMEV #x | None => NONEV end.

(* the scan of a pool by tryRem: the top read by the walk, and the candidate (if any) with its
   position and timestamp *)
Definition wentry : Type := loc * option (loc * nat * (nat * nat)).

Definition res_of (ws : list wentry) (j : nat) : scan_res :=
  match ws !! j with Some (_, Some (_, k, t)) => Some (k, t) | _ => None end.

(* the youngest candidate so far: its node, timestamp, pool and the top read by its walk *)
Definition youngest_ok (pools : loc) (ws : list wentry) (yv cv pv tv : val) : Prop :=
  (yv = NONEV ∧ cv = (#0, #0)%V ∧ ∀ j w, ws !! j = Some w → w.2 = None) ∨
  (∃ (y : loc) (jy : nat) (A : loc) (ky : nat) (tb : nat * nat), yv = SOMEV #y ∧ cv = (#tb.1, #tb.2)%V ∧
     pv = #(pools +ₗ jy) ∧ tv = #A ∧ ws !! jy = Some (A, Some (y, ky, tb)) ∧
     ∀ j A' x k t, ws !! j = Some (A', Some (x, k, t)) → ¬ tb.2 < t.1).

Lemma youngest_ok_none pools ws yv cv pv tv (A : loc) :
  youngest_ok pools ws yv cv pv tv → youngest_ok pools (ws ++ [(A, None)]) yv cv pv tv.
Proof.
  intros [(? & ? & Hnone)|(y & jy & Ay & ky & tb & ? & ? & ? & ? & Hjy & Hmax)].
  - left. split_and!; [done|done|]. intros j w [Hw|[_ Hw]]%lookup_app_Some; [by eapply Hnone|].
    by apply list_lookup_singleton_Some in Hw as [_ <-].
  - right. exists y, jy, Ay, ky, tb. split_and!; [done..|by apply lookup_app_l_Some|].
    intros j A' x k t [Hw|[_ Hw]]%lookup_app_Some; [by eapply Hmax|].
    apply list_lookup_singleton_Some in Hw as [_ ?]. by simplify_eq.
Qed.

(* a candidate younger than all candidates so far *)
Lemma youngest_ok_new pools ws (A x : loc) k (t : nat * nat) :
  t.1 ≤ t.2 → (∀ j A' x' k' t', ws !! j = Some (A', Some (x', k', t')) → t'.1 ≤ t.2) →
  youngest_ok pools (ws ++ [(A, Some (x, k, t))]) (SOMEV #x) (#t.1, #t.2)%V #(pools +ₗ length ws) #A.
Proof.
  intros Ht Hprev. right. exists x, (length ws), A, k, t. split_and!; [done|done|done|done| |].
  - by rewrite lookup_app_r // Nat.sub_diag.
  - intros j A' x' k' t' [Hw|[Hlen Hw]]%lookup_app_Some.
    + specialize (Hprev _ _ _ _ _ Hw). lia.
    + apply list_lookup_singleton_Some in Hw as [_ Heq]. injection Heq as -> -> -> ->. lia.
Qed.

(* a candidate not younger than the youngest so far *)
Lemma youngest_ok_keep pools ws (A x : loc) k (t : nat * nat) (y : loc) (jy : nat) (Ay : loc) ky (tb : nat * nat) :
  ws !! jy = Some (Ay, Some (y, ky, tb)) →
  (∀ j A' x' k' t', ws !! j = Some (A', Some (x', k', t')) → ¬ tb.2 < t'.1) → ¬ tb.2 < t.1 →
  youngest_ok pools (ws ++ [(A, Some (x, k, t))]) (SOMEV #y) (#tb.1, #tb.2)%V #(pools +ₗ jy) #Ay.
Proof.
  intros Hjy Hmax Ht. right. exists y, jy, Ay, ky, tb. split_and!; [done..|by apply lookup_app_l_Some|].
  intros j A' x' k' t' [Hw|[_ Hw]]%lookup_app_Some; [by eapply Hmax|].
  apply list_lookup_singleton_Some in Hw as [_ Heq]. by injection Heq as -> -> -> ->.
Qed.

Lemma pnodes_in_pool_list (sent : list loc) (pts : list pt_entry) j x s :
  sent !! j = Some s → x ∈ pnodes pts j → x ∈ pool_list_l sent pts j.
Proof. intros Hs Hx. rewrite /pool_list_l Hs. by right. Qed.

(* the LIFO condition of a commit of (b, p) (stack/vis.v) *)
Definition lifo_ok (σ : tss) (b p : positive) : Prop :=
  pre_of_trace (s_ts σ) b p → ∀ c, c ≠ b → ts_tr (s_ts σ) (pts_tags σ) b c →
    c ∈ push_of_trace (s_ts σ) → pt_before (pts_tags σ) c p → c ∈ (s_m σ).*1.

Section inv.
  Context `{!heapGS Σ, !traceG Σ, !tsG Σ}.
  Implicit Types σ : tss.

  (* the owner of a pool (the holder of its thread ID) is pushing iff b *)
  Definition owner_res γs (j : nat) (b : bool) (k : nat) : iProp Σ :=
    ghost_var (γ_O γs !!! j) (1/2) (b, k) ∗
    (if b then own_tid (γ_tid γs) j else ghost_var (γ_O γs !!! j) (1/2) (false, k)).

  Definition node_res σ (x y : loc) : iProp Σ :=
    (x +ₗ 2) ↦ #y ∗ (x +ₗ 3) ↦ #(takenb σ x) ∗ (x +ₗ 1) ↦ tsfield σ x.

  Definition elem_res σ (e : pt_entry) : iProp Σ :=
    match e.2 with
    | Some (x, _) => ∃ v, x ↦□ v ∗ ⌜(e.1.1, Call Push v) ∈ s_ts σ⌝
    | None => True
    end.

  Definition ts_rest γs (pools ctr : loc) σ : iProp Σ :=
    own (γ_m γs) (●ML (s_m σ : list (leibnizO (positive * positive)))) ∗
    own (γ_pts γs) (●ML (s_pts σ : list (leibnizO pt_entry))) ∗
    own (γ_c γs) (●MN (s_c σ)) ∗ ctr ↦ #(s_c σ) ∗
    ghost_map_auth (γ_TS γs) 1 (s_TS σ) ∗ ([∗ map] τ ↦ t ∈ s_TS σ, τ ↪[γ_TS γs]□ t) ∗
    ghost_map_auth (γ_K γs) 1 (s_K σ) ∗ ([∗ map] τ ↦ k ∈ s_K σ, τ ↪[γ_K γs]□ k) ∗
    ghost_map_auth (γ_os γs) 1 (s_os σ) ∗
    ([∗ list] j ↦ (t : loc) ∈ s_top σ, (pools +ₗ j) ↦ #t) ∗
    ([∗ map] x ↦ y ∈ s_next σ, node_res σ x y) ∗
    ([∗ list] e ∈ s_pts σ, elem_res σ e) ∗
    ([∗ list] j ↦ b ∈ s_busy σ, owner_res γs j b (length (pool_list σ j))).

  Definition ts_res γs (n : nat) (pools ctr : loc) (sents : list loc) (tracer : loc) σ : iProp Σ :=
    ⌜tss_inv n σ ∧ s_sent σ = sents⌝ ∗ trace_is tracer (s_ts σ) ∗ ts_rest γs pools ctr σ.

  Definition ts_inv γs n pools ctr sents tracer : iProp Σ :=
    ∃ σ, ts_res γs n pools ctr sents tracer σ.

  Definition is_ts (tracer : loc) (γ : gname) (q : val) : iProp Σ :=
    ∃ γs (pools ctr : loc) (tpl : val) (n : nat) (sents : list loc),
      ⌜q = (#pools, #ctr, tpl, #n)%V ∧ 0 < n ∧ length sents = n⌝ ∗
      own γ (to_agree (γs : leibnizO ts_names)) ∗ is_threadpool (γ_tid γs) tpl n ∗
      inv tsN (ts_inv γs n pools ctr sents tracer).

  Global Instance is_ts_persistent tracer γ q : Persistent (is_ts tracer γ q).
  Proof. apply _. Qed.

  (* a snapshot of the points and of the commits *)
  Definition view γs (pS : list pt_entry) (mS : list (positive * positive)) : iProp Σ :=
    own (γ_pts γs) (◯ML (pS : list (leibnizO pt_entry))) ∗
    own (γ_m γs) (◯ML (mS : list (leibnizO (positive * positive)))).

  Global Instance view_persistent γs pS mS : Persistent (view γs pS mS).
  Proof. apply _. Qed.

  (* the newest node of pool j (in the snapshot pS) is timestamped *)
  Definition last_stamped γs sents (pS : list pt_entry) (j : nat) : iProp Σ :=
    ∀ x τx, ⌜last (pool_list_l sents pS j) = Some x ∧ tag_of_l pS x = Some τx⌝ →
      ∃ t : nat * nat, τx ↪[γ_TS γs]□ t.

  Global Instance last_stamped_persistent γs sents pS j : Persistent (last_stamped γs sents pS j).
  Proof. apply _. Qed.

  Definition walk_wit γs sents (p : positive) (j : nat) (A : loc) (ro : option (loc * nat)) : iProp Σ :=
    ∃ pS pT mT, own (γ_pts γs) (◯ML (pS : list (leibnizO pt_entry))) ∗ view γs pT mT ∗
      ⌜p ∈ (λ e : pt_entry, e.1.1) <$> pS ∧ walk_res sents pS pT mT j A ro⌝.

  Global Instance walk_wit_persistent γs sents p j A ro : Persistent (walk_wit γs sents p j A ro).
  Proof. apply _. Qed.

  (* what justifies the commit of the push of node x by pop p, whenever it happens *)
  Definition lifo_wit γs n pools ctr sents tracer (x : loc) (p : positive) : iProp Σ :=
    □ ∀ σ b, ⌜tss_inv n σ ∧ s_sent σ = sents ∧ tag_of σ x = Some b⌝ -∗
      trace_is tracer (s_ts σ) -∗ ts_rest γs pools ctr σ -∗ ⌜lifo_ok σ b p⌝.

  Global Instance lifo_wit_persistent γs n pools ctr sents tracer x p :
    Persistent (lifo_wit γs n pools ctr sents tracer x p).
  Proof. apply _. Qed.

  Definition stamp_wit γs (x : loc) (t : nat * nat) : iProp Σ :=
    ∃ (pX : list pt_entry) τ, own (γ_pts γs) (◯ML (pX : list (leibnizO pt_entry))) ∗
      ⌜tag_of_l pX x = Some τ⌝ ∗ τ ↪[γ_TS γs]□ t.

  Definition pool_wit γs sents p (j : nat) (w : wentry) : iProp Σ :=
    match w with
    | (A, None) => walk_wit γs sents p j A None
    | (A, Some (x, k, t)) => walk_wit γs sents p j A (Some (x, k)) ∗ stamp_wit γs x t
    end.

  Global Instance pool_wit_persistent γs sents p j w : Persistent (pool_wit γs sents p j w).
  Proof. destruct w as [A [[[x k] t]|]]; apply _. Qed.

  (* the emptiness check of pool j succeeded, relative to the end (pT, mT) of the scan *)
  Definition check_wit γs sents (pT : list pt_entry) mT (j : nat) : iProp Σ :=
    ∃ pj, own (γ_pts γs) (◯ML (pj : list (leibnizO pt_entry))) ∗
      ⌜pT `prefix_of` pj ∧ ∀ x, x ∈ pnodes pT j → takenb_l sents pj mT x = true⌝.

  Definition empty_wit γs (tracer : loc) sents (n : nat) (p : positive) : iProp Σ :=
    ∃ (tsT : list (positive * trace)) (mT : list (positive * positive)) (pT : list pt_entry),
      hist tracer tsT ∗ own (γ_m γs) (◯ML (mT : list (leibnizO (positive * positive)))) ∗
      own (γ_pts γs) (◯ML (pT : list (leibnizO pt_entry))) ∗
      ⌜(p, Call Pop #()) ∈ tsT ∧
        (∀ τ1 r v, (τ1, Ret r) ∈ tsT → (τ1, Call Push v) ∈ tsT → ∃ c x j, (τ1, c, Some (x, j)) ∈ pT) ∧
        (∀ τ2, τ2 ∈ mT.*2 → (τ2, Call Pop #()) ∈ tsT) ∧
        (∀ τ c x j, (τ, c, Some (x, j)) ∈ pT → j < n)⌝ ∗
      [∗ list] j ∈ seq 0 n, check_wit γs sents pT mT j.

  Definition tryRem_post γs (tracer : loc) sents (n : nat) (p : positive) (w : val) : iProp Σ :=
    (⌜w = NONEV⌝ ∗ p ↪[γ_os γs] PopStarted) ∨
    (∃ b v (mC : list (positive * positive)) tsC, ⌜w = SOMEV (SOMEV v) ∧ (b, p) ∈ mC ∧ (b, Call Push v) ∈ tsC⌝ ∗
       p ↪[γ_os γs] PopCommitted ∗ own (γ_m γs) (◯ML (mC : list (leibnizO (positive * positive)))) ∗
       hist tracer tsC) ∨
    (⌜w = SOMEV NONEV⌝ ∗ p ↪[γ_os γs] PopStarted ∗ empty_wit γs tracer sents n p).
End inv.

Definition I_ts (ts : list (positive * trace)) : Prop :=
  per_tag_wellformed_bag MayEmpty (λ _, True) ts ∧ I_stack_vis ts.

Definition repr_ts `{!traceG Σ, !tsG Σ} : mgc_repr Σ := {|
  I_lang := I_ts;
  mgc_inv _ tracer γ q := is_ts tracer γ q;
|}.
