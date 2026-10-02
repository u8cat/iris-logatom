(* The pure part of the TS-stack proof: an abstract view of the stack's state together with
   the ghost data of the proof, the invariant on it, and one lemma per atomic step showing
   that the step preserves the invariant. The Iris proof (aspect.v) only relates this view
   to the physical state and the ghost resources. *)

From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect Require Import stack.
From iris.heap_lang Require Import lang notation.

Inductive op_state :=
  | PushCalled | PushInserted | PushStamped | PushReturned
  | PopCalled | PopStarted | PopCommitted | PopReturned.

(* A point (stack/vis.v) with the counter at that moment; the point of a push records the
   push's node and pool. *)
Definition pt_entry := (positive * nat * option (loc * nat))%type.

Record tss := TSS {
  s_ts : list (positive * trace);       (* the trace *)
  s_m : list (positive * positive);     (* commits (push, pop), in order *)
  s_pts : list pt_entry;                (* points, in order *)
  s_sent : list loc;                    (* the sentinel of each pool *)
  s_top : list loc;                     (* the top pointer of each pool *)
  s_next : gmap loc loc;                (* the next field of every node *)
  s_TS : gmap positive (nat * nat);     (* the timestamps of pushes *)
  s_K : gmap positive nat;              (* the counter at each call *)
  s_os : gmap positive op_state;        (* the progress of each operation *)
  s_c : nat;                            (* the counter *)
  s_busy : list bool;                   (* whether the owner of a pool is pushing *)
}.

Definition timestamp_val (t : option (nat * nat)) : val :=
  match t with
  | Some (t1, t2) => (#t1, #t2)%V
  | None => (#(-1), #(-1))%V
  end.

(* the nodes of pool j in insertion order, without the sentinel *)
Definition pnodes (pts : list pt_entry) (j : nat) : list loc :=
  omap (λ e : pt_entry, match e.2 with
                        | Some (x, j') => if decide (j' = j) then Some x else None
                        | None => None end) pts.

(* Functions of the points and the commits only, so that snapshots determine them. *)
Definition tag_of_l (pts : list pt_entry) (x : loc) : option positive :=
  (λ ie : nat * pt_entry, ie.2.1.1) <$> list_find (λ e : pt_entry, fst <$> e.2 = Some x) pts.

Definition takenb_l (sent : list loc) (pts : list pt_entry) (m : list (positive * positive))
    (x : loc) : bool :=
  bool_decide (x ∈ sent) ||
  match tag_of_l pts x with Some τ => bool_decide (τ ∈ m.*1) | None => false end.

(* the position of a node's commit in m, plus one; 0 for sentinels *)
Definition tk_l (pts : list pt_entry) (m : list (positive * positive)) (x : loc) : nat :=
  match tag_of_l pts x with
  | Some τ => match list_find (λ e, e.1 = τ) m with Some (i, _) => 1 + i | None => 0 end
  | None => 0
  end.

Definition PT_l (pts : list pt_entry) (τ : positive) : option nat :=
  (λ ie : nat * pt_entry, ie.2.1.2) <$> list_find (λ e : pt_entry, e.1.1 = τ) pts.

Definition node_of_l (pts : list pt_entry) (τ : positive) : option (loc * nat) :=
  match list_find (λ e : pt_entry, e.1.1 = τ) pts with
  | Some (_, e) => e.2
  | None => None
  end.

(* the nodes of pool j in insertion order, starting with the sentinel *)
Definition pool_list_l (sent : list loc) (pts : list pt_entry) (j : nat) : list loc :=
  match sent !! j with Some s => s :: pnodes pts j | None => [] end.

(* The invariant of pool j with sentinel s, top t, and owner flag b. *)
Record pool_ok (sent : list loc) (pts : list pt_entry) (m : list (positive * positive))
    (next : gmap loc loc) (TS : gmap positive (nat * nat)) (j : nat) (s t : loc) (b : bool) : Prop := {
  (* next pointers only skip taken nodes *)
  po_next_sent : next !! s = Some s;
  po_next i x : pool_list_l sent pts j !! i = Some x → 0 < i →
    ∃ k y, k < i ∧ pool_list_l sent pts j !! k = Some y ∧ next !! x = Some y ∧
      ∀ i' z, k < i' < i → pool_list_l sent pts j !! i' = Some z → takenb_l sent pts m z = true;
  (* every node above the top is taken, before the top if the top is taken *)
  po_top : ∃ it, pool_list_l sent pts j !! it = Some t ∧
    ∀ i z, it < i → pool_list_l sent pts j !! i = Some z →
      takenb_l sent pts m z = true ∧ (takenb_l sent pts m t = true → tk_l pts m z ≤ tk_l pts m t);
  (* a node is timestamped before the next node of its pool is inserted *)
  po_chain i x y τx τy : 1 ≤ i → pool_list_l sent pts j !! i = Some x →
    pool_list_l sent pts j !! (1 + i) = Some y →
    tag_of_l pts x = Some τx → tag_of_l pts y = Some τy →
    ∃ tx ky, TS !! τx = Some tx ∧ PT_l pts τy = Some ky ∧ tx.2 < ky;
  (* when the owner is not pushing, the newest node is timestamped *)
  po_owner x τ : b = false → last (pool_list_l sent pts j) = Some x → tag_of_l pts x = Some τ →
    is_Some (TS !! τ);
}.

Section defs.
  Context (σ : tss).

  Definition pts_tags : list positive := (λ e : pt_entry, e.1.1) <$> s_pts σ.

  Definition pool_nodes (j : nat) : list loc := pnodes (s_pts σ) j.

  Definition pool_list (j : nat) : list loc := pool_list_l (s_sent σ) (s_pts σ) j.

  Definition node_of (τ : positive) : option (loc * nat) := node_of_l (s_pts σ) τ.
  Definition tag_of (x : loc) : option positive := tag_of_l (s_pts σ) x.
  Definition PT (τ : positive) : option nat := PT_l (s_pts σ) τ.
  Definition takenb (x : loc) : bool := takenb_l (s_sent σ) (s_pts σ) (s_m σ) x.
  Definition taken (x : loc) : Prop := takenb x = true.
  Definition tk (x : loc) : nat := tk_l (s_pts σ) (s_m σ) x.

  Definition tsfield (x : loc) : val := timestamp_val (tag_of x ≫= (s_TS σ !!.)).

  Definition os_ok (τ : positive) (s : op_state) : Prop :=
    let ts_τ := filter (λ x, x.1 = τ) (s_ts σ) in
    match s with
    | PushCalled => (∃ v, ts_τ = [(τ, Call Push v)]) ∧ τ ∉ pts_tags ∧ s_TS σ !! τ = None
    | PushInserted => (∃ v, ts_τ = [(τ, Call Push v)]) ∧ τ ∈ pts_tags ∧ s_TS σ !! τ = None
    | PushStamped => (∃ v, ts_τ = [(τ, Call Push v)]) ∧ τ ∈ pts_tags ∧ is_Some (s_TS σ !! τ)
    | PushReturned => (∃ v, ts_τ = [(τ, Call Push v); (τ, Ret #())]) ∧ τ ∈ pts_tags ∧
                      is_Some (s_TS σ !! τ)
    | PopCalled => ts_τ = [(τ, Call Pop #())] ∧ τ ∉ pts_tags ∧ τ ∉ (s_m σ).*2
    | PopStarted => ts_τ = [(τ, Call Pop #())] ∧ τ ∈ pts_tags ∧ τ ∉ (s_m σ).*2
    | PopCommitted => ts_τ = [(τ, Call Pop #())] ∧ τ ∈ (s_m σ).*2
    | PopReturned => ∃ r, ts_τ = [(τ, Call Pop #()); (τ, Ret (encode_response r))]
    end.

End defs.

Record tss_inv (n : nat) (σ : tss) : Prop := {
  ti_wf : per_tag_wellformed_bag MayEmpty (λ _, True) (s_ts σ);
  ti_stack : I_stack_vis_pre (s_ts σ) (s_m σ) (pts_tags σ);
  ti_len : length (s_sent σ) = n ∧ length (s_top σ) = n ∧ length (s_busy σ) = n;
  (* operations *)
  ti_os_dom : dom (s_os σ) = events_of_trace (s_ts σ);
  ti_os τ s : s_os σ !! τ = Some s → os_ok σ τ s;
  (* points: a push's point records its node, in a pool < n *)
  ti_pts_node τ c e : (τ, c, e) ∈ s_pts σ → (is_Some e ↔ τ ∈ push_of_trace (s_ts σ));
  ti_pts_pool τ c x j : (τ, c, Some (x, j)) ∈ s_pts σ → j < n;
  (* nodes *)
  ti_nodes_nodup : NoDup (s_sent σ ++ omap (λ e : pt_entry, fst <$> e.2) (s_pts σ));
  ti_next_dom : dom (s_next σ) = list_to_set (s_sent σ ++ omap (λ e : pt_entry, fst <$> e.2) (s_pts σ));
  ti_pool j s t b : s_sent σ !! j = Some s → s_top σ !! j = Some t → s_busy σ !! j = Some b →
    pool_ok (s_sent σ) (s_pts σ) (s_m σ) (s_next σ) (s_TS σ) j s t b;
  ti_m_node b p : (b, p) ∈ s_m σ → is_Some (node_of σ b);
  (* the counter *)
  ti_K τ k : s_K σ !! τ = Some k → k ≤ s_c σ;
  ti_K_dom : dom (s_K σ) = events_of_trace (s_ts σ);
  ti_pt_K τ c e : (τ, c, e) ∈ s_pts σ → ∃ k, s_K σ !! τ = Some k ∧ k ≤ c ∧ c ≤ s_c σ;
  ti_pt_mono i j e1 e2 : i < j → s_pts σ !! i = Some e1 → s_pts σ !! j = Some e2 → e1.1.2 ≤ e2.1.2;
  ti_TS τ t : s_TS σ !! τ = Some t → ∃ k, PT σ τ = Some k ∧ k ≤ t.1 ∧ t.1 ≤ t.2 ∧ t.2 < s_c σ;
  ti_pre b o : pre_of_trace (s_ts σ) b o → b ∈ push_of_trace (s_ts σ) →
    ∃ t k, s_TS σ !! b = Some t ∧ s_K σ !! o = Some k ∧ t.2 < k;
  (* the counter starts at 1 *)
  ti_c_pos : 1 ≤ s_c σ;
  ti_pts_pos τ c e : (τ, c, e) ∈ s_pts σ → 1 ≤ c;
}.

(* ====================================================================== *)
(* Basic facts.                                                           *)
(* ====================================================================== *)

Lemma NoDup_omap_inj {A B} (f : A → option B) (l : list A) i j x y b :
  NoDup (omap f l) → l !! i = Some x → l !! j = Some y → f x = Some b → f y = Some b → i = j.
Proof.
  revert i j. induction l as [|a l IH]; intros i j Hnd Hi Hj Hx Hy; first done.
  destruct i as [|i], j as [|j]; simpl in *; simplify_eq; [done| | |].
  - rewrite Hx in Hnd. apply NoDup_cons in Hnd as [Hnin _]. exfalso. apply Hnin.
    apply list_elem_of_omap. exists y. split; [by eapply list_elem_of_lookup_2|done].
  - rewrite Hy in Hnd. apply NoDup_cons in Hnd as [Hnin _]. exfalso. apply Hnin.
    apply list_elem_of_omap. exists x. split; [by eapply list_elem_of_lookup_2|done].
  - f_equal. destruct (f a); [apply NoDup_cons in Hnd as [_ Hnd]|]; by eapply IH.
Qed.

Section facts.
  Implicit Types (σ : tss) (pts : list pt_entry).

  Lemma pts_tags_lookup σ i e : s_pts σ !! i = Some e → pts_tags σ !! i = Some e.1.1.
  Proof. intros Hi. by rewrite /pts_tags list_lookup_fmap Hi. Qed.

  Lemma pts_tags_lookup_inv σ i τ :
    pts_tags σ !! i = Some τ → ∃ e, s_pts σ !! i = Some e ∧ e.1.1 = τ.
  Proof.
    rewrite /pts_tags list_lookup_fmap. destruct (s_pts σ !! i) eqn:?; simpl; intros; simplify_eq.
    by eexists.
  Qed.

  Lemma elem_of_pts_tags σ τ : τ ∈ pts_tags σ ↔ ∃ c e, (τ, c, e) ∈ s_pts σ.
  Proof.
    rewrite /pts_tags list_elem_of_fmap. split.
    - intros ([[τ' c] e] & -> & Hin). by exists c, e.
    - intros (c & e & Hin). by exists (τ, c, e).
  Qed.

  Local Lemma find_tag_lookup σ i e :
    NoDup (pts_tags σ) → s_pts σ !! i = Some e →
    list_find (λ e' : pt_entry, e'.1.1 = e.1.1) (s_pts σ) = Some (i, e).
  Proof.
    intros Hnd Hi. apply list_find_Some. split_and!; [done|done|].
    intros j y Hj Hlt Heq.
    pose proof (NoDup_lookup (pts_tags σ) i j e.1.1 Hnd (pts_tags_lookup _ _ _ Hi)) as Hij.
    rewrite (pts_tags_lookup _ _ _ Hj) Heq in Hij. specialize (Hij eq_refl). lia.
  Qed.

  Lemma PT_lookup σ i e : NoDup (pts_tags σ) → s_pts σ !! i = Some e → PT σ e.1.1 = Some e.1.2.
  Proof. intros Hnd Hi. by rewrite /PT /PT_l (find_tag_lookup σ i e Hnd Hi). Qed.

  Lemma node_of_lookup σ i e : NoDup (pts_tags σ) → s_pts σ !! i = Some e → node_of σ e.1.1 = e.2.
  Proof. intros Hnd Hi. by rewrite /node_of /node_of_l (find_tag_lookup σ i e Hnd Hi). Qed.

  Lemma PT_Some σ τ k : PT σ τ = Some k → ∃ i e, s_pts σ !! i = Some e ∧ e.1.1 = τ ∧ e.1.2 = k.
  Proof.
    rewrite /PT /PT_l. destruct (list_find _ _) as [[i e]|] eqn:Hf; simpl; intros; simplify_eq.
    apply list_find_Some in Hf as (Hi & Hτ & _). by exists i, e.
  Qed.

  Lemma tag_of_lookup σ i τ c x j :
    NoDup (omap (λ e : pt_entry, fst <$> e.2) (s_pts σ)) →
    s_pts σ !! i = Some (τ, c, Some (x, j)) → tag_of σ x = Some τ.
  Proof.
    intros Hnd Hi. rewrite /tag_of /tag_of_l.
    destruct (list_find_elem_of (λ e : pt_entry, fst <$> e.2 = Some x) (s_pts σ) (τ, c, Some (x, j)))
      as [[i' e'] Hf]; [by eapply list_elem_of_lookup_2|done|].
    rewrite Hf /=. apply list_find_Some in Hf as (Hi' & He' & _).
    pose proof (NoDup_omap_inj _ _ i i' _ _ x Hnd Hi Hi' eq_refl He') as <-.
    rewrite Hi in Hi'. by simplify_eq.
  Qed.

  Lemma tag_of_Some σ x τ : tag_of σ x = Some τ → ∃ i c j, s_pts σ !! i = Some (τ, c, Some (x, j)).
  Proof.
    rewrite /tag_of /tag_of_l. destruct (list_find _ _) as [[i [[τ' c] e]]|] eqn:Hf; simpl; intros; simplify_eq.
    apply list_find_Some in Hf as (Hi & He & _). simpl in He.
    destruct e as [[x' j]|]; simpl in He; simplify_eq. by exists i, c, j.
  Qed.

  Lemma elem_of_pnodes pts j x : x ∈ pnodes pts j ↔ ∃ τ c, (τ, c, Some (x, j)) ∈ pts.
  Proof.
    rewrite /pnodes list_elem_of_omap. split.
    - intros ([[τ c] [[x' j']|]] & Hin & Heq); simpl in Heq; [|done].
      case_decide; simplify_eq. by exists τ, c.
    - intros (τ & c & Hin). exists (τ, c, Some (x, j)). split; [done|]. simpl. by rewrite decide_True.
  Qed.

  Lemma pnodes_prefix pts1 pts2 j : pts1 `prefix_of` pts2 → pnodes pts1 j `prefix_of` pnodes pts2 j.
  Proof. intros [k ->]. rewrite /pnodes omap_app. by apply prefix_app_r. Qed.

  Lemma pnodes_app pts1 pts2 j : pnodes (pts1 ++ pts2) j = pnodes pts1 j ++ pnodes pts2 j.
  Proof. by rewrite /pnodes omap_app. Qed.

  (* the node at position i of pool j comes from an entry, and later positions from later
     entries *)
  Lemma pnodes_lookup pts j i x :
    pnodes pts j !! i = Some x → ∃ k τ c, pts !! k = Some (τ, c, Some (x, j)) ∧
      length (pnodes (take k pts) j) = i.
  Proof.
    revert i. induction pts as [|e pts IH]; intros i Hi; first done.
    rewrite /pnodes /= in Hi.
    destruct e as [[τ c] [[x' j']|]]; simpl in Hi.
    - case_decide as Hj; subst.
      + destruct i as [|i]; simpl in Hi.
        * simplify_eq. exists 0, τ, c. split; [done|]. done.
        * destruct (IH i Hi) as (k & τ' & c' & Hk & Hlen).
          exists (1 + k), τ', c'. split; [done|]. rewrite /pnodes /= decide_True //=. by f_equal.
      + destruct (IH i Hi) as (k & τ' & c' & Hk & Hlen).
        exists (1 + k), τ', c'. split; [done|]. rewrite /pnodes /= decide_False //.
    - destruct (IH i Hi) as (k & τ' & c' & Hk & Hlen).
      exists (1 + k), τ', c'. split; [done|]. done.
  Qed.
End facts.

(* ====================================================================== *)
(* The LIFO condition at a commit.                                        *)
(* ====================================================================== *)

(* What a pop knows about its scan of pool j: the pool as it was when the scan read the
   top (after the pop's point), and either that all its nodes are taken, or a candidate
   (by position) with its timestamp such that all nodes above the candidate are taken. *)
Definition scan_res : Type := option (nat * (nat * nat)).

Definition scan_ok (σ : tss) (p : positive) (j : nat) (r : scan_res) : Prop :=
  ∃ pS s, pS `prefix_of` s_pts σ ∧ p ∈ (λ e : pt_entry, e.1.1) <$> pS ∧ s_sent σ !! j = Some s ∧
    match r with
    | None => ∀ x, x ∈ s :: pnodes pS j → taken σ x
    | Some (k, t) => ∃ x τ, (s :: pnodes pS j) !! k = Some x ∧ tag_of σ x = Some τ ∧
        s_TS σ !! τ = Some t ∧ ∀ i z, k < i → (s :: pnodes pS j) !! i = Some z → taken σ z
    end.

Section lifo.
  Context (n : nat).
  Implicit Types σ : tss.

  Lemma pt_nodup σ : tss_inv n σ → NoDup (pts_tags σ).
  Proof. intros HI. apply (isv_nodup _ _ _ (ti_stack _ _ HI)). Qed.

  Lemma nodes_nodup σ : tss_inv n σ → NoDup (omap (λ e : pt_entry, fst <$> e.2) (s_pts σ)).
  Proof. intros HI. pose proof (ti_nodes_nodup _ _ HI) as Hnd. by apply NoDup_app in Hnd as (_ & _ & ?). Qed.

  Lemma PT_of_pts σ τ :
    tss_inv n σ → τ ∈ pts_tags σ → ∃ k p, s_K σ !! τ = Some k ∧ PT σ τ = Some p ∧ k ≤ p.
  Proof.
    intros HI (c & e & Hin)%elem_of_pts_tags.
    destruct (ti_pt_K _ _ HI τ c e Hin) as (k & Hk & Hkc & _).
    apply list_elem_of_lookup in Hin as [i Hi].
    exists k, c. split_and!; [done| |done].
    exact (PT_lookup σ i (τ, c, e) (pt_nodup σ HI) Hi).
  Qed.

  Lemma PT_mono σ x y :
    tss_inv n σ → pt_before (pts_tags σ) x y →
    ∃ px py, PT σ x = Some px ∧ PT σ y = Some py ∧ px ≤ py.
  Proof.
    intros HI (i & j & Hij & Hi & Hj).
    destruct (pts_tags_lookup_inv _ _ _ Hi) as (ex & Hex & <-).
    destruct (pts_tags_lookup_inv _ _ _ Hj) as (ey & Hey & <-).
    exists ex.1.2, ey.1.2. split_and!.
    - exact (PT_lookup _ _ _ (pt_nodup σ HI) Hex).
    - exact (PT_lookup _ _ _ (pt_nodup σ HI) Hey).
    - exact (ti_pt_mono _ _ HI i j ex ey Hij Hex Hey).
  Qed.

  (* Along a ts-path, the first push's timestamp ends before the last push's point. *)
  Lemma ts_tr_PT σ b c :
    tss_inv n σ → ts_tr (s_ts σ) (pts_tags σ) b c → b ∈ push_of_trace (s_ts σ) →
    c ∈ push_of_trace (s_ts σ) → c ∈ pts_tags σ →
    ∃ tb kc, s_TS σ !! b = Some tb ∧ PT σ c = Some kc ∧ tb.2 < kc.
  Proof.
    intros HI Hts Hb Hc Hcp.
    pose proof (ti_wf _ _ HI) as Hwf.
    assert (Hnpop : c ∉ pop_of_trace (s_ts σ)).
    { intros Hcpop. exact (push_xor_pop_of_trace _ _ _ c Hwf Hc Hcpop). }
    assert (Hvis_c : ∀ q, vis_tr (s_ts σ) (pts_tags σ) q c →
              q ∈ pop_of_trace (s_ts σ) ∧ pt_before (pts_tags σ) q c).
    { intros q [(_ & Hcpop & _)|(Hq & Hqp & _ & Hnb)]; first done.
      split; [done|]. destruct (pt_before_total (pts_tags σ) q c Hqp Hcp) as [|Hcq]; [|done|done].
      by intros ->. }
    destruct Hts as [Hbc|[(q & Hbq & Hqc)|(d & q & Hbd & Hdq & Hqc)]].
    - destruct (ti_pre _ _ HI b c Hbc Hb) as (tb & k & Htb & Hk & Hlt).
      destruct (PT_of_pts σ c HI Hcp) as (k' & pc & Hk' & Hpc & Hle). rewrite Hk in Hk'; simplify_eq.
      exists tb, pc. split_and!; [done|done|lia].
    - destruct (Hvis_c q Hqc) as [Hq Hqc'].
      destruct (ti_pre _ _ HI b q Hbq Hb) as (tb & k & Htb & Hk & Hlt).
      destruct (PT_of_pts σ q HI (proj1 (pt_before_elem _ _ _ Hqc'))) as (k' & pq & Hk' & Hpq & Hle).
      rewrite Hk in Hk'; simplify_eq.
      destruct (PT_mono σ q c HI Hqc') as (pq' & pc & Hpq' & Hpc & Hle'). rewrite Hpq in Hpq'; simplify_eq.
      exists tb, pc. split_and!; [done|done|lia].
    - destruct (Hvis_c q Hqc) as [Hq Hqc'].
      assert (Hdq' : pt_before (pts_tags σ) d q).
      { destruct Hdq as [(_ & _ & ?)|(_ & _ & Hqpush & _)]; [done|].
        exfalso. exact (push_xor_pop_of_trace _ _ _ q Hwf Hqpush Hq). }
      destruct (ti_pre _ _ HI b d Hbd Hb) as (tb & k & Htb & Hk & Hlt).
      destruct (PT_of_pts σ d HI (proj1 (pt_before_elem _ _ _ Hdq'))) as (k' & pd & Hk' & Hpd & Hle).
      rewrite Hk in Hk'; simplify_eq.
      destruct (PT_mono σ d q HI Hdq') as (pd' & pq & Hpd' & Hpq & Hle1). rewrite Hpd in Hpd'; simplify_eq.
      destruct (PT_mono σ q c HI Hqc') as (pq' & pc & Hpq' & Hpc & Hle2). rewrite Hpq in Hpq'; simplify_eq.
      exists tb, pc. split_and!; [done|done|lia].
  Qed.

  Lemma pool_list_tag σ j i x :
    tss_inv n σ → 1 ≤ i → pool_list σ j !! i = Some x → ∃ τ c, tag_of σ x = Some τ ∧
      (τ, c, Some (x, j)) ∈ s_pts σ.
  Proof.
    intros HI Hi Hx. rewrite /pool_list /pool_list_l in Hx.
    destruct (s_sent σ !! j) as [s|]; last done.
    destruct i as [|i]; first lia. simpl in Hx.
    destruct (pnodes_lookup _ _ _ _ Hx) as (k & τ & c & Hk & _).
    exists τ, c. split; [exact (tag_of_lookup σ k τ c x j (nodes_nodup σ HI) Hk)|].
    by eapply list_elem_of_lookup_2.
  Qed.

  (* Timestamps grow along a pool. *)
  Lemma pool_chain σ j i i' x y τx τy :
    tss_inv n σ → j < n → 1 ≤ i → i < i' →
    pool_list σ j !! i = Some x → pool_list σ j !! i' = Some y →
    tag_of σ x = Some τx → tag_of σ y = Some τy →
    ∃ tx ky, s_TS σ !! τx = Some tx ∧ PT σ τy = Some ky ∧ tx.2 < ky.
  Proof.
    intros HI Hj Hi. destruct (ti_len _ _ HI) as (Hls & Hlt & Hlb).
    destruct (lookup_lt_is_Some_2 (s_sent σ) j) as [s Hs]; first lia.
    destruct (lookup_lt_is_Some_2 (s_top σ) j) as [t Ht]; first lia.
    destruct (lookup_lt_is_Some_2 (s_busy σ) j) as [bj Hbj]; first lia.
    pose proof (ti_pool _ _ HI j s t bj Hs Ht Hbj) as Hpool.
    intros Hii'. revert y τy. induction Hii' as [|i' Hii' IH]; intros y τy Hx Hy Htx Hty.
    - by eapply (po_chain _ _ _ _ _ _ _ _ _ Hpool i x y).
    - destruct (lookup_lt_is_Some_2 (pool_list σ j) i') as [z Hz].
      { apply lookup_lt_Some in Hy. lia. }
      destruct (pool_list_tag σ j i' z HI ltac:(lia) Hz) as (τz & cz & Htz & _).
      destruct (IH z τz Hx Hz Htx Htz) as (tx & kz & Htx' & Hkz & Hlt1).
      destruct (po_chain _ _ _ _ _ _ _ _ _ Hpool i' z y τz τy ltac:(lia) Hz Hy Htz Hty) as (tz & ky & Htz' & Hky & Hlt2).
      destruct (ti_TS _ _ HI τz tz Htz') as (kz' & Hkz' & Hle1 & Hle2 & _).
      rewrite Hkz in Hkz'; simplify_eq.
      exists tx, ky. split_and!; [done|done|lia].
  Qed.

  (* The commit of the youngest candidate b of a complete scan satisfies the LIFO
     condition of stack/vis.v for every push c that is ts-after b and visible to p. *)
  Lemma commit_lifo σ p b tb (res : nat → scan_res) :
    tss_inv n σ →
    (∀ j, j < n → scan_ok σ p j (res j)) →
    s_TS σ !! b = Some tb →
    (∀ j k t, j < n → res j = Some (k, t) → ¬ tb.2 < t.1) →
    b ∈ push_of_trace (s_ts σ) →
    ∀ c, ts_tr (s_ts σ) (pts_tags σ) b c → c ∈ push_of_trace (s_ts σ) →
      pt_before (pts_tags σ) c p → c ∈ (s_m σ).*1.
  Proof.
    intros HI Hscan Htb Hyoung Hb c Hts Hc Hcp.
    destruct (pt_before_elem _ _ _ Hcp) as [Hcpts Hppts].
    destruct (ts_tr_PT σ b c HI Hts Hb Hc Hcpts) as (tb' & kc & Htb' & Hkc & Hlt).
    rewrite Htb in Htb'; simplify_eq.
    pose proof Hcpts as (cc & ec & Hcin)%elem_of_pts_tags.
    destruct (ti_pts_node _ _ HI c cc ec Hcin) as [_ Hsome].
    destruct (Hsome Hc) as [[xc jc] ->].
    pose proof (ti_pts_pool _ _ HI c cc xc jc Hcin) as Hjc.
    destruct (Hscan jc Hjc) as (pS & s & HpS & HppS & Hs & Hres).
    (* c's point is before p's, so c's entry is in the scanned prefix *)
    assert (HcS : (c, cc, Some (xc, jc)) ∈ pS).
    { destruct Hcp as (ic & ip & Hlt' & Hic & Hip).
      apply list_elem_of_fmap in HppS as (ep & Hep & HepS).
      apply list_elem_of_lookup in HepS as [jp Hjp].
      pose proof (prefix_lookup_Some _ _ _ _ Hjp HpS) as Hjp'.
      pose proof (NoDup_lookup _ ip jp p (pt_nodup σ HI) Hip) as Hipjp.
      rewrite (pts_tags_lookup _ _ _ Hjp') -Hep in Hipjp. specialize (Hipjp eq_refl) as ->.
      destruct (pts_tags_lookup_inv _ _ _ Hic) as (e & He & Hec).
      apply list_elem_of_lookup in Hcin as [ic' Hic'].
      pose proof (NoDup_lookup _ ic ic' c (pt_nodup σ HI) Hic) as Hicic.
      rewrite (pts_tags_lookup _ _ _ Hic') in Hicic. specialize (Hicic eq_refl) as ->.
      assert (Hlen : ic' < length pS) by (apply lookup_lt_Some in Hjp; lia).
      destruct (lookup_lt_is_Some_2 pS ic' Hlen) as [e' He'].
      rewrite (prefix_lookup_Some _ _ _ _ He' HpS) in Hic'. simplify_eq.
      by eapply list_elem_of_lookup_2. }
    assert (∃ ic, (s :: pnodes pS jc) !! ic = Some xc ∧ 1 ≤ ic) as (ic & Hic & Hic1).
    { assert (Hxc : xc ∈ pnodes pS jc) by (apply elem_of_pnodes; eauto).
      apply list_elem_of_lookup in Hxc as [i0 Hi0]. exists (1 + i0). split; [done|lia]. }
    assert (Hpref : ∀ i z, (s :: pnodes pS jc) !! i = Some z → pool_list σ jc !! i = Some z).
    { intros i z Hz. rewrite /pool_list /pool_list_l Hs. eapply prefix_lookup_Some; [exact Hz|].
      apply prefix_cons, pnodes_prefix, HpS. }
    assert (Htag_c : tag_of σ xc = Some c).
    { apply list_elem_of_lookup in Hcin as [i Hi]. exact (tag_of_lookup σ i c cc xc jc (nodes_nodup σ HI) Hi). }
    assert (Htaken : taken σ xc → c ∈ (s_m σ).*1).
    { rewrite /taken /takenb /takenb_l -/(tag_of σ xc) Htag_c. intros [Hsent|Hm]%orb_true_iff; [|by apply bool_decide_eq_true in Hm].
      exfalso. apply bool_decide_eq_true in Hsent.
      pose proof (ti_nodes_nodup _ _ HI) as Hnd. apply NoDup_app in Hnd as (_ & Hdisj & _).
      apply (Hdisj xc Hsent). apply list_elem_of_omap. by exists (c, cc, Some (xc, jc)). }
    destruct (res jc) as [[k t]|] eqn:Hr; simpl in Hres.
    - destruct Hres as (x & τ & Hx & Htagx & Ht & Habove).
      destruct (decide (k < ic)) as [Hlt'|Hge].
      + by apply Htaken, (Habove ic).
      + exfalso. apply (Hyoung jc k t Hjc Hr).
        destruct (decide (ic = k)) as [<-|Hne].
        * rewrite Hic in Hx. injection Hx as <-. rewrite Htag_c in Htagx. injection Htagx as <-.
          destruct (ti_TS _ _ HI c t Ht) as (k' & Hk' & Hle & _ & _). rewrite Hkc in Hk'; simplify_eq.
          lia.
        * destruct (pool_chain σ jc ic k xc x c τ HI Hjc Hic1 ltac:(lia) (Hpref _ _ Hic) (Hpref _ _ Hx)
                      Htag_c Htagx) as (tx & ky & Htx & Hky & Hlt2).
          destruct (ti_TS _ _ HI c tx Htx) as (k1 & Hk1 & Hle1 & Hle2 & _).
          rewrite Hkc in Hk1; simplify_eq.
          destruct (ti_TS _ _ HI τ t Ht) as (k2 & Hk2 & Hle3 & _ & _). rewrite Hky in Hk2; simplify_eq.
          lia.
    - apply Htaken, Hres. by eapply list_elem_of_lookup_2.
  Qed.
End lifo.

(* ====================================================================== *)
(* Derived functions under extensions.                                    *)
(* ====================================================================== *)

Section derived.
  Implicit Types (pts : list pt_entry) (m : list (positive * positive)).

  Lemma tag_of_l_prefix pts pts' x τ :
    pts `prefix_of` pts' → tag_of_l pts x = Some τ → tag_of_l pts' x = Some τ.
  Proof.
    intros [k ->]. rewrite /tag_of_l.
    destruct (list_find _ pts) as [[i e]|] eqn:Hf; simpl; intros; simplify_eq.
    by rewrite (list_find_app_l _ _ _ _ _ Hf).
  Qed.

  Lemma tag_of_l_snoc pts e x :
    tag_of_l (pts ++ [e]) x =
      match tag_of_l pts x with
      | Some τ => Some τ
      | None => if decide (fst <$> e.2 = Some x) then Some e.1.1 else None
      end.
  Proof.
    rewrite /tag_of_l. destruct (list_find _ pts) as [[i e']|] eqn:Hf; simpl.
    - by rewrite (list_find_app_l _ _ _ _ _ Hf).
    - rewrite (list_find_app_r _ _ _ Hf) /=. by case_decide.
  Qed.

  Lemma PT_l_prefix pts pts' τ k : pts `prefix_of` pts' → PT_l pts τ = Some k → PT_l pts' τ = Some k.
  Proof.
    intros [l ->]. rewrite /PT_l.
    destruct (list_find _ pts) as [[i e]|] eqn:Hf; simpl; intros; simplify_eq.
    by rewrite (list_find_app_l _ _ _ _ _ Hf).
  Qed.

  Lemma PT_l_snoc pts e τ :
    PT_l (pts ++ [e]) τ =
      match PT_l pts τ with Some k => Some k | None => if decide (e.1.1 = τ) then Some e.1.2 else None end.
  Proof.
    rewrite /PT_l. destruct (list_find _ pts) as [[i e']|] eqn:Hf; simpl.
    - by rewrite (list_find_app_l _ _ _ _ _ Hf).
    - rewrite (list_find_app_r _ _ _ Hf) /=. by case_decide.
  Qed.

  Lemma node_of_l_prefix pts pts' τ v :
    pts `prefix_of` pts' → node_of_l pts τ = Some v → node_of_l pts' τ = Some v.
  Proof.
    intros [l ->]. rewrite /node_of_l.
    destruct (list_find _ pts) as [[i e]|] eqn:Hf; simpl; intros; simplify_eq.
    by rewrite (list_find_app_l _ _ _ _ _ Hf).
  Qed.

  Lemma node_of_l_snoc pts e τ :
    node_of_l (pts ++ [e]) τ =
      match list_find (λ e : pt_entry, e.1.1 = τ) pts with
      | Some (_, e') => e'.2
      | None => if decide (e.1.1 = τ) then e.2 else None
      end.
  Proof.
    rewrite /node_of_l. destruct (list_find _ pts) as [[i e']|] eqn:Hf; simpl.
    - by rewrite (list_find_app_l _ _ _ _ _ Hf).
    - rewrite (list_find_app_r _ _ _ Hf) /=. by case_decide.
  Qed.

  Lemma takenb_l_mono sent pts pts' m m' x :
    pts `prefix_of` pts' → m `prefix_of` m' →
    takenb_l sent pts m x = true → takenb_l sent pts' m' x = true.
  Proof.
    intros Hp Hm. rewrite /takenb_l. intros [Hs|Ht]%orb_true_iff; apply orb_true_iff; [by left|right].
    destruct (tag_of_l pts x) as [τ|] eqn:Htag; last done.
    rewrite (tag_of_l_prefix _ _ _ _ Hp Htag).
    apply bool_decide_eq_true in Ht. apply bool_decide_eq_true.
    destruct Hm as [l ->]. rewrite fmap_app elem_of_app. by left.
  Qed.

  Lemma tk_l_stable pts pts' m m' x τ :
    pts `prefix_of` pts' → m `prefix_of` m' →
    tag_of_l pts x = Some τ → τ ∈ m.*1 → tk_l pts' m' x = tk_l pts m x.
  Proof.
    intros Hp [l ->] Htag Hτ. rewrite /tk_l (tag_of_l_prefix _ _ _ _ Hp Htag) Htag.
    apply list_elem_of_fmap in Hτ as ([τ' p] & Heq & Hin). simpl in Heq. subst τ'.
    destruct (list_find_elem_of (λ e : positive * positive, e.1 = τ) m (τ, p) Hin eq_refl)
      as [[i e] Hf].
    by rewrite Hf (list_find_app_l _ _ _ _ _ Hf).
  Qed.

  Lemma tk_l_snoc_m pts m b p x :
    tag_of_l pts x = Some b → b ∉ m.*1 → tk_l pts (m ++ [(b, p)]) x = 1 + length m.
  Proof.
    intros Htag Hb. rewrite /tk_l Htag.
    assert (Hn : list_find (λ e : positive * positive, e.1 = b) m = None).
    { apply list_find_None, Forall_forall. intros [b' p'] Hin Heq. simpl in Heq. subst b'.
      apply Hb. by apply (list_elem_of_fmap_2 fst _ (b, p')). }
    rewrite (list_find_app_r _ _ _ Hn) /= decide_True //=.
  Qed.

  Lemma tk_l_le pts m x : tk_l pts m x ≤ length m.
  Proof.
    rewrite /tk_l. destruct (tag_of_l pts x); last lia.
    destruct (list_find _ m) as [[i e]|] eqn:Hf; last lia.
    apply list_find_Some in Hf as (Hi & _). apply lookup_lt_Some in Hi. lia.
  Qed.

  Lemma pnodes_snoc pts e j :
    pnodes (pts ++ [e]) j = pnodes pts j ++
      match e.2 with Some (x, j') => if decide (j' = j) then [x] else [] | None => [] end.
  Proof.
    rewrite /pnodes omap_app /=. destruct e as [[τ c] [[x j']|]]; simpl; [|done].
    by case_decide.
  Qed.

  Lemma pool_list_l_snoc sent pts e j s :
    sent !! j = Some s →
    pool_list_l sent (pts ++ [e]) j = pool_list_l sent pts j ++
      match e.2 with Some (x, j') => if decide (j' = j) then [x] else [] | None => [] end.
  Proof. intros Hs. by rewrite /pool_list_l Hs pnodes_snoc. Qed.

  Lemma tag_of_l_snoc_ne pts e x : fst <$> e.2 ≠ Some x → tag_of_l (pts ++ [e]) x = tag_of_l pts x.
  Proof. intros Hne. rewrite tag_of_l_snoc. destruct (tag_of_l pts x); [done|]. by rewrite decide_False. Qed.

  Lemma takenb_l_snoc_ne sent pts m e x :
    fst <$> e.2 ≠ Some x → takenb_l sent (pts ++ [e]) m x = takenb_l sent pts m x.
  Proof. intros Hne. by rewrite /takenb_l tag_of_l_snoc_ne. Qed.

  Lemma tk_l_snoc_ne pts m e x : fst <$> e.2 ≠ Some x → tk_l (pts ++ [e]) m x = tk_l pts m x.
  Proof. intros Hne. by rewrite /tk_l tag_of_l_snoc_ne. Qed.

  Lemma PT_l_snoc_old pts e τ k : PT_l pts τ = Some k → PT_l (pts ++ [e]) τ = Some k.
  Proof. intros Hk. by rewrite PT_l_snoc Hk. Qed.
End derived.

(* ====================================================================== *)
(* The atomic steps.                                                      *)
(* ====================================================================== *)

Definition ev_inc (σ : tss) : tss :=
  TSS (s_ts σ) (s_m σ) (s_pts σ) (s_sent σ) (s_top σ) (s_next σ) (s_TS σ) (s_K σ) (s_os σ)
    (1 + s_c σ) (s_busy σ).

Definition ev_call (σ : tss) (τ : positive) (t : trace) (s : op_state) : tss :=
  TSS (s_ts σ ++ [(τ, t)]) (s_m σ) (s_pts σ) (s_sent σ) (s_top σ) (s_next σ) (s_TS σ)
    (<[τ := s_c σ]> (s_K σ)) (<[τ := s]> (s_os σ)) (s_c σ) (s_busy σ).

(* ====================================================================== *)
(* The pool invariant under the atomic steps.                             *)
(* ====================================================================== *)

Section pool_steps.
  Implicit Types (pts : list pt_entry) (m : list (positive * positive)).

  Lemma pool_list_l_snoc_other sent pts e j :
    match e.2 with Some (_, j') => j' ≠ j | None => True end →
    pool_list_l sent (pts ++ [e]) j = pool_list_l sent pts j.
  Proof.
    intros He. rewrite /pool_list_l. destruct (sent !! j); [|done].
    rewrite pnodes_snoc. destruct e as [[τ c] [[x j']|]]; simpl in *; [|by rewrite right_id_L].
    by rewrite decide_False // right_id_L.
  Qed.

  (* Appending a point whose node (if any) is not in pool j, and changing next only
     outside pool j. *)
  Lemma pool_ok_snoc_other sent pts m next next' TS j s t b e :
    sent !! j = Some s →
    match e.2 with Some (_, j') => j' ≠ j | None => True end →
    (∀ z, z ∈ pool_list_l sent pts j → fst <$> e.2 ≠ Some z) →
    (∀ z, z ∈ pool_list_l sent pts j → next' !! z = next !! z) →
    pool_ok sent pts m next TS j s t b →
    pool_ok sent (pts ++ [e]) m next' TS j s t b.
  Proof.
    intros Hs He Hfresh Hnext Hpo.
    pose proof (pool_list_l_snoc_other sent pts e j He) as Hl.
    assert (Hin : ∀ i z, pool_list_l sent pts j !! i = Some z → z ∈ pool_list_l sent pts j)
      by (intros; by eapply list_elem_of_lookup_2).
    assert (Htk : ∀ i z, pool_list_l sent pts j !! i = Some z →
              takenb_l sent (pts ++ [e]) m z = takenb_l sent pts m z ∧ tk_l (pts ++ [e]) m z = tk_l pts m z ∧
              tag_of_l (pts ++ [e]) z = tag_of_l pts z).
    { intros i z Hz. pose proof (Hfresh z (Hin _ _ Hz)).
      split_and!; [by apply takenb_l_snoc_ne|by apply tk_l_snoc_ne|by apply tag_of_l_snoc_ne]. }
    destruct Hpo as [Hns Hnx Htop Hch How]. constructor; rewrite ?Hl.
    - rewrite Hnext; [done|]. rewrite /pool_list_l Hs. by left.
    - intros i x Hx Hi. destruct (Hnx i x Hx Hi) as (k & y & Hk & Hy & Hxy & Hbetw).
      exists k, y. split_and!; [done|done|by rewrite Hnext; [|eapply Hin]|].
      intros i' z Hi' Hz. rewrite (proj1 (Htk _ _ Hz)). by eapply Hbetw.
    - destruct Htop as (it & Hit & Habove). exists it. split; [done|].
      intros i z Hi Hz. destruct (Htk _ _ Hz) as (-> & -> & _). destruct (Htk _ _ Hit) as (-> & -> & _).
      by apply (Habove i).
    - intros i x y τx τy Hi Hx Hy Htx Hty.
      rewrite (proj2 (proj2 (Htk _ _ Hx))) in Htx. rewrite (proj2 (proj2 (Htk _ _ Hy))) in Hty.
      destruct (Hch i x y τx τy Hi Hx Hy Htx Hty) as (tx & ky & ? & Hky & ?).
      exists tx, ky. split_and!; [done|by apply PT_l_snoc_old|done].
    - intros x τ Hb Hlast Htx. eapply How; [done|done|].
      destruct (last _) eqn:Heqo; [|done]. simplify_eq.
      rewrite -(proj2 (proj2 (Htk (length (pool_list_l sent pts j) - 1) x _))); [done|].
      rewrite last_lookup in Heqo. by replace (pred (length _)) with (length (pool_list_l sent pts j) - 1) in Heqo by lia.
  Qed.

  Lemma pool_ok_next_agree sent pts m next next' TS j s t b :
    sent !! j = Some s →
    (∀ z, z ∈ pool_list_l sent pts j → next' !! z = next !! z) →
    pool_ok sent pts m next TS j s t b → pool_ok sent pts m next' TS j s t b.
  Proof.
    intros Hs Hnext [Hns Hnx Htop Hch How].
    constructor; try done.
    - rewrite Hnext; [done|]. rewrite /pool_list_l Hs. by left.
    - intros i x Hx Hi. destruct (Hnx i x Hx Hi) as (k & y & ? & ? & Hxy & ?).
      exists k, y. split_and!; [done|done| |done]. rewrite Hnext; [done|]. by eapply list_elem_of_lookup_2.
  Qed.

  (* Inserting a node x on top of pool j: x's next is a node y below which ... *)
  Lemma pool_ok_publish sent pts m next TS j s t b τ c x y iy :
    sent !! j = Some s →
    x ∉ pool_list_l sent pts j → tag_of_l pts x = None → x ∉ sent →
    τ ∉ m.*1 → PT_l pts τ = None →
    pool_list_l sent pts j !! iy = Some y →
    (∀ i z, iy < i → pool_list_l sent pts j !! i = Some z → takenb_l sent pts m z = true) →
    (∀ z τz, last (pool_list_l sent pts j) = Some z → tag_of_l pts z = Some τz →
       ∃ tz, TS !! τz = Some tz ∧ tz.2 < c) →
    pool_ok sent pts m next TS j s t b →
    pool_ok sent (pts ++ [(τ, c, Some (x, j))]) m (<[x := y]> next) TS j s x true.
  Proof.
    intros Hs Hx Htagx Hxs Hτm HPTτ Hy Habove Hlast Hpo.
    set (L := pool_list_l sent pts j).
    assert (HL : pool_list_l sent (pts ++ [(τ, c, Some (x, j))]) j = L ++ [x]).
    { rewrite (pool_list_l_snoc _ _ _ _ s Hs) /= decide_True //. }
    assert (Hold : ∀ i z, L !! i = Some z →
              takenb_l sent (pts ++ [(τ, c, Some (x, j))]) m z = takenb_l sent pts m z ∧
              tk_l (pts ++ [(τ, c, Some (x, j))]) m z = tk_l pts m z ∧
              tag_of_l (pts ++ [(τ, c, Some (x, j))]) z = tag_of_l pts z ∧ z ≠ x).
    { intros i z Hz. assert (Hzx : z ≠ x) by (intros ->; apply Hx; by eapply list_elem_of_lookup_2).
      assert (Hne : fst <$> Some (x, j) ≠ Some z) by (simpl; congruence).
      split_and!; [by apply takenb_l_snoc_ne|by apply tk_l_snoc_ne|by apply tag_of_l_snoc_ne|done]. }
    assert (Hlk : ∀ i z, (L ++ [x]) !! i = Some z → (L !! i = Some z) ∨ (i = length L ∧ z = x)).
    { intros i z Hz. apply lookup_app_Some in Hz as [?|(Hle & Hz)]; [by left|right].
      apply list_lookup_singleton_Some in Hz as [? ->]. split; [lia|done]. }
    assert (HyL : iy < length L) by (by apply lookup_lt_Some in Hy).
    destruct Hpo as [Hns Hnx Htop Hch How]. constructor; rewrite ?HL.
    - rewrite lookup_insert_ne; [done|]. intros ->. apply Hx. rewrite /L /pool_list_l Hs. by left.
    - intros i x0 Hx0 Hi. apply Hlk in Hx0 as [Hx0|[-> ->]].
      + destruct (Hnx i x0 Hx0 Hi) as (k & y0 & Hk & Hy0 & Hxy & Hbetw).
        destruct (Hold _ _ Hx0) as (_ & _ & _ & Hx0x).
        pose proof (lookup_lt_Some _ _ _ Hx0) as HiL.
        exists k, y0. split_and!; [done|by apply lookup_app_l_Some|by rewrite lookup_insert_ne|].
        intros i' z Hi' Hz. apply Hlk in Hz as [Hz|[? _]]; [|lia].
        rewrite (proj1 (Hold _ _ Hz)). by eapply Hbetw.
      + exists iy, y. split_and!; [done|by apply lookup_app_l_Some|by rewrite lookup_insert_eq|].
        intros i' z Hi' Hz. apply Hlk in Hz as [Hz|[? _]]; [|lia].
        rewrite (proj1 (Hold _ _ Hz)). apply (Habove i'); [lia|done].
    - exists (length L). split.
      + by rewrite lookup_app_r // Nat.sub_diag.
      + intros i z Hi Hz. apply Hlk in Hz as [Hz|[? _]]; [|lia]. apply lookup_lt_Some in Hz. lia.
    - intros i x0 y0 τx τy Hi Hx0 Hy0 Htx Hty.
      apply Hlk in Hy0 as [Hy0|[Hlen ->]].
      + assert (Hx0' : L !! i = Some x0).
        { apply Hlk in Hx0 as [?|[? _]]; [done|]. apply lookup_lt_Some in Hy0. lia. }
        rewrite (proj1 (proj2 (proj2 (Hold _ _ Hx0')))) in Htx.
        rewrite (proj1 (proj2 (proj2 (Hold _ _ Hy0)))) in Hty.
        destruct (Hch i x0 y0 τx τy Hi Hx0' Hy0 Htx Hty) as (tx & ky & ? & ? & ?).
        exists tx, ky. split_and!; [done|by apply PT_l_snoc_old|done].
      + assert (Hx0' : L !! i = Some x0).
        { apply Hlk in Hx0 as [?|[? _]]; [done|lia]. }
        rewrite (proj1 (proj2 (proj2 (Hold _ _ Hx0')))) in Htx.
        rewrite tag_of_l_snoc Htagx /= decide_True // in Hty. simplify_eq.
        destruct (Hlast x0 τx) as (tx & Htx' & Hlt); [|done|].
        { rewrite last_lookup -Hlen /=. done. }
        exists tx, c. split_and!; [done| |done].
        by rewrite PT_l_snoc HPTτ /= decide_True.
    - intros ? ? Hf. done.
  Qed.

  Lemma pool_ok_next sent pts m next TS j s t b ix x iy y :
    sent !! j = Some s → NoDup (pool_list_l sent pts j) →
    pool_list_l sent pts j !! ix = Some x → 0 < ix →
    iy < ix → pool_list_l sent pts j !! iy = Some y →
    (∀ i' z, iy < i' < ix → pool_list_l sent pts j !! i' = Some z → takenb_l sent pts m z = true) →
    pool_ok sent pts m next TS j s t b →
    pool_ok sent pts m (<[x := y]> next) TS j s t b.
  Proof.
    intros Hs Hnd Hx Hix Hiy Hy Hbetw [Hns Hnx Htop Hch How].
    assert (Hsx : s ≠ x).
    { intros ->. assert (Hs0 : pool_list_l sent pts j !! 0 = Some x) by (by rewrite /pool_list_l Hs).
      pose proof (NoDup_lookup _ _ _ _ Hnd Hx Hs0). lia. }
    constructor; [by rewrite lookup_insert_ne| |done|done|done].
    intros i x0 Hx0 Hi. destruct (decide (x0 = x)) as [->|Hne].
    - pose proof (NoDup_lookup _ _ _ _ Hnd Hx0 Hx) as ->.
      exists iy, y. split_and!; [done|done|by rewrite lookup_insert_eq|done].
    - destruct (Hnx i x0 Hx0 Hi) as (k & y0 & ? & ? & Hxy & ?).
      exists k, y0. split_and!; [done|done|by rewrite lookup_insert_ne|done].
  Qed.

  Lemma pool_ok_commit sent pts m next TS j s t b' bt p :
    (∀ z, z ∈ sent → tag_of_l pts z = None) → bt ∉ m.*1 →
    pool_ok sent pts m next TS j s t b' →
    pool_ok sent pts (m ++ [(bt, p)]) next TS j s t b'.
  Proof.
    intros Hsent Hbt [Hns Hnx Htop Hch How].
    assert (Hpre : m `prefix_of` m ++ [(bt, p)]) by by apply prefix_app_r.
    assert (Hmono : ∀ z, takenb_l sent pts m z = true → takenb_l sent pts (m ++ [(bt, p)]) z = true)
      by (intros z; by apply takenb_l_mono).
    (* tk of an old taken node is unchanged *)
    assert (Htk : ∀ z, takenb_l sent pts m z = true → tk_l pts (m ++ [(bt, p)]) z = tk_l pts m z).
    { intros z Hz. destruct (tag_of_l pts z) as [τz|] eqn:Hτz.
      - rewrite /takenb_l Hτz in Hz. apply orb_true_iff in Hz as [Hz|Hz].
        + apply bool_decide_eq_true in Hz. by rewrite Hsent in Hτz.
        + apply bool_decide_eq_true in Hz. by eapply tk_l_stable.
      - by rewrite /tk_l Hτz. }
    constructor; [done| | |done|done].
    - intros i x Hx Hi. destruct (Hnx i x Hx Hi) as (k & y & ? & ? & ? & Hbetw).
      exists k, y. split_and!; [done..|]. intros i' z Hi' Hz. by apply Hmono, (Hbetw i').
    - destruct Htop as (it & Hit & Habove). exists it. split; [done|].
      intros i z Hi Hz. destruct (Habove i z Hi Hz) as [Hzt Hle]. split; [by apply Hmono|].
      intros Ht'. rewrite (Htk z Hzt).
      destruct (takenb_l sent pts m t) eqn:Ht.
      + rewrite (Htk t Ht). by apply Hle.
      + pose proof (tk_l_le pts m z). rewrite /takenb_l in Ht'.
        destruct (tag_of_l pts t) as [τt|] eqn:Hτt.
        * apply orb_true_iff in Ht' as [Ht'|Ht'].
          { rewrite /takenb_l Ht' in Ht. done. }
          apply bool_decide_eq_true in Ht'. rewrite fmap_app elem_of_app in Ht'.
          destruct Ht' as [Ht'|Ht'].
          { exfalso. rewrite /takenb_l Hτt in Ht. apply orb_false_iff in Ht as [_ Ht].
            by apply bool_decide_eq_false in Ht. }
          apply list_elem_of_singleton in Ht'. simpl in Ht'. subst τt.
          rewrite (tk_l_snoc_m _ _ _ _ _ Hτt Hbt). lia.
        * rewrite orb_false_r in Ht'. rewrite /takenb_l Ht' in Ht. done.
  Qed.

  Lemma pool_ok_top sent pts m next TS j s t t' b it' :
    pool_list_l sent pts j !! it' = Some t' →
    (∀ i z, it' < i → pool_list_l sent pts j !! i = Some z →
       takenb_l sent pts m z = true ∧ (takenb_l sent pts m t' = true → tk_l pts m z ≤ tk_l pts m t')) →
    pool_ok sent pts m next TS j s t b → pool_ok sent pts m next TS j s t' b.
  Proof. intros Hit Habove [Hns Hnx Htop Hch How]. constructor; try done. by exists it'. Qed.

  Lemma pool_ok_stamp sent pts m next TS j s t b τ ts :
    TS !! τ = None →
    (∀ i x y, pool_list_l sent pts j !! i = Some x → pool_list_l sent pts j !! (1 + i) = Some y →
       tag_of_l pts x ≠ Some τ) →
    pool_ok sent pts m next TS j s t b → pool_ok sent pts m next (<[τ := ts]> TS) j s t b.
  Proof.
    intros Hτ Hnolast [Hns Hnx Htop Hch How]. constructor; try done.
    - intros i x y τx τy Hi Hx Hy Htx Hty.
      destruct (Hch i x y τx τy Hi Hx Hy Htx Hty) as (tx & ky & ? & ? & ?).
      exists tx, ky. rewrite lookup_insert_ne; [done|]. intros ->. by apply (Hnolast i x y).
    - intros x τ' Hb Hlast Htx. destruct (decide (τ' = τ)) as [->|Hne].
      + rewrite lookup_insert_eq. by eexists.
      + rewrite lookup_insert_ne //. by eapply How.
  Qed.

  Lemma pool_ok_busy sent pts m next TS j s t b b' :
    (b' = false → ∀ x τ, last (pool_list_l sent pts j) = Some x → tag_of_l pts x = Some τ →
       is_Some (TS !! τ)) →
    pool_ok sent pts m next TS j s t b → pool_ok sent pts m next TS j s t b'.
  Proof. intros Hb' [Hns Hnx Htop Hch How]. constructor; try done. intros x τ Hb. by apply Hb'. Qed.
End pool_steps.

Section trace_facts.
  Implicit Types (ts : list (positive * trace)).

  Lemma events_of_trace_snoc ts τ t :
    events_of_trace (ts ++ [(τ, t)]) = {[τ]} ∪ events_of_trace ts.
  Proof. rewrite /events_of_trace fmap_app list_to_set_app_L /=. set_solver. Qed.

  Lemma filter_snoc_ne ts τ τ' t :
    τ' ≠ τ → filter (λ x : positive * trace, x.1 = τ') (ts ++ [(τ, t)]) =
             filter (λ x : positive * trace, x.1 = τ') ts.
  Proof. intros Hne. rewrite filter_app filter_cons_False /=; last done. by rewrite filter_nil right_id_L. Qed.

  Lemma filter_snoc_eq ts τ t :
    filter (λ x : positive * trace, x.1 = τ) (ts ++ [(τ, t)]) =
    filter (λ x : positive * trace, x.1 = τ) ts ++ [(τ, t)].
  Proof. rewrite filter_app filter_cons_True /=; last done. by rewrite filter_nil. Qed.

  Lemma filter_fresh ts τ : τ ∉ ts.*1 → filter (λ x : positive * trace, x.1 = τ) ts = [].
  Proof.
    induction ts as [|[τ' t] ts IH]; intros Hfresh; first done.
    rewrite filter_cons_False /=.
    - apply IH. set_solver.
    - intros ->. set_solver.
  Qed.
End trace_facts.

Definition ev_point (σ : tss) (p : positive) : tss :=
  TSS (s_ts σ) (s_m σ) (s_pts σ ++ [(p, s_c σ, None)]) (s_sent σ) (s_top σ) (s_next σ) (s_TS σ)
    (s_K σ) (<[p := PopStarted]> (s_os σ)) (s_c σ) (s_busy σ).

Definition ev_publish (σ : tss) (τ : positive) (x : loc) (j : nat) (y : loc) : tss :=
  TSS (s_ts σ) (s_m σ) (s_pts σ ++ [(τ, s_c σ, Some (x, j))]) (s_sent σ) (<[j := x]> (s_top σ))
    (<[x := y]> (s_next σ)) (s_TS σ) (s_K σ) (<[τ := PushInserted]> (s_os σ)) (s_c σ) (s_busy σ).

Definition ev_next (σ : tss) (x y : loc) : tss :=
  TSS (s_ts σ) (s_m σ) (s_pts σ) (s_sent σ) (s_top σ) (<[x := y]> (s_next σ)) (s_TS σ) (s_K σ)
    (s_os σ) (s_c σ) (s_busy σ).

Definition ev_stamp (σ : tss) (τ : positive) (t : nat * nat) : tss :=
  TSS (s_ts σ) (s_m σ) (s_pts σ) (s_sent σ) (s_top σ) (s_next σ) (<[τ := t]> (s_TS σ)) (s_K σ)
    (<[τ := PushStamped]> (s_os σ)) (s_c σ) (s_busy σ).

Definition ev_busy (σ : tss) (j : nat) (b : bool) : tss :=
  TSS (s_ts σ) (s_m σ) (s_pts σ) (s_sent σ) (s_top σ) (s_next σ) (s_TS σ) (s_K σ) (s_os σ)
    (s_c σ) (<[j := b]> (s_busy σ)).

Definition ev_ret (σ : tss) (τ : positive) (r : val) (s : op_state) : tss :=
  TSS (s_ts σ ++ [(τ, Ret r)]) (s_m σ) (s_pts σ) (s_sent σ) (s_top σ) (s_next σ) (s_TS σ)
    (s_K σ) (<[τ := s]> (s_os σ)) (s_c σ) (s_busy σ).

Definition ev_commit (σ : tss) (b p : positive) : tss :=
  TSS (s_ts σ) (s_m σ ++ [(b, p)]) (s_pts σ) (s_sent σ) (s_top σ) (s_next σ) (s_TS σ) (s_K σ)
    (<[p := PopCommitted]> (s_os σ)) (s_c σ) (s_busy σ).

Definition ev_top (σ : tss) (j : nat) (t : loc) : tss :=
  TSS (s_ts σ) (s_m σ) (s_pts σ) (s_sent σ) (<[j := t]> (s_top σ)) (s_next σ) (s_TS σ) (s_K σ)
    (s_os σ) (s_c σ) (s_busy σ).

Lemma NoDup_omap_sub {A B} (f g : A → option B) (l : list A) :
  (∀ a b, g a = Some b → f a = Some b) → NoDup (omap f l) → NoDup (omap g l).
Proof.
  intros Hgf. induction l as [|a l IH]; simpl; [done|].
  destruct (g a) as [b|] eqn:Hg.
  - rewrite (Hgf a b Hg). intros [Hnin Hnd]%NoDup_cons. apply NoDup_cons. split; [|by apply IH].
    intros Hin. apply Hnin. apply list_elem_of_omap in Hin as (a' & Ha' & Hga').
    apply list_elem_of_omap. exists a'. split; [done|by apply Hgf].
  - destruct (f a); [intros [_ Hnd]%NoDup_cons|]; by apply IH.
Qed.

Section steps.
  Context (n : nat).
  Implicit Types σ : tss.

  Lemma pts_called σ τ : tss_inv n σ → τ ∈ pts_tags σ → τ ∈ (s_ts σ).*1.
  Proof. intros HI. apply (isv_called _ _ _ (ti_stack _ _ HI)). Qed.

  Lemma TS_pts σ τ t : tss_inv n σ → s_TS σ !! τ = Some t → τ ∈ pts_tags σ.
  Proof.
    intros HI Ht. destruct (ti_TS _ _ HI τ t Ht) as (k & Hk & _).
    destruct (PT_Some σ τ k Hk) as (i & e & Hi & <- & _).
    rewrite /pts_tags list_elem_of_fmap. exists e. split; [done|]. by eapply list_elem_of_lookup_2.
  Qed.

  Lemma m2_called σ p : tss_inv n σ → p ∈ (s_m σ).*2 → p ∈ (s_ts σ).*1.
  Proof.
    intros HI ([b p'] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst p'.
    apply (list_elem_of_fmap_2 fst _ (p, Call Pop #())).
    exact (valid_match_call_pop _ _ _ _ (isv_valid _ _ _ (ti_stack _ _ HI)) Hin).
  Qed.

  (* a push that has returned is timestamped *)
  Lemma push_ret_TS σ b r :
    tss_inv n σ → b ∈ push_of_trace (s_ts σ) → (b, Ret r) ∈ s_ts σ → ∃ t, s_TS σ !! b = Some t.
  Proof.
    intros HI Hb Hr.
    destruct (push_tag_in_trace _ _ Hb) as [w Hw].
    assert (Hev : b ∈ dom (s_os σ)).
    { rewrite (ti_os_dom _ _ HI) /events_of_trace elem_of_list_to_set.
      by apply (list_elem_of_fmap_2 fst _ (b, Call Push w)). }
    apply elem_of_dom in Hev as [s Hs].
    assert (Hw' : (b, Call Push w) ∈ filter (λ x : positive * trace, x.1 = b) (s_ts σ))
      by (by apply list_elem_of_filter).
    assert (Hr' : (b, Ret r) ∈ filter (λ x : positive * trace, x.1 = b) (s_ts σ))
      by (by apply list_elem_of_filter).
    pose proof (ti_os _ _ HI b s Hs) as Hok.
    destruct s; rewrite /os_ok in Hok; simpl in Hok;
      repeat match goal with
      | H : _ ∧ _ |- _ => destruct H
      | H : ∃ _, _ |- _ => destruct H
      | H : filter _ _ = _ |- _ => rewrite H in Hw', Hr'
      end; set_solver.
  Qed.

  Lemma tss_inv_inc σ : tss_inv n σ → tss_inv n (ev_inc σ).
  Proof.
    intros HI. constructor; try by destruct HI.
    - intros τ k Hk.
      pose proof (ti_K _ _ HI τ k Hk). simpl. lia.
    - intros τ c e Hin.
      destruct (ti_pt_K _ _ HI τ c e Hin) as (k & ? & ? & ?).
      exists k. split_and!; [done|done|simpl; lia].
    - intros τ t Ht.
      destruct (ti_TS _ _ HI τ t Ht) as (k & ? & ? & ? & ?).
      exists k. split_and!; [done..|simpl; lia].
    - simpl. lia.
  Qed.

  Lemma os_ok_ext σ σ' τ s :
    filter (λ x : positive * trace, x.1 = τ) (s_ts σ') = filter (λ x : positive * trace, x.1 = τ) (s_ts σ) →
    (τ ∈ pts_tags σ' ↔ τ ∈ pts_tags σ) → s_TS σ' !! τ = s_TS σ !! τ →
    (τ ∈ (s_m σ').*2 ↔ τ ∈ (s_m σ).*2) →
    os_ok σ τ s → os_ok σ' τ s.
  Proof. intros Hf Hp HT Hm. destruct s; rewrite /os_ok /= Hf; rewrite ?HT; naive_solver. Qed.

  (* A call (with a fresh tag) needs no condition beyond the bag ones. *)
  Lemma tss_inv_call σ τ t s :
    tss_inv n σ → τ ∉ (s_ts σ).*1 → is_call t →
    per_tag_wellformed_bag MayEmpty (λ _, True) (s_ts σ ++ [(τ, t)]) →
    I_stack_vis_pre (s_ts σ ++ [(τ, t)]) (s_m σ) (pts_tags σ) →
    os_ok (ev_call σ τ t s) τ s →
    tss_inv n (ev_call σ τ t s).
  Proof.
    intros HI Hfresh Hcall Hwf' Hstack' Hok.
    assert (Hτpts : τ ∉ pts_tags σ) by (intros Hin; by apply Hfresh, pts_called).
    assert (Hpush : ∀ x, x ≠ τ → x ∈ push_of_trace (s_ts σ ++ [(τ, t)]) ↔ x ∈ push_of_trace (s_ts σ)).
    { intros x Hx. rewrite /push_of_trace filter_app fmap_app elem_of_app. split; [|by left].
      intros [?|Hin]; [done|]. apply list_elem_of_fmap in Hin as ([y e] & -> & Hin).
      apply list_elem_of_filter in Hin as [_ Hin]. apply list_elem_of_singleton in Hin. by simplify_eq. }
    constructor; simpl.
    - done.
    - done.
    - apply HI.
    - rewrite dom_insert_L events_of_trace_snoc (ti_os_dom _ _ HI). done.
    - intros τ' s' Hs'. destruct (decide (τ' = τ)) as [->|Hne].
      + rewrite lookup_insert_eq in Hs'. injection Hs' as <-. exact Hok.
      + rewrite lookup_insert_ne // in Hs'. apply (os_ok_ext σ); [|done|done|done|].
        * simpl. by apply filter_snoc_ne.
        * by apply (ti_os _ _ HI).
    - intros τ' c e Hin. rewrite (Hpush τ'); first by apply (ti_pts_node _ _ HI τ' c e).
      intros ->. apply Hτpts, elem_of_pts_tags. eauto.
    - apply HI.
    - apply HI.
    - apply HI.
    - apply HI.
    - apply HI.
    - intros τ' k Hk. destruct (decide (τ' = τ)) as [->|Hne].
      + rewrite lookup_insert_eq in Hk. simplify_eq. done.
      + rewrite lookup_insert_ne // in Hk. by apply (ti_K _ _ HI τ').
    - rewrite dom_insert_L events_of_trace_snoc (ti_K_dom _ _ HI). done.
    - intros τ' c e Hin. destruct (ti_pt_K _ _ HI τ' c e Hin) as (k & Hk & Hle).
      exists k. rewrite lookup_insert_ne; [done|]. intros ->. apply Hτpts, elem_of_pts_tags. eauto.
    - apply HI.
    - apply HI.
    - intros b o Hbo Hb.
      assert (Hbτ : b ≠ τ).
      { intros ->. destruct (pre_of_trace_ret _ _ _ Hbo) as [r Hr].
        apply elem_of_app in Hr as [Hr|Hr]; [by apply Hfresh, (list_elem_of_fmap_2 fst _ (τ, Ret r))|].
        apply list_elem_of_singleton in Hr. simplify_eq. done. }
      apply (Hpush b Hbτ) in Hb.
      destruct (decide (o = τ)) as [->|Hoτ].
      + destruct (pre_of_trace_ret _ _ _ Hbo) as [r Hr].
        apply elem_of_app in Hr as [Hr|Hr]; last (apply list_elem_of_singleton in Hr; simplify_eq; done).
        destruct (push_ret_TS σ b r HI Hb Hr) as [tb Htb].
        destruct (ti_TS _ _ HI b tb Htb) as (_ & _ & _ & _ & Hlt).
        exists tb, (s_c σ). rewrite lookup_insert_eq. split_and!; [done|done|lia].
      + destruct t as [nc vc| |]; try done.
        apply (pre_snoc_call_old (s_ts σ) τ nc vc) in Hbo; last done.
        destruct (ti_pre _ _ HI b o Hbo Hb) as (tb & k & Htb & Hk & Hlt).
        exists tb, k. rewrite lookup_insert_ne //.
    - apply HI.
    - apply HI.
  Qed.

  Lemma tss_inv_call_push σ τ v :
    tss_inv n σ → τ ∉ (s_ts σ).*1 → tss_inv n (ev_call σ τ (Call Push v) PushCalled).
  Proof.
    intros HI Hfresh. apply tss_inv_call; [done|done|done| | |].
    - by apply per_tag_wellformed_bag_snoc_call_push; [apply HI| |].
    - by apply I_stack_vis_pre_snoc_call_push; [apply HI|].
    - rewrite /os_ok /= filter_snoc_eq filter_fresh //=. split_and!; [by eexists| |].
      + intros Hin. by apply Hfresh, pts_called.
      + destruct (s_TS σ !! τ) as [t|] eqn:Ht; [|done].
        exfalso. by apply Hfresh, pts_called, (TS_pts σ τ t).
  Qed.

  Lemma elem_of_snoc_pts (pts : list pt_entry) e e' : e' ∈ pts ++ [e] ↔ e' ∈ pts ∨ e' = e.
  Proof. by rewrite elem_of_app list_elem_of_singleton. Qed.

  Lemma sent_no_tag σ z : tss_inv n σ → z ∈ s_sent σ → tag_of_l (s_pts σ) z = None.
  Proof.
    intros HI Hz. destruct (tag_of_l (s_pts σ) z) as [τ|] eqn:Ht; [|done].
    destruct (tag_of_Some σ z τ Ht) as (i & c & j & Hi).
    pose proof (ti_nodes_nodup _ _ HI) as Hnd. apply NoDup_app in Hnd as (_ & Hdisj & _).
    exfalso. apply (Hdisj z Hz). apply list_elem_of_omap. exists (τ, c, Some (z, j)).
    split; [by eapply list_elem_of_lookup_2|done].
  Qed.

  Lemma not_pts_node σ x : tss_inv n σ → x ∉ dom (s_next σ) → tag_of_l (s_pts σ) x = None.
  Proof.
    intros HI Hx. destruct (tag_of_l (s_pts σ) x) as [τ|] eqn:Ht; [|done].
    destruct (tag_of_Some σ x τ Ht) as (i & c & j & Hi). exfalso. apply Hx.
    rewrite (ti_next_dom _ _ HI) elem_of_list_to_set elem_of_app. right.
    apply list_elem_of_omap. exists (τ, c, Some (x, j)). split; [by eapply list_elem_of_lookup_2|done].
  Qed.

  Lemma pool_list_in_dom σ j z : tss_inv n σ → z ∈ pool_list σ j → z ∈ dom (s_next σ).
  Proof.
    intros HI Hz. rewrite (ti_next_dom _ _ HI) elem_of_list_to_set elem_of_app.
    rewrite /pool_list /pool_list_l in Hz. destruct (s_sent σ !! j) as [s|] eqn:Hs; [|by apply elem_of_nil in Hz].
    apply elem_of_cons in Hz as [->|Hz]; [left; by eapply list_elem_of_lookup_2|right].
    apply elem_of_pnodes in Hz as (τ & c & Hin). apply list_elem_of_omap. by exists (τ, c, Some (z, j)).
  Qed.

  Lemma m1_pts σ b : tss_inv n σ → b ∈ (s_m σ).*1 → b ∈ pts_tags σ.
  Proof.
    intros HI ([b' p] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst b'.
    destruct (ti_m_node _ _ HI b p Hin) as [v Hv]. rewrite /node_of /node_of_l in Hv.
    destruct (list_find _ _) as [[i e]|] eqn:Hf; [|done].
    apply list_find_Some in Hf as (Hi & He & _). rewrite /pts_tags list_elem_of_fmap.
    exists e. split; [done|by eapply list_elem_of_lookup_2].
  Qed.

  Lemma tss_inv_point σ p :
    tss_inv n σ → s_os σ !! p = Some PopCalled → tss_inv n (ev_point σ p).
  Proof.
    intros HI Hos. pose proof (ti_os _ _ HI p _ Hos) as (Hfp & Hpts & Hm2).
    assert (Hcall : (p, Call Pop #()) ∈ s_ts σ).
    { assert (Hin : (p, Call Pop #()) ∈ filter (λ x : positive * trace, x.1 = p) (s_ts σ))
        by (rewrite Hfp; by left).
      by apply list_elem_of_filter in Hin as [_ ?]. }
    assert (Hnret : p ∉ (filter (is_ret ∘ snd) (s_ts σ)).*1).
    { intros ([τ' t] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst τ'.
      apply list_elem_of_filter in Hin as [Hret Hin].
      assert (Hin' : (p, t) ∈ filter (λ x : positive * trace, x.1 = p) (s_ts σ)) by (by apply list_elem_of_filter).
      rewrite Hfp in Hin'. apply list_elem_of_singleton in Hin'. simplify_eq. done. }
    assert (Hpop : p ∈ pop_of_trace (s_ts σ)).
    { apply (list_elem_of_fmap_2 fst _ (p, Call Pop #())). by apply list_elem_of_filter_2. }
    assert (Htags : pts_tags (ev_point σ p) = pts_tags σ ++ [p]) by (by rewrite /pts_tags /= fmap_app).
    constructor; simpl.
    - apply HI.
    - rewrite Htags. apply I_stack_vis_pre_snoc_point; [apply HI| |done|done].
      by apply (list_elem_of_fmap_2 fst _ (p, Call Pop #())).
    - apply HI.
    - rewrite dom_insert_L (ti_os_dom _ _ HI).
      apply subseteq_union_1_L, singleton_subseteq_l. rewrite /events_of_trace elem_of_list_to_set.
      by apply (list_elem_of_fmap_2 fst _ (p, Call Pop #())).
    - intros τ s Hs. destruct (decide (τ = p)) as [->|Hne].
      + rewrite lookup_insert_eq in Hs. simplify_eq. rewrite /os_ok /= Htags.
        split_and!; [done| |done]. apply elem_of_app. right. by left.
      + rewrite lookup_insert_ne // in Hs. apply (os_ok_ext σ); [done| |done|done|by apply (ti_os _ _ HI)].
        rewrite Htags elem_of_app list_elem_of_singleton. naive_solver.
    - intros τ c e [Hin|Heq]%elem_of_snoc_pts; [by apply (ti_pts_node _ _ HI τ c e)|].
      simplify_eq. split; [by intros []|]. intros Hpush. exfalso.
      exact (push_xor_pop_of_trace _ _ _ p (ti_wf _ _ HI) Hpush Hpop).
    - intros τ c x j [Hin|Heq]%elem_of_snoc_pts; [by apply (ti_pts_pool _ _ HI τ c x j)|done].
    - rewrite omap_app /= right_id_L. apply HI.
    - rewrite omap_app /= right_id_L. apply HI.
    - intros j s t b Hs Ht Hb. apply (pool_ok_snoc_other _ _ _ (s_next σ)); [done|done|done|done|].
      by apply (ti_pool _ _ HI).
    - intros b q Hin. destruct (ti_m_node _ _ HI b q Hin) as [v Hv]. exists v.
      by eapply node_of_l_prefix; [apply prefix_app_r|].
    - apply HI.
    - apply HI.
    - intros τ c e [Hin|Heq]%elem_of_snoc_pts; [by apply (ti_pt_K _ _ HI τ c e)|].
      simplify_eq. assert (Hpd : p ∈ dom (s_K σ)).
      { rewrite (ti_K_dom _ _ HI) /events_of_trace elem_of_list_to_set.
        by apply (list_elem_of_fmap_2 fst _ (p, Call Pop #())). }
      apply elem_of_dom in Hpd as [k Hk]. exists k. split_and!; [done|by apply (ti_K _ _ HI p)|done].
    - intros i j e1 e2 Hij Hi Hj.
      apply lookup_app_Some in Hj as [Hj|(Hlen & Hj)]; [apply lookup_app_Some in Hi as [Hi|(? & _)]|].
      + by apply (ti_pt_mono _ _ HI i j).
      + apply lookup_lt_Some in Hj. lia.
      + apply list_lookup_singleton_Some in Hj as [Hj0 <-].
        apply lookup_app_Some in Hi as [Hi|(? & _)]; [|lia]. simpl.
        destruct e1 as [[τ1 c1] o1]. destruct (ti_pt_K _ _ HI τ1 c1 o1) as (_ & _ & _ & ?); [|done].
        by eapply list_elem_of_lookup_2.
    - intros τ t Ht. destruct (ti_TS _ _ HI τ t Ht) as (k & Hk & ?). exists k.
      split; [by apply PT_l_snoc_old|done].
    - apply HI.
    - apply HI.
    - intros τ' c e [Hin|Heq]%elem_of_snoc_pts; [by apply (ti_pts_pos _ _ HI τ' c e)|].
      injection Heq as _ -> _. apply HI.
  Qed.

  Lemma tss_inv_publish σ τ x j y iy :
    tss_inv n σ → s_os σ !! τ = Some PushCalled → j < n → s_busy σ !! j = Some true →
    x ∉ dom (s_next σ) →
    pool_list σ j !! iy = Some y →
    (∀ i z, iy < i → pool_list σ j !! i = Some z → taken σ z) →
    (∀ z τz, last (pool_list σ j) = Some z → tag_of σ z = Some τz → is_Some (s_TS σ !! τz)) →
    tss_inv n (ev_publish σ τ x j y).
  Proof.
    intros HI Hos Hj Hbusy Hx Hy Habove Hlast.
    pose proof (ti_os _ _ HI τ _ Hos) as ((v & Hfτ) & Hτpts & HTS).
    assert (Hcall : (τ, Call Push v) ∈ s_ts σ).
    { assert (Hin : (τ, Call Push v) ∈ filter (λ x : positive * trace, x.1 = τ) (s_ts σ))
        by (rewrite Hfτ; by left).
      by apply list_elem_of_filter in Hin as [_ ?]. }
    assert (Hnret : τ ∉ (filter (is_ret ∘ snd) (s_ts σ)).*1).
    { intros ([τ' t] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst τ'.
      apply list_elem_of_filter in Hin as [Hret Hin].
      assert (Hin' : (τ, t) ∈ filter (λ x : positive * trace, x.1 = τ) (s_ts σ)) by (by apply list_elem_of_filter).
      rewrite Hfτ in Hin'. apply list_elem_of_singleton in Hin'. simplify_eq. done. }
    assert (Hpush : τ ∈ push_of_trace (s_ts σ)).
    { apply (list_elem_of_fmap_2 fst _ (τ, Call Push v)). apply list_elem_of_filter_2; [by exists v|done]. }
    assert (Htags : pts_tags (ev_publish σ τ x j y) = pts_tags σ ++ [τ]) by (by rewrite /pts_tags /= fmap_app).
    assert (Hτm : τ ∉ (s_m σ).*1) by (intros Hin; by apply Hτpts, m1_pts).
    assert (HPT : PT_l (s_pts σ) τ = None).
    { destruct (PT_l (s_pts σ) τ) as [k|] eqn:Hk; [|done]. exfalso.
      destruct (PT_Some σ τ k Hk) as (i & e & Hi & <- & _). apply Hτpts.
      rewrite /pts_tags list_elem_of_fmap. exists e. split; [done|by eapply list_elem_of_lookup_2]. }
    destruct (ti_len _ _ HI) as (Hls & Hlt & Hlb).
    constructor; simpl.
    - apply HI.
    - rewrite Htags. apply I_stack_vis_pre_snoc_point; [apply HI| |done|done].
      by apply (list_elem_of_fmap_2 fst _ (τ, Call Push v)).
    - by rewrite length_insert.
    - rewrite dom_insert_L (ti_os_dom _ _ HI).
      apply subseteq_union_1_L, singleton_subseteq_l. rewrite /events_of_trace elem_of_list_to_set.
      by apply (list_elem_of_fmap_2 fst _ (τ, Call Push v)).
    - intros τ' s Hs. destruct (decide (τ' = τ)) as [->|Hne].
      + rewrite lookup_insert_eq in Hs. simplify_eq. rewrite /os_ok /= Htags.
        split_and!; [by eexists| |done]. apply elem_of_app. right. by left.
      + rewrite lookup_insert_ne // in Hs. apply (os_ok_ext σ); [done| |done|done|by apply (ti_os _ _ HI)].
        rewrite Htags elem_of_app list_elem_of_singleton. naive_solver.
    - intros τ' c e [Hin|Heq]%elem_of_snoc_pts; [by apply (ti_pts_node _ _ HI τ' c e)|].
      simplify_eq. split; [done|by eexists].
    - intros τ' c x' j' [Hin|Heq]%elem_of_snoc_pts; [by apply (ti_pts_pool _ _ HI τ' c x' j')|].
      simplify_eq. done.
    - rewrite omap_app /=. rewrite app_assoc. apply NoDup_app. split_and!; [apply HI| |apply NoDup_singleton].
      intros z Hz ->%list_elem_of_singleton. apply Hx. by rewrite (ti_next_dom _ _ HI) elem_of_list_to_set.
    - rewrite dom_insert_L (ti_next_dom _ _ HI) omap_app /= app_assoc list_to_set_app_L /=. set_solver.
    - intros j' s t b Hs Ht Hb. destruct (decide (j' = j)) as [->|Hne].
      + rewrite list_lookup_insert_eq in Ht; [|lia]. injection Ht as <-. rewrite Hbusy in Hb. injection Hb as <-.
        destruct (lookup_lt_is_Some_2 (s_top σ) j) as [t0 Ht0]; [lia|].
        eapply (pool_ok_publish _ _ _ _ _ _ _ t0 true); [done| | | |done|done|exact Hy|exact Habove| |].
        * intros Hin. apply Hx. by eapply pool_list_in_dom.
        * by apply not_pts_node.
        * intros Hin. apply Hx. rewrite (ti_next_dom _ _ HI) elem_of_list_to_set elem_of_app. by left.
        * intros z τz Hz Hτz. destruct (Hlast z τz Hz Hτz) as [tz Htz].
          destruct (ti_TS _ _ HI τz tz Htz) as (_ & _ & _ & _ & ?). by exists tz.
        * by apply (ti_pool _ _ HI).
      + rewrite list_lookup_insert_ne // in Ht.
        apply (pool_ok_snoc_other _ _ _ (s_next σ)); [done|simpl; congruence| | |by apply (ti_pool _ _ HI)].
        * intros z Hz. simpl. intros [= ->]. apply Hx. by eapply pool_list_in_dom.
        * intros z Hz. rewrite lookup_insert_ne; [done|]. intros ->. apply Hx. by eapply pool_list_in_dom.
    - intros b q Hin. destruct (ti_m_node _ _ HI b q Hin) as [w Hw]. exists w.
      by eapply node_of_l_prefix; [apply prefix_app_r|].
    - apply HI.
    - apply HI.
    - intros τ' c e [Hin|Heq]%elem_of_snoc_pts; [by apply (ti_pt_K _ _ HI τ' c e)|].
      injection Heq as -> -> ->. assert (Hpd : τ ∈ dom (s_K σ)).
      { rewrite (ti_K_dom _ _ HI) /events_of_trace elem_of_list_to_set.
        by apply (list_elem_of_fmap_2 fst _ (τ, Call Push v)). }
      apply elem_of_dom in Hpd as [k Hk]. exists k. split_and!; [done|by apply (ti_K _ _ HI τ)|done].
    - intros i j' e1 e2 Hij Hi Hj'.
      apply lookup_app_Some in Hj' as [Hj'|(Hlen & Hj')]; [apply lookup_app_Some in Hi as [Hi|(? & _)]|].
      + by apply (ti_pt_mono _ _ HI i j').
      + apply lookup_lt_Some in Hj'. lia.
      + apply list_lookup_singleton_Some in Hj' as [Hj0 <-].
        apply lookup_app_Some in Hi as [Hi|(? & _)]; [|lia]. simpl.
        destruct e1 as [[τ1 c1] o1]. destruct (ti_pt_K _ _ HI τ1 c1 o1) as (_ & _ & _ & ?); [|done].
        by eapply list_elem_of_lookup_2.
    - intros τ' t Ht. destruct (ti_TS _ _ HI τ' t Ht) as (k & Hk & ?). exists k.
      split; [by apply PT_l_snoc_old|done].
    - apply HI.
    - apply HI.
    - intros τ' c e [Hin|Heq]%elem_of_snoc_pts; [by apply (ti_pts_pos _ _ HI τ' c e)|].
      injection Heq as _ -> _. apply HI.
  Qed.

  Lemma pool_list_nodup σ j : tss_inv n σ → NoDup (pool_list σ j).
  Proof.
    intros HI. rewrite /pool_list /pool_list_l. destruct (s_sent σ !! j) as [s|] eqn:Hs; [|constructor].
    pose proof (ti_nodes_nodup _ _ HI) as Hnd. apply NoDup_app in Hnd as (_ & Hdisj & Hnd).
    apply NoDup_cons. split.
    - intros Hin. apply elem_of_pnodes in Hin as (τ & c & Hin).
      apply (Hdisj s); [by eapply list_elem_of_lookup_2|]. apply list_elem_of_omap. by exists (τ, c, Some (s, j)).
    - revert Hnd. apply NoDup_omap_sub. intros [[τ c] [[x j']|]] b; simpl; [|done].
      case_decide; [intros [= ->]|]; done.
  Qed.

  Lemma pnodes_unique σ x j j' :
    tss_inv n σ → x ∈ pnodes (s_pts σ) j → x ∈ pool_list σ j' → j = j'.
  Proof.
    intros HI (τ & c & Hin)%elem_of_pnodes Hx'. rewrite /pool_list /pool_list_l in Hx'.
    destruct (s_sent σ !! j') as [s|] eqn:Hs; [|by apply elem_of_nil in Hx'].
    pose proof (ti_nodes_nodup _ _ HI) as Hnd. apply NoDup_app in Hnd as (_ & Hdisj & Hnd).
    apply elem_of_cons in Hx' as [->|Hx'].
    - exfalso. apply (Hdisj s); [by eapply list_elem_of_lookup_2|]. apply list_elem_of_omap. by exists (τ, c, Some (s, j)).
    - apply elem_of_pnodes in Hx' as (τ' & c' & Hin').
      apply list_elem_of_lookup in Hin as [i Hi]. apply list_elem_of_lookup in Hin' as [i' Hi'].
      pose proof (NoDup_omap_inj _ _ i i' _ _ x Hnd Hi Hi' eq_refl eq_refl) as <-.
      rewrite Hi in Hi'. by simplify_eq.
  Qed.

  Lemma tag_node σ z τ x j : tss_inv n σ → tag_of σ z = Some τ → node_of σ τ = Some (x, j) → z = x.
  Proof.
    intros HI Hz Hτ. destruct (tag_of_Some σ z τ Hz) as (i & c & j' & Hi).
    rewrite (node_of_lookup σ i _ (pt_nodup n σ HI) Hi) /= in Hτ. by simplify_eq.
  Qed.

  Lemma tss_inv_next σ j ix x iy y :
    tss_inv n σ → j < n → pool_list σ j !! ix = Some x → 0 < ix → iy < ix → pool_list σ j !! iy = Some y →
    (∀ i' z, iy < i' < ix → pool_list σ j !! i' = Some z → taken σ z) →
    tss_inv n (ev_next σ x y).
  Proof.
    intros HI Hj Hx Hix Hiy Hy Hbetw.
    assert (Hxd : x ∈ dom (s_next σ)) by (eapply pool_list_in_dom; [done|by eapply list_elem_of_lookup_2]).
    assert (Hxn : x ∈ pnodes (s_pts σ) j).
    { rewrite /pool_list /pool_list_l in Hx. destruct (s_sent σ !! j); [|done].
      destruct ix as [|ix]; [lia|]. by eapply list_elem_of_lookup_2. }
    constructor; simpl; try apply HI.
    - rewrite dom_insert_L (ti_next_dom _ _ HI). apply subseteq_union_1_L, singleton_subseteq_l.
      by rewrite -(ti_next_dom _ _ HI).
    - intros j' s t b Hs Ht Hb. pose proof (ti_pool _ _ HI j' s t b Hs Ht Hb) as Hpo.
      destruct (decide (j' = j)) as [->|Hne].
      + by eapply (pool_ok_next _ _ _ _ _ _ _ _ _ ix x iy y); [done|apply (pool_list_nodup σ j HI)|..].
      + apply (pool_ok_next_agree _ _ _ (s_next σ)); [done| |done].
        intros z Hz. rewrite lookup_insert_ne; [done|]. intros ->. apply Hne. symmetry. by eapply pnodes_unique.
  Qed.

  Lemma tss_inv_stamp σ τ t x j k :
    tss_inv n σ → s_os σ !! τ = Some PushInserted →
    node_of σ τ = Some (x, j) → last (pool_list σ j) = Some x →
    PT σ τ = Some k → k ≤ t.1 → t.1 ≤ t.2 → t.2 < s_c σ →
    tss_inv n (ev_stamp σ τ t).
  Proof.
    intros HI Hos Hnode Hlast HPT Hk Ht12 Ht2.
    pose proof (ti_os _ _ HI τ _ Hos) as (Hf & Hτpts & HTS).
    constructor; simpl; try apply HI.
    - rewrite dom_insert_L (ti_os_dom _ _ HI). apply subseteq_union_1_L, singleton_subseteq_l.
      rewrite -(ti_os_dom _ _ HI). by apply elem_of_dom.
    - intros τ' s Hs. destruct (decide (τ' = τ)) as [->|Hne].
      + rewrite lookup_insert_eq in Hs. injection Hs as <-. rewrite /os_ok /= lookup_insert_eq.
        split_and!; [done|done|by eexists].
      + rewrite lookup_insert_ne // in Hs. apply (os_ok_ext σ); [done|done| |done|by apply (ti_os _ _ HI)].
        simpl. by rewrite lookup_insert_ne.
    - intros j' s' t' b Hs Ht Hb. apply pool_ok_stamp; [done| |by apply (ti_pool _ _ HI)].
      intros i z z' Hz Hz' Hτz. pose proof (tag_node σ z τ x j HI Hτz Hnode) as ->.
      assert (Hj' : j' = j).
      { symmetry. apply (pnodes_unique σ x j j' HI); [|by eapply list_elem_of_lookup_2].
        rewrite /node_of /node_of_l in Hnode. destruct (list_find _ _) as [[i0 e]|] eqn:Hf'; [|done].
        apply list_find_Some in Hf' as (Hi0 & He & _). destruct e as [[τ0 c0] o]. simpl in He, Hnode.
        subst o τ0. apply elem_of_pnodes. exists τ, c0. by eapply list_elem_of_lookup_2. }
      subst j'. rewrite last_lookup in Hlast.
      pose proof (NoDup_lookup _ _ _ _ (pool_list_nodup σ j HI) Hz Hlast) as Hieq.
      apply lookup_lt_Some in Hz'. rewrite /pool_list in Hieq. lia.
    - intros τ' t' Ht'. destruct (decide (τ' = τ)) as [->|Hne].
      + rewrite lookup_insert_eq in Ht'. injection Ht' as <-. exists k. split_and!; done.
      + rewrite lookup_insert_ne // in Ht'. by apply (ti_TS _ _ HI).
    - intros b o Hbo Hb. destruct (ti_pre _ _ HI b o Hbo Hb) as (tb & ko & Htb & Hko & Hlt).
      exists tb, ko. rewrite lookup_insert_ne; [done|]. intros ->. by rewrite HTS in Htb.
  Qed.

  Lemma tss_inv_busy σ j b :
    tss_inv n σ → j < n →
    (b = false → ∀ x τ, last (pool_list σ j) = Some x → tag_of σ x = Some τ → is_Some (s_TS σ !! τ)) →
    tss_inv n (ev_busy σ j b).
  Proof.
    intros HI Hj Hb. constructor; simpl; try apply HI.
    - destruct (ti_len _ _ HI) as (? & ? & ?). by rewrite length_insert.
    - intros j' s t b' Hs Ht Hb'. destruct (decide (j' = j)) as [->|Hne].
      + rewrite list_lookup_insert_eq in Hb'; [|destruct (ti_len _ _ HI) as (? & ? & ?); lia].
        injection Hb' as <-.
        destruct (lookup_lt_is_Some_2 (s_busy σ) j) as [b0 Hb0]; [destruct (ti_len _ _ HI) as (? & ? & ?); lia|].
        apply (pool_ok_busy _ _ _ _ _ _ _ _ b0); [done|by apply (ti_pool _ _ HI)].
      + rewrite list_lookup_insert_ne // in Hb'. by apply (ti_pool _ _ HI).
  Qed.

  (* A return keeps everything but the bag part and the operation's state. *)
  Lemma tss_inv_ret σ τ r s :
    tss_inv n σ → τ ∈ (s_ts σ).*1 →
    per_tag_wellformed_bag MayEmpty (λ _, True) (s_ts σ ++ [(τ, Ret r)]) →
    I_stack_vis_pre (s_ts σ ++ [(τ, Ret r)]) (s_m σ) (pts_tags σ) →
    os_ok (ev_ret σ τ r s) τ s →
    tss_inv n (ev_ret σ τ r s).
  Proof.
    intros HI Hτ Hwf' Hst' Hok.
    assert (Hev : events_of_trace (s_ts σ ++ [(τ, Ret r)]) = events_of_trace (s_ts σ)).
    { rewrite events_of_trace_snoc. apply subseteq_union_1_L, singleton_subseteq_l.
      by rewrite /events_of_trace elem_of_list_to_set. }
    constructor; simpl; try apply HI.
    - done.
    - done.
    - rewrite dom_insert_L Hev (ti_os_dom _ _ HI). apply subseteq_union_1_L, singleton_subseteq_l.
      by rewrite /events_of_trace elem_of_list_to_set.
    - intros τ' s' Hs. destruct (decide (τ' = τ)) as [->|Hne].
      + rewrite lookup_insert_eq in Hs. by injection Hs as <-.
      + rewrite lookup_insert_ne // in Hs. apply (os_ok_ext σ); [|done|done|done|by apply (ti_os _ _ HI)].
        simpl. by apply filter_snoc_ne.
    - intros τ' c e Hin. rewrite push_of_trace_snoc_ret. by apply (ti_pts_node _ _ HI τ' c e).
    - rewrite Hev. apply HI.
    - intros b o Hbo Hb. rewrite push_of_trace_snoc_ret in Hb. apply pre_snoc_ret_iff in Hbo.
      by apply (ti_pre _ _ HI).
  Qed.

  Lemma tss_inv_ret_push σ τ :
    tss_inv n σ → s_os σ !! τ = Some PushStamped →
    tss_inv n (ev_ret σ τ #() PushReturned).
  Proof.
    intros HI Hos. pose proof (ti_os _ _ HI τ _ Hos) as ((w & Hf) & Hτpts & HTS).
    apply tss_inv_ret; [done| | | |].
    - apply (list_elem_of_fmap_2 fst _ (τ, Call Push w)).
      assert (Hin : (τ, Call Push w) ∈ filter (λ x : positive * trace, x.1 = τ) (s_ts σ)) by (rewrite Hf; by left).
      by apply list_elem_of_filter in Hin as [_ ?].
    - by eapply per_tag_wellformed_bag_snoc_ret_push; [apply HI|..].
    - by eapply I_stack_vis_pre_snoc_ret_push; [apply HI| |].
    - rewrite /os_ok /= filter_snoc_eq Hf. split_and!; [by eexists|done|done].
  Qed.

  Lemma tss_inv_ret_pop_val σ p b v :
    tss_inv n σ → s_os σ !! p = Some PopCommitted → (b, p) ∈ s_m σ → (b, Call Push v) ∈ s_ts σ →
    tss_inv n (ev_ret σ p (encode_response (NonEmpty v)) PopReturned).
  Proof.
    intros HI Hos Hm Hb. pose proof (ti_os _ _ HI p _ Hos) as (Hf & Hm2).
    apply tss_inv_ret; [done| | | |].
    - apply (list_elem_of_fmap_2 fst _ (p, Call Pop #())).
      assert (Hin : (p, Call Pop #()) ∈ filter (λ x : positive * trace, x.1 = p) (s_ts σ)) by (rewrite Hf; by left).
      by apply list_elem_of_filter in Hin as [_ ?].
    - by apply per_tag_wellformed_bag_snoc_ret_pop; [apply HI|..].
    - exact (I_stack_vis_pre_snoc_ret_pop_val MayEmpty (λ _, True) (s_ts σ) (s_m σ) (pts_tags σ) b p v
               (ti_wf _ _ HI) (ti_stack _ _ HI) Hm Hb Hf).
    - rewrite /os_ok /= filter_snoc_eq Hf. by exists (NonEmpty v).
  Qed.

  Lemma tss_inv_ret_pop_empty σ p icall i :
    tss_inv n σ → s_os σ !! p = Some PopStarted →
    s_ts σ !! icall = Some (p, Call Pop #()) → icall ≤ i ≤ length (s_ts σ) →
    (∀ τ1 τ2, (τ1, τ2) ∈ s_m σ → ¬ push_pop_covers (s_ts σ) τ1 τ2 i) →
    (∀ τ1, τ1 ∈ push_of_trace (s_ts σ) ∧ τ1 ∉ (s_m σ).*1 → ¬ dangling_push_covers (s_ts σ) τ1 i) →
    tss_inv n (ev_ret σ p (encode_response IsEmpty) PopReturned).
  Proof.
    intros HI Hos Hicall Hi Hcov Hdang. pose proof (ti_os _ _ HI p _ Hos) as (Hf & Hpts & Hm2).
    apply tss_inv_ret; [done| | | |].
    - apply (list_elem_of_fmap_2 fst _ (p, Call Pop #())). by eapply list_elem_of_lookup_2.
    - by apply per_tag_wellformed_bag_snoc_ret_pop; [apply HI|..].
    - by eapply I_stack_vis_pre_snoc_ret_pop_empty; [apply HI|..].
    - rewrite /os_ok /= filter_snoc_eq Hf. by exists IsEmpty.
  Qed.

  Lemma tss_inv_commit σ b p x j :
    tss_inv n σ → s_os σ !! p = Some PopStarted → node_of σ b = Some (x, j) → b ∉ (s_m σ).*1 →
    (pre_of_trace (s_ts σ) b p → ∀ c, c ≠ b → ts_tr (s_ts σ) (pts_tags σ) b c →
       c ∈ push_of_trace (s_ts σ) → pt_before (pts_tags σ) c p → c ∈ (s_m σ).*1) →
    tss_inv n (ev_commit σ b p).
  Proof.
    intros HI Hos Hnode Hbm Hlifo. pose proof (ti_os _ _ HI p _ Hos) as (Hf & Hpts & Hm2).
    assert (Hcallp : (p, Call Pop #()) ∈ s_ts σ).
    { assert (Hin : (p, Call Pop #()) ∈ filter (λ x : positive * trace, x.1 = p) (s_ts σ)) by (rewrite Hf; by left).
      by apply list_elem_of_filter in Hin as [_ ?]. }
    assert (Hnret : p ∉ (filter (is_ret ∘ snd) (s_ts σ)).*1).
    { intros ([τ' t] & Heq & Hin)%list_elem_of_fmap_1. simpl in Heq. subst τ'.
      apply list_elem_of_filter in Hin as [Hret Hin].
      assert (Hin' : (p, t) ∈ filter (λ x : positive * trace, x.1 = p) (s_ts σ)) by (by apply list_elem_of_filter).
      rewrite Hf in Hin'. apply list_elem_of_singleton in Hin'. simplify_eq. done. }
    assert (Hbpush : b ∈ push_of_trace (s_ts σ)).
    { rewrite /node_of /node_of_l in Hnode. destruct (list_find _ _) as [[i e]|] eqn:Hfd; [|done].
      apply list_find_Some in Hfd as (Hi & He & _). destruct e as [[τ c] o]. simpl in *. subst.
      apply (ti_pts_node _ _ HI b c (Some (x, j))); [by eapply list_elem_of_lookup_2|by eexists]. }
    destruct (push_tag_in_trace _ _ Hbpush) as [v Hv].
    constructor; simpl; try apply HI.
    - eapply I_stack_vis_pre_snoc_match; [apply HI|apply HI|done|done|exact Hv|done|done|done|done].
    - rewrite dom_insert_L (ti_os_dom _ _ HI). apply subseteq_union_1_L, singleton_subseteq_l.
      rewrite -(ti_os_dom _ _ HI). by apply elem_of_dom.
    - intros τ' s Hs. destruct (decide (τ' = p)) as [->|Hnp].
      + rewrite lookup_insert_eq in Hs. injection Hs as <-. rewrite /os_ok /=. split; [done|].
        rewrite fmap_app elem_of_app. right. by left.
      + rewrite lookup_insert_ne // in Hs. apply (os_ok_ext σ); [done|done|done| |by apply (ti_os _ _ HI)].
        simpl. rewrite fmap_app elem_of_app list_elem_of_singleton. naive_solver.
    - intros j' s t b' Hs Ht Hb'. apply pool_ok_commit; [|done|by apply (ti_pool _ _ HI)].
      intros z Hz. by apply sent_no_tag.
    - intros b' q [Hin|Heq]%elem_of_app; [by apply (ti_m_node _ _ HI b' q)|].
      apply list_elem_of_singleton in Heq. simplify_eq. by eexists.
  Qed.

  Lemma tss_inv_top σ j t' it' :
    tss_inv n σ → j < n → pool_list σ j !! it' = Some t' →
    (∀ i z, it' < i → pool_list σ j !! i = Some z → taken σ z ∧ (taken σ t' → tk σ z ≤ tk σ t')) →
    tss_inv n (ev_top σ j t').
  Proof.
    intros HI Hj Hit Habove. constructor; simpl; try apply HI.
    - destruct (ti_len _ _ HI) as (? & ? & ?). by rewrite length_insert.
    - intros j' s t b Hs Ht Hb. destruct (decide (j' = j)) as [->|Hne].
      + rewrite list_lookup_insert_eq in Ht; [|destruct (ti_len _ _ HI) as (? & ? & ?); lia].
        injection Ht as <-.
        destruct (lookup_lt_is_Some_2 (s_top σ) j) as [t0 Ht0]; [destruct (ti_len _ _ HI) as (? & ? & ?); lia|].
        apply (pool_ok_top _ _ _ _ _ _ _ t0 _ _ it'); [done|done|by apply (ti_pool _ _ HI)].
      + rewrite list_lookup_insert_ne // in Ht. by apply (ti_pool _ _ HI).
  Qed.

  Lemma tss_inv_call_pop σ τ :
    tss_inv n σ → τ ∉ (s_ts σ).*1 → tss_inv n (ev_call σ τ (Call Pop #()) PopCalled).
  Proof.
    intros HI Hfresh. apply tss_inv_call; [done|done|done| | |].
    - by apply per_tag_wellformed_bag_snoc_call_pop; [apply HI|].
    - by apply I_stack_vis_pre_snoc_call_pop; [apply HI|].
    - rewrite /os_ok /= filter_snoc_eq filter_fresh //=. split_and!; [done| |].
      + intros Hin. by apply Hfresh, pts_called.
      + intros Hin. by apply Hfresh, (m2_called σ τ).
  Qed.
End steps.

(* ====================================================================== *)
(* Initialization, reads, the top-CAS, and the emptiness check.           *)
(* ====================================================================== *)

Definition tss_init (sents : list loc) : tss :=
  TSS [] [] [] sents sents (list_to_map ((λ s, (s, s)) <$> sents)) ∅ ∅ ∅ 1 (replicate (length sents) false).

Section more.
  Context (n : nat).
  Implicit Types σ : tss.

  Lemma tss_inv_init sents : length sents = n → NoDup sents → tss_inv n (tss_init sents).
  Proof.
    intros Hlen Hnd.
    assert (Hfst : ((λ s : loc, (s, s)) <$> sents).*1 = sents).
    { clear. induction sents as [|s sents IH]; [done|]. simpl. by f_equal. }
    assert (Hnext : ∀ s, s ∈ sents → (list_to_map ((λ s, (s, s)) <$> sents) : gmap loc loc) !! s = Some s).
    { intros s Hs. apply elem_of_list_to_map_1.
      - by rewrite Hfst.
      - apply list_elem_of_fmap. by exists s. }
    constructor; simpl.
    - apply per_tag_wellformed_bag_nil.
    - apply I_stack_vis_pre_nil.
    - by rewrite length_replicate.
    - done.
    - done.
    - by intros ??? ?%elem_of_nil.
    - by intros ???? ?%elem_of_nil.
    - by rewrite right_id_L.
    - by rewrite right_id_L dom_list_to_map_L Hfst.
    - intros j s t b Hs Ht Hb. rewrite Hs in Ht. injection Ht as <-.
      rewrite lookup_replicate in Hb. destruct Hb as [-> _].
      assert (Hl : pool_list_l sents [] j = [s]) by (by rewrite /pool_list_l Hs).
      constructor; rewrite ?Hl.
      + apply Hnext. by eapply list_elem_of_lookup_2.
      + intros [|i] x Hx Hi; [lia|done].
      + exists 0. split; [done|]. intros [|i] z Hi Hz; [lia|done].
      + intros [|i] x y τx τy Hi; [lia|done].
      + intros x τ _ Hx. done.
    - by intros ?? ?%elem_of_nil.
    - done.
    - done.
    - by intros ??? ?%elem_of_nil.
    - by intros ????? [].
    - done.
    - intros b o Hbo. by apply pre_of_trace_ret in Hbo as [? ?%elem_of_nil].
    - done.
    - by intros ??? ?%elem_of_nil.
  Qed.

  (* reading the top of pool j *)
  Lemma read_top σ j t :
    tss_inv n σ → j < n → s_top σ !! j = Some t →
    ∃ it, pool_list σ j !! it = Some t ∧
      ∀ i z, it < i → pool_list σ j !! i = Some z → taken σ z ∧ (taken σ t → tk σ z ≤ tk σ t).
  Proof.
    intros HI Hj Ht. destruct (ti_len _ _ HI) as (Hls & Hlt & Hlb).
    destruct (lookup_lt_is_Some_2 (s_sent σ) j) as [s Hs]; [lia|].
    destruct (lookup_lt_is_Some_2 (s_busy σ) j) as [b Hb]; [lia|].
    by destruct (ti_pool _ _ HI j s t b Hs Ht Hb) as [_ _ Htop _ _].
  Qed.

  (* reading the next field of a node of pool j *)
  Lemma read_next σ j i x :
    tss_inv n σ → j < n → pool_list σ j !! i = Some x →
    (i = 0 ∧ s_next σ !! x = Some x) ∨
    (0 < i ∧ ∃ k y, k < i ∧ pool_list σ j !! k = Some y ∧ s_next σ !! x = Some y ∧ y ≠ x ∧
      ∀ i' z, k < i' < i → pool_list σ j !! i' = Some z → taken σ z).
  Proof.
    intros HI Hj Hx. destruct (ti_len _ _ HI) as (Hls & Hlt & Hlb).
    destruct (lookup_lt_is_Some_2 (s_sent σ) j) as [s Hs]; [lia|].
    destruct (lookup_lt_is_Some_2 (s_top σ) j) as [t Ht]; [lia|].
    destruct (lookup_lt_is_Some_2 (s_busy σ) j) as [b Hb]; [lia|].
    destruct (ti_pool _ _ HI j s t b Hs Ht Hb) as [Hns Hnx _ _ _].
    destruct i as [|i].
    - left. split; [done|]. rewrite /pool_list /pool_list_l Hs in Hx. simpl in Hx. by simplify_eq.
    - right. split; [lia|]. destruct (Hnx (1 + i) x Hx ltac:(lia)) as (k & y & Hk & Hy & Hxy & Hbetw).
      exists k, y. split_and!; [done|done|done| |done].
      intros ->. pose proof (NoDup_lookup _ _ _ _ (pool_list_nodup n σ j HI) Hx Hy). lia.
  Qed.

  Lemma taken_snapshot σ (pS : list pt_entry) mS x :
    pS `prefix_of` s_pts σ → mS `prefix_of` s_m σ →
    takenb_l (s_sent σ) pS mS x = true → taken σ x.
  Proof. intros Hp Hm. by apply takenb_l_mono. Qed.

  Lemma tk_after σ (mW : list (positive * positive)) x τ :
    mW `prefix_of` s_m σ → tag_of σ x = Some τ → τ ∉ mW.*1 → τ ∈ (s_m σ).*1 → 1 + length mW ≤ tk σ x.
  Proof.
    intros [l Hm] Hx Hτ Hτm. rewrite /tk /tk_l -/(tag_of σ x) Hx.
    rewrite Hm in Hτm |- *.
    assert (Hn : list_find (λ e : positive * positive, e.1 = τ) mW = None).
    { apply list_find_None, Forall_forall. intros [b p] Hin Heq. simpl in Heq. subst b.
      apply Hτ. by apply (list_elem_of_fmap_2 fst _ (τ, p)). }
    rewrite (list_find_app_r _ _ _ Hn).
    rewrite fmap_app elem_of_app in Hτm. destruct Hτm as [?|Hτm]; [done|].
    apply list_elem_of_fmap in Hτm as ([τ' p] & Heq & Hin). simpl in Heq. subst τ'.
    destruct (list_find_elem_of (λ e : positive * positive, e.1 = τ) l (τ, p) Hin eq_refl) as [[i e] Hf].
    rewrite Hf /=. lia.
  Qed.

  Lemma tk_snapshot σ (pS : list pt_entry) mS x :
    tss_inv n σ → pS `prefix_of` s_pts σ → mS `prefix_of` s_m σ → x ∉ s_sent σ →
    takenb_l (s_sent σ) pS mS x = true → tk σ x ≤ length mS.
  Proof.
    intros HI Hp Hm Hxs Hx. rewrite /takenb_l in Hx.
    apply orb_true_iff in Hx as [Hx|Hx]; [by apply bool_decide_eq_true in Hx|].
    destruct (tag_of_l pS x) as [τ|] eqn:Hτ; [|done]. apply bool_decide_eq_true in Hx.
    rewrite /tk (tk_l_stable _ _ _ _ _ τ Hp Hm Hτ Hx). apply tk_l_le.
  Qed.

  (* The remover of node t' (with oldTop t) may set the top to t' when the CAS on the top
     succeeds: its walk saw everything between t' and t taken, before it took t'. *)
  Lemma top_cas_ok σ j t t' it it' (L0 : list loc) (pW : list pt_entry) mW τ' :
    tss_inv n σ → j < n → s_top σ !! j = Some t →
    L0 `prefix_of` pool_list σ j → L0 !! it = Some t → L0 !! it' = Some t' → it' ≤ it →
    pW `prefix_of` s_pts σ → mW `prefix_of` s_m σ →
    (∀ i z, it' < i → L0 !! i = Some z → takenb_l (s_sent σ) pW mW z = true) →
    tag_of σ t' = Some τ' → τ' ∉ mW.*1 → τ' ∈ (s_m σ).*1 →
    ∀ i z, it' < i → pool_list σ j !! i = Some z → taken σ z ∧ (taken σ t' → tk σ z ≤ tk σ t').
  Proof.
    intros HI Hj Ht HL0 Hit Hit' Hle HpW HmW Hwalk Hτ' Hτ'W Hτ'm i z Hi Hz.
    destruct (read_top σ j t HI Hj Ht) as (it0 & Hit0 & Htop).
    pose proof (prefix_lookup_Some _ _ _ _ Hit HL0) as Hit_.
    pose proof (NoDup_lookup _ _ _ _ (pool_list_nodup n σ j HI) Hit0 Hit_) as ->.
    assert (Hnot_sent : ∀ i0 z0, 0 < i0 → pool_list σ j !! i0 = Some z0 → z0 ∉ s_sent σ).
    { intros i0 z0 Hi0 Hz0 Hsent. rewrite /pool_list /pool_list_l in Hz0.
      destruct (s_sent σ !! j) as [s|] eqn:Hs; [|done]. destruct i0 as [|i0]; [lia|]. simpl in Hz0.
      pose proof (ti_nodes_nodup _ _ HI) as Hnd. apply NoDup_app in Hnd as (_ & Hdisj & _).
      destruct (pnodes_lookup _ _ _ _ Hz0) as (k & τ0 & c0 & Hk & _).
      apply (Hdisj z0 Hsent). apply list_elem_of_omap. exists (τ0, c0, Some (z0, j)).
      split; [by eapply list_elem_of_lookup_2|done]. }
    assert (Htk' : 1 + length mW ≤ tk σ t') by (by eapply tk_after).
    destruct (decide (i < length L0)) as [HiL|HiL].
    - destruct (lookup_lt_is_Some_2 L0 i HiL) as [z0 Hz0].
      rewrite (prefix_lookup_Some _ _ _ _ Hz0 HL0) in Hz. injection Hz as <-.
      pose proof (Hwalk i z0 Hi Hz0) as Hz0W.
      split; [by eapply taken_snapshot|]. intros _.
      pose proof (tk_snapshot σ pW mW z0 HI HpW HmW (Hnot_sent i z0 ltac:(lia) (prefix_lookup_Some _ _ _ _ Hz0 HL0)) Hz0W).
      lia.
    - assert (Hit_lt : it < i) by (apply lookup_lt_Some in Hit; lia).
      destruct (Htop i z Hit_lt Hz) as [Hzt Hzle]. split; [done|]. intros Ht'.
      destruct (decide (it' = it)) as [->|Hne].
      + rewrite Hit in Hit'. injection Hit' as <-. by apply Hzle.
      + pose proof (Hwalk it t ltac:(lia) Hit) as HtW.
        pose proof (tk_snapshot σ pW mW t HI HpW HmW (Hnot_sent it t ltac:(lia) Hit_) HtW).
        specialize (Hzle (taken_snapshot σ pW mW t HpW HmW HtW)). lia.
  Qed.

  (* The emptiness check of pool j succeeded: the top is still the oldTop A of a scan that saw
     the whole pool taken; then every node of the pool is taken by a commit in mT. *)
  Lemma check_ok σ j A (L0 : list loc) ia (pS : list pt_entry) mS mT :
    tss_inv n σ → j < n → s_top σ !! j = Some A →
    L0 `prefix_of` pool_list σ j → L0 !! ia = Some A →
    pS `prefix_of` s_pts σ → mS `prefix_of` mT → mT `prefix_of` s_m σ →
    (∀ x, x ∈ L0 → takenb_l (s_sent σ) pS mS x = true) →
    ∀ x, x ∈ pool_list σ j → takenb_l (s_sent σ) (s_pts σ) mT x = true.
  Proof.
    intros HI Hj Ht HL0 Hia HpS HmS HmT Hall x Hx.
    destruct (read_top σ j A HI Hj Ht) as (ia0 & Hia0 & Htop).
    pose proof (NoDup_lookup _ _ _ _ (pool_list_nodup n σ j HI) Hia0 (prefix_lookup_Some _ _ _ _ Hia HL0)) as ->.
    apply list_elem_of_lookup in Hx as [i Hi].
    destruct (decide (i ≤ ia)) as [Hle|Hlt].
    - assert (Hz : L0 !! i = Some x).
      { destruct (lookup_lt_is_Some_2 L0 i) as [z Hz]; [apply lookup_lt_Some in Hia; lia|].
        rewrite (prefix_lookup_Some _ _ _ _ Hz HL0) in Hi. by simplify_eq. }
      eapply takenb_l_mono; [done|done|]. apply Hall. by eapply list_elem_of_lookup_2.
    - destruct (Htop i x ltac:(lia) Hi) as [Hxt Hxle].
      pose proof (Hall A (list_elem_of_lookup_2 _ _ _ Hia)) as HAS.
      specialize (Hxle (taken_snapshot σ pS mS A HpS (transitivity HmS HmT) HAS)).
      (* A's commit is in mS, so x's commit is in mT *)
      rewrite /taken /takenb /takenb_l in Hxt.
      apply orb_true_iff in Hxt as [Hxt|Hxt]; [by rewrite /takenb_l Hxt|].
      destruct (tag_of_l (s_pts σ) x) as [τ|] eqn:Hτ; [|done]. apply bool_decide_eq_true in Hxt.
      rewrite /takenb_l Hτ. apply orb_true_iff. right. apply bool_decide_eq_true.
      destruct (decide (τ ∈ mT.*1)) as [|Hnot]; [done|exfalso].
      pose proof (tk_after σ mT x τ HmT Hτ Hnot Hxt) as Hge.
      destruct (decide (A ∈ s_sent σ)) as [HAs|HAs].
      + assert (HA0 : tk σ A = 0) by (by rewrite /tk /tk_l (sent_no_tag n σ A HI HAs)). lia.
      + pose proof (tk_snapshot σ pS mS A HI HpS (transitivity HmS HmT) HAs HAS) as HAle.
        pose proof (prefix_length _ _ HmS). lia.
  Qed.

  Lemma per_tag_wellformed_prefix (ts tsT : list (positive * trace)) :
    tsT `prefix_of` ts → per_tag_wellformed ts → per_tag_wellformed tsT.
  Proof.
    intros [l ->] Hwf τ. destruct (Hwf τ) as (n' & v & v' & Hp). exists n', v, v'.
    rewrite filter_app in Hp. by eapply prefix_app_l.
  Qed.

  Lemma ret_has_call (ts : list (positive * trace)) τ r :
    per_tag_wellformed ts → (τ, Ret r) ∈ ts → ∃ nc vc, (τ, Call nc vc) ∈ ts.
  Proof.
    intros Hwf Hr. destruct (Hwf τ) as (nc & vc & v' & [k Hk]).
    assert (Hr' : (τ, Ret r) ∈ filter (λ t : positive * trace, t.1 = τ) ts) by (by apply list_elem_of_filter).
    exists nc, vc.
    destruct (filter (λ t : positive * trace, t.1 = τ) ts) as [|a fl] eqn:Hf; [by apply elem_of_nil in Hr'|].
    simpl in Hk. injection Hk as Ha _. subst a.
    assert (Hin : (τ, Call nc vc) ∈ filter (λ t : positive * trace, t.1 = τ) ts) by (rewrite Hf; by left).
    by apply list_elem_of_filter in Hin as [_ ?].
  Qed.

  Lemma call_unique (ts : list (positive * trace)) τ n1 v1 n2 v2 :
    per_tag_wellformed ts → (τ, Call n1 v1) ∈ ts → (τ, Call n2 v2) ∈ ts → n1 = n2 ∧ v1 = v2.
  Proof.
    intros Hwf H1 H2. destruct (Hwf τ) as (nc & vc & v' & Hp).
    assert (∀ n0 v, (τ, Call n0 v) ∈ ts → n0 = nc ∧ v = vc) as Hc.
    { intros n0 v Hin. assert (Hin' : (τ, Call n0 v) ∈ filter (λ t : positive * trace, t.1 = τ) ts)
        by (by apply list_elem_of_filter).
      eapply elem_of_prefix in Hin'; [|exact Hp].
      apply elem_of_cons in Hin' as [Heq|Hin']; [by simplify_eq|].
      apply list_elem_of_singleton in Hin'. discriminate. }
    destruct (Hc _ _ H1) as [-> ->]. destruct (Hc _ _ H2) as [-> ->]. done.
  Qed.

  Lemma call_in_prefix (ts tsT : list (positive * trace)) τ r nc vc :
    per_tag_wellformed ts → tsT `prefix_of` ts → (τ, Ret r) ∈ tsT → (τ, Call nc vc) ∈ ts →
    (τ, Call nc vc) ∈ tsT.
  Proof.
    intros Hwf Hp Hr Hc.
    destruct (ret_has_call tsT τ r (per_tag_wellformed_prefix _ _ Hp Hwf) Hr) as (n' & v' & Hc').
    assert (Hc'' : (τ, Call n' v') ∈ ts) by (by eapply elem_of_prefix).
    by destruct (call_unique ts τ nc vc n' v' Hwf Hc Hc'') as [-> ->].
  Qed.

  Lemma ret_of_tag_prefix (ts tsT : list (positive * trace)) τ r e :
    tsT `prefix_of` ts → ret_of_tag ts τ = Some (r, e) → r < length tsT → e ∈ tsT ∧ e.1 = τ ∧ is_ret e.2.
  Proof.
    intros Hp Hr Hlt. apply list_find_Some in Hr as (Hre & [He Hret] & _).
    destruct (lookup_lt_is_Some_2 tsT r Hlt) as [e' He'].
    rewrite (prefix_lookup_Some _ _ _ _ He' Hp) in Hre. simplify_eq.
    split_and!; [by eapply list_elem_of_lookup_2|done|done].
  Qed.

  Lemma call_of_tag_prefix (ts tsT : list (positive * trace)) τ nc vc :
    tsT `prefix_of` ts → (τ, Call nc vc) ∈ tsT → ∃ k e, call_of_tag ts τ = Some (k, e) ∧ k < length tsT.
  Proof.
    intros [l ->] Hin.
    destruct (list_find_elem_of (λ t : positive * trace, t.1 = τ ∧ is_call t.2) tsT (τ, Call nc vc))
      as [[k e] Hf]; [done|done|].
    exists k, e. split; [by rewrite /call_of_tag (list_find_app_l _ _ _ _ _ Hf)|].
    apply list_find_Some in Hf as (Hk & _). by apply lookup_lt_Some in Hk.
  Qed.

  (* The witness for a pop that returns EMPTY: the end of its scan, when every node of every
     pool was taken by a commit before that moment. *)
  Lemma empty_witness σ (tsT : list (positive * trace)) (mT : list (positive * positive)) (pT : list pt_entry) :
    tss_inv n σ →
    tsT `prefix_of` s_ts σ → mT `prefix_of` s_m σ → pT `prefix_of` s_pts σ →
    (∀ τ1 r v, (τ1, Ret r) ∈ tsT → (τ1, Call Push v) ∈ tsT → ∃ c x j, (τ1, c, Some (x, j)) ∈ pT) →
    (∀ τ2, τ2 ∈ mT.*2 → (τ2, Call Pop #()) ∈ tsT) →
    (∀ j x, x ∈ pnodes pT j → takenb_l (s_sent σ) (s_pts σ) mT x = true) →
    (∀ τ1 τ2, (τ1, τ2) ∈ s_m σ → ¬ push_pop_covers (s_ts σ) τ1 τ2 (length tsT)) ∧
    (∀ τ1, τ1 ∈ push_of_trace (s_ts σ) ∧ τ1 ∉ (s_m σ).*1 → ¬ dangling_push_covers (s_ts σ) τ1 (length tsT)).
  Proof.
    intros HI HtsT HmT HpT Hpointed Hcalled Hall.
    pose proof (per_tag_wellformed_bag_wellformed _ _ _ (ti_wf _ _ HI)) as Hwf.
    (* a push returned before T* was committed before T* *)
    assert (Hkey : ∀ τ1 v r e, (τ1, Call Push v) ∈ s_ts σ → ret_of_tag (s_ts σ) τ1 = Some (r, e) →
              r < length tsT → τ1 ∈ mT.*1).
    { intros τ1 v r e Hc Hr Hlt.
      destruct (ret_of_tag_prefix _ _ τ1 r e HtsT Hr Hlt) as (HeT & He1 & He2).
      destruct e as [τ' [| |ρ]]; simpl in *; try done. subst τ'.
      pose proof (call_in_prefix _ _ τ1 ρ Push v Hwf HtsT HeT Hc) as HcT.
      destruct (Hpointed τ1 ρ v HeT HcT) as (c & x & j & Hin).
      assert (Hx : x ∈ pnodes pT j) by (apply elem_of_pnodes; eauto).
      specialize (Hall j x Hx). rewrite /takenb_l in Hall.
      apply list_elem_of_lookup in Hin as [i Hi].
      pose proof (tag_of_lookup σ i τ1 c x j (nodes_nodup n σ HI) (prefix_lookup_Some _ _ _ _ Hi HpT)) as Htag.
      rewrite /tag_of in Htag. rewrite Htag in Hall.
      apply orb_true_iff in Hall as [Hs|Hm]; [|by apply bool_decide_eq_true in Hm].
      exfalso. apply bool_decide_eq_true in Hs. by rewrite (sent_no_tag n σ x HI Hs) in Htag. }
    pose proof (isv_valid _ _ _ (ti_stack _ _ HI)) as Hvm.
    split.
    - intros τ1 τ2 Hin Hcov. rewrite /push_pop_covers in Hcov.
      destruct (ret_of_tag (s_ts σ) τ1) as [[r e]|] eqn:Hr; [|done].
      destruct (call_of_tag (s_ts σ) τ2) as [[k e']|] eqn:Hc; [|done].
      simpl in Hcov. destruct Hcov as [Hr' Hk'].
      destruct (valid_match_call_push _ _ _ _ Hvm Hin) as [v Hv].
      pose proof (Hkey τ1 v r e Hv Hr Hr') as Hτ1.
      apply list_elem_of_fmap in Hτ1 as ([τ1' τ2'] & Heq & Hin'). simpl in Heq. subst τ1'.
      assert (Hin'' : (τ1, τ2') ∈ s_m σ) by (by eapply elem_of_prefix).
      pose proof (valid_match_inj_ret _ _ _ _ _ Hvm Hin Hin'') as <-.
      assert (HcT : (τ2, Call Pop #()) ∈ tsT) by (apply Hcalled; by apply (list_elem_of_fmap_2 snd _ (τ1, τ2))).
      destruct (call_of_tag_prefix _ _ τ2 _ _ HtsT HcT) as (k' & e'' & Hc' & Hk'').
      rewrite Hc in Hc'. simplify_eq. lia.
    - intros τ1 [Hpush Hnm] Hdang. rewrite /dangling_push_covers in Hdang.
      destruct (ret_of_tag (s_ts σ) τ1) as [[r e]|] eqn:Hr; [|done]. simpl in Hdang.
      destruct (push_tag_in_trace _ _ Hpush) as [v Hv].
      pose proof (Hkey τ1 v r e Hv Hr Hdang) as Hτ1.
      apply Hnm. destruct HmT as [l Hm]. rewrite Hm fmap_app elem_of_app. by left.
  Qed.
End more.

(* ====================================================================== *)
(* The node fields under the steps.                                       *)
(* ====================================================================== *)

Section fields.
  Context (n : nat).
  Implicit Types σ : tss.

  Lemma takenb_publish σ τ x j y z : z ≠ x → takenb (ev_publish σ τ x j y) z = takenb σ z.
  Proof. intros Hne. rewrite /takenb /=. apply takenb_l_snoc_ne. simpl. congruence. Qed.

  Lemma tsfield_publish σ τ x j y z : z ≠ x → tsfield (ev_publish σ τ x j y) z = tsfield σ z.
  Proof. intros Hne. rewrite /tsfield /tag_of /= tag_of_l_snoc_ne //. simpl. congruence. Qed.

  Lemma takenb_publish_new σ τ x j y :
    tss_inv n σ → x ∉ dom (s_next σ) → τ ∉ (s_m σ).*1 → takenb (ev_publish σ τ x j y) x = false.
  Proof.
    intros HI Hx Hτ. rewrite /takenb /takenb_l /= tag_of_l_snoc (not_pts_node n σ x HI Hx).
    rewrite decide_True //. apply orb_false_iff. split; apply bool_decide_eq_false; [|done].
    intros Hs. apply Hx. rewrite (ti_next_dom _ _ HI) elem_of_list_to_set elem_of_app. by left.
  Qed.

  Lemma tsfield_publish_new σ τ x j y :
    tss_inv n σ → x ∉ dom (s_next σ) → s_TS σ !! τ = None →
    tsfield (ev_publish σ τ x j y) x = timestamp_val None.
  Proof.
    intros HI Hx Hτ. rewrite /tsfield /tag_of /= tag_of_l_snoc (not_pts_node n σ x HI Hx) /= decide_True //=.
    by rewrite Hτ.
  Qed.

  Lemma tsfield_stamp σ τ t z : tag_of σ z ≠ Some τ → tsfield (ev_stamp σ τ t) z = tsfield σ z.
  Proof.
    intros Hne. rewrite /tsfield /=. change (tag_of (ev_stamp σ τ t) z) with (tag_of σ z).
    destruct (tag_of σ z) as [τ'|] eqn:Hz; simpl; [|done]. rewrite lookup_insert_ne //. congruence.
  Qed.

  Lemma tsfield_stamp_new σ τ t x : tag_of σ x = Some τ → tsfield (ev_stamp σ τ t) x = timestamp_val (Some t).
  Proof.
    intros Hx. rewrite /tsfield /=. change (tag_of (ev_stamp σ τ t) x) with (tag_of σ x).
    rewrite Hx /=. by rewrite lookup_insert_eq.
  Qed.

  Lemma takenb_commit σ b p z : tag_of σ z ≠ Some b → takenb (ev_commit σ b p) z = takenb σ z.
  Proof.
    intros Hne. rewrite /takenb /takenb_l /=. change (tag_of_l (s_pts σ) z) with (tag_of σ z).
    destruct (tag_of σ z) as [τ'|] eqn:Hz; [|done]. f_equal.
    apply bool_decide_ext. rewrite fmap_app elem_of_app list_elem_of_singleton. naive_solver.
  Qed.

  Lemma takenb_commit_new σ b p x : tag_of σ x = Some b → takenb (ev_commit σ b p) x = true.
  Proof.
    intros Hx. rewrite /takenb /takenb_l /=. change (tag_of_l (s_pts σ) x) with (tag_of σ x).
    rewrite Hx. apply orb_true_iff. right.
    apply bool_decide_eq_true. rewrite fmap_app elem_of_app. right. by left.
  Qed.

  Lemma tag_of_publish σ τ x j y z : z ≠ x → tag_of (ev_publish σ τ x j y) z = tag_of σ z.
  Proof. intros Hne. rewrite /tag_of /= tag_of_l_snoc_ne //. simpl. congruence. Qed.
End fields.

(* ====================================================================== *)
(* What a push knows about its node after publishing it.                  *)
(* ====================================================================== *)

Section published.
  Context (n : nat).
  Implicit Types σ : tss.

  Lemma node_of_tag σ τ x j : tss_inv n σ → node_of σ τ = Some (x, j) → tag_of σ x = Some τ.
  Proof.
    intros HI. rewrite /node_of /node_of_l.
    destruct (list_find _ _) as [[i e]|] eqn:Hf; [|done]. intros He.
    apply list_find_Some in Hf as (Hi & Hτ & _).
    destruct e as [[τ' c] e2]. simpl in *. subst τ' e2.
    exact (tag_of_lookup σ i τ c x j (nodes_nodup n σ HI) Hi).
  Qed.

  Lemma node_of_dom σ τ x j : tss_inv n σ → node_of σ τ = Some (x, j) → x ∈ dom (s_next σ).
  Proof.
    intros HI. rewrite /node_of /node_of_l.
    destruct (list_find _ _) as [[i e]|] eqn:Hf; [|done]. intros He.
    apply list_find_Some in Hf as (Hi & _ & _).
    rewrite (ti_next_dom _ _ HI) elem_of_list_to_set elem_of_app. right.
    apply list_elem_of_omap. exists e. split; [by eapply list_elem_of_lookup_2|by rewrite He].
  Qed.

  Lemma publish_facts σ τ x j y :
    tss_inv n σ → j < n → s_os σ !! τ = Some PushCalled → x ∉ dom (s_next σ) →
    node_of (ev_publish σ τ x j y) τ = Some (x, j) ∧ PT (ev_publish σ τ x j y) τ = Some (s_c σ) ∧
    tag_of (ev_publish σ τ x j y) x = Some τ ∧
    pool_list (ev_publish σ τ x j y) j = pool_list σ j ++ [x].
  Proof.
    intros HI Hj Hos Hx.
    destruct (ti_os _ _ HI τ _ Hos) as (_ & Hτpts & _).
    assert (Hnf : list_find (λ e : pt_entry, e.1.1 = τ) (s_pts σ) = None).
    { apply list_find_None, Forall_forall. intros [[τ' c] e] Hin Heq. simpl in Heq. subst τ'.
      apply Hτpts, elem_of_pts_tags. by exists c, e. }
    destruct (ti_len _ _ HI) as (Hls & _ & _).
    destruct (lookup_lt_is_Some_2 (s_sent σ) j) as [s Hs]; first lia.
    split_and!.
    - rewrite /node_of /= node_of_l_snoc Hnf /= decide_True //.
    - rewrite /PT /= PT_l_snoc /PT_l Hnf /= decide_True //.
    - rewrite /tag_of /= tag_of_l_snoc (not_pts_node n σ x HI Hx) /= decide_True //.
    - rewrite /pool_list /= (pool_list_l_snoc _ _ _ _ s Hs) /= decide_True //.
  Qed.

  (* a node of pool j keeps its tag *)
  Lemma tag_of_old σ σ' j z τ :
    tss_inv n σ → tss_inv n σ' → s_sent σ = s_sent σ' → s_pts σ `prefix_of` s_pts σ' →
    z ∈ pool_list σ j → tag_of σ' z = Some τ → tag_of σ z = Some τ.
  Proof.
    intros HI HI' Hs Hp Hz Hτ. rewrite /pool_list /pool_list_l in Hz.
    destruct (s_sent σ !! j) as [s|] eqn:Hsj; [|by apply elem_of_nil in Hz].
    apply elem_of_cons in Hz as [->|Hz].
    - rewrite /tag_of (sent_no_tag n σ' s HI') in Hτ; [done|]. rewrite -Hs. by eapply list_elem_of_lookup_2.
    - apply elem_of_pnodes in Hz as (τ' & c & Hin). apply list_elem_of_lookup in Hin as [i Hi].
      pose proof (tag_of_lookup σ i τ' c z j (nodes_nodup n σ HI) Hi) as Hz.
      rewrite /tag_of (tag_of_l_prefix _ _ _ _ Hp Hz) in Hτ. by simplify_eq.
  Qed.
End published.

(* ====================================================================== *)
(* Facts used by the pop.                                                 *)
(* ====================================================================== *)

Lemma push_of_trace_call (ts : list (positive * trace)) τ v :
  (τ, Call Push v) ∈ ts → τ ∈ push_of_trace ts.
Proof.
  intros Hin. apply (list_elem_of_fmap_2 fst _ (τ, Call Push v)).
  apply list_elem_of_filter. split; [by eexists|done].
Qed.

Section pop_facts.
  Context (n : nat).
  Implicit Types σ : tss.

  Lemma TS_pos σ τ t : tss_inv n σ → s_TS σ !! τ = Some t → 1 ≤ t.1.
  Proof.
    intros HI Ht. destruct (ti_TS _ _ HI τ t Ht) as (k & Hk & Hkt & _).
    destruct (PT_Some σ τ k Hk) as (i & e & Hi & _ & He).
    destruct e as [[τ' c] o]. simpl in He. subst c.
    pose proof (ti_pts_pos _ _ HI τ' k o ltac:(by eapply list_elem_of_lookup_2)). lia.
  Qed.

  Lemma sent_taken σ s : s ∈ s_sent σ → taken σ s.
  Proof. intros Hs. rewrite /taken /takenb /takenb_l bool_decide_eq_true_2 //. Qed.

  (* the node at position i ≥ 1 of pool j belongs to a push *)
  Lemma pool_node_tag σ j i x :
    tss_inv n σ → 1 ≤ i → pool_list σ j !! i = Some x →
    ∃ b, tag_of σ x = Some b ∧ node_of σ b = Some (x, j) ∧ b ∈ push_of_trace (s_ts σ).
  Proof.
    intros HI Hi Hx. destruct (pool_list_tag n σ j i x HI Hi Hx) as (b & c & Htag & Hin).
    exists b. split_and!; [done| |].
    - apply list_elem_of_lookup in Hin as [k Hk]. exact (node_of_lookup σ k _ (pt_nodup n σ HI) Hk).
    - destruct (ti_pts_node _ _ HI b c (Some (x, j)) Hin) as [Hs _]. by apply Hs.
  Qed.

  (* A pop that saw the node of push b without a timestamp did not start after b returned. *)
  Lemma elim_unstamped σr σ b p :
    tss_inv n σr → s_ts σr `prefix_of` s_ts σ → (p, Call Pop #()) ∈ s_ts σr →
    b ∈ push_of_trace (s_ts σr) → s_TS σr !! b = None → ¬ pre_of_trace (s_ts σ) b p.
  Proof.
    intros HIr [l Hl] Hp Hb HTS Hpre. rewrite Hl in Hpre.
    apply pre_of_trace_app_inv in Hpre; [|by exists Pop, #()].
    destruct (pre_of_trace_ret _ _ _ Hpre) as [r Hr].
    destruct (push_ret_TS n σr b r HIr Hb Hr) as [t Ht]. congruence.
  Qed.

  (* A pop that saw the node of push b with a timestamp later than its start time. *)
  Lemma elim_stamped σ b p tb kp s1 s2 :
    tss_inv n σ → b ∈ push_of_trace (s_ts σ) → s_TS σ !! b = Some tb → s_K σ !! p = Some kp →
    kp ≤ s1 → s1 ≤ s2 → s2 < tb.1 → ¬ pre_of_trace (s_ts σ) b p.
  Proof.
    intros HI Hpush Hb Hp Hk Hs Hlt Hpre.
    destruct (ti_pre _ _ HI b p Hpre Hpush) as (tb' & kp' & Hb' & Hp' & Hlt').
    rewrite Hb in Hb'. injection Hb' as <-. rewrite Hp in Hp'. injection Hp' as <-.
    destruct (ti_TS _ _ HI b tb Hb) as (_ & _ & _ & Hle & _). lia.
  Qed.

  (* a returned push has its point and node *)
  Lemma returned_push_pt σ τ r v :
    tss_inv n σ → (τ, Ret r) ∈ s_ts σ → (τ, Call Push v) ∈ s_ts σ →
    ∃ c x j, (τ, c, Some (x, j)) ∈ s_pts σ.
  Proof.
    intros HI Hr Hc. pose proof (push_of_trace_call _ _ _ Hc) as Hpush.
    destruct (push_ret_TS n σ τ r HI Hpush Hr) as [t Ht].
    pose proof (TS_pts n σ τ t HI Ht) as (c & e & Hin)%elem_of_pts_tags.
    destruct (ti_pts_node _ _ HI τ c e Hin) as [_ Hsome].
    destruct (Hsome Hpush) as [[x j] ->]. by exists c, x, j.
  Qed.
End pop_facts.

Lemma tag_push n σ x b : tss_inv n σ → tag_of σ x = Some b → b ∈ push_of_trace (s_ts σ).
Proof.
  intros HI Htag. destruct (tag_of_Some σ x b Htag) as (i & c & j & Hi).
  destruct (ti_pts_node _ _ HI b c (Some (x, j))) as [Hs _]; [by eapply list_elem_of_lookup_2|]. by apply Hs.
Qed.
