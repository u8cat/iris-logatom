(* tracking.v *)
(* A mechanization of the meta-configuration tracking technique proposed by
    Prasad Jayanti, Siddhartha Jayanti, Ugur Y. Yavuz, and Lizzie Hernandez.
    2024. A Universal, Sound, and Complete Forward Reasoning Technique for
    Machine-Verified Proofs of Linearizability. Proc. ACM Program. Lang. 8,
    POPL, Article 82 (January 2024), 29 pages. https://doi.org/10.1145/3632924 *)

From stdpp Require Import base list gmap propset.
From iris_logatom.pure_logic Require Import linear.
From iris_logatom.heap_lang Require Import patch.
From iris.heap_lang Require Import notation.

(* .1.1 is the index of operation; .1.2 is the value of request;
  .2 is the value of response *)
Definition proc_status: Set := nat * val * option val.

Definition single_config {M: model}: Set := S * gmap positive proc_status.
Definition meta_config {M: model} := propset single_config.

Section def.
  Context `{M : model}.
  Implicit Types (s : S) (π : gmap positive proc_status) (τ : positive)
                 (v : val) (scfg : single_config) (mcfg : meta_config).

  Definition mcfg_init: meta_config := {[ (s_init, ∅) ]}.

  Inductive mcfg_step: meta_config → meta_config → list (positive*trace) → Prop :=
    | mcfg_step_call mcfg τ n v :
      set_Forall (λ '(_, π), τ ∉ dom π) mcfg →
      default default_vr (valid_requests!!n) v →
      mcfg_step mcfg ((λ '(s, π), (s, <[τ:=(n, v, None)]> π)) <$> mcfg) [(τ, Call n v)]
    | mcfg_step_interm mcfg s π τ n v s' v' :
      (s,π) ∈ mcfg →
      π !! τ = Some (n, v, None) →
      default default_rr (request_responses!!n) s v s' v' →
      mcfg_step mcfg ({[ (s',<[τ:=(n, v, Some v')]> π) ]} ∪ mcfg) []
    | mcfg_step_ret mcfg τ v' :
      mcfg_step mcfg (mcfg ∩ {[ (_,π) | snd <$> (π !! τ) = Some (Some v') ]}) [(τ, Ret v')].

  Inductive mcfg_steps: meta_config → meta_config → list (positive*trace) → Prop :=
    | mcfg_steps_nil mcfg : mcfg_steps mcfg mcfg []
    | mcfg_steps_cons mcfg0 mcfg1 ts1 mcfg2 ts2 :
      mcfg_step  mcfg0 mcfg1 ts1 →
      mcfg_steps mcfg1 mcfg2 ts2 →
      mcfg_steps mcfg0 mcfg2 (ts1++ts2).

  Definition I_metaconfig ts : Prop :=
    ∃ mcfg' s π, mcfg_steps mcfg_init mcfg' ts ∧ (s, π) ∈ mcfg'.

  Lemma mcfg_steps_singleton mcfg0 mcfg1 ts :
    mcfg_step mcfg0 mcfg1 ts → mcfg_steps mcfg0 mcfg1 ts.
  Proof.
    intros H.
    rewrite -(app_nil_r ts).
    eapply mcfg_steps_cons; first exact H.
    apply mcfg_steps_nil.
  Qed.

  Lemma mcfg_steps_app mcfg0 mcfg1 mcfg2 ts1 ts2 :
    mcfg_steps mcfg0 mcfg1 ts1 →
    mcfg_steps mcfg1 mcfg2 ts2 →
    mcfg_steps mcfg0 mcfg2 (ts1 ++ ts2).
  Proof.
    intros H1 H2. revert mcfg2 ts2 H2.
    induction H1 as [mcfg|mcfg0' mcfg1' ts1' mcfg2' ts2' Hstep H_rest IH];
      intros mcfg2 ts2_outer H2.
    - simpl. exact H2.
    - rewrite -app_assoc.
      eapply mcfg_steps_cons; first exact Hstep.
      by apply IH.
  Qed.

  Lemma mcfg_steps_snoc mcfg0 mcfg1 mcfg2 ts1 ts2 :
    mcfg_steps mcfg0 mcfg1 ts1 →
    mcfg_step mcfg1 mcfg2 ts2 →
    mcfg_steps mcfg0 mcfg2 (ts1 ++ ts2).
  Proof.
    intros H1 H2.
    eapply mcfg_steps_app; first exact H1.
    by apply mcfg_steps_singleton.
  Qed.
End def.

Section lemmas.
  Context `{M : model}.
  Implicit Types (s : S) (π : gmap positive proc_status) (τ : positive)
                 (v : val) (ts : list (positive*trace)).

  (** Canonical gmap derived from a trace, tracking each τ's latest non-Ret event. *)
  Definition proc_status_of_trace (ts : list (positive*trace)) : gmap positive proc_status :=
    foldl (λ p e,
      match e with
      | (τ, Call n v) => <[τ:=(n, v, None)]> p
      | (τ, Lin n v v') => <[τ:=(n, v, Some v')]> p
      | (τ, Ret _) => p
      end) ∅ ts.

  Lemma proc_status_of_trace_nil : proc_status_of_trace [] = ∅.
  Proof. done. Qed.

  Lemma proc_status_of_trace_snoc_call ts τ n v :
    proc_status_of_trace (ts ++ [(τ, Call n v)]) = <[τ:=(n, v, None)]> (proc_status_of_trace ts).
  Proof. rewrite /proc_status_of_trace foldl_app //. Qed.

  Lemma proc_status_of_trace_snoc_lin ts τ n v v' :
    proc_status_of_trace (ts ++ [(τ, Lin n v v')]) = <[τ:=(n, v, Some v')]> (proc_status_of_trace ts).
  Proof. rewrite /proc_status_of_trace foldl_app //. Qed.

  Lemma proc_status_of_trace_snoc_ret ts τ v' :
    proc_status_of_trace (ts ++ [(τ, Ret v')]) = proc_status_of_trace ts.
  Proof. rewrite /proc_status_of_trace foldl_app //. Qed.

  Lemma proc_status_of_trace_lookup_None ts τ :
    filter (λ t, t.1 = τ) ts = [] →
    proc_status_of_trace ts !! τ = None.
  Proof.
    induction ts as [|t ts IH] using rev_ind; intros Hfilter.
    - by rewrite proc_status_of_trace_nil lookup_empty.
    - rewrite filter_app in Hfilter.
      apply app_nil in Hfilter as [Hpre Hsnoc].
      destruct t as [τ' tr].
      destruct (decide (τ' = τ)) as [-> | Hne].
      + rewrite filter_cons_True // filter_nil in Hsnoc.
      + destruct tr as [v|v v'|v'].
        * rewrite proc_status_of_trace_snoc_call lookup_insert_ne //.
          by apply IH.
        * rewrite proc_status_of_trace_snoc_lin lookup_insert_ne //.
          by apply IH.
        * rewrite proc_status_of_trace_snoc_ret. by apply IH.
  Qed.

  (** Snoc analysis for per_tag_linearized via length + position. *)

  Lemma per_tag_linearized_snoc_call_inv ts τ n v :
    per_tag_linearized (ts ++ [(τ, Call n v)]) →
    filter (λ t, t.1 = τ) ts = [].
  Proof.
    intros Hpt.
    destruct (Hpt τ) as (i & v_x & v_y & Hprefix).
    rewrite filter_app filter_cons_True // filter_nil /= in Hprefix.
    pose proof (prefix_length _ _ Hprefix) as Hlen.
    rewrite length_app /= in Hlen.
    remember (filter (λ t, t.1 = τ) ts) as l eqn:Hl. clear Hl.
    destruct l as [|h1 [|h2 [|h3 ft']]]; simpl in Hlen; [done | | | exfalso; lia ].
    - exfalso. destruct Hprefix as [k Hk]. simpl in Hk.
      apply (f_equal (lookup 1)) in Hk. simpl in Hk. inversion Hk.
    - exfalso. destruct Hprefix as [k Hk]. simpl in Hk.
      apply (f_equal (lookup 2)) in Hk. simpl in Hk. inversion Hk.
  Qed.

  Lemma per_tag_linearized_snoc_lin_inv ts τ n v v' :
    per_tag_linearized (ts ++ [(τ, Lin n v v')]) →
    filter (λ t, t.1 = τ) ts = [(τ, Call n v)].
  Proof.
    intros Hpt.
    destruct (Hpt τ) as (i & v_x & v_y & Hprefix).
    rewrite filter_app filter_cons_True // filter_nil /= in Hprefix.
    pose proof (prefix_length _ _ Hprefix) as Hlen.
    rewrite length_app /= in Hlen.
    remember (filter (λ t, t.1 = τ) ts) as l eqn:Hl. clear Hl.
    destruct l as [|h1 [|h2 [|h3 ft']]]; simpl in Hlen; [ | | | exfalso; lia ].
    - exfalso. destruct Hprefix as [k Hk]. simpl in Hk.
      apply (f_equal (lookup 0)) in Hk. simpl in Hk. inversion Hk.
    - destruct Hprefix as [k Hk]. simpl in Hk.
      apply (f_equal (lookup 0)) in Hk as Hk0. simpl in Hk0.
      apply (f_equal (lookup 1)) in Hk as Hk1. simpl in Hk1.
      injection Hk0 as <-. injection Hk1 as <- <-. done.
    - exfalso. destruct Hprefix as [k Hk]. simpl in Hk.
      apply (f_equal (lookup 2)) in Hk. simpl in Hk. inversion Hk.
  Qed.

  Lemma per_tag_linearized_snoc_ret_inv ts τ v' :
    per_tag_linearized (ts ++ [(τ, Ret v')]) →
    ∃ n v, filter (λ t, t.1 = τ) ts = [(τ, Call n v); (τ, Lin n v v')].
  Proof.
    intros Hpt.
    destruct (Hpt τ) as (n & v_x & v_y & Hprefix).
    rewrite filter_app filter_cons_True // filter_nil /= in Hprefix.
    pose proof (prefix_length _ _ Hprefix) as Hlen.
    rewrite length_app /= in Hlen.
    remember (filter (λ t, t.1 = τ) ts) as l eqn:Hl. clear Hl.
    destruct l as [|h1 [|h2 [|h3 ft']]]; simpl in Hlen; [ | | | exfalso; lia ].
    - exfalso. destruct Hprefix as [k Hk]. simpl in Hk.
      apply (f_equal (lookup 0)) in Hk. simpl in Hk. inversion Hk.
    - exfalso. destruct Hprefix as [k Hk]. simpl in Hk.
      apply (f_equal (lookup 1)) in Hk. simpl in Hk. inversion Hk.
    - destruct Hprefix as [k Hk]. simpl in Hk.
      apply (f_equal (lookup 0)) in Hk as Hk0. simpl in Hk0.
      apply (f_equal (lookup 1)) in Hk as Hk1. simpl in Hk1.
      apply (f_equal (lookup 2)) in Hk as Hk2. simpl in Hk2.
      injection Hk0 as <-. injection Hk1 as <-. injection Hk2 as <-.
      eauto.
  Qed.

  (** Helper: proc_status_of_trace is unchanged on τ over a τ-free suffix. *)
  Lemma proc_status_of_trace_no_τ_app ts1 ts2 τ :
    filter (λ t, t.1 = τ) ts2 = [] →
    proc_status_of_trace (ts1 ++ ts2) !! τ = proc_status_of_trace ts1 !! τ.
  Proof.
    induction ts2 as [|t ts2 IH] using rev_ind; intros Hfilter.
    - by rewrite app_nil_r.
    - rewrite filter_app in Hfilter.
      apply app_nil in Hfilter as [Hpre Hsnoc].
      destruct t as [τ' tr].
      destruct (decide (τ' = τ)) as [-> | Hne].
      + rewrite filter_cons_True // filter_nil in Hsnoc.
      + rewrite assoc_L.
        destruct tr as [v|v v'|v'].
        * rewrite proc_status_of_trace_snoc_call lookup_insert_ne //. by apply IH.
        * rewrite proc_status_of_trace_snoc_lin lookup_insert_ne //. by apply IH.
        * rewrite proc_status_of_trace_snoc_ret. by apply IH.
  Qed.

  (** After a (τ, Call n v) event with no later τ events,
    proc_status_of_trace[τ] = Some (n, v, None). *)
  Lemma proc_status_of_trace_lookup_pending ts τ n v :
    filter (λ t, t.1 = τ) ts = [(τ, Call n v)] →
    proc_status_of_trace ts !! τ = Some (n, v, None).
  Proof.
    induction ts as [|t ts IH] using rev_ind; intros Hfilter.
    - simpl in Hfilter. discriminate.
    - rewrite filter_app in Hfilter.
      destruct t as [τ' tr].
      destruct (decide (τ' = τ)) as [-> | Hne].
      + rewrite filter_cons_True // filter_nil /= in Hfilter.
        destruct (filter (λ t, t.1 = τ) ts) as [|h ft] eqn:Hf_ts.
        * simpl in Hfilter.
          assert (tr = Call n v) as -> by (inversion Hfilter; reflexivity).
          rewrite proc_status_of_trace_snoc_call.
          rewrite lookup_insert_eq.
          reflexivity.
        * exfalso. apply (f_equal length) in Hfilter.
          simpl in Hfilter. rewrite length_app /= in Hfilter. lia.
      + rewrite filter_cons_False in Hfilter; last by intros [=].
        rewrite filter_nil app_nil_r in Hfilter.
        destruct tr as [v_t|v_t v_t'|v_t'].
        * rewrite proc_status_of_trace_snoc_call lookup_insert_ne; last done.
          by apply IH.
        * rewrite proc_status_of_trace_snoc_lin lookup_insert_ne; last done.
          by apply IH.
        * rewrite proc_status_of_trace_snoc_ret. by apply IH.
  Qed.

  (** After Call+Lin events with no later τ events,
    proc_status_of_trace[τ] = Some (n, v, Some v'). *)
  Lemma proc_status_of_trace_lookup_linearized ts τ n v v' :
    filter (λ t, t.1 = τ) ts = [(τ, Call n v); (τ, Lin n v v')] →
    proc_status_of_trace ts !! τ = Some (n, v, Some v').
  Proof.
    induction ts as [|t ts IH] using rev_ind; intros Hfilter.
    - simpl in Hfilter. discriminate.
    - rewrite filter_app in Hfilter.
      destruct t as [τ' tr].
      destruct (decide (τ' = τ)) as [-> | Hne].
      + rewrite filter_cons_True // filter_nil /= in Hfilter.
        (* filter τ ts ++ [(τ, tr)] = [(τ, Call n v); (τ, Lin n v v')] *)
        destruct (filter (λ t, t.1 = τ) ts) as [|h [|h2 ft]] eqn:Hf_ts.
        * (* filter ts = [], so [(τ, tr)] = 2-element list. Length mismatch. *)
          exfalso. apply (f_equal length) in Hfilter. simpl in Hfilter. lia.
        * (* filter ts = [h], so [h; (τ, tr)] = [(τ, Call n v); (τ, Lin n v v')]. tr = Lin n v v'. *)
          simpl in Hfilter.
          assert (tr = Lin n v v') as -> by (inversion Hfilter; reflexivity).
          rewrite proc_status_of_trace_snoc_lin.
          rewrite lookup_insert_eq.
          reflexivity.
        * (* filter ts has ≥ 2 elements, plus snoc, ≥ 3. Length mismatch. *)
          exfalso. apply (f_equal length) in Hfilter.
          simpl in Hfilter. rewrite length_app /= in Hfilter. lia.
      + rewrite filter_cons_False in Hfilter; last by intros [=].
        rewrite filter_nil app_nil_r in Hfilter.
        destruct tr as [v_t|v_t v_t'|v_t'].
        * rewrite proc_status_of_trace_snoc_call lookup_insert_ne; last done.
          by apply IH.
        * rewrite proc_status_of_trace_snoc_lin lookup_insert_ne; last done.
          by apply IH.
        * rewrite proc_status_of_trace_snoc_ret. by apply IH.
  Qed.

  (** Single-step domain preservation: if M0's configs have dom ⊆
      list_to_set ts0_tags (the tags already in the trace prefix), then
      M1's configs (post-step) have dom ⊆ list_to_set (ts0_tags ++ ts1.*1). *)
  Lemma mcfg_step_dom_preserved M0 M1 (ts0_tags : list positive)
                                 (ts1 : list (positive * trace)) s π :
    mcfg_step M0 M1 ts1 →
    (∀ s' π', (s', π') ∈ M0 → dom π' ⊆ list_to_set ts0_tags) →
    (s, π) ∈ M1 →
    dom π ⊆ list_to_set (ts0_tags ++ ts1.*1).
  Proof.
    intros Hstep Hpre Hin.
    inversion Hstep as
      [M' τ v Hf Hvr Heq1 Heq2 Heq3
      | M' s_a π_a τ n v s_b v' Hin_a Hπ_a Hrr Heq1 Heq2 Heq3
      | M' τ v' Heq1 Heq2 Heq3]; subst.
    - (* Call *)
      apply elem_of_PropSet in Hin as ([s_x π_x] & Heq & Hin_old).
      simpl in Heq. injection Heq as -> ->.
      rewrite dom_insert_L. rewrite list_to_set_app_L.
      pose proof (Hpre _ _ Hin_old) as Hdom_pre. simpl. set_solver.
    - (* Interm *)
      apply elem_of_union in Hin as [Hin_new | Hin_old].
      + apply elem_of_singleton in Hin_new. injection Hin_new as -> ->.
        rewrite dom_insert_L. simpl. rewrite app_nil_r.
        pose proof (Hpre _ _ Hin_a) as Hdom_pre.
        apply elem_of_dom_2 in Hπ_a. set_solver.
      + simpl. rewrite app_nil_r. by eapply Hpre.
    - (* Ret *)
      apply elem_of_intersection in Hin as [Hin_old _].
      simpl. rewrite list_to_set_app_L. simpl.
      pose proof (Hpre _ _ Hin_old). set_solver.
  Qed.

  (** Multi-step domain preservation. *)
  Lemma mcfg_steps_dom_in_trace M_init M_final
                                 (ts_init_tags : list positive)
                                 (ts_run : list (positive * trace)) :
    mcfg_steps M_init M_final ts_run →
    (∀ s' π', (s', π') ∈ M_init → dom π' ⊆ list_to_set ts_init_tags) →
    ∀ s π, (s, π) ∈ M_final →
      dom π ⊆ list_to_set (ts_init_tags ++ ts_run.*1).
  Proof.
    intros Hsteps. revert ts_init_tags.
    induction Hsteps as [M_x | M0 M1 ts_a M2 ts_b Hstep Hsteps IH];
      intros ts_init_tags Hpre s π Hin.
    - rewrite fmap_nil app_nil_r. by eapply Hpre.
    - rewrite fmap_app app_assoc.
      eapply (IH (ts_init_tags ++ ts_a.*1)).
      + intros s' π' Hin'.
        eapply mcfg_step_dom_preserved; [exact Hstep | exact Hpre | exact Hin'].
      + exact Hin.
  Qed.

  (** Specialized form: from mcfg_init, dom is bounded by trace tags. *)
  Lemma mcfg_steps_dom_init M_f ts s π :
    mcfg_steps mcfg_init M_f ts → (s, π) ∈ M_f →
    dom π ⊆ list_to_set ts.*1.
  Proof.
    intros Hsteps Hin.
    pose proof (mcfg_steps_dom_in_trace mcfg_init M_f ([] : list positive) ts Hsteps) as Hdom.
    rewrite app_nil_l in Hdom.
    eapply Hdom; last exact Hin.
    intros s' π' Hin'. rewrite /mcfg_init in Hin'.
    apply elem_of_singleton in Hin'.
    injection Hin' as -> ->. rewrite dom_empty_L. set_solver.
  Qed.

  (** ============================================================== *)
  (** (⟸) direction: trace_linearizable → I_metaconfig.
      Construct mcfg_steps by walking through the linearization witness ts',
      maintaining an mcfg that CONTAINS the canonical config. Under the
      branching [mcfg_step_interm], the mcfg can grow as more Lin events
      occur; we only need to keep the canonical (s, π) somewhere in it. *)

  Lemma trace_linearizable_witness ts' s :
    call_valid (filter (not ∘ is_lin ∘ snd) ts') →
    per_tag_linearized ts' →
    linearized_sound (filter (is_lin ∘ snd) ts') s_init s →
    ∃ M, mcfg_steps mcfg_init M (filter (not ∘ is_lin ∘ snd) ts') ∧
         (s, proc_status_of_trace ts') ∈ M.
  Proof.
    revert s.
    induction ts' as [|t ts' IH] using rev_ind; intros s Hcv Hpt Hls.
    - rewrite filter_nil proc_status_of_trace_nil.
      rewrite filter_nil in Hls.
      apply linearized_sound_nil_inv in Hls as <-.
      exists ({[ (s_init, ∅ : gmap positive proc_status) ]}).
      split; first apply mcfg_steps_nil.
      apply elem_of_singleton. reflexivity.
    - destruct t as [τ tr].
      destruct tr as [n v|n v v'|v'].
      + (* (τ, Call n v) event *)
        rewrite filter_app filter_cons_True in Hcv; last by intros [].
        rewrite filter_nil in Hcv.
        rewrite filter_app filter_cons_False in Hls; last by intros [].
        rewrite filter_nil app_nil_r in Hls.
        unfold call_valid in Hcv.
        rewrite Forall_app Forall_singleton /= in Hcv.
        destruct Hcv as [Hcv_pre Hvr].
        assert (Hpt_pre : per_tag_linearized ts')
          by (by eapply per_tag_linearized_snoc).
        assert (Hτ_fresh : filter (λ t, t.1 = τ) ts' = [])
          by (by eapply per_tag_linearized_snoc_call_inv).
        destruct (IH s Hcv_pre Hpt_pre Hls) as (M_pre & Hsteps_pre & Hin_pre).
        rewrite filter_app filter_cons_True; last by intros [].
        rewrite filter_nil.
        exists ((λ '(s_x, π_x), (s_x, <[τ:=(n, v, None)]> π_x)) <$> M_pre).
        split.
        * eapply mcfg_steps_snoc; first exact Hsteps_pre.
          apply (mcfg_step_call _ τ n v); last done.
          (* dom-fresh: every config in M_pre has τ ∉ dom π. Follows
             from [filter (λ t, t.1 = τ) ts' = []] and the domain bound. *)
          intros [s_x π_x] Hin_x.
          pose proof (mcfg_steps_dom_init _ _ s_x π_x Hsteps_pre Hin_x) as Hdom.
          rewrite not_elem_of_dom.
          destruct (π_x !! τ) as [vv|] eqn:Hτ; last reflexivity.
          exfalso. apply elem_of_dom_2 in Hτ.
          apply Hdom in Hτ. apply elem_of_list_to_set in Hτ.
          apply list_elem_of_fmap in Hτ as ([τ_y t] & Heq & Hin_y).
          simpl in Heq. subst τ_y.
          apply list_elem_of_filter in Hin_y as [Hnot_lin Hin_ts'].
          assert (Hin_τ : (τ, t) ∈ filter (λ t, t.1 = τ) ts').
          { apply list_elem_of_filter. split; first reflexivity. exact Hin_ts'. }
          rewrite Hτ_fresh in Hin_τ. apply elem_of_nil in Hin_τ. exact Hin_τ.
        * rewrite proc_status_of_trace_snoc_call.
          apply elem_of_PropSet. exists (s, proc_status_of_trace ts').
          split; first reflexivity. exact Hin_pre.
      + (* (τ, Lin n v v') event *)
        rewrite filter_app filter_cons_False in Hcv;
          last by intros HLin; apply HLin; done.
        rewrite filter_nil app_nil_r in Hcv.
        rewrite filter_app filter_cons_True in Hls; last done.
        rewrite filter_nil in Hls.
        apply linearized_sound_snoc_inv in Hls as (s_mid & Hls_pre & Hvr & Hrr).
        assert (Hpt_pre : per_tag_linearized ts')
          by (by eapply per_tag_linearized_snoc).
        assert (Hτ_call : filter (λ t, t.1 = τ) ts' = [(τ, Call n v)])
          by (by eapply per_tag_linearized_snoc_lin_inv).
        destruct (IH s_mid Hcv Hpt_pre Hls_pre) as (M_pre & Hsteps_pre & Hin_pre).
        rewrite filter_app filter_cons_False;
          last by intros HLin; apply HLin; done.
        rewrite filter_nil app_nil_r.
        replace (filter (not ∘ is_lin ∘ snd) ts')
          with ((filter (not ∘ is_lin ∘ snd) ts') ++ ([] : list (positive*trace)))
          by apply app_nil_r.
        exists ({[ (s, <[τ:=(n, v, Some v')]> (proc_status_of_trace ts')) ]} ∪ M_pre).
        split.
        * eapply mcfg_steps_snoc; first exact Hsteps_pre.
          apply (mcfg_step_interm _ s_mid (proc_status_of_trace ts') τ n v s v').
          -- exact Hin_pre.
          -- by apply proc_status_of_trace_lookup_pending.
          -- done.
        * rewrite proc_status_of_trace_snoc_lin.
          apply elem_of_union. left. apply elem_of_singleton. reflexivity.
      + (* (τ, Ret v') event *)
        rewrite filter_app filter_cons_True in Hcv; last by intros [].
        rewrite filter_nil in Hcv.
        unfold call_valid in Hcv. rewrite Forall_app Forall_singleton /= in Hcv.
        destruct Hcv as [Hcv_pre _].
        rewrite filter_app filter_cons_False in Hls; last by intros [].
        rewrite filter_nil app_nil_r in Hls.
        assert (Hpt_pre : per_tag_linearized ts')
          by (by eapply per_tag_linearized_snoc).
        destruct (per_tag_linearized_snoc_ret_inv _ _ _ Hpt) as (n_call & v_call & Hf_τ).
        assert (Hcanon : proc_status_of_trace ts' !! τ = Some (n_call, v_call, Some v'))
          by (by apply proc_status_of_trace_lookup_linearized).
        destruct (IH s Hcv_pre Hpt_pre Hls) as (M_pre & Hsteps_pre & Hin_pre).
        rewrite filter_app filter_cons_True; last by intros [].
        rewrite filter_nil.
        exists (M_pre ∩ {[ (_, π) | snd <$> (π !! τ) = Some (Some v') ]}).
        split.
        * eapply mcfg_steps_snoc; first exact Hsteps_pre.
          apply (mcfg_step_ret _ τ v').
        * rewrite proc_status_of_trace_snoc_ret.
          apply elem_of_intersection. split; first exact Hin_pre.
          apply elem_of_PropSet. rewrite Hcanon /=. reflexivity.
  Qed.

  (** Main (⟸): trace_linearizable → I_metaconfig (and per_tag_wellformed). *)
  Theorem metaconfig_tracking_complete ts :
    trace_linearizable ts → I_metaconfig ts.
  Proof.
    intros [Hcv (ts' & -> & Hpt & s & Hls)].
    destruct (trace_linearizable_witness ts' s Hcv Hpt Hls)
      as (M_final & Hsteps & Hin).
    exists M_final, s, (proc_status_of_trace ts'). split; assumption.
  Qed.

  (** ============================================================== *)
  (** (⟹) direction: I_metaconfig ∧ per_tag_wellformed → trace_linearizable.
      Use a has_witness invariant: every config in any reachable mcfg
      corresponds to some linearization witness ts'. *)

  (** Consistency between a gmap π and a witness ts': each τ's status in π
      reflects τ's events in ts'. *)
  Definition config_consistent (π : gmap positive proc_status)
                                (ts' : list (positive*trace)) : Prop :=
    ∀ τ, match π !! τ with
         | None => filter (λ t, t.1 = τ) ts' = []
         | Some (n, v, None) => filter (λ t, t.1 = τ) ts' = [(τ, Call n v)]
         | Some (n, v, Some v') =>
             filter (λ t, t.1 = τ) ts' = [(τ, Call n v); (τ, Lin n v v')]
           ∨ filter (λ t, t.1 = τ) ts' = [(τ, Call n v); (τ, Lin n v v'); (τ, Ret v')]
         end.

  (** Every config in mcfg has a witness ts'. *)
  Definition has_witness (mcfg : meta_config) (ts : list (positive*trace)) : Prop :=
    ∀ s π, (s, π) ∈ mcfg → ∃ ts',
        ts = filter (not ∘ is_lin ∘ snd) ts'
      ∧ call_valid ts
      ∧ per_tag_linearized ts'
      ∧ linearized_sound (filter (is_lin ∘ snd) ts') s_init s
      ∧ config_consistent π ts'.

  (** Per-tag wellformed is preserved under prefixes. *)
  Lemma per_tag_wellformed_prefix_app ts1 ts2 :
    per_tag_wellformed (ts1 ++ ts2) → per_tag_wellformed ts1.
  Proof.
    intros H τ.
    destruct (H τ) as (n & v & v' & Hprefix).
    exists n, v, v'.
    rewrite filter_app in Hprefix.
    by apply prefix_app_l in Hprefix.
  Qed.

  Lemma has_witness_init : has_witness mcfg_init [].
  Proof.
    intros s π Hin.
    rewrite /mcfg_init in Hin.
    apply elem_of_singleton in Hin.
    injection Hin as -> ->.
    exists []. split_and!.
    - rewrite filter_nil //.
    - rewrite /call_valid //.
    - apply per_tag_linearized_nil.
    - rewrite filter_nil. apply linearized_sound_nil.
    - intros τ. rewrite lookup_empty. by rewrite filter_nil.
  Qed.

  (** Preservation of has_witness under mcfg_step_call. *)
  Lemma has_witness_step_call mcfg ts τ n v :
    has_witness mcfg ts →
    set_Forall (λ '(_, π), τ ∉ dom π) mcfg →
    default default_vr (valid_requests!!n) v →
    has_witness ((λ '(s, π), (s, <[τ:=(n, v, None)]> π)) <$> mcfg) (ts ++ [(τ, Call n v)]).
  Proof.
    intros HW Hfresh Hvr s π_new Hin.
    apply elem_of_PropSet in Hin as (a & Heq & Hain).
    destruct a as [s' π']. simpl in Heq. injection Heq as -> ->.
    pose proof (Hfresh _ Hain) as Hτfresh.
    destruct (HW s' π' Hain) as (ts'_old & Heq_ts & Hcv & Hpt & Hls & Hcc).
    exists (ts'_old ++ [(τ, Call n v)]). split_and!.
    - rewrite filter_app filter_cons_True; last by intros [].
      rewrite filter_nil. rewrite -Heq_ts //.
    - rewrite /call_valid Forall_app. split.
      + done.
      + by repeat constructor.
    - intros τ_x. destruct (Hpt τ_x) as (i & v_x & v_y & Hprefix).
      rewrite filter_app filter_cons. case_decide as Heq.
      + simpl in Heq. subst τ_x.
        pose proof (Hcc τ) as Hcc_τ.
        rewrite not_elem_of_dom in Hτfresh.
        rewrite Hτfresh in Hcc_τ. simpl in Hcc_τ.
        rewrite Hcc_τ. exists n, v, v.
        rewrite filter_nil /=. apply prefix_cons. apply prefix_nil.
      + exists i, v_x, v_y. by rewrite filter_nil app_nil_r.
    - rewrite filter_app filter_cons_False; last by intros [].
      by rewrite filter_nil app_nil_r.
    - intros τ_x. destruct (decide (τ = τ_x)) as [-> | Hne].
      + rewrite lookup_insert_eq.
        rewrite not_elem_of_dom in Hτfresh.
        rewrite filter_app filter_cons. case_decide as Hd.
        * rewrite filter_nil /=.
          pose proof (Hcc τ_x) as Hcc_τ.
          rewrite Hτfresh in Hcc_τ. by rewrite Hcc_τ.
        * exfalso. apply Hd. reflexivity.
      + rewrite lookup_insert_ne; last (intros ?; apply Hne; congruence).
        rewrite filter_app filter_cons. case_decide as Hd.
        * exfalso. simpl in Hd. by apply Hne.
        * rewrite filter_nil app_nil_r.
          apply (Hcc τ_x).
  Qed.

  (** A (τ, Call n v) event in a trace ts with call_valid ts gives that v
    satisfies operation n's request predicate. *)
  Lemma call_valid_elem_of ts τ n v :
    call_valid ts →
    (τ, Call n v) ∈ ts →
    default default_vr (valid_requests!!n) v.
  Proof.
    intros Hcv Hin.
    rewrite /call_valid Forall_forall in Hcv.
    by apply (Hcv (τ, Call n v) Hin).
  Qed.

  (** If filter P l = [x], then x ∈ l. *)
  Lemma filter_eq_singleton_elem_of {A} (P : A → Prop) `{!∀ x, Decision (P x)} (x : A) l :
    filter P l = [x] → x ∈ l.
  Proof.
    intros Hfilter.
    assert (x ∈ filter P l) as Hin by (rewrite Hfilter; apply list_elem_of_singleton; reflexivity).
    apply list_elem_of_filter in Hin as [_ Hin].
    exact Hin.
  Qed.

  (** Preservation under mcfg_step_interm: trace unchanged. The new
      linearized config is added alongside the original. *)
  Lemma has_witness_step_interm mcfg s π τ n v s' v' ts :
    has_witness mcfg ts →
    (s, π) ∈ mcfg →
    π !! τ = Some (n, v, None) →
    default default_rr (request_responses!!n) s v s' v' →
    has_witness ({[ (s', <[τ:=(n, v, Some v')]> π) ]} ∪ mcfg) ts.
  Proof.
    intros HW Hsπ Hπτ Hrr s_x π_x Hin.
    apply elem_of_union in Hin as [Hin | Hin].
    - (* (s_x, π_x) is the newly linearized config. *)
      apply elem_of_singleton in Hin. injection Hin as -> ->.
      destruct (HW _ _ Hsπ) as (ts'_old & Heq_ts & Hcv & Hpt & Hls & Hcc).
      (* Extract that (τ, Call n v) ∈ ts, hence v is a valid request for n. *)
      pose proof (Hcc τ) as Hcc_τ. rewrite Hπτ in Hcc_τ. simpl in Hcc_τ.
      assert (Hvr : default default_vr (valid_requests!!n) v).
      { eapply call_valid_elem_of; first exact Hcv.
        rewrite Heq_ts. apply list_elem_of_filter. split; first by intros [].
        apply (filter_eq_singleton_elem_of _ _ _ Hcc_τ). }
      exists (ts'_old ++ [(τ, Lin n v v')]). split_and!.
      + rewrite filter_app filter_cons_False;
          last by intros HLin; apply HLin; done.
        rewrite filter_nil app_nil_r. exact Heq_ts.
      + exact Hcv.
      + intros τ_x.
        destruct (Hpt τ_x) as (v_a & v_b & Hprefix).
        destruct (decide (τ = τ_x)) as [-> | Hne].
        * rewrite filter_app filter_cons. case_decide as Hd; last by exfalso.
          rewrite filter_nil /= Hcc_τ. exists n, v, v'.
          apply prefix_cons, prefix_cons, prefix_nil.
        * rewrite filter_app filter_cons. case_decide as Hd.
          { simpl in Hd. exfalso. by apply Hne. }
          { rewrite filter_nil app_nil_r. exists v_a, v_b. exact Hprefix. }
      + rewrite filter_app filter_cons_True; last done.
        rewrite filter_nil.
        eapply linearized_sound_snoc; [exact Hls | exact Hvr | exact Hrr].
      + intros τ_x. destruct (decide (τ = τ_x)) as [-> | Hne].
        * rewrite lookup_insert_eq.
          rewrite filter_app filter_cons. case_decide as Hd; last by exfalso.
          rewrite filter_nil /= Hcc_τ. left. reflexivity.
        * rewrite lookup_insert_ne; last (intros ?; apply Hne; congruence).
          rewrite filter_app filter_cons. case_decide as Hd.
          { exfalso. simpl in Hd. by apply Hne. }
          { rewrite filter_nil app_nil_r. apply (Hcc τ_x). }
    - apply (HW _ _ Hin).
  Qed.

  (** Preservation under mcfg_step_ret: trace appends Ret event.
      Requires per_tag_wellformed on the resulting trace. *)
  Lemma has_witness_step_ret mcfg ts τ v' :
    has_witness mcfg ts →
    per_tag_wellformed (ts ++ [(τ, Ret v')]) →
    has_witness (mcfg ∩ {[ (_, π) | snd <$> (π !! τ) = Some (Some v') ]})
                (ts ++ [(τ, Ret v')]).
  Proof.
    intros HW Hpw s_x π_x Hin.
    apply elem_of_intersection in Hin as [Hin Hfilter_in].
    rewrite elem_of_PropSet in Hfilter_in.
    destruct (HW _ _ Hin) as (ts'_old & -> & Hcv & Hpt & Hls & Hcc).
    pose proof (Hcc τ) as Hcc_τ.
    destruct (π_x !! τ) as [[[n_x v_x] [v_x'|]]|] eqn:Hπτ;
      simpl in Hfilter_in; simplify_eq.
    (* π_x !! τ = Some (v_x, Some v'). Hcc_τ has filter τ ts'_old as one of two cases. *)
    assert (Hno_ret : filter (λ t, t.1 = τ) ts'_old = [(τ, Call n_x v_x); (τ, Lin n_x v_x v')]).
    { destruct Hcc_τ as [Hcc1 | Hcc2]; first exact Hcc1.
      exfalso.
      (* Hcc2: filter τ ts'_old = [Call n_x v_x; Lin n_x v_x v'; Ret v'].
         Compute filter τ (filter not_is_lin ts'_old). *)
      assert (Hfilter_double :
              filter (λ t : positive * trace, t.1 = τ)
                (filter (not ∘ is_lin ∘ snd) ts'_old) = [(τ, Call n_x v_x); (τ, Ret v')]).
      { rewrite list_filter_filter.
        transitivity (filter (λ a : positive * trace, (not ∘ is_lin ∘ snd) a ∧ a.1 = τ) ts'_old).
        { apply list_filter_iff. intros []. tauto. }
        rewrite -list_filter_filter.
        rewrite Hcc2.
        rewrite filter_cons_True; last by intros [].
        rewrite filter_cons_False; last (intros H; apply H; done).
        rewrite filter_cons_True; last by intros [].
        rewrite filter_nil. reflexivity. }
      (* Now Hpw gives prefix constraint on filter τ (ts ++ [Ret v']). *)
      destruct (Hpw τ) as (n & v_a & v_b & [k Hk]).
      rewrite filter_app filter_cons_True // filter_nil /= in Hk.
      rewrite Hfilter_double in Hk.
      (* Hk: [(τ, Call n v_a); (τ, Ret v_b)] = [(τ, Call n_x v_x); (τ, Ret v'); (τ, Ret v')] ++ k. *)
      apply (f_equal length) in Hk.
      simpl in Hk. lia.
    }
    exists (ts'_old ++ [(τ, Ret v')]). split_and!.
    - rewrite filter_app filter_cons_True; last by intros [].
      by rewrite filter_nil.
    - rewrite /call_valid Forall_app Forall_singleton /=. split; first exact Hcv.
      done.
    - intros τ_y. destruct (decide (τ = τ_y)) as [-> | Hne].
      + rewrite filter_app filter_cons. case_decide as Hd; last (exfalso; by apply Hd).
        rewrite filter_nil /= Hno_ret. exists n_x, v_x, v'.
        repeat (apply prefix_cons). apply prefix_nil.
      + rewrite filter_app filter_cons. case_decide as Hd.
        { exfalso. simpl in Hd. by apply Hne. }
        { rewrite filter_nil app_nil_r. apply (Hpt τ_y). }
    - rewrite filter_app filter_cons_False; last by intros [].
      rewrite filter_nil app_nil_r. exact Hls.
    - intros τ_y. destruct (decide (τ = τ_y)) as [-> | Hne].
      + rewrite Hπτ filter_app filter_cons. case_decide as Hd; last (exfalso; by apply Hd).
        rewrite filter_nil /= Hno_ret. right. reflexivity.
      + rewrite filter_app filter_cons. case_decide as Hd.
        { exfalso. simpl in Hd. by apply Hne. }
        { rewrite filter_nil app_nil_r. apply (Hcc τ_y). }
  Qed.

  (** Generalized preservation under mcfg_steps. *)
  Lemma has_witness_steps mcfg_pre mcfg ts_pre ts_step :
    has_witness mcfg_pre ts_pre →
    mcfg_steps mcfg_pre mcfg ts_step →
    per_tag_wellformed (ts_pre ++ ts_step) →
    has_witness mcfg (ts_pre ++ ts_step).
  Proof.
    intros HW Hsteps.
    revert ts_pre HW.
    induction Hsteps as [mcfg | mcfg0 mcfg1 ts1 mcfg2 ts2 Hstep _ IH];
      intros ts_pre HW Hpw.
    - rewrite right_id_L. exact HW.
    - rewrite app_assoc in Hpw |- *.
      apply IH; last exact Hpw.
      pose proof (per_tag_wellformed_prefix_app _ _ Hpw) as Hpw_pre.
      inversion Hstep; subst.
      + apply has_witness_step_call; assumption.
      + rewrite app_nil_r. by eapply has_witness_step_interm.
      + by apply has_witness_step_ret.
  Qed.

  Theorem metaconfig_tracking_sound ts :
    I_metaconfig ts ∧ per_tag_wellformed ts → trace_linearizable ts.
  Proof.
    intros [(mcfg' & s & π & Hsteps & Hin) Hpw].
    pose proof has_witness_init as HW_init.
    pose proof (has_witness_steps mcfg_init mcfg' [] ts HW_init Hsteps) as HW.
    rewrite app_nil_l in HW. specialize (HW Hpw).
    destruct (HW _ _ Hin) as (ts' & Heq_ts & Hcv & Hpt & Hls & _).
    split; first exact Hcv.
    exists ts'. split_and!; [exact Heq_ts | exact Hpt | exists s; exact Hls].
  Qed.
End lemmas.

(* === Main theorem === *)

Theorem metaconfig_tracking_iff_linearizable `{M : model} ts :
  I_metaconfig ts ∧ per_tag_wellformed ts ↔ trace_linearizable ts.
Proof.
  split.
  - apply metaconfig_tracking_sound.
  - intros Hlin. split.
    + by apply metaconfig_tracking_complete.
    + by apply trace_linearizable_per_tag_wellformed.
Qed.
