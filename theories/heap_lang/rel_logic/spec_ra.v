(** A resource algebra for the specification programs. *)
From iris.algebra Require Import auth excl gmap gset agree list frac.
From iris.bi Require Export fractional.
From iris.base_logic Require Export ghost_map invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang adequacy primitive_laws.
Import uPred.

Definition relocN := nroot .@ "reloc".
Definition specN := relocN .@ "spec".

Definition prophUR (P : Type) `{Countable P} : ucmra :=
  gsetUR P.

(** The CMRA for the thread pool. *)
Class cfgGS Σ := CFGGS {
  #[local] tpoolG :: ghost_mapG Σ nat expr;
  #[local] heapG  :: ghost_mapG Σ loc (option val);
  #[local] proph_inG  :: inG Σ (authUR (prophUR proph_id));
  tpool_name : gname;
  heap_name : gname;
  proph_name : gname;
}.

(* TODO: rename relocGS -> relocGSS *)
Class relocGS Σ := RelocGS {
  relocGS_heapGS :: heapGS Σ;
  relocGS_cfgGS :: cfgGS Σ;
}.

Class relocPreG Σ := RelocPreG {
  reloc_preG_heap :: heapGpreS Σ;
  reloc_preG_cfgGS_tpool :: ghost_mapG Σ nat expr;
  reloc_preG_cfgGS_heap :: ghost_mapG Σ loc (option val);
  reloc_preG_cfgGS_proph  :: inG Σ (authUR (prophUR proph_id))
}.


Definition relocΣ : gFunctors :=
  #[heapΣ;
    ghost_mapΣ nat expr;
    ghost_mapΣ loc (option val);
    GFunctor (authUR (prophUR proph_id))].

Global Instance subG_relocPreG {Σ} : subG relocΣ Σ → relocPreG Σ.
Proof. solve_inG. Qed.

Section definitionsS.
  Context `{cfgGS Σ, invGS Σ}.

  Definition heapS_auth (σ : state) : iProp Σ := ghost_map_auth heap_name 1 σ.(heap).
  Definition heapS_pointsto (l : loc) (q : dfrac) (v: val) : iProp Σ := ghost_map_elem heap_name l q (Some v).

  Definition tpool_auth (tp : list expr) : iProp Σ := ghost_map_auth tpool_name 1 (map_seq 0 tp).
  Definition tpool_pointsto (j : nat) (e: expr) : iProp Σ := ghost_map_elem tpool_name j (DfracOwn 1) e.

  Definition prophS_auth (σ : state) : iProp Σ := own proph_name (● σ.(used_proph_id)).
  Definition prophS (p : proph_id) : iProp Σ := own proph_name (◯ {[ p  ]}).

  Definition spec_inv ρ : iProp Σ :=
    (∃ tp σ, tpool_auth tp ∗ heapS_auth σ ∗ prophS_auth σ ∗ ⌜rtc erased_step ρ (tp,σ)⌝)%I.
  Definition spec_ctx : iProp Σ :=
    (∃ ρ, inv specN (spec_inv ρ))%I.

  Global Instance heapS_pointsto_timeless l q v : Timeless (heapS_pointsto l q v).
  Proof. apply _. Qed.
  Global Instance heapS_proph_timeless p : Timeless (prophS p).
  Proof. apply _. Qed.
  Global Instance heapS_proph_persistent p : Persistent (prophS p).
  Proof. apply _. Qed.
  Global Instance tpool_pointsto_timeless j e: Timeless (tpool_pointsto j e).
  Proof. apply _. Qed.
  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.


  Lemma prophS_included σ p :
    prophS_auth σ -∗ prophS p -∗ ⌜p ∈ σ.(used_proph_id)⌝.
  Proof.
    iIntros "HF Hip".
    iDestruct (own_valid_2 with "HF Hip")
      as %[Hps%gset_included ?]%auth_both_valid_discrete.
    iPureIntro. set_solver.
  Qed.

  Lemma prophS_insert σ p :
    p ∉ σ.(used_proph_id) →
    prophS_auth σ ⊢ |==> prophS_auth {| heap := σ.(heap); used_proph_id := {[ p ]} ∪ σ.(used_proph_id) |} ∗ prophS p.
  Proof.
    destruct σ as [h ps] => /=.
    iIntros (Hp) "Hauth".
    iMod (own_update with "Hauth") as "[$ Hproph]".
    { apply auth_update_alloc.
      apply (gset_local_update _ _ ({[ p ]} ∪ ps)).
      set_solver. }
    iApply (own_mono with "Hproph").
    apply auth_frag_mono. eapply gset_included.
    set_solver.
  Qed.

End definitionsS.

Lemma prophS_alloc σ `{!inG Σ (authUR (prophUR proph_id))} :
  ⊢ |==> ∃ γ, own γ (● σ.(used_proph_id)).
Proof. iApply own_alloc. by apply auth_auth_valid. Qed.

Notation "l ↦ₛ dq v" := (heapS_pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ₛ dq  v") : bi_scope.
Notation "j ⤇ e" := (tpool_pointsto j e) (at level 20) : bi_scope.
