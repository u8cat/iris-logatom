From iris.heap_lang Require Import primitive_laws notation proofmode.
From iris.prelude Require Import options.

Definition NewGhostID : expr := NewProph.

Section spec.
  Context `{!heapGS Σ}.

  Definition ghost_id_token τ : iProp Σ := ∃ vs, proph τ vs.

  Lemma wp_new_token s E :
    {{{ True }}}
      NewGhostID @ s; E
    {{{ τ, RET (LitV (LitProphecy τ)); ghost_id_token τ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_new_proph with "[//]") as (vs τ) "Hτ".
    iApply "HΦ". iFrame "Hτ".
  Qed.

  Lemma ghost_id_fresh τ π :
    ghost_id_token τ -∗ ([∗ list] τ ∈ π, ghost_id_token τ) -∗ ⌜τ ∉ π⌝.
  Proof.
    iIntros "Hτ Hπ %Hin".
    apply list_elem_of_split in Hin.
    destruct Hin as (π₁ & π₂ & ->).
    rewrite big_sepL_app big_sepL_cons.
    iDestruct "Hπ" as "(_ & [% Hτ'] & _)".
    iDestruct "Hτ" as (?) "Hτ".
    iDestruct (proph_exclusive with "Hτ Hτ'") as "%".
    done.
  Qed.

  Lemma ghost_id_nodup π :
    ([∗ list] τ ∈ π, ghost_id_token τ) -∗ ⌜NoDup π⌝.
  Proof.
    iIntros "Hπ".
    iInduction π as [|τ π] "IH".
    - iPureIntro. by apply NoDup_nil.
    - rewrite big_sepL_cons.
      iDestruct "Hπ" as "[Hτ Hπ]".
      iDestruct (ghost_id_fresh with "Hτ Hπ") as %Hfresh.
      iDestruct ("IH" with "Hπ") as %Hnodup.
      iPureIntro. by apply NoDup_cons_2.
  Qed.
End spec.
