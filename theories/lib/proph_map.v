From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic Require Export proph_map.

Local Existing Instances proph_map_inG proph_map_GpreS_inG.

Lemma proph_map_init_strong `{Countable P, !proph_mapGpreS P V Σ} pvs ps :
  ⊢ |==> ∃ _ : proph_mapGS P V Σ, proph_map_interp pvs ps ∗
    [∗ set] p ∈ ps, proph p (proph_list_resolves pvs p).
Proof.
  set (R := list_to_map ((λ p, (p,proph_list_resolves pvs p)) <$> elements ps) : gmap P (list V)).
  iMod (ghost_map_alloc R) as (γ) "[Hh Hps]".
  iModIntro. iExists (ProphMapGS P V _ _ _ _ γ).
  iSplitL "Hh".
  - iExists R. iSplit; last iFrame.
    iPureIntro. subst R. split.
    + intros p vs (p' & Heq & _)%elem_of_list_to_map_2%list_elem_of_fmap_1.
      by simplify_eq.
    + rewrite dom_list_to_map_L -list_fmap_compose.
      rewrite (list_fmap_ext _ id) // list_fmap_id.
      rewrite list_to_set_elements_L.
      done.
  - subst R. rewrite proph_map.proph_unseal /proph_map.proph_def /=.
    rewrite big_sepM_list_to_map; last first.
    { rewrite -list_fmap_compose (list_fmap_ext _ id) // list_fmap_id.
      apply NoDup_elements. }
    rewrite big_sepL_fmap -big_sepS_elements //.
Qed.
