From iris.heap_lang Require Import primitive_laws.
From iris.heap_lang Require Export adequacy.

Lemma heap_inG Σ :
  heapGS Σ → heapGpreS Σ.
Proof.
  intros [Hinv Hgen_heap Hinv_heap Hproph_map ? ?]. constructor.
  - destruct Hinv as [Hwsat Hlc]. constructor.
    + apply wsat_inG.
    + constructor. apply lcGS_inG.
  - apply gen_heap_inG.
  - apply inv_heap_inG.
  - apply proph_map_inG.
  - assumption.
Qed.
