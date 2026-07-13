From iris.proofmode Require Import base proofmode classes.

From case_studies.hw_queue Require aspect.
From case_studies.hw_queue.refine Require chain.
From case_studies.hw_queue.metaconfig Require chain.
From case_studies.baskets_queue.refine Require chain.
From case_studies.folly_queue Require mpmc_linearizable.

Set Printing Width 65536.

Check "### Herlihy-Wing Queue ###".
Check "aspect.new_queue_spec".
Print Assumptions case_studies.hw_queue.aspect.new_queue_spec.
Check "aspect.enqueue_spec".
Print Assumptions case_studies.hw_queue.aspect.enqueue_spec.
Check "aspect.dequeue_spec".
Print Assumptions case_studies.hw_queue.aspect.dequeue_spec.

Check "refine.chain.new_queue_spec".
Print Assumptions case_studies.hw_queue.refine.chain.new_queue_spec.
Check "refine.chain.enqueue_spec".
Print Assumptions case_studies.hw_queue.refine.chain.enqueue_spec.
Check "refine.chain.dequeue_spec".
Print Assumptions case_studies.hw_queue.refine.chain.dequeue_spec.

Check "metaconfig.chain.new_queue_spec".
Print Assumptions case_studies.hw_queue.metaconfig.chain.new_queue_spec.
Check "metaconfig.chain.enqueue_spec".
Print Assumptions case_studies.hw_queue.metaconfig.chain.enqueue_spec.
Check "metaconfig.chain.dequeue_spec".
Print Assumptions case_studies.hw_queue.metaconfig.chain.dequeue_spec.

Check "### Baskets Queue ###".
Check "refine.chain.new_queue_spec".
Print Assumptions case_studies.baskets_queue.refine.chain.new_queue_spec.
Check "refine.chain.enqueue_spec".
Print Assumptions case_studies.baskets_queue.refine.chain.enqueue_spec.
Check "refine.chain.dequeue_spec".
Print Assumptions case_studies.baskets_queue.refine.chain.dequeue_spec.

Check "### Folly Queue ###".
Check "mpmc_linearizable.MPMC_init_spec".
Print Assumptions case_studies.folly_queue.mpmc_linearizable.MPMC_init_spec.
Check "mpmc_linearizable.MPMC_enqueue_spec".
Print Assumptions case_studies.folly_queue.mpmc_linearizable.MPMC_enqueue_spec.
Check "mpmc_linearizable.MPMC_dequeue_spec".
Print Assumptions case_studies.folly_queue.mpmc_linearizable.MPMC_dequeue_spec.
