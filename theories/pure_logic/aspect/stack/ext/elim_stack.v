(* elim_stack.v, ported from elimination_stack.thy *)

From stdpp Require Import finite.
From iris_logatom.lib Require Import list.
From iris_logatom.pure_logic.aspect.stack.ext Require Import conc_his_rel.

Section elimination_stack.
  Context `{abstract_stack_model}.
  Context (pre val : relation operation).
  Context (lin : relation operation).
  Context `{!RelDecision pre, !RelDecision val, !RelDecision lin}.

  (* Assumptions of the elimination_stack locale *)
  Context (wf_history : WellformedHistory pre val).
  Context (ef_linearizable_def : SequentialStack lin (elim_free_val pre val)).
  Context (pr_in_lin : forall a b, elim_free_pre pre val a b -> lin a b).
  Context (finite_set_def : FinitePredicate (elim_free pre val)).
  Context (pre_abcd_assumption : Abcd pre).
  (* Injective function for ordering - from Isabelle's operations_countable *)
  Context (f : operation -> nat).
  Context (f_inj : forall a b, f a = f b -> a = b).

  (* elimination_stack.thy:36 *)
  (* same_val is already defined in conc_his_rel.v *)

  (* elimination_stack.thy:39-48 *)
  Lemma same_valD a b : same_val val a b -> val a b \/ val b a.
  Proof. intros [Hab|Hba]; [left|right]; done. Qed.

  Lemma same_valI1 a b : val a b -> same_val val a b.
  Proof. intros Hab. left. done. Qed.

  Lemma same_valI2 a b : val a b -> same_val val b a.
  Proof. intros Hab. right. done. Qed.

  (* elimination_stack.thy:51-55 *)
  Lemma always_same_val1 a b : pre a b -> exists c, same_val val a c.
  Proof.
    intros Hab.
    destruct (def_push_or_pop a b Hab) as [[c [Hac|Hca]] _].
    - exists c. left. done.
    - exists c. right. done.
  Qed.

  Lemma always_same_val2 a b : pre a b -> exists c, same_val val b c.
  Proof.
    intros Hab.
    destruct (def_push_or_pop a b Hab) as [_ [c [Hbc|Hcb]]].
    - exists c. left. done.
    - exists c. right. done.
  Qed.

  Lemma not_same_valD a b :
    pre a b -> ~ same_val val a b ->
    a = b \/ (exists ra rb, same_val val a ra /\ same_val val b rb /\ a <> b /\ a <> rb /\ ra <> b /\ ra <> rb).
  Proof.
    intros Hab Hnsv.
    destruct (decide (a = b)) as [Heq|Hneq].
    - left. done.
    - right.
      destruct (always_same_val1 a b Hab) as [ra Hsva].
      destruct (always_same_val2 a b Hab) as [rb Hsvb].
      exists ra, rb.
      repeat split; try done.
      + (* a <> rb *)
        intros Heq. subst rb.
        apply Hnsv. apply same_val_symmetric. done.
      + (* ra <> b *)
        intros Heq. subst ra. done.
      + (* ra <> rb *)
        intros Heq. subst rb.
        apply Hnsv.
        destruct Hsva as [Hara|Hraa]; destruct Hsvb as [Hbra|Hrab].
        * pose proof (def_push_once a b ra Hara Hbra) as Heq'. done.
        * exfalso. eapply def_val_order. exact Hara. exists b. right. done.
        * exfalso. eapply def_val_order. exact Hbra. exists a. right. done.
        * pose proof (def_pop_once ra a b Hraa Hrab) as Heq'. left. done.
  Qed.

  (* elimination_stack.thy:61-71 *)
  Lemma same_val_commutative a b : same_val val a b -> same_val val b a.
  Proof. apply same_val_symmetric. Qed.

  Lemma same_val_unique a b c :
    WellformedHistory pre val ->
    same_val val a b -> same_val val a c -> b = c.
  Proof.
    intros Hwf [Hab|Hba] [Hac|Hca].
    - (* val a b, val a c *) eapply def_pop_once; done.
    - (* val a b, val c a *) exfalso. eapply def_val_order. exact Hab. exists c. left. done.
    - (* val b a, val a c *) exfalso. eapply def_val_order. exact Hac. exists b. left. done.
    - (* val b a, val c a *) eapply def_push_once; done.
  Qed.

  (* elimination_stack.thy:73-75 - ef is elim_free from conc_his_rel *)
  (* elimination_stack.thy:77-92 *)
  Lemma efD a : elim_free pre val a -> exists b, same_val val a b /\ (pre a b \/ pre b a).
  Proof. intros (b & Hsv & Hpre). exists b. done. Qed.

  Lemma efI1 a b : same_val val a b -> pre a b -> elim_free pre val a.
  Proof. intros Hsv Hpre. exists b. split; [done|left; done]. Qed.

  Lemma efI2 a b : same_val val a b -> pre a b -> elim_free pre val b.
  Proof.
    intros Hsv Hpre.
    exists a. split.
    - apply same_val_commutative. done.
    - right. done.
  Qed.

  Lemma ef_val_then_ef a b :
    WellformedHistory pre val ->
    elim_free pre val a -> same_val val a b -> elim_free pre val b.
  Proof.
    intros Hwf Hefa Hsv.
    destruct (efD a Hefa) as [c [Hsvc Hpre]].
    pose proof (same_val_unique a c b Hwf Hsvc Hsv) as Heq. subst c.
    destruct Hpre as [Hab|Hba].
    - eapply efI2; [exact Hsv|exact Hab].
    - eapply efI1. apply same_val_commutative. exact Hsv. exact Hba.
  Qed.

  Lemma ef_then_push_or_pop a : elim_free pre val a -> is_push val a \/ is_pop val a.
  Proof. apply elim_free_push_pop. Qed.

  (* elimination_stack.thy:97-98 - el is elim from conc_his_rel *)
  (* elimination_stack.thy:100-127 *)
  Lemma elD a :
    WellformedHistory pre val ->
    elim pre val a -> exists b, same_val val a b /\ ~ pre a b /\ ~ pre b a.
  Proof.
    intros Hwf [[Hpush|Hpop] Hnef].
    - (* is_push a *)
      destruct Hpush as [b Hab].
      exists b. split; [left; done|].
      split.
      + intros Hpre. apply Hnef. exists b. split; [left; done|left; done].
      + intros Hpre. apply Hnef. exists b. split; [left; done|right; done].
    - (* is_pop a *)
      destruct Hpop as [b Hba].
      exists b. split; [right; done|].
      split.
      + intros Hpre. apply Hnef. exists b. split; [right; done|left; done].
      + intros Hpre. apply Hnef. exists b. split; [right; done|right; done].
  Qed.

  Lemma elI1 a b : same_val val a b -> ~ pre a b -> ~ pre b a -> elim pre val a.
  Proof.
    intros Hsv Hnab Hnba.
    split.
    - destruct Hsv as [Hab|Hba].
      + left. exists b. done.
      + right. exists b. done.
    - intros (c & Hsvc & [Hac|Hca]).
      + apply Hnab. pose proof (same_val_unique a b c wf_history Hsv Hsvc) as Heq. subst c. done.
      + apply Hnba. pose proof (same_val_unique a b c wf_history Hsv Hsvc) as Heq. subst c. done.
  Qed.

  Lemma elI2 a b : same_val val a b -> ~ pre a b -> ~ pre b a -> elim pre val b.
  Proof.
    intros Hsv Hnab Hnba.
    apply (elI1 b a).
    - apply same_val_commutative. done.
    - done.
    - done.
  Qed.

  Lemma elI3 a b :
    WellformedHistory pre val ->
    elim pre val a -> same_val val a b -> elim pre val b.
  Proof.
    intros Hwf Hela Hsv.
    destruct (elD a Hwf Hela) as [c [Hsvc [Hnac Hnca]]].
    pose proof (same_val_unique a c b Hwf Hsvc Hsv) as Heq. subst c.
    eapply elI2; done.
  Qed.

  Lemma el_or_ef1 a b : pre a b -> elim pre val a \/ elim_free pre val a.
  Proof.
    intros Hab.
    destruct (always_same_val1 a b Hab) as [c Hsvc].
    destruct (decide (elim_free pre val a)) as [Hef|Hnef].
    - right. done.
    - left. split.
      + destruct Hsvc as [Hac|Hca].
        * left. exists c. done.
        * right. exists c. done.
      + done.
  Qed.

  Lemma el_or_ef2 a b : pre a b -> elim pre val b \/ elim_free pre val b.
  Proof.
    intros Hab.
    destruct (always_same_val2 a b Hab) as [c Hsvc].
    destruct (decide (elim_free pre val b)) as [Hef|Hnef].
    - right. done.
    - left. split.
      + destruct Hsvc as [Hbc|Hcb].
        * left. exists c. done.
        * right. exists c. done.
      + done.
  Qed.

  Lemma push_then_el_or_ef a : is_push val a -> elim pre val a \/ elim_free pre val a.
  Proof.
    intros [b Hab].
    destruct (decide (elim_free pre val a)) as [Hef|Hnef].
    - right. done.
    - left. split; [left; exists b|]; done.
  Qed.

  Lemma pop_then_el_or_ef a : is_pop val a -> elim pre val a \/ elim_free pre val a.
  Proof.
    intros [b Hba].
    destruct (decide (elim_free pre val a)) as [Hef|Hnef].
    - right. done.
    - left. split; [right; exists b|]; done.
  Qed.

  Lemma el_then_not_ef a : elim pre val a -> ~ elim_free pre val a.
  Proof. intros [_ Hnel]. done. Qed.

  Lemma ef_then_not_el a : elim_free pre val a -> ~ elim pre val a.
  Proof. intros Hef [_ Hnel]. done. Qed.

  (* elimination_stack.thy:132-142 - ef_pre is elim_free_pre from conc_his_rel *)
  Lemma ef_preD a b : elim_free_pre pre val a b -> elim_free pre val a /\ elim_free pre val b /\ pre a b.
  Proof. intros (Ha & Hb & Hab). done. Qed.

  Lemma ef_preI a b : elim_free pre val a -> elim_free pre val b -> pre a b -> elim_free_pre pre val a b.
  Proof. intros Ha Hb Hab. split; [|split]; done. Qed.

  (* elimination_stack.thy:144-164 - ef_val is elim_free_val from conc_his_rel *)
  Lemma ef_valD a b : elim_free_val pre val a b -> elim_free pre val a /\ elim_free pre val b /\ val a b.
  Proof. intros (Ha & Hb & Hab). done. Qed.

  Lemma ef_valI a b : elim_free pre val a -> elim_free pre val b -> val a b -> elim_free_val pre val a b.
  Proof. intros Ha Hb Hab. split; [|split]; done. Qed.

  Lemma ef_val_then_elimination_free_val a b :
    WellformedHistory pre val ->
    elim_free_val pre val a b -> elim_free_val pre val a b.
  Proof. done. Qed.

  Lemma elimination_free_val_then_ef_val a b :
    WellformedHistory pre val ->
    elim_free_val pre val a b -> elim_free_val pre val a b.
  Proof. done. Qed.

  Lemma ef_linearizable : SequentialStack lin (elim_free_val pre val).
  Proof. exact ef_linearizable_def. Qed.

  Lemma finite_set : FinitePredicate (elim_free pre val).
  Proof. exact finite_set_def. Qed.

  (* elimination_stack.thy:176-221 - minf *)
  Definition minf : relation operation :=
    fun a b => exists ra rb, same_val val a ra /\ same_val val b rb /\
      Nat.min (f a) (f ra) < Nat.min (f b) (f rb).

  Local Instance minf_dec : RelDecision minf.
  Proof. intros a b. unfold minf. apply _. Qed.

  Lemma minfD a b :
    minf a b -> exists ra rb, same_val val a ra /\ same_val val b rb.
  Proof.
    intros (ra & rb & Hsva & Hsvb & _). exists ra, rb. done.
  Qed.

  Lemma minfI a ra b rb :
    same_val val a ra -> same_val val b rb ->
    Nat.min (f a) (f ra) < Nat.min (f b) (f rb) ->
    minf a b.
  Proof.
    intros Hsva Hsvb Hlt. exists ra, rb. done.
  Qed.

  Lemma lem_f_orders a b : a <> b -> f a < f b \/ f b < f a.
  Proof.
    intros Hneq.
    destruct (Nat.lt_trichotomy (f a) (f b)) as [Hlt|[Heq|Hgt]].
    - left. done.
    - exfalso. apply Hneq. apply f_inj. done.
    - right. done.
  Qed.

  Lemma lem_min_f_orders a b c d :
    a <> c -> a <> d -> b <> c -> b <> d ->
    Nat.min (f a) (f b) < Nat.min (f c) (f d) \/ Nat.min (f c) (f d) < Nat.min (f a) (f b).
  Proof.
    intros Hnac Hnad Hnbc Hnbd.
    destruct (Nat.lt_trichotomy (Nat.min (f a) (f b)) (Nat.min (f c) (f d))) as [Hlt|[Heq|Hgt]].
    - left. done.
    - (* equality case - we need to derive contradiction from injectivity *)
      (* If min (f a) (f b) = min (f c) (f d), then either:
         - f a = f c or f a = f d (but a <> c and a <> d)
         - f b = f c or f b = f d (but b <> c and b <> d) *)
      exfalso.
      destruct (Nat.min_spec (f a) (f b)) as [[Hle Hmin1]|[Hle Hmin1]];
      destruct (Nat.min_spec (f c) (f d)) as [[Hle' Hmin2]|[Hle' Hmin2]];
      rewrite Hmin1 in Heq; rewrite Hmin2 in Heq.
      + apply Hnac. apply f_inj. done.
      + apply Hnad. apply f_inj. done.
      + apply Hnbc. apply f_inj. done.
      + apply Hnbd. apply f_inj. done.
    - right. done.
  Qed.

  Lemma always_minf a ra b rb :
    same_val val a ra -> same_val val b rb -> a <> b -> ~ same_val val a b ->
    minf a b \/ minf b a.
  Proof.
    intros Hsva Hsvb Hneqab Hnsv.
    (* We need a <> rb, ra <> b, ra <> rb *)
    assert (Hneqarb : a <> rb).
    { intros Heq. subst rb. apply Hnsv.
      destruct Hsva as [Hara|Hraa]; destruct Hsvb as [Hba|Hab].
      - (* val a ra, val b a - contradiction: a is both push and pop target *)
        exfalso. eapply def_val_order. exact Hara. exists b. left. done.
      - (* val a ra, val a b - a pushes both ra and b, so ra = b by pop_once *)
        pose proof (def_pop_once a ra b Hara Hab) as Heq. subst b. left. done.
      - (* val ra a, val b a - both ra and b push to a, so ra = b by push_once *)
        pose proof (def_push_once ra b a Hraa Hba) as Heq. subst b. right. done.
      - (* val ra a, val a b - contradiction: a is both pop and push *)
        exfalso. eapply def_val_order. exact Hab. exists ra. left. done. }
    assert (Hneqrab : ra <> b).
    { intros Heq. subst ra. apply Hnsv.
      destruct Hsva as [Hab|Hba]; destruct Hsvb as [Hbrb|Hrbb].
      - (* val a b, val b rb - a pushes b who pushes rb, contradiction *)
        exfalso. eapply def_val_order. exact Hab. exists rb. right. done.
      - (* val a b, val rb b - a and rb both push to b, so a = rb *)
        pose proof (def_push_once a rb b Hab Hrbb) as Heq. subst rb. right. done.
      - (* val b a, val b rb - b pushes to both a and rb, so a = rb *)
        pose proof (def_pop_once b a rb Hba Hbrb) as Heq. subst rb. left. done.
      - (* val b a, val rb b - rb pushes b pushes a, contradiction *)
        exfalso. eapply def_val_order. exact Hrbb. exists a. right. done. }
    assert (Hneqrarb : ra <> rb).
    { intros Heq. subst rb. apply Hnsv.
      destruct Hsva as [Hara|Hraa]; destruct Hsvb as [Hbra|Hrab].
      - (* val a ra, val b ra - both a and b push to ra, so a = b *)
        pose proof (def_push_once a b ra Hara Hbra) as Heq. done.
      - (* val a ra, val ra b - a pushes ra pushes b, contradiction *)
        exfalso. eapply def_val_order. exact Hara. exists b. right. done.
      - (* val ra a, val b ra - b pushes ra pops to a, contradiction *)
        exfalso. eapply def_val_order. exact Hbra. exists a. right. done.
      - (* val ra a, val ra b - ra pushes to both a and b, so a = b *)
        pose proof (def_pop_once ra a b Hraa Hrab) as Heq. done. }
    destruct (lem_min_f_orders a ra b rb Hneqab Hneqarb Hneqrab Hneqrarb) as [Hlt|Hgt].
    - left. exists ra, rb. done.
    - right. exists rb, ra. split; [done|split; done].
  Qed.

  Lemma not_minf_then_same_val a b :
    ~ minf a b -> ~ minf b a ->
    is_push val a \/ is_pop val a -> is_push val b \/ is_pop val b ->
    same_val val a b \/ a = b.
  Proof.
    intros Hnab Hnba Hppa Hppb.
    destruct (decide (a = b)) as [Heq|Hneq].
    - right. done.
    - destruct (decide (same_val val a b)) as [Hsv|Hnsv].
      + left. done.
      + exfalso.
        destruct Hppa as [[ra Hara]|[ra Hraa]];
        destruct Hppb as [[rb Hbrb]|[rb Hrbb]].
        * destruct (always_minf a ra b rb) as [Hminf|Hminf];
            [left; done|left; done|done|done|done|done].
        * destruct (always_minf a ra b rb) as [Hminf|Hminf];
            [left; done|right; done|done|done|done|done].
        * destruct (always_minf a ra b rb) as [Hminf|Hminf];
            [right; done|left; done|done|done|done|done].
        * destruct (always_minf a ra b rb) as [Hminf|Hminf];
            [right; done|right; done|done|done|done|done].
  Qed.

  Lemma minf_irreflexive : Irreflexive minf.
  Proof.
    intros a (ra & rb & Hsva & Hsvb & Hlt).
    pose proof (same_val_unique a ra rb wf_history Hsva Hsvb) as Heq. subst rb.
    lia.
  Qed.

  Lemma minf_antisymmetric : Antisymmetric operation eq minf.
  Proof.
    intros a b (ra & rb & Hsva & Hsvb & Hlt1) (rb' & ra' & Hsvb' & Hsva' & Hlt2).
    pose proof (same_val_unique a ra ra' wf_history Hsva Hsva') as Heq1. subst ra'.
    pose proof (same_val_unique b rb rb' wf_history Hsvb Hsvb') as Heq2. subst rb'.
    lia.
  Qed.

  Lemma minf_transitive : Transitive minf.
  Proof.
    intros a b c (ra & rb & Hsva & Hsvb & Hlt1) (rb' & rc & Hsvb' & Hsvc & Hlt2).
    pose proof (same_val_unique b rb rb' wf_history Hsvb Hsvb') as Heq. subst rb'.
    exists ra, rc. split; [|split]; [done|done|lia].
  Qed.

  Lemma same_val_then_not_minf a b : same_val val a b -> ~ minf a b.
  Proof.
    intros Hsv (ra & rb & Hsva & Hsvb & Hlt).
    pose proof (same_val_unique a ra b wf_history Hsva Hsv) as Heq1. subst ra.
    (* Now we have Hsv : same_val val a b, Hsvb : same_val val b rb *)
    (* We need to show a = rb or get contradiction *)
    destruct Hsv as [Hab|Hba]; destruct Hsvb as [Hbrb|Hrbb].
    - (* val a b, val b rb - b is both pop and push, contradiction *)
      exfalso. eapply def_val_order. exact Hab. exists rb. right. done.
    - (* val a b, val rb b - a and rb both push to b, so a = rb *)
      pose proof (def_push_once a rb b Hab Hrbb) as Heq. subst rb. lia.
    - (* val b a, val b rb - b pushes to both a and rb, so a = rb *)
      pose proof (def_pop_once b a rb Hba Hbrb) as Heq. subst rb. lia.
    - (* val b a, val rb b - rb pushes b pushes a, contradiction *)
      exfalso. eapply def_val_order. exact Hrbb. exists a. right. done.
  Qed.

  (* elimination_stack.thy:223-243 - el_pre *)
  Definition el_pre : relation operation :=
    fun a b => exists c, same_val val b c /\ (pre a b \/ pre a c).

  Local Instance el_pre_dec : RelDecision el_pre.
  Proof. intros a b. unfold el_pre. apply _. Qed.

  Lemma el_preD1 a b : el_pre a b -> exists c, same_val val b c /\ (pre a b \/ pre a c).
  Proof. done. Qed.

  Lemma el_preD a b c :
    WellformedHistory pre val ->
    el_pre a b -> same_val val b c -> pre a b \/ pre a c.
  Proof.
    intros Hwf (d & Hsvbd & Hpre) Hsvbc.
    pose proof (same_val_unique b d c Hwf Hsvbd Hsvbc) as Heq. subst d. done.
  Qed.

  Lemma el_preI1 b c a : same_val val b c -> pre a b \/ pre a c -> el_pre a b.
  Proof. intros Hsv Hpre. exists c. done. Qed.

  Lemma el_preI2 b c a : same_val val b c -> pre a b \/ pre a c -> el_pre a c.
  Proof.
    intros Hsv Hpre.
    exists b. split.
    - apply same_val_commutative. done.
    - destruct Hpre as [Hab|Hac]; [right|left]; done.
  Qed.

  Lemma el_pre_abcd : Abcd el_pre.
  Proof.
    intros a b c d (e & Hsve & [Hab|Hae]) (g & Hsvg & [Hcd|Hcg]).
    - destruct (pre_abcd_assumption a b c d Hab Hcd) as [Had|Hcb].
      + left. exists g. split; [done|left; done].
      + right. exists e. split; [done|left; done].
    - destruct (pre_abcd_assumption a b c g Hab Hcg) as [Hag|Hcb].
      + left. exists g. split; [done|right; done].
      + right. exists e. split; [done|left; done].
    - destruct (pre_abcd_assumption a e c d Hae Hcd) as [Had|Hce].
      + left. exists g. split; [done|left; done].
      + right. exists e. split; [done|right; done].
    - destruct (pre_abcd_assumption a e c g Hae Hcg) as [Hag|Hce].
      + left. exists g. split; [done|right; done].
      + right. exists e. split; [done|right; done].
  Qed.

  Lemma lem_is_push_ef_then_is_ef_push a :
    is_push val a -> elim_free pre val a -> is_push (elim_free_val pre val) a.
  Proof.
    intros [b Hab] Hefa.
    exists b. split; [|split]; [done| |done].
    eapply ef_val_then_ef; [exact wf_history|exact Hefa|left; done].
  Qed.

  Lemma lem_is_pop_ef_then_is_ef_pop a :
    is_pop val a -> elim_free pre val a -> is_pop (elim_free_val pre val) a.
  Proof.
    intros [b Hba] Hefa.
    exists b. split; [|split]; [| |done].
    - eapply ef_val_then_ef; [exact wf_history|exact Hefa|right; done].
    - done.
  Qed.

  (* Helper: find minimal ef element with el_pre in a list *)
  Lemma lem_pos_exists_list b (L : list operation) :
    elim pre val b ->
    NoDup L ->
    (forall x, x ∈ L -> elim_free pre val x) ->
    (forall a, a ∈ L -> ~ el_pre a b) \/
    (exists a, a ∈ L /\ el_pre a b /\
      (forall c, c ∈ L /\ lin a c -> ~ el_pre c b)).
  Proof.
    intros Helb Hnodup HefL.
    induction L as [|x xs IH].
    - left. intros a Ha. inversion Ha.
    - apply NoDup_cons in Hnodup. destruct Hnodup as [Hxnin Hnodup'].
      assert (HefL' : forall y, y ∈ xs -> elim_free pre val y) by (intros y Hy; apply HefL; by right).
      specialize (IH Hnodup' HefL').
      destruct (decide (el_pre x b)) as [Hxb|Hnxb].
      + (* el_pre x b *)
        destruct IH as [Hnoef|[a (Hain & Hab & Hmin)]].
        * (* No element in xs has el_pre *)
          right. exists x. split; [by left|split; [done|]].
          intros c (Hcin & Hlinxc).
          apply elem_of_cons in Hcin.
          destruct Hcin as [Heq|Hcxs].
          -- subst c.
             destruct ef_linearizable_def as [Hseq _].
             destruct Hseq as [Hwflin _ _ _].
             destruct Hwflin as [_ _ Hirr _ _ _ _ _ _].
             exfalso. by eapply Hirr.
          -- apply Hnoef. done.
        * (* a is witness in xs *)
          assert (Hefx : elim_free pre val x) by (apply HefL; by left).
          assert (Hefa : elim_free pre val a) by (apply HefL'; done).
          destruct (decide (x = a)) as [Heq|Hneq].
          -- subst x. done.
          -- assert (Hppx : is_push (elim_free_val pre val) x ∨ is_pop (elim_free_val pre val) x).
             { destruct (ef_then_push_or_pop x Hefx) as [[d Hxd]|[d Hdx]].
               - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
               - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
             assert (Hppa : is_push (elim_free_val pre val) a ∨ is_pop (elim_free_val pre val) a).
             { destruct (ef_then_push_or_pop a Hefa) as [[d Had]|[d Hda]].
               - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
               - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
             destruct ef_linearizable_def as [Hseq _].
             destruct Hseq as [Hwflin Htotpush Htotpop Htotpp].
             assert (Hlinord : lin x a ∨ lin a x).
             { destruct Hppx as [[dx Hxdx]|[dx Hdxx]];
               destruct Hppa as [[da Hada]|[da Hdaa]].
               - apply (Htotpush x a); [exists dx|exists da|]; done.
               - apply (Htotpp x a); [exists dx|exists da]; done.
               - destruct (Htotpp a x) as [Hax|Hxa]; [exists da|exists dx|right|left]; done.
               - apply (Htotpop x a); [exists dx|exists da|]; done. }
             destruct Hlinord as [Hlinxa|Hlinax].
             ++ (* lin x a: a stays minimal *)
                right. exists a. split; [by right|split; [done|]].
                intros c (Hcin & Hlinac).
                apply elem_of_cons in Hcin.
                destruct Hcin as [Hceq|Hcxs].
                ** subst c.
                   destruct Hwflin as [_ Hanti _ _ _ _ _ _ _].
                   pose proof (Hanti x a Hlinxa Hlinac) as Heq. done.
                ** apply Hmin. split; done.
             ++ (* lin a x: x becomes minimal *)
                right. exists x. split; [by left|split; [done|]].
                intros c (Hcin & Hlinxc).
                apply elem_of_cons in Hcin.
                destruct Hcin as [Hceq|Hcxs].
                ** subst c.
                   destruct Hwflin as [_ _ Hirr _ _ _ _ _ _].
                   exfalso. by eapply Hirr.
                ** assert (Hefc : elim_free pre val c) by (apply HefL'; done).
                   destruct (decide (lin a c)) as [Hlinac|Hnlinac].
                   --- apply Hmin. split; done.
                   --- assert (Hppc : is_push (elim_free_val pre val) c ∨ is_pop (elim_free_val pre val) c).
                       { destruct (ef_then_push_or_pop c Hefc) as [[d Hcd]|[d Hdc]].
                         - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
                         - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
                       destruct (decide (c = a)) as [Hcaeq|Hcaneq].
                       +++ subst c.
                           destruct Hwflin as [_ Hanti _ _ _ _ _ _ _].
                           pose proof (Hanti x a Hlinxc Hlinax) as Heq. done.
                       +++ destruct Hwflin as [Htrans Hanti _ _ _ _ _ _ _].
                           assert (Hlinca : lin c a).
                           { destruct Hppc as [[dc Hcdc]|[dc Hdcc]];
                             destruct Hppa as [[da Hada]|[da Hdaa]].
                             - destruct (Htotpush c a (ex_intro _ dc Hcdc) (ex_intro _ da Hada) Hcaneq); done.
                             - destruct (Htotpp c a (ex_intro _ dc Hcdc) (ex_intro _ da Hdaa)); done.
                             - destruct (Htotpp a c (ex_intro _ da Hada) (ex_intro _ dc Hdcc)); done.
                             - destruct (Htotpop c a (ex_intro _ dc Hdcc) (ex_intro _ da Hdaa) Hcaneq); done. }
                           pose proof (Htrans c a x Hlinca Hlinax) as Hlincx.
                           pose proof (Hanti x c Hlinxc Hlincx) as Heq.
                           subst c. exfalso. apply Hxnin. done.
      + (* ~el_pre x b *)
        destruct IH as [Hnoef|[a (Hain & Hab & Hmin)]].
        * left. intros y Hyin.
          apply elem_of_cons in Hyin.
          destruct Hyin as [Heq|Hyxs].
          -- subst y. done.
          -- apply Hnoef. done.
        * right. exists a. split; [by right|split; [done|]].
          intros c (Hcin & Hlinac).
          apply elem_of_cons in Hcin.
          destruct Hcin as [Heqcx|Hcxs].
          -- subst c. done.
          -- apply Hmin. split; done.
  Qed.

  Lemma lem_pos_exists b :
    elim pre val b ->
    (forall a, elim_free pre val a -> ~ el_pre a b) \/
    (exists a, elim_free pre val a /\ el_pre a b /\
      (forall c, elim_free pre val c /\ lin a c -> ~ el_pre c b)).
  Proof.
    intros Helb.
    destruct finite_set_def as [enum [Hnodup Henum]].
    (* We do induction on enum, tracking the intermediate result *)
    (* Invariant: either no ef element seen so far has el_pre to b,
       or there's a minimal one among those seen *)
    assert (Hmain :
      (forall a, elim_free pre val a -> a ∈ enum -> ~ el_pre a b) \/
      (exists a, elim_free pre val a /\ a ∈ enum /\ el_pre a b /\
        (forall c, elim_free pre val c /\ c ∈ enum /\ lin a c -> ~ el_pre c b))).
    { clear Henum.
      induction enum as [|x xs IH].
      - left. intros a _ Ha. inversion Ha.
      - apply NoDup_cons in Hnodup. destruct Hnodup as [Hxnin Hnodup'].
        specialize (IH Hnodup').
        destruct (decide (elim_free pre val x /\ el_pre x b)) as [[Hefx Hprex]|Hnx].
        + (* x is ef and has el_pre to b *)
          destruct IH as [Hnoef|[a (Hefa & Hain & Hprea & Hmina)]].
          * (* No previous ef element has el_pre *)
            right. exists x. split; [done|split; [by left|split; [done|]]].
            intros c (Hefc & Hcin & Hlinxc).
            apply elem_of_cons in Hcin.
            destruct Hcin as [Heq|Hcxs].
            -- subst c.
               destruct ef_linearizable_def as [Hseq _].
               destruct Hseq as [Hwflin _ _ _].
               destruct Hwflin as [_ _ Hirr _ _ _ _ _ _].
               exfalso. by eapply Hirr.
            -- apply Hnoef; done.
          * (* a is minimal in xs *)
            destruct (decide (x = a)) as [Heq|Hneq].
            -- subst x. right. exists a. split; [done|split; [by left|split; [done|]]].
               intros c (Hefc & Hcin & Hlinac).
               apply elem_of_cons in Hcin.
               destruct Hcin as [Heq|Hcxs].
               ++ subst c.
                  destruct ef_linearizable_def as [Hseq _].
                  destruct Hseq as [Hwflin _ _ _].
                  destruct Hwflin as [_ _ Hirr _ _ _ _ _ _].
                  exfalso. by eapply Hirr.
               ++ apply Hmina. split; [|split]; done.
            -- (* x ≠ a: compare in lin order *)
               assert (Hppx : is_push (elim_free_val pre val) x ∨ is_pop (elim_free_val pre val) x).
               { destruct (ef_then_push_or_pop x Hefx) as [[d Hxd]|[d Hdx]].
                 - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
                 - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
               assert (Hppa : is_push (elim_free_val pre val) a ∨ is_pop (elim_free_val pre val) a).
               { destruct (ef_then_push_or_pop a Hefa) as [[d Had]|[d Hda]].
                 - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
                 - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
               destruct ef_linearizable_def as [Hseq _].
               destruct Hseq as [Hwflin Htotpush Htotpop Htotpp].
               assert (Hlinord : lin x a ∨ lin a x).
               { destruct Hppx as [[dx Hxdx]|[dx Hdxx]];
                 destruct Hppa as [[da Hada]|[da Hdaa]].
                 - apply (Htotpush x a); [exists dx|exists da|]; done.
                 - apply (Htotpp x a); [exists dx|exists da]; done.
                 - destruct (Htotpp a x) as [Hax|Hxa]; [exists da|exists dx|right|left]; done.
                 - apply (Htotpop x a); [exists dx|exists da|]; done. }
               destruct Hlinord as [Hlinxa|Hlinax].
               ++ (* lin x a: a stays minimal *)
                  right. exists a. split; [done|split; [by right|split; [done|]]].
                  intros c (Hefc & Hcin & Hlinac).
                  apply elem_of_cons in Hcin.
                  destruct Hcin as [Hceq|Hcxs].
                  ** subst c.
                     destruct Hwflin as [_ Hanti _ _ _ _ _ _ _].
                     pose proof (Hanti x a Hlinxa Hlinac) as Heq. done.
                  ** apply Hmina. split; [|split]; done.
               ++ (* lin a x: x becomes minimal *)
                  right. exists x. split; [done|split; [by left|split; [done|]]].
                  intros c (Hefc & Hcin & Hlinxc).
                  apply elem_of_cons in Hcin.
                  destruct Hcin as [Hceq|Hcxs].
                  ** subst c.
                     destruct Hwflin as [_ _ Hirr _ _ _ _ _ _].
                     exfalso. by eapply Hirr.
                  ** destruct (decide (lin a c)) as [Hlinac|Hnlinac].
                     --- apply Hmina. split; [|split]; done.
                     --- destruct (decide (c = a)) as [Hcaeq|Hcaneq].
                         +++ subst c.
                             destruct Hwflin as [_ Hanti _ _ _ _ _ _ _].
                             pose proof (Hanti x a Hlinxc Hlinax) as Heq. done.
                         +++ assert (Hppc : is_push (elim_free_val pre val) c ∨ is_pop (elim_free_val pre val) c).
                             { destruct (ef_then_push_or_pop c Hefc) as [[d Hcd]|[d Hdc]].
                               - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
                               - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
                             destruct Hwflin as [Htrans Hanti _ _ _ _ _ _ _].
                             assert (Hlinca : lin c a).
                             { destruct Hppc as [[dc Hcdc]|[dc Hdcc]];
                               destruct Hppa as [[da Hada]|[da Hdaa]].
                               - destruct (Htotpush c a (ex_intro _ dc Hcdc) (ex_intro _ da Hada) Hcaneq); done.
                               - destruct (Htotpp c a (ex_intro _ dc Hcdc) (ex_intro _ da Hdaa)); done.
                               - destruct (Htotpp a c (ex_intro _ da Hada) (ex_intro _ dc Hdcc)); done.
                               - destruct (Htotpop c a (ex_intro _ dc Hdcc) (ex_intro _ da Hdaa) Hcaneq); done. }
                             pose proof (Htrans c a x Hlinca Hlinax) as Hlincx.
                             pose proof (Hanti x c Hlinxc Hlincx) as Heq.
                             subst c. exfalso. apply Hxnin. done.
        + (* x is not ef or doesn't have el_pre *)
          destruct IH as [Hnoef|[a (Hefa & Hain & Hprea & Hmina)]].
          * left. intros y Hefy Hyin.
            apply elem_of_cons in Hyin.
            destruct Hyin as [Heq|Hyxs].
            -- subst y. intros Hprey. apply Hnx. done.
            -- apply Hnoef; done.
          * right. exists a. split; [done|split; [by right|split; [done|]]].
            intros c (Hefc & Hcin & Hlinac).
            apply elem_of_cons in Hcin.
            destruct Hcin as [Hceq|Hcxs].
            -- subst c. intros Hprec. apply Hnx. done.
            -- apply Hmina. split; [|split]; done. }
    destruct Hmain as [Hcase1|[a (Hefa & Hain & Hprea & Hmina)]].
    - left. intros a Hefa. apply Hcase1; [done|apply Henum; done].
    - right. exists a. split; [done|split; [done|]].
      intros c [Hefc Hlinac].
      apply Hmina. split; [|split]; [done|apply Henum; done|done].
  Qed.

  (* elimination_stack.thy:293-303 - el_pos *)
  Definition el_pos : relation operation :=
    fun a b => elim_free pre val a /\ elim pre val b /\ el_pre a b /\
      (forall c, elim_free pre val c /\ lin a c -> ~ el_pre c b).

  Local Instance el_pos_dec : RelDecision el_pos.
  Proof. intros a b. unfold el_pos. apply _. Qed.

  Lemma el_posD a b :
    el_pos a b ->
    elim_free pre val a /\ elim pre val b /\ el_pre a b /\
      (forall c, elim_free pre val c /\ lin a c -> ~ el_pre c b).
  Proof. done. Qed.

  Lemma el_posI a b :
    elim_free pre val a -> elim pre val b -> el_pre a b ->
    (forall c, elim_free pre val c /\ lin a c -> ~ el_pre c b) ->
    el_pos a b.
  Proof. intros Ha Hb Hab Hc. split; [|split; [|split]]; done. Qed.


  Lemma one_el_pos a b c : el_pos a b -> el_pos c b -> a = c.
  Proof.
    intros (Hefa & Helb & Hab & Hcond1) (Hefc & Helb' & Hcb & Hcond2).
    destruct (decide (a = c)) as [Heq|Hneq]; [done|].
    (* a and c are both ef elements, so they're totally ordered by lin *)
    assert (Hppa : is_push val a \/ is_pop val a) by (apply ef_then_push_or_pop; done).
    assert (Hppc : is_push val c \/ is_pop val c) by (apply ef_then_push_or_pop; done).
    assert (Hpusha : is_push (elim_free_val pre val) a \/ is_pop (elim_free_val pre val) a).
    { destruct Hppa as [Hpush|Hpop].
      - left. apply lem_is_push_ef_then_is_ef_push; done.
      - right. apply lem_is_pop_ef_then_is_ef_pop; done. }
    assert (Hpushc : is_push (elim_free_val pre val) c \/ is_pop (elim_free_val pre val) c).
    { destruct Hppc as [Hpush|Hpop].
      - left. apply lem_is_push_ef_then_is_ef_push; done.
      - right. apply lem_is_pop_ef_then_is_ef_pop; done. }
    (* lin is total on ef, so either lin a c or lin c a *)
    destruct ef_linearizable_def as [Hseq Hlifo].
    destruct Hseq as [Hwf Htotpush Htotpop Htotpp].
    destruct Hpusha as [[da Hada]|[da Hdaa]]; destruct Hpushc as [[dc Hcdc]|[dc Hdcc]].
    - (* both pushes *)
      destruct (Htotpush a c) as [Hac|Hca].
      + exists da. done.
      + exists dc. done.
      + done.
      + exfalso. apply (Hcond1 c). split; [done|done]. done.
      + exfalso. apply (Hcond2 a). split; [done|done]. done.
    - (* a push, c pop *)
      destruct (Htotpp a c) as [Hac|Hca].
      + exists da. done.
      + exists dc. done.
      + exfalso. apply (Hcond1 c). split; [done|done]. done.
      + exfalso. apply (Hcond2 a). split; [done|done]. done.
    - (* a pop, c push *)
      destruct (Htotpp c a) as [Hca|Hac].
      + exists dc. done.
      + exists da. done.
      + exfalso. apply (Hcond2 a). split; [done|done]. done.
      + exfalso. apply (Hcond1 c). split; [done|done]. done.
    - (* both pops *)
      destruct (Htotpop a c) as [Hac|Hca].
      + exists da. done.
      + exists dc. done.
      + done.
      + exfalso. apply (Hcond1 c). split; [done|done]. done.
      + exfalso. apply (Hcond2 a). split; [done|done]. done.
  Qed.

  Lemma not_el_posD b :
    ~ (exists a, el_pos a b) -> elim pre val b -> forall a, elim_free pre val a -> ~ el_pre a b.
  Proof.
    intros Hnpos Helb a Hefa Hpre.
    destruct (lem_pos_exists b Helb) as [Hnopos|[a' (Hefa' & Hpre' & Hcond)]].
    - apply (Hnopos a); done.
    - apply Hnpos. exists a'. apply el_posI; done.
  Qed.

  (* elimination_stack.thy:346-379 - ef_el *)
  Definition ef_el : relation operation :=
    fun x y =>
      (elim pre val x /\ elim_free pre val y /\ (forall a, elim_free pre val a -> ~ el_pre a x)) \/
      (elim pre val x /\ elim_free pre val y /\ (exists a, el_pos a x /\ lin a y)) \/
      (elim pre val y /\ elim_free pre val x /\ el_pos x y) \/
      (elim pre val y /\ elim_free pre val x /\ (exists a, el_pos a y /\ lin x a)).

  Lemma ef_elD x y :
    ef_el x y ->
    (elim pre val x /\ elim_free pre val y /\ (forall a, elim_free pre val a -> ~ el_pre a x)) \/
    (elim pre val x /\ elim_free pre val y /\ (exists a, el_pos a x /\ lin a y)) \/
    (elim pre val y /\ elim_free pre val x /\ el_pos x y) \/
    (elim pre val y /\ elim_free pre val x /\ (exists a, el_pos a y /\ lin x a)).
  Proof. done. Qed.

  Lemma ef_elI1 x y : elim pre val x -> elim_free pre val y -> (forall a, elim_free pre val a -> ~ el_pre a x) -> ef_el x y.
  Proof. intros Hx Hy Ha. left. done. Qed.

  Lemma ef_elI2 x y a : elim pre val x -> elim_free pre val y -> el_pos a x -> lin a y -> ef_el x y.
  Proof. intros Hx Hy Hpos Hlin. right. left. split; [|split]; [done|done|exists a; done]. Qed.

  Lemma ef_elI3 x y a : elim pre val x -> elim_free pre val y -> el_pos a x -> lin y a -> ef_el y x.
  Proof. intros Hx Hy Hpos Hlin. do 3 right. split; [|split]; [done|done|exists a; done]. Qed.

  Lemma ef_elI4 x y : elim pre val x -> el_pos y x -> ef_el y x.
  Proof.
    intros Hx Hpos.
    destruct Hpos as (Hefy & Helx & Hpre & Hcond).
    do 2 right. left. done.
  Qed.

  Lemma ef_el_total x y : elim pre val x -> elim_free pre val y -> ef_el x y \/ ef_el y x.
  Proof.
    intros Helx Hefy.
    destruct (lem_pos_exists x Helx) as [Hnopos|[a (Hefa & Hpre & Hcond)]].
    - (* No ef element is el_pre to x - ef_el x y via case 1 *)
      left. apply ef_elI1; done.
    - (* a is the minimal ef element with el_pre a x *)
      destruct (decide (a = y)) as [Heq|Hneq].
      + (* a = y, so el_pos y x - ef_el y x via case 3 *)
        subst a.
        right. do 2 right. left. split; [|split; [|split]]; [done|done|done|done].
      + (* a <> y, use totality of lin on ef elements *)
        assert (Hppa : is_push val a \/ is_pop val a) by (apply ef_then_push_or_pop; done).
        assert (Hppy : is_push val y \/ is_pop val y) by (apply ef_then_push_or_pop; done).
        destruct ef_linearizable_def as [Hseq _].
        destruct Hseq as [_ Htotpush Htotpop Htotpp].
        assert (Hlinord : lin a y \/ lin y a).
        { destruct Hppa as [[da Hada]|[da Hdaa]]; destruct Hppy as [[dy Hydy]|[dy Hdyy]].
          - apply Htotpush; try done.
            + apply lem_is_push_ef_then_is_ef_push; [exists da|]; done.
            + apply lem_is_push_ef_then_is_ef_push; [exists dy|]; done.
          - apply Htotpp.
            + apply lem_is_push_ef_then_is_ef_push; [exists da|]; done.
            + apply lem_is_pop_ef_then_is_ef_pop; [exists dy|]; done.
          - destruct (Htotpp y a) as [Hya|Hay].
            + apply lem_is_push_ef_then_is_ef_push; [exists dy|]; done.
            + apply lem_is_pop_ef_then_is_ef_pop; [exists da|]; done.
            + right. done.
            + left. done.
          - apply Htotpop; try done.
            + apply lem_is_pop_ef_then_is_ef_pop; [exists da|]; done.
            + apply lem_is_pop_ef_then_is_ef_pop; [exists dy|]; done. }
        destruct Hlinord as [Hlinay|Hlinya].
        * (* lin a y - ef_el x y via case 2 *)
          left. apply ef_elI2 with a; [done|done| |done].
          split; [|split; [|split]]; [done|done|done|done].
        * (* lin y a - ef_el y x via case 4 *)
          right. do 3 right. split; [|split]; [done|done|].
          exists a. split; [|done].
          split; [|split; [|split]]; [done|done|done|done].
  Qed.

  Lemma pr_in_ef_el_help x y : elim_free pre val x -> elim pre val y -> pre x y -> ~ (exists a, el_pos a y) -> False.
  Proof.
    intros Hefx Hely Hprexy Hnpos.
    pose proof (not_el_posD y Hnpos Hely) as Hnoelpre.
    apply (Hnoelpre x Hefx).
    destruct (elD y wf_history Hely) as (c & Hsvc & _).
    apply (el_preI1 y c x Hsvc). left. done.
  Qed.

  Lemma pr_in_ef_el_help2 x y a : elim_free pre val x -> elim pre val y -> pre x y -> el_pos a y -> x = a \/ lin x a.
  Proof.
    intros Hefx Hely Hprexy Hpos.
    destruct (el_posD a y Hpos) as (Hefa & _ & _ & Hmin).
    destruct (decide (x = a)) as [Heq|Hneq]; [by left|right].
    (* x and a are both ef, so totality gives us lin ordering *)
    assert (Hppx : is_push (elim_free_val pre val) x ∨ is_pop (elim_free_val pre val) x).
    { destruct (ef_then_push_or_pop x Hefx) as [[d Hxd]|[d Hdx]].
      - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
      - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
    assert (Hppa : is_push (elim_free_val pre val) a ∨ is_pop (elim_free_val pre val) a).
    { destruct (ef_then_push_or_pop a Hefa) as [[d Had]|[d Hda]].
      - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
      - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
    destruct ef_linearizable_def as [Hseq _].
    destruct Hseq as [_ Htotpush Htotpop Htotpp].
    assert (Hlinord : lin x a ∨ lin a x).
    { destruct Hppx as [[dx Hxdx]|[dx Hdxx]];
      destruct Hppa as [[da Hada]|[da Hdaa]].
      - apply (Htotpush x a); [exists dx|exists da|]; done.
      - apply (Htotpp x a); [exists dx|exists da]; done.
      - destruct (Htotpp a x) as [Hax|Hxa]; [exists da|exists dx|right|left]; done.
      - apply (Htotpop x a); [exists dx|exists da|]; done. }
    destruct Hlinord as [|Hlinax]; [done|].
    (* lin a x contradicts minimality of a since el_pre x y *)
    exfalso. apply (Hmin x).
    - split; [done|done].
    - destruct (elD y wf_history Hely) as (c & Hsvc & _).
      apply (el_preI1 y c x Hsvc). left. done.
  Qed.

  Lemma pr_then_not_rev_pr x y a :
    WellformedHistory pre val ->
    elim pre val x -> same_val val x y -> pre x a -> ~ pre a y.
  Proof.
    intros Hwf Helx Hsv Hprexa Hpreay.
    destruct (elD x Hwf Helx) as (c & Hsvc & Hnprexc & _).
    pose proof (same_val_unique x y c Hwf Hsv Hsvc) as Heq. subst c.
    apply Hnprexc.
    destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
    eapply Htrans; done.
  Qed.

  Lemma ef_then_elimination_free a : elim_free pre val a -> elim_free pre val a.
  Proof. done. Qed.

  Lemma ef_pre_then_elimination_free_pre a b : elim_free_pre pre val a b -> elim_free_pre pre val a b.
  Proof. done. Qed.

  Lemma pr_then_lin x y a :
    WellformedHistory pre val ->
    elim pre val x -> elim_free pre val y -> pre x y -> el_pos a x -> lin a y.
  Proof.
    intros Hwf Helx Hefy Hprexy Hpos.
    destruct (el_posD a x Hpos) as (Hefa & _ & Hpre & _).
    destruct (el_preD1 a x Hpre) as (c & Hsvc & Hpreaorx).
    assert (Hpreay : pre a y).
    { destruct Hpreaorx as [Hpreax|Hpreac].
      - destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
        eapply Htrans; done.
      - destruct (pre_abcd_assumption a c x y Hpreac Hprexy) as [Hpreay|Hprexc].
        + done.
        + exfalso. destruct (elD x Hwf Helx) as (d & Hsvd & Hnprexd & _).
          pose proof (same_val_unique x c d Hwf Hsvc Hsvd) as Heq. subst d.
          apply Hnprexd. done. }
    apply pr_in_lin.
    split; [|split]; done.
  Qed.

  Lemma pr_in_ef_el1 x y : elim_free pre val x -> elim pre val y -> pre x y -> ef_el x y.
  Proof.
    intros Hefx Hely Hprexy.
    (* We need to show ef_el x y, with ef x and el y, this uses cases 3-4 *)
    (* First establish el_pre x y *)
    assert (Hprex : el_pre x y).
    { destruct (elD y wf_history Hely) as (c & Hsvc & _ & _).
      exists c. split; [done|left; done]. }
    (* Use lem_pos_exists to find the minimal ef element with el_pre to y *)
    destruct (lem_pos_exists y Hely) as [Hnopos|[a (Hefa & Hprea & Hcond)]].
    - (* No ef element has el_pre to y - but x does, contradiction *)
      exfalso. apply (Hnopos x); done.
    - (* a is the minimal ef element with el_pre a y *)
      destruct (decide (x = a)) as [Heq|Hneq].
      + (* x = a, so el_pos x y - case 3 *)
        subst a.
        do 2 right. left. split; [|split; [|split]]; [done|done|done|done].
      + (* x <> a, determine lin relationship *)
        assert (Hlinord : lin x a \/ lin a x).
        { assert (Hppx : is_push val x \/ is_pop val x) by (apply ef_then_push_or_pop; done).
          assert (Hppa : is_push val a \/ is_pop val a) by (apply ef_then_push_or_pop; done).
          destruct ef_linearizable_def as [Hseq _].
          destruct Hseq as [_ Htotpush Htotpop Htotpp].
          destruct Hppx as [[dx Hxdx]|[dx Hdxx]]; destruct Hppa as [[da Hada]|[da Hdaa]].
          - apply Htotpush; try done.
            + apply lem_is_push_ef_then_is_ef_push; [exists dx|]; done.
            + apply lem_is_push_ef_then_is_ef_push; [exists da|]; done.
          - apply Htotpp.
            + apply lem_is_push_ef_then_is_ef_push; [exists dx|]; done.
            + apply lem_is_pop_ef_then_is_ef_pop; [exists da|]; done.
          - destruct (Htotpp a x) as [Hax|Hxa].
            + apply lem_is_push_ef_then_is_ef_push; [exists da|]; done.
            + apply lem_is_pop_ef_then_is_ef_pop; [exists dx|]; done.
            + right. done.
            + left. done.
          - apply Htotpop; try done.
            + apply lem_is_pop_ef_then_is_ef_pop; [exists dx|]; done.
            + apply lem_is_pop_ef_then_is_ef_pop; [exists da|]; done. }
        destruct Hlinord as [Hlinxa|Hlinax].
        * (* lin x a - case 4 *)
          do 3 right. split; [|split]; [done|done|].
          exists a. split; [|done].
          split; [|split; [|split]]; [done|done|done|done].
        * (* lin a x - minimality gives ~ el_pre x y, contradiction *)
          exfalso. apply (Hcond x (conj Hefx Hlinax)). done.
  Qed.

  Lemma pr_in_ef_el2 x y : elim pre val x -> elim_free pre val y -> pre x y -> ef_el x y.
  Proof.
    intros Helx Hefy Hprexy.
    destruct (decide (exists a, el_pos a x)) as [[a Hpos]|Hnpos].
    - (* el_pos a x exists *)
      apply (ef_elI2 x y a Helx Hefy Hpos).
      apply (pr_then_lin x y a wf_history Helx Hefy Hprexy Hpos).
    - (* no el_pos to x *)
      apply ef_elI1; [done|done|].
      apply not_el_posD; done.
  Qed.

  Lemma ef_el_then_ef_and_el a b : ef_el a b -> (elim pre val a /\ elim_free pre val b) \/ (elim_free pre val a /\ elim pre val b).
  Proof.
    intros [(Ha & Hb & _)|[(Ha & Hb & _)|[(Ha & Hb & _)|(Ha & Hb & _)]]].
    - left. done.
    - left. done.
    - right. done.
    - right. done.
  Qed.

  Lemma ef_el_irreflexive : Irreflexive ef_el.
  Proof.
    intros a Haa.
    apply ef_el_then_ef_and_el in Haa.
    destruct Haa as [[Hel Hef]|[Hef Hel]].
    - apply el_then_not_ef in Hel. done.
    - apply el_then_not_ef in Hel. done.
  Qed.

  Lemma ef_el_antisymmetric : Antisymmetric operation eq ef_el.
  Proof.
    intros x y Hxy Hyx.
    (* ef_el x y gives (elim x /\ ef y) or (ef x /\ elim y) *)
    (* ef_el y x gives (elim y /\ ef x) or (ef y /\ elim x) *)
    assert (Hxy' := Hxy). assert (Hyx' := Hyx).
    apply ef_el_then_ef_and_el in Hxy'.
    apply ef_el_then_ef_and_el in Hyx'.
    destruct Hxy' as [[Helx Hefy]|[Hefx Hely]];
    destruct Hyx' as [[Hely' Hefx']|[Hefy' Helx']].
    - (* (elim x /\ ef y) and (elim y /\ ef x) *)
      exfalso. apply el_then_not_ef in Hely'. done.
    - (* (elim x /\ ef y) and (ef y /\ elim x) - need detailed analysis *)
      (* Both agree on elim x and ef y, need to look at subcases *)
      exfalso.
      (* ef_el x y with (elim x /\ ef y) is cases 1-2 *)
      destruct Hxy as [(Helx_ & Hefy_ & Hnopos)|[(Helx_ & Hefy_ & [a [Hposa Hlinay]])|[Hcontra|Hcontra]]];
      [| |destruct Hcontra as (_ & Hef & _); apply el_then_not_ef in Hef; done
       |destruct Hcontra as (_ & Hef & _); apply el_then_not_ef in Hef; done].
      { (* case 1: forall a, ef a -> ~ el_pre a x *)
        (* ef_el y x with (ef y /\ elim x) is cases 3-4 *)
        destruct Hyx as [Hcontra|[Hcontra|[(? & ? & Hposy)|(_ & _ & [b [Hposb ?]])]]];
        [destruct Hcontra as (? & Hef & _); apply el_then_not_ef in Hefy'; done
        |destruct Hcontra as (? & Hef & _); apply el_then_not_ef in Hefy'; done| |].
        - (* el_pos y x *)
          destruct Hposy as (Hef_y & ? & Hprey & _).
          apply (Hnopos y); done.
        - (* exists b, el_pos b x /\ lin y b *)
          destruct Hposb as (Hefb & ? & Hpreb & _).
          apply (Hnopos b); done. }
      { (* case 2: exists a, el_pos a x /\ lin a y *)
        destruct Hyx as [Hcontra|[Hcontra|[(? & ? & Hposy)|(_ & _ & [b [Hposb Hlinyb]])]]];
        [destruct Hcontra as (? & Hef & _); apply el_then_not_ef in Hefy'; done
        |destruct Hcontra as (? & Hef & _); apply el_then_not_ef in Hefy'; done| |].
        - (* el_pos y x and el_pos a x -> y = a by one_el_pos *)
          pose proof (one_el_pos a x y Hposa Hposy) as Heq. subst a.
          (* lin y y - contradiction *)
          destruct ef_linearizable_def as [[Hwf _ _ _] _].
          destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
          eapply Hirr. exact Hlinay.
        - (* el_pos a x, el_pos b x -> a = b *)
          pose proof (one_el_pos a x b Hposa Hposb) as Heq. subst b.
          (* lin a y and lin y a *)
          destruct ef_linearizable_def as [[Hwf _ _ _] _].
          destruct Hwf as [_ Hanti Hirr _ _ _ _ _ _].
          pose proof (Hanti a y Hlinay Hlinyb) as Heq. subst y.
          eapply Hirr. exact Hlinay. }
    - (* (ef x /\ elim y) and (elim y /\ ef x) - symmetric *)
      exfalso.
      (* ef_el x y with (ef x /\ elim y) is cases 3-4 *)
      (* ef_el y x with (elim y /\ ef x) is cases 1-2 *)
      destruct Hxy as [Hcontra|[Hcontra|[(? & ? & Hposx)|(_ & _ & [a [Hposa Hlinxa]])]]];
      [destruct Hcontra as (? & Hef & _); apply el_then_not_ef in Hefx; done
      |destruct Hcontra as (? & Hef & _); apply el_then_not_ef in Hefx; done| |].
      { destruct Hyx as [(? & ? & Hnopos)|[(? & ? & [b [Hposb Hlinbx]])|[Hcontra|Hcontra]]];
        [| |destruct Hcontra as (_ & Hef & _); apply el_then_not_ef in Hef; done
         |destruct Hcontra as (_ & Hef & _); apply el_then_not_ef in Hef; done].
        - destruct Hposx as (Hef_x & ? & Hprex & _).
          apply (Hnopos x); done.
        - pose proof (one_el_pos x y b Hposx Hposb) as Heq. subst b.
          destruct ef_linearizable_def as [[Hwf _ _ _] _].
          destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
          eapply Hirr. exact Hlinbx. }
      { destruct Hyx as [(? & ? & Hnopos)|[(? & ? & [b [Hposb Hlinbx]])|[Hcontra|Hcontra]]];
        [| |destruct Hcontra as (_ & Hef & _); apply el_then_not_ef in Hef; done
         |destruct Hcontra as (_ & Hef & _); apply el_then_not_ef in Hef; done].
        - destruct Hposa as (Hef_a & ? & Hprea & _).
          apply (Hnopos a); done.
        - pose proof (one_el_pos a y b Hposa Hposb) as Heq. subst b.
          destruct ef_linearizable_def as [[Hwf _ _ _] _].
          destruct Hwf as [_ Hanti Hirr _ _ _ _ _ _].
          pose proof (Hanti x a Hlinxa Hlinbx) as Heq. subst a.
          eapply Hirr. exact Hlinxa. }
    - (* (ef x /\ elim y) and (ef y /\ elim x) *)
      exfalso. apply el_then_not_ef in Hely. done.
  Qed.

  (* elimination_stack.thy:468-527 - el_el *)
  Definition el_el : relation operation :=
    fun x y => elim pre val x /\ elim pre val y /\
      ( val x y \/
        (~ (exists a, el_pos a x) /\ (exists b, el_pos b y)) \/
        (~ (exists a, el_pos a x) /\ ~ (exists b, el_pos b y) /\ (exists c, ~ el_pre c x /\ el_pre c y)) \/
        (~ (exists a, el_pos a x) /\ ~ (exists b, el_pos b y) /\ (forall c, el_pre c x -> el_pre c y) /\ minf x y) \/
        (exists a b, el_pos a x /\ el_pos b y /\ lin a b) \/
        (exists a, el_pos a x /\ el_pos a y /\ (exists c, el_pos a c /\ ~ el_pre c x /\ el_pre c y)) \/
        ((exists a, el_pos a x /\ el_pos a y /\ (forall c, el_pos a c /\ el_pre c x -> el_pre c y)) /\ minf x y)
      ).

  Lemma el_elD x y :
    el_el x y ->
    elim pre val x /\ elim pre val y /\
      ( val x y \/
        (~ (exists a, el_pos a x) /\ (exists b, el_pos b y)) \/
        (~ (exists a, el_pos a x) /\ ~ (exists b, el_pos b y) /\ (exists c, ~ el_pre c x /\ el_pre c y)) \/
        (~ (exists a, el_pos a x) /\ ~ (exists b, el_pos b y) /\ (forall c, el_pre c x -> el_pre c y) /\ minf x y) \/
        (exists a b, el_pos a x /\ el_pos b y /\ lin a b) \/
        (exists a, el_pos a x /\ el_pos a y /\ (exists c, el_pos a c /\ ~ el_pre c x /\ el_pre c y)) \/
        ((exists a, el_pos a x /\ el_pos a y /\ (forall c, el_pos a c /\ el_pre c x -> el_pre c y)) /\ minf x y)
      ).
  Proof. done. Qed.

  Lemma el_elI1 x y : elim pre val x -> elim pre val y -> val x y -> el_el x y.
  Proof. intros Hx Hy Hval. split; [|split]; [done|done|left; done]. Qed.

  Lemma el_elI2 x y b : elim pre val x -> elim pre val y -> ~ (exists a, el_pos a x) -> el_pos b y -> el_el x y.
  Proof. intros Hx Hy Hnpos Hpos. split; [|split]; [done|done|right; left; split; [done|exists b; done]]. Qed.

  Lemma el_elI3 x y c : elim pre val x -> elim pre val y -> ~ (exists a, el_pos a x) -> ~ (exists b, el_pos b y) -> ~ el_pre c x -> el_pre c y -> el_el x y.
  Proof. intros Hx Hy Hnposx Hnposy Hnpre Hpre. split; [|split]; [done|done|do 2 right; left; split; [|split; [|exists c]]; done]. Qed.

  Lemma el_elI4 x y : elim pre val x -> elim pre val y -> ~ (exists a, el_pos a x) -> ~ (exists b, el_pos b y) -> (forall c, el_pre c x -> el_pre c y) -> minf x y -> el_el x y.
  Proof. intros Hx Hy Hnposx Hnposy Hpre Hminf. split; [|split]; [done|done|do 3 right; left; done]. Qed.

  Lemma el_elI5 x y a b : elim pre val x -> elim pre val y -> el_pos a x -> el_pos b y -> lin a b -> el_el x y.
  Proof. intros Hx Hy Hposx Hposy Hlin. split; [|split]; [done|done|do 4 right; left; exists a, b; done]. Qed.

  Lemma el_elI6 x y a : elim pre val x -> elim pre val y -> el_pos a x -> el_pos a y -> (exists c, el_pos a c /\ ~ el_pre c x /\ el_pre c y) -> el_el x y.
  Proof. intros Hx Hy Hposx Hposy Hc. split; [|split]; [done|done|do 5 right; left; exists a; done]. Qed.

  Lemma el_elI7 x y a : elim pre val x -> elim pre val y -> el_pos a x -> el_pos a y -> (forall c, el_pos a c /\ el_pre c x -> el_pre c y) -> minf x y -> el_el x y.
  Proof. intros Hx Hy Hposx Hposy Hc Hminf. split; [|split]; [done|done|do 6 right; split; [exists a|]; done]. Qed.

  Lemma el_el_then_el_and_el a b : el_el a b -> elim pre val a /\ elim pre val b.
  Proof. intros (Ha & Hb & _). done. Qed.

  Lemma el_el_total x y : elim pre val x -> elim pre val y -> x = y \/ el_el x y \/ el_el y x.
  Proof.
    intros Helx Hely.
    destruct (decide (x = y)) as [Heq|Hneq]; [by left|right].
    destruct (decide (same_val val x y)) as [Hsv|Hnsv].
    { (* same_val x y *)
      destruct (same_valD x y Hsv) as [Hval|Hval].
      - left. apply el_elI1; done.
      - right. apply el_elI1; done. }
    (* ~same_val x y *)
    destruct (decide (exists a, el_pos a x)) as [[a Hposa]|Hnposa].
    - (* exists el_pos a x *)
      destruct (decide (exists b, el_pos b y)) as [[b Hposb]|Hnposb].
      + (* exists el_pos b y *)
        destruct (el_posD a x Hposa) as (Hefa & _ & _ & _).
        destruct (el_posD b y Hposb) as (Hefb & _ & _ & _).
        destruct (decide (a = b)) as [Heqab|Hneqab].
        * (* a = b - same position *)
          subst b.
          (* Check el_pre subsumption *)
          destruct (decide (forall c, el_pos a c /\ el_pre c x -> el_pre c y)) as [Hsubxy|Hnsubxy].
          { (* el_pre x implies el_pre y *)
            destruct (decide (minf x y)) as [Hmxy|Hnmxy].
            - left. apply (el_elI7 x y a Helx Hely Hposa Hposb Hsubxy Hmxy).
            - (* ~minf x y *)
              destruct (decide (forall c, el_pos a c /\ el_pre c y -> el_pre c x)) as [Hsubyx|Hnsubyx].
              + (* el_pre y implies el_pre x *)
                destruct (decide (minf y x)) as [Hmyx|Hnmyx].
                ++ right. apply (el_elI7 y x a Hely Helx Hposb Hposa Hsubyx Hmyx).
                ++ (* ~minf x y and ~minf y x *)
                   (* By not_minf_then_same_val, same_val x y, contradiction *)
                   exfalso. apply Hnsv.
                   assert (Hppx : is_push val x \/ is_pop val x).
                   { destruct Helx as [[Hp|Hp] _]; [left|right]; done. }
                   assert (Hppy : is_push val y \/ is_pop val y).
                   { destruct Hely as [[Hp|Hp] _]; [left|right]; done. }
                   destruct (not_minf_then_same_val x y Hnmxy Hnmyx Hppx Hppy) as [?|?]; done.
              + (* ~(el_pre y implies el_pre x) *)
                left. apply (el_elI6 x y a Helx Hely Hposa Hposb).
                destruct (decide (exists c, (el_pos a c /\ el_pre c y) /\ ~ el_pre c x))
                  as [(c & [Hposc Hprecy] & Hnprecx)|Hno].
                { exists c. split; [|split]; done. }
                exfalso. apply Hnsubyx. intros c Hc.
                destruct (decide (el_pre c x)); naive_solver. }
          { (* ~(el_pre x implies el_pre y) *)
            right. apply (el_elI6 y x a Hely Helx Hposb Hposa).
            destruct (decide (exists c, (el_pos a c /\ el_pre c x) /\ ~ el_pre c y))
              as [(c & [Hposc Hprecx] & Hnprecy)|Hno].
            { exists c. split; [|split]; done. }
            exfalso. apply Hnsubxy. intros c Hc.
            destruct (decide (el_pre c y)); naive_solver. }
        * (* a ≠ b - different positions, use lin totality *)
          assert (Hppx : is_push (elim_free_val pre val) a ∨ is_pop (elim_free_val pre val) a).
          { destruct (ef_then_push_or_pop a Hefa) as [[d Had]|[d Hda]].
            - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
            - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
          assert (Hppy : is_push (elim_free_val pre val) b ∨ is_pop (elim_free_val pre val) b).
          { destruct (ef_then_push_or_pop b Hefb) as [[d Hbd]|[d Hdb]].
            - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
            - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
          destruct ef_linearizable_def as [Hseq _].
          destruct Hseq as [_ Htotpush Htotpop Htotpp].
          assert (Hlinord : lin a b ∨ lin b a).
          { destruct Hppx as [[da Hada]|[da Hdaa]];
            destruct Hppy as [[db Hbdb]|[db Hdbb]].
            - apply (Htotpush a b); [exists da|exists db|]; done.
            - apply (Htotpp a b); [exists da|exists db]; done.
            - destruct (Htotpp b a) as [Hba|Hab]; [exists db|exists da|right|left]; done.
            - apply (Htotpop a b); [exists da|exists db|]; done. }
          destruct Hlinord as [Hlinab|Hlinba].
          { left. apply (el_elI5 x y a b Helx Hely Hposa Hposb Hlinab). }
          { right. apply (el_elI5 y x b a Hely Helx Hposb Hposa Hlinba). }
      + (* ~exists el_pos b y *)
        right. apply (el_elI2 y x a Hely Helx Hnposb Hposa).
    - (* ~exists el_pos a x *)
      destruct (decide (exists b, el_pos b y)) as [[b Hposb]|Hnposb].
      + (* exists el_pos b y *)
        left. apply (el_elI2 x y b Helx Hely Hnposa Hposb).
      + (* ~exists el_pos for x or y - use el_elI3/el_elI4 with minf *)
        destruct (elD x wf_history Helx) as (rx & Hsvrx & _).
        destruct (elD y wf_history Hely) as (ry & Hsvry & _).
        (* Check if el_pre conditions differ *)
        destruct (decide (exists c, ~ el_pre c x /\ el_pre c y)) as [[c [Hnx Hy]]|Hnxy].
        { (* exists c with ~el_pre c x and el_pre c y - use el_elI3 *)
          left. apply (el_elI3 x y c Helx Hely Hnposa Hnposb Hnx Hy). }
        destruct (decide (exists c, el_pre c x /\ ~ el_pre c y)) as [[c [Hx Hny]]|Hnyx].
        { (* exists c with el_pre c x and ~el_pre c y - use el_elI3 symmetric *)
          right. apply (el_elI3 y x c Hely Helx Hnposb Hnposa Hny Hx). }
        (* el_pre are equivalent - use el_elI4 with minf *)
        destruct (always_minf x rx y ry Hsvrx Hsvry Hneq Hnsv) as [Hmxy|Hmyx].
        * (* minf x y *)
          left. apply (el_elI4 x y Helx Hely Hnposa Hnposb).
          -- intros c Hprecx.
             destruct (decide (el_pre c y)) as [Hprecy|Hnprecy]; [done|].
             exfalso. apply Hnyx. exists c. done.
          -- done.
        * (* minf y x *)
          right. apply (el_elI4 y x Hely Helx Hnposb Hnposa).
          -- intros c Hprecy.
             destruct (decide (el_pre c x)) as [Hprecx|Hnprecx]; [done|].
             exfalso. apply Hnxy. exists c. done.
          -- done.
  Qed.

  Lemma lem_pr_in_el_el_help x y a b :
    WellformedHistory pre val ->
    elim pre val x -> elim pre val y -> pre x y -> el_pos a x -> el_pos b y -> a = b \/ lin a b.
  Proof.
    intros Hwf Helx Hely Hprexy Hposa Hposb.
    destruct (el_posD a x Hposa) as (Hefa & _ & Hpreax & _).
    destruct (el_preD1 a x Hpreax) as (c & Hsvc & Hpreaorx).
    (* First establish pre a y *)
    assert (Hpreay : pre a y).
    { destruct Hpreaorx as [Hpreax'|Hpreac].
      - destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
        eapply Htrans; done.
      - destruct (pre_abcd_assumption a c x y Hpreac Hprexy) as [Hpreay|Hprexc].
        + done.
        + exfalso. destruct (elD x Hwf Helx) as (d & Hsvd & Hnprexd & _).
          pose proof (same_val_unique x c d Hwf Hsvc Hsvd) as Heq. subst d.
          apply Hnprexd. done. }
    (* Now apply pr_in_ef_el_help2 *)
    apply (pr_in_ef_el_help2 a y b Hefa Hely Hpreay Hposb).
  Qed.

  Lemma lem_pr_in_el_el_help2 x y a :
    WellformedHistory pre val ->
    elim pre val x -> elim pre val y -> pre x y -> el_pos a x -> exists b, el_pos b y.
  Proof.
    intros Hwf Helx Hely Hprexy Hposa.
    destruct (el_posD a x Hposa) as (Hefa & _ & Hpreax & _).
    destruct (el_preD1 a x Hpreax) as (c & Hsvc & Hpreaorx).
    (* First establish pre a y *)
    assert (Hpreay : pre a y).
    { destruct Hpreaorx as [Hpreax'|Hpreac].
      - destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
        eapply Htrans; done.
      - destruct (pre_abcd_assumption a c x y Hpreac Hprexy) as [Hpreay|Hprexc].
        + done.
        + exfalso. destruct (elD x Hwf Helx) as (d & Hsvd & Hnprexd & _).
          pose proof (same_val_unique x c d Hwf Hsvc Hsvd) as Heq. subst d.
          apply Hnprexd. done. }
    (* By pr_in_ef_el_help, there must exist el_pos to y *)
    destruct (decide (exists b, el_pos b y)) as [Hex|Hnex]; [done|].
    exfalso. apply (pr_in_ef_el_help a y Hefa Hely Hpreay Hnex).
  Qed.

  Lemma lem_pr_in_el_el x y :
    WellformedHistory pre val ->
    elim pre val x -> elim pre val y -> pre x y -> el_el x y.
  Proof.
    intros Hwf Helx Hely Hprexy.
    (* Case: x = y - contradiction with pre irreflexive *)
    destruct (decide (x = y)) as [Heq|Hneq].
    { subst y. destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
      exfalso. by eapply Hirr. }
    (* Case: same_val x y *)
    destruct (decide (same_val val x y)) as [Hsv|Hnsv].
    { destruct (same_valD x y Hsv) as [Hval|Hval].
      - apply el_elI1; done.
      - exfalso. eapply def_val_then_not_pr; [exact Hval|exact Hprexy]. }
    (* Case: ~same_val x y *)
    destruct (decide (exists a, el_pos a x)) as [[a Hposa]|Hnposa].
    - (* exists a, el_pos a x *)
      destruct (decide (exists b, el_pos b y)) as [[b Hposb]|Hnposb].
      + (* exists b, el_pos b y *)
        destruct (lem_pr_in_el_el_help x y a b Hwf Helx Hely Hprexy Hposa Hposb) as [Heqab|Hlinab].
        * (* a = b *)
          subst b.
          apply (el_elI6 x y a Helx Hely Hposa Hposb).
          exists x. split; [|split].
          -- done.
          -- (* ~el_pre x x *)
             intros (c & Hsvc & Hprex).
             destruct (elD x Hwf Helx) as (d & Hsvd & Hnprexd & _).
             pose proof (same_val_unique x c d Hwf Hsvc Hsvd) as Heq. subst d.
             destruct Hprex as [Hprexx|Hprexc].
             ++ destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
                by eapply Hirr.
             ++ apply Hnprexd. done.
          -- (* el_pre x y *)
             destruct (elD y Hwf Hely) as (c & Hsvc & _).
             apply (el_preI1 y c x Hsvc). left. done.
        * (* lin a b *)
          apply (el_elI5 x y a b Helx Hely Hposa Hposb Hlinab).
      + (* ~ exists b, el_pos b y - contradiction *)
        exfalso. apply Hnposb. apply (lem_pr_in_el_el_help2 x y a Hwf Helx Hely Hprexy Hposa).
    - (* ~ exists a, el_pos a x *)
      destruct (decide (exists b, el_pos b y)) as [[b Hposb]|Hnposb].
      + (* exists b, el_pos b y *)
        apply (el_elI2 x y b Helx Hely Hnposa Hposb).
      + (* ~ exists b, el_pos b y - use el_elI3 with c = x *)
        apply (el_elI3 x y x Helx Hely Hnposa Hnposb).
        * (* ~el_pre x x *)
          intros (c & Hsvc & Hprex).
          destruct (elD x Hwf Helx) as (d & Hsvd & Hnprexd & _).
          pose proof (same_val_unique x c d Hwf Hsvc Hsvd) as Heq. subst d.
          destruct Hprex as [Hprexx|Hprexc].
          -- destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
             by eapply Hirr.
          -- apply Hnprexd. done.
        * (* el_pre x y *)
          destruct (elD y Hwf Hely) as (c & Hsvc & _).
          apply (el_preI1 y c x Hsvc). left. done.
  Qed.

  Lemma lem_position_exists ia ra :
    val ia ra -> ~ pre ia ra ->
    (forall a, elim_free pre val a -> ~ pre a ia /\ ~ pre a ra) \/
    (exists a, elim_free pre val a /\ (pre a ia \/ pre a ra) /\
      (forall b, elim_free pre val b /\ lin a b -> ~ pre b ia /\ ~ pre b ra)).
  Proof.
    intros Hval Hnpre.
    destruct finite_set_def as [enum [Hnodup Henum]].
    assert (Hmain :
      (forall a, elim_free pre val a -> a ∈ enum -> ~ pre a ia /\ ~ pre a ra) \/
      (exists a, elim_free pre val a /\ a ∈ enum /\ (pre a ia \/ pre a ra) /\
        (forall b, elim_free pre val b /\ b ∈ enum /\ lin a b -> ~ pre b ia /\ ~ pre b ra))).
    { clear Henum.
      induction enum as [|x xs IH].
      - left. intros a _ Ha. inversion Ha.
      - apply NoDup_cons in Hnodup. destruct Hnodup as [Hxnin Hnodup'].
        specialize (IH Hnodup').
        destruct (decide (elim_free pre val x /\ (pre x ia \/ pre x ra))) as [[Hefx Hprex]|Hnx].
        + (* x is ef and has pre to ia or ra *)
          destruct IH as [Hnoef|[a (Hefa & Hain & Hprea & Hmina)]].
          * (* No previous ef element has pre to ia or ra *)
            right. exists x. split; [done|split; [by left|split; [done|]]].
            intros b (Hefb & Hbin & Hlinxb).
            apply elem_of_cons in Hbin.
            destruct Hbin as [Heq|Hbxs].
            -- subst b.
               destruct ef_linearizable_def as [Hseq _].
               destruct Hseq as [Hwflin _ _ _].
               destruct Hwflin as [_ _ Hirr _ _ _ _ _ _].
               exfalso. by eapply Hirr.
            -- apply Hnoef; done.
          * (* a is minimal in xs *)
            destruct (decide (x = a)) as [Heq|Hneq].
            -- subst x. right. exists a. split; [done|split; [by left|split; [done|]]].
               intros b (Hefb & Hbin & Hlinab).
               apply elem_of_cons in Hbin.
               destruct Hbin as [Heq|Hbxs].
               ++ subst b.
                  destruct ef_linearizable_def as [Hseq _].
                  destruct Hseq as [Hwflin _ _ _].
                  destruct Hwflin as [_ _ Hirr _ _ _ _ _ _].
                  exfalso. by eapply Hirr.
               ++ apply Hmina. split; [|split]; done.
            -- (* x ≠ a: compare in lin order *)
               assert (Hppx : is_push (elim_free_val pre val) x ∨ is_pop (elim_free_val pre val) x).
               { destruct (ef_then_push_or_pop x Hefx) as [[d Hxd]|[d Hdx]].
                 - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
                 - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
               assert (Hppa : is_push (elim_free_val pre val) a ∨ is_pop (elim_free_val pre val) a).
               { destruct (ef_then_push_or_pop a Hefa) as [[d Had]|[d Hda]].
                 - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
                 - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
               destruct ef_linearizable_def as [Hseq _].
               destruct Hseq as [Hwflin Htotpush Htotpop Htotpp].
               assert (Hlinord : lin x a ∨ lin a x).
               { destruct Hppx as [[dx Hxdx]|[dx Hdxx]];
                 destruct Hppa as [[da Hada]|[da Hdaa]].
                 - apply (Htotpush x a); [exists dx|exists da|]; done.
                 - apply (Htotpp x a); [exists dx|exists da]; done.
                 - destruct (Htotpp a x) as [Hax|Hxa]; [exists da|exists dx|right|left]; done.
                 - apply (Htotpop x a); [exists dx|exists da|]; done. }
               destruct Hlinord as [Hlinxa|Hlinax].
               ++ (* lin x a: a stays minimal *)
                  right. exists a. split; [done|split; [by right|split; [done|]]].
                  intros b (Hefb & Hbin & Hlinab).
                  apply elem_of_cons in Hbin.
                  destruct Hbin as [Hbeq|Hbxs].
                  ** subst b.
                     destruct Hwflin as [_ Hanti _ _ _ _ _ _ _].
                     pose proof (Hanti x a Hlinxa Hlinab) as Heq. done.
                  ** apply Hmina. split; [|split]; done.
               ++ (* lin a x: x becomes minimal *)
                  right. exists x. split; [done|split; [by left|split; [done|]]].
                  intros b (Hefb & Hbin & Hlinxb).
                  apply elem_of_cons in Hbin.
                  destruct Hbin as [Hbeq|Hbxs].
                  ** subst b.
                     destruct Hwflin as [_ _ Hirr _ _ _ _ _ _].
                     exfalso. by eapply Hirr.
                  ** destruct (decide (lin a b)) as [Hlinab|Hnlinab].
                     --- apply Hmina. split; [|split]; done.
                     --- destruct (decide (b = a)) as [Hbaeq|Hbaneq].
                         +++ subst b.
                             destruct Hwflin as [_ Hanti _ _ _ _ _ _ _].
                             pose proof (Hanti x a Hlinxb Hlinax) as Heq. done.
                         +++ assert (Hppb : is_push (elim_free_val pre val) b ∨ is_pop (elim_free_val pre val) b).
                             { destruct (ef_then_push_or_pop b Hefb) as [[d Hbd]|[d Hdb]].
                               - left. apply lem_is_push_ef_then_is_ef_push; [exists d|]; done.
                               - right. apply lem_is_pop_ef_then_is_ef_pop; [exists d|]; done. }
                             destruct Hwflin as [Htrans Hanti _ _ _ _ _ _ _].
                             assert (Hlinba : lin b a).
                             { destruct Hppb as [[db Hbdb]|[db Hdbb]];
                               destruct Hppa as [[da Hada]|[da Hdaa]].
                               - destruct (Htotpush b a (ex_intro _ db Hbdb) (ex_intro _ da Hada) Hbaneq); done.
                               - destruct (Htotpp b a (ex_intro _ db Hbdb) (ex_intro _ da Hdaa)); done.
                               - destruct (Htotpp a b (ex_intro _ da Hada) (ex_intro _ db Hdbb)); done.
                               - destruct (Htotpop b a (ex_intro _ db Hdbb) (ex_intro _ da Hdaa) Hbaneq); done. }
                             pose proof (Htrans b a x Hlinba Hlinax) as Hlinbx.
                             pose proof (Hanti x b Hlinxb Hlinbx) as Heq.
                             subst b. exfalso. apply Hxnin. done.
        + (* x is not ef or doesn't have pre to ia or ra *)
          destruct IH as [Hnoef|[a (Hefa & Hain & Hprea & Hmina)]].
          * left. intros y Hefy Hyin.
            apply elem_of_cons in Hyin.
            destruct Hyin as [Heq|Hyxs].
            -- subst y. split; intros Hprey; apply Hnx; split; [done|left; done|done|right; done].
            -- apply Hnoef; done.
          * right. exists a. split; [done|split; [by right|split; [done|]]].
            intros b (Hefb & Hbin & Hlinab).
            apply elem_of_cons in Hbin.
            destruct Hbin as [Hbeq|Hbxs].
            -- subst b. split; intros Hpreb; apply Hnx; split; [done|left; done|done|right; done].
            -- apply Hmina. split; [|split]; done. }
    destruct Hmain as [Hcase1|[a (Hefa & Hain & Hprea & Hmina)]].
    - left. intros a Hefa. apply Hcase1; [done|apply Henum; done].
    - right. exists a. split; [done|split; [done|]].
      intros b [Hefb Hlinab].
      apply Hmina. split; [|split]; [done|apply Henum; done|done].
  Qed.

  Lemma val_then_el_pre x y a : same_val val x y -> el_pre a x -> el_pre a y.
  Proof.
    intros Hsv (c & Hsvc & Hpre).
    pose proof (same_val_unique x c y wf_history Hsvc Hsv) as Heq. subst c.
    exists x. split.
    - apply same_val_commutative. done.
    - destruct Hpre; [right|left]; done.
  Qed.

  Lemma val_then_el_pos1 x y a :
    WellformedHistory pre val ->
    same_val val x y -> el_pos a x -> el_pos a y.
  Proof.
    intros Hwf Hsv (Hefa & Helx & Hprex & Hcond).
    split; [|split; [|split]].
    - done.
    - (* elim pre val y *)
      destruct (elD x Hwf Helx) as (b & Hsvxb & Hnpre1 & Hnpre2).
      pose proof (same_val_unique x b y Hwf Hsvxb Hsv) as Heq. subst b.
      split.
      + destruct Hsv as [Hxy|Hyx].
        * right. exists x. done.
        * left. exists x. done.
      + intros (c & Hsvc & Hprey).
        pose proof (same_val_unique y c x Hwf Hsvc (same_val_commutative x y Hsv)) as Heq. subst c.
        destruct Hprey as [Hyx|Hxy]; [apply Hnpre2|apply Hnpre1]; done.
    - (* el_pre a y - inline val_then_el_pre logic *)
      destruct Hprex as (c & Hsvc & Hpre).
      pose proof (same_val_unique x c y Hwf Hsvc Hsv) as Heq. subst c.
      exists x. split.
      + apply same_val_commutative. done.
      + destruct Hpre; [right|left]; done.
    - (* forall c, ... *)
      intros c [Hefc Hlinac] Hprey.
      apply (Hcond c (conj Hefc Hlinac)).
      destruct Hprey as (d & Hsvyd & Hpre).
      pose proof (same_val_unique y d x Hwf Hsvyd (same_val_commutative x y Hsv)) as Heq. subst d.
      exists y. split.
      + apply same_val_commutative. done.
      + destruct Hpre as [Hcy|Hcx]; [right|left]; done.
  Qed.

  Lemma val_then_el_pos2 x y a :
    WellformedHistory pre val ->
    same_val val x y -> el_pos a y -> el_pos a x.
  Proof.
    intros Hwf Hsv Hpos.
    eapply val_then_el_pos1; [done|apply same_val_commutative; done|done].
  Qed.

  Lemma el_el_irreflexive : Irreflexive el_el.
  Proof.
    intros x (Helx & Helx' & Hcases).
    destruct Hcases as [Hval|[Hcase2|[Hcase3|[Hcase4|[Hcase5|[Hcase6|Hcase7]]]]]].
    - (* val x x - contradicts val_order *)
      eapply def_val_order; [exact Hval|exists x; left; done].
    - (* (~ exists el_pos) /\ (exists el_pos) - direct contradiction *)
      destruct Hcase2 as [Hnpos [b Hpos]].
      apply Hnpos. exists b. done.
    - (* exists c, ~ el_pre c x /\ el_pre c x - contradiction *)
      destruct Hcase3 as (_ & _ & c & Hnpre & Hpre). done.
    - (* minf x x - false by irreflexivity *)
      destruct Hcase4 as (_ & _ & _ & Hminf).
      eapply minf_irreflexive. exact Hminf.
    - (* el_pos a x /\ el_pos b x /\ lin a b, but a = b by one_el_pos, so lin a a *)
      destruct Hcase5 as (a & b & Hposa & Hposb & Hlin).
      pose proof (one_el_pos a x b Hposa Hposb) as Heq. subst b.
      destruct ef_linearizable_def as [[Hwf _ _ _] _].
      destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
      eapply Hirr. exact Hlin.
    - (* exists c, el_pos a c /\ ~ el_pre c x /\ el_pre c x - contradiction *)
      destruct Hcase6 as (a & _ & _ & c & _ & Hnpre & Hpre). done.
    - (* minf x x - false by irreflexivity *)
      destruct Hcase7 as (_ & Hminf).
      eapply minf_irreflexive. exact Hminf.
  Qed.

  Lemma el_el_antisymmetric : Antisymmetric operation eq el_el.
  Proof.
    intros x y Hxy Hyx.
    destruct Hxy as (Helx & Hely & Hcasexy).
    destruct Hyx as (_ & _ & Hcaseyx).
    (* Case analysis on the 7 cases of each *)
    destruct Hcasexy as [Hvalxy|[Hcase2xy|[Hcase3xy|[Hcase4xy|[Hcase5xy|[Hcase6xy|Hcase7xy]]]]]].
    - (* el_el x y via val x y *)
      destruct Hcaseyx as [Hvalyx|[Hcase2yx|[Hcase3yx|[Hcase4yx|[Hcase5yx|[Hcase6yx|Hcase7yx]]]]]].
      + (* val y x - contradiction via val_order *)
        exfalso. eapply def_val_order. exact Hvalxy. exists y. left. done.
      + (* no el_pos y, el_pos to x *)
        destruct Hcase2yx as (Hnposy & [a Hposa]).
        pose proof (val_then_el_pos1 x y a wf_history (same_valI1 x y Hvalxy) Hposa) as Hposy.
        exfalso. apply Hnposy. exists a. done.
      + (* no el_pos y or x, exists c *)
        destruct Hcase3yx as (Hnposy & Hnposx & [c [Hnprecy Hprecx]]).
        (* c has el_pre to x. By val_then_el_pre, c also has el_pre to y *)
        pose proof (val_then_el_pre x y c (same_valI1 x y Hvalxy) Hprecx) as Hprecy.
        done.
      + (* no el_pos y or x, forall c, minf *)
        destruct Hcase4yx as (_ & _ & _ & Hminf).
        exfalso. apply (same_val_then_not_minf y x).
        * apply same_val_commutative. left. done.
        * done.
      + (* el_pos a y, el_pos b x, lin a b - contradiction via irrefl of lin *)
        destruct Hcase5yx as [a [b [Hposa [Hposb Hlinab]]]].
        pose proof (val_then_el_pos1 y x a wf_history (same_val_commutative x y (same_valI1 x y Hvalxy)) Hposa) as Hposx'.
        pose proof (one_el_pos a x b Hposx' Hposb) as Heq. subst b.
        (* Now we have lin a a which contradicts irrefl *)
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
        exfalso. eapply Hirr. exact Hlinab.
      + (* el_pos a y, el_pos a x, exists c - contradiction via val_then_el_pre *)
        destruct Hcase6yx as [a [Hposa [Hposx [c [Hposac [Hnprecy Hprecx]]]]]].
        (* c has el_pre to x but not y. val x y implies el_pre c y from el_pre c x *)
        pose proof (val_then_el_pre x y c (same_valI1 x y Hvalxy) Hprecx) as Hprecy.
        done.
      + (* el_pos a y, el_pos a x, forall c, minf *)
        destruct Hcase7yx as [[a [Hposa [Hposx _]]] Hminf].
        exfalso. apply (same_val_then_not_minf y x).
        * apply same_val_commutative. left. done.
        * done.
    - (* el_el x y via no el_pos x, el_pos to y *)
      destruct Hcase2xy as (Hnposx & [b Hposb]).
      destruct Hcaseyx as [Hvalyx|[Hcase2yx|[Hcase3yx|[Hcase4yx|[Hcase5yx|[Hcase6yx|Hcase7yx]]]]]].
      + (* val y x *)
        pose proof (val_then_el_pos1 y x b wf_history (same_valI1 y x Hvalyx) Hposb) as Hposx.
        exfalso. apply Hnposx. exists b. done.
      + (* no el_pos y, el_pos to x - contradicts Hnposx *)
        destruct Hcase2yx as (_ & [a Hposa]).
        exfalso. apply Hnposx. exists a. done.
      + (* no el_pos y or x *)
        destruct Hcase3yx as (Hnposy' & _ & _).
        exfalso. apply Hnposy'. exists b. done.
      + (* no el_pos y or x, forall, minf *)
        destruct Hcase4yx as (Hnposy' & _ & _ & _).
        exfalso. apply Hnposy'. exists b. done.
      + (* el_pos a y, el_pos b' x *)
        destruct Hcase5yx as [a [b' [Hposa [Hposb' _]]]].
        exfalso. apply Hnposx. exists b'. done.
      + (* el_pos a y, el_pos a x *)
        destruct Hcase6yx as [a [_ [Hposx _]]].
        exfalso. apply Hnposx. exists a. done.
      + (* el_pos a y, el_pos a x, forall, minf *)
        destruct Hcase7yx as [[a [_ [Hposx _]]] _].
        exfalso. apply Hnposx. exists a. done.
    - (* el_el x y via no el_pos x or y, exists c *)
      destruct Hcase3xy as (Hnposx & Hnposy & [c [Hnprecx Hprecy]]).
      destruct Hcaseyx as [Hvalyx|[Hcase2yx|[Hcase3yx|[Hcase4yx|[Hcase5yx|[Hcase6yx|Hcase7yx]]]]]].
      + (* val y x *)
        pose proof (val_then_el_pre y x c (same_valI1 y x Hvalyx) Hprecy) as Hprecx.
        done.
      + (* no el_pos y, el_pos to x *)
        destruct Hcase2yx as (_ & [a Hposa]).
        exfalso. apply Hnposx. exists a. done.
      + (* no el_pos y or x, exists c' *)
        destruct Hcase3yx as (_ & _ & [c' [Hnprecy' Hprecx']]).
        destruct (el_pre_abcd c y c' x Hprecy Hprecx') as [Hprecx|Hprecy'].
        * done.
        * done.
      + (* no el_pos y or x, forall, minf *)
        destruct Hcase4yx as (_ & _ & Himplic & _).
        pose proof (Himplic c Hprecy) as Hprecx.
        done.
      + (* el_pos a y, el_pos b x *)
        destruct Hcase5yx as [a [b [Hposa _]]].
        exfalso. apply Hnposy. exists a. done.
      + (* el_pos a y, el_pos a x *)
        destruct Hcase6yx as [a [Hposa _]].
        exfalso. apply Hnposy. exists a. done.
      + (* el_pos a y, el_pos a x, forall, minf *)
        destruct Hcase7yx as [[a [Hposa _]] _].
        exfalso. apply Hnposy. exists a. done.
    - (* el_el x y via no el_pos x or y, forall, minf x y *)
      destruct Hcase4xy as (Hnposx & Hnposy & Himplic & Hminfxy).
      destruct Hcaseyx as [Hvalyx|[Hcase2yx|[Hcase3yx|[Hcase4yx|[Hcase5yx|[Hcase6yx|Hcase7yx]]]]]].
      + (* val y x *)
        exfalso. apply (same_val_then_not_minf x y).
        * right. done.
        * done.
      + (* no el_pos y, el_pos to x *)
        destruct Hcase2yx as (_ & [a Hposa]).
        exfalso. apply Hnposx. exists a. done.
      + (* no el_pos y or x, exists c *)
        destruct Hcase3yx as (_ & _ & [c [Hnprecy Hprecx]]).
        pose proof (Himplic c Hprecx) as Hprecy.
        done.
      + (* no el_pos y or x, forall, minf y x *)
        destruct Hcase4yx as (_ & _ & _ & Hminfyx).
        apply (minf_antisymmetric x y Hminfxy Hminfyx).
      + (* el_pos a y, el_pos b x *)
        destruct Hcase5yx as [a [b [Hposa _]]].
        exfalso. apply Hnposy. exists a. done.
      + (* el_pos a y, el_pos a x *)
        destruct Hcase6yx as [a [Hposa _]].
        exfalso. apply Hnposy. exists a. done.
      + (* el_pos a y, el_pos a x, forall, minf *)
        destruct Hcase7yx as [[a [Hposa _]] _].
        exfalso. apply Hnposy. exists a. done.
    - (* el_el x y via el_pos a x, el_pos b y, lin a b *)
      destruct Hcase5xy as [a [b [Hposa [Hposb Hlinab]]]].
      destruct Hcaseyx as [Hvalyx|[Hcase2yx|[Hcase3yx|[Hcase4yx|[Hcase5yx|[Hcase6yx|Hcase7yx]]]]]].
      + (* val y x *)
        pose proof (val_then_el_pos1 x y a wf_history (same_val_commutative y x (same_valI1 y x Hvalyx)) Hposa) as Hposy.
        pose proof (one_el_pos a y b Hposy Hposb) as Heq. subst b.
        (* Now we have lin a a which contradicts irrefl *)
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
        exfalso. eapply Hirr. exact Hlinab.
      + (* no el_pos y, el_pos to x *)
        destruct Hcase2yx as (Hnposy & _).
        exfalso. apply Hnposy. exists b. done.
      + (* no el_pos y or x *)
        destruct Hcase3yx as (Hnposy & _ & _).
        exfalso. apply Hnposy. exists b. done.
      + (* no el_pos y or x, forall, minf *)
        destruct Hcase4yx as (Hnposy & _ & _ & _).
        exfalso. apply Hnposy. exists b. done.
      + (* el_pos a' y, el_pos b' x, lin a' b' - contradiction via antisymmetry of lin *)
        destruct Hcase5yx as [a' [b' [Hposa' [Hposb' Hlina'b']]]].
        pose proof (one_el_pos b y a' Hposb Hposa') as Heq1. subst a'.
        pose proof (one_el_pos a x b' Hposa Hposb') as Heq2. subst b'.
        (* Now we have lin a b and lin b a. By antisymmetry, a = b. Then lin a a contradicts irrefl. *)
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [_ Hanti Hirr _ _ _ _ _ _].
        pose proof (Hanti a b Hlinab Hlina'b') as Heq. subst b.
        exfalso. eapply Hirr. exact Hlinab.
      + (* el_pos a' y, el_pos a' x *)
        destruct Hcase6yx as [a' [Hposa' [Hposx _]]].
        pose proof (one_el_pos a x a' Hposa Hposx) as Heq. subst a'.
        (* Now Hposa' : el_pos a y. With Hposb : el_pos b y, we get a = b *)
        pose proof (one_el_pos a y b Hposa' Hposb) as Heq'. subst b.
        (* Now lin a a contradicts irrefl *)
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
        exfalso. eapply Hirr. exact Hlinab.
      + (* el_pos a' y, el_pos a' x, forall, minf *)
        destruct Hcase7yx as [[a' [Hposa' [Hposx _]]] _].
        pose proof (one_el_pos a x a' Hposa Hposx) as Heq. subst a'.
        pose proof (one_el_pos a y b Hposa' Hposb) as Heq'. subst b.
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
        exfalso. eapply Hirr. exact Hlinab.
    - (* el_el x y via el_pos a x, el_pos a y, exists c *)
      destruct Hcase6xy as [a [Hposa [Hposay [c [Hposac [Hnprecx Hprecy]]]]]].
      destruct Hcaseyx as [Hvalyx|[Hcase2yx|[Hcase3yx|[Hcase4yx|[Hcase5yx|[Hcase6yx|Hcase7yx]]]]]].
      + (* val y x *)
        pose proof (val_then_el_pre y x c (same_valI1 y x Hvalyx) Hprecy) as Hprecx.
        done.
      + (* no el_pos y *)
        destruct Hcase2yx as (Hnposy & _).
        exfalso. apply Hnposy. exists a. done.
      + (* no el_pos y or x *)
        destruct Hcase3yx as (Hnposy & _ & _).
        exfalso. apply Hnposy. exists a. done.
      + (* no el_pos y or x, forall, minf *)
        destruct Hcase4yx as (Hnposy & _ & _ & _).
        exfalso. apply Hnposy. exists a. done.
      + (* el_pos a' y, el_pos b' x, lin a' b' *)
        destruct Hcase5yx as [a' [b' [Hposa' [Hposb' Hlina'b']]]].
        pose proof (one_el_pos a y a' Hposay Hposa') as Heq1. subst a'.
        pose proof (one_el_pos a x b' Hposa Hposb') as Heq2. subst b'.
        (* Now lin a a contradicts irrefl *)
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
        exfalso. eapply Hirr. exact Hlina'b'.
      + (* el_pos a' y, el_pos a' x, exists c' *)
        destruct Hcase6yx as [a' [Hposa' [Hposx' [c' [Hposac' [Hnprec'y Hprec'x]]]]]].
        pose proof (one_el_pos a x a' Hposa Hposx') as Heq. subst a'.
        (* From case 6 xy: ~ el_pre c x and el_pre c y *)
        (* From case 6 yx: ~ el_pre c' y and el_pre c' x *)
        (* By el_pre_abcd: el_pre c y -> el_pre c' x -> el_pre c x \/ el_pre c' y *)
        destruct (el_pre_abcd c y c' x Hprecy Hprec'x) as [Hcx|Hc'y].
        * exfalso. apply Hnprecx. done.
        * exfalso. apply Hnprec'y. done.
      + (* el_pos a' y, el_pos a' x, forall, minf *)
        destruct Hcase7yx as [[a' [Hposa' [Hposx' Hcond']]] _].
        pose proof (one_el_pos a x a' Hposa Hposx') as Heq. subst a'.
        (* Hcond' : forall d, el_pos a d /\ el_pre d y -> el_pre d x *)
        (* We have el_pos a c (Hposac) and el_pre c y (Hprecy), so Hcond' gives el_pre c x *)
        (* But Hnprecx says ~ el_pre c x *)
        pose proof (Hcond' c (conj Hposac Hprecy)) as Hprecx'.
        done.
    - (* el_el x y via el_pos a x, el_pos a y, forall, minf x y *)
      destruct Hcase7xy as [[a [Hposa [Hposay Himplic]]] Hminfxy].
      destruct Hcaseyx as [Hvalyx|[Hcase2yx|[Hcase3yx|[Hcase4yx|[Hcase5yx|[Hcase6yx|Hcase7yx]]]]]].
      + (* val y x *)
        exfalso. apply (same_val_then_not_minf x y).
        * right. done.
        * done.
      + (* no el_pos y *)
        destruct Hcase2yx as (Hnposy & _).
        exfalso. apply Hnposy. exists a. done.
      + (* no el_pos y or x *)
        destruct Hcase3yx as (Hnposy & _ & _).
        exfalso. apply Hnposy. exists a. done.
      + (* no el_pos y or x, forall, minf *)
        destruct Hcase4yx as (Hnposy & _ & _ & _).
        exfalso. apply Hnposy. exists a. done.
      + (* el_pos a' y, el_pos b' x, lin a' b' *)
        destruct Hcase5yx as [a' [b' [Hposa' [Hposb' Hlina'b']]]].
        pose proof (one_el_pos a y a' Hposay Hposa') as Heq1. subst a'.
        pose proof (one_el_pos a x b' Hposa Hposb') as Heq2. subst b'.
        (* Now lin a a contradicts irrefl *)
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
        exfalso. eapply Hirr. exact Hlina'b'.
      + (* el_pos a' y, el_pos a' x, exists c' *)
        destruct Hcase6yx as [a' [Hposa' [Hposx' [c' [Hposac' [Hnprec'y Hprec'x]]]]]].
        pose proof (one_el_pos a x a' Hposa Hposx') as Heq. subst a'.
        (* From case 7 xy: Himplic says forall c, el_pos a c /\ el_pre c x -> el_pre c y *)
        (* From case 6 yx: el_pos a c' and el_pre c' x, so by Himplic, el_pre c' y *)
        (* But Hnprec'y says ~ el_pre c' y *)
        pose proof (Himplic c' (conj Hposac' Hprec'x)) as Hprec'y.
        done.
      + (* el_pos a' y, el_pos a' x, forall, minf y x *)
        destruct Hcase7yx as [[a' [Hposa' [Hposx' _]]] Hminfyx].
        apply (minf_antisymmetric x y Hminfxy Hminfyx).
  Qed.

  Lemma val_not_el_pos_then_not_el_pos x y :
    WellformedHistory pre val ->
    same_val val x y -> ~ (exists a, el_pos a y) -> ~ (exists a, el_pos a x).
  Proof.
    intros Hwf Hsv Hnpos [a (Hefa & Helx & Hprex & Hcond)].
    apply Hnpos. exists a.
    split; [|split; [|split]].
    - done.
    - (* elim pre val y *)
      destruct (elD x Hwf Helx) as (b & Hsvxb & Hnpre1 & Hnpre2).
      pose proof (same_val_unique x b y Hwf Hsvxb Hsv) as Heq. subst b.
      split.
      + destruct Hsv as [Hxy|Hyx].
        * right. exists x. done.
        * left. exists x. done.
      + intros (c & Hsvc & Hprey).
        pose proof (same_val_unique y c x Hwf Hsvc (same_val_commutative x y Hsv)) as Heq. subst c.
        destruct Hprey as [Hyx|Hxy]; [apply Hnpre2|apply Hnpre1]; done.
    - (* el_pre a y - inline val_then_el_pre logic *)
      destruct Hprex as (c & Hsvc & Hpre).
      pose proof (same_val_unique x c y Hwf Hsvc Hsv) as Heq. subst c.
      exists x. split.
      + apply same_val_commutative. done.
      + destruct Hpre; [right|left]; done.
    - (* forall c, ... *)
      intros c [Hefc Hlinac] Hprey.
      apply (Hcond c (conj Hefc Hlinac)).
      destruct Hprey as (d & Hsvyd & Hpre).
      pose proof (same_val_unique y d x Hwf Hsvyd (same_val_commutative x y Hsv)) as Heq. subst d.
      exists y. split.
      + apply same_val_commutative. done.
      + destruct Hpre as [Hcy|Hcx]; [right|left]; done.
  Qed.

  Lemma val_minf_then_minf x y z : same_val val x y -> minf y z -> minf x z.
  Proof.
    intros Hsv (ra & rb & Hsvra & Hsvrb & Hlt).
    pose proof (same_val_unique y ra x wf_history Hsvra (same_val_commutative x y Hsv)) as Heq.
    subst ra.
    exists y, rb. split; [|split]; [done|done|].
    rewrite Nat.min_comm. done.
  Qed.

  Lemma val_minf_then_minf2 x y z : same_val val x y -> minf z y -> minf z x.
  Proof.
    intros Hsv (ra & rb & Hsvra & Hsvrb & Hlt).
    pose proof (same_val_unique y rb x wf_history Hsvrb (same_val_commutative x y Hsv)) as Heq.
    subst rb.
    exists ra, y. split; [|split]; [done|done|].
    rewrite (Nat.min_comm (f x) (f y)). done.
  Qed.

  Lemma el_el_transitive_help x y z a :
    same_val val y z ->
    (forall c, el_pos a c /\ el_pre c x -> el_pre c y) ->
    (forall c, el_pos a c /\ el_pre c x -> el_pre c z).
  Proof.
    intros Hsv Hpre c [Hpos Hprecx].
    specialize (Hpre c (conj Hpos Hprecx)).
    eapply val_then_el_pre; done.
  Qed.

  Lemma el_el_transitive : Transitive el_el.
  Proof.
    intros x y z Hxy Hyz.
    destruct (el_elD x y Hxy) as (Helx & Hely & Hcasesxy).
    destruct (el_elD y z Hyz) as (Hely' & Helz & Hcasesyz).
    destruct Hcasesxy as [Hvalxy|[Hcase2xy|[Hcase3xy|[Hcase4xy|[Hcase5xy|[Hcase6xy|Hcase7xy]]]]]];
    destruct Hcasesyz as [Hvalyz|[Hcase2yz|[Hcase3yz|[Hcase4yz|[Hcase5yz|[Hcase6yz|Hcase7yz]]]]]].
    (* Case 1-1: val x y, val y z *)
    - exfalso. eapply def_val_order; [exact Hvalxy|]. exists z. right. done.
    (* Case 1-2: val x y, ~el_pos y /\ el_pos z *)
    - destruct Hcase2yz as (Hnposy & [b Hposb]).
      assert (Hnposx : ~ exists a, el_pos a x).
      { intros [a Ha]. apply Hnposy.
        exists a. eapply val_then_el_pos1; [exact wf_history|exact (same_valI1 x y Hvalxy)|done]. }
      apply (el_elI2 x z b Helx Helz Hnposx Hposb).
    (* Case 1-3: val x y, ~el_pos y /\ ~el_pos z /\ exists c *)
    - destruct Hcase3yz as (Hnposy & Hnposz & [c [Hnprecy Hprecz]]).
      assert (Hnposx : ~ exists a, el_pos a x).
      { intros [a Ha]. apply Hnposy.
        exists a. eapply val_then_el_pos1; [exact wf_history|exact (same_valI1 x y Hvalxy)|done]. }
      apply (el_elI3 x z c Helx Helz Hnposx Hnposz).
      + intros Hprecx. apply Hnprecy.
        eapply val_then_el_pre; [exact (same_valI1 x y Hvalxy)|done].
      + done.
    (* Case 1-4: val x y, ~el_pos y /\ ~el_pos z /\ forall /\ minf *)
    - destruct Hcase4yz as (Hnposy & Hnposz & Hpre & Hminf).
      assert (Hnposx : ~ exists a, el_pos a x).
      { intros [a Ha]. apply Hnposy.
        exists a. eapply val_then_el_pos1; [exact wf_history|exact (same_valI1 x y Hvalxy)|done]. }
      apply (el_elI4 x z Helx Helz Hnposx Hnposz).
      + intros c Hprecx.
        pose proof (val_then_el_pre x y c (same_valI1 x y Hvalxy) Hprecx) as Hprecy.
        apply Hpre. done.
      + eapply val_minf_then_minf; [exact (same_valI1 x y Hvalxy)|done].
    (* Case 1-5: val x y, el_pos a y /\ el_pos b z /\ lin a b *)
    - destruct Hcase5yz as [a [b [Hposa [Hposb Hlin]]]].
      pose proof (val_then_el_pos2 x y a wf_history (same_valI1 x y Hvalxy) Hposa) as Hposx.
      apply (el_elI5 x z a b Helx Helz Hposx Hposb Hlin).
    (* Case 1-6: val x y, el_pos a y /\ el_pos a z /\ exists c *)
    - destruct Hcase6yz as [a [Hposa [Hposaz [c [Hposac [Hnprecy Hprecz]]]]]].
      pose proof (val_then_el_pos2 x y a wf_history (same_valI1 x y Hvalxy) Hposa) as Hposx.
      apply (el_elI6 x z a Helx Helz Hposx Hposaz).
      exists c. split; [|split]; [done| |done].
      intros Hprecx. apply Hnprecy.
      eapply val_then_el_pre; [exact (same_valI1 x y Hvalxy)|done].
    (* Case 1-7: val x y, el_pos a y /\ el_pos a z /\ forall /\ minf *)
    - destruct Hcase7yz as [[a [Hposa [Hposaz Hcond]]] Hminf].
      pose proof (val_then_el_pos2 x y a wf_history (same_valI1 x y Hvalxy) Hposa) as Hposx.
      pose proof (val_minf_then_minf x y z (same_valI1 x y Hvalxy) Hminf) as Hminfxz.
      apply (el_elI7 x z a Helx Helz Hposx Hposaz); [|done].
      intros c [Hposac Hprecx].
      pose proof (val_then_el_pre x y c (same_valI1 x y Hvalxy) Hprecx) as Hprecy.
      apply Hcond. done.
    (* Case 2-1: ~el_pos x /\ el_pos y, val y z *)
    - destruct Hcase2xy as (Hnposx & [b Hposb]).
      pose proof (val_then_el_pos1 y z b wf_history (same_valI1 y z Hvalyz) Hposb) as Hposz.
      apply (el_elI2 x z b Helx Helz Hnposx Hposz).
    (* Case 2-2: ~el_pos x /\ el_pos y, ~el_pos y /\ el_pos z *)
    - destruct Hcase2xy as (Hnposx & [b Hposb]).
      destruct Hcase2yz as (Hnposy & _).
      exfalso. apply Hnposy. exists b. done.
    (* Case 2-3: ~el_pos x /\ el_pos y, ~el_pos y /\ ~el_pos z /\ exists c *)
    - destruct Hcase2xy as (Hnposx & [b Hposb]).
      destruct Hcase3yz as (Hnposy & _).
      exfalso. apply Hnposy. exists b. done.
    (* Case 2-4: ~el_pos x /\ el_pos y, ~el_pos y /\ ~el_pos z /\ forall /\ minf *)
    - destruct Hcase2xy as (Hnposx & [b Hposb]).
      destruct Hcase4yz as (Hnposy & _).
      exfalso. apply Hnposy. exists b. done.
    (* Case 2-5: ~el_pos x /\ el_pos y, el_pos a y /\ el_pos b z /\ lin a b *)
    - destruct Hcase2xy as (Hnposx & [b' Hposb']).
      destruct Hcase5yz as [a [b [Hposa [Hposb Hlin]]]].
      pose proof (one_el_pos a y b' Hposa Hposb') as Heq. subst b'.
      apply (el_elI2 x z b Helx Helz Hnposx Hposb).
    (* Case 2-6: ~el_pos x /\ el_pos y, el_pos a y /\ el_pos a z /\ exists c *)
    - destruct Hcase2xy as (Hnposx & [b Hposb]).
      destruct Hcase6yz as [a [Hposa [Hposaz _]]].
      pose proof (one_el_pos a y b Hposa Hposb) as Heq. subst b.
      apply (el_elI2 x z a Helx Helz Hnposx Hposaz).
    (* Case 2-7: ~el_pos x /\ el_pos y, el_pos a y /\ el_pos a z /\ forall /\ minf *)
    - destruct Hcase2xy as (Hnposx & [b Hposb]).
      destruct Hcase7yz as [[a [Hposa [Hposaz _]]] _].
      pose proof (one_el_pos a y b Hposa Hposb) as Heq. subst b.
      apply (el_elI2 x z a Helx Helz Hnposx Hposaz).
    (* Case 3-1: ~el_pos x /\ ~el_pos y /\ exists c, val y z *)
    - destruct Hcase3xy as (Hnposx & Hnposy & [c [Hnprecx Hprecy]]).
      pose proof (val_then_el_pre y z c (same_valI1 y z Hvalyz) Hprecy) as Hprecz.
      apply (el_elI3 x z c Helx Helz Hnposx).
      + intros [a Ha]. apply Hnposy.
        pose proof (val_then_el_pos2 y z a wf_history (same_valI1 y z Hvalyz) Ha) as Hay.
        exists a. done.
      + done.
      + done.
    (* Case 3-2: ~el_pos x /\ ~el_pos y /\ exists c, ~el_pos y /\ el_pos z *)
    - destruct Hcase3xy as (Hnposx & Hnposy & _).
      destruct Hcase2yz as (Hnposy' & [b Hposb]).
      apply (el_elI2 x z b Helx Helz Hnposx Hposb).
    (* Case 3-3: ~el_pos x /\ ~el_pos y /\ exists c, ~el_pos y /\ ~el_pos z /\ exists c' *)
    - destruct Hcase3xy as (Hnposx & Hnposy & [c [Hnprecx Hprecy]]).
      destruct Hcase3yz as (Hnposy' & Hnposz & [c' [Hnprecy' Hprec'z]]).
      destruct (el_pre_abcd c y c' z Hprecy Hprec'z) as [Hprecz|Hprec'y].
      + apply (el_elI3 x z c Helx Helz Hnposx Hnposz Hnprecx Hprecz).
      + exfalso. apply Hnprecy'. done.
    (* Case 3-4: ~el_pos x /\ ~el_pos y /\ exists c, ~el_pos y /\ ~el_pos z /\ forall /\ minf *)
    - destruct Hcase3xy as (Hnposx & Hnposy & [c [Hnprecx Hprecy]]).
      destruct Hcase4yz as (Hnposy' & Hnposz & Hpre & Hminf).
      apply (el_elI3 x z c Helx Helz Hnposx Hnposz Hnprecx).
      apply Hpre. done.
    (* Case 3-5: ~el_pos x /\ ~el_pos y /\ exists c, el_pos a y /\ el_pos b z /\ lin a b *)
    - destruct Hcase3xy as (Hnposx & Hnposy & _).
      destruct Hcase5yz as [a [_ [Hposa _]]].
      exfalso. apply Hnposy. exists a. done.
    (* Case 3-6: ~el_pos x /\ ~el_pos y /\ exists c, el_pos a y /\ el_pos a z /\ exists c' *)
    - destruct Hcase3xy as (Hnposx & Hnposy & _).
      destruct Hcase6yz as [a [Hposa _]].
      exfalso. apply Hnposy. exists a. done.
    (* Case 3-7: ~el_pos x /\ ~el_pos y /\ exists c, el_pos a y /\ el_pos a z /\ forall /\ minf *)
    - destruct Hcase3xy as (Hnposx & Hnposy & _).
      destruct Hcase7yz as [[a [Hposa _]] _].
      exfalso. apply Hnposy. exists a. done.
    (* Case 4-1: ~el_pos x /\ ~el_pos y /\ forall /\ minf, val y z *)
    - destruct Hcase4xy as (Hnposx & Hnposy & Hpre & Hminf).
      apply (el_elI4 x z Helx Helz Hnposx).
      + intros [a Ha]. apply Hnposy.
        pose proof (val_then_el_pos2 y z a wf_history (same_valI1 y z Hvalyz) Ha) as Hay.
        exists a. done.
      + intros c Hprecx.
        pose proof (Hpre c Hprecx) as Hprecy.
        eapply val_then_el_pre; [exact (same_valI1 y z Hvalyz)|done].
      + (* minf x z from minf x y and same_val y z *)
        destruct Hminf as (ra & rb & Hsvra & Hsvrb & Hlt).
        pose proof (same_val_unique y rb z wf_history Hsvrb (same_valI1 y z Hvalyz)) as Heq.
        subst rb.
        exists ra, y. split; [|split]; [done|apply same_val_commutative; exact (same_valI1 y z Hvalyz)|].
        rewrite (Nat.min_comm (f z) (f y)). done.
    (* Case 4-2: ~el_pos x /\ ~el_pos y /\ forall /\ minf, ~el_pos y /\ el_pos z *)
    - destruct Hcase4xy as (Hnposx & Hnposy & Hpre & Hminf).
      destruct Hcase2yz as (_ & [b Hposb]).
      apply (el_elI2 x z b Helx Helz Hnposx Hposb).
    (* Case 4-3: ~el_pos x /\ ~el_pos y /\ forall /\ minf, ~el_pos y /\ ~el_pos z /\ exists c *)
    - destruct Hcase4xy as (Hnposx & Hnposy & Hpre & Hminf).
      destruct Hcase3yz as (_ & Hnposz & [c [Hnprecy Hprecz]]).
      apply (el_elI3 x z c Helx Helz Hnposx Hnposz).
      + intros Hprecx. apply Hnprecy. apply Hpre. done.
      + done.
    (* Case 4-4: ~el_pos x /\ ~el_pos y /\ forall /\ minf, ~el_pos y /\ ~el_pos z /\ forall /\ minf *)
    - destruct Hcase4xy as (Hnposx & Hnposy & Hprexy & Hminfxy).
      destruct Hcase4yz as (_ & Hnposz & Hpreyz & Hminfyz).
      apply (el_elI4 x z Helx Helz Hnposx Hnposz).
      + intros c Hprecx. apply Hpreyz. apply Hprexy. done.
      + eapply minf_transitive; done.
    (* Case 4-5: ~el_pos x /\ ~el_pos y /\ forall /\ minf, el_pos a y /\ el_pos b z /\ lin a b *)
    - destruct Hcase4xy as (Hnposx & Hnposy & _).
      destruct Hcase5yz as [a [_ [Hposa _]]].
      exfalso. apply Hnposy. exists a. done.
    (* Case 4-6: ~el_pos x /\ ~el_pos y /\ forall /\ minf, el_pos a y /\ el_pos a z /\ exists c *)
    - destruct Hcase4xy as (Hnposx & Hnposy & _).
      destruct Hcase6yz as [a [Hposa _]].
      exfalso. apply Hnposy. exists a. done.
    (* Case 4-7: ~el_pos x /\ ~el_pos y /\ forall /\ minf, el_pos a y /\ el_pos a z /\ forall /\ minf *)
    - destruct Hcase4xy as (Hnposx & Hnposy & _).
      destruct Hcase7yz as [[a [Hposa _]] _].
      exfalso. apply Hnposy. exists a. done.
    (* Case 5-1: el_pos a x /\ el_pos b y /\ lin a b, val y z *)
    - destruct Hcase5xy as [a [b [Hposa [Hposb Hlin]]]].
      pose proof (val_then_el_pos1 y z b wf_history (same_valI1 y z Hvalyz) Hposb) as Hposz.
      apply (el_elI5 x z a b Helx Helz Hposa Hposz Hlin).
    (* Case 5-2: el_pos a x /\ el_pos b y /\ lin a b, ~el_pos y /\ el_pos z *)
    - destruct Hcase5xy as [a [b [_ [Hposb _]]]].
      destruct Hcase2yz as (Hnposy & _).
      exfalso. apply Hnposy. exists b. done.
    (* Case 5-3: el_pos a x /\ el_pos b y /\ lin a b, ~el_pos y /\ ~el_pos z /\ exists c *)
    - destruct Hcase5xy as [a [b [_ [Hposb _]]]].
      destruct Hcase3yz as (Hnposy & _).
      exfalso. apply Hnposy. exists b. done.
    (* Case 5-4: el_pos a x /\ el_pos b y /\ lin a b, ~el_pos y /\ ~el_pos z /\ forall /\ minf *)
    - destruct Hcase5xy as [a [b [_ [Hposb _]]]].
      destruct Hcase4yz as (Hnposy & _).
      exfalso. apply Hnposy. exists b. done.
    (* Case 5-5: el_pos a x /\ el_pos b y /\ lin a b, el_pos a' y /\ el_pos b' z /\ lin a' b' *)
    - destruct Hcase5xy as [a [b [Hposa [Hposb Hlinab]]]].
      destruct Hcase5yz as [a' [b' [Hposa' [Hposb' Hlina'b']]]].
      pose proof (one_el_pos a' y b Hposa' Hposb) as Heq. subst b.
      destruct ef_linearizable_def as [[Hwf _ _ _] _].
      destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
      apply (el_elI5 x z a b' Helx Helz Hposa Hposb').
      eapply Htrans; done.
    (* Case 5-6: el_pos a x /\ el_pos b y /\ lin a b, el_pos a' y /\ el_pos a' z /\ exists c *)
    - destruct Hcase5xy as [a [b [Hposa [Hposb Hlinab]]]].
      destruct Hcase6yz as [a' [Hposa' [Hposa'z _]]].
      pose proof (one_el_pos a' y b Hposa' Hposb) as Heq. subst b.
      apply (el_elI5 x z a a' Helx Helz Hposa Hposa'z Hlinab).
    (* Case 5-7: el_pos a x /\ el_pos b y /\ lin a b, el_pos a' y /\ el_pos a' z /\ forall /\ minf *)
    - destruct Hcase5xy as [a [b [Hposa [Hposb Hlinab]]]].
      destruct Hcase7yz as [[a' [Hposa' [Hposa'z _]]] _].
      pose proof (one_el_pos a' y b Hposa' Hposb) as Heq. subst b.
      apply (el_elI5 x z a a' Helx Helz Hposa Hposa'z Hlinab).
    (* Case 6-1: el_pos a x /\ el_pos a y /\ exists c, val y z *)
    - destruct Hcase6xy as [a [Hposax [Hposay [c [Hposac [Hnprecx Hprecy]]]]]].
      pose proof (val_then_el_pos1 y z a wf_history (same_valI1 y z Hvalyz) Hposay) as Hposaz.
      pose proof (val_then_el_pre y z c (same_valI1 y z Hvalyz) Hprecy) as Hprecz.
      apply (el_elI6 x z a Helx Helz Hposax Hposaz).
      exists c. split; [|split]; done.
    (* Case 6-2: el_pos a x /\ el_pos a y /\ exists c, ~el_pos y /\ el_pos z *)
    - destruct Hcase6xy as [a [_ [Hposay _]]].
      destruct Hcase2yz as (Hnposy & _).
      exfalso. apply Hnposy. exists a. done.
    (* Case 6-3: el_pos a x /\ el_pos a y /\ exists c, ~el_pos y /\ ~el_pos z /\ exists c' *)
    - destruct Hcase6xy as [a [_ [Hposay _]]].
      destruct Hcase3yz as (Hnposy & _).
      exfalso. apply Hnposy. exists a. done.
    (* Case 6-4: el_pos a x /\ el_pos a y /\ exists c, ~el_pos y /\ ~el_pos z /\ forall /\ minf *)
    - destruct Hcase6xy as [a [_ [Hposay _]]].
      destruct Hcase4yz as (Hnposy & _).
      exfalso. apply Hnposy. exists a. done.
    (* Case 6-5: el_pos a x /\ el_pos a y /\ exists c, el_pos a' y /\ el_pos b z /\ lin a' b *)
    - destruct Hcase6xy as [a [Hposax [Hposay _]]].
      destruct Hcase5yz as [a' [b [Hposa' [Hposb Hlin]]]].
      pose proof (one_el_pos a y a' Hposay Hposa') as Heq. subst a'.
      apply (el_elI5 x z a b Helx Helz Hposax Hposb Hlin).
    (* Case 6-6: el_pos a x /\ el_pos a y /\ exists c, el_pos a' y /\ el_pos a' z /\ exists c' *)
    - destruct Hcase6xy as [a [Hposax [Hposay [c [Hposac [Hnprecx Hprecy]]]]]].
      destruct Hcase6yz as [a' [Hposa' [Hposa'z [c' [Hposac' [Hnprecy' Hprec'z]]]]]].
      pose proof (one_el_pos a y a' Hposay Hposa') as Heq. subst a'.
      destruct (el_pre_abcd c y c' z Hprecy Hprec'z) as [Hprecz|Hprec'y].
      + apply (el_elI6 x z a Helx Helz Hposax Hposa'z).
        exists c. split; [|split]; done.
      + exfalso. apply Hnprecy'. done.
    (* Case 6-7: el_pos a x /\ el_pos a y /\ exists c, el_pos a' y /\ el_pos a' z /\ forall /\ minf *)
    - destruct Hcase6xy as [a [Hposax [Hposay [c [Hposac [Hnprecx Hprecy]]]]]].
      destruct Hcase7yz as [[a' [Hposa' [Hposa'z Hcond]]] _].
      pose proof (one_el_pos a y a' Hposay Hposa') as Heq. subst a'.
      apply (el_elI6 x z a Helx Helz Hposax Hposa'z).
      exists c. split; [|split]; [done|done|].
      apply Hcond. split; done.
    (* Case 7-1: el_pos a x /\ el_pos a y /\ forall /\ minf, val y z *)
    - destruct Hcase7xy as [[a [Hposax [Hposay Hcond]]] Hminfxy].
      pose proof (val_then_el_pos1 y z a wf_history (same_valI1 y z Hvalyz) Hposay) as Hposaz.
      apply (el_elI7 x z a Helx Helz Hposax Hposaz).
      + intros c' [Hposac' Hprec'x].
        pose proof (Hcond c' (conj Hposac' Hprec'x)) as Hprec'y.
        eapply val_then_el_pre; [exact (same_valI1 y z Hvalyz)|done].
      + (* minf x z from minf x y and same_val y z *)
        destruct Hminfxy as (ra & rb & Hsvra & Hsvrb & Hlt).
        pose proof (same_val_unique y rb z wf_history Hsvrb (same_valI1 y z Hvalyz)) as Heq.
        subst rb.
        exists ra, y. split; [|split]; [done|apply same_val_commutative; exact (same_valI1 y z Hvalyz)|].
        rewrite (Nat.min_comm (f z) (f y)). done.
    (* Case 7-2: el_pos a x /\ el_pos a y /\ forall /\ minf, ~el_pos y /\ el_pos z *)
    - destruct Hcase7xy as [[a [_ [Hposay _]]] _].
      destruct Hcase2yz as (Hnposy & _).
      exfalso. apply Hnposy. exists a. done.
    (* Case 7-3: el_pos a x /\ el_pos a y /\ forall /\ minf, ~el_pos y /\ ~el_pos z /\ exists c *)
    - destruct Hcase7xy as [[a [_ [Hposay _]]] _].
      destruct Hcase3yz as (Hnposy & _).
      exfalso. apply Hnposy. exists a. done.
    (* Case 7-4: el_pos a x /\ el_pos a y /\ forall /\ minf, ~el_pos y /\ ~el_pos z /\ forall /\ minf *)
    - destruct Hcase7xy as [[a [_ [Hposay _]]] _].
      destruct Hcase4yz as (Hnposy & _).
      exfalso. apply Hnposy. exists a. done.
    (* Case 7-5: el_pos a x /\ el_pos a y /\ forall /\ minf, el_pos a' y /\ el_pos b z /\ lin a' b *)
    - destruct Hcase7xy as [[a [Hposax [Hposay _]]] _].
      destruct Hcase5yz as [a' [b [Hposa' [Hposb Hlin]]]].
      pose proof (one_el_pos a y a' Hposay Hposa') as Heq. subst a'.
      apply (el_elI5 x z a b Helx Helz Hposax Hposb Hlin).
    (* Case 7-6: el_pos a x /\ el_pos a y /\ forall /\ minf, el_pos a' y /\ el_pos a' z /\ exists c *)
    - destruct Hcase7xy as [[a [Hposax [Hposay Hcond]]] _].
      destruct Hcase6yz as [a' [Hposa' [Hposa'z [c [Hposac [Hnprecy Hprecz]]]]]].
      pose proof (one_el_pos a y a' Hposay Hposa') as Heq. subst a'.
      destruct (decide (el_pre c x)) as [Hprecx|Hnprecx].
      + pose proof (Hcond c (conj Hposac Hprecx)) as Hprecy.
        exfalso. apply Hnprecy. done.
      + apply (el_elI6 x z a Helx Helz Hposax Hposa'z).
        exists c. split; [|split]; done.
    (* Case 7-7: el_pos a x /\ el_pos a y /\ forall /\ minf, el_pos a' y /\ el_pos a' z /\ forall /\ minf *)
    - destruct Hcase7xy as [[a [Hposax [Hposay Hcondxy]]] Hminfxy].
      destruct Hcase7yz as [[a' [Hposa' [Hposa'z Hcondyz]]] Hminfyz].
      pose proof (one_el_pos a y a' Hposay Hposa') as Heq. subst a'.
      apply (el_elI7 x z a Helx Helz Hposax Hposa'z).
      + intros c [Hposac Hprecx].
        pose proof (Hcondxy c (conj Hposac Hprecx)) as Hprecy.
        apply Hcondyz. split; done.
      + eapply minf_transitive; done.
  Qed.

  Lemma ef_el_ef_then_lin x y z : elim_free pre val x -> elim pre val y -> elim_free pre val z -> ef_el x y -> ef_el y z -> lin x z.
  Proof.
    intros Hefx Hely Hefz Hxy Hyz.
    (* ef_el x y with ef x, el y comes from cases 3 or 4 *)
    destruct (ef_elD x y Hxy) as [Hcase1|[Hcase2|[Hcase3|Hcase4]]].
    - (* case 1: el x - but x is ef, contradiction *)
      destruct Hcase1 as (Helx & _ & _). exfalso. apply el_then_not_ef in Helx. done.
    - (* case 2: el x - contradiction *)
      destruct Hcase2 as (Helx & _ & _). exfalso. apply el_then_not_ef in Helx. done.
    - (* case 3: el_pos x y *)
      destruct Hcase3 as (_ & _ & Hposx).
      (* ef_el y z with el y, ef z comes from cases 1 or 2 *)
      destruct (ef_elD y z Hyz) as [Hcase1'|[Hcase2'|[Hcase3'|Hcase4']]].
      + (* case 1: forall a, ef a -> ~el_pre a y *)
        destruct Hcase1' as (_ & _ & Hnoelpre).
        destruct Hposx as (Hefx' & _ & Hprex & _).
        exfalso. apply (Hnoelpre x Hefx' Hprex).
      + (* case 2: exists a, el_pos a y ∧ lin a z *)
        destruct Hcase2' as (_ & _ & [a [Hposa Hlinaz]]).
        pose proof (one_el_pos x y a Hposx Hposa) as Heq. subst a.
        done.
      + (* case 3: el z - but z is ef, contradiction *)
        destruct Hcase3' as (Helz & _ & _). exfalso. apply el_then_not_ef in Helz. done.
      + (* case 4: el z - contradiction *)
        destruct Hcase4' as (Helz & _ & _). exfalso. apply el_then_not_ef in Helz. done.
    - (* case 4: exists a, el_pos a y ∧ lin x a *)
      destruct Hcase4 as (_ & _ & [a [Hposa Hlinxa]]).
      destruct (ef_elD y z Hyz) as [Hcase1'|[Hcase2'|[Hcase3'|Hcase4']]].
      + (* case 1: forall b, ef b -> ~el_pre b y *)
        destruct Hcase1' as (_ & _ & Hnoelpre).
        destruct Hposa as (Hefa & _ & Hprea & _).
        exfalso. apply (Hnoelpre a Hefa Hprea).
      + (* case 2: exists b, el_pos b y ∧ lin b z *)
        destruct Hcase2' as (_ & _ & [b [Hposb Hlinbz]]).
        pose proof (one_el_pos a y b Hposa Hposb) as Heq. subst b.
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
        eapply Htrans; done.
      + (* case 3: el z - contradiction *)
        destruct Hcase3' as (Helz & _ & _). exfalso. apply el_then_not_ef in Helz. done.
      + (* case 4: el z - contradiction *)
        destruct Hcase4' as (Helz & _ & _). exfalso. apply el_then_not_ef in Helz. done.
  Qed.

  Lemma el_ef_el_then_lin x y z : elim pre val x -> elim_free pre val y -> elim pre val z -> ef_el x y -> ef_el y z -> el_el x z.
  Proof.
    intros Helx Hefy Helz Hxy Hyz.
    (* ef_el x y with el x, ef y comes from cases 1 or 2 *)
    destruct (ef_elD x y Hxy) as [Hcase1|[Hcase2|[Hcase3|Hcase4]]].
    - (* case 1: no el_pos to x *)
      destruct Hcase1 as (_ & _ & Hnoelpre).
      (* ef_el y z with ef y, el z comes from cases 3 or 4 *)
      destruct (ef_elD y z Hyz) as [Hcase1'|[Hcase2'|[Hcase3'|Hcase4']]].
      + (* case 1: el y - contradiction *)
        destruct Hcase1' as (Hely' & _ & _). exfalso. apply el_then_not_ef in Hely'. done.
      + (* case 2: el y - contradiction *)
        destruct Hcase2' as (Hely' & _ & _). exfalso. apply el_then_not_ef in Hely'. done.
      + (* case 3: el_pos y z *)
        destruct Hcase3' as (_ & _ & Hposy).
        assert (Hnposx : ~ exists a, el_pos a x).
        { intros [a Hposa]. destruct Hposa as (Hefa & _ & Hprea & _).
          apply (Hnoelpre a Hefa Hprea). }
        apply (el_elI2 x z y Helx Helz Hnposx Hposy).
      + (* case 4: el_pos a z, lin y a *)
        destruct Hcase4' as (_ & _ & [a [Hposa Hlinya]]).
        assert (Hnposx : ~ exists b, el_pos b x).
        { intros [b Hposb]. destruct Hposb as (Hefb & _ & Hpreb & _).
          apply (Hnoelpre b Hefb Hpreb). }
        apply (el_elI2 x z a Helx Helz Hnposx Hposa).
    - (* case 2: el_pos a x, lin a y *)
      destruct Hcase2 as (_ & _ & [a [Hposa Hlinay]]).
      destruct (ef_elD y z Hyz) as [Hcase1'|[Hcase2'|[Hcase3'|Hcase4']]].
      + (* case 1: el y - contradiction *)
        destruct Hcase1' as (Hely' & _ & _). exfalso. apply el_then_not_ef in Hely'. done.
      + (* case 2: el y - contradiction *)
        destruct Hcase2' as (Hely' & _ & _). exfalso. apply el_then_not_ef in Hely'. done.
      + (* case 3: el_pos y z *)
        destruct Hcase3' as (_ & _ & Hposy).
        apply (el_elI5 x z a y Helx Helz Hposa Hposy Hlinay).
      + (* case 4: el_pos b z, lin y b *)
        destruct Hcase4' as (_ & _ & [b [Hposb Hlinyb]]).
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
        assert (Hlinab : lin a b) by (eapply Htrans; done).
        apply (el_elI5 x z a b Helx Helz Hposa Hposb Hlinab).
    - (* case 3: el y - but y is ef, contradiction *)
      destruct Hcase3 as (Hely' & _ & _). exfalso. apply el_then_not_ef in Hely'. done.
    - (* case 4: el y - contradiction *)
      destruct Hcase4 as (Hely' & _ & _). exfalso. apply el_then_not_ef in Hely'. done.
  Qed.

  Lemma el_el_ef_then_lin x y z : elim pre val x -> elim pre val y -> elim_free pre val z -> el_el x y -> ef_el y z -> ef_el x z.
  Proof.
    intros Helx Hely Hefz Hxy Hyz.
    (* ef_el y z with el y, ef z comes from cases 1 or 2 *)
    destruct (ef_elD y z Hyz) as [Hyz1|[Hyz2|[Hyz3|Hyz4]]].
    - (* ef_el y z case 1: no el_pos to y *)
      destruct Hyz1 as (_ & _ & Hnoelprex).
      (* Any el_pre to x gives el_pre to y by el_el case analysis, but y has no el_pre, so no el_pre to x *)
      apply ef_elI1; [done|done|].
      intros a Hefa Hpreax.
      destruct Hxy as (_ & _ & Hcases).
      destruct Hcases as [Hval|[Hcase2|[Hcase3|[Hcase4|[Hcase5|[Hcase6|Hcase7]]]]]].
      + (* val x y - el_pre a y via same_val and el_pre a x *)
        apply (Hnoelprex a Hefa).
        eapply val_then_el_pre; [left; exact Hval|exact Hpreax].
      + (* no el_pos to x, el_pos to y - but y has no el_pos contradiction *)
        destruct Hcase2 as (_ & [b Hposb]).
        destruct Hposb as (Hefb & _ & Hpreb & _).
        apply (Hnoelprex b Hefb Hpreb).
      + (* no el_pos to x or y, exists c with ~el_pre c x and el_pre c y *)
        destruct Hcase3 as (_ & _ & [c [Hnprecx Hprecy]]).
        (* Use el_pre_abcd: el_pre a x -> el_pre c y -> el_pre a y \/ el_pre c x *)
        destruct (el_pre_abcd a x c y Hpreax Hprecy) as [Hpreay|Hprecx].
        * (* el_pre a y - contradicts Hnoelprex *)
          exfalso. apply (Hnoelprex a Hefa Hpreay).
        * (* el_pre c x - contradicts Hnprecx *)
          exfalso. apply Hnprecx. done.
      + (* no el_pos to x or y, forall el_pre c x -> el_pre c y, minf *)
        destruct Hcase4 as (_ & _ & Himplic & _).
        apply (Hnoelprex a Hefa (Himplic a Hpreax)).
      + (* el_pos a x, el_pos b y, lin a b *)
        destruct Hcase5 as [a' [b' [Hposa' [Hposb' _]]]].
        destruct Hposb' as (Hefb' & _ & Hpreb' & _).
        apply (Hnoelprex b' Hefb' Hpreb').
      + (* el_pos a x, el_pos a y, exists c with ... *)
        destruct Hcase6 as [a' [Hposa' [Hposb' _]]].
        destruct Hposb' as (Hefa' & _ & Hprea' & _).
        apply (Hnoelprex a' Hefa' Hprea').
      + (* el_pos a x, el_pos a y, forall c ..., minf *)
        destruct Hcase7 as [[a' [Hposa' [Hposb' _]]] _].
        destruct Hposb' as (Hefa' & _ & Hprea' & _).
        apply (Hnoelprex a' Hefa' Hprea').
    - (* ef_el y z case 2: el_pos a y, lin a z *)
      destruct Hyz2 as (_ & _ & [a [Hposa Hlinaz]]).
      (* el_el x y gives us info about el_pos to x and y *)
      destruct Hxy as (_ & _ & Hcases).
      destruct Hcases as [Hval|[Hcase2|[Hcase3|[Hcase4|[Hcase5|[Hcase6|Hcase7]]]]]].
      + (* val x y *)
        pose proof (val_then_el_pos2 x y a wf_history (same_valI1 x y Hval) Hposa) as Hposx.
        apply (ef_elI2 x z a Helx Hefz Hposx Hlinaz).
      + (* no el_pos to x, el_pos to y *)
        destruct Hcase2 as (Hnposx & _).
        apply ef_elI1; [done|done|].
        apply not_el_posD; done.
      + (* no el_pos to x or y, exists c ... - but el_pos a y contradicts no el_pos to y *)
        destruct Hcase3 as (_ & Hnposy & _).
        exfalso. apply Hnposy. exists a. done.
      + (* no el_pos to x or y, forall ... - contradicts el_pos a y *)
        destruct Hcase4 as (_ & Hnposy & _ & _).
        exfalso. apply Hnposy. exists a. done.
      + (* el_pos a' x, el_pos b' y, lin a' b' *)
        destruct Hcase5 as [a' [b' [Hposa' [Hposb' Hlinab]]]].
        pose proof (one_el_pos b' y a Hposb' Hposa) as Heq. subst b'.
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
        assert (Hlinaz' : lin a' z) by (eapply Htrans; done).
        apply (ef_elI2 x z a' Helx Hefz Hposa' Hlinaz').
      + (* el_pos a' both x and y, exists c ... *)
        destruct Hcase6 as [a' [Hposa' [Hposay _]]].
        pose proof (one_el_pos a' y a Hposay Hposa) as Heq. subst a'.
        apply (ef_elI2 x z a Helx Hefz Hposa' Hlinaz).
      + (* el_pos a' both x and y, forall c ..., minf *)
        destruct Hcase7 as [[a' [Hposa' [Hposay _]]] _].
        pose proof (one_el_pos a' y a Hposay Hposa) as Heq. subst a'.
        apply (ef_elI2 x z a Helx Hefz Hposa' Hlinaz).
    - (* ef_el y z case 3: el z - but z is ef, contradiction *)
      destruct Hyz3 as (Helz & _ & _). exfalso. apply el_then_not_ef in Helz. done.
    - (* ef_el y z case 4: el z - contradiction *)
      destruct Hyz4 as (Helz & _ & _). exfalso. apply el_then_not_ef in Helz. done.
  Qed.

  Lemma ef_el_el_then_lin x y z : elim_free pre val x -> elim pre val y -> elim pre val z -> ef_el x y -> el_el y z -> ef_el x z.
  Proof.
    intros Hefx Hely Helz Hxy Hyz.
    (* ef_el x y with ef x, el y comes from cases 3 or 4 *)
    destruct (ef_elD x y Hxy) as [Hcase1|[Hcase2|[Hcase3|Hcase4]]].
    - (* case 1: el x - but x is ef, contradiction *)
      destruct Hcase1 as (Helx & _ & _). exfalso. apply el_then_not_ef in Helx. done.
    - (* case 2: el x - contradiction *)
      destruct Hcase2 as (Helx & _ & _). exfalso. apply el_then_not_ef in Helx. done.
    - (* case 3: el_pos x y *)
      destruct Hcase3 as (_ & _ & Hposx).
      (* el_el y z gives us info - need ef_el x z *)
      destruct Hyz as (_ & _ & Hcases).
      destruct Hcases as [Hval|[Hcase2'|[Hcase3'|[Hcase4'|[Hcase5'|[Hcase6'|Hcase7']]]]]].
      + (* val y z *)
        pose proof (val_then_el_pos1 y z x wf_history (same_valI1 y z Hval) Hposx) as Hposz.
        apply (ef_elI4 z x Helz Hposz).
      + (* no el_pos to y, el_pos b z - but el_pos x y contradicts *)
        destruct Hcase2' as (Hnposy & _).
        exfalso. apply Hnposy. exists x. done.
      + (* no el_pos to y or z, exists c ... - contradicts el_pos x y *)
        destruct Hcase3' as (Hnposy & _ & _).
        exfalso. apply Hnposy. exists x. done.
      + (* no el_pos to y or z, forall ..., minf - contradicts el_pos x y *)
        destruct Hcase4' as (Hnposy & _ & _ & _).
        exfalso. apply Hnposy. exists x. done.
      + (* el_pos a y, el_pos b z, lin a b *)
        destruct Hcase5' as [a [b [Hposa [Hposb Hlinab]]]].
        pose proof (one_el_pos x y a Hposx Hposa) as Heq. subst a.
        apply (ef_elI3 z x b Helz Hefx Hposb Hlinab).
      + (* el_pos a y, el_pos a z, exists c ... *)
        destruct Hcase6' as [a [Hposa [Hposaz _]]].
        pose proof (one_el_pos x y a Hposx Hposa) as Heq. subst a.
        apply (ef_elI4 z x Helz Hposaz).
      + (* el_pos a y, el_pos a z, forall ..., minf *)
        destruct Hcase7' as [[a [Hposa [Hposaz _]]] _].
        pose proof (one_el_pos x y a Hposx Hposa) as Heq. subst a.
        apply (ef_elI4 z x Helz Hposaz).
    - (* case 4: el_pos a y, lin x a *)
      destruct Hcase4 as (_ & _ & [a [Hposa Hlinxa]]).
      destruct Hyz as (_ & _ & Hcases).
      destruct Hcases as [Hval|[Hcase2'|[Hcase3'|[Hcase4'|[Hcase5'|[Hcase6'|Hcase7']]]]]].
      + (* val y z *)
        pose proof (val_then_el_pos1 y z a wf_history (same_valI1 y z Hval) Hposa) as Hposz.
        apply (ef_elI3 z x a Helz Hefx Hposz Hlinxa).
      + (* no el_pos to y, el_pos b z - but el_pos a y contradicts *)
        destruct Hcase2' as (Hnposy & _).
        exfalso. apply Hnposy. exists a. done.
      + (* no el_pos to y or z, exists c ... - contradicts el_pos a y *)
        destruct Hcase3' as (Hnposy & _ & _).
        exfalso. apply Hnposy. exists a. done.
      + (* no el_pos to y or z, forall ..., minf - contradicts el_pos a y *)
        destruct Hcase4' as (Hnposy & _ & _ & _).
        exfalso. apply Hnposy. exists a. done.
      + (* el_pos a' y, el_pos b z, lin a' b *)
        destruct Hcase5' as [a' [b [Hposa' [Hposb Hlina'b]]]].
        pose proof (one_el_pos a y a' Hposa Hposa') as Heq. subst a'.
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
        assert (Hlinxb : lin x b) by (eapply Htrans; done).
        apply (ef_elI3 z x b Helz Hefx Hposb Hlinxb).
      + (* el_pos a' y, el_pos a' z, exists c ... *)
        destruct Hcase6' as [a' [Hposa' [Hposaz _]]].
        pose proof (one_el_pos a y a' Hposa Hposa') as Heq. subst a'.
        apply (ef_elI3 z x a Helz Hefx Hposaz Hlinxa).
      + (* el_pos a' y, el_pos a' z, forall ..., minf *)
        destruct Hcase7' as [[a' [Hposa' [Hposaz _]]] _].
        pose proof (one_el_pos a y a' Hposa Hposa') as Heq. subst a'.
        apply (ef_elI3 z x a Helz Hefx Hposaz Hlinxa).
  Qed.

  (* elimination_stack.thy:893-903 - ef_lin *)
  Definition ef_lin : relation operation :=
    fun a b => lin a b /\ elim_free pre val a /\ elim_free pre val b.

  Lemma ef_linI a b : lin a b -> elim_free pre val a -> elim_free pre val b -> ef_lin a b.
  Proof. intros Hlin Ha Hb. split; [|split]; done. Qed.

  Lemma ef_linD a b : ef_lin a b -> lin a b /\ elim_free pre val a /\ elim_free pre val b.
  Proof. done. Qed.

  Lemma ef_lin_transitive : Transitive ef_lin.
  Proof.
    intros a b c (Hab & Hefa & Hefb) (Hbc & Hefb' & Hefc).
    split; [|split]; [|done|done].
    destruct ef_linearizable_def as [Hseq _].
    destruct Hseq as [Hwf _ _ _].
    destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
    eapply Htrans; done.
  Qed.

  (* elimination_stack.thy:917-927 - witness *)
  Definition witness : relation operation :=
    fun a b => ef_lin a b \/ ef_el a b \/ el_el a b.

  Lemma lin_then_witness a b : ef_lin a b -> witness a b.
  Proof. intros Hab. left. done. Qed.

  Lemma ef_el_then_witness a b : ef_el a b -> witness a b.
  Proof. intros Hab. right. left. done. Qed.

  Lemma el_el_then_witness a b : el_el a b -> witness a b.
  Proof. intros Hab. right. right. done. Qed.

  Lemma pr_in_witness a b : pre a b -> witness a b.
  Proof.
    intros Hab.
    destruct (el_or_ef1 a b Hab) as [Hela|Hefa];
    destruct (el_or_ef2 a b Hab) as [Helb|Hefb].
    - (* both el *)
      apply el_el_then_witness. apply lem_pr_in_el_el; done.
    - (* a el, b ef *)
      apply ef_el_then_witness. apply pr_in_ef_el2; done.
    - (* a ef, b el *)
      apply ef_el_then_witness. apply pr_in_ef_el1; done.
    - (* both ef *)
      apply lin_then_witness.
      split; [|split]; [|done|done].
      apply pr_in_lin.
      split; [|split]; done.
  Qed.

  Lemma ef_then_in_lin a b : elim_free pre val a -> elim_free pre val b -> a <> b -> lin a b \/ lin b a.
  Proof.
    intros Hefa Hefb Hneq.
    destruct (ef_then_push_or_pop a Hefa) as [Hpusha|Hpopa];
    destruct (ef_then_push_or_pop b Hefb) as [Hpushb|Hpopb].
    - (* both pushes *)
      destruct ef_linearizable_def as [Hseq _].
      destruct Hseq as [_ Htotpush _ _].
      apply Htotpush; try done.
      + apply lem_is_push_ef_then_is_ef_push; done.
      + apply lem_is_push_ef_then_is_ef_push; done.
    - (* a push, b pop *)
      destruct ef_linearizable_def as [Hseq _].
      destruct Hseq as [_ _ _ Htotpp].
      apply Htotpp.
      + apply lem_is_push_ef_then_is_ef_push; done.
      + apply lem_is_pop_ef_then_is_ef_pop; done.
    - (* a pop, b push *)
      destruct ef_linearizable_def as [Hseq _].
      destruct Hseq as [_ _ _ Htotpp].
      destruct (Htotpp b a) as [Hba|Hab].
      + apply lem_is_push_ef_then_is_ef_push; done.
      + apply lem_is_pop_ef_then_is_ef_pop; done.
      + right. done.
      + left. done.
    - (* both pops *)
      destruct ef_linearizable_def as [Hseq _].
      destruct Hseq as [_ _ Htotpop _].
      apply Htotpop; try done.
      + apply lem_is_pop_ef_then_is_ef_pop; done.
      + apply lem_is_pop_ef_then_is_ef_pop; done.
  Qed.

  Lemma ef_el_b_ef_then_a_el a b : ef_el a b -> elim_free pre val b -> elim pre val a.
  Proof.
    intros Hab Hefb.
    apply ef_el_then_ef_and_el in Hab.
    destruct Hab as [[Hela Hefb']|[Hefa Helb]].
    - done.
    - exfalso. apply el_then_not_ef in Helb. done.
  Qed.

  Lemma witness_transitive : Transitive witness.
  Proof.
    intros x y z [Hlinxy|[Hefelxy|Helelxy]] [Hlinyz|[Hefelyz|Helelyz]].
    (* Case 1: ef_lin x y, ef_lin y z -> ef_lin x z *)
    - apply lin_then_witness. eapply ef_lin_transitive; done.
    (* Case 2: ef_lin x y, ef_el y z *)
    - destruct Hlinxy as (Hlinxy' & Hefx & Hefy).
      destruct (ef_elD y z Hefelyz) as [Hcase1|[Hcase2|[Hcase3|Hcase4]]].
      + (* case 1: el y, ef z, forall - but y is ef, contradiction *)
        destruct Hcase1 as (Hely & _ & _). exfalso. apply el_then_not_ef in Hely. done.
      + (* case 2: el y, ef z, exists - contradiction *)
        destruct Hcase2 as (Hely & _ & _). exfalso. apply el_then_not_ef in Hely. done.
      + (* case 3: el z, ef y, el_pos y z *)
        destruct Hcase3 as (Helz & _ & Hposyz).
        apply ef_el_then_witness.
        apply (ef_elI3 z x y Helz Hefx Hposyz Hlinxy').
      + (* case 4: el z, ef y, exists a, el_pos a z, lin y a *)
        destruct Hcase4 as (Helz & _ & [a [Hposa Hlinya]]).
        apply ef_el_then_witness.
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
        apply (ef_elI3 z x a Helz Hefx Hposa).
        eapply Htrans; done.
    (* Case 3: ef_lin x y, el_el y z *)
    - destruct Hlinxy as (_ & Hefx & Hefy).
      destruct (el_el_then_el_and_el y z Helelyz) as [Hely _].
      exfalso. apply el_then_not_ef in Hely. done.
    (* Case 4: ef_el x y, ef_lin y z *)
    - destruct (ef_el_then_ef_and_el x y Hefelxy) as [[Helx Hefy]|[Hefx Hely]].
      + (* el x, ef y - use ef_el_then_witness and build ef_el x z *)
        destruct Hlinyz as (Hlinyz' & Hefy' & Hefz).
        destruct (ef_elD x y Hefelxy) as [Hcase1|[Hcase2|[Hcase3|Hcase4]]].
        * destruct Hcase1 as (_ & _ & Hforall).
          (* forall case - x has no el_pre from any ef *)
          apply ef_el_then_witness.
          apply (ef_elI1 x z Helx Hefz Hforall).
        * destruct Hcase2 as (_ & _ & [a [Hposa Hlinya]]).
          destruct ef_linearizable_def as [[Hwf _ _ _] _].
          destruct Hwf as [Htrans _ _ _ _ _ _ _ _].
          apply ef_el_then_witness.
          apply (ef_elI2 x z a Helx Hefz Hposa). eapply Htrans; done.
        * destruct Hcase3 as (Hefy'' & _ & _). exfalso. apply el_then_not_ef in Hefy''. done.
        * destruct Hcase4 as (Hefy'' & _ & _). exfalso. apply el_then_not_ef in Hefy''. done.
      + (* ef x, el y - but y is also ef via ef_lin, contradiction *)
        destruct Hlinyz as (_ & Hefy' & _).
        exfalso. apply el_then_not_ef in Hely. done.
    (* Case 5: ef_el x y, ef_el y z *)
    - destruct (ef_el_then_ef_and_el x y Hefelxy) as [[Helx Hefy]|[Hefx Hely]];
      destruct (ef_el_then_ef_and_el y z Hefelyz) as [[Hely' Hefz]|[Hefy' Helz]].
      + (* el x, ef y, el y, ef z - contradiction: y is both el and ef *)
        exfalso. apply el_then_not_ef in Hely'. done.
      + (* el x, ef y, ef y, el z *)
        apply el_el_then_witness.
        apply (el_ef_el_then_lin x y z Helx Hefy Helz Hefelxy Hefelyz).
      + (* ef x, el y, el y, ef z *)
        apply lin_then_witness.
        apply (ef_linI x z (ef_el_ef_then_lin x y z Hefx Hely Hefz Hefelxy Hefelyz) Hefx Hefz).
      + (* ef x, el y, ef y, el z - contradiction *)
        exfalso. apply el_then_not_ef in Hely. done.
    (* Case 6: ef_el x y, el_el y z *)
    - destruct (ef_el_then_ef_and_el x y Hefelxy) as [[Helx Hefy]|[Hefx Hely]].
      + (* el x, ef y - but y is el via el_el, contradiction *)
        destruct (el_el_then_el_and_el y z Helelyz) as [Hely _].
        exfalso. apply el_then_not_ef in Hely. done.
      + (* ef x, el y *)
        destruct (el_el_then_el_and_el y z Helelyz) as [Hely' Helz].
        apply ef_el_then_witness.
        apply (ef_el_el_then_lin x y z Hefx Hely Helz Hefelxy Helelyz).
    (* Case 7: el_el x y, ef_lin y z *)
    - destruct (el_el_then_el_and_el x y Helelxy) as [_ Hely].
      destruct Hlinyz as (_ & Hefy & _).
      exfalso. apply el_then_not_ef in Hely. done.
    (* Case 8: el_el x y, ef_el y z *)
    - destruct (el_el_then_el_and_el x y Helelxy) as [Helx Hely].
      destruct (ef_el_then_ef_and_el y z Hefelyz) as [[Hely' Hefz]|[Hefy Helz]].
      + (* el y, ef z *)
        apply ef_el_then_witness.
        apply (el_el_ef_then_lin x y z Helx Hely Hefz Helelxy Hefelyz).
      + (* ef y, el z - contradiction *)
        exfalso. apply el_then_not_ef in Hely. done.
    (* Case 9: el_el x y, el_el y z -> el_el x z *)
    - apply el_el_then_witness. eapply el_el_transitive; done.
  Qed.

  Lemma witness_irreflexive : Irreflexive witness.
  Proof.
    intros a [Hlin|[Hefel|Helel]].
    - destruct Hlin as (Hlinaa & _ & _).
      destruct ef_linearizable_def as [[Hwf _ _ _] _].
      destruct Hwf as [_ _ Hirr _ _ _ _ _ _].
      eapply Hirr. exact Hlinaa.
    - eapply ef_el_irreflexive. exact Hefel.
    - eapply el_el_irreflexive. exact Helel.
  Qed.

  Lemma witness_antisymmetric : Antisymmetric operation eq witness.
  Proof.
    intros x y [Hlinxy|[Hefelxy|Helelxy]] [Hlinyx|[Hefelyx|Helelyx]].
    (* Case 1: ef_lin x y, ef_lin y x -> x = y by lin antisymmetry *)
    - destruct Hlinxy as (Hxy & Hefx & Hefy).
      destruct Hlinyx as (Hyx & _ & _).
      destruct ef_linearizable_def as [[Hwf _ _ _] _].
      destruct Hwf as [_ Hanti _ _ _ _ _ _ _].
      apply Hanti; done.
    (* Case 2: ef_lin x y, ef_el y x -> contradiction *)
    - destruct Hlinxy as (_ & Hefx & Hefy).
      destruct (ef_el_then_ef_and_el y x Hefelyx) as [[Hely _]|[_ Helx]].
      + exfalso. apply el_then_not_ef in Hely. done.
      + exfalso. apply el_then_not_ef in Helx. done.
    (* Case 3: ef_lin x y, el_el y x -> contradiction *)
    - destruct Hlinxy as (_ & Hefx & Hefy).
      destruct (el_el_then_el_and_el y x Helelyx) as [Hely _].
      exfalso. apply el_then_not_ef in Hely. done.
    (* Case 4: ef_el x y, ef_lin y x -> contradiction *)
    - destruct Hlinyx as (_ & Hefy & Hefx).
      destruct (ef_el_then_ef_and_el x y Hefelxy) as [[Helx _]|[_ Hely]].
      + exfalso. apply el_then_not_ef in Helx. done.
      + exfalso. apply el_then_not_ef in Hely. done.
    (* Case 5: ef_el x y, ef_el y x -> x = y by ef_el antisymmetry *)
    - apply ef_el_antisymmetric; done.
    (* Case 6: ef_el x y, el_el y x -> contradiction *)
    - destruct (ef_el_then_ef_and_el x y Hefelxy) as [[Helx Hefy]|[Hefx Hely]].
      + destruct (el_el_then_el_and_el y x Helelyx) as [Hely' _].
        exfalso. apply el_then_not_ef in Hely'. done.
      + destruct (el_el_then_el_and_el y x Helelyx) as [_ Helx'].
        exfalso. apply el_then_not_ef in Helx'. done.
    (* Case 7: el_el x y, ef_lin y x -> contradiction *)
    - destruct Hlinyx as (_ & Hefy & Hefx).
      destruct (el_el_then_el_and_el x y Helelxy) as [Helx _].
      exfalso. apply el_then_not_ef in Helx. done.
    (* Case 8: el_el x y, ef_el y x -> contradiction *)
    - destruct (ef_el_then_ef_and_el y x Hefelyx) as [[Hely Hefx]|[Hefy Helx]].
      + destruct (el_el_then_el_and_el x y Helelxy) as [Helx' _].
        exfalso. apply el_then_not_ef in Helx'. done.
      + destruct (el_el_then_el_and_el x y Helelxy) as [_ Hely'].
        exfalso. apply el_then_not_ef in Hely'. done.
    (* Case 9: el_el x y, el_el y x -> x = y by el_el antisymmetry *)
    - apply el_el_antisymmetric; done.
  Qed.

  Lemma witness_total_on_push a b : is_push val a -> is_push val b -> a <> b -> witness a b \/ witness b a.
  Proof.
    intros Hpusha Hpushb Hneq.
    (* a and b are both pushes, so they're either ef or el *)
    destruct (push_then_el_or_ef a Hpusha) as [Hela|Hefa];
    destruct (push_then_el_or_ef b Hpushb) as [Helb|Hefb].
    - (* both el - use el_el_total *)
      destruct (el_el_total a b Hela Helb) as [Heq|[Hab|Hba]].
      + subst. done.
      + left. apply el_el_then_witness. done.
      + right. apply el_el_then_witness. done.
    - (* a el, b ef - use ef_el_total *)
      destruct (ef_el_total a b Hela Hefb) as [Hab|Hba].
      + left. apply ef_el_then_witness. done.
      + right. apply ef_el_then_witness. done.
    - (* a ef, b el - use ef_el_total *)
      destruct (ef_el_total b a Helb Hefa) as [Hba|Hab].
      + right. apply ef_el_then_witness. done.
      + left. apply ef_el_then_witness. done.
    - (* both ef - use ef_then_in_lin *)
      destruct (ef_then_in_lin a b Hefa Hefb Hneq) as [Hab|Hba].
      + left. apply lin_then_witness. split; [|split]; done.
      + right. apply lin_then_witness. split; [|split]; done.
  Qed.

  Lemma witness_total_on_pop a b : is_pop val a -> is_pop val b -> a <> b -> witness a b \/ witness b a.
  Proof.
    intros Hpopa Hpopb Hneq.
    destruct (pop_then_el_or_ef a Hpopa) as [Hela|Hefa];
    destruct (pop_then_el_or_ef b Hpopb) as [Helb|Hefb].
    - destruct (el_el_total a b Hela Helb) as [Heq|[Hab|Hba]].
      + subst. done.
      + left. apply el_el_then_witness. done.
      + right. apply el_el_then_witness. done.
    - destruct (ef_el_total a b Hela Hefb) as [Hab|Hba].
      + left. apply ef_el_then_witness. done.
      + right. apply ef_el_then_witness. done.
    - destruct (ef_el_total b a Helb Hefa) as [Hba|Hab].
      + right. apply ef_el_then_witness. done.
      + left. apply ef_el_then_witness. done.
    - destruct (ef_then_in_lin a b Hefa Hefb Hneq) as [Hab|Hba].
      + left. apply lin_then_witness. split; [|split]; done.
      + right. apply lin_then_witness. split; [|split]; done.
  Qed.

  Lemma witness_total_on_push_pop a b : is_push val a -> is_pop val b -> witness a b \/ witness b a.
  Proof.
    intros Hpusha Hpopb.
    destruct (decide (a = b)) as [Heq|Hneq].
    - (* a = b - impossible since a is push and b is pop *)
      subst. destruct Hpusha as [c Hac]. destruct Hpopb as [d Hdb].
      (* val a c and val d a - contradicts val_order *)
      exfalso. eapply def_val_order; [exact Hac|exists d; left; done].
    - destruct (push_then_el_or_ef a Hpusha) as [Hela|Hefa];
      destruct (pop_then_el_or_ef b Hpopb) as [Helb|Hefb].
      + destruct (el_el_total a b Hela Helb) as [Heq'|[Hab|Hba]].
        * subst. done.
        * left. apply el_el_then_witness. done.
        * right. apply el_el_then_witness. done.
      + destruct (ef_el_total a b Hela Hefb) as [Hab|Hba].
        * left. apply ef_el_then_witness. done.
        * right. apply ef_el_then_witness. done.
      + destruct (ef_el_total b a Helb Hefa) as [Hba|Hab].
        * right. apply ef_el_then_witness. done.
        * left. apply ef_el_then_witness. done.
      + destruct (ef_then_in_lin a b Hefa Hefb Hneq) as [Hab|Hba].
        * left. apply lin_then_witness. split; [|split]; done.
        * right. apply lin_then_witness. split; [|split]; done.
  Qed.

  Lemma el_then_same_witness x y a :
    WellformedHistory pre val ->
    elim pre val x -> same_val val x y -> witness a x -> same_val val x a \/ witness a y.
  Proof.
    intros Hwf Helx Hsv [Hlin|[Hefel|Helel]].
    - (* ef_lin a x - contradicts x being el *)
      destruct Hlin as (_ & _ & Hefx).
      exfalso. apply el_then_not_ef in Helx. done.
    - (* ef_el a x - case analysis on 4 cases *)
      destruct (ef_elD a x Hefel) as [Hcase1|[Hcase2|[Hcase3|Hcase4]]].
      + (* case 1: el a, ef x - contradiction *)
        destruct Hcase1 as (_ & Hefx & _).
        exfalso. apply el_then_not_ef in Helx. done.
      + (* case 2: el a, ef x - contradiction *)
        destruct Hcase2 as (_ & Hefx & _).
        exfalso. apply el_then_not_ef in Helx. done.
      + (* case 3: el x, ef a, el_pos a x *)
        destruct Hcase3 as (_ & Hefa & Hposa).
        right. apply ef_el_then_witness.
        pose proof (val_then_el_pos1 x y a Hwf Hsv Hposa) as Hposy.
        apply (ef_elI4 y a (elI3 x y Hwf Helx Hsv) Hposy).
      + (* case 4: el x, ef a, exists b, el_pos b x, lin a b *)
        destruct Hcase4 as (_ & Hefa & [b [Hposb Hlinab]]).
        right. apply ef_el_then_witness.
        pose proof (val_then_el_pos1 x y b Hwf Hsv Hposb) as Hposy.
        apply (ef_elI3 y a b (elI3 x y Hwf Helx Hsv) Hefa Hposy Hlinab).
    - (* el_el a x - case analysis on 7 cases *)
      destruct (el_elD a x Helel) as (Hela & _ & Hcases).
      destruct Hcases as [Hval|[Hcase2|[Hcase3|[Hcase4|[Hcase5|[Hcase6|Hcase7]]]]]].
      + (* val a x - same_val x a *)
        left. right. done.
      + (* no el_pos a, el_pos to x *)
        destruct Hcase2 as (Hnposa & [b Hposb]).
        pose proof (val_then_el_pos1 x y b Hwf Hsv Hposb) as Hposy.
        right. apply el_el_then_witness.
        apply (el_elI2 a y b Hela (elI3 x y Hwf Helx Hsv) Hnposa Hposy).
      + (* no el_pos a or x, exists c *)
        destruct Hcase3 as (Hnposa & Hnposx & [c [Hnpreca Hprecx]]).
        pose proof (val_then_el_pre x y c Hsv Hprecx) as Hprecy.
        right. apply el_el_then_witness.
        destruct (decide (el_pre c a)) as [Hpreca|Hnpreca'].
        * (* el_pre c a - use el_elI2 or el_elI3 *)
          pose proof (val_not_el_pos_then_not_el_pos y x Hwf (same_val_commutative x y Hsv) Hnposx) as Hnposy.
          apply (el_elI3 a y c Hela (elI3 x y Hwf Helx Hsv) Hnposa Hnposy Hnpreca Hprecy).
        * (* ~ el_pre c a - still use el_elI3 *)
          pose proof (val_not_el_pos_then_not_el_pos y x Hwf (same_val_commutative x y Hsv) Hnposx) as Hnposy.
          apply (el_elI3 a y c Hela (elI3 x y Hwf Helx Hsv) Hnposa Hnposy Hnpreca Hprecy).
      + (* no el_pos, forall c, minf a x *)
        destruct Hcase4 as (Hnposa & Hnposx & Hpre & Hminf).
        pose proof (val_not_el_pos_then_not_el_pos y x Hwf (same_val_commutative x y Hsv) Hnposx) as Hnposy.
        pose proof (val_minf_then_minf2 y x a (same_val_commutative x y Hsv) Hminf) as Hminfy.
        right. apply el_el_then_witness.
        apply (el_elI4 a y Hela (elI3 x y Hwf Helx Hsv) Hnposa Hnposy); [|done].
        intros c' Hprec'a.
        pose proof (Hpre c' Hprec'a) as Hprec'x.
        eapply val_then_el_pre; done.
      + (* el_pos a' a, el_pos b x, lin a' b *)
        destruct Hcase5 as [a' [b [Hposa' [Hposb Hlin]]]].
        pose proof (val_then_el_pos1 x y b Hwf Hsv Hposb) as Hposy.
        right. apply el_el_then_witness.
        apply (el_elI5 a y a' b Hela (elI3 x y Hwf Helx Hsv) Hposa' Hposy Hlin).
      + (* el_pos a' a, el_pos a' x, exists c *)
        destruct Hcase6 as [a' [Hposa' [Hposx [c [Hposc [Hnprec Hprecx]]]]]].
        pose proof (val_then_el_pos1 x y a' Hwf Hsv Hposx) as Hposy.
        pose proof (val_then_el_pre x y c Hsv Hprecx) as Hprecy.
        right. apply el_el_then_witness.
        apply (el_elI6 a y a' Hela (elI3 x y Hwf Helx Hsv) Hposa' Hposy).
        exists c. split; [|split]; done.
      + (* el_pos a' a, el_pos a' x, forall c, minf a x *)
        destruct Hcase7 as [[a' [Hposa' [Hposx Hcond]]] Hminf].
        pose proof (val_then_el_pos1 x y a' Hwf Hsv Hposx) as Hposy.
        pose proof (val_minf_then_minf2 y x a (same_val_commutative x y Hsv) Hminf) as Hminfy.
        right. apply el_el_then_witness.
        apply (el_elI7 a y a' Hela (elI3 x y Hwf Helx Hsv) Hposa' Hposy); [|done].
        intros c [Hposa'c Hpreca].
        specialize (Hcond c (conj Hposa'c Hpreca)).
        eapply val_then_el_pre; done.
  Qed.

  Lemma witness_then_push_or_pop1 a b : witness a b -> is_push val a \/ is_pop val a.
  Proof.
    intros [Hlin|[Hefel|Helel]].
    - destruct Hlin as (_ & Hefa & _).
      apply ef_then_push_or_pop. done.
    - apply ef_el_then_ef_and_el in Hefel.
      destruct Hefel as [[Hela _]|[Hefa _]].
      + destruct Hela as [[Hpush|Hpop] _]; [left|right]; done.
      + apply ef_then_push_or_pop. done.
    - destruct Helel as (Hela & _ & _).
      destruct Hela as [[Hpush|Hpop] _]; [left|right]; done.
  Qed.

  Lemma witness_then_push_or_pop2 a b : witness a b -> is_push val b \/ is_pop val b.
  Proof.
    intros [Hlin|[Hefel|Helel]].
    - destruct Hlin as (_ & _ & Hefb).
      apply ef_then_push_or_pop. done.
    - apply ef_el_then_ef_and_el in Hefel.
      destruct Hefel as [[_ Hefb]|[_ Helb]].
      + apply ef_then_push_or_pop. done.
      + destruct Helb as [[Hpush|Hpop] _]; [left|right]; done.
    - destruct Helel as (_ & Helb & _).
      destruct Helb as [[Hpush|Hpop] _]; [left|right]; done.
  Qed.

  Lemma el_then_same_witness2 x y a :
    WellformedHistory pre val ->
    elim pre val x -> same_val val x y -> witness x a -> same_val val x a \/ witness y a.
  Proof.
    intros Hwf Helx Hsv Hxa.
    (* a is a push or pop since it's in a witness relation *)
    pose proof (witness_then_push_or_pop2 x a Hxa) as Hppa.
    (* y is el via elI3 *)
    pose proof (elI3 x y Hwf Helx Hsv) as Hely.
    (* y is a push or pop from definition of elim *)
    destruct Hely as [Hppy _].
    destruct (decide (a = y)) as [Heq|Hneq].
    - (* a = y -> same_val x a = same_val x y ✓ *)
      subst a. left. done.
    - (* a ≠ y -> use witness totality *)
      destruct Hppa as [Hpusha|Hpopa]; destruct Hppy as [Hpushy|Hpopy].
      + (* both pushes *)
        destruct (witness_total_on_push a y Hpusha Hpushy Hneq) as [Hay|Hya].
        * (* witness a y - use el_then_same_witness *)
          pose proof (el_then_same_witness y x a Hwf (elI3 x y Hwf Helx Hsv) (same_val_commutative x y Hsv) Hay) as [Hsva|Hax].
          -- (* same_val y a -> by same_val_unique, a = x -> witness x x contradicts irrefl *)
             pose proof (same_val_unique y x a Hwf (same_val_commutative x y Hsv) Hsva) as Heq.
             subst a. exfalso. eapply witness_irreflexive. exact Hxa.
          -- (* witness a x and witness x a -> a = x by antisymmetry *)
             pose proof (witness_antisymmetric a x Hax Hxa) as Heq.
             subst a. exfalso. eapply witness_irreflexive. exact Hxa.
        * right. done.
      + (* a push, y pop *)
        destruct (witness_total_on_push_pop a y Hpusha Hpopy) as [Hay|Hya].
        * pose proof (el_then_same_witness y x a Hwf (elI3 x y Hwf Helx Hsv) (same_val_commutative x y Hsv) Hay) as [Hsva|Hax].
          -- pose proof (same_val_unique y x a Hwf (same_val_commutative x y Hsv) Hsva) as Heq.
             subst a. exfalso. eapply witness_irreflexive. exact Hxa.
          -- pose proof (witness_antisymmetric a x Hax Hxa) as Heq.
             subst a. exfalso. eapply witness_irreflexive. exact Hxa.
        * right. done.
      + (* a pop, y push *)
        destruct (witness_total_on_push_pop y a Hpushy Hpopa) as [Hya|Hay].
        * right. done.
        * pose proof (el_then_same_witness y x a Hwf (elI3 x y Hwf Helx Hsv) (same_val_commutative x y Hsv) Hay) as [Hsva|Hax].
          -- pose proof (same_val_unique y x a Hwf (same_val_commutative x y Hsv) Hsva) as Heq.
             subst a. exfalso. eapply witness_irreflexive. exact Hxa.
          -- pose proof (witness_antisymmetric a x Hax Hxa) as Heq.
             subst a. exfalso. eapply witness_irreflexive. exact Hxa.
      + (* both pops *)
        destruct (witness_total_on_pop a y Hpopa Hpopy Hneq) as [Hay|Hya].
        * pose proof (el_then_same_witness y x a Hwf (elI3 x y Hwf Helx Hsv) (same_val_commutative x y Hsv) Hay) as [Hsva|Hax].
          -- pose proof (same_val_unique y x a Hwf (same_val_commutative x y Hsv) Hsva) as Heq.
             subst a. exfalso. eapply witness_irreflexive. exact Hxa.
          -- pose proof (witness_antisymmetric a x Hax Hxa) as Heq.
             subst a. exfalso. eapply witness_irreflexive. exact Hxa.
        * right. done.
  Qed.

  Lemma ef_ef_then_lin a b : elim_free pre val a -> elim_free pre val b -> witness a b -> ef_lin a b.
  Proof.
    intros Hefa Hefb [Hlin|[Hefel|Helel]].
    - done.
    - apply ef_el_then_ef_and_el in Hefel.
      destruct Hefel as [[Hela _]|[_ Helb]].
      + exfalso. apply el_then_not_ef in Hela. done.
      + exfalso. apply el_then_not_ef in Helb. done.
    - destruct Helel as (Hela & Helb & _).
      exfalso. apply el_then_not_ef in Hela. done.
  Qed.

  Lemma ef_val_ef a b : val a b -> elim_free pre val a -> elim_free pre val b.
  Proof.
    intros Hab Hefa.
    eapply ef_val_then_ef; [exact wf_history|exact Hefa|left; exact Hab].
  Qed.

  Lemma witness_ooo : sequential_lifo witness val.
  Proof.
    (* sequential_lifo: ∀ ia ib ra rb, val ia ra → val ib rb → witness ia ib → witness ib ra → witness rb ra *)
    intros ia ib ra rb Hia Hib Hiaib Hibra.
    (* ia is a push *)
    assert (Hpushia : is_push val ia) by (exists ra; done).
    destruct (push_then_el_or_ef ia Hpushia) as [Helia|Hefia].
    - (* ia is el *)
      (* Use el_then_same_witness2: el ia, same_val ia ra, witness ia ib -> same_val ia ib \/ witness ra ib *)
      pose proof (el_then_same_witness2 ia ra ib wf_history Helia (same_valI1 ia ra Hia) Hiaib) as [Hsv|Hraib].
      + (* same_val ia ib -> contradiction with val_order *)
        destruct (same_valD ia ib Hsv) as [Hvalia|Hvalib].
        * (* val ia ib - but ia is push, so ib is pop. Then val ia ra and val ia ib, so ra = ib by pop_once *)
          pose proof (def_pop_once ia ra ib Hia Hvalia) as Heq. subst ib.
          (* witness ra ra contradicts irreflexive *)
          exfalso. eapply witness_irreflexive. exact Hibra.
        * (* val ib ia - ia is push, ib is push too but then val_order violated *)
          (* val ia ra and val ib ia - so ia is both push (for ra) and pop (of ib) - contradiction *)
          exfalso. eapply def_val_order. exact Hia. exists ib. left. exact Hvalib.
      + (* witness ra ib *)
        pose proof (witness_antisymmetric ib ra Hibra Hraib) as Heq. subst ib.
        (* Now ra = ib, so val ra rb. Need witness rb ra. *)
        (* witness_antisymmetric gave us ra = ib, so Hib : val ra rb *)
        (* val ra rb and val ia ra, so ra is both pop (from ia) and push (to rb) - contradiction *)
        exfalso. eapply def_val_order. exact Hia. exists rb. right. done.
    - (* ia is ef *)
      (* ib is a push *)
      assert (Hpushib : is_push val ib) by (exists rb; done).
      destruct (push_then_el_or_ef ib Hpushib) as [Helib|Hefib].
      + (* ib is el *)
        (* Use el_then_same_witness2: el ib, same_val ib rb, witness ib ra -> same_val ib ra \/ witness rb ra *)
        pose proof (el_then_same_witness2 ib rb ra wf_history Helib (same_valI1 ib rb Hib) Hibra) as [Hsv|Hrbra].
        * (* same_val ib ra *)
          destruct (same_valD ib ra Hsv) as [Hvalibra|Hvalraib].
          -- (* val ib ra - ib push, ra pop. But ra is also pop of ia.
                val ia ra with ia ef. By ef_val_ef, ra is ef.
                But ib is el and val ib ra would make ra el too? Let me check. *)
             (* Actually: ib is el (so ra must be el). But ia is ef, and val ia ra, so ra is ef. Contradiction. *)
             pose proof (ef_val_ef ia ra Hia Hefia) as Hefra.
             pose proof (elI3 ib ra wf_history Helib (same_valI1 ib ra Hvalibra)) as Helra.
             exfalso. apply el_then_not_ef in Helra. done.
          -- (* val ra ib - ra is push, ib is pop. But ib is push (we have val ib rb). Contradiction. *)
             exfalso. eapply def_val_order. exact Hib. exists ra. left. done.
        * (* witness rb ra - exactly what we want *)
          done.
      + (* ib is ef - both ia and ib are ef *)
        (* From val ia ra and ef ia, ra is ef *)
        pose proof (ef_val_ef ia ra Hia Hefia) as Hefra.
        (* From val ib rb and ef ib, rb is ef *)
        pose proof (ef_val_ef ib rb Hib Hefib) as Hefrb.
        (* From witness ia ib with both ef, ef_lin ia ib *)
        pose proof (ef_ef_then_lin ia ib Hefia Hefib Hiaib) as Hefliniaib.
        (* From witness ib ra with both ef, ef_lin ib ra *)
        pose proof (ef_ef_then_lin ib ra Hefib Hefra Hibra) as Heflinibra.
        (* Extract lin from ef_lin *)
        destruct Hefliniaib as (Hliniaib & _ & _).
        destruct Heflinibra as (Hlinibra & _ & _).
        (* Build elim_free_val *)
        assert (Hefvalia : elim_free_val pre val ia ra) by (split; [|split]; done).
        assert (Hefvalib : elim_free_val pre val ib rb) by (split; [|split]; done).
        (* Use sequential_lifo from ef_linearizable *)
        destruct ef_linearizable_def as [_ Hlifo].
        pose proof (Hlifo ia ib ra rb Hefvalia Hefvalib Hliniaib Hlinibra) as Hlinrbra.
        (* Now lin rb ra with ef rb and ef ra gives ef_lin rb ra, so witness rb ra *)
        apply lin_then_witness. split; [|split]; done.
  Qed.

  Lemma val_then_not_witness ia ra : val ia ra -> ~ witness ra ia.
  Proof.
    intros Hval Hwitness.
    (* ia is a push *)
    assert (Hpush : is_push val ia) by (exists ra; done).
    destruct (push_then_el_or_ef ia Hpush) as [Helia|Hefia].
    - (* ia is el - construct el_el ia ra *)
      pose proof (elI3 ia ra wf_history Helia (same_valI1 ia ra Hval)) as Helra.
      pose proof (el_elI1 ia ra Helia Helra Hval) as Hel_ia_ra.
      pose proof (el_el_then_witness ia ra Hel_ia_ra) as Hwit_ia_ra.
      (* witness ia ra and witness ra ia -> ra = ia by antisymmetry *)
      pose proof (witness_antisymmetric ra ia Hwitness Hwit_ia_ra) as Heq.
      subst ra.
      (* val ia ia contradicts val_order *)
      eapply def_val_order. exact Hval. exists ia. left. done.
    - (* ia is ef - ra must also be ef by ef_val_ef *)
      pose proof (ef_val_ef ia ra Hval Hefia) as Hefra.
      (* witness ra ia with both ef gives ef_lin ra ia *)
      destruct Hwitness as [Hlin|[Hefel|Helel]].
      + (* ef_lin ra ia *)
        destruct Hlin as (Hlinra & _ & _).
        (* val ia ra with both ef gives elim_free_val ia ra *)
        assert (Hefval : elim_free_val pre val ia ra) by (split; [|split]; done).
        (* From SequentialStack lin (elim_free_val), WellformedHistory gives def_val_then_not_pr *)
        destruct ef_linearizable_def as [[Hwf _ _ _] _].
        destruct Hwf as [_ _ _ _ _ _ _ _ Hvtnpr].
        pose proof (Hvtnpr ia ra Hefval) as Hnlin.
        (* But ef_lin ra ia implies lin ra ia - contradiction *)
        apply Hnlin. done.
      + (* ef_el ra ia - but both ra and ia are ef, so this is impossible *)
        destruct (ef_el_then_ef_and_el ra ia Hefel) as [[Helra _]|[_ Helia']].
        * exfalso. apply el_then_not_ef in Helra. done.
        * exfalso. apply el_then_not_ef in Helia'. done.
      + (* el_el ra ia - but ia is ef, so this is impossible *)
        destruct (el_el_then_el_and_el ra ia Helel) as [_ Helia'].
        exfalso. apply el_then_not_ef in Helia'. done.
  Qed.

  Lemma witness_abcd : Abcd witness.
  Proof.
    intros a b c d Hab Hcd.
    (* a, b, c, d are all push/pop by witness_then_push_or_pop *)
    pose proof (witness_then_push_or_pop1 a b Hab) as Hppa.
    pose proof (witness_then_push_or_pop2 a b Hab) as Hppb.
    pose proof (witness_then_push_or_pop1 c d Hcd) as Hppc.
    pose proof (witness_then_push_or_pop2 c d Hcd) as Hppd.
    destruct (decide (a = d)) as [Heq|Hneq].
    - (* a = d - need witness c b *)
      subst d.
      destruct (decide (b = c)) as [Heqbc|Hneqbc].
      + (* b = c - witness a b and witness b a (since c = b) would give a = b, then witness c b = witness b b - contradiction *)
        subst c.
        pose proof (witness_antisymmetric a b Hab Hcd) as Heq. subst b.
        exfalso. eapply witness_irreflexive. exact Hab.
      + (* b ≠ c *)
        assert (Hneqcb : c ≠ b) by (intro; subst; done).
        destruct Hppb as [Hpushb|Hpopb]; destruct Hppc as [Hpushc|Hpopc].
        * destruct (witness_total_on_push c b Hpushc Hpushb Hneqcb) as [Hcb|Hbc]; [right; done|].
          (* Hbc : witness b c, Hab : witness a b, Hcd : witness c a *)
          pose proof (witness_transitive a b c Hab Hbc) as Hac.
          pose proof (witness_antisymmetric a c Hac Hcd) as Heq. subst c.
          exfalso. eapply witness_irreflexive. exact Hac.
        * destruct (witness_total_on_push_pop b c Hpushb Hpopc) as [Hbc|Hcb]; [|right; done].
          pose proof (witness_transitive a b c Hab Hbc) as Hac.
          pose proof (witness_antisymmetric a c Hac Hcd) as Heq. subst c.
          exfalso. eapply witness_irreflexive. exact Hac.
        * destruct (witness_total_on_push_pop c b Hpushc Hpopb) as [Hcb|Hbc]; [right; done|].
          pose proof (witness_transitive a b c Hab Hbc) as Hac.
          pose proof (witness_antisymmetric a c Hac Hcd) as Heq. subst c.
          exfalso. eapply witness_irreflexive. exact Hac.
        * destruct (witness_total_on_pop c b Hpopc Hpopb Hneqcb) as [Hcb|Hbc]; [right; done|].
          pose proof (witness_transitive a b c Hab Hbc) as Hac.
          pose proof (witness_antisymmetric a c Hac Hcd) as Heq. subst c.
          exfalso. eapply witness_irreflexive. exact Hac.
    - (* a ≠ d - try witness a d *)
      destruct Hppa as [Hpusha|Hpopa]; destruct Hppd as [Hpushd|Hpopd].
      + destruct (witness_total_on_push a d Hpusha Hpushd Hneq) as [Had|Hda]; [left; done|].
        (* witness d a - need witness c b *)
        destruct (decide (b = c)) as [Heqbc|Hneqbc].
        * subst c. left. eapply witness_transitive. exact Hab. exact Hcd.
        * assert (Hneqcb : c ≠ b) by (intro; subst; done).
          destruct Hppb as [Hpushb|Hpopb]; destruct Hppc as [Hpushc|Hpopc].
          -- destruct (witness_total_on_push c b Hpushc Hpushb Hneqcb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_push_pop b c Hpushb Hpopc) as [Hbc|Hcb]; [|right; done].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_push_pop c b Hpushc Hpopb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_pop c b Hpopc Hpopb Hneqcb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
      + destruct (witness_total_on_push_pop a d Hpusha Hpopd) as [Had|Hda]; [left; done|].
        destruct (decide (b = c)) as [Heqbc|Hneqbc].
        * subst c. left. eapply witness_transitive. exact Hab. exact Hcd.
        * assert (Hneqcb : c ≠ b) by (intro; subst; done).
          destruct Hppb as [Hpushb|Hpopb]; destruct Hppc as [Hpushc|Hpopc].
          -- destruct (witness_total_on_push c b Hpushc Hpushb Hneqcb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_push_pop b c Hpushb Hpopc) as [Hbc|Hcb]; [|right; done].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_push_pop c b Hpushc Hpopb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_pop c b Hpopc Hpopb Hneqcb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
      + destruct (witness_total_on_push_pop d a Hpushd Hpopa) as [Hda|Had]; [|left; done].
        destruct (decide (b = c)) as [Heqbc|Hneqbc].
        * subst c. left. eapply witness_transitive. exact Hab. exact Hcd.
        * assert (Hneqcb : c ≠ b) by (intro; subst; done).
          destruct Hppb as [Hpushb|Hpopb]; destruct Hppc as [Hpushc|Hpopc].
          -- destruct (witness_total_on_push c b Hpushc Hpushb Hneqcb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_push_pop b c Hpushb Hpopc) as [Hbc|Hcb]; [|right; done].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_push_pop c b Hpushc Hpopb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_pop c b Hpopc Hpopb Hneqcb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
      + destruct (witness_total_on_pop a d Hpopa Hpopd Hneq) as [Had|Hda]; [left; done|].
        destruct (decide (b = c)) as [Heqbc|Hneqbc].
        * subst c. left. eapply witness_transitive. exact Hab. exact Hcd.
        * assert (Hneqcb : c ≠ b) by (intro; subst; done).
          destruct Hppb as [Hpushb|Hpopb]; destruct Hppc as [Hpushc|Hpopc].
          -- destruct (witness_total_on_push c b Hpushc Hpushb Hneqcb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_push_pop b c Hpushb Hpopc) as [Hbc|Hcb]; [|right; done].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_push_pop c b Hpushc Hpopb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
          -- destruct (witness_total_on_pop c b Hpopc Hpopb Hneqcb) as [Hcb|Hbc]; [right; done|].
             pose proof (witness_transitive d a b Hda Hab) as Hdb.
             right. eapply witness_transitive. exact Hcd. exact Hdb.
  Qed.

  Lemma witness_wellformed_history :
    WellformedHistory pre val ->
    WellformedHistory witness val.
  Proof.
    intros Hwf.
    constructor.
    - (* Transitive witness *)
      exact witness_transitive.
    - (* Antisymmetric witness *)
      exact witness_antisymmetric.
    - (* Irreflexive witness *)
      exact witness_irreflexive.
    - (* FinitePredicate for pushes/pops - same as for pre *)
      destruct Hwf as [_ _ _ Hfin _ _ _ _ _]. exact Hfin.
    - (* push_once val *)
      destruct Hwf as [_ _ _ _ Hpo _ _ _ _]. exact Hpo.
    - (* pop_once val *)
      destruct Hwf as [_ _ _ _ _ Hpopo _ _ _]. exact Hpopo.
    - (* val_order val *)
      destruct Hwf as [_ _ _ _ _ _ Hvo _ _]. exact Hvo.
    - (* push_or_pop *)
      intros a b Hwit.
      split.
      + pose proof (witness_then_push_or_pop1 a b Hwit) as [Hpush|Hpop].
        * destruct Hpush as [c Hac]. exists c. left. done.
        * destruct Hpop as [c Hca]. exists c. right. done.
      + pose proof (witness_then_push_or_pop2 a b Hwit) as [Hpush|Hpop].
        * destruct Hpush as [c Hbc]. exists c. left. done.
        * destruct Hpop as [c Hcb]. exists c. right. done.
    - (* val_then_not_pr witness val *)
      exact val_then_not_witness.
  Qed.

  Lemma witness_sequential_history :
    WellformedHistory pre val ->
    SequentialSet witness val.
  Proof.
    intros Hwf.
    constructor.
    - exact (witness_wellformed_history Hwf).
    - exact witness_total_on_push.
    - exact witness_total_on_pop.
    - exact witness_total_on_push_pop.
  Qed.

  Lemma witness_sequential_stack :
    WellformedHistory pre val ->
    SequentialStack witness val.
  Proof.
    intros Hwf.
    constructor.
    - exact (witness_sequential_history Hwf).
    - exact witness_ooo.
  Qed.

  Local Instance witness_dec : RelDecision witness.
  Proof.
    intros a b. unfold witness, ef_lin, ef_el, el_el. apply _.
  Qed.

  Theorem elimination_stack_linearizable :
    WellformedHistory pre val ->
    exists prt (_ : RelDecision prt), subrelation pre prt /\ SequentialStack prt val.
  Proof.
    intros Hwf.
    exists witness, _. split.
    - exact pr_in_witness.
    - exact (witness_sequential_stack Hwf).
  Qed.

End elimination_stack.

(* elimination_stack.thy:1230-1277 *)
Lemma help_elimination_stack `{abstract_stack_model} pre val :
  WellformedHistory pre val -> Abcd pre ->
  linearizable_non_empty_stack (elim_free_pre pre val) (elim_free_val pre val) ->
  exists lin, forall a b, elim_free_pre pre val a b -> lin a b.
Proof.
  intros Hwf Habcd (Hch & prt & _ & Hsub & Hseq).
  exists prt.
  intros a b Hpre.
  apply Hsub. done.
Qed.

(* elimination_stack.thy:1284-1306 *)
Theorem elimination_theorem `{abstract_stack_model} pre val
    `{!RelDecision pre, !RelDecision val} :
  WellformedHistory pre val -> Abcd pre ->
  linearizable_non_empty_stack (elim_free_pre pre val) (elim_free_val pre val) ->
  linearizable_non_empty_stack pre val.
Proof.
  intros Hwf Habcd Hlin.
  (* Get the SequentialStack from Hlin *)
  destruct Hlin as (Hch & prt & Hprt_dec & Hsub & Hseq).
  (* Derive pr_in_prt from subrelation *)
  assert (Hpr_in_prt : forall a b, elim_free_pre pre val a b -> prt a b).
  { intros a b Hpre. apply Hsub. done. }
  (* Get FinitePredicate for ef from WellformedHistory *)
  assert (Hfinef : FinitePredicate (elim_free pre val)).
  { apply finite_elim_free. destruct Hwf as [_ _ _ Hfin _ _ _ _ _]. exact Hfin. }
  (* Build linearizable_non_empty_stack pre val *)
  unfold linearizable_non_empty_stack.
  split.
  - (* ConcHistory pre *)
    constructor.
    + apply wf_pre_transitive.
    + apply wf_pre_antisymmetric.
    + apply wf_pre_irreflexive.
    + exact Habcd.
  - (* exists prt', subrelation pre prt' /\ SequentialStack prt' val *)
    (* Construct f and f_inj from Countable instance *)
    pose (f := fun (x : operation) => Pos.to_nat (encode x)).
    assert (f_inj : forall a b, f a = f b -> a = b).
    { intros a b Heq. unfold f in Heq.
      apply (f_equal Pos.of_nat) in Heq.
      rewrite !Pos2Nat.id in Heq.
      by apply (inj encode). }
    (* Use elimination_stack_linearizable with prt *)
    pose proof (elimination_stack_linearizable pre val prt Hwf Hseq Hpr_in_prt Hfinef Habcd f f_inj Hwf)
      as (wit & Hwit_dec & Hsub_pre & Hwit_seq).
    exists wit, _. done.
Qed.
