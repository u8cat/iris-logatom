From iris.heap_lang Require Import lang.

Class Encodable (A : Type) := {
  encode_val : A → val;
  decode_val : val → option A;
  decode_encode_val a : decode_val (encode_val a) = Some a;
  encode_decode_val v a : decode_val v = Some a → v = encode_val a
}.
Global Hint Mode Encodable ! : typeclass_instances.
Global Arguments encode_val : simpl never.
Global Arguments decode_val : simpl never.

Global Instance encode_val_inj `{!Encodable A} : Inj (=) (=) (encode_val (A:=A)).
Proof.
  intros x y Hxy; apply (inj Some).
  by rewrite <-(decode_encode_val x), Hxy, decode_encode_val.
Qed.

Global Program Instance encodable_val : Encodable val := {
  encode_val v := v;
  decode_val v := Some v;
}.
Solve Obligations with naive_solver.
