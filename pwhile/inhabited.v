(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope nat_scope.

(* -------------------------------------------------------------------- *)
Module Inhabited.
Section ClassDef.
Record class_of T := Class {
  base : Choice.class_of T;
  witness : T
}.
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (x : T) :=
  fun bT b & phant_id (Choice.class bT) b =>
  Pack (@Class T b x) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation ihbType := type.
Notation IhbType T m := (@pack T m _ _ id).
Notation "[ 'ihbType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ihbType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ihbType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ihbType'  'of'  T ]") : form_scope.
End Exports.
End Inhabited.

Export Inhabited.Exports.

(* -------------------------------------------------------------------- *)
Definition witness_of (T : ihbType) & phant T := nosimpl
  (Inhabited.witness (Inhabited.class T)).

Notation witness T := (witness_of (Phant T)).

(* -------------------------------------------------------------------- *)
Canonical unit_ihbType := Eval hnf in IhbType unit tt.
Canonical nat_ihbType := Eval hnf in IhbType nat 0%N.

(* -------------------------------------------------------------------- *)
Canonical prod_ihbType (T U : ihbType) :=
  Eval hnf in IhbType (T * U)%type (witness T, witness U).

(* -------------------------------------------------------------------- *)
Canonical int_ihbType := Eval hnf in IhbType int 0.

(* -------------------------------------------------------------------- *)
Canonical seq_ihbType (T:ihbType) := 
   Eval hnf in IhbType (seq.seq T) [::].
