(** Coq Library *)
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Logic.Decidable.

(** Oqarina library *)
(*Require Import Oqarina.AADL.Kernel.categories.
Require Import Oqarina.core.identifiers.
Require Import Oqarina.coq_utils.utils.*)
(* end hide *)

#[local] Open Scope Z_scope.
#[local] Open Scope string_scope.
(*| .. coq:: |*)

(*|

Properties
==========

|*)

Definition INT := Z.
Definition REAL := Z.

(*+ Property Types *)

(* should we use this? *)
Inductive identifier : Type :=
| Id (name : string).

Definition empty_identifier := Id "".

Scheme Equality for identifier.

Lemma identifier_string_eq (s1 s2 : string) : s1 = s2 <-> Id s1 = Id s2.
Proof.
  split.
  - apply f_equal.
  - intros H1. injection H1. auto.
Qed.

Lemma identifier_string_neq (s1 s2 : string) : s1 <> s2 <-> Id s1 <> Id s2.
Proof.
  rewrite <- identifier_string_eq. easy.
Qed.

Definition projectionIdentifierString (i : identifier) : string :=
  match i with
  | Id s => s
  end.
Inductive enumeration_literal :=
| EnumLiteral (name : identifier).

Definition enumeration_type :=
  list identifier.
(* !!! unique identifiers *)

Inductive unit_literal :=
| BaseUnit (name : identifier)
| DerivedUnit (name : identifier) (base: identifier) (factor: nat).

Definition units_type :=
  list unit_literal.
(* !!! unique identifiers, derived/base unit consistency, factor int or real *)

Inductive int_range_constraint :=
  IRC (min max : INT).

Inductive real_range_constraint :=
  RRC (rmin rmax : REAL).

Inductive range_constraint :=
| C_IntRange (irc : int_range_constraint)
| C_RealRange (rrc : real_range_constraint).

(** [ps_qname] defines a qualified name for property related construct, e.g.  "foo::bar" *)

Inductive ps_qname :=
| PSQN (psname : string) (name : string).

Definition empty_ps_qname := PSQN "" "".

Inductive property_type :=
(* Predeclared types are constructors for performance *)
| aadlboolean | aadlstring | aadlinteger | aadlreal
| PT_Enumeration (literals : list identifier)
| PT_Units (units : units_type)
| PT_Number (p : property_type) (* must be aadlinteger or aadlreal *)
            (range: option range_constraint)
            (units: option property_type)
| PT_Range (p : property_type) (* must be numeric *)
| PT_Classifier (* TBD *)
| PT_Reference
| PT_Record (fields: list field_decl)
| PT_List (of: property_type) (* not allowed in named types in AADL2 (why???) *)
| PT_TypeRef (qname : ps_qname)
with field_decl :=
| FieldDecl (name: identifier) (type: property_type).

Section Definitions.
(* end hide *)

Section Sumbool_Decidability.
(* end hide *)

  (** The following defines a shortcut to use sumbool-based definition for decidability. See %\cite{appel2018software}%, chapter "Programming with Decision Procedures" for details. *)

Variable A : Prop.
Hypothesis HA : { A } + {~ A}.

Variable B : Prop.
Hypothesis HB : { B } + {~ B}.

Definition dec_sumbool (P : Prop) := { P } + { ~ P }.

Lemma dec_sumbool_and:  { A /\ B  } + { ~ (A /\ B) }.
Proof.
    destruct HA , HB ;
      auto ||
      right; intuition.
Defined.

Lemma dec_sumbool_or:  { A \/ B  } + { ~ (A \/ B) }.
Proof.
  destruct HA , HB ;
    auto ||
  right; intuition.
Defined.

Lemma dec_sumbool_not: dec_sumbool ( ~ A ).
Proof.
    destruct HA.
    - right. auto.
    - left. auto.
Defined.

(* begin hide *)
End Sumbool_Decidability.

Definition eq_dec T := forall x y : T, {x=y}+{x<>y}.

Definition Oracle (P : Prop) (P_dec : dec_sumbool P): bool :=
    match (P_dec) with
      | left _ => true
      | right _ => false
    end.

(* begin hide *)
End Definitions.

Lemma unit_literal_eq_dec : eq_dec unit_literal.
Proof.
  unfold eq_dec.
  decide equality ;
   apply identifier_eq_dec ||
   apply PeanoNat.Nat.eq_dec.
Qed.

Lemma units_type_eq_dec : eq_dec units_type.
Proof.
  unfold eq_dec.
  apply list_eq_dec.
  apply unit_literal_eq_dec.
Qed.

Lemma int_range_constraint_eq_dec (a b : int_range_constraint): {a=b}+{a<>b}.
Proof.
  decide equality;
  apply Z.eq_dec.
Qed.

Lemma real_range_constraint_eq_dec (a b : real_range_constraint): {a=b}+{a<>b}.
Proof.
  decide equality;
  apply Z.eq_dec.
Qed.

Lemma range_constraint_eq_dec (a b : range_constraint): {a=b}+{a<>b}.
Proof.
  decide equality.
  apply int_range_constraint_eq_dec.
  apply real_range_constraint_eq_dec.
Qed.

Local Hint Resolve units_type_eq_dec identifier_eq_dec range_constraint_eq_dec:core.

Lemma property_type_eq_dec (a b : property_type) : {a=b}+{a<>b}
  with field_decl_eq_dec (a b : field_decl): {a=b}+{a<>b}.
Proof.
  (* proof for property_type *)
  repeat decide equality.

  (* proof for field_decl_eq *)
  decide equality.
Qed.

(*! Examples *)

Check PT_TypeRef (PSQN "ps" "pt") : property_type.
Check aadlboolean : property_type.
Check PT_Units [BaseUnit (Id "m"); DerivedUnit (Id "cm") (Id "m") 100] : property_type.
Check PT_Number aadlinteger None None : property_type.
Check PT_Range aadlinteger : property_type.

Definition is_numeric_predef (p : property_type) : bool :=
  match p with
  | aadlinteger | aadlreal => true
  | _ => false
  end.

Inductive is_numeric_predefR : property_type -> Prop :=
| Predef_Int : is_numeric_predefR aadlinteger
| Predef_Real : is_numeric_predefR aadlstring.

Definition property_type_wf (t : property_type) : bool :=
  match t with
  | PT_Number p _ _ => is_numeric_predef p
  | PT_Range p => is_numeric_predef p
  (* !!! add more *)
  | _ => true
  end.

(*+ Property Expressions and Values *)

Inductive property_value :=
| PV_Bool (b : bool)
| PV_String (s : string)
| PV_Int (n : Z)
| PV_Real (r : REAL)
| PV_IntU (n : Z) (unit : property_value)
| PV_RealU (r : REAL) (unit : property_value)
| PV_Enum (i : identifier)
| PV_Unit (i : identifier)
| PV_IntRange (min max : property_value)
| PV_RealRange (min max : property_value)
| PV_IntRangeD (min max : property_value) (delta : property_value)
| PV_RealRangeD (min max : property_value) (delta : property_value)
| PV_PropertyRef (qname : ps_qname) (* ref to property or constant *)
| PV_Classifier (* TBD *)
| PV_ModelRef (path : list identifier)
| PV_Record (fields : list field_value)
| PV_List (elements: list property_value)
| PV_Computed (function : string)
with field_value :=
| FieldVal (name : identifier) (value : property_value).

(*--------------------------Example-------------------------------*)
Definition my_property_type : property_type :=
  PT_Number aadlinteger (Some (C_IntRange (IRC 0 100))) None.

Definition my_property_value : property_value :=
  PV_Int 42.

