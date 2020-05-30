Require Import Ensembles.
Require Import Relations.

(*
Require Import ListSet.
Definition ss := set. 
*)

Definition set := Ensemble.
Definition rel := relation.

Set Implicit Arguments. 

(** ** Departure set *)
Definition dep (A: Type) (r: rel A) : set A :=
  fun x => exists y, r x y.

(** ** Destination set *)
Definition des (A: Type) (r: rel A) : set A :=
  fun y => exists x, r x y.

(** ** Departure and desitination set *)
Definition ups (A: Type) (r: rel A) : set A :=
  Union _ (dep r) (des r).

(** ** Departure set of a given destination *)
Definition dep_restrict (A: Type) (r: rel A) (e: A) : set A :=
  fun x => r x e.

(** ** Operations of relations *)

Section Relation_Operations.

(** ** Composition *)
Definition composition (A: Type) (r1 r2: rel A) :=
  fun x y => exists z, r1 x z /\ r2 z y.

(** ** Union *)
Definition union_rel (A: Type) (r1 r2: rel A) : rel A :=
  union _ r1 r2.

(** ** Projection *)
Definition projection_rel (A: Type) (r: rel A) (s: set A) : rel A := 
  fun x y => r x y /\ In _ s x /\ In _ s y.

(** ** Transitive closure *)
Inductive tc (A : Type)(r : A -> A -> Prop) : rel A :=
   | trc_step : forall x, forall y : A, r x y -> (tc r) x y
   | trc_ind  : forall x y z : A,
                (tc r) x z -> (tc  r) z y -> (tc r) x y.

End Relation_Operations.

(** ** Relations of relations *)

Section Relation_Relations.

(** ** Inclusion *)
Definition rel_incl (A: Type) (r1 r2 : rel A) : Prop := 
  inclusion _ r1 r2.

(** ** Strict inclusion *)
Definition rel_sincl (A: Type) (r1 r2 : rel A)  : Prop  :=
  inclusion _ r1 r2 /\ ~(inclusion _ r2 r1).

End Relation_Relations.

(** ** Properties of relations *)

Section Relation_Properties.

(** ** Irreflexive *)
Definition irreflexive (A: Type) (r: rel A) : Prop :=
  ~ reflexive _ r.

(** ** Transitive *)
Definition transitive (A: Type) (r: rel A) : Prop :=
  transitive _ r.

(** ** Symmetric *)
Definition symmetric (A: Type) (r: rel A) : Prop :=
  symmetric _ r.

(** ** Anti-symmetric *)
Definition antisymmetric (A: Type) (r: rel A) : Prop  :=
  antisymmetric _ r.

(** ** Partial order *)
Definition partial (A: Type) (r: rel A) : Prop := 
  (irreflexive r) /\ (transitive r).

(** ** Acyclic *)
Definition acyclic (A:Type) (r: rel A) : Prop :=
  forall x, ~((tc r) x x).

(** ** Total order *)
Definition total (A: Type) (r: rel A) (s: set A) : Prop :=
  Included _ (Union _ (dep r) (des r)) s /\
  (*transitive*)
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) /\
  (*irreflexivity*)
  (forall x, ~(r x x)) /\
  (*linear on s*)
  (forall x1 x2, (x1 <> x2) -> (In _ s x1) -> (In _ s x2) -> 
    (r x1 x2) \/ (r x2 x1)).

End Relation_Properties.
