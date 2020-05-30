Require Import Nat.
Require Import Relations.
Require Import Ensembles.
Require Import ZArith.
From RDT Require Export util.

Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

Ltac decide_equality := decide equality; auto with equality arith.

Section Identifier.

(** ** Processors *)
  (** Processors are indexed by natural numbers. *)

Definition Proc := nat.
Lemma eqProc_dec : forall (x y: Proc), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqProc_dec : equality.

(** ** Index in session order on each process *)

Definition session_order_index := nat.
Lemma eqSoi_dec : forall (x y: session_order_index), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
Hint Resolve eqSoi_dec : equality.

(** ** Identifier: 
       - proc: process where it was executed
       - soi: index of the session order point when it was executed*) 
       (** The id of a event also be recorded in the op and rval of it *)

Record Id : Type := mk_id {
  proc: nat;
  soi: nat
}.

Lemma eqId_dec : forall (x y: Id), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
Hint Resolve eqSoi_dec : equality.

Open Scope bool_scope.

Definition eqb_id (x y: Id) :=
   (x.(proc) =? y.(proc)) && (x.(soi) =? y.(soi)).  

Close Scope bool_scope.
(*
Definition Id' (x y: Type):= prod x y.  

Check Id'. 
*)
End Identifier.

(** *** Objects *)
  (*Object are indexed by natural numbers. *)

Definition Object := nat.
Lemma eqObj_dec : forall (x y: Object), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqObj_dec : equality.

(** ** Event *)

Record Event : Type := mk_e {
  id: Id;
  obj : Object
}.


(** ** Execution witness *)
Section Witness.

Definition Rvis := rel Event.
Definition Rar := rel Event.

Record Witness : Type := mk_wt {
  vis: Rvis;
  ar: Rar
}.

End Witness.

Record Event_structure : Type := mk_h {
  events: set Event;
  so : rel Event
}.

(** ** Process an event *)
Definition proc_of (e: Event) : Proc := e.(id).(proc). 

(** ** Session order index *)
Definition soi_of (e: Event) : session_order_index := e.(id).(soi). 

(** ** visible events set of a event (on the same object) *)
Definition vis_refl (e: Event) (w: Witness) : set Event := 
  fun x => exists x, (vis w) x e /\ e.(obj) = x.(obj).    

(** ** Well-formed witness*)

Definition well_formed_vis (h: Event_structure) (vis: Rvis) : Prop :=
  (* all associated events of vis are in the events of h *) 
  Included _ (ups vis) h.(events) /\
  (* vis is acyclic *)
  acyclic vis.

Definition well_formed_ar (h: Event_structure) (ar: Rar) : Prop :=
  (* ar is total *)
  total ar h.(events).

Definition well_formed_witness (h: Event_structure) (w: Witness) : Prop :=
  (* well formed vis *)
  well_formed_vis h (vis w) /\
  (* ar is total *)
  well_formed_ar h (ar w) /\
  (* vis is a subset of ar *)
  rel_incl (vis w) (ar w).

(** ** Projections on a process *)

(** *** Of session order *)
Definition so_on_proc (h: Event_structure) (p: Proc) : rel Event :=
  fun e1 e2 => (so h) e1 e2 /\ proc_of e1 = proc_of e2.

(** *** Of events *)
Definition events_on_proc (h: Event_structure) (p: Proc) : set Event :=
  fun e => In _ h.(events) e /\ proc_of e = p.

Definition proc_set (h: Event_structure) : set Proc := 
   fun p => exists e, 
     In _ h.(events) e /\ 
     p = proc_of e. 

(** **Well-formedness of a history *)

Definition well_formed_history (h: Event_structure) : Prop :=
  (** ** well-formed session order *)
  (forall x y, (so h) x y -> proc_of x = proc_of y /\
                             lt (soi_of x) (soi_of y)) /\
  Included _  h.(events) (dep (so h)) /\
  Included _  h.(events) (des (so h)) /\
  (* each event has a unique identifier *)
  (forall e1 e2, In _ h.(events) e1 -> In _ h.(events) e2 ->
   (e1.(id) = e2.(id)) -> (e1 = e2)) /\
  (* events in a process are in a total order *)
   forall p, In _ (proc_set h) p -> 
          total (so_on_proc h p) (events_on_proc h p).

Module Type Ord_Gua.

Parameter ordering_guarantee : Event_structure -> Witness -> Prop.

End Ord_Gua.


(** ** Ordering guarantees *)

(** ** ReadMyWrites *)
Definition read_my_writes (h: Event_structure) (w: Witness): Prop := 
  rel_incl (so h) (vis w).

(** ** MonotonicReads *)
Definition monotonic_reads (h: Event_structure) (w: Witness): Prop := 
  rel_incl (composition (vis w) (so h)) (vis w).

(** ** CausalVisibility *)
Global Definition causal_visibility (h: Event_structure) (w: Witness): Prop := 
  rel_incl (tc (union_rel (so h) (vis w))) (vis w).

(** ** CausalArbitration *)
Global Definition causal_arbitration (h: Event_structure) (w: Witness): Prop := 
  rel_incl (tc (union_rel (so h) (ar w))) (ar w).

(** ** Causality *)
Global Definition causality (h: Event_structure) (w: Witness): Prop := 
  causal_visibility h w /\ causal_arbitration h w.

Section Map.

Definition total_map (A : Type) := Id -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A : Type} (m : total_map A)
                    (x : Id) (v : A) :=
  fun x' => if eqb_id x x' then v else m x'.

Definition t_find {A : Type} (m : total_map A) (x : Id) := m x.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : Id) (v : A) :=
 (x !-> Some v ; m).

Definition find {A : Type} (m : partial_map A) (x : Id) := m x.
End Map.

Module Type RDT.

Parameter data_type: nat.
Parameter Ival_type: Type.
Parameter Rval_type : Type.
Parameter Op_type: Type.

Definition event_type_map := Id -> Op_type.
Definition event_input_map := Id -> Ival_type.

Definition event_rval_map := Id -> option Rval_type.

(*
Parameter event_op_map : total_map Operation.

Check event_op_map.

Parameter event_rval_map : partial_map Rval_type.
*)
(*
Module Import id_pair := PairOrderedType Nat_as_OT Nat_as_OT.
Module Import M := FMapList.Make(id_pair).
Definition Event_Op_map := M.t Operation.
Definition Event_Rval_map := M.t Rval_type.
*)

(*
Inductive Op_set : Type := 
  | op_empty
  | op (i: Id) (t: Op_type) (v: option Ival_type) (p: Op_set).

Inductive Rval_set: Type := 
  | rval_empty
  | rval (i: Id) (v: option Rval_type) (p: Rval_set).

(** ** Return value of an event *)
Fixpoint rval_of (e: Event) (s: Rval_set): option Rval_type := 
  match s with
  | rval_empty  => None
  | rval i v s' => if eqb_id i e.(id) then v
                   else rval_of e s'
  end.
*)

Parameter Fun : set Event -> Witness -> Event -> 
    event_type_map -> event_input_map -> event_rval_map -> option Rval_type.

End RDT.

(** ** Framework for consistency models *)

Module CModel (T: RDT) (G: Ord_Gua).

Import T.
Import G.


Definition admitted_execution (h: Event_structure) 
              (eo: event_type_map)(ei: event_input_map) (ev: event_rval_map): Prop :=
  exists w, 

  (** ** Well-formed witness relations *) 
  (well_formed_witness h w) /\

  (** ** Ordering guarantees *)
  (ordering_guarantee h w) /\

  (** ** return value guarantee *)
  (forall e: Event, In _ h.(events) e -> 
                        Fun (vis_refl e w) w e eo ei ev = ev e.(id)).

End CModel.
