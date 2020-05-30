(*********************************************************************)
(*             A Formal Hierarchy of Weak Memory Models              *)
(*                                                                   *)
(*   Jade Alglave INRIA Paris-Rocquencourt, France.                  *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique. All rights reserved. This file is distributed    *)
(*  under the terms of the Lesser GNU General Public License.        *)
(*********************************************************************)

Require Import ZArith.
Require Import Ensembles.
From dev Require Export util.

Set Implicit Arguments.

Ltac decide_equality := decide equality; auto with equality arith.

(** * Basic types *)

(** ** Words *)
  (** We abstract from word-size and alignment issues for now,
        modelling both memory addresses and the values that may be
        stored in them by natural numbers. *) 

Definition Word := nat.

(** *** Addresses *)
Definition Address := Word.

(** *** Values *)
Definition Value := Word.

(** ** Processors *)
  (** Processors are indexed by natural numbers. *)

Definition Proc := nat.

Lemma eqProc_dec : forall (x y: Proc), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqProc_dec : equality.

(** The model is expressed in terms of allowable orderings on events:
      individual reads and writes to memory, and
      memory barrier events.  Each instance of an instruction in a
      program execution may give rise to multiple events, as described
      by the instruction semantics.  We abstract from
      the details of instructions, but we record in each event the
      instruction instance id (an iiid) that gave rise to it, so that
      we can refer to the program order over the instruction
      instances.  An instruction instance id specifies the processor
      on which the instruction was executed together with the index of
      the program-order point at which it was executed (represented by
      a natural number).*)

(** ** Index in program order *)

Definition program_order_index := nat.
Lemma eqPoi_dec : forall (x y: program_order_index), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
Hint Resolve eqPoi_dec : equality.

(** ** Iiid: instruction identifier *)

Record Iiid  : Set := mkiiid {
  proc : Proc;
  poi: program_order_index }.
Lemma eqIiid_dec : forall (x y: Iiid), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined. 
Hint Resolve eqIiid_dec : equality.

(** Each event has an event instance id (eiid), the associated
      instruction instance id (iiid), and an action.  An action is
      either an access, with a direction (read or write),
      a memory location specified by an address, and a value. *)

(** ** Eiid: unique event identifier *)

Definition Eiid := nat.
Lemma eqEiid_dec : forall (x y: Eiid), {x=y} + {x<>y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqEiid_dec : equality.

(** ** Directions
          i.e. read or write*)

Inductive Dirn : Set :=
  | R : Dirn
  | W : Dirn.
Lemma eqDirn_dec : forall (x y: Dirn), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqDirn_dec.

(** ** Location:
          - a memory location is specified by an address*)

Definition Location := Address.

Lemma eqLoc_dec : forall (x y: Location), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqLoc_dec : equality.

(** ** Action:
          - an access specified by a polarity, a location and a value *)

Parameter Synchronization : Set.
Lemma eqSynchronization_dec : forall (x y: Synchronization), {x=y} + {x<>y}.
Proof.
Admitted.

Hint Resolve eqSynchronization_dec : equality.

Inductive Action : Set :=
  | Access : Dirn -> Location -> Value -> Action.

Lemma eqAction_dec : forall (x y: Action), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqAction_dec : equality.

(** ** Event:
      - an unique identifier; 
      - the associated index in program order and the proc; 
      - the associated action *)

Record Event : Set := mkev {
  eiid : Eiid; 
  iiid : Iiid;
  action : Action}.
Lemma eqEv_dec : forall (x y: Event), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqEv_dec : equality.

Lemma eqEvc_dec : forall (x y: Event*Event), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqEvc_dec : equality.

Module OEEvt.
Parameter LE : Rln Event -> Rln Event.
Lemma OE : forall (s S:set Event) (r:Rln Event),
  Included _ s S ->
  partial_order r s -> 
  rel_incl r (LE r) /\
  linear_strict_order (LE r) S.
Proof.
Admitted.
Lemma le_lso : forall (s:set Event) (r:Rln Event),
  linear_strict_order r s -> LE r = r.
Proof.
Admitted.

End OEEvt.
Import OEEvt.
(** Finally, an event structure collects the events of a candidate execution. *)

(** ** Event structure: 
       - a set of events; 
       - the intra causality relation between events from a same instruction *)

(*note that we have to work in Type if we use Ensemble.*)

Record Event_struct : Type := mkes {
  events : set Event;
  iico : Rln Event}. 

(** * Program order *)
  (** We define program order as a relation over two events e1 and e2, 
        wrt to an event structure es; two events are in program order if:
        - both e1 and e2 are in the events of es;
        - both events have same processor;
        - the program order index of e1 is less than the program order index of e2.*)

Definition po (es: Event_struct) : set (Event*Event) :=
  fun c => match c with (e1,e2) =>
   (* both events have same processor *)
  (e1.(iiid).(proc) = e2.(iiid).(proc)) /\
  (* the program order index of e1 is less than the program order index of e2 *)
  (le e1.(iiid).(poi) e2.(iiid).(poi)) /\
  (* both e1 and e2 are in the events of e *)
  (In _ es.(events) e1) /\
  (In _ es.(events) e2)
  end.

Definition po_strict (es: Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
   (* both events have same processor *)
  (e1.(iiid).(proc) = e2.(iiid).(proc)) /\
  (* the program order index of e1 is less than the program order index of e2 *)
  (lt e1.(iiid).(poi) e2.(iiid).(poi)) /\
  (* both e1 and e2 are in the events of e *)
  (In _ es.(events) e1) /\
  (In _ es.(events) e2).

Definition po_iico (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    (po_strict E) e1 e2 \/ (iico E) e1 e2.

(** ** State constraints *)

Definition State_constraint := Location -> Value.

(** * Basic operations on data types *)

(** ** Location of an event *)

 Definition loc (e:Event) : (*option*) Location :=
  match e.(action) with
  | Access _ l _ => (*Some*) l
  end. 

(** ** Value of an event *)

Definition value_of (e:Event) : option Value :=
  match e.(action) with
  | Access _ _ v => Some v
  end.

(** ** Processors *)

(** *** Of an event *)

Definition proc_of (e:Event) : Proc := e.(iiid).(proc). 

(** *** Of an event structure *)

Definition procs (es: Event_struct) : set Proc := 
   fun p => exists e, 
     In _ es.(events) e /\ 
     p = proc_of e. 

(** ** Particular events of an event structure *)

Definition to_shared (s:set Event) : set (Event) :=
  fun e => In _ s e /\ exists l, exists a, l = a /\ loc e = (*Some*) l.

(** *** Loads *)

Definition reads (es:Event_struct) : set Event :=
  fun e => (In _ es.(events) e) /\ (exists l, exists v, e.(action) = Access R l v). 

(** *** Stores *)

Definition writes (es:Event_struct) : set Event :=
  fun e => (In _ es.(events) e) /\ (exists l, exists v, e.(action) = Access W l v).

(** * Proc issue order -- minimum syndical, cf. proc issue order chez alpha *)

Definition pio (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    loc e1 = loc e2 /\ po_iico E e1 e2.

(** * Well-formedness of an event structure *)

Definition well_formed_event_structure (E:Event_struct) : Prop :=
  (forall x y, po_iico E x y -> proc_of x = proc_of y) /\
  (forall e1 e2, In _ E.(events) e1 -> In _ E.(events) e2 ->
   (e1.(eiid) = e2.(eiid)) /\ (e1.(iiid) = e2.(iiid)) -> (e1 = e2)) /\
   Included _ (dom (iico E)) E.(events) /\
   Included _ (ran (iico E)) E.(events) /\
   acyclic (iico E) /\ (forall x y, poi (iiid x) = poi (iiid y) -> iico E x y) /\
    (forall e1 e2, (iico E) e1 e2 -> (e1.(iiid) = e2.(iiid))) /\
   trans (iico E).

(** * Write serializations *)

Definition Write_serialization := Rln Event.

Definition write_to (e:Event) (l:Location) : Prop :=
  exists v, action e = Access W l v.

Definition writes_to_same_loc_l (s:set Event) (l:Location) : set Event :=
  fun e => In _ s e /\ write_to e l.

(* ... whereas ws really is a relation on mem events only ... *)

Definition write_serialization_well_formed (s:set Event) (ws:Write_serialization) : Prop :=
  (forall l, linear_strict_order 
     (rrestrict ws (writes_to_same_loc_l s l)) 
       (writes_to_same_loc_l s l)) (*Hws_tot*) /\
  (forall x e, ws x e ->
   (exists l : Location,
    In _ (writes_to_same_loc_l s l) x /\
    In _ (writes_to_same_loc_l s l) e)) (*Hws_cands*).

Ltac destruct_ws H :=
  destruct H as [Hws_tot Hws_cands].

(** * Rfmaps *)

Definition Rfmap := Rln Event.

Definition read_from (e:Event) (l:Location) : Prop :=
  exists v, action e = Access R l v.

Definition rfmaps (s:set Event) : Rln Event :=
  fun e1 => fun e2 =>
  In _ s e1 /\ In _ s e2 /\
  exists l, write_to e1 l /\ read_from e2 l.

Definition no_intervening_write (e1 e2:Event) (s:Rln Event): Prop :=
  s e1 e2 /\
  forall l, write_to e1 l ->
    ~(exists e3, write_to e3 l /\ s e1 e3 /\ s e3 e2).

Definition ls (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    In _ (reads E) e1 /\ In _ (writes E) e2 /\ (po_iico E) e1 e2.

Definition rfmaps_well_formed (E:Event_struct) (s:set Event) (rf:Rfmap) : Prop :=
  (forall er, exists ew, In _ s ew /\ rf ew er) /\ (*Hrf_init*) 
  (forall e1 e2, rf e1 e2 -> (rfmaps s) e1 e2) /\ (*Hrf_cands*) 
   (forall x w1 w2, rf w1 x -> rf w2 x ->
    w1 = w2).  (*Hrf_uni*)

Ltac destruct_rf H :=
  destruct H as [Hrf_init [Hrf_cands Hrf_uni]].

(** * Frmaps *)

Definition Frmap := Rln Event.

(* ... thus fr is too on mem only *)

Definition frmaps (s:set Event) (rf:Rfmap) (ws:Write_serialization) : Frmap :=
  fun er => fun ew =>
    In _ s er /\ In _ s ew /\
    exists wr, rf wr er /\ ws wr ew.  

(** * AB orderings *)

Definition AB := Rln Event. 

Definition ab_well_formed (s:set Event) (abc : AB) :=
  (forall x y, abc x y -> In _ s x /\ In _ s y /\ x<>y).

(** * Execution Witness *)

Record Execution_witness : Type := mkew {
  ws : Write_serialization;
  rf : Rfmap }.
  
Definition fr (E:Event_struct) (X:Execution_witness) : Frmap :=
  frmaps (events E) (rf X) (ws X).
Definition rf_intra (X:Execution_witness) : Rfmap :=
  fun ew => fun er => (rf X) ew er /\ proc_of ew = proc_of er.
Definition rf_inter (X:Execution_witness) : Rfmap :=
  fun ew => fun er => (rf X) ew er /\ proc_of ew <> proc_of er.

(** ** Initial and final states *)

Definition init (X:Execution_witness) : set Event :=
  fun x => exists wx, (rf X) wx x /\ ~(exists ew, (ws X) ew wx).

Definition final (X:Execution_witness) : set Event :=
  fun x => ~(exists e, (ws X) x e).

(** * Finally, definition of a valid execution *)
  
(** ** happens before *)

Definition hb (E:Event_struct) (X:Execution_witness) : Rln Event :=
  rel_union (rel_union (rf X) (fr E X)) (ws X).
Definition sc_check (E:Event_struct) (X:Execution_witness) : Prop :=
  acyclic (rel_union (po_iico E) (hb E X)).

Definition compete E : Rln Event :=
  fun e1 => fun e2 =>
  (events E) e1 /\ (events E) e2 /\
  loc e1 = loc e2 /\ proc_of e1 <> proc_of e2 /\
  (writes E e1 \/ writes E e2).

Parameter dp : Event_struct -> Rln Event.
(*Hypothesis dp_valid : forall (E:Event_struct),
  rel_incl (dp E) (po_iico E) /\ trans (dp E) /\
  forall x y, dp E x y -> reads E x.*)
Lemma dp_valid : forall (E:Event_struct),
  rel_incl (dp E) (po_iico E) /\ trans (dp E) /\
  forall x y, dp E x y -> reads E x.
Proof.
Admitted.

Module Type Archi.
Parameter ppo : Event_struct -> Rln Event.
(*Hypothesis ppo_valid : forall (E:Event_struct),
  rel_incl (ppo E) (po_iico E).*)
Lemma ppo_valid : forall (E:Event_struct),
  rel_incl (ppo E) (po_iico E).
Proof.
Admitted.

Parameter intra : bool.
Parameter inter : bool.

Parameter abc : Event_struct -> Execution_witness -> Rln Event.
(*Hypothesis ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, abc E X x y -> In _ (events E) x /\ In _ (events E) y.
*)
Lemma ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Proof.
Admitted.

Parameter stars : Event_struct -> Execution_witness -> set Event.
Parameter Cs : Type.
Parameter cs : Event_struct -> Execution_witness -> Location -> Cs -> Prop.
Parameter evts : Cs -> set Event.
Parameter lockc : Event_struct -> Execution_witness -> Location -> Rln Event.
Definition lock E X := fun e1 => fun e2 => exists l, lockc E X l e1 e2.
End Archi.

Module Wmm (A : Archi).
Import A.

Definition ghb (E:Event_struct) (X:Execution_witness) : 
  Rln Event :=
  match inter,intra with
  | true,true =>
    rel_union (rf_inter X) (rel_union (rf_intra X) (rel_union (abc E X)
      (rel_union (rel_union (ws X) (fr E X)) (ppo E))))
  | true,false =>
    rel_union (rf_inter X) (rel_union (abc E X) (rel_union (rel_union (ws X) (fr E X)) 
      (ppo E)))
  | false,true =>
    rel_union (rf_intra X) (rel_union (abc E X) (rel_union (rel_union (ws X) (fr E X)) 
      (ppo E)))
  | false,false =>
    rel_union (abc E X) (rel_union (rel_union (ws X) (fr E X)) 
      (ppo E))
  end.

Definition valid_execution (E:Event_struct) (X:Execution_witness) : Prop :=
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) /\
  acyclic (rel_union (hb E X) (pio E)) /\ (* uniproc: per location coherence *) 
  acyclic (rel_union (rf X) (dp E)) /\ (* thin *)
  acyclic (ghb E X).

Definition mrfi X :=
  mrel intra (rf_intra X).
Definition mrfe X :=
  mrel inter (rf_inter X).
Definition mrf X :=
  rel_union (mrfi X) (mrfe X).
Definition mhb (E:Event_struct) (X:Execution_witness) : 
  Rln Event :=
  match inter,intra with
  | true,true =>
    rel_union (rf_inter X) (rel_union (rf_intra X) (rel_union (ws X) (fr E X)))
  | true,false =>
    rel_union (rf_inter X) (rel_union (ws X) (fr E X))
  | false,true =>
    rel_union (rf_intra X) (rel_union (ws X) (fr E X))
  | false,false =>
    (rel_union (ws X) (fr E X))
  end.
Definition mhb' (E:Event_struct) (X:Execution_witness) : Rln Event :=
  fun e1 => fun e2 => 
    (rel_union (rel_union (mhb E X) (rel_seq (ws X) (mrf X))) (rel_seq (fr E X) (mrf X))) e1 e2.

Ltac destruct_valid H :=
  destruct H as [[Hws_tot Hws_cands] [[Hrf_init [Hrf_cands Hrf_uni]] [Hsp [Hth Hvalid]]]]; 
  unfold write_serialization_well_formed in Hws_tot.

(*Goal forall E X, valid_execution E X -> True.
intros E X Hvalid.
destruct_valid Hvalid. *)

End Wmm.
