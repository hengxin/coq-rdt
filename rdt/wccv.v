From RDT Require Export framework.
Require Import Nat.
Require Import Relations.
Require Import Ensembles.

Set Implicit Arguments.

Module Causal_Consistency.

Module G_CC <: Ord_Gua.

Definition ordering_guarantee (h: Event_structure) (w: Witness): Prop :=  
  causality h w.

End G_CC.

Module EPick.
Parameter pick : set Event -> Event.
Axiom pick_singleton :
  forall e, pick (Singleton _ e) = e.
Axiom pick_in :
  forall s, s (pick s).
End EPick.

(*
Parameter e_v : Event.

Definition pick_last (s: set Event) (ar: Rar) :=
  EPick.pick (fun w => (~(exists w, ar e_v w) /\ w = e_v) \/
                        ((exists w, s w /\ ar e_v w) /\ ar e_v w /\ 
                          ~(exists w', s w' /\ ar w' w))).
*)

Module Reg <: RDT.

Definition data_type := 1.
Definition Ival_type := nat.
Definition Rval_type := nat.
Definition Op_type := nat.

Definition event_type_map := Id -> Op_type.
Definition event_input_map := Id -> Ival_type.
Definition event_rval_map := Id -> option Rval_type.

Definition latest_write (w: Witness): set Event := 
  fun x => ~(exists e, (ar w) x e).

Definition writes (s: set Event) (t: event_type_map): set Event :=
  fun x => s x /\ ((t x.(id))=1).

Definition pick_last (s: set Event) (ar: Rar) :=
  EPick.pick (fun x => s x /\ ~(exists e, s e /\ ar x e)).

(** ** s: visible events of e*)
Definition Fun (s: set Event) (w: Witness) (e: Event) 
            (t: event_type_map)(input: event_input_map) (rval: event_rval_map): option Rval_type := 
  match eqb (t e.(id)) 1 with
  | true => None (*write*)
  | false => rval (id (pick_last (writes s t) w.(ar)))
  end.

End Reg.

Import G_CC.
Import Reg.

Module CC_Model := CModel Reg G_CC.

End Causal_Consistency.