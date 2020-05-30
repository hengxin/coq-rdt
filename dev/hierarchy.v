(*********************************************************************)
(*             A Formal Hierarchy of Weak Memory Models              *)
(*                                                                   *)
(*   Jade Alglave INRIA Paris-Rocquencourt, France.                  *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique. All rights reserved. This file is distributed    *)
(*  under the terms of the Lesser GNU General Public License.        *)
(*********************************************************************)
Require Import Ensembles.
Require Import Bool.
From dev Require Export util.
From dev Require Export wmm.
From dev Require Export basic.
Set Implicit Arguments.

Module Hierarchy.

Module Weaker (A1 A2 : Archi).

Definition bot_ghb1 (E:Event_struct) (X:Execution_witness) := 
         (rel_union (rel_union (ws X) (fr E X)) (A1.ppo E)).
Definition bot_ghb2 (E:Event_struct) (X:Execution_witness) := 
        (rel_union (rel_union (ws X) (fr E X)) (A2.ppo E)).

Definition bimpl (b1 b2:bool) : Prop:=
  if (negb b1) || b2 then True else False.
Definition rf_impl (rf1 rf2 : bool) :=
  bimpl rf1 rf2.
Definition ppo_incl (ppo1 ppo2 : Event_struct -> Rln Event) :=
  forall E, rel_incl (ppo1 E) (ppo2 E).
Definition weaker := (*A1 incl in A2*)
  ppo_incl (A1.ppo) (A2.ppo) /\
  bimpl (A1.intra) (A2.intra) /\
  bimpl (A1.inter) (A2.inter). 

Ltac destruct_wk H :=
  destruct H as [Hppoi [Hrfii Hrfei]].

Import A1. Import A2.
Module A1Basic := Basic A1.
Import A1Basic.
Module A2Basic := Basic A2.
Import A2Basic.
Module A1Wmm := Wmm A1.
Import A1Wmm.
Module A2Wmm := Wmm A2.
Import A2Wmm.

Module A1n <: Archi.
Definition ppo := A1.ppo.
Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
  apply A1.ppo_valid.
Qed.
Definition inter := A1.inter.
Definition intra := A1.intra.
Definition abc (E:Event_struct) (X:Execution_witness) : Rln Event := 
  fun e1 => fun e2 => False.
Lemma ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Proof.
intros E X x y Hxy. inversion Hxy.
Qed.
Parameter Cs : Type.
Parameter cs : Event_struct -> Execution_witness -> Location -> Cs -> Prop.
Parameter evts : Cs -> set Event.
Parameter lockc : Event_struct -> Execution_witness -> Location -> Rln Event.
Definition lock E X := fun e1 => fun e2 => exists l, lockc E X l e1 e2.
Parameter stars : Event_struct -> Execution_witness -> set Event.
End A1n.

Module A2n <: Archi.
Definition ppo := A2.ppo.
Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
  apply A2.ppo_valid.
Qed.
Definition inter := A2.inter.
Definition intra := A2.intra.
Definition abc (E:Event_struct) (X:Execution_witness) : Rln Event := 
  fun e1 => fun e2 => False.
Lemma ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Proof.
intros E X x y Hxy. inversion Hxy.
Qed.
Parameter Cs : Type.
Parameter cs : Event_struct -> Execution_witness -> Location -> Cs -> Prop.
Parameter evts : Cs -> set Event.
Parameter lockc : Event_struct -> Execution_witness -> Location -> Rln Event.
Definition lock E X := fun e1 => fun e2 => exists l, lockc E X l e1 e2.
Parameter stars : Event_struct -> Execution_witness -> set Event.
End A2n.

Import A1n. Import A2n.
Module A1nBasic := Basic A1n.
Import A1nBasic.
Module A2nBasic := Basic A2n.
Import A2nBasic.
Module A1nWmm := Wmm A1n.
Import A1nWmm.
Module A2nWmm := Wmm A2n.
Import A2nWmm.

Section Char.

Definition check (E:Event_struct) (X:Execution_witness) := 
  acyclic (rel_union (mrf X) (bot_ghb2 E X)).

Lemma bot_ghb_incl :
  forall E X,
  weaker ->
  rel_incl (bot_ghb1 E X) (bot_ghb2 E X).
Proof.
unfold bot_ghb1; unfold bot_ghb2;
intros E X H12 x y Hxy; 
destruct_wk H12.
    inversion Hxy as [Hws_fr | Hre].
      left; auto.
      right; apply (Hppoi E x y Hre).        
Qed.

Lemma ghb2_is_mhb_ppo2 :
  forall E X,
  ghb E X = rel_union (mhb E X) (A2.ppo E).
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra;
unfold ghb; unfold mhb; rewrite Hinter; rewrite Hintra;
unfold abc; intros E X; apply ext_rel; split; intro Hxy; auto.

  inversion Hxy as [Hrfe | Hr].
    left; left; auto.
    inversion Hr as [Hrfi | Hre].
      left; right; left; auto.
      inversion Hre as [Ht | Hres].
        inversion Ht.
        inversion Hres as [Hws_fr | Hppo].
          left; right; right; auto.
            right; auto.

  inversion Hxy as [Hr | Hppo].
    inversion Hr as [Hrfe | Hre].
      left; auto.
      inversion Hre as [Hrfi | Hws_fr].
        right ; left; auto.
          right; right; right; left; auto.
          right; right; right; right; auto.

  inversion Hxy as [Hrfi | Hr].
      left; left; auto.
      inversion Hr as [Ht | Hre].
        inversion Ht.
        inversion Hre as [Hws_fr | Hppo].
          left; right; auto.
            right; auto.

  inversion Hxy as [Hr | Hppo].
    inversion Hr as [Hrfi | Hre].
      left; auto.
          right; right; left; auto.
          right; right; right; auto.

  inversion Hxy as [Hrfi | Hr].
      left; left; auto.
      inversion Hr as [Ht | Hre].
        inversion Ht.
        inversion Hre as [Hws_fr | Hppo].
          left; right; auto.
            right;auto.

  inversion Hxy as [Hr | Hppo].
    inversion Hr as [Hrfi | Hre].
      left; auto.
          right; right; left; auto.
          right; right; right; auto.

  inversion Hxy as [Ht | Hre].
        inversion Ht.
        inversion Hre as [Hws_fr | Hppo].
          left; auto.
            right; auto.

  inversion Hxy as [Hws_fr | Hppo].
          right; left; auto.
          right; right; auto.
Qed.

Lemma ghb2_eq :
  forall E X,
  ghb E X = rel_union (mrf X) (bot_ghb2 E X).
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra;
unfold ghb; unfold mrf; unfold mrfe; unfold mrfi; rewrite Hinter; rewrite Hintra;
unfold bot_ghb2;
unfold abc; intros E X; apply ext_rel; split; intro Hxy; auto.

  inversion Hxy as [Hrfe | Hr].
    left; simpl; right; auto.
    inversion Hr as [Hrfi | Hre].
      left; simpl; left; auto.
      inversion Hre as [Ht | Hres].
        inversion Ht.
        right; auto.

  inversion Hxy as [Hrf | Hor].
    inversion Hrf as [Hrfi | Hrfe].
      right; simpl; left; auto.
      left; auto.
        right; right; right; auto.

  inversion Hxy as [Hrfi | Hor].
      left; right; auto.
          inversion Hor as [Ht | Hbghb].
            inversion Ht.
            right; auto.

  inversion Hxy as [Hrf | Hr].
    inversion Hrf as [Hrfi | Hrfe].
      inversion Hrfi.
      left; auto.
           right; right;auto.

  inversion Hxy as [Hrfi | Hor].
      left; left; auto.
          inversion Hor as [Ht | Hbghb].
            inversion Ht.
            right; auto.

  inversion Hxy as [Hrf | Hor].
    inversion Hrf as [Hrfi | Hrfe].
      left; auto.
      inversion Hrfe.
          right; right; auto.

  inversion Hxy as [Ht | Hre].
        inversion Ht.
            right; auto.

  inversion Hxy as [Hort | Hor].
    inversion Hort; inversion H.
       right; auto.
Qed.

Lemma ghb_incl :
  forall E X,
  weaker ->
  rel_incl (A1nWmm.ghb E X) (A2nWmm.ghb E X).
Proof.
intros E X; rewrite (ghb2_eq E X).
unfold A1nWmm.ghb; unfold A1n.ppo; unfold mrf; unfold mrfe; unfold mrfi;
intros H12 x y Hxy; case_eq inter; case_eq intra; 
intros Hintra2 Hinter2; case_eq A1n.inter; case_eq A1n.intra;
intros Hintra1 Hinter1; rewrite Hintra1 in *; rewrite Hinter1 in *.
  (*A1 : true true ; A2 : true true*)
  inversion Hxy as [Hrfi | Hr].
    left; right; auto.
    inversion Hr as [Hrfi | Hre].
      left; left; auto.
      inversion Hre as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb1 E X) in Hres.
      apply bot_ghb_incl; auto.
  (*A1 : false true ; A2 : true true*)
  inversion Hxy as [Hrfe | Hr].
    left; right; auto.
      inversion Hr as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hr;
      apply bot_ghb_incl; auto.
  (*A1 : true false ; A2 : true true*)  
  inversion Hxy as [Hrfi | Hr].
    left; left; auto.
      inversion Hr as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hr;
      apply bot_ghb_incl; auto.
  (*A1 : false false ; A2 : true true*)    
      inversion Hxy as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true true ; A2 : false true*)
  destruct H12 as (*[?*) [? [Himpl ?]](*]*).
  unfold A1n.intra in Hintra1; unfold A2n.intra in Hintra2;
  rewrite Hintra1 in Himpl; rewrite Hintra2 in Himpl; inversion Himpl.
  (*A1 : false true ; A2 : false true*)
  inversion Hxy as [Hrfe | Hr].
    left; right; auto.
      inversion Hr as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true false ; A2 : false true*)  
  destruct H12 as (*[?*) [? [Himpl ?]] (*]*).
  unfold A1n.intra in Hintra1; unfold A2n.intra in Hintra2;
  rewrite Hintra1 in Himpl; rewrite Hintra2 in Himpl; inversion Himpl.
  (*A1 : false false ; A2 : false true*)    
      inversion Hxy as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true true ; A2 : true false *)  
 destruct_wk H12.
  unfold A1n.inter in Hinter1; unfold A2n.inter in Hinter2;
  rewrite Hinter1 in Hrfei; rewrite Hinter2 in Hrfei; inversion Hrfei.
  (*A1 : false true ; A2 : true false *)  
 destruct_wk H12.
  unfold A1n.inter in Hinter1; unfold A2n.inter in Hinter2;
  rewrite Hinter1 in Hrfei; rewrite Hinter2 in Hrfei; inversion Hrfei.
  (*A1 : true false ; A2 : true false *)  
  inversion Hxy as [Hrfi | Hr].
    left; left; auto.
      inversion Hr as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : false false ; A2 : true false *)  
      inversion Hxy as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true true ; A2 : false false *)  
 destruct_wk H12.
  unfold A1n.inter in Hinter1; unfold A2n.inter in Hinter2;
  rewrite Hinter1 in Hrfei; rewrite Hinter2 in Hrfei; inversion Hrfei.
  (*A1 : false true ; A2 : false false *)  
 destruct_wk H12.
  unfold A1n.inter in Hinter1; unfold A2n.inter in Hinter2;
  rewrite Hinter1 in Hrfei; rewrite Hinter2 in Hrfei; inversion Hrfei. 
  (*A1 : true false ; A2 : false false *)  
  destruct H12 as (*[?*) [? [Himpl ?]](*]*).
  unfold A1n.intra in Hintra1; unfold A2n.intra in Hintra2;
  rewrite Hintra1 in Himpl; rewrite Hintra2 in Himpl; inversion Himpl.
  (*A1 : false false ; A2 : false false*)
      inversion Hxy as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
Qed.

Lemma v2_implies_v1 :
  forall E X,
  weaker ->
  A2nWmm.valid_execution E X ->
  A1nWmm.valid_execution E X.
Proof.
intros E X H21 Hv1.
destruct_valid Hv1.
 split; auto; [ |split; auto; split; auto].
split; auto; split; auto.
split.
  auto.
eapply incl_ac; [apply ghb_incl; auto | apply Hvalid].
Qed.

Lemma A2_impl_A1_check :
  forall E X,
  weaker ->
  A2nWmm.valid_execution E X ->
  A1nWmm.valid_execution E X /\ check E X.
Proof.
intros E X Hincl Hv2.
  split; [apply v2_implies_v1; auto |].
    destruct_valid Hv2; unfold check.
    rewrite (ghb2_eq E X) in Hvalid; auto.
Qed.

Lemma A1_check_impl_A2 :
  forall E X,
  weaker ->
  A1nWmm.valid_execution E X /\ check E X ->
  A2nWmm.valid_execution E X.
Proof.
intros E X Hincl [Hv1 Hc2].
  destruct_valid Hv1; split; auto; split; auto; split; auto.
    split.
    auto. 
    rewrite (ghb2_eq E X); unfold check in Hc2; auto.
Qed.

Lemma charac :
  forall E X,
  weaker ->
  ((A1nWmm.valid_execution E X /\ check E X) <->
    (A2nWmm.valid_execution E X)).
Proof.
intros E X; split; [intros [Hv1 Hc2] | intro Hv2].
  apply A1_check_impl_A2; auto.
  apply A2_impl_A1_check; auto.
Qed.

End Char.

Module A1b <: Archi.
Definition ppo := A1.ppo.
Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
  apply A1.ppo_valid.
Qed.
Definition inter := A1.inter.
Definition intra := A1.intra.
Parameter abc : Event_struct -> Execution_witness -> Rln Event.
Hypothesis ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Parameter Cs : Type.
Parameter cs : Event_struct -> Execution_witness -> Location -> Cs -> Prop.
Parameter evts : Cs -> set Event.
Parameter lockc : Event_struct -> Execution_witness -> Location -> Rln Event.
Definition lock E X := fun e1 => fun e2 => exists l, lockc E X l e1 e2.
Parameter stars : Event_struct -> Execution_witness -> set Event.
End A1b.

Definition ppo_sub E :=
  rel_sub (A1.ppo E) (A2.ppo E).
Definition mrfi2 X :=
  mrel (A2.intra) (rf_intra X).
Definition mrfe2 X :=
  mrel (A2.inter) (rf_inter X).
Definition mrf2 X :=
  rel_union (mrfi2 X) (mrfe2 X).
Definition mrfi1 X :=
  mrel (A1.intra) (rf_intra X).
Definition mrfe1 X :=
  mrel (A1.inter) (rf_inter X).
Definition mrf1 X :=
  rel_union (mrfi1 X) (mrfe1 X).
Definition rf_sub X :=
  rel_sub (mrf1 X) (mrf2 X).

Import A1b.
Module A1bBasic := Basic A1b.
Import A1bBasic.
Module A1bWmm := Wmm A1b.
Import A1bWmm.

Import A2n. Import A2nBasic. Import A2nWmm.

Section Barriers.

Definition fully_barriered (E:Event_struct) (X:Execution_witness) :=
  rel_incl (rel_union (ppo_sub E) (rel_seq (rf_sub X) (A2.ppo E))) (A1b.abc E X).

Lemma ghb1b_eq :
  forall E X,
  A1bWmm.ghb E X = rel_union (rel_union (ws X) (fr E X)) 
                                        (rel_union (rel_union (mrf1 X) (A1.ppo E)) 
                                            (A1b.abc E X)) .
Proof.    
intros E X; unfold A1bWmm.ghb; unfold mrf1; unfold mrfi1; unfold mrfe1; 
  unfold A1b.ppo; unfold A1b.inter; unfold A1b.intra;
  case_eq A1.inter; case_eq A1.intra; intros Hintra Hinter; simpl;
  apply ext_rel; split; intro Hxy.
  
  inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
    inversion Hr as [Hrfi | Hre].
      right; left; left; left; auto.
      inversion Hre as [Hab | Hres].
        right; right; auto.
        inversion Hres as [Hws_fr | Hppo].
          left; auto.
            right; left; right; auto.

  inversion Hxy as [Hws_fr | Hr].
    right; right; right; left; auto.
    inversion Hr as [Hre | Hab].
      inversion Hre as [Hrf | Hppo].
        inversion Hrf as [Hrfi | Hrfe]; [right; left; auto | left; auto].
        right; right; right; right; auto.
      right; right; left; auto.

  inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
    inversion Hr as [Hab | Hre].
      right; right; auto.
      inversion Hre as [Hws_fr | Hppo].
        left; auto.
          right; left; right; auto.

  inversion Hxy as [Hws_fr | Hr].
    right; right; left; auto.
    inversion Hr as [Hre | Hab].
      inversion Hre as [Hrf | Hppo].
        inversion Hrf as [Ht | Hrfi].
          inversion Ht.
          left; auto.
        right; right; right; auto.
      right; left; auto.      

  inversion Hxy as [Hrfi | Hr].
    right; left; left; left; auto.
    inversion Hr as [Hab | Hre].
      right; right; auto.
      inversion Hre as [Hws_fr | Hppo].
        left; auto.
          right; left; right; auto.

  inversion Hxy as [Hws_fr | Hr].
    right; right; left; auto.
    inversion Hr as [Hre | Hab].
      inversion Hre as [Hrf | Hppo].
        inversion Hrf as [Hrfi | Ht].
          left; auto.
          inversion Ht.
        right; right; right; auto.
      right; left; auto.

  inversion Hxy as [Hab | Hr].
    right; right; auto.
    inversion Hr as [Hws_fr | Hppo].
      left; auto.
        right; left; right; auto.

  inversion Hxy as [Hws_fr | Hr].
    right; left; auto.
    inversion Hr as [Hre | Hab].
      inversion Hre as [Ht | Hppo].
        inversion Ht as [Ht1 | Ht2]; [inversion Ht1 | inversion Ht2].
        right; right; auto.
      left; auto.
Qed.

Lemma mhb'2_is_mhb'1_u_rf_sub :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  (A2nWmm.mhb' E X) = 
  rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
    (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X))).
Proof.
case_eq A2.inter; case_eq A2.intra; intros Hinter2 Hintra2;
case_eq A1.inter; case_eq A1.intra; intros Hinter1 Hintra1;
unfold mhb'; unfold mhb; unfold rf_sub; 
unfold A1bWmm.mhb'; unfold A1bWmm.mhb;
unfold A1bWmm.mrf; unfold mrf; unfold A1bWmm.mrfi; unfold mrfi; 
unfold A1bWmm.mrfe; unfold mrfe; unfold inter; unfold intra;
unfold A1b.inter; unfold A1b.intra; unfold mrf1; unfold mrf2;
unfold mrfi1; unfold mrfi2; unfold mrfe1; unfold mrfe2;
rewrite Hinter1; rewrite Hintra1; rewrite Hinter2; rewrite Hintra2; 
unfold abc; intros E X Hwk Hwf; apply ext_rel; split; intro Hxy; auto;
simpl in * |- *.

inversion Hxy as [Hr | Hsfr].
  inversion Hr as [Hre | Hsws].
  inversion Hre as [Hrfe | Hres].
  left; left; left; left; auto.
  inversion Hres as [Hrfi | Hws_rf].
    left; left; left; left; auto.
    left; left; left; left; right; auto.
  left; left; left; right; auto.
  left; left; right; auto.  

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hhb | Hsws].
    left; auto.
      left; right; auto.
      right; auto.
      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Hrfe].
      left; left; right; left; auto.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [? [? Ht]]; destruct Ht; contradiction.
    destruct Hsfr as [? [? Ht]]; destruct Ht; contradiction.

inversion Hxy as [Hu | Hsfr].
    inversion Hu as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hr].
        left; left; left; left; left; auto.
        inversion Hr as [Hrfi | Hwsfr].
        left; right; split.
          left; auto. 
          intro Hor; inversion Hor as [| Hrfe]; auto.
          destruct Hrfi; destruct Hrfe; contradiction.
        left; left; left; left; right; auto.

      destruct Hsws as [z [Hz Hurf]].
      inversion Hurf as [Hrfi | Hrfe].
      right; left.
      exists z; split; auto.
          split. left; auto. 
          intro Hor; inversion Hor as [| Hrfe]; auto.
          destruct Hrfi; destruct Hrfe; contradiction.

      left; left; left; right.
      exists z; split; auto.
          right; auto. 

      destruct Hsfr as [z [Hz Hurf]].
      inversion Hurf as [Hrfi | Hrfe].
      right; right.
      exists z; split; auto.
          split. left; auto. 
          intro Hor; inversion Hor as [| Hrfe]; auto.
          destruct Hrfi; destruct Hrfe; contradiction.

      left; left; right.
      exists z; split; auto.
          right; auto. 

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hwsfr].
        left; left; left; auto.
        left; left; right; right; auto.

      left; right; destruct Hsws as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Ht | Hrfe].
          inversion Ht. right; auto.
     right; destruct Hsfr as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Ht | Hrfe].
          inversion Ht. right; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Hrfe].
      left; left; right; left; auto.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

inversion Hxy as [Hu | Hsfr].
    inversion Hu as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hr].
        left; right; split.
          right; auto.
          intro Hor; inversion Hor as [Hrfi | Ht].
            destruct Hrfi; destruct Hrfe; contradiction.
             inversion Ht.
        inversion Hr as [Hrfi | Hwsfr].
        left; left; left; left.
          left; auto. 
        left; left; left; left; right; auto.

      destruct Hsws as [z [Hz Hurf]].
      inversion Hurf as [Hrfi | Hrfe].
      left; left; left; right.
      exists z; split; auto.
      left; auto.

      right; left; exists z; split; auto.
      split. right; auto.
      intro Hor; inversion Hor as [Hrfi | Ht].
        destruct Hrfe; destruct Hrfi; contradiction.
        inversion Ht; auto.

      destruct Hsfr as [z [Hz Hurf]].
      inversion Hurf as [Hrfi | Hrfe].
      left; left; right.
      exists z; split; auto.
          left; auto. 

      right; right.
      exists z; split; auto.
          split. right; auto. 
          intro Hor; inversion Hor as [Hrfi | Ht]; auto.
          destruct Hrfi; destruct Hrfe; contradiction.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hwsfr].
        left; left; right; auto.
        left; left; right; right; auto.

      left; right; destruct Hsws as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Hrfi | Ht].
          left; auto. inversion Ht; auto.
     right; destruct Hsfr as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Hrfi | Ht].
          left; auto. inversion Ht. 

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Hrfe].
      left; left; right; left; auto.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

inversion Hxy as [Hu | Hsfr].
    inversion Hu as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hr].
        left; right; split.
          right; auto.
          intro Hor; inversion Hor as [Ht | Hrfi].
             inversion Ht.
            destruct Hrfi; destruct Hrfe; contradiction.
        inversion Hr as [Hrfi | Hwsfr].
        left; right.
          split.
          left; auto.
          intro Hor; inversion Hor; auto. 
        left; left; left; left; auto.

      destruct Hsws as [z [Hz Hurf]].
        right; left.
      exists z; split; auto.
      split; auto.
      intro Hor; inversion Hor; auto.

      destruct Hsfr as [z [Hz Hurf]].
      right; right.
      exists z; split; auto.
      split; auto.
      intro Hor; inversion Hor; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; left; right; right; auto.

      left; right; destruct Hsws as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Ht1 | Ht2].
          inversion Ht1; auto. inversion Ht2; auto.
     right; destruct Hsfr as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Ht1 | Ht2].
          inversion Ht1; auto. inversion Ht2; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Hrfe].
      left; left; right; left; auto.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

inversion Hxy as [Hu | Hsfr].
    inversion Hu as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hr].
        left; left; left; left; left; auto.
        left; left; left; left; right; right; auto.       

      destruct Hsws as [z [Hz Hurf]].
        left; left; left; right.
      exists z; split; auto.
      inversion Hurf; auto. inversion H; auto. right; auto.

      destruct Hsfr as [z [Hz Hurf]].
      left; left; right.
      exists z; split; auto.
      inversion Hurf; auto. inversion H; auto. right; auto.

destruct_wk Hwk; rewrite Hinter1 in Hrfii; 
  rewrite Hinter2 in Hrfii; inversion Hrfii.
destruct_wk Hwk; rewrite Hinter1 in Hrfii; 
  rewrite Hinter2 in Hrfii; inversion Hrfii.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hr | Hsws].
    inversion Hr as [Hrfe | Hwsfr].
        left; left; left; left; left; auto.
        left; left; left; left; right; auto.

      left; left; left; right; auto.
      left; left; right; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Huf | Hsws].
      inversion Huf as [Hrfe | Hwsfr].
        left; left; left; auto.
        left; left; right; auto.

      left; right; auto.
      right; auto. 

      destruct Hsub as [Hrf ?]; inversion Hrf as [Ht | Hrfe].
      inversion Ht.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

destruct_wk Hwk; rewrite Hinter1 in Hrfii; 
  rewrite Hinter2 in Hrfii; inversion Hrfii.
destruct_wk Hwk; rewrite Hinter1 in Hrfii; 
  rewrite Hinter2 in Hrfii; inversion Hrfii.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hr | Hsws].
    inversion Hr as [Hrfe | Hwsfr].
        left; right; split.
          right; auto.
          intro Hor; inversion Hor; auto.

      left; left; left; left; auto.
       right; left; destruct Hsws as [z [? Hor]]; exists z; split; auto.
         inversion Hor as [Ht | Hrfe].
           inversion Ht.
           split. right; auto.
             intro Hort; inversion Hort as [Ht1 | Ht2]; auto.
       right; right; destruct Hsfr as [z [? Hor]]; exists z; split; auto.
         inversion Hor as [Ht | Hrfe].
           inversion Ht.
           split. right; auto.
             intro Hort; inversion Hort as [Ht1 | Ht2]; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; left; right; auto.

      destruct Hsws as [? [? Hor]]; inversion Hor as [t1 | t2].
        inversion t1; auto. inversion t2; auto.
      destruct Hsfr as [? [? Hor]]; inversion Hor as [t1 | t2].
        inversion t1; auto. inversion t2; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Ht | Hrfe].
      inversion Ht.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

destruct_wk Hwk; rewrite Hintra1 in Hrfei; 
  rewrite Hintra2 in Hrfei; inversion Hrfei.
destruct_wk Hwk; rewrite Hintra1 in Hrfei; 
  rewrite Hintra2 in Hrfei; inversion Hrfei.

destruct_wk Hwk; rewrite Hintra1 in Hrfei; 
  rewrite Hintra2 in Hrfei; inversion Hrfei.
destruct_wk Hwk; rewrite Hintra1 in Hrfei; 
  rewrite Hintra2 in Hrfei; inversion Hrfei.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hr | Hsws].
    inversion Hr as [Hrfi | Hwsfr].
        left; left; left; left; left; auto.
        left; left; left; left; right; auto.

      left; left; left; auto.
      left; left; right; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; auto.

      destruct Hsws as [z [? Hor]]; inversion Hor as [Hrfi | t2].
        left; right; exists z; split; auto. inversion t2; auto.
      destruct Hsfr as [z [? Hor]]; inversion Hor as [Hrfi | t2].
        right; exists z; split; auto. inversion t2; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Ht].
      left; left; left; auto.
      inversion Ht.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hor ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hr | Hsws].
    inversion Hr as [Hrfi | Hwsfr].
        left; right; split; auto.
          left; auto.
          intro Hor; inversion Hor; auto.

      left; left; left; left; auto.
      right; left; destruct Hsws as [z [? Hor]]; exists z; split; auto.
      split; auto. intro Hort; inversion Hort; auto.
      right; right; destruct Hsfr as [z [? Hor]]; exists z; split; auto.
      split; auto. intro Hort; inversion Hort; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; left; right; auto.

      destruct Hsws as [z [? Hor]]; inversion Hor as [t1 | t2].
        inversion t1; auto. inversion t2; auto. 
      destruct Hsfr as [z [? Hor]]; inversion Hor as [t1 | t2].
        inversion t1; auto. inversion t2; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Ht].
      left; left; left; auto.
      inversion Ht.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hor ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

destruct_wk Hwk; rewrite Hintra1 in Hrfei; 
  rewrite Hintra2 in Hrfei; inversion Hrfei.
destruct_wk Hwk; rewrite Hintra1 in Hrfei; 
  rewrite Hintra2 in Hrfei; inversion Hrfei.

destruct_wk Hwk; rewrite Hintra1 in Hrfei; 
  rewrite Hintra2 in Hrfei; inversion Hrfei.
destruct_wk Hwk; rewrite Hintra1 in Hrfei; 
  rewrite Hintra2 in Hrfei; inversion Hrfei.

destruct_wk Hwk; rewrite Hinter1 in Hrfii; 
  rewrite Hinter2 in Hrfii; inversion Hrfii.
destruct_wk Hwk; rewrite Hinter1 in Hrfii; 
  rewrite Hinter2 in Hrfii; inversion Hrfii.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hwsfr | Hsws].
        left; left; left; left; auto.

    destruct Hsws as [? [? Hor]]; inversion Hor as [Ht1 | Ht2]. 
    inversion Ht1; auto. inversion Ht2; auto.
    destruct Hsfr as [? [? Hor]]; inversion Hor as [Ht1 | Ht2]. 
    inversion Ht1; auto. inversion Ht2; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; left; auto.
        left; right; auto.

      right; auto. 

      destruct Hsub as [Hrf ?]; inversion Hrf as [Ht1 | Ht2].
      inversion Ht1.
      inversion Ht2.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Ht ?]]].
    inversion Ht as [t1 | t2]. inversion t1; auto. inversion t2; auto.
    destruct Hsfr as [z [Hws [Ht ?]]].
    inversion Ht as [t1 | t2]. inversion t1; auto. inversion t2; auto.
Qed. 

Lemma mhb'_ppo2_is_u_seq_int :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  tc (rel_seq (A2nWmm.mhb' E X) (tc (ppo E))) x y ->
  tc (rel_seq (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
    (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X)))) (tc (ppo E))) x y.
Proof.
intros E X x y Hwk Hwf Hxy.
rewrite (mhb'2_is_mhb'1_u_rf_sub X Hwk Hwf) in Hxy; auto.
Qed.

Lemma mhb'_ppo2_is_u_seq :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  tc (rel_seq (maybe (A2nWmm.mhb' E X)) (tc (ppo E))) x y ->
  tc (rel_seq (maybe (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
    (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X))))) (tc (ppo E))) x y.
Proof.
intros E X x y Hwk Hwf Hxy.
rewrite (mhb'2_is_mhb'1_u_rf_sub X Hwk Hwf) in Hxy; auto.
Qed.

Lemma mhb1_eq :
  forall E X x y,
  A1bWmm.mhb E X x y ->
  tc
  (rel_union (rel_union (ws X) (fr E X))
     (rel_union (rel_union (mrf1 X) (A1.ppo E)) 
     (A1b.abc E X) )) x y.
Proof.
unfold A1bWmm.mhb; case_eq A1.inter; case_eq A1.intra; intros Hintra Hinter;
unfold A1b.inter; unfold A1b.intra; unfold mrf1; unfold mrfi1; unfold mrfe1; 
rewrite Hinter; rewrite Hintra; intros E X x y Hxy; apply trc_step; simpl.

inversion Hxy as [Hrfe | Hr].
  right; left; left; right; auto.
  inversion Hr as [Hrfi | Hws_fr].
    right; left; left; left; auto.
    left; auto.

inversion Hxy as [Hrfe | Hws_fr].
  right; left; left; right; auto.
  left; auto.

inversion Hxy as [Hrfi | Hws_fr].
  right; left; left; left; auto.
  left; auto.

left; auto.  
Qed.

Lemma mhb'1_eq :
  forall E X x y,
  A1bWmm.mhb' E X x y ->
  tc
  (rel_union (rel_union (ws X) (fr E X))
     (rel_union (rel_union (mrf1 X) (A1.ppo E)) 
     (A1b.abc E X) )) x y.
Proof.
intros E X x y Hxy;
inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hmhb | Hsws].
    apply mhb1_eq; auto.

    destruct Hsws as [z [Hxz Hzy]]; apply trc_ind with z; apply trc_step.
      left; left; auto.
      right; left; left; auto.

    destruct Hsfr as [z [Hxz Hzy]]; apply trc_ind with z; apply trc_step.
      left; right; auto.
      right; left; left; auto.
Qed.

Axiom excluded_middle : forall (A:Prop), A \/ ~A.

Lemma ppo2_in_ghb1 :
  forall E X x y,
  fully_barriered E X ->
  ppo E x y ->
  A1bWmm.ghb E X x y.
Proof.
intros E X x y Hfb Hxy.
  generalize (excluded_middle (A1b.ppo E x y)); intro Hor.
  inversion Hor as [Hppo1 | Hnppo1].
   apply A1bBasic.ppo_in_ghb; auto.
   assert (ppo_sub E x y) as Hppos.
     split; auto.

   apply A1bBasic.ab_in_ghb; apply Hfb;
 left; auto.
Qed.

Lemma rf_sub_seq_ppo2_in_ab1 :
  forall E X x z y,
  fully_barriered E X ->
  rf_sub X x z ->
  ppo E z y ->
  A1b.abc E X x y.
Proof.
intros E X x z y Hfb Hxz Hzy; apply Hfb.
right.
exists z; split; auto.
Qed.

Lemma seq_implies_ghb1_int :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
 fully_barriered E X ->
  tc (rel_seq (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
   (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X)))) (tc (ppo E))) x y ->
  tc (A1bWmm.ghb E X) x y.
Proof.
intros E X x y Hwk Hwf Hfb Hxy.

induction Hxy.
  destruct H as [z [Hxz Hzy]].
    inversion Hxz as [Hu | Hs].
    inversion Hu as [Hmhb'1 | Hrf_sub].
      apply trc_ind with z.
        rewrite (ghb1b_eq E X).
        apply (mhb'1_eq Hmhb'1).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1; auto.
        apply (tc_incl Hincl Hzy).

        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
        rewrite (ghb1b_eq E X).
      apply trc_step; right; right.
       apply (rf_sub_seq_ppo2_in_ab1 Hfb Hrf_sub Hzz').
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1; auto.
        apply (tc_incl Hincl Htc).
         subst;        rewrite (ghb1b_eq E X).
      apply trc_step; right; right.
       apply (rf_sub_seq_ppo2_in_ab1 Hfb Hrf_sub Hzz').

  inversion Hs as [Hsws | Hsfr].
    destruct Hsws as [e [Hxe Hez]].
        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
    apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; left; auto.
        rewrite (ghb1b_eq E X).
      right; right. apply rf_sub_seq_ppo2_in_ab1 with z; auto. 
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1; auto.
        apply (tc_incl Hincl Htc).

  subst;     apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; left; auto. 
        rewrite (ghb1b_eq E X).
      right; right. apply rf_sub_seq_ppo2_in_ab1 with z; auto. 
    
    destruct Hsfr as [e [Hxe Hez]].

        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
    apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; right; auto.
        rewrite (ghb1b_eq E X).
      right; right;  apply rf_sub_seq_ppo2_in_ab1 with z; auto.
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1; auto.
        apply (tc_incl Hincl Htc).

  subst;     apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; right; auto.
        rewrite (ghb1b_eq E X).
      right; right;  apply rf_sub_seq_ppo2_in_ab1 with z; auto.

apply trc_ind with z; auto.
Qed.

Lemma seq_implies_ghb1 :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
 fully_barriered E X ->
  tc (rel_seq (maybe (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
   (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X))))) (tc (ppo E))) x y ->
  tc (A1bWmm.ghb E X) x y.
Proof.
intros E X x y Hwk Hwf Hfb Hxy.

induction Hxy.
  destruct H as [z [Hor Hzy]].
    inversion Hor as [Hxz | Heq].
      apply seq_implies_ghb1_int; auto.
        apply trc_step; exists z; auto.
   subst; generalize Hzy; apply tc_incl. 
  intros e1 e2 H12; apply ppo2_in_ghb1; auto.
 
  apply trc_ind with z; auto.
Qed.


Lemma ppo_ac :
  forall E, 
  well_formed_event_structure E ->
  ~(exists x, (ppo E) x x).
Proof.
unfold not;
intros E Hwf [x Hppo].
unfold well_formed_event_structure in Hwf.
generalize (ppo_valid Hppo); intro Hpo_iico.
apply (po_ac Hwf Hpo_iico).
Qed.

Lemma mhb_ac :
  forall E X,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(exists x, mhb E X x x).
Proof.
unfold not;
intros E X Hs [x Hx].
generalize (mhb_in_hb E X x x Hx); intro Hhb.
apply (hb_ac Hs Hhb).
Qed.

Lemma ghb2_cycle_implies_ghb1_cycle :
  forall E X x,
  weaker ->
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  fully_barriered E X ->
  tc (A2nWmm.ghb E X) x x ->
  exists y, tc (A1bWmm.ghb E X) y y.
Proof.
intros E X x Hwk Hwf Hs Hfb Hx.
rewrite (ghb2_is_mhb_ppo2 E X) in Hx.
assert (exists y, tc (rel_seq (maybe (mhb' E X)) (tc (A2.ppo E))) y y) as Hc.
eapply (mhb_union_ppo_cycle_implies_mhb'_seq_ppo_cycle2 X Hwf Hs Hx); auto; apply Hx.
destruct Hc as [y Hc].
generalize (mhb'_ppo2_is_u_seq Hwk Hwf Hc); intro Hcy.
exists y; apply (seq_implies_ghb1 Hwk Hwf Hfb Hcy).
Qed.

Lemma fb_implies_valid : (*barriers guarantee*)
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  fully_barriered E X ->
  A1bWmm.valid_execution E X -> 
  A2nWmm.valid_execution E X.
Proof.
intros E X Hincl Hwf Hfb Hva1.
  destruct_valid Hva1; split; auto; split; auto.
   split; auto; split; auto.
   split; auto. 
   split.
    auto. 
  unfold acyclic; unfold not; intros x Hx.
  assert (exists x, tc (ghb E X) x x) as Hc.
    exists x; auto.
  assert (write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
    split; auto; split; auto.
  generalize (ghb2_cycle_implies_ghb1_cycle Hincl Hwf Hs Hfb Hx); intros [y Hcy].
  apply (Hvalid y Hcy).
Qed.

Inductive AB (E:Event_struct) (X:Execution_witness) (fenb fenc:Rln Event) : Event -> Event -> Prop :=
  | Base : forall e1 e2,
      fenb e1 e2 -> AB E X fenb fenc e1 e2
  | Acumul : forall w1 r1 e2, 
      (rf_sub X) w1 r1 /\ fenc r1 e2 -> AB E X fenb fenc w1 e2.

Lemma barriers_placement :
  forall E X, 
  weaker ->
  well_formed_event_structure E ->
  A1b.abc E X = AB E X (ppo_sub E) (A2n.ppo E) ->
  A1bWmm.valid_execution E X -> 
  A2nWmm.valid_execution E X.
Proof.
intros E X Hwk Hwf Hab; apply fb_implies_valid; auto;
unfold fully_barriered; rewrite Hab.
intros x y Hxy; inversion Hxy as [Hb | Hc].
  apply Base; auto.
  destruct Hc as [z [Hrf Hppo]]; apply Acumul with z; auto.
Qed.

Definition wfb E X := rel_incl (ppo_sub E) (A1b.abc E X).

Lemma mrf_or :
  forall X x y,
  mrf2 X x y -> mrfe2 X x y \/ mrfi2 X x y.
Proof.
intros X x y Hxy.
inversion Hxy; [right; auto | left; auto].
Qed.

Lemma mrfi2_implies_same_proc :
  forall X x y, mrfi2 X x y -> proc_of x = proc_of y.
Proof.
intros X x y Hxy; unfold mrfi2 in Hxy;
case_eq A2.intra; intro Hi; rewrite Hi in Hxy; simpl in Hxy.
destruct Hxy; auto.
inversion Hxy.
Qed.
Lemma mrfe1_implies_diff_proc :
  forall X x y, mrfe1 X x y -> proc_of x <> proc_of y.
Proof.
intros X x y Hxy; unfold mrfe1 in Hxy;
case_eq A1.inter; intro Hi; rewrite Hi in Hxy; simpl in Hxy.
destruct Hxy; auto.
inversion Hxy.
Qed.

Lemma same_rfe_implies_rf_sub_is_rfi_sub :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  mrfe1 = mrfe2 ->
  rf_sub X = rel_sub (mrfi1 X) (mrfi2 X).
Proof.
intros E X Hwk Hwf Hmrf; apply (ext_rel (rf_sub X) (rel_sub (mrfi1 X) (mrfi2 X))); split; intro Hxy.
  destruct Hxy as [H2 H1].
  generalize (mrf_or H2); intro Hor.
  inversion Hor as [He | Hi].
    rewrite <- Hmrf in He.
    assert (mrf1 X x y) as Hc.
      right; auto.
    contradiction.
    split; auto.
      intro Hc; apply H1; left; auto.
  destruct Hxy as [H2 H1]; split.
    left; auto.
    intro Hc; apply H1. 
    inversion Hc as [Hi | He]; auto.
    generalize (mrfi2_implies_same_proc X x y H2); intro Heq.
    generalize (mrfe1_implies_diff_proc X x y He); intro Hdiff.
  contradiction.
Qed.

Lemma wfb_ppo_sub_in_ab1 :
  forall E X x y,
  wfb E X ->
  ppo_sub E x y ->
  A1b.abc E X x y.
Proof.
intros E X x y Hfb Hxy; apply Hfb.
auto.
Qed.

Lemma mhb_incl :
  forall E X x y, 
  weaker ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  mhb E X x y ->
  tc
    (rel_union (rel_union (ws X) (fr E X))
       (rel_union (rel_union (mrf1 X) (A1.ppo E))
          (A1b.abc E X) )) x y.
Proof.
case_eq A2.inter; case_eq A2.intra; intros Hintra2 Hinter2;
case_eq A1.inter; case_eq A1.intra; intros Hintra1 Hinter1;
unfold mhb; unfold mrf1; unfold mrfi1; unfold mrfe1; 
unfold inter; unfold intra;
rewrite Hintra2; rewrite Hinter2; rewrite Hintra1; rewrite Hinter1; simpl;
intros E X x y Hwk Hwfb HmrfX Hrfi_or Hxy.

  apply trc_step; inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
    inversion Hr as [Hrfi | Hre].
      right; left; left; left; auto.
      left; auto.

  apply trc_step; inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
    inversion Hr as [Hrfi | Hre].
      assert (mrfi2 X x y) as Hmrfi.
        unfold mrfi2; unfold intra; rewrite Hintra2; simpl; auto.
      inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].
        rewrite <- mrfi_eq in Hmrfi; inversion Hmrfi.

      generalize (mrfi_in_ppo x y Hmrfi); intro Hppo.
      generalize (excluded_middle (A1.ppo E x y)); intro Hor.
      inversion Hor as [H1 | Hn1].
        right; left; right; auto.
        right; right; apply Hwfb; split; auto.
      left; auto.

  assert ( (fun  (_ _ : Event) => False) = mrfe2 X) as Hmrf.
    rewrite <- HmrfX; trivial.
  unfold mrfe2 in Hmrf; rewrite Hinter2 in Hmrf; simpl in Hmrf.
  apply trc_step; inversion Hxy as [Hrfe | Hr].
    rewrite <- Hmrf in Hrfe; inversion Hrfe.
    inversion Hr as [Hrfi | Hre].
      right; left; left; left; auto.
      left; auto.

  assert ( (fun  (_ _ : Event) => False) = mrfe2 X) as Hmrf.
    rewrite <- HmrfX; trivial.
  unfold mrfe2 in Hmrf; rewrite Hinter2 in Hmrf; simpl in Hmrf.
  apply trc_step; inversion Hxy as [Hrfe | Hr].
    rewrite <- Hmrf in Hrfe; inversion Hrfe.  
    inversion Hr as [Hrfi | Hre].
      assert (mrfi2 X x y) as Hmrfi.
        unfold mrfi2; unfold intra; rewrite Hintra2; simpl; auto.
     inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].
        rewrite <- mrfi_eq in Hmrfi; inversion Hmrfi.

      generalize (mrfi_in_ppo x y Hmrfi); intro Hppo.
      generalize (excluded_middle (A1.ppo E x y)); intro Hor.
      inversion Hor as [H1 | Hn1].
        right; left; right; auto.
        right; right; apply Hwfb; split; auto.
      left; auto.

 destruct_wk Hwk;
 rewrite Hintra1 in Hrfii; 
  rewrite Hintra2 in Hrfii; inversion Hrfii.

  apply trc_step; inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
      left; auto.

 destruct_wk Hwk;
 rewrite Hintra1 in Hrfii; 
  rewrite Hintra2 in Hrfii; inversion Hrfii.
 
  assert ( (fun  (_ _ : Event) => False) = mrfe2 X) as Hmrf.
    rewrite <- HmrfX; trivial.
  unfold mrfe2 in Hmrf; rewrite Hinter2 in Hmrf; simpl in Hmrf.
  apply trc_step; inversion Hxy as [Hrfe | Hr].
    rewrite <- Hmrf in Hrfe; inversion Hrfe.  
      left; auto.

 destruct_wk Hwk;
 rewrite Hinter1 in Hrfei; 
  rewrite Hinter2 in Hrfei; inversion Hrfei.

 destruct_wk Hwk;
 rewrite Hinter1 in Hrfei; 
  rewrite Hinter2 in Hrfei; inversion Hrfei.

    apply trc_step; inversion Hxy as [Hrfi | Hre].
      right; left; left; left; auto.
      left; auto.

    apply trc_step; inversion Hxy as [Hrfi | Hre].
      assert (mrfi2 X x y) as Hmrfi.
        unfold mrfi2; unfold intra; rewrite Hintra2; simpl; auto.
     inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].
        rewrite <- mrfi_eq in Hmrfi; inversion Hmrfi.
      generalize (mrfi_in_ppo x y Hmrfi); intro Hppo.
      generalize (excluded_middle (A1.ppo E x y)); intro Hor.
      inversion Hor as [H1 | Hn1].
        right; left; right; auto.
        right; right; apply Hwfb; split; auto.
      left; auto.

 destruct_wk Hwk;
 rewrite Hinter1 in Hrfei; 
  rewrite Hinter2 in Hrfei; inversion Hrfei.

 destruct_wk Hwk;
 rewrite Hinter1 in Hrfei; 
  rewrite Hinter2 in Hrfei; inversion Hrfei.

 destruct_wk Hwk;
 rewrite Hintra1 in Hrfii; 
  rewrite Hintra2 in Hrfii; inversion Hrfii.

  apply trc_step; left; auto.
Qed.

Lemma ppo2_in_ghb1' :
  forall E X x y,
  wfb E X ->
  ppo E x y ->
  A1bWmm.ghb E X x y.
Proof.
intros E X x y Hfb Hxy.
  generalize (excluded_middle (A1b.ppo E x y)); intro Hor.
  inversion Hor as [Hppo1 | Hnppo1].
   apply A1bBasic.ppo_in_ghb; auto.
   assert (ppo_sub E x y) as Hppos.
     split; auto.

   apply A1bBasic.ab_in_ghb; apply Hfb; auto.
Qed.

Lemma wfb_seq_implies_ghb1' :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  tc (rel_seq (A2nWmm.mhb' E X) (tc (A2n.ppo E))) x y ->
  tc (A1bWmm.ghb E X) x y.
Proof.
intros E X x y Hwk Hwf Hfb Hmrf Hrfi_or Hxy.
rewrite (ghb1b_eq E X).
induction Hxy.
  destruct H as [z [Hxz Hzy]].
    inversion Hxz as [Hu | Hs].
    inversion Hu as [Hmhb | Hrf_sub].

     generalize (tc_dec Hzy); intros [z' [Hzz' Horz'y]].
     inversion Horz'y as [Hz'y | Heq].
      apply trc_ind with z'.

      apply trc_ind with z.
      apply (mhb_incl x z Hwk Hfb Hmrf Hrfi_or Hmhb).
        apply trc_step; right.
        generalize (excluded_middle (A1b.ppo E z z')); intro Hor.
        inversion Hor as [H1 | Hn1].
          left; right; auto.
          right; apply wfb_ppo_sub_in_ab1; unfold ppo_sub; unfold rel_sub; auto.

        rewrite <- (ghb1b_eq E X).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hz'y).
         
   subst; apply trc_ind with z.
      apply (mhb_incl x z Hwk Hfb Hmrf Hrfi_or Hmhb).

        rewrite <- (ghb1b_eq E X).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hzy).

     generalize (tc_dec Hzy); intros [z' [Hzz' Horz'y]].
     inversion Horz'y as [Hz'y | Heq].
      apply trc_ind with z'.

      destruct Hrf_sub as [e [Hws Hrf]].
      apply trc_ind with e.
      apply trc_step; left; left; auto.
        generalize (excluded_middle (mrf1 X e z)); intro Hor.
        inversion Hor as [H1 | Hn1].
          apply trc_ind with z.
          apply trc_step; right; left; left; auto.
        generalize (excluded_middle (A1b.ppo E z z')); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
        assert (rf_sub X e z) as Hrf_sub.
          unfold rf_sub; unfold rel_sub; split; auto.
          apply trc_ind with z; apply trc_step.
        assert (mrfi2 X e z) as Hmrfi.
          rewrite (same_rfe_implies_rf_sub_is_rfi_sub X Hwk Hwf) in Hrf_sub.
          destruct Hrf_sub; auto. apply Hmrf.
          
          inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].

          rewrite <- mrfi_eq in Hmrfi; assert False as Ht.
            apply Hn1; left; auto. inversion Ht.

        generalize (mrfi_in_ppo e z Hmrfi); intro Hppo2.
        generalize (excluded_middle (A1b.ppo E e z)); intro Horp.
        inversion Horp as [H1p | Hn1p].
           right; left; right; auto.
            right; right; apply Hfb; split; auto.

        generalize (excluded_middle (A1b.ppo E z z')); intro Horp.
        inversion Horp as [H1p | Hn1p].
            right; left; right; auto.
            right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.

        rewrite <- (ghb1b_eq E X).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hz'y).

  subst;
      destruct Hrf_sub as [e [Hws Hrf]].
      apply trc_ind with e.
      apply trc_step; left; left; auto.
        generalize (excluded_middle (mrf1 X e z)); intro Hor.
        inversion Hor as [H1 | Hn1].
          apply trc_ind with z.
          apply trc_step; right; left; left; auto.
        generalize (excluded_middle (A1b.ppo E z y)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
        assert (rf_sub X e z) as Hrf_sub.
          unfold rf_sub; unfold rel_sub; split; auto.
          apply trc_ind with z; apply trc_step.
        assert (mrfi2 X e z) as Hmrfi.
          rewrite (same_rfe_implies_rf_sub_is_rfi_sub X Hwk Hwf) in Hrf_sub.
          destruct Hrf_sub; auto. apply Hmrf.
          
          inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].

          rewrite <- mrfi_eq in Hmrfi; assert False as Ht.
            apply Hn1; left; auto. inversion Ht.

        generalize (mrfi_in_ppo e z Hmrfi); intro Hppo2.
        generalize (excluded_middle (A1b.ppo E e z)); intro Horp.
        inversion Horp as [H1p | Hn1p].
           right; left; right; auto.
            right; right; apply Hfb; split; auto.

        generalize (excluded_middle (A1b.ppo E z y)); intro Horp.
        inversion Horp as [H1p | Hn1p].
            right; left; right; auto.
            right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.

     generalize (tc_dec Hzy); intros [z' [Hzz' Horz'y]].
     inversion Horz'y as [Hz'y | Heq].
      apply trc_ind with z'.

    destruct Hs as [e [Hxe Hez]].
    apply trc_ind with e.
      apply trc_step; left; right; auto.
        generalize (excluded_middle (mrf1 X e z)); intro Hor.
        inversion Hor as [H1 | Hn1].
          apply trc_ind with z.
            apply trc_step; right; left; left; auto.
        generalize (excluded_middle (A1b.ppo E z z')); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
        assert (rf_sub X e z) as Hrf_sub.
          unfold rf_sub; unfold rel_sub; split; auto.
            rewrite (same_rfe_implies_rf_sub_is_rfi_sub X Hwk Hwf) in Hrf_sub.
          apply trc_ind with z.
          destruct Hrf_sub as [H2 ?].
        generalize (excluded_middle (A1b.ppo E e z)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb.
            split; auto. 

          inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].

          rewrite <- mrfi_eq in H2; assert False as Ht.
            apply H; auto. inversion Ht.

        apply (mrfi_in_ppo e z); auto. 
        generalize (excluded_middle (A1b.ppo E z z')); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
      apply Hmrf.

        rewrite <- (ghb1b_eq E X).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hz'y).  

 subst;    destruct Hs as [e [Hxe Hez]].
    apply trc_ind with e.
      apply trc_step; left; right; auto.
        generalize (excluded_middle (mrf1 X e z)); intro Hor.
        inversion Hor as [H1 | Hn1].
          apply trc_ind with z.
            apply trc_step; right; left; left; auto.
        generalize (excluded_middle (A1b.ppo E z y)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
        assert (rf_sub X e z) as Hrf_sub.
          unfold rf_sub; unfold rel_sub; split; auto.
            rewrite (same_rfe_implies_rf_sub_is_rfi_sub X Hwk Hwf) in Hrf_sub.
          apply trc_ind with z.
          destruct Hrf_sub as [H2 ?].
        generalize (excluded_middle (A1b.ppo E e z)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb.
            split; auto. 

          inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].

          rewrite <- mrfi_eq in H2; assert False as Ht.
            apply H; auto. inversion Ht.

        apply (mrfi_in_ppo e z); auto. 
        generalize (excluded_middle (A1b.ppo E z y)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
      apply Hmrf.

apply trc_ind with z; auto.
Qed.

Lemma wfb_seq_implies_ghb1 :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  tc (rel_seq (maybe (A2nWmm.mhb' E X)) (tc (A2n.ppo E))) x y ->
  tc (A1bWmm.ghb E X) x y.
Proof.
intros E X x y Hwk Hwf Hfb Hmrf Hrfi_or Hxy.
induction Hxy.
  destruct H as [e [Hor Hey]].
  inversion Hor.
    apply wfb_seq_implies_ghb1'; auto.
      apply trc_step; exists e; auto.
  subst; 
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hey).
apply trc_ind with z; auto.  
Qed.

Lemma wfb_ghb2_cycle_implies_ghb1_cycle :
  forall E X x,
  weaker ->
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  tc (A2nWmm.ghb E X) x x ->
  exists y, tc (A1bWmm.ghb E X) y y.
Proof.
intros E X x Hwk Hwf Hs Hfb Hmrf Hrfi_or Hx.
rewrite (ghb2_is_mhb_ppo2 E X) in Hx.
assert (exists y, tc (rel_seq (maybe (mhb' E X)) (tc (ppo E))) y y) as Hc.
eapply (mhb_union_ppo_cycle_implies_mhb'_seq_ppo_cycle2 X Hwf Hs Hx); auto; apply Hx.
destruct Hc as [y Hc].
exists y; eapply (wfb_seq_implies_ghb1 Hwk Hwf Hfb Hmrf Hrfi_or Hc).
Qed.

Lemma wfb_and_same_rfe_implies_valid :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  A1bWmm.valid_execution E X -> 
  A2nWmm.valid_execution E X.
Proof.
intros E X Hwk Hwf Hwfb Hmrf Hrfi_or Hv1.
  destruct_valid Hv1; split; auto; split; auto; split; auto.
  split.
    auto.
 unfold acyclic; unfold not; intros x Hx.  
  assert (exists x, tc (ghb E X) x x) as Hc.
    exists x; auto.
  assert (write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
    split; auto; split; auto.
  generalize (wfb_ghb2_cycle_implies_ghb1_cycle Hwk Hwf Hs Hwfb Hmrf Hrfi_or Hx); intros [y Hcy].
  apply (Hvalid y Hcy).
Qed.  

Inductive wAB (E:Event_struct) (X:Execution_witness) (fenced:Rln Event) : Event -> Event -> Prop :=
  | wBase : forall e1 e2, 
      fenced e1 e2 -> wAB E X fenced e1 e2.

Lemma wbarriers_placement : (*weaker barriers guarantee*)
  forall E X, 
  weaker -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  well_formed_event_structure E ->
  A1b.abc E X = wAB E X (ppo_sub E) ->
  A1bWmm.valid_execution E X -> 
  A2nWmm.valid_execution E X.
Proof.
intros E X Hwk Hmrf Hrfi_or Hwf Hab; apply wfb_and_same_rfe_implies_valid; auto;
unfold wfb; rewrite Hab.
intros x y Hxy.
  apply wBase; auto.
Qed.

End Barriers.

End Weaker.

End Hierarchy.
