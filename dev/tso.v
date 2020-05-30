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
Require Import Arith.
Require Import util.
Require Import wmm.
Require Import basic.
Require Import Bool.
Import OEEvt. 
Require Import hierarchy.
Set Implicit Arguments.

Module Tso.

(** * TSO execution *)

(** ** Definition *)

Definition LoadOp (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    In _ (reads E) e1 /\ (po_iico E) e1 e2.
Definition StoreStore (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    In _ (writes E) e1 /\ In _ (writes E) e2 /\ (po_iico E) e1 e2.

Lemma udr_ss : 
  forall E,
  Included _ (udr (StoreStore E)) (writes E).
Proof.
intro E; unfold udr; intros x Hx.
  inversion Hx.
    destruct H as [y [Hwx ?]]; auto.
    destruct H as [y [? [Hwx ?]]]; auto.
Qed.

Definition tso_exec (E:Event_struct) (Ex:Rln Event) : Prop := 
  partial_order Ex (events E) /\
  (exists tso, rel_incl tso Ex /\ linear_strict_order tso (writes E)) /\
  rel_incl (LoadOp E) Ex /\
  rel_incl (StoreStore E) Ex.

Ltac destruct_tso H :=
  destruct H as [Hpart [[tso [Hincl Hlin]] [Hlo Hss]]].

(** * Building a TSO witness *)

(** ** tso rfmaps *)

Set Implicit Arguments.
Definition maximal_elements (A:Set) (xs:set A) (r:Rln A) : set A :=
  fun x => In _ xs x /\ forall x', In _ xs x'/\ r x x' -> (x = x').
Unset Implicit Arguments.

Definition previous_writes (E:Event_struct) (r : Rln Event) (er:Event) :=
  fun ew => writes E ew /\ r ew er /\ loc ew = loc er.
Definition tso_rfm (E:Event_struct) (Ex : Rln Event) :=
  fun ew => fun er =>
    (rfmaps (events E)) ew er /\
    (maximal_elements 
       (previous_writes E (rel_union (LE Ex) (po_iico E)) er) Ex) ew.

Hypothesis tso_rfm_init :
  forall E Ex,
  forall er,
    exists ew, In _ (events E) ew /\ tso_rfm E Ex ew er.

(** ** tso ws *)

Definition tso_ws (Ex:Rln Event) : (Rln Event) :=
    fun e1 => fun e2 =>
    Ex e1 e2 /\
    exists l, In _ (writes_to_same_loc_l (udr Ex) l) e1 /\
      In _ (writes_to_same_loc_l (udr Ex) l) e2.

(** ** Definition of a TSO witness *)

Definition tso_witness (E:Event_struct) (Ex:Rln Event) : Execution_witness :=
  mkew (tso_ws Ex) (tso_rfm E Ex).

Definition hb_tso (E:Event_struct) (X:Execution_witness) : Rln Event :=
  rel_union (rel_union (ws X) (fr E X)) (rf_inter X).
Definition po_tso (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 => (po_iico E) e1 e2 /\
    (reads E e1 \/ (writes E e1 /\ writes E e2)).
Definition tso_check (E:Event_struct) (X:Execution_witness) : Prop :=
  acyclic (rel_union (po_tso E) (hb_tso E X)). 

Module AiTso <: Archi.
Parameter ppo : Event_struct -> Rln Event.
Hypothesis ppo_tso_compat : 
  forall E, rel_incl (ppo E) (po_tso E).
Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
  intro E; eapply rel_incl_trans.
  apply ppo_tso_compat.
  intros x y Hxy; destruct Hxy; auto.
Qed.
Parameter inter : bool.
Definition intra := false.
Parameter abc  : Event_struct -> Execution_witness -> Rln Event.
Hypothesis ab_tso_compat :
  forall E X, rel_incl (abc E X) (rel_seq (maybe (rf_inter X)) (rel_seq (po_tso E) (maybe (rf_inter X)))).
Hypothesis ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Parameter lockc : Event_struct -> Execution_witness -> Location -> Rln Event.
Definition lock E X := fun e1 => fun e2 => exists l, lockc E X l e1 e2.
Parameter stars : Event_struct -> Execution_witness -> set Event.
Parameter Cs : Type.
Parameter cs : Event_struct -> Execution_witness -> Location -> Cs -> Prop.
Parameter evts : Cs -> set Event.
End AiTso.

Import AiTso.
Module TsoAx (A:Archi).
Definition bimpl (b1 b2:bool) : Prop:=
  if (negb b1) || b2 then True else False.
Definition rf_impl (rf1 rf2 : bool) :=
  bimpl rf1 rf2.
Definition ppo_incl (ppo1 ppo2 : Event_struct -> Rln Event) :=
  forall E, rel_incl (ppo1 E) (ppo2 E).
Definition ab_incl (ab1 ab2 : Event_struct -> Execution_witness -> Rln Event) :=
  forall E X, rel_incl (ab1 E X) (ab2 E X).
Hypothesis AwkAiTso : 
  ppo_incl (A.ppo) (AiTso.ppo) /\
  bimpl (A.intra) (AiTso.intra) /\
  bimpl (A.inter) (AiTso.inter) /\
  ab_incl (A.abc) (AiTso.abc).
Module ABasic := Basic A.
Import ABasic.
Module AWmm := Wmm A.
Import AWmm.
Import A.

Section tso_valid.

(** * A TSO witness is a valid one *)

Lemma tso_ws_dom_ran_wf :
  forall E Ex l,
  tso_exec E Ex ->
  Included _ 
  (Union _
    (dom (rrestrict (tso_ws Ex) (writes_to_same_loc_l (events E) l)))
    (ran (rrestrict (tso_ws Ex) (writes_to_same_loc_l (events E) l)))) (* = *)
  (writes_to_same_loc_l (events E) l).
Proof.
intros E Ex l Htso.
unfold Included; intros x Hx.
inversion Hx as [e Hd | e Hr].
  unfold dom in Hd; unfold In in Hd; unfold rrestrict in Hd.
  destruct Hd as [y [Hso [Hmx Hmy]]]; apply Hmx.
  unfold ran in Hr; unfold In in Hr; unfold rrestrict in Hr.
  destruct Hr as [y [Hso [Hmy Hmx]]]; apply Hmx.
Qed.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

Lemma ex_w_implies_tso :
  forall E Ex tso x1 x2,
    partial_order Ex (events E) ->
    Ex x1 x2 /\
    (exists l : Location,
       In _ (writes_to_same_loc_l (udr Ex) l) x1 /\
       In _ (writes_to_same_loc_l (udr Ex) l) x2) ->
   rel_incl tso Ex ->
   linear_strict_order tso (writes E) ->
   tso x1 x2.
Proof.
intros E Ex tso x1 x2 Hp [H12 [l [H1 H2]]] Hincl Hlin.
destruct Hp as [Hudr [Ht Ha]];
destruct_lin Hlin; destruct (eqEv_dec x1 x2) as [Heq | Hdiff].
subst; generalize (Ha x2); intro Hc; contradiction.
destruct H1 as [H1 Hww1]; 
generalize (Hudr x1 H1); intro Hevt1;
generalize (write_to_implies_writes E Hevt1 Hww1); intro Hw1;
destruct H2 as [H2 Hww2]; 
generalize (Hudr x2 H2); intro Hevt2;
generalize (write_to_implies_writes E Hevt2 Hww2); intro Hw2.
generalize (Htot x1 x2 Hdiff Hw1 Hw2); intro Hor.
inversion Hor; auto.
generalize (Hincl x2 x1 H); intro Hex21.
assert (Ex x1 x2 /\ Ex x2 x1) as Hand.
  split; auto.
generalize (Ht x1 x2 x1 Hand); intro Hc; 
  generalize (Ha x1 Hc); intro Hco; contradiction.
Qed.

Lemma tso_ws_wf :
  forall E Ex,
  tso_exec E Ex ->
  write_serialization_well_formed (events E) (tso_ws Ex).
Proof.
intros E Ex Htso; split.
(*lin*)
intro l;split.
  (*dom/ran*)
  eapply (tso_ws_dom_ran_wf). apply Htso.
  destruct_tso Htso; split.
  (*trans*)
  intros x1 x2 x3 H123; destruct H123 as [H12 H23].
  unfold In in * |- * ; unfold rrestrict in * |- * ;
  destruct H12 as [Htso_ws12 [H1 H2]]; destruct H23 as [Htso_ws23 [H2' H3]];
  split; [| split; [exact H1 | exact H3]].
  unfold In in * |- *; unfold tso_ws in * |- *.
  assert (tso x1 x2) as Htso12.
    eapply ex_w_implies_tso; [apply Hpart | apply Htso_ws12 | auto | apply Hlin].
  assert (tso x2 x3) as Htso23.
    eapply ex_w_implies_tso; [apply Hpart | apply Htso_ws23 | auto | apply Hlin].
  destruct Htso_ws12 as [HEx12 Hl12]; destruct Htso_ws23 as [HEx23 Hl23]; split.
  destruct Hpart as [? [Htrans ?]]; apply Htrans with x2; auto.
      exists l; split.
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_left_in; exists x2; auto.
    destruct H1 as [Hevt1 Hw1]; apply Hw1.
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_right_in; exists x2; auto.
    destruct H3 as [Hevt3 Hw3]; apply Hw3.
  split.
  (*ac*)
  generalize Hlin; intro Hli.
  destruct_lin Hlin.
  unfold not; intros x Hx; destruct Hx as [[Htso_ws Hl] Hrest]; unfold not in Hac; 
  apply (Hac x).
  apply ex_w_implies_tso with E Ex; auto.
  (*tot*)
  intros x1 x2 Hdiff H1 H2.
  assert (In _ (writes E) x1) as Hevt1.
    destruct H1 as [He1 Hw1]; unfold udr in He1.
    apply (write_to_implies_writes E He1 Hw1); auto.
   assert (In _ (writes E) x2) as Hevt2.
    destruct H2 as [He2 Hrest]; unfold udr in He2.
    apply (write_to_implies_writes E He2 Hrest); auto.
  destruct_lin Hlin.
  generalize (Htot x1 x2 Hdiff Hevt1 Hevt2); intro Ht.
  inversion Ht as [H12 | H21]; unfold rrestrict; unfold tso_ws; unfold In; 
  [left | right]; split.
  split; [apply Hincl; auto | exists l; split].
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_left_in; exists x2; apply Hincl; auto.
    destruct H1 as [He1 Hw1]; apply Hw1.
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_right_in; exists x1; apply Hincl; auto.
    destruct H2 as [He2 Hw2]; apply Hw2.
  unfold In in H1; unfold In in H2; split; [apply H1 | apply H2].
  split; [ apply Hincl; auto | exists l; split].
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_left_in; exists x1; apply Hincl; auto.
    destruct H2 as [He2 Hw2]; apply Hw2.
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_right_in; exists x2; apply Hincl; auto.
    destruct H1 as [He1 Hw1]; apply Hw1.
  unfold In in H1; unfold In in H2; split; [apply H2 | apply H1].
(*mem*)
intros x e Hws.
destruct_tso Htso.
destruct Hws as [Hso [l [[Hex Hwx] [Hee Hwe]]]]; exists l; split;
  unfold In; unfold writes_to_same_loc_l.
  destruct Hpart as [Hdr ?].
  inversion Hex;
    [ split; [apply Hdr; apply incl_union_left_in; auto |apply Hwx] |
      split; [apply Hdr; apply incl_union_right_in; auto |apply Hwx]].
  destruct Hpart as [Hdr ?].
  inversion Hee;
  [ split; [apply Hdr; apply incl_union_left_in; apply H0 |apply Hwe] |
      split; [apply Hdr; apply incl_union_right_in; apply H0 |apply Hwe]].
Qed.

Lemma tso_rfm_fx :
  forall E Ex,
  ~(exists x, tso_rfm E Ex x x).
Proof.
intros E Ex [x [Hrf Hmax]].
destruct Hrf as [? [? [l [Hw Hr]]]].
assert (write_to x l /\ read_from x l) as Hand.
  split; auto.
apply (read_write_contrad Hand).
Qed.
Lemma ls_fx :
  forall E,
  ~(exists x, ls E x x).
Proof.
intros E [x Hx].
destruct Hx as [[Hexr [lr [vr Hr]]] [[Hexw [lw [vw Hw]]] ?]].
rewrite Hw in Hr; inversion Hr.
Qed.
Lemma tso_rfm_ls_fx :
  forall E Ex,
  ~(exists x, (rel_union (tso_rfm E Ex) (ls E)) x x).
Proof.
intros E Ex [x Hor].
inversion Hor.
  apply (tso_rfm_fx E Ex); exists x; auto.
  apply (ls_fx E); exists x; auto.
Qed.

Lemma ls_trans :
  forall E, trans (ls E).
Proof.
unfold trans;
intros E x y z [? [Hw ?]] [Hr ?].
destruct Hr as [Hexr [lr [vr Hr]]]; 
destruct Hw as [Hexw [lw [vw Hw]]].
rewrite Hw in Hr; inversion Hr.
Qed.

Lemma tso_rfm_trans :
  forall E Ex, trans (tso_rfm E Ex).
Proof.
unfold trans;
intros E Ex x y z [[? [? [lr [? Hr]]]] ?] [[? [? [lw [? Hw]]]] ?]. 
assert (write_to y lw /\ read_from y lr) as Hand.
  split; auto.
generalize (read_write_contrad Hand); intro Hc. contradiction.
Qed.

Lemma ls_seq_tso_rfm_implies_ex_path :
  forall E Ex x y,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  tc (rel_seq (ls E) (tso_rfm E Ex)) x y ->
  LE Ex x y.
Proof.
intros E Ex x y Hwf Htso Hin.
destruct_tso Htso.
    assert (Included _ (events E) (events E)) as Ht.
      unfold Included; trivial.
    generalize (OE Ht Hpart); intros [Hinc Hle].
    destruct_lin Hle.
induction Hin.
  destruct H as [z [Hxz Hzy]].
  destruct Hzy as [Hrf [Hpw Hmax]].
  destruct Hpw as [Hwz [Hu Hl]].
  destruct Hxz as [Hrx [Hwz' Hpo]]; inversion Hu as [Hex | Hpo_zy].

  apply (Htrans x z y); split; auto.
   apply Hinc; apply Hlo; split; auto.
    
    assert (LoadOp E x y) as Hlo_xy.
      split; auto.
        eapply po_trans; [apply Hwf | apply Hpo | auto].
        apply Hinc; apply Hlo; auto.
  apply (Htrans x z y); split; auto.  
Qed.

Lemma tso_caus_wf :
  forall E Ex, 
  well_formed_event_structure E ->
  tso_exec E Ex ->
  acyclic (rel_union (tso_rfm E Ex) (ls E)).
Proof.
intros E Ex Hwf Htso; generalize Htso; intro Ht.
destruct_tso Htso; generalize Hpart; intro Hp;
destruct Hpart as [Hudr [Htr Hacy]].
unfold acyclic; unfold not; intros x Hx.
generalize (tso_rfm_fx E Ex); intro Hfx1.
generalize (ls_fx E); intro Hfx2.
generalize (tso_rfm_ls_fx E Ex); intro Hfxu.
generalize (tso_rfm_trans E Ex); intro Ht1.
generalize (ls_trans E); intro Ht2.
generalize (union_cycle_implies_seq_cycle2 Hfx1 Hfx2 Hfxu Ht2 Ht1 Hx); intros [y Hpa].
generalize (ls_seq_tso_rfm_implies_ex_path E Ex y y Hwf Ht Hpa); intro Hc.
assert (Included _ (events E) (events E)) as Htriv.
  unfold Included; trivial.
generalize (OE Htriv Hp); intros [Hin Hle].
destruct_lin Hle.
generalize (Hac y); intro Hcon.
contradiction.
Qed. 

Lemma tso_tot :
  forall E Ex tso x y,
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex -> 
  writes E x -> writes E y ->
  (tso x y \/ tso y x) \/ x = y.
Proof.
intros E Ex tso x y Hpo Hincl Hlin Hlo Hss Hwx Hwy.
destruct (eqEv_dec x y) as [Heq | Hdiff].
right; auto.
destruct_lin Hlin.
left; apply (Htot x y Hdiff Hwx Hwy).
Qed.

Lemma tso_rfm_uni :
  forall E Ex,
  tso_exec E Ex ->
    forall w1 w2 r,
      tso_rfm E Ex w1 r ->
      tso_rfm E Ex w2 r ->
      w1 = w2.
Proof.
intros E Ex Htso w1 w2 r H1 H2.
destruct_tso Htso.
destruct H1 as [Hrf1 [Hpw1 Hm1]];
destruct H2 as [Hrf2 [Hpw2 Hm2]].
destruct (eqEv_dec w1 w2) as [Heq | Hdiff]; auto.
assert (tso w1 w2 \/ tso w2 w1) as Hor.
  assert (writes E w1) as Hw1.
    destruct Hrf1 as [? [? [l [[v1 Hw1]]]]]; split.
    apply H.
    exists l; exists v1; auto.    
  assert (writes E w2) as Hw2.
    destruct Hrf2 as [? [? [l [[v2 Hw2]]]]]; split.
    apply H.
    exists l; exists v2; auto.    
  generalize (tso_tot E Ex tso w1 w2 Hpart Hincl Hlin Hlo Hss Hw1 Hw2); intro Hor.
  inversion Hor; auto.
  unfold not in Hdiff; generalize (Hdiff H); intro Ht; inversion Ht.

inversion Hor as [H12 | H21].
apply (Hm1 w2); split.
  destruct Hrf2 as [? [? [l [[v2 Hw2]]]]]; split.
  split.
   apply H.
    exists l; exists v2; auto.
  split;
    destruct Hpw2 as [? [Hu Hl]]; auto.
  apply Hincl; auto.

apply sym_eq; apply (Hm2 w1); split.
  destruct Hrf1 as [? [? [l [[v1 Hw1]]]]]; split.
  split.
  apply H.
    exists l; exists v1; auto.
  split;
    destruct Hpw1 as [? [Hu Hl]]; auto.
  apply Hincl; auto.
Qed.

Lemma tso_rf_wf :
  forall E Ex,
  well_formed_event_structure E ->
  rel_incl (ls E) (po_iico E) ->
  tso_exec E Ex ->
  rfmaps_well_formed E (events E) (tso_rfm E Ex).
Proof.
intros E Ex Hwf Hdp Htso; unfold rfmaps_well_formed; split.
  apply tso_rfm_init; auto.
  split;
  [intros e1 e2 H12 | ].
destruct H12 as [Hso12 [Hrf12 Hno12]].
destruct_tso Htso.
unfold rfmaps.
destruct Hso12 as [Hevt1 [Hevt2 Hl]].
destruct Hpart as [Hdr ?];
split; [ | split; [|apply Hl]].
apply Hevt1.
apply Hevt2.
intros x w1 w2 [Htso_w1x [Hrf_w1x Hno_w1x]] [Htso_w2x [Hrf_w2x Hno_w2x]].
destruct (eqEv_dec w1 w2) as [Hy | Hn].
    apply Hy.
    destruct_tso Htso.
    destruct_lin Hlin.
    destruct Hpart as [Hudr [Ht Ha]].
    assert (writes E w1) as Hw1.
      destruct Htso_w1x as [Hew1 [Hex [l [Hw1 Hrx]]]].
      apply (write_to_implies_writes E Hew1 Hw1); auto.
    assert (writes E w2) as Hw2.
      destruct Htso_w2x as [Hew2 [Hex [l [Hw2 Hrx]]]].
      apply (write_to_implies_writes E Hew2 Hw2); auto.
    generalize (Htot w1 w2 Hn Hw1 Hw2); intro Hor.
    inversion Hor as [H12 | H21].
      apply (Hno_w1x w2); split; auto.
      apply sym_eq; apply (Hno_w2x w1); split; auto.
Qed. 

Lemma hb'_seq_pio_irrefl :
  forall E Ex x,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  ~((rel_seq (hb' E (tso_witness E Ex)) (pio E)) x x).
Proof.
unfold not;
intros E Ex x Hwf Htso [y [Hxy Hyx]].
destruct_tso Htso.
assert (Included _ (events E) (events E)) as Htriv.
  unfold Included; trivial.
generalize (OE Htriv Hpart); intros [Hin Hle].
inversion Hxy as [Hu | Hfrrf].
      inversion Hu as [Hhb | Hwsrf].
        inversion Hhb as [Hun | Hws].
          inversion Hun as [Hrf | Hfr].
            (*rf;pio*)
            destruct Hyx as [? Hpo_yx].
            destruct Hrf as [Hrf [[Hwx [Hor Hloc]] Hmax]]. 
            inversion Hor as [Hex_xy | Hpo_xy].
                  generalize Hpart; intro Hp.
                  destruct Hpart as [Hudr [Htr Hacy]].
              assert (Ex y x) as Hex_yx.
                apply Hlo; split; auto.
                  destruct Hrf as [Hex [Hey [l [Hx Hy]]]].
                  unfold In; eapply (read_from_implies_reads E); 
                    [apply Hey | apply Hy].
              destruct_lin Hle.
                  unfold not in Hac; apply (Hac x).  
                  apply Htrans with y; auto. 
              generalize (po_trans Hwf Hpo_xy Hpo_yx); intro Hc.
              apply (po_ac Hwf Hc).
            (*fr;pio*)
            destruct Hyx as [? Hpo_yx].
            destruct Hfr as [Hex [Hey [wx [Hrf Hws]]]].
            destruct Hrf as [Hrf [[Hwx [Hor Hloc]] Hmax]]. 
            destruct (eqEv_dec wx y) as [Heq | Hdiff].
              destruct Hws as [HEx ?]; subst.
              destruct Hpart as [Hudr [Htrans Hac]]; unfold not in Hac;
              apply (Hac y HEx).
              destruct_lin Hlin.
                assert (writes E y) as Hwy.
              destruct Hws as  [? [l [? Hwy]]].
              destruct Hwy; eapply (write_to_implies_writes E); auto.
                  apply H3.
                generalize (Htot wx y Hdiff Hwx Hwy); intro Horwxy.
                inversion Horwxy as [Hwxy | Hywx].
                assert (In _ (previous_writes E (rel_union (LE Ex) (po_iico E)) x) y /\ Ex wx y) as Hpwy.
                  split; [split; [auto | split; [right; auto |]] | apply Hincl; auto].
                    rewrite <- Hloc.
              destruct Hws as  [? [l [Hmwx Hmy]]].
              destruct Hmwx; destruct Hmy.
              rewrite (write_to_implies_this_loc H2);
              rewrite (write_to_implies_this_loc H4); trivial.
                generalize (Hmax y Hpwy); intro Heq; contradiction.
              destruct Hws as [Hex_wxy ?].
              destruct Hpart as [? [Ht Hacy]];
              apply (Hacy y); apply Ht with wx; split; auto.
            (*ws;pio*)
            destruct Hyx as [? Hpo_yx].
            destruct Hws as [Hex_xy ?].
              destruct Hpart as [Hudr [Ht Hacy]];
            assert (Ex y x) as Hex_yx. 
              destruct H0 as [l [Hmx Hmy]];
              apply Hss; split; [|split; auto].  
                destruct Hmy; unfold In; eapply (write_to_implies_writes E); auto.
                apply Hudr; auto. apply H1.
                destruct Hmx; unfold In; eapply (write_to_implies_writes E); auto.
                apply Hudr; auto. apply H1.
              apply (Hacy y); apply Ht with x; split; auto.
    (*ws;rf;pio*)
    destruct Hyx as [? Hpo_yx].
    destruct Hwsrf as [z [Hws Hrf]].
    destruct Hrf as [Hrf [[Hwx [Hor Hloc]] Hmax]].
    destruct Hpart as [Hudr [Ht Hacy]];
    inversion Hor as [Hex_zy | Hpo_zy].
      assert (Ex y z) as Hex_yz.
        apply Ht with x; split.
        apply Hlo; split; [| auto].
          destruct Hrf as [Hez [Hey [l [Hwz Hry]]]].
          unfold In; eapply (read_from_implies_reads E); auto.
          auto. apply Hry.
          destruct Hws; auto.
       generalize (Hin y z Hex_yz); intro Hlex_yz.
        destruct_lin Hle.
        apply (Hac y); apply Htrans with z; auto.
      assert (Ex z x) as Hex_zx.
        apply Hss; split; [auto | split; auto].
          destruct Hws as [Hex_zx [l [Hwwx Hwz]]].
          destruct Hwwx.
          unfold In; eapply (write_to_implies_writes E); auto.
          apply Hudr; apply incl_union_left_in; exists z; auto.
          apply H1.
          apply po_trans with y; auto.
      destruct Hws;
      apply (Hacy z); apply Ht with x; auto.
    (*fr;rf;pio*)
    destruct Hpart as [Hudr [Ht Hacy]];
    destruct Hyx as [? Hpo].
    destruct Hfrrf as [z [Hfr Hrf_zy]].
    destruct Hfr as [Hex [Hez [wx [Hrf_wxx Hws_wxz]]]].
    destruct Hrf_zy as [Hrf_zy [[Hwy [Hor_zy Hloc_zy]] Hmax_zy]].
    destruct Hrf_wxx as [Hrf_x [[Hwx [Hor_wxx Hloc_wxx]] Hmax_wxx]].
    inversion Hor_zy as [Hex_zy | Hpo_zy].
      assert (In _ (previous_writes E (rel_union (LE Ex) (po_iico E)) x) z /\ Ex wx z) as Hpwwx.
        destruct Hws_wxz; split; [split; [|split] | auto].
        auto.
        destruct_lin Hle.
        left; apply Htrans with y; split; auto.
        apply Hin; apply Hlo; split; auto.
          destruct Hrf_zy as [Heez [Hey [l [Hwz Hry]]]].
          unfold In; eapply (read_from_implies_reads E); auto.
          auto.  apply Hry.
          (*Hloc_zy then loc y = loc x since in pio cf. Hyx*)
          rewrite Hloc_zy; auto.
        generalize (Hmax_wxx z Hpwwx); intro Heq.
        destruct Hws_wxz as [Hex_wxz ?]; subst.
        apply (Hacy z); auto.
      generalize (po_trans Hwf Hpo_zy Hpo); intro Hpo_zx.
      assert (In _ (previous_writes E (rel_union (LE Ex) (po_iico E)) x) z /\ Ex wx z) as Hpwwx.
        destruct Hws_wxz; split; [split; [|split] | auto].
        auto.
        right; auto.
          (*Hloc_zy then loc y = loc x since in pio cf. Hyx*)
          rewrite Hloc_zy; auto.
        generalize (Hmax_wxx z Hpwwx); intro Heq.
        destruct Hws_wxz as [Hex_wxz ?]; subst.
        apply (Hacy z); auto.
Qed.

Lemma ws_tso :
  forall E Ex tso x y,
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex -> 
  ws (tso_witness E Ex) x y -> 
  tso x y.
Proof.
intros E Ex tso x y Hpo Hincl Hlin Hlo Hss [Hex [l [Hwx Hwy]]].
destruct_lin Hlin; destruct Hpo as [Hudr [Ht Hacy]].
destruct (eqEv_dec x y) as [Heq | Hdiff].
  subst; generalize (Hacy y); intro Hc; contradiction.
  assert (writes E x) as Hwwx.
  destruct Hwx as [Hevtx [v Hx]]; split; auto.
  exists l; exists v; auto.
  assert (writes E y) as Hwwy.
  destruct Hwy as [Hevty [v Hy]]; split; auto.
  exists l; exists v; auto.
generalize (Htot x y Hdiff Hwwx Hwwy); intro Hor.
inversion Hor as [Hxy | Hyx]; auto.
generalize (Hincl y x Hyx); intro Hex_yx.
assert (Ex x y /\ Ex y x) as Hand.
  split; auto.
generalize (Ht x y x Hand); intro Hxx.
generalize (Hacy x); intro Hc; contradiction.
Qed.

Lemma rf_init_right_tso :
  forall E Ex tso x y,
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex -> 
  writes E x -> reads E y ->  
  exists wy : Event, rf (tso_witness E Ex) wy y /\ 
  ((tso x wy \/ tso wy x) \/ x = wy).
Proof.
intros E Ex tso x y Hpo Hincl Hlin Hlo Hss Hwx Hry.
generalize (tso_rfm_init E Ex y); intros [wy [Hevt Hrf]].
destruct (eqEv_dec x wy) as [Heq | Hdiff].
exists x; subst; split.
  unfold tso_witness; simpl; auto.
  right; trivial.
exists wy; split.
  unfold tso_witness; simpl; auto.
left; destruct_lin Hlin; apply Htot; auto.
destruct Hrf as [[? [? [l [[v Hwwy] ?]]]] ?].
split; auto.
exists l; exists v; auto.
Qed.

Lemma rf_init_left_tso :
  forall E Ex tso x y,
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex -> 
  reads E x -> writes E y ->  
  exists wx : Event, rf (tso_witness E Ex) wx x /\ 
  ((tso wx y \/ tso y wx) \/ wx = y).
Proof.
intros E Ex tso x y Hpo Hincl Hlin Hlo Hss Hrx Hwy.
generalize (tso_rfm_init E Ex x); intros [wx [Hevt Hrf]].
destruct (eqEv_dec y wx) as [Heq | Hdiff].
exists y; subst; split.
  unfold tso_witness; simpl; auto.
  right; trivial.
exists wx; split.
  unfold tso_witness; simpl; auto.
left; destruct_lin Hlin; apply Htot; auto.
destruct Hrf as [[? [? [l [[v Hwwy] ?]]]] ?].
split; auto.
exists l; exists v; auto.
Qed.

Lemma rf_init_both_tso :
  forall E Ex tso x y,
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex -> 
  reads E x -> reads E y ->  
  exists wx, exists wy, 
    rf (tso_witness E Ex) wx x /\ 
    rf (tso_witness E Ex) wy y /\ 
    ((tso wx wy \/ tso wy wx) \/ wx = wy).
Proof.
intros E Ex tso x y Hpo Hincl Hlin Hlo Hss Hrx Hry.
generalize (tso_rfm_init E Ex x); intros [wx [Hevtx Hrfx]].
generalize (tso_rfm_init E Ex y); intros [wy [Hevty Hrfy]].
exists wx; exists wy; split; [|split]; auto.
destruct (eqEv_dec wy wx) as [Heq | Hdiff].
right; auto.
left; destruct_lin Hlin; apply Htot; auto.
destruct Hrfx as [[? [? [lx [[vx Hwwx] ?]]]] ?].
split; auto.
exists lx; exists vx; auto.
destruct Hrfy as [[? [? [ly [[vy Hwwy] ?]]]] ?].
split; auto.
exists ly; exists vy; auto.
Qed.

Lemma rf_wr_contrad :
  forall E Ex x y z e,
  (y = z \/ x = e) ->
  ~(rf (tso_witness E Ex) x y /\ rf (tso_witness E Ex) z e).
Proof.
intros E Ex x y z e Hor [Hxy Hze].
inversion Hor; subst.
  destruct Hxy as [[? [? [? [? [? Hrz]]]]] ?].
  destruct Hze as [[? [? [? [[? Hwz] ?]]]] ?].
  rewrite Hwz in Hrz; inversion Hrz.
  destruct Hxy as [[? [? [? [[? Hwe] ?]]]] ?].
  destruct Hze as [[? [? [? [? [? Hre]]]]] ?].
  rewrite Hwe in Hre; inversion Hre.
Qed.

Lemma rf_tso_wr_contrad :
  forall E Ex tso x y z e,
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  (y = z \/ y = e) ->
  ~(rf (tso_witness E Ex) x y /\ (tso z e \/ tso e z)).
Proof.
intros E Ex tso x y z e Hpo Hincl Hlin Hor [Hxy Hez].
destruct_lin Hlin.
inversion Hor; inversion Hez; subst.
  destruct Hxy as [[? [? [? [? [? Hrz]]]]] ?].
  assert (writes E z) as Hwz.
    apply Hdr; apply incl_union_left_in; exists e; auto.
  destruct Hwz as [Hevz [l [v Hwz]]].
  rewrite Hwz in Hrz; inversion Hrz.

  destruct Hxy as [[? [? [? [? [? Hrz]]]]] ?].
  assert (writes E z) as Hwz.
    apply Hdr; apply incl_union_right_in; exists e; auto.
  destruct Hwz as [Hevz [l [v Hwz]]].
  rewrite Hwz in Hrz; inversion Hrz.

  destruct Hxy as [[? [? [? [? [? Hre]]]]] ?].
  assert (writes E e) as Hwe.
    apply Hdr; apply incl_union_right_in; exists z; auto.
  destruct Hwe as [Heve [l [v Hwe]]].
  rewrite Hwe in Hre; inversion Hre.

  destruct Hxy as [[? [? [? [? [? Hre]]]]] ?].
  assert (writes E e) as Hwe.
    apply Hdr; apply incl_union_left_in; exists z; auto.
  destruct Hwe as [Heve [l [v Hwe]]].
  rewrite Hwe in Hre; inversion Hre.
Qed.

Definition hat E (rf:Rln Event) x y :=
  exists w, rf w x /\ rf w y /\ po_iico E x y.

Lemma pio_implies_or :
  forall E Ex tso x y,
  well_formed_event_structure E ->
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex ->    
  (pio E) x y ->
  (rf (tso_witness E Ex) x y \/
   (tso x y) \/ 
   (exists wx, rf (tso_witness E Ex) wx x /\ (tso wx y)) \/
   (exists wy, rf (tso_witness E Ex) wy y /\ (tso x wy)) \/
   (exists wx, exists wy, 
      rf (tso_witness E Ex) wx x /\ 
      rf (tso_witness E Ex) wy y /\ 
      (tso wx wy)) \/ 
   hat E (rf (tso_witness E Ex)) x y).
Proof.
intros E Ex tso x y Hwf Hpart Hincl Hlin Hlo Hss Hpo.
assert (tso_exec E Ex) as Htso.
  split; [|split; [exists tso|]]; auto.
case_eq (action y); case_eq (action x).
  intros dx lx vx Hx dy ly vy Hy; case_eq dy; case_eq dx; intros Hdy Hdx.
  (*R R*)
  generalize (tso_rfm_init E Ex x); intros [wx [Hewx Hrfx]];
  generalize (tso_rfm_init E Ex y); intros [wy [Hewy Hrfy]].
  destruct (eqEv_dec wx wy) as [Heq | Hdiff].

    right; right; right; right; right; unfold hat; exists wx; split; [|split]; auto.
    rewrite Heq; unfold tso_witness; simpl; auto. destruct Hpo; auto.

    right; right; right; right; left; exists wx; exists wy; split; [|split]; auto.
    assert (writes E wx) as Hwwx.
      split; auto; destruct Hrfx as [[? [? [lxx [[vxx Hwxx] ?]]]] ?];
      exists lxx; exists vxx; auto.
    assert (writes E wy) as Hwwy.
      split; auto; destruct Hrfy as [[? [? [lyy [[vyy Hwyy] ?]]]] ?];
      exists lyy; exists vyy; auto.
    generalize (tso_tot E Ex tso wx wy Hpart Hincl Hlin Hlo Hss Hwwx Hwwy); intro Hor.
    inversion Hor as [Htso_or | Heq].
    inversion Htso_or as [Hxy | Hyx]; auto.
    destruct Hrfy as [? [? Hmax]].
    assert (In _ (previous_writes E (rel_union (LE Ex) (po_iico E)) y) wx /\
       Ex wy wx) as Hc.
      split; [split |]; auto; split.
      destruct Hrfx as [Hrfx [Hpw ?]].
      destruct Hpw as [? [Horin ?]].
      inversion Horin as [Hex | Hpowxx].
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
      generalize (OE Htriv Hpart); intros [Hin Hle].
      destruct_lin Hle. left; eapply Htrans; split.
        apply Hex. apply Hin; apply Hlo; split; destruct Hpo; auto.
        destruct Hrfx as [? [? [l [? [v Hrx]]]]]; split; auto.
        exists l; exists v; auto.
      right; eapply po_trans; auto.
        apply Hpowxx. destruct Hpo; auto.
      destruct Hpo as [Hl ?]; rewrite <- Hl.
      destruct Hrfx as [Hrfx [Hpw ?]].
        destruct Hrfx as [? [? [l [[v1 Hwx] [v2 Hrx]]]]]; unfold loc;
        rewrite Hwx; rewrite Hrx; auto.
    generalize (Hmax wx Hc); intro Heq.

    destruct_lin Hlin; generalize (Hac wx); intro Hcy.
    rewrite Heq in Hyx; contradiction.

    unfold not in Hdiff; generalize (Hdiff Heq); intro Ht; inversion Ht.

  (*W R*)
  generalize (tso_rfm_init E Ex y); intros [wy [Hewy Hrfy]].
  destruct (eqEv_dec x wy) as [Heq | Hdiff].

    left; rewrite Heq; auto.

    right; right; right; left; exists wy; split; auto.
    assert (writes E x) as Hwx.
      split.
      eapply po_iico_domain_in_events; auto; destruct Hpo as [? Hpo]; apply Hpo. 
      exists lx; exists vx; subst; auto.
    assert (writes E wy) as Hwwy.
      split; auto; destruct Hrfy as [[? [? [lyy [[vyy Hwyy] ?]]]] ?];
      exists lyy; exists vyy; auto.
    generalize (tso_tot E Ex tso x wy Hpart Hincl Hlin Hlo Hss Hwx Hwwy); intro Hor.
    inversion Hor as [Htso_or | Heq].
    inversion Htso_or as [Hxy | Hyx]; auto.
    destruct Hrfy as [? [? Hmax]].
    assert (In _ (previous_writes E (rel_union (LE Ex) (po_iico E)) y) x /\
       Ex wy x) as Hc.
      split; [split |]; auto; split.
      right; destruct Hpo; auto.
      destruct Hpo; auto.
    generalize (Hmax x Hc); intro Heq.

    destruct_lin Hlin; generalize (Hac x); intro Hcy.
    rewrite Heq in Hyx; contradiction.

    unfold not in Hdiff; generalize (Hdiff Heq); intro Ht; inversion Ht.
  
  (*R W*)
  generalize (tso_rfm_init E Ex x); intros [wx [Hewx Hrfx]].
  destruct (eqEv_dec wx y) as [Heq | Hdiff].

    generalize (hb'_seq_pio_irrefl E Ex y Hwf Htso); intro Hnc.
    assert (rel_seq (hb' E (tso_witness E Ex)) (pio E) y y) as Hc.
      exists x; split; auto.
        left; left; left; left; simpl; rewrite Heq in Hrfx; auto.
    contradiction.

    right; right; left; exists wx; split; auto.
    assert (writes E wx) as Hwwx.
      split; auto; destruct Hrfx as [[? [? [lxx [[vxx Hwxx] ?]]]] ?];
      exists lxx; exists vxx; auto.
    assert (writes E y) as Hwy.
      split.
      eapply po_iico_range_in_events; auto; destruct Hpo as [? Hpo]; apply Hpo.
      exists ly; exists vy; subst; auto.
    generalize (tso_tot E Ex tso wx y Hpart Hincl Hlin Hlo Hss Hwwx Hwy); intro Hor.
    inversion Hor as [Hor_tso | Heq].
    inversion Hor_tso as [Hxy | Hyx]; auto.
    
    assert (LE Ex wx y) as Hex.
        generalize Hpart; intro Hp.
        destruct Hpart as [? [Ht Hacy]].
        destruct Hrfx as [? [Hpw ?]].
        destruct Hpw as [? [Horin ?]].
        inversion Horin as [Hex | Hpoin].
        assert (LE Ex wx x /\ LE Ex x y) as Hand.
          split; auto.
          assert (Included _ (events E) (events E)) as Htriv.
            unfold Included; trivial.
          generalize (OE Htriv Hp); intros [Hin Hle].
          apply Hin; apply Hlo; split; auto.
          split.
            eapply (po_iico_domain_in_events); destruct Hpo as [? Hpo]; auto; apply Hpo.
             exists lx; exists vx; subst; auto.

          destruct Hpo; auto.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
          generalize (OE Htriv Hp); intros [Hin Hle].
        destruct_lin Hle.
        apply (Htrans wx x y Hand).

        assert (po_iico E wx y) as Hpowxy.
          eapply po_trans; auto. apply Hpoin.
          destruct Hpo; auto.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
          generalize (OE Htriv Hp); intros [Hin Hle].
          apply Hin; apply Hss; split; auto.

      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
          generalize (OE Htriv Hpart); intros [Hin Hle].
       assert (LE Ex wx wx) as Hc.
        assert (LE Ex wx y /\ LE Ex y wx) as Hand.
          split; auto. 
          apply Hin; apply Hincl; auto.

      destruct_lin Hle.
      generalize (Htrans wx y wx Hand); intro Hc.
      generalize (Hac wx); intro Hcy. contradiction.
      destruct_lin Hle.
      generalize (Hac wx); intro Hcy. contradiction.
    unfold not in Hdiff; generalize (Hdiff Heq); intro Ht; inversion Ht.

  (*W W*)
    right; left.
    assert (writes E x) as Hwx.
      split.
      eapply po_iico_domain_in_events; auto; destruct Hpo as [? Hpo]; apply Hpo.
      exists lx; exists vx; subst; auto.
    assert (writes E y) as Hwy.
      split.
      eapply po_iico_range_in_events; auto; destruct Hpo as [? Hpo]; apply Hpo.
      exists ly; exists vy; subst; auto.
    generalize (tso_tot E Ex tso x y Hpart Hincl Hlin Hlo Hss Hwx Hwy); intro Hor.
    inversion Hor as [Htso_or | Heq].
    inversion Htso_or as [Hxy | Hyx]; auto.
    assert (Ex x y /\ Ex y x) as Hex.
      split; [apply Hss; split; auto | apply Hincl; auto].
      split; destruct Hpo; auto.
    destruct Hpart as [? [Ht Hac]].
    generalize (Ht x y x Hex); intro Hc.
    generalize (Hac x); intro Hcy; contradiction. 
    destruct Hpo as [? Hpo].
    rewrite Heq in Hpo; generalize (po_ac Hwf Hpo); intro Ht; inversion Ht.
Qed. 

Lemma rf_left_implies_write :
  forall E Ex x y,
  partial_order Ex (events E) ->
  rf (tso_witness E Ex) x y ->
  writes E x.
Proof.
intros E Ex x y [Hdr ?] [[Hin [? [l [[v Hwx] ?]]]] ?].
  split; [apply Hin | exists l; exists v; auto].
Qed.

Lemma rf_right_implies_read :
  forall E Ex x y,
  partial_order Ex (events E) ->
  rf (tso_witness E Ex) x y ->
  reads E y.
Proof.
intros E Ex x y [Hdr ?] [[? [Hin [l [? [v Hwx]]]]] ?].
  split; [apply Hin | exists l; exists v; auto].
Qed.

Lemma hat_left_implies_read :
  forall E Ex x y,
  partial_order Ex (events E) ->
  hat E (rf (tso_witness E Ex)) x y ->
  reads E x.
Proof.
intros E Ex x y [Hdr ?] [? [[[? [? [l [? [v Hrx]]]]] ?] ?]].
  split; [apply H1 | exists l; exists v; auto].
Qed.

Lemma hat_right_implies_read :
  forall E Ex x y,
  partial_order Ex (events E) ->
  hat E (rf (tso_witness E Ex)) x y ->
  reads E y.
Proof.
intros E Ex x y [Hdr ?] [? [? [Hrf ?]]].
destruct Hrf as [[? [? [l [? [v Hry]]]]] [? ?]].
  split; [apply H3 | exists l; exists v; auto].
Qed.

Lemma tso_left_implies_write :
  forall E Ex tso x y,
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  tso x y ->
  writes E x.
Proof.
intros E Ex tso x y Hincl [Hdr ?] Hxy.
  apply Hdr; apply incl_union_left_in; exists y; auto.
Qed.

Lemma tso_right_implies_write :
  forall E Ex tso x y,
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  tso x y ->
  writes E y.
Proof.
intros E Ex tso x y Hincl [Hdr ?] Hxy.
  apply Hdr; apply incl_union_right_in; exists x; auto.
Qed.

Lemma tso_rfm_hat_contrad :
  forall E Ex x y z e,
  partial_order Ex (events E) ->
  (x = z \/ x = e) ->
  ~(rf (tso_witness E Ex) x y /\ hat E (rf (tso_witness E Ex)) z e).
Proof.
intros E Ex x y z e Hpart Hor [Hrf Hhat].
generalize (rf_left_implies_write E Ex x y Hpart Hrf); intros [? [l [v Hwx]]].
inversion Hor as [Hxz | Hxe].
  generalize (hat_left_implies_read E Ex z e Hpart Hhat); intros [? [le [ve Hre]]].
  rewrite Hxz in Hwx; rewrite Hwx in Hre; inversion Hre.
  generalize (hat_right_implies_read E Ex z e Hpart Hhat); intros [? [le [ve Hre]]].
  rewrite Hxe in Hwx; rewrite Hwx in Hre; inversion Hre.  
Qed.

Lemma tso_hat_contrad :
  forall E Ex tso x y z e,
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex -> 
  ((x = z \/ x = e) \/ (y = z \/ y = e)) ->
  ~(tso x y /\ hat E (rf (tso_witness E Ex)) z e).
Proof.
intros E Ex tso x y z e Hpart Hincl Hlin Hlo Hss Horb [Htso Hhat].
inversion Horb as [Horl | Hord].

  generalize (tso_left_implies_write E Ex tso x y Hincl Hlin Htso); intros [? [lx [vx Hwx]]].
  inversion Horl as [Hxz | Hxe].
    generalize (hat_left_implies_read E Ex z e Hpart Hhat); intros [? [le [ve Hre]]].
    rewrite Hxz in Hwx; rewrite Hwx in Hre; inversion Hre.
    generalize (hat_right_implies_read E Ex z e Hpart Hhat); intros [? [le [ve Hre]]].
    rewrite Hxe in Hwx; rewrite Hwx in Hre; inversion Hre.

  generalize (tso_right_implies_write E Ex tso x y Hincl Hlin Htso); intros [? [lx [vx Hwx]]].
  inversion Hord as [Hxz | Hxe].
    generalize (hat_left_implies_read E Ex z e Hpart Hhat); intros [? [le [ve Hre]]].
    rewrite Hxz in Hwx; rewrite Hwx in Hre; inversion Hre.
    generalize (hat_right_implies_read E Ex z e Hpart Hhat); intros [? [le [ve Hre]]].
    rewrite Hxe in Hwx; rewrite Hwx in Hre; inversion Hre.
Qed.

Lemma tso_trans :
  forall E Ex tso x z y,
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex ->
  tso x z -> tso z y -> tso x y.
Proof.
intros E Ex tso x z y Hpart Hincl Hlin Hlo Hss Hxz Hzy.
destruct_lin Hlin; apply (Htrans x z y); auto.
Qed.

Lemma hat_trans :
  forall E Ex x z y,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  hat E (rf (tso_witness E Ex)) x z ->
  hat E (rf (tso_witness E Ex)) z y ->
  hat E (rf (tso_witness E Ex)) x y.
Proof.
intros E Ex x z y Hwf Htso [wx [Hrfx [Hrf1 Hpoxz]]] [wy [Hrf2 [Hrfy Hpozy]]];
exists wx; split; [| split]; auto.
generalize (tso_rfm_uni E Ex Htso wx wy z Hrf1 Hrf2); intro Heq.
subst; auto.
apply po_trans with z; auto.
Qed.

Lemma hb_pio_path_implies_tso_path :
  forall E Ex tso x y,
  well_formed_event_structure E ->
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex ->    
  tc (rel_union (hb E (tso_witness E Ex)) (pio E)) x y ->
  (rf (tso_witness E Ex) x y \/
   ((tso x y)) \/ 
   (exists wx, rf (tso_witness E Ex) wx x /\ ((tso wx y ))) \/
   (exists wy, rf (tso_witness E Ex) wy y /\ ((tso x wy ))) \/
   (exists wx, exists wy, 
      rf (tso_witness E Ex) wx x /\ 
      rf (tso_witness E Ex) wy y /\ 
       ((tso wx wy ))) \/ 
   hat E (rf (tso_witness E Ex)) x y).
Proof.
intros E Ex tso x y Hwf Hpart Hincl Hlin Hlo Hss Hxy.
assert (tso_exec E Ex) as Htsoex.
  split; auto.
  split; [exists tso; split; auto | split; auto].
induction Hxy.
  inversion H as [Hhb | Hpo].

    inversion Hhb as [Hrf_fr | Hws].
      inversion Hrf_fr as [Hrf | Hfr].
        left; auto.
        destruct Hfr as [Hex [Hey [wx [Hrf_x Hws]]]].
        right; right; left; exists wx; split; auto.
          apply (ws_tso E Ex tso wx y); auto.
          right; left; apply (ws_tso E Ex tso x y); auto.
    
    apply pio_implies_or; auto.

    inversion IHHxy1 as [Hrf1 | Hr1]; inversion IHHxy2 as [Hrf2 | Hr2].
    
    (*Hrf1 Hrf2*)
      assert (z=z \/ x=y) as Ht.
        left; trivial.
      generalize (rf_wr_contrad E Ex x z z y Ht); intro Hc.
      assert (rf (tso_witness E Ex) x z /\ rf (tso_witness E Ex) z y) as Hand.
        split; auto.
      contradiction.
    (*Hrf1 Hr2*)
      inversion Hr2 as [Htso2 | Hre2].
      assert (z=z \/ z=y) as Ht.
        left; trivial.
      generalize (rf_tso_wr_contrad E Ex tso x z z y Hpart Hincl Hlin Ht); intro Hc.
      assert (rf (tso_witness E Ex) x z /\ (tso z y \/ tso y z)) as Hand.
        split; auto.
      contradiction.
        inversion Hre2 as [Hrf2 | Hres2].

          right; left. 
          destruct Hrf2 as  [wx [Hrf Htso]].
          generalize (tso_rfm_uni E Ex Htsoex x wx z Hrf1 Hrf); intro Heq.
          rewrite Heq; auto.

          inversion Hres2 as [Hrf2 | Hrest2].
            right; right; right; left.

            destruct Hrf2 as [wy [Hrfy Htsoz]].
              assert (z = z \/ z = wy) as Ht.
                left; trivial.
              generalize (rf_tso_wr_contrad E Ex tso x z z wy Hpart Hincl Hlin Ht); 
              intro Hc. assert (rf (tso_witness E Ex) x z /\ (tso z wy \/ tso wy z)) as Hco.
                split; auto. contradiction.

              inversion Hrest2 as [Hrf2 | Hhat2].
                destruct Hrf2 as [w [wy [Hrf [Hrfy Htsoy]]]].
                destruct (eqEv_dec x wy) as [Heq | Hdiff].
                left; subst; auto.
                right; right; right; left.
                generalize (tso_rfm_uni E Ex Htsoex x w z Hrf1 Hrf); intro Heq.
                exists wy; subst; split; auto.
                left; unfold hat in Hhat2.
                destruct Hhat2 as [w [Hrf [Hrfy Hpo]]].
                generalize (tso_rfm_uni E Ex Htsoex x w z Hrf1 Hrf); intro Heq; subst; auto.

    (*Hr1 Hrf2*)
      inversion Hr1 as [Htso1 | Hre1].
        right; right; right; left; exists z; split; auto.
        inversion Hre1 as [Hrf1 | Hres1].
          right; right; right; right; left.
            destruct Hrf1 as [wx [Hrfx Htsox]]; exists wx; exists z; split; [|split]; auto; split; auto.

          inversion Hres1 as [Hrf1 | Hrest1].
      destruct Hrf1 as [wy [Hrfy Htsowy]].
      assert (z=z \/ wy=y) as Ht.
        left; trivial.
      generalize (rf_wr_contrad E Ex wy z z y Ht); intro Hc.
      assert (rf (tso_witness E Ex) wy z /\ rf (tso_witness E Ex) z y) as Hand.
        split; auto.
      contradiction.
            inversion Hrest1 as [Hrf1 | Hhat1].
      destruct Hrf1 as [wx [wy [Hrfx [Hrfy Htsowy]]]].
      assert (z=z \/ wy=y) as Ht.
        left; trivial.
      generalize (rf_wr_contrad E Ex wy z z y Ht); intro Hc.
      assert (rf (tso_witness E Ex) wy z /\ rf (tso_witness E Ex) z y) as Hand.
        split; auto.
      contradiction. 
    
      assert (z = x \/ z = z) as Ht.
        right; auto.
      generalize (tso_rfm_hat_contrad E Ex z y x z Hpart Ht); intro Hc.
      assert (rf (tso_witness E Ex) z y /\ hat E (rf (tso_witness E Ex)) x z) as Hco.
        split; auto. contradiction.

    (*Hr1 Hr2*)
    inversion Hr1 as [Htso1 | Hre1]; inversion Hr2 as [Htso2 | Hre2].
      (*Htso1 Htso2*)
      right; left; apply (tso_trans E Ex tso x z y); auto.

      (*Htso1 Hre2*)
      inversion Hre2 as [Hrf2 | Hres2].
        destruct Hrf2 as [wx [Hrfx Htsox]].
      assert (z = x \/ z=z) as Ht.
        right; trivial.
      generalize (rf_tso_wr_contrad E Ex tso wx z x z Hpart Hincl Hlin Ht); intro Hc.
      assert (rf (tso_witness E Ex) wx z /\ (tso x z \/ tso z x)) as Hand.
        split; auto.
      contradiction.

        inversion Hres2 as [Hrf2 | Hrest2].
          destruct Hrf2 as [wy [Hrfy Htsowy]]; 
          destruct (eqEv_dec x wy) as [Heq | Hdiff].
          left; subst; auto.
          right; right; right; left.
             exists wy; split; auto.
            apply (tso_trans E Ex tso x z wy); auto.
          inversion Hrest2 as [Hrf2 | Hhat2].

            destruct Hrf2 as [w [wy [Hrf [Hrfy Htsoy]]]].
            assert (z = x \/ z = z) as Ht.
              right; trivial.
            generalize (rf_tso_wr_contrad E Ex tso w z x z Hpart Hincl Hlin Ht);
              intro Hc. assert (rf (tso_witness E Ex) w z /\ (tso x z \/ tso z x)) as Hco.
                split; auto. contradiction.

            assert ((x = z \/ x = y) \/ z = z \/ z = y ) as Ht.
              right; left; trivial.
            generalize (tso_hat_contrad E Ex tso x z z y Hpart Hincl Hlin Hlo Hss Ht); intro Hc.
            assert (tso x z /\ hat E (rf (tso_witness E Ex)) z y) as Hco.
              split; auto. contradiction.

      (*Hre1 Htso2*)
      inversion Hre1 as [Hrf1 | Hres1].
        right; right; left.
          destruct Hrf1 as [wx [Hrfx Htsox]]; exists wx; split; auto.
          apply (tso_trans E Ex tso wx z y); auto.
        inversion Hres1 as [Hrf1 | Hrest1].

          destruct Hrf1 as [wy [Hrfy Htsoy]].
          assert (z = z \/ z = y) as Ht.
            left; trivial.
          generalize (rf_tso_wr_contrad E Ex tso wy z z y Hpart Hincl Hlin Ht); intro Hc.
          assert (rf (tso_witness E Ex) wy z /\ (tso z y \/ tso y z)) as Hco.
            split; auto. contradiction.

          inversion Hrest1 as [Hrf1 | Hhat1].

            destruct Hrf1 as [wx [w [Hrfx [Hrf Htsoy]]]].
            assert (z = z \/ z = y) as Ht.
              left; trivial.
            generalize (rf_tso_wr_contrad E Ex tso w z z y Hpart Hincl Hlin Ht); intro Hc.
            assert (rf (tso_witness E Ex) w z /\ (tso z y \/ tso y z)) as Hco.
              split; auto. contradiction.

            assert ((z=x \/ z=z)\/ y = x \/ y = z) as Ht.
              left; right; auto.
            generalize (tso_hat_contrad E Ex tso z y x z Hpart Hincl Hlin Hlo Hss Ht); intro Hc.
            assert (tso z y /\ hat E (rf (tso_witness E Ex)) x z) as Hco.
              split; auto. contradiction.

    (*Hre1 Hre2*)
    inversion Hre1 as [Hrf1 | Hres1]; inversion Hre2 as [Hrf2 | Hres2].
      (*Hrf1 Hrf2*)
      destruct Hrf1 as [wx [Hrfx Htsox]]; destruct Hrf2 as [w [Hrf Htso]].
      assert (z = wx \/ z = z) as Ht.
        right; trivial.
      generalize (rf_tso_wr_contrad E Ex tso w z wx z Hpart Hincl Hlin Ht); intro Hc.
      assert (rf (tso_witness E Ex) w z /\ (tso wx z \/ tso z wx)) as Hco.
        split; auto. contradiction.

      inversion Hres2 as [Hrf2 | Hrest2].
        destruct Hrf1 as [wx [Hrfx Htsox]]; destruct Hrf2 as [wy [Hrfy Htsoy]].
        destruct (eqEv_dec wx wy) as [Heq | Hdiff].
        right; right; right; right; right; exists wx; split; subst; [|split]; auto.
          generalize (tso_trans E Ex tso z wy z Hpart Hincl Hlin Hlo Hss Htsoy Htsox); intro Hc.
          destruct_lin Hlin; generalize (Hac z); intro Hcy; contradiction.
        right; right; right; right; left; exists wx; exists wy; split; [|split]; auto.
        apply (tso_trans E Ex tso wx z wy); auto.
        
        inversion Hrest2 as [Hrf2 | Hhat2].

          destruct Hrf1 as [wx [Hrfx Htsox]];
          destruct Hrf2 as [w [wy [Hrf [Hrfy Htsoy]]]].
          assert (z = wx \/ z = z) as Ht.
            right; auto.
          generalize (rf_tso_wr_contrad E Ex tso w z wx z Hpart Hincl Hlin Ht); intro Hc.
          assert (rf (tso_witness E Ex) w z /\ (tso wx z \/ tso z wx)) as Hco.
            split; auto. contradiction.

          destruct Hrf1 as [wx [Hrfx Htsox]].
          assert ((wx = z \/ wx = y) \/ z = z \/ z = y) as Ht.
            right; left; auto.
          generalize (tso_hat_contrad E Ex tso wx z z y Hpart Hincl Hlin Hlo Hss Ht); intro Hc.
          assert (tso wx z /\ hat E (rf (tso_witness E Ex)) z y) as Hco.
            split; auto. contradiction.
      
     (*Hres1 Hrf2*)
     inversion Hres1 as [Hrf1 | Hrest1].
       right; left. 
         destruct Hrf1 as [w1 [Hrf1 Htsox]];
         destruct Hrf2 as [w2 [Hrf2 Htsoy]].
         generalize (tso_rfm_uni E Ex Htsoex w1 w2 z Hrf1 Hrf2); intro Heq.
       rewrite Heq in Htsox.
       apply (tso_trans E Ex tso x w2 y); auto.
       inversion Hrest1 as [Hrf1 | Hhat1].
         destruct Hrf1 as [wx [w [Hrfx [Hrf Htsowx]]]]; destruct Hrf2 as [w' [Hrf' Htsoy]].
         right; right; left. 
         generalize (tso_rfm_uni E Ex Htsoex w' w z Hrf' Hrf); intro Heq.
         rewrite Heq in Htsoy.
         exists wx; split; auto.
         apply (tso_trans E Ex tso wx w y); auto.

        destruct Hrf2 as [wx [Hrf Htsoy]].
        right; right; left; exists wx; split; auto.
        destruct Hhat1 as [w [Hrfx [Hrfz Hpo]]].
        generalize (tso_rfm_uni E Ex Htsoex w wx z Hrfz Hrf); intro Heq.
        subst; auto.
     
    (*Hres1 Hres2*)
    inversion Hres1 as [Hrf1 | Hrest1]; inversion Hres2 as [Hrf2 | Hrest2].
      destruct Hrf1 as [w [Hrf Htsox]]; destruct Hrf2 as [wy [Hrfy Htsowy]].
        right; right; right; left; exists wy; split; auto.
       
        assert (z = z \/ z = wy) as Ht.
          left; auto.
        generalize (rf_tso_wr_contrad E Ex tso w z z wy Hpart Hincl Hlin Ht); intro Hc.
        assert (rf (tso_witness E Ex) w z /\ (tso z wy \/ tso wy z)) as Hco.
          split; auto. contradiction.

      inversion Hrest2 as [Hrf2 | Hhat2].
        destruct Hrf1 as [w [Hrf Htsox]]; destruct Hrf2 as [w' [wy [Hrf' [Hrfy Htsowy]]]].
        destruct (eqEv_dec x wy) as [Heq | Hdiff].
        left; subst; auto.
        right; right; right; left; exists wy; split; auto.
        generalize (tso_rfm_uni E Ex Htsoex w w' z Hrf Hrf'); intro Heq.
        rewrite <- Heq in Htsowy.
        apply (tso_trans E Ex tso x w wy); auto.
        destruct Hrf1 as [wy [Hrfy Htsox]].
        right; right; right; left; exists wy; split; auto.
        destruct Hhat2 as [w [Hrf [Hrfy' Hpo]]].
        generalize (tso_rfm_uni E Ex Htsoex w wy z Hrf Hrfy); intro Heq.
        subst; auto.

      inversion Hrest1 as [Hrf1 | Hhat1].
       
        destruct Hrf2 as [wy [Hrfy Htsoy]];
        destruct Hrf1 as [wx [w [Hrfx [Hrf Htsox]]]].
        assert (z = z \/ z = wy) as Ht.
          left; trivial.
        generalize (rf_tso_wr_contrad E Ex tso w z z wy Hpart Hincl Hlin Ht); intro Hc.
        assert (rf (tso_witness E Ex) w z /\ (tso z wy \/ tso wy z)) as Hco.
          split; auto. contradiction.

        destruct Hrf2 as [wy [Hrfy Htsoy]].
        assert ((z = x \/ z = z) \/ wy = x \/ wy = z) as Ht.
          left; right; auto.
        generalize (tso_hat_contrad E Ex tso z wy x z Hpart Hincl Hlin Hlo Hss Ht); intro Hc.
        assert (tso z wy /\ hat E (rf (tso_witness E Ex)) x z) as Hco.
          split; auto. contradiction.
 
    (*Hrest1 Hrest2*)
    inversion Hrest1 as [Hrf1 | Hhat1]; inversion Hrest2 as [Hrf2 | Hhat2].
      destruct Hrf1 as [wx [w1 [Hrfx [Hrf1 Htsowx]]]]; 
      destruct Hrf2 as [w2 [wy [Hrf2 [Hrfy Htsowy]]]].
      right; right; right; right; left; exists wx; exists wy; split; [|split]; auto.
      generalize (tso_rfm_uni E Ex Htsoex w1 w2 z Hrf1 Hrf2); intro Heq.
      rewrite <- Heq in Htsowy.
      apply (tso_trans E Ex tso wx w1 wy); auto.
 
      destruct Hrf1 as [wx [wy [Hrfx [Hrf Htsowx]]]];
      right; right; right; right; left; exists wx; exists wy; split; [|split]; auto.
      destruct Hhat2 as [w [Hrfz [Hrfy Hpo]]].
      generalize (tso_rfm_uni E Ex Htsoex wy w z Hrf Hrfz); intro Heq.
      subst; auto.

      destruct Hrf2 as [wx [wy [Hrf [Hrfy Htsowy]]]].
      right; right; right; right; left; exists wx; exists wy; split; [|split]; auto.
        destruct Hhat1 as [w [Hrfx [Hrfz Hpo]]].
        generalize (tso_rfm_uni E Ex Htsoex w wx z Hrfz Hrf); intro Heq.
        subst; auto.

     right; right; right; right; right.
     apply (hat_trans E Ex x z y); auto.
Qed.

Lemma rf_contrad : 
  forall E Ex x,
  tso_exec E Ex ->
  ~(rf (tso_witness E Ex) x x).
Proof.
intros E Ex x Htso Hx.
destruct Hx as [Hrf ?]; destruct Hrf as [? [? [l [[v1 Hw] [v2 Hr]]]]].
rewrite Hw in Hr; inversion Hr.
Qed.

Lemma tso_contrad :
  forall E Ex tso x,
  partial_order Ex (events E) ->
  rel_incl tso Ex ->
  linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex ->
  ~(tso x x).
Proof.
intros E Ex tso x Hpo Hincl Hlin Hlo Hss Hx.
destruct_lin Hlin; generalize (Hac x); intro Ht; contradiction.
Qed.
          
Lemma hat_irrefl :
  forall E Ex x,
  well_formed_event_structure E ->
  ~(hat E (rf (tso_witness E Ex)) x x).
Proof.
intros E Ex x Hwf Hx.
destruct Hx as [? [? [? Hpo]]].
apply (po_ac Hwf Hpo).
Qed.

Lemma tso_hb_wf :
  forall E Ex,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  (acyclic (rel_union (hb E (tso_witness E Ex))
     (pio E))).
Proof.
intros E Ex Hwf Htso.
unfold acyclic; unfold not; intros x Hx.
generalize Htso; intro Ht.
destruct_tso Htso.
generalize (hb_pio_path_implies_tso_path E Ex tso x x Hwf Hpart Hincl Hlin Hlo Hss Hx);
  intro Hor.
  inversion Hor. 
    generalize (rf_contrad E Ex x Ht); intro Hc; contradiction.
    inversion H.
      generalize (tso_contrad E Ex tso x Hpart Hincl Hlin Hlo Hss); intro Hc.
      contradiction.
      inversion H0.
        destruct H1 as [wx [Hrf Htso]].
        assert (rf (tso_witness E Ex) wx x /\ (tso wx x \/ tso x wx)) as Hand.
          split; auto.
        assert (x = wx \/ x = x) as Htr.
          right; trivial.
        apply (rf_tso_wr_contrad E Ex tso wx x wx x Hpart Hincl Hlin Htr Hand).
        inversion H1.
        destruct H2 as [wx [Hrf Htso]].
        assert (rf (tso_witness E Ex) wx x /\ (tso wx x \/ tso x wx)) as Hand.
          split; auto; inversion Htso; auto.
        assert (x = wx \/ x = x) as Htr.
          right; trivial.
        apply (rf_tso_wr_contrad E Ex tso wx x wx x Hpart Hincl Hlin Htr Hand).

         inversion H2.
          destruct H3 as [wx [wy [Hrfx [Hrfy Htso]]]].
            generalize (tso_rfm_uni E Ex Ht wx wy x Hrfx Hrfy); intro Heq.
            rewrite Heq in Htso; destruct_lin Hlin; generalize (Hac wy); 
            intro Hc; contradiction.

            generalize (hat_irrefl E Ex x Hwf); intro Hc; contradiction.
Qed. 

Lemma tso_ws_in_tso :
  forall E Ex,
  rel_incl (ws (tso_witness E Ex)) Ex.
Proof.
intros E Ex; unfold tso_witness; simpl; unfold tso_ws.
intros e1 e2 Hin; destruct Hin as [Hso Hrest]; exact Hso.
Qed.

Definition bot_ghb E X :=
(rel_union (abc E X) 
    (rel_union (rel_union (ws X) (fr E X)) (ppo E) )).
 
Lemma rf_po_rf_tso_in_hb_po_tso :
  forall E Ex x y,
  rel_seq (maybe (rf_inter (tso_witness E Ex)))
        (rel_seq (Tso.po_tso E) (maybe (rf_inter (tso_witness E Ex)))) x y ->
  tc (rel_union (hb E (tso_witness E Ex)) (po_tso E)) x y.
Proof.
intros E Ex x y [z [Hxz [e [Hze Hey]]]].
  inversion Hxz as [Hrfxz | Heqxz]; inversion Hey as [Hrfey | Heqey].
    apply trc_ind with z.
      apply trc_step; left; left; left; destruct Hrfxz; auto.
      apply trc_ind with e; apply trc_step.
        right; auto.
        left; left; left; destruct Hrfey; auto.
    rewrite <- Heqey.
    apply trc_ind with z; apply trc_step.
      left; left; left; destruct Hrfxz; auto.
        right; auto.
    rewrite Heqxz.
    apply trc_ind with e; apply trc_step.
        right; auto.
        left; left; left; destruct Hrfey; auto.
  rewrite <- Heqey; rewrite Heqxz.
  apply trc_step; right; auto.
Qed.

Lemma bot_ghb_path_implies_hb_po_path :
  forall E Ex tso x y,
  well_formed_event_structure E ->
  partial_order Ex (events E) ->
  rel_incl tso Ex /\ linear_strict_order tso (writes E) ->
  rel_incl (LoadOp E) Ex /\ rel_incl (StoreStore E) Ex ->    
  tc (bot_ghb E (tso_witness E Ex)) x y ->
  tc (rel_union (hb E (tso_witness E Ex)) (po_tso E)) x y.
Proof.
intros E Ex tso x y Hwf Hpart Htso Hloss Hxy.
induction Hxy.
  inversion H as [Hab | Hr].
   generalize AwkAiTso; intros [? [? [? Habe]]].
    generalize (Habe E (tso_witness E Ex) x y Hab); intro Hxy.
    generalize (ab_tso_compat E (tso_witness E Ex) x y Hxy); intro Hin.
    apply (rf_po_rf_tso_in_hb_po_tso E Ex x y Hin).
    inversion Hr as [Hws_fr | Hor].
      inversion Hws_fr as [Hws | Hfr].
        apply trc_step; left; right; auto.
        apply trc_step; left; left; right ; auto.
      apply trc_step; right; auto.
      apply ppo_tso_compat.  
      generalize AwkAiTso; intros [Hincl ?]; apply Hincl; auto.
  apply trc_ind with z; auto.
Qed.

Lemma po_tso_in_ex :
  forall E Ex,
  rel_incl (LoadOp E) Ex ->
  rel_incl (StoreStore E) Ex ->
  rel_incl (po_tso E) Ex.
Proof.
intros E Ex Hlo Hss x y Hxy.
destruct Hxy as [Hpo Hor]; inversion Hor.
  apply Hlo; split; auto.
  apply Hss; destruct H; split; auto.
Qed.

Lemma rf_ws_act_contrad :
  forall E Ex x y z e,
  tso_exec E Ex ->
  rf (tso_witness E Ex) x y -> 
  ws (tso_witness E Ex) z e -> 
  y <> e.
Proof.   
intros E Ex x y z e Htso Hrf Hws.
destruct (eqEv_dec y e) as [Heq | Hdiff]; auto.
destruct_tso Htso.
generalize (rf_right_implies_read E Ex x y Hpart Hrf); intros [? [ly [vy Hy]]].
destruct Hws as [? [l [? [? [ve He]]]]].
intro Heql; rewrite <- Heql in He; rewrite He in Hy; inversion Hy.
Qed.

Lemma rf_inter_in_ex :
  forall E Ex x y,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  rf_inter (tso_witness E Ex) x y ->
  LE Ex x y.
Proof.
intros E Ex x y Hwf Htso [Hrf Hproc].
  destruct Hrf as [? [Hpw ?]].
  destruct Hpw as [? [Hor ?]].
  inversion Hor; auto.
    generalize (diff_proc_implies_not_po Hwf Hproc H3); intro Ht.
    inversion Ht.
Qed.

Lemma rf_po_rf_tso_in_ex :
  forall E Ex x y,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  rel_seq (maybe (rf_inter (tso_witness E Ex)))
        (rel_seq (Tso.po_tso E) (maybe (rf_inter (tso_witness E Ex)))) x y ->
  LE Ex x y.
Proof.
intros E Ex x y Hwf Htso [z [Hxz [e [Hze Hey]]]].
  generalize Htso; intro Htsob.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
  destruct_tso Htsob; generalize (OE Htriv Hpart); intros [Hin Hle].
  destruct_lin Hle.
  inversion Hxz as [Hrfxz | Heqxz]; inversion Hey as [Hrfey | Heqey].
    apply (Htrans x z y); split; [|apply (Htrans z e y); split].
      apply (rf_inter_in_ex E Ex x z Hwf Htso Hrfxz).
      apply Hin; apply (po_tso_in_ex E Ex Hlo Hss z e Hze).
      apply (rf_inter_in_ex E Ex e y Hwf Htso Hrfey).
  rewrite <- Heqey; apply (Htrans x z e); split.
    apply (rf_inter_in_ex E Ex x z Hwf Htso Hrfxz).
    apply Hin; apply (po_tso_in_ex E Ex Hlo Hss z e Hze).
  rewrite Heqxz; apply (Htrans z e y); split.
    apply Hin; apply (po_tso_in_ex E Ex Hlo Hss z e Hze).
      apply (rf_inter_in_ex E Ex e y Hwf Htso Hrfey).
  rewrite Heqxz; rewrite <- Heqey.
    apply Hin; apply (po_tso_in_ex E Ex Hlo Hss z e Hze).    
Qed.

Lemma bot_ghb_in_ex :
  forall E Ex,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  rel_incl (bot_ghb E (tso_witness E Ex)) (LE Ex).
Proof.
intros E Ex Hwf Htso x y Hxy.
generalize Htso; intro Htsob.
inversion Hxy as [Hab | Hr].
   generalize AwkAiTso; intros [? [? [? Habe]]].
    generalize (Habe E (tso_witness E Ex) x y Hab); intro Habxy.
    generalize (ab_tso_compat E (tso_witness E Ex) x y Habxy); intro Hin.
      destruct_tso Htsob.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
      generalize (OE Htriv Hpart); intros [Hinc Hle]. 
    apply (rf_po_rf_tso_in_ex E Ex x y Hwf Htso Hin).
  inversion Hr as [Hws_fr | Hor].
      destruct_tso Htso.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
      generalize (OE Htriv Hpart); intros [Hin Hle]. 
    inversion Hws_fr as [Hws | Hfr].
      destruct Hws; apply Hin; auto.
      destruct Hfr as [? [? [z [Hrf Hws]]]].
      destruct_lin Hle.
        assert (x <> y) as Hdiff.
          apply (rf_ws_act_contrad E Ex z x z y); auto. 
        assert (events E x) as Hex.
          destruct Hrf as [[? [Hudr ?]] ?].
        auto.
        assert (events E y) as Hey.
          destruct Hws as [Hws ?].
          assert (In Event (Union Event (dom Ex) (ran Ex)) y) as Hy.
          apply incl_union_right_in; exists z; apply Hws.
          apply Hdr; apply (udr_r_in_udr_le Hin Hy).
    generalize (Htot x y Hdiff Hex Hey); intro Hor.
    inversion Hor; auto.
      destruct Hrf as [? [Hpw Hmax]].
      assert (In Event (previous_writes E (rel_union (LE Ex) (po_iico E)) x) y /\
       Ex z y) as Hc.
        split; [split |].
          destruct Hws as [Hws [l [? [? [v Hy]]]]].
          split.
          assert (In Event (Union Event (dom Ex) (ran Ex)) y) as Hudry.
          apply incl_union_right_in; exists z; apply Hws.
          apply Hdr; apply (udr_r_in_udr_le Hin Hudry).
          exists l; exists v; auto.
          split; [left; auto |].
 
          destruct Hws as [? [l [[? [vz Hz]] [? [vy Hy]]]]].
          destruct H2 as [? [? [lx [[v Hwz] [vx Hrx]]]]].
          rewrite Hwz in Hz; inversion Hz as [Hl ].
          unfold loc; rewrite Hy; rewrite Hrx; rewrite Hl; auto.

       destruct Hws; auto.
    generalize (Hmax y Hc); intro Heq.

    destruct Hws as [Hexzy ?].
    rewrite Heq in Hexzy.
    destruct Hpart as [? [Htr Hacy]].
    generalize (Hacy y); intro Hco.
    contradiction.
    destruct_tso Htso.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
    generalize (OE Htriv Hpart); intros [Hin Hle]; 
    generalize AwkAiTso; intros [Hppowk [? [? ?]]].
    apply Hin; generalize (Hppowk E x y Hor); intro Hppoi.
    generalize (ppo_tso_compat E x y Hppoi).
    apply po_tso_in_ex; auto.
Qed.

Lemma ghb_in_ex :
  forall E Ex,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  rel_incl (ghb E (tso_witness E Ex)) (LE Ex).
Proof.
intros E Ex Hwf Htso x y Hxy.
  unfold ghb in *; case_eq inter; case_eq intra; intros Hintra Hinter;
  rewrite Hinter in *; rewrite Hintra in *.
(*true true*) 
generalize AwkAiTso; intros [? [intra_hyp ?]].
unfold AiTso.intra in intra_hyp; rewrite Hintra in intra_hyp;
inversion intra_hyp.
(*false true*)
  inversion Hxy as [Hrf | Hbot].
    destruct Hrf as [[Hrf [[? [Hor ?]] Hmax]] Hproc].
    inversion Hor; auto.
      generalize (diff_proc_implies_not_po Hwf Hproc H1); intro Hc.
      inversion Hc.
  fold (bot_ghb E (tso_witness E Ex)) in Hbot;
  generalize Hbot; apply bot_ghb_in_ex; auto.
(*true false*)
generalize AwkAiTso; intros [? [intra_hyp ?]].
unfold AiTso.intra in intra_hyp; rewrite Hintra in intra_hyp;
inversion intra_hyp.
(*false false*)
  fold (bot_ghb E (tso_witness E Ex)) in Hxy; 
  generalize Hxy; apply bot_ghb_in_ex; auto.
Qed.

Lemma tso_exec_wf :
  forall E Ex,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  acyclic (ghb E (tso_witness E Ex)).
Proof.
intros E Ex Hwf Htso.
eapply incl_ac.
apply ghb_in_ex; auto.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
destruct_tso Htso; generalize (OE Htriv Hpart); intros [Hin Hle].
  generalize (lso_is_tc Hle); intro Heq.
unfold acyclic; rewrite Heq.
destruct_lin Hle; auto.
Qed.

Lemma tso_rfm_dp_in_ex :
  forall E Ex,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  rel_incl (tc (rel_seq (dp E) (tso_rfm E Ex))) (LE Ex).
Proof.
intros E Ex Hwf Htso x y Hxy.
generalize Htso; intro Htsob.
destruct_tso Htso.
induction Hxy.
  destruct H as [z [Hxz Hzy]].
  destruct (eqProc_dec (proc_of z) (proc_of y)) as [Heq | Hn].
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
        generalize (OE Htriv Hpart); intros [Hin Hle].
    apply Hin.
    apply Hlo; generalize (dp_valid E); intros [Hpo [? Hr]]; split.
    apply (Hr x z); auto.
    apply po_trans with z; auto.
    assert (In _ (events E) z) as Hez.
      destruct Hzy as [[? ?] ?]; auto.
    assert (In _ (events E) y) as Hey.
      destruct Hzy as [[? [? ?]] ?]; auto.
    generalize (same_proc_implies_po z y Hwf Heq Hez Hey);
      intro Hor; inversion Hor; auto.
    assert (tc (rel_union (hb E (tso_witness E Ex)) (pio E)) z z) as Hc.
      apply trc_ind with y; apply trc_step.
      left; left; left; unfold tso_witness; simpl; auto.
      right; split; auto.
        destruct Hzy as [[? [? [l [[vz Haz] [vy Hay]]]]] ?];
        unfold loc; rewrite Haz; rewrite Hay; auto.
      generalize (tso_hb_wf E Ex Hwf Htsob z Hc); intro Ht.
      inversion Ht.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
        generalize (OE Htriv Hpart); intros [Hin Hle].
  destruct_lin Hle.
    apply (Htrans x z y); split.
    apply Hin.
    apply Hlo; generalize (dp_valid E); intros [Hpo [? Hr]]; split.
      apply (Hr x z); auto.
      apply Hpo; auto.
  apply (rf_inter_in_ex E); auto.
  unfold tso_witness; unfold rf_inter; simpl; split; auto.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
        generalize (OE Htriv Hpart); intros [Hin Hle].
  destruct_lin Hle.
  apply (Htrans x z y); split; auto.
Qed.

Lemma tso_thin :
  forall E Ex,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  acyclic (rel_union (tso_rfm E Ex) (dp E)).
Proof.
intros E Ex Hwf Htso x Hx.
generalize Htso; intro Htsob.
destruct Htso as [Hp ?].
assert (~(exists x, tso_rfm E Ex x x)) as Hrfn.
  apply tso_rfm_fx.
assert (~(exists x, dp E x x)) as Hdpn.
  intros [e He].
  assert (po_iico E e e) as Hpoe.
    generalize (dp_valid E); intros [Hi ?]; apply (Hi e e He).
  generalize Hpoe; apply po_ac; auto. 
assert (~(exists x, (rel_union (tso_rfm E Ex) (dp E)) x x)) as Hun.
  intros [e He]; inversion He.
    assert (exists e, tso_rfm E Ex e e) as Hc.
      exists e; auto.
    contradiction.
    assert (exists e, dp E e e) as Hc.
      exists e; auto.
    contradiction.
assert (trans (dp E)) as Htdp.
  generalize (dp_valid E); intros [? [? ?]]; auto.
assert (trans (tso_rfm E Ex)) as Htrf.
  apply tso_rfm_trans.
generalize (union_cycle_implies_seq_cycle2 Hrfn Hdpn Hun Htdp Htrf Hx);
  intros [y Hy].
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
        generalize (OE Htriv Hp); intros [Hin Hle].
  destruct_lin Hle.
apply (Hac y).
apply (tso_rfm_dp_in_ex E Ex); auto.
Qed.

Lemma tso_witness_valid :
  forall E Ex, 
  well_formed_event_structure E ->
  tso_exec E Ex ->
  valid_execution E (tso_witness E Ex).
Proof.
intros E Ex Hwf Htso.
unfold valid_execution; unfold tso_witness; simpl.
 split;  [eapply tso_ws_wf; apply Htso | 
  split; [apply tso_rf_wf; [apply Hwf | | apply Htso ]  | 
    split;[ fold (tso_witness E Ex); apply tso_hb_wf; [apply Hwf | apply Htso] |]]].
unfold ls; intros x y [? [? Hxy]]; auto.
   split.
     apply tso_thin; auto.
   fold (tso_witness E Ex); 
   apply tso_exec_wf; auto.
Qed. 

(*A TSO witness tso checks *)

Definition top_tso_ghb E X : Rln Event :=
(rel_union (rf_inter X)
(rel_union (abc E X) 
    (rel_union (rel_union (ws X) (fr E X)) 
      (po_tso E)))).

Lemma po_tso_hb_tso_path_implies_ghb_path :
  forall E Ex x y,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  tc (rel_union (po_tso E) (hb_tso E (tso_witness E Ex))) x y ->
  tc (top_tso_ghb E (tso_witness E Ex)) x y.
Proof.
intros E Ex x y Hwf Htso Hxy.
induction Hxy; [| apply trc_ind with z; auto].
apply trc_step; unfold top_tso_ghb.
inversion H as [Hpo | Hr].
  right; right; right; auto.
  inversion Hr as [Hws_fr | Hrf].
    inversion Hws_fr as [Hws | Hfr].
      right; right; left; left; auto.
      right; right; left; right; auto.
  left; auto.
Qed.

Lemma tc_ghb_in_ex :
  forall E Ex x y,
  well_formed_event_structure E ->
  tso_exec E Ex ->
  tc (top_tso_ghb E (tso_witness E Ex)) x y ->
  LE Ex x y.
Proof.
intros E Ex x y Hwf Htso Hxy.
  generalize Htso; intro Htsob.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
  destruct_tso Htsob; generalize (OE Htriv Hpart); intros [Hin Hle].
induction Hxy.
  inversion H as [Hrf | Hbot].
    destruct Hrf as [[Hrf [[? [Hor ?]] Hmax]] Hproc].
    inversion Hor; auto.
      generalize (diff_proc_implies_not_po Hwf Hproc H2); intro Hc.
      inversion Hc.
  inversion Hbot as [Hab | Hr].
   generalize AwkAiTso; intros [? [? [? Habe]]].
    generalize (Habe E (tso_witness E Ex) x y Hab); intro Habxy.
    generalize (ab_tso_compat E (tso_witness E Ex) x y Habxy); intro Hinc.
    apply (rf_po_rf_tso_in_ex E Ex x y Hwf Htso Hinc).
    inversion Hr as [Hws_fr | Hpo_tso].
      inversion Hws_fr as [Hws | Hfr].
      destruct Hws; apply Hin; auto.
      destruct Hfr as [? [? [z [Hrf Hws]]]].
      destruct_lin Hle.
        assert (x <> y) as Hdiff.
          apply (rf_ws_act_contrad E Ex z x z y); auto.
        assert (events E x) as Hex.
          destruct Hrf as [[? [Hudr ?]] ?].
        auto.
        assert (events E y) as Hey.
          destruct Hws as [Hws ?].
          assert (In Event (Union Event (dom Ex) (ran Ex)) y) as Hudry.
          apply incl_union_right_in; exists z; apply Hws.
          apply Hdr; apply (udr_r_in_udr_le Hin Hudry).
    generalize (Htot x y Hdiff Hex Hey); intro Hor.
    inversion Hor; auto.
      destruct Hrf as [? [Hpw Hmax]].
      assert (In Event (previous_writes E (rel_union (LE Ex) (po_iico E)) x) y /\
       Ex z y) as Hc.
        split; [split |].
          destruct Hws as [Hws [l [? [? [v Hy]]]]].
          split.
          assert (In Event (Union Event (dom Ex) (ran Ex)) y) as Hudry.
          apply incl_union_right_in; exists z; apply Hws.
          apply Hdr; apply (udr_r_in_udr_le Hin Hudry). 
          exists l; exists v; auto.
          split; [left; auto |].
          destruct Hws as [? [l [[? [vz Hz]] [? [vy Hy]]]]].
          destruct H3 as [? [? [lx [[v Hwz] [vx Hrx]]]]].
          rewrite Hwz in Hz; inversion Hz as [Hl ].
          unfold loc; rewrite Hy; rewrite Hrx; rewrite Hl; auto.

       destruct Hws; auto.
    generalize (Hmax y Hc); intro Heq.
    destruct Hws as [Hexzy ?].
    rewrite Heq in Hexzy.
    destruct Hpart as [? [Htr Hacy]].
    generalize (Hacy y); intro Hco.
    contradiction.
   apply Hin; generalize Hpo_tso; generalize y; generalize x; apply po_tso_in_ex; auto.
  destruct_lin Hle.
  eapply Htrans; split; [apply IHHxy1 | apply IHHxy2].
Qed.

Lemma tso_witness_tso :
  forall E so,
  well_formed_event_structure E ->
  tso_exec E so ->
  tso_check E (tso_witness E so).
Proof.
intros E Ex Hwf Htso x Hxtso; unfold tso_check.
generalize (po_tso_hb_tso_path_implies_ghb_path E Ex x x Hwf Htso Hxtso); intro Hc.
generalize (tc_ghb_in_ex E Ex x x Hwf Htso Hc); intro Hcy.
      assert (Included _ (events E) (events E)) as Htriv.
        unfold Included; trivial.
  destruct_tso Htso; generalize (OE Htriv Hpart); intros [Hin Hle].
  destruct_lin Hle.
  generalize (Hac x); intro Hco; contradiction.
Qed.

End tso_valid.

Section obs.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].
  
Lemma po_tso_hb_in_po_hb :
  forall E X,
  Included _ (Union _ (dom (rel_union (po_tso E) (hb E X)))
           (ran (rel_union (po_tso E) (hb E X))))
    (Union _ (dom (rel_union (po_iico E) (hb E X)))
     (ran (rel_union (po_iico E) (hb E X)))).
Proof.
intros E X x Hx.
  inversion Hx as [e Hd | e Hr].
    destruct Hd as [y Hxy]; apply incl_union_left_in; exists y.
    inversion Hxy as [Hpo | Hhb].
      left; destruct Hpo; auto.
      right; auto.
    destruct Hr as [y Hxy]; apply incl_union_right_in; exists y.
    inversion Hxy as [Hpo | Hhb].
      left; destruct Hpo; auto.
      right; auto.
Qed.

Lemma po_tso_hb_tso_in_po_hb :
  forall E X,
  Included _ (Union _ (dom (rel_union (po_tso E) (hb_tso E X)))
           (ran (rel_union (po_tso E) (hb_tso E X))))
    (Union _ (dom (rel_union (po_iico E) (hb E X)))
     (ran (rel_union (po_iico E) (hb E X)))).
Proof.
intros E X x Hx.
  inversion Hx as [e Hd | e Hr].
    destruct Hd as [y Hxy]; apply incl_union_left_in; exists y.
    inversion Hxy as [Hpo | Hhb].
      left; destruct Hpo; auto.
      right; destruct Hhb as [Hws_fr | Hrfi].
        inversion Hws_fr as [Hws | Hfr].
          right; auto.
          left; right; auto.
          left; left; destruct Hrfi; auto.
    destruct Hr as [y Hxy]; apply incl_union_right_in; exists y.
    inversion Hxy as [Hpo | Hhb].
      left; destruct Hpo; auto.
      right; destruct Hhb as [Hws_fr | Hrfi].
        inversion Hws_fr as [Hws | Hfr].
          right; auto.
          left; right; auto.
          left; left; destruct Hrfi; auto.
Qed.

Lemma ac_tso_hb_implies_same_ws :
  forall E X so,
  well_formed_event_structure E ->
  valid_execution E X ->
  acyclic (rel_union (po_tso E) (hb_tso E X))->
  linear_strict_order so (events E) ->
  rel_incl (rel_union (po_tso E) (hb_tso E X)) so ->
  ws X = ws (tso_witness E so).
Proof.
intros E X so Hwf Hvalid Hacy Hlin Hincl.
generalize Hvalid; intro Hv.
assert (forall x y, (ws X) x y <-> (ws (tso_witness E so)) x y) as Hext.
  split; intro Hin;
unfold tso_witness; unfold tso_ws; simpl.
  split; [|destruct_valid Hvalid].
  apply Hincl; right; unfold hb; 
  left; left; apply Hin.
  destruct_lin Hlin.
    assert (write_serialization_well_formed (events E) (ws X)) as Hwswf.
      split; auto.
    generalize (ws_cands E X x y Hwswf Hin).
    intros [l [Hx Hy]]; exists l; split.
  split; destruct Hx as [Hudr Hwx]; auto.
  unfold udr; apply incl_union_left_in; exists y; apply Hincl.
    right; left; left; auto.

  split; destruct Hy as [Hudr Hwy]; auto.
  unfold udr; apply incl_union_right_in; exists x; apply Hincl.
    right; left; left; auto.

  unfold tso_witness in Hin; simpl in Hin.
  destruct_valid Hvalid.
  unfold tso_ws in Hin;
  unfold udr in Hin.
  destruct Hin as [Hin [l Hm]];
 assert (In _ (writes_to_same_loc_l (events E) l) x /\
    In _ (writes_to_same_loc_l (events E) l) y) as Hmem.
  split; split; destruct Hm as [[Hx Hwx] [Hy Hwy]].
  destruct_lin Hlin.
  apply Hdr; auto.
  auto.
  destruct_lin Hlin.
  apply Hdr; auto.
  auto.
  generalize (ws_tot E X (Hws_tot l) Hmem); intro Hor.
  assert (x <> y) as Hneq.
  destruct_lin Hlin.
    unfold not; intro Heq_xe; unfold acyclic in Hac; unfold not in Hac; apply (Hac x).
    rewrite <- Heq_xe in Hin; exact Hin.
  generalize (Hor Hneq); intro Horb.
  inversion Horb as [Hws_xe | Hws_ex].
    exact Hws_xe.
    assert (so y x) as Hin_ex.
      apply Hincl; unfold hb;
        right; left; left; exact Hws_ex.
    assert (~(acyclic so)) as Hcontrad.
      unfold acyclic; unfold not; intro Hcy; apply (Hcy x).
      eapply trc_ind with y; apply trc_step; [apply Hin | exact Hin_ex].
  generalize Hlin; intro Hli; destruct_lin Hlin; unfold acyclic in Hcontrad.
  generalize (lso_is_tc Hli); intro Heq; rewrite Heq in Hcontrad.
    contradiction.
apply (ext_rel (ws X) (ws (tso_witness E so)) Hext).
Qed.

End obs.

Section tso_carac.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

Lemma tso_rfm_in_rf :
  forall E X so x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  linear_strict_order so (events E) ->
  rel_incl (rel_union (po_tso E) (hb_tso E X)) so ->
  tso_rfm E so x y ->
  rf X x y.
Proof.
intros E X so x y Hwf Hv Hlin Hincl [Hin [Hrf Hno]].
generalize Hlin; intro Hline.
generalize Hv; intro Hva.
assert (exists w, rf X w y) as Hrf_y.
  destruct_valid Hv; generalize (Hrf_init y); intros [w [Hew Hwy]]; exists w; auto.
destruct Hrf_y as [w Hrf_wy].
destruct (eqEv_dec w x)  as [Heq | Hdiff].
  subst; trivial.
  assert (tso_rfm E so w y) as Hc.
    split.
      destruct_valid Hv.
      split.
        assert (ws X w x \/ ws X x w) as Hor.
          
                generalize (Hrf_cands w y Hrf_wy); intros [Hw [Hy [l [Hww Hry]]]].
                assert (In _ (writes_to_same_loc_l (events E) l) w /\
                             In _ (writes_to_same_loc_l (events E) l) x) as Hand.
                destruct Hrf as [[Hex' Hwx'] [Hx'y Hl]].
                split; split; auto.
                destruct Hwx' as [lx' [vx' Hx']].
                unfold loc in Hl; rewrite Hx' in Hl; fold (loc y) in Hl.
                generalize (read_from_implies_this_loc Hry); intro Hll.
                destruct Hin as [? [? [lxx [[vxx Hx] [vy Hyy]]]]].
                unfold write_to; exists vxx; rewrite Hx.
                unfold loc in Hll; rewrite Hyy in Hll; inversion Hll; trivial.
                apply (ws_tot E X (Hws_tot l) Hand Hdiff).

        inversion Hor.
        eapply dom_ws_in_events; auto.
        split; auto. apply H.
        eapply ran_ws_in_events; auto.
        split; auto. apply H.
        split.
          destruct Hin as [Hudrx [Hudry ?]]; auto.
          generalize (Hrf_cands w y Hrf_wy); intros [? [? Hl]]; auto.
      split.
        unfold In; unfold previous_writes; split.
          destruct_valid Hv; generalize (Hrf_cands w y Hrf_wy); intros [? [? [l [Hw Hy]]]]; auto.
          apply (write_to_implies_writes E H Hw); auto.         
        split.
         destruct (eqProc_dec (proc_of w) (proc_of y)) as [Heqp | Hdiffp].
            assert (rf_intra X w y) as Hintra.
              split; auto.
            right; destruct_valid Hva.
            assert (In _ (events E) w) as Hew.
              eapply dom_rf_in_events; auto. split; auto. apply Hrf_wy.
            assert (In _ (events E) y) as Hey.
              eapply ran_rf_in_events; auto. split; auto. apply Hrf_wy.
            generalize (same_proc_implies_po w y Hwf Heqp Hew Hey); intro Hor.
    
            inversion Hor; auto.
             assert (pio E y w) as Hpio.
                split; auto.
                generalize (Hrf_cands w y Hrf_wy); intros [? [? [l [[vw Hw] [vy Hy]]]]];
                unfold loc; rewrite Hw; rewrite Hy; auto.
            assert (tc (rel_union (hb E X) (pio E)) w w) as Hcy.
              apply trc_ind with y; apply trc_step; [left | right; auto].
              left; left; destruct Hintra; auto.
           generalize (Hsp w Hcy); intro Ht; inversion Ht.

            assert (rf_inter X w y) as Hinter.
              split; auto.
            generalize (le_lso Hlin); intro Heq.
            left; rewrite Heq; apply Hincl; right; right; auto.
            destruct Hva as [Hwswf [Hrfwf ?]].
            assert (write_serialization_well_formed (events E) (ws X) /\
                         rfmaps_well_formed E (events E) (rf X)) as Hand.
              split; auto.
            apply (rf_implies_same_loc2 X w y Hand Hrf_wy).

          intros x' [Hpwx' Hso_wx'].
          destruct (eqEv_dec w x') as [Heqwx' | Hdiffwx'].
            auto.
            assert (ws X w x' \/ ws X x' w) as Hor.
                 destruct_valid Hv.
                generalize (Hrf_cands w y Hrf_wy); intros [Hw [Hy [l [Hww Hry]]]].
                assert (In _ (writes_to_same_loc_l (events E) l) w /\
                             In _ (writes_to_same_loc_l (events E) l) x') as Hand.
                destruct Hpwx' as [[Hex' Hwx'] [Hx'y Hl]].
                split; split; auto.
                destruct Hwx' as [lx' [vx' Hx']].
                unfold loc in Hl; rewrite Hx' in Hl; fold (loc y) in Hl.
                generalize (read_from_implies_this_loc Hry); intro Hll.
                subst. (* inversion Hll. *)
                destruct Hin as [? [? [lxx [[vxx Hx] [vy Hyy]]]]].
                unfold write_to; exists vx'; rewrite Hx'.
                (*rewrite Hll in Hl; inversion Hl;*) trivial.
                apply (ws_tot E X (Hws_tot l) Hand Hdiffwx').

            inversion Hor as [Hwx' | Hx'w].
              assert (fr E X y x') as Hrf_yx'.
                split.  
                  assert (hb E X w y) as Hhb.
                    left; left; auto.
                  assert (write_serialization_well_formed (events E) (ws X) /\
                              rfmaps_well_formed E (events E) (rf X)) as Hs.
                    destruct_valid Hva; split; split; auto.
                  apply (hb_range_in_events Hwf Hs Hhb); auto.
                  split. 
                  assert (hb E X w x') as Hhb.
                    right; auto.
                  assert (write_serialization_well_formed (events E) (ws X) /\
                              rfmaps_well_formed E (events E) (rf X)) as Hs.
                    destruct_valid Hva; split; split; auto.
                    apply (hb_range_in_events Hwf Hs Hhb); auto.
                    exists w; split; auto.
                    destruct Hpwx' as [Hwwx' [Horx'y Hloc]].
                    inversion Horx'y as [Hso_x'y | Hpo_x'y].
                      assert (so y x') as Hso_yx'.
                        apply Hincl; right; left; right; auto.
                      destruct_lin Hlin.
                       generalize (le_lso Hline); intro Heq.
                       rewrite Heq in Hso_x'y.
                        assert (so x' y /\ so y x') as Hand.
                          split; auto.
                        generalize (Htrans x' y x' Hand); intro Hc.
                        generalize (Hac x' Hc); intro Ht; inversion Ht.

                   assert (pio E x' y) as Hpio.
                          split; auto.
                      assert (tc (rel_union (hb E X) (pio E)) y y) as Hc.
                        apply trc_ind with x'; apply trc_step.
                          left; left; right; auto.
                          right; auto.
                      destruct_valid Hva.
                      unfold acyclic in Hsp; generalize (Hsp y); intro Hco.  
                      contradiction.

             assert (so x' w) as Hso_x'w.
               apply Hincl; right; left; left; auto.
             destruct_lin Hlin.
             assert (so w x' /\ so x' w) as Hand.
               split; auto.
             generalize (Htrans w x' w Hand); intro Hc. 
             unfold acyclic in Hac; generalize (Hac w); intro Hco.
             contradiction.
        assert (ws X w x \/ ws X x w) as Hor.
          destruct_valid Hv.

                generalize (Hrf_cands w y Hrf_wy); intros [Hw [Hy [l [Hww Hry]]]].
                assert (In _ (writes_to_same_loc_l (events E) l) w /\
                             In _ (writes_to_same_loc_l (events E) l) x) as Hand.
                destruct Hrf as [[Hex' Hwx'] [Hx'y Hl]].
                split; split; auto.
                destruct Hwx' as [lx' [vx' Hx']].
                unfold loc in Hl; rewrite Hx' in Hl; fold (loc y) in Hl.
                generalize (read_from_implies_this_loc Hry); intro Hll.
                rewrite <- Hll; inversion Hll.
                destruct Hin as [? [? [lxx [[vxx Hx] [vy Hyy]]]]].
                unfold write_to; exists vxx; rewrite Hx.
                unfold loc in Hll; rewrite Hyy in Hll; inversion Hll; subst; trivial.
                apply (ws_tot E X (Hws_tot l) Hand Hdiff).

        inversion Hor as [Hwx | Hxw].
        assert (so w x) as Hso_wx.
          apply Hincl; right; left; left; auto.
        destruct Hc as [Hrfw [Hpw Hmax]].
        generalize (le_lso Hline); intro Heql; rewrite Heql in *.
        assert (In _ (previous_writes E (rel_union so (po_iico E)) y) x /\ so w x) as Hco.
          split; auto.
        generalize (Hmax x Hco); intro Heq. contradiction.
        assert (so x w) as Hso_xw.
          apply Hincl; right; left; left; auto.
        destruct Hc as [Hrfw [Hpw Hmax]].
        generalize (le_lso Hline); intro Heql; rewrite Heql in *.
        assert (In _ (previous_writes E (rel_union so (po_iico E)) y) w /\ so x w) as Hco.
          split; auto.
        generalize (Hno w Hco); intro Heq. rewrite Heq; unfold not in Hdiff. 
        assert False as Ht.
          apply Hdiff; trivial.
        rewrite Heq; trivial.
       inversion Ht.
Qed.

Lemma rf_in_tso_rfm :
  forall E X so x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  linear_strict_order so (events E) ->
  rel_incl (rel_union (po_tso E) (hb_tso E X)) so ->
  rf X x y ->
  tso_rfm E so x y.
Proof.
intros E X so x y Hwf Hv Hlin Hincl Hrf.
generalize Hv; intro Hva.
split; [|split].

  destruct_valid Hva; generalize (Hrf_cands x y Hrf); 
    intros [Hex [Hey Hl]]; split; [| split]; auto.
  destruct (eqProc_dec (proc_of x) (proc_of y)) as [Heq | Hdiff].
  assert (rf_intra X x y) as Hintra.
    split; auto.
          destruct_valid Hva; generalize (Hrf_cands x y Hrf);
          intros [? [? [l [ [vx Hx] [vy Hy]  ]]]].
      split.
      split; auto. exists l; exists vx; auto.
      split; [right |].
            destruct Hintra as [Hrf_xy ?].
            assert (In _ (events E) x) as Hex.
              eapply dom_rf_in_events; auto. split; auto. apply Hrf_xy.
            assert (In _ (events E) y) as Hey.
              eapply ran_rf_in_events; auto. split; auto. apply Hrf_xy.
      generalize (same_proc_implies_po x y Hwf Heq Hex Hey); intro Hor; 
        inversion Hor; auto.

             assert (pio E y x) as Hpio.
                split; auto.
                unfold loc; rewrite Hx; rewrite Hy; auto.
            assert (tc (rel_union (hb E X) (pio E)) x x) as Hcy.
              apply trc_ind with y; apply trc_step; [left | right; auto].
              left; left; auto.
           generalize (Hsp x Hcy); intro Ht; inversion Ht.
        unfold loc; rewrite Hx; rewrite Hy; auto.

  assert (rf_inter X x y) as Hinter.
    split; auto.
          destruct_valid Hva; generalize (Hrf_cands x y Hrf);
          intros [? [? [l [ [vx Hx] [vy Hy]  ]]]].
  split.
    split; auto. exists l; exists vx; auto.
    split. 
      generalize (le_lso Hlin); intro Heq.
      rewrite Heq.
      left; apply Hincl; right; right; auto.
      unfold loc; rewrite Hx; rewrite Hy; auto.
  intros x' [Hpwx' Hso_xx'].
  destruct Hpwx' as [Hwwx' [Horx' Hl]].
  destruct (eqEv_dec x x') as [Heq | Hdiff].
   auto.
  assert (ws X x x' \/ ws X x' x) as Horxx'.

                 destruct_valid Hv.
                generalize (Hrf_cands x y Hrf); intros [Hx [Hy [l [Hwx Hry]]]].
                assert (In _ (writes_to_same_loc_l (events E) l) x /\
                             In _ (writes_to_same_loc_l (events E) l) x') as Hand.
                destruct Hwwx' as [Hex' [lx' [vx' Hx']]].
                split; split; auto.
                unfold loc in Hl; rewrite Hx' in Hl; fold (loc y) in Hl.
                generalize (read_from_implies_this_loc Hry); intro Hll.
                subst(*; inversion Hll*). 
                generalize (Hrf_cands x y Hrf); intro Hin.
                destruct Hin as [? [? [lxx [[vxx Hxx] [vy Hyy]]]]].
                unfold write_to; exists vx'; rewrite Hx'.
                (*rewrite Hll in Hl; inversion Hl;*) trivial.
                apply (ws_tot E X (Hws_tot l) Hand Hdiff).

  inversion Horxx' as [Hxx' | Hx'x].
    assert (fr E X y x') as Hfr.
      split. 
        assert (hb E X x y) as Hhb.
          left; left; auto.
                  assert (write_serialization_well_formed (events E) (ws X) /\
                              rfmaps_well_formed E (events E) (rf X)) as Hs.
                    destruct_valid Hva; split; split; auto.
        apply (hb_range_in_events Hwf Hs Hhb).
        split. 
        assert (hb E X x x') as Hhb.
          right; auto.
                  assert (write_serialization_well_formed (events E) (ws X) /\
                              rfmaps_well_formed E (events E) (rf X)) as Hs.
                    destruct_valid Hva; split; split; auto.
        apply (hb_range_in_events Hwf Hs Hhb).         
          exists x; split; auto.
  inversion Horx' as [Hso | Hpo].
    assert (so y x') as Hso_yx'.
      apply Hincl; right; left; right; auto.
    generalize Hlin; intro Hline.
    destruct_lin Hlin.
      assert (so x' x') as Hsoc.
        generalize (le_lso Hline); intro Heq; rewrite Heq in Hso.
        eapply Htrans; split; [apply Hso | apply Hso_yx'].
      generalize (Hac x'); intro Hc. contradiction.

    assert (tc (rel_union (hb E X) (pio E)) y y) as Hc.
      apply trc_ind with x'; apply trc_step.
        left; left; right; auto.
        right; split; auto.
     destruct_valid Hva.
     generalize (Hsp y); intro Hco.
     contradiction.
  assert (so x' x) as Hso_x'x.
    apply Hincl; right; left; left; auto.
        destruct_lin Hlin.
        assert (so x' x') as Hsoc.
        eapply Htrans; split; [apply Hso_x'x | apply Hso_xx'].
      generalize (Hac x'); intro Hc. contradiction.
Qed.

Lemma rf_in_hb :
  forall E X x y,
  valid_execution E X ->
  rf X x y ->
  hb E X x y. 
Proof.
intros E X x y Hv Hrf.
left; left; auto.
Qed.

Lemma tso_rfm_po_hb_is_rf :
  forall E X so, 
  well_formed_event_structure E ->
  valid_execution E X ->
  tso_check E X ->
  linear_strict_order so (events E) ->
  rel_incl (rel_union (po_tso E) (hb_tso E X)) so ->
  tso_rfm E so = rf X.
Proof.
intros E X so Hwf Hvalid Hsc Hlin Hincl; generalize Hvalid; intro Hv.
  apply (ext_rel (tso_rfm E so) (rf X)); intros x y; split; intro Hxy.
    apply (tso_rfm_in_rf E X so x y Hwf Hvalid Hlin Hincl Hxy).
    apply (rf_in_tso_rfm E X so x y Hwf Hvalid Hlin Hincl Hxy).
Qed.

Lemma rr_so_in_so :
  forall E so, 
  rel_incl (rrestrict so (writes E)) so.
Proof.
intros E so x y [Hxy ?]; auto.
Qed.

Lemma rr_so_is_writes :
  forall E so,
  Included _
    (Union _ (dom (rrestrict so (writes E)))
      (ran (rrestrict so (writes E)))) (writes E).
Proof.
intros E so x Hx.
inversion Hx as [e Hd | e Hr].
  destruct Hd as [? [? [Hw ?]]]; auto.
  destruct Hr as [? [? [Hw ?]]]; auto.
Qed.

Lemma rr_so_is_lin :
  forall E so,
  linear_strict_order so (events E) ->
  linear_strict_order (rrestrict so (writes E)) (writes E).
Proof.
intros E so Hlin.
destruct_lin Hlin; split; [|split; [|split]].
  apply rr_so_is_writes.
  
  intros x1 x2 x3 [[Hso12 [Hw1 Hw2]] [Hso23 [Hw2' Hw3]]]; split; [|split]; auto.
  assert (so x1 x2 /\ so x2 x3) as Hand.
    split; auto.
  apply (Htrans x1 x2 x3 Hand).

  intros x [Hsox ?]; apply (Hac x Hsox).

  intros x1 x2 Hdiff Hw1 Hw2.
  destruct Hw1 as [He1 ?].
  destruct Hw2 as [He2 ?].
  generalize (Htot x1 x2 Hdiff He1 He2); intro Hor.
  inversion Hor as [H12 | H21]; [left | right]; split; auto.
split; split; auto.
split; split; auto.
Qed.

Lemma tso_req :
  forall E X so, 
  well_formed_event_structure E ->
  valid_execution E X ->
  tso_check E X ->
  linear_strict_order so (events E) ->
  rel_incl (rel_union (po_tso E) (hb_tso E X)) so ->
  (partial_order so (events E) /\
     (exists tso : Rln Event,
     rel_incl tso so /\ linear_strict_order tso (writes E)) /\
     rel_incl (LoadOp E) so /\ rel_incl (StoreStore E) so).
Proof.
intros E X so Hwf Hvalid Htso Hlin Hincl.
split; [| split; [|split]].
destruct_lin Hlin; split; [|split; auto].
eapply incl_trans; [apply Hdr |].
  unfold Included; trivial.
exists (rrestrict so (writes E)); split.
  apply rr_so_in_so.
  eapply rr_so_is_lin; apply Hlin.

    eapply rel_incl_trans; [|apply Hincl].  
  intros x y [Hrx Hpo]; left; unfold po_tso; auto.
    eapply rel_incl_trans; [|apply Hincl].  
  intros x y [Hwx [Hwy Hpo]]; left; unfold po_tso; auto.
Qed.

Lemma incl_udr_tso_check_events :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  Included _ (udr (rel_union (po_tso E) (hb_tso E X))) (events E).
Proof.
intros E X Hwf Hv.
 apply incl_trans with (udr (rel_union (po_iico E) ((*ABasic.AWmm.*)hb E X)));
  [trivial | unfold udr; apply po_union_hb_in_evts; auto].
intros x Hx.
generalize (po_hb_tso_in_po_hb Hwf Hx); intro Hincl; auto.
destruct_valid Hv; split; split; auto.
Qed.

Lemma tso_carac :
  forall E rfm wsn,
  well_formed_event_structure E ->
  ((exists X, valid_execution E X /\ tso_check E X /\ (rf X) = rfm /\ (ws X) = wsn) <->
    (exists so, tso_exec E so /\ tso_rfm E so = rfm /\ tso_ws so = wsn)).
Proof.
intros E rfm wsn Hwf; split; intro Hsc; 
  [destruct Hsc as [X [Hvalid [Hsc [Hrf Hws]]]] | destruct Hsc as [so [Hseq Hrf]]].
generalize (incl_udr_tso_check_events E X Hwf Hvalid); intro Hudrinc.
generalize (topo_ordering_correct Hudrinc Hsc); intros [so [Hlin Hincl]].
 exists so; unfold tso_exec; split.
   eapply tso_req; [apply Hwf | apply Hvalid | apply Hsc | apply Hlin |apply Hincl]. 
  split.

rewrite (tso_rfm_po_hb_is_rf E X so Hwf Hvalid Hsc Hlin Hincl); auto.
rewrite <- Hws;
rewrite (ac_tso_hb_implies_same_ws E X so Hwf Hvalid Hsc Hlin Hincl); auto.
exists (tso_witness E so); split; 
  [apply tso_witness_valid; auto | 
     split; [apply tso_witness_tso| unfold tso_witness; simpl; auto]].
auto. auto.
Qed.

End tso_carac.

End TsoAx.

Module TsoModel.

Definition po_tso (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 => (po_iico E) e1 e2 /\
    (reads E e1 \/ (writes E e1 /\ writes E e2)).

Module TsoArch <: Archi.
Definition ppo (E:Event_struct) := (po_tso E).
Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
  intros E x y [Hpo ?]; auto.
Qed.
Definition inter := true.
Definition intra := false.
Parameter abc : Event_struct -> Execution_witness -> Rln Event.
Hypothesis ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Parameter lockc : Event_struct -> Execution_witness -> Location -> Rln Event.
Definition lock E X := fun e1 => fun e2 => exists l, lockc E X l e1 e2.
Parameter stars : Event_struct -> Execution_witness -> set Event.
Parameter Cs : Type.
Parameter cs : Event_struct -> Execution_witness -> Location -> Cs -> Prop.
Parameter evts : Cs -> set Event.
End TsoArch.

Import TsoArch.
Module TsoBasic := Basic TsoArch.
Import TsoBasic.
Module TsoWmm := Wmm TsoArch.
Import TsoWmm.
Module TsoAx := TsoAx TsoArch.
Import TsoAx.

Lemma po_tso_hb_in_ghb :
  forall E X,
  rel_incl (rel_union (po_tso E) (hb_tso E X)) (ghb E X).
Proof.
intros E X x y Hxy.
inversion Hxy.
right; right; right; auto.
inversion H.
   (* left; auto.
    inversion H. *)
    inversion H0.
    right; right; left; auto.
    right; right; left; auto.
    left; auto.    
Qed.

Lemma exec_tso_check :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  tso_check E X.
Proof.
unfold tso_check;
intros E X Hwf Hvalid.
destruct_valid Hvalid.
generalize (po_tso_hb_in_ghb); intro Hincl.
apply (incl_ac (Hincl E X)); auto.
Qed.

Lemma tso_is_tso :
  forall E rfm wsn,
  well_formed_event_structure E ->
  ((exists so, tso_exec E so /\ tso_rfm E so = rfm /\ tso_ws so = wsn) <->
    (exists X, (*TsoWmm.*)valid_execution E X /\ (rf X) = rfm /\ (ws X) = wsn)).
Proof.
intros E rfm wsn Hwf; split; intro Hex.
  destruct Hex as [so [Hseq [Hrf Hws]]].
  exists (tso_witness E so); split.
  apply tso_witness_valid; 
    [apply Hwf | apply Hseq].
  unfold tso_witness; simpl; auto.
  generalize (tso_carac E rfm wsn Hwf); intros [dir bak].
  apply dir; destruct Hex as [X [? ?]]; exists X; split; [auto | split; auto].
  apply exec_tso_check; auto.
Qed. 

End TsoModel.

Module ABTso.

Definition po_tso (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 => (po_iico E) e1 e2 /\
    (reads E e1 \/ (writes E e1 /\ writes E e2)).
Inductive ABTso (E:Event_struct) (X:Execution_witness) : Event -> Event -> Prop :=
  | Base : forall e1 e2, events E e1 -> events E e2 ->
      po_tso E e1 e2 -> ABTso E X e1 e2
  | Right : forall e1 w2 r2, events E e1 -> events E w2 -> events E r2 ->
      ABTso E X e1 w2 /\ (rf_inter X) w2 r2 -> ABTso E X e1 r2
  | Left : forall w1 r1 e2, events E w1 -> events E r1 -> events E e2 ->
      (rf_inter X) w1 r1 /\ ABTso E X r1 e2 -> ABTso E X w1 e2.

Module SyncTso <: Archi.
Parameter ppo : Event_struct -> Rln Event.
Hypothesis ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
Parameter inter : bool.
Parameter intra : bool.
Definition abc := ABTso.
Lemma ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Proof.
intros E X x y Hxy; split; induction Hxy; auto.
Qed.
Parameter lockc : Event_struct -> Execution_witness -> Location -> Rln Event.
Definition lock E X := fun e1 => fun e2 => exists l, lockc E X l e1 e2.
Parameter stars : Event_struct -> Execution_witness -> set Event.
Parameter Cs : Type.
Parameter cs : Event_struct -> Execution_witness -> Location -> Cs -> Prop.
Parameter evts : Cs -> set Event.
End SyncTso.

Import SyncTso.
Module SyncTsoBasic := Basic SyncTso.
Import SyncTsoBasic.
Module SyncTsoWmm := Wmm SyncTso.
Import SyncTsoWmm.
Module SyncTsoAx := TsoAx SyncTso.
Import SyncTsoAx.

Definition pb_tso (E:Event_struct) : Rln Event := po_tso E.

Lemma hb_tso_seq_pb_incl_ws_u_fr_seq_ab :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  rel_incl (rel_seq (hb_tso E X) (pb_tso E)) (rel_union (rel_seq (rel_union (ws X) (fr E X)) (abc E X)) (abc E X)).
Proof.
intros E X Hwf Hv x y [z [Hhb_xz Hpo_zy]].
  inversion Hhb_xz as [Hws_fr | Hrf].
    inversion Hws_fr as [Hws | Hfr].
  left; exists z; split; [left; auto| eapply Base].
  change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
    unfold pb_tso in Hpo_zy. apply Hpo_zy.
  left; exists z; split; [right; auto| eapply Base].
  change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
    unfold pb_tso in Hpo_zy. apply Hpo_zy.
  right; 
  eapply Left with z.
  change (events E x) with (In _ (events E) x); eapply dom_rf_in_events; auto.
  destruct_valid Hv; split; auto. destruct Hrf as [Hrf ?]; apply Hrf.
  change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
   split; [apply Hrf |].
    eapply Base.
  change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  unfold pb_tso in Hpo_zy. apply Hpo_zy.
Qed. 

Lemma wsrf_seq_pb_incl_ws_u_fr_seq_ab :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  rel_incl (rel_seq (rel_seq (ws X) (rf_inter X)) (pb_tso E)) (rel_seq (rel_union (ws X) (fr E X)) (abc E X)).
Proof.
intros E X Hwf Hv x y [z [ [e [Hws_xe Hrf_ez]] Hpo_zy]].
exists e; split; [left; auto |].
eapply Left with z.
  change (events E e) with (In _ (events E) e); eapply dom_rf_in_events; auto.
  destruct_valid Hv; split; auto. destruct Hrf_ez as [Hrf ?]; apply Hrf.
  change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
 split.
  apply Hrf_ez.
  eapply Base.
  change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  unfold pb_tso in Hpo_zy; auto.
Qed. 

Lemma frrf_seq_pb_incl_ws_u_fr_seq_ab :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  rel_incl (rel_seq (rel_seq (fr E X) (rf_inter X)) (pb_tso E)) (rel_seq (rel_union (ws X) (fr E X)) (abc E X)).
Proof.
intros E X Hwf Hv x y [z [ [e [Hfr_xe Hrf_ez]] Hpo_zy ]].
exists e; split; [right; auto |].
eapply Left with z.
  change (events E e) with (In _ (events E) e); eapply dom_rf_in_events; auto.
  destruct_valid Hv; split; auto. destruct Hrf_ez as [Hrf ?]; apply Hrf.
  change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
 split.
  apply Hrf_ez.
  eapply Base.
  change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
    destruct Hpo_zy as [Hpo ?]; apply Hpo.
  unfold pb_tso in Hpo_zy; auto.
Qed.

Lemma hb'_tso_seq_po_tso_incl_ws_u_fr_seq_ab :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  (rel_incl (po_tso E) (pb_tso E)) -> 
  rel_incl (rel_seq (hb'_tso E X) (po_tso E)) (rel_union (rel_seq (rel_union (ws X) (fr E X)) (abc E X)) (abc E X)).
Proof.
intros E X Hwf Hv Hincl x y Hxy.
destruct Hxy as [z [Hhb'_xz Hpo_zy]].
generalize (Hincl z y Hpo_zy); intro Hpb_zy.
inversion Hhb'_xz as [Hhb_wsrf | Hfr_rf_xz].
  inversion Hhb_wsrf as [Hhb_xz | Hwsrf_xz].
    assert (rel_seq (hb_tso E X) (pb_tso E) x y) as Hhb_pb_xy.
      exists z; auto.
    apply (hb_tso_seq_pb_incl_ws_u_fr_seq_ab E X Hwf Hv x y Hhb_pb_xy).
    assert (rel_seq (rel_seq (ws X) (rf_inter X)) (pb_tso E) x y) as Hwsrf_pb_xy.
      exists z; auto.
    left; apply (wsrf_seq_pb_incl_ws_u_fr_seq_ab E X Hwf Hv x y Hwsrf_pb_xy).
    assert (rel_seq (rel_seq (fr E X) (rf_inter X)) (pb_tso E) x y) as Hfrrf_pb_xy.
      exists z; auto.
    left; apply (frrf_seq_pb_incl_ws_u_fr_seq_ab E X Hwf Hv x y Hfrrf_pb_xy).
Qed.

Lemma hb'_tso_seq_po_tso_path_implies_ws_u_fr_seq_ab_path :
  forall E X x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  (rel_incl (po_tso E) (pb_tso E)) ->
  tc (rel_seq (hb'_tso E X) (po_tso E)) x y ->
  tc (rel_union (rel_seq (rel_union (ws X) (fr E X)) (abc E X)) (abc E X)) x y.
Proof.
intros E X x y Hwf Hv Hincl Htc.
induction Htc.
  apply trc_step; apply (hb'_tso_seq_po_tso_incl_ws_u_fr_seq_ab E X Hwf Hv Hincl x y H).
  apply trc_ind with z; auto.
Qed. 

Lemma po_in_pb_implies_ac_hb_po : (*this is the real important lemma*)
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  (rel_incl (po_tso E) (pb_tso E)) ->
  acyclic (rel_union (hb_tso E X) (po_tso E)).
Proof.
intros E X Hwf Hvalid Hincl.
unfold acyclic; unfold not; intros x Hx.
assert (write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
  destruct_valid Hvalid; split; split; auto.
generalize (hb_tso_union_po_tso_cycle_implies_hb'_tso_seq_po_tso_cycle Hwf Hs Hx); intro Hy.
destruct Hy as [y Hy].
generalize (hb'_tso_seq_po_tso_path_implies_ws_u_fr_seq_ab_path E X y y Hwf Hvalid Hincl Hy); intro Hp.
generalize (ws_u_fr_seq_ab_path_implies_ghb_path Hwf Hvalid Hp); intro Hc.
destruct_valid Hvalid.
unfold acyclic in Hvalid; apply (Hvalid y Hc).
Qed.

Lemma barriers_provide_tso_exec :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  (rel_incl (po_tso E) (pb_tso E)) ->
  (exists so, (tso_exec E so) /\ (tso_rfm E so = rf X) /\ tso_ws so = ws X).
Proof.
intros E X Hwf Hvalid Hpo_in_pb.
generalize (po_in_pb_implies_ac_hb_po E X Hwf Hvalid Hpo_in_pb); intro Hac.
  generalize (tso_carac E (rf X) (ws X) Hwf); intros [dir bak].
apply dir; exists X; split; [auto | unfold tso_check; split; auto].
rewrite (union_triv (Tso.po_tso E) (Tso.hb_tso E X)); auto.
Qed.

End ABTso.

End Tso.
