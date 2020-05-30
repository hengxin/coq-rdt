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
Require Import Classical_Prop.
Require Import basic.
Import OEEvt. 

Set Implicit Arguments.

Module Uniproc (A : Archi).
Import A.
Module ABasic := Basic A.
Import ABasic.
Module AWmm := Wmm A.
Import AWmm.

Lemma pio_ac :
  forall E x, 
  well_formed_event_structure E ->
  ~((pio E) x x).
Proof.
unfold not;
intros E x Hwf [Hsl Hpo_iico].
unfold well_formed_event_structure in Hwf.
destruct Hwf as [? [? [? [? [Hac ?]]]]].
inversion Hpo_iico as [Hpo | Hiico].
  unfold po_strict in Hpo.
  destruct Hpo as [? [Hinf [? ?]]].
  generalize (gt_irrefl (poi (iiid x))); intro Hc.
  contradiction.
  unfold acyclic in Hac; apply (Hac x);
    apply trc_step; apply Hiico.
Qed.

Lemma pio_trans :
  forall E x y z,
  well_formed_event_structure E ->
  (pio E) x y ->
  (pio E) y z ->
  (pio E) x z.
Proof.
unfold pio;
intros E x y z Hwf [Hslxy Hxy] [Hslyz Hyz].
inversion Hxy as [Hpo_xy | Hiico_xy];
inversion Hyz as [Hpo_yz | Hiico_yz].
  split.
    rewrite Hslxy; auto.
    left; eapply pos_trans; eauto.
  split.
    rewrite Hslxy; auto.
    left; eapply po_iico_trans; eauto.
  split.
    rewrite Hslxy; auto.
    left; eapply iico_po_trans; eauto.
  split.
    rewrite Hslxy; auto.  
    right; eapply iico_trans; eauto.
Qed.

Lemma hb'_pio_irr :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(exists x, rel_union (hb' E X) (pio E) x x).
Proof.
intros E X Hwf Hs [x Hx].
inversion Hx.
generalize (hb'_ac); intro thm; unfold not in thm; apply (thm E X x Hs H).
generalize (pio_ac); intro thm; unfold not in thm; apply (thm E x Hwf H).
Qed.

Lemma hb_union_pio_cycle_implies_hb'_seq_pio_cycle : (*2*)
  forall E X x,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (tc (rel_union (hb E X) (pio E))) x x ->
  (exists y, (tc (rel_seq (hb' E X) (pio E))) y y).
Proof.
intros E X x Hwf Hvalid Hc.
eapply union_cycle_implies_seq_cycle.
apply hb'_pio_irr; auto. apply Hvalid.
unfold not; intros [e Hpio]. 
generalize (pio_ac); intro thm; unfold not in thm; apply (thm E e Hwf Hpio).
unfold not; intros [e Hhb]. 
generalize (hb'_ac); intro thm; unfold not in thm; apply (thm E X e Hvalid Hhb).
unfold trans; intros; eapply hb'_trans; auto.
  apply H. apply H0.
unfold trans; intros; eapply pio_trans; auto.
  apply H. apply H0.
intros e1 e2 H12; auto.
assert (rel_incl (rel_union (hb E X) (pio E)) (rel_union (hb' E X) (pio E))) as Hincl.
  intros e1 e2 H12; inversion H12.
    left; left; left; auto.
    right; auto.
apply (tc_incl Hincl).
apply Hc.
Qed.

Definition hat E (rf:Rln Event) x y :=
  exists w, rf w x /\ rf w y /\ po_iico E x y.

Hypothesis rfm_init :
  forall E X,
  forall er,
    exists ew, In _ (events E) ew /\ rf X ew er.

Lemma hb'_seq_pio_irrefl : (*uni12*)
  forall E X x,
  well_formed_event_structure E ->
  acyclic (rel_union (hb E X) (pio E)) ->
  ~((rel_seq (hb' E X) (pio E)) x x).
Proof.
intros E X e1 Hwf Huni.
  unfold not. intros [e2 [Hhb' Hpio]].
  apply (Huni e2); apply trc_ind with e1.
    apply trc_step; right; auto.
     inversion Hhb' as [Hu | Hfrrf].
       inversion Hu as [Hhb | Hwsrf].
         apply trc_step; left; auto.
         destruct Hwsrf as [x [H2x Hx1]]; apply trc_ind with x; apply trc_step; left; auto.
           right; auto. left; left; auto.
         destruct Hfrrf as [x [H2x Hx1]]; apply trc_ind with x; apply trc_step; left; auto.
           left; right; auto. left; left; auto.
Qed.

Lemma pio_implies_or : (*uni13*)
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  valid_execution E X ->
  acyclic (rel_union (hb E X) (pio E)) ->
  (pio E) x y ->
  (rf X x y \/
   (ws X x y) \/ 
   (exists wx, rf X wx x /\ ws X wx y) \/
   (exists wy, rf X wy y /\ (ws X x wy)) \/
   (exists wx, exists wy, 
      rf X wx x /\ 
      rf X wy y /\ 
      (ws X wx wy)) \/ 
   hat E (rf X) x y).
Proof.
intros E X x y Hwf Hs Hv Huni Hpo.
case_eq (action y); case_eq (action x).
  intros dx lx vx Hx dy ly vy Hy; case_eq dy; case_eq dx; intros Hdy Hdx.
  (*R R*)
  generalize (rfm_init E X x); intros [wx [Hewx Hrfx]];
  generalize (rfm_init E X y); intros [wy [Hewy Hrfy]].
  destruct (eqEv_dec wx wy) as [Heq | Hdiff].

    right; right; right; right; right; unfold hat; exists wx; split; [|split]; auto.
    rewrite Heq; simpl; auto. destruct Hpo; auto.

    right; right; right; right; left; exists wx; exists wy; split; [|split]; auto.
    assert (writes E wx) as Hwwx.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hrfwf as [? [Hrfwf ?]].
      generalize (Hrfwf wx x Hrfx); intros [? [? [l [Hwx ?]]]].
      split; auto. exists l; destruct Hwx as [v Hwx]; exists v; auto.
    assert (writes E wy) as Hwwy.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hrfwf as [? [Hrfwf ?]].
      generalize (Hrfwf wy y Hrfy); intros [? [? [l [Hwy ?]]]].
      split; auto. exists l; destruct Hwy as [v Hwy]; exists v; auto.

    assert (ws X wx wy \/ ws X wy wx) as Hor. 
      destruct Hs as [Hwswf Hrfwf].
      destruct Hwswf.
      destruct_lin (H lx).
      assert (In Event (writes_to_same_loc_l (events E) lx) wx) as Hwx.
        split; auto. apply rf_implies_same_loc with E X x; auto.
        exists vx; rewrite<- Hdy; auto.
      assert (In Event (writes_to_same_loc_l (events E) lx) wy) as Hwy.
        split; auto. apply rf_implies_same_loc with E X y; auto.
        exists vy; rewrite<- Hdx; auto.
        destruct Hpo as [Hsl ?].
        unfold loc in Hsl; rewrite Hx in Hsl; rewrite Hy in Hsl; inversion Hsl; auto.
        generalize (Htot wx wy Hdiff Hwx Hwy); intro Hinv.
        inversion Hinv. destruct H1; left; auto. destruct H1; right; auto.

    inversion Hor as [Hxy | Hyx]; auto.
      assert (fr E X y wx) as Hfr.
        split; auto.
          apply ran_rf_in_events with X wy; auto.
          destruct Hs; auto.
          split. 
          apply dom_rf_in_events with X x; auto.
          destruct Hs; auto.
            exists wy; split; auto.

    assert False as Ht.
      unfold acyclic in Huni; unfold not in Huni; apply Huni with y.
        apply trc_ind with wx. apply trc_step; left; left; right; auto.
        apply trc_ind with x; apply trc_step.
          left; left; left; auto. right; auto.
    inversion Ht.

  (*W R*)
  generalize (rfm_init E X y); intros [wy [Hewy Hrfy]].
  destruct (eqEv_dec x wy) as [Heq | Hdiff].

    left; rewrite Heq; auto.

    right; right; right; left; exists wy; split; auto.
    assert (writes E x) as Hwx.
      split.
      eapply po_iico_domain_in_events; auto; destruct Hpo as [? Hpo]; apply Hpo. 
      exists lx; exists vx; subst; auto.
    assert (writes E wy) as Hwwy.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hrfwf as [? [Hrfwf ?]].
      generalize (Hrfwf wy y Hrfy); intros [? [? [l [Hwy ?]]]].
      split; auto. exists l; destruct Hwy as [v Hwy]; exists v; auto.
    assert (ws X x wy \/ ws X wy x) as Hor. 
      destruct Hs as [Hwswf Hrfwf].
      destruct Hwswf.
      destruct_lin (H lx).
      assert (In Event (writes_to_same_loc_l (events E) lx) x) as Hwwx.
        split; auto. 
          destruct Hpo as [Hsl Hpo]; apply po_iico_domain_in_events with y; auto. 
        exists vx; rewrite<- Hdy; auto.
      assert (In Event (writes_to_same_loc_l (events E) lx) wy) as Hwy.
        split; auto. apply rf_implies_same_loc with E X y; auto.
        exists vy; rewrite<- Hdx; auto.
        destruct Hpo as [Hsl ?].
        unfold loc in Hsl; rewrite Hx in Hsl; rewrite Hy in Hsl; inversion Hsl; auto.
        generalize (Htot x wy Hdiff Hwwx Hwy); intro Hinv.
        inversion Hinv. destruct H1; left; auto. destruct H1; right; auto.

    inversion Hor as [Hxy | Hyx]; auto.
    assert (fr E X y x) as Hfr.
        split; auto.
          apply ran_rf_in_events with X wy; auto.
          destruct Hs; auto.
          split. 
          apply ran_ws_in_events with X wy; auto.
          destruct Hs; auto.
            exists wy; split; auto.
    assert False as Ht.
      unfold acyclic in Huni; unfold not in Huni; apply Huni with y.
        apply trc_ind with x. apply trc_step; left; left; right; auto.
        apply trc_step. right; auto.
    inversion Ht.

  (*R W*)
  generalize (rfm_init E X x); intros [wx [Hewx Hrfx]].
  destruct (eqEv_dec wx y) as [Heq | Hdiff].

    assert (rel_seq (hb' E X) (pio E) y y) as Hseq.
      exists x; split; auto.
        left; left; left; left; subst; auto.
    generalize (hb'_seq_pio_irrefl Hwf Huni Hseq); intro Hnc.
    assert (rel_seq (hb' E X) (pio E) y y) as Hc.
      exists x; split; auto.
        left; left; left; left; simpl; rewrite Heq in Hrfx; auto.
    contradiction.

    right; right; left; exists wx; split; auto.
    assert (writes E wx) as Hwwx.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hrfwf as [? [Hrfwf ?]].
      generalize (Hrfwf wx x Hrfx); intros [? [? [l [Hwx ?]]]].
      split; auto. exists l; destruct Hwx as [v Hwx]; exists v; auto.
    assert (writes E y) as Hwy.
      split.
      eapply po_iico_range_in_events; auto; destruct Hpo as [? Hpo]; apply Hpo.
      exists ly; exists vy; subst; auto.
    assert (ws X wx y \/ ws X y wx) as Hor.

      destruct Hs as [Hwswf Hrfwf].
      destruct Hwswf.
      destruct_lin (H lx).
      assert (In Event (writes_to_same_loc_l (events E) lx) wx) as Hwx.
        split; auto. apply rf_implies_same_loc with E X x; auto.
        exists vx; rewrite<- Hdy; auto.
      assert (In Event (writes_to_same_loc_l (events E) lx) y) as Hwwy.
        split; auto. destruct Hpo as [Hsl Hpo]; apply po_iico_range_in_events with x; auto. 
        exists vy; rewrite<- Hdx; auto.
        destruct Hpo as [Hsl ?].
        unfold loc in Hsl; rewrite Hx in Hsl; rewrite Hy in Hsl; inversion Hsl; auto.
        generalize (Htot wx y Hdiff Hwx Hwwy); intro Hinv.
        inversion Hinv. destruct H1; left; auto. destruct H1; right; auto.

    inversion Hor as [Hxy | Hyx]; auto.
    assert False as Ht.
      unfold acyclic in Huni; unfold not in Huni; apply (Huni y).
        apply trc_ind with wx.
          apply trc_step; left; right; auto.
          apply trc_ind with x; apply trc_step.
            left; left; left; auto. right; auto.
     inversion Ht.

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
    assert (x <> y) as Hdiff.
      destruct (eqEv_dec x y) as [Heq | Hneq]; auto.
      subst; generalize (pio_ac Hwf Hpo); intro Ht; inversion Ht.
    assert (ws X x y \/ ws X y x) as Hor.

      destruct Hs as [Hwswf Hrfwf].
      destruct Hwswf.
      destruct_lin (H lx).
      assert (In Event (writes_to_same_loc_l (events E) lx) x) as Hwwx.
        split; auto. destruct Hpo as [Hsl Hpo]; apply po_iico_domain_in_events with y; auto. 
        exists vx; rewrite<- Hdy; auto.
      assert (In Event (writes_to_same_loc_l (events E) lx) y) as Hwwy.
        split; auto. destruct Hpo as [Hsl Hpo]; apply po_iico_range_in_events with x; auto. 
        exists vy; rewrite<- Hdx; auto.
        destruct Hpo as [Hsl ?].
        unfold loc in Hsl; rewrite Hx in Hsl; rewrite Hy in Hsl; inversion Hsl; auto.
        generalize (Htot x y Hdiff Hwwx Hwwy); intro Hinv.
        inversion Hinv. destruct H1; left; auto. destruct H1; right; auto.
 
    inversion Hor as [Hxy | Hyx]; auto.
       assert False as Ht.
      unfold acyclic in Huni; unfold not in Huni; apply (Huni y).
        apply trc_ind with x.
          apply trc_step; left; right; auto.
          apply trc_step; right; auto.
     inversion Ht.
Qed. 

Lemma hb'_hb' :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_incl (rel_seq (hb' E X) (hb' E X)) (hb' E X).
Proof.
intros E X Hwf Hs x y [e [Hxe Hey]].
inversion Hxe as [Huxe | Hfrrfxe]; inversion Hey as [Huey | Hfrrfey].
  inversion Huxe as [Hhbxe | Hwsrfxe]; inversion Huey as [Hhbey | Hwsrfey].
    inversion Hhbxe as [Hrffrxe | Hwsxe]; inversion Hhbey as [Hrffrey | Hwsey].
      inversion Hrffrxe as [Hrfxe | Hfrxe]; inversion Hrffrey as [Hrfey | Hfrey].

        destruct Hs as [? [? [Hrfc ?]]].
        generalize (ran_rf_is_read E X x e Hrfc Hrfxe); intros [l1 [v1 He1]].
        generalize (dom_rf_is_write E X e y Hrfc Hrfey); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.

        destruct Hfrey as [? [? [we [Hrf Hws]]]].
        destruct Hs as [? [? [? Hrfu]]].
        generalize (Hrfu e we x Hrf Hrfxe); intro Heq.
        rewrite Heq in Hws; left; left; right; auto.

        right; exists e; split; auto.

        destruct Hs as [Hwswf Hrfwf].
        generalize (ran_fr_is_write Hwswf Hfrxe); intros [l1 [v1 He1]].
        generalize (dom_fr_is_read Hrfwf Hfrey); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.

        inversion Hrffrxe as [Hrfxe | Hfrxe].
     
        destruct Hs as [Hwswf Hrfwf].
        destruct Hrfwf as [? [Hrfc ?]].
        generalize (ran_rf_is_read E X x e Hrfc Hrfxe); intros [l1 [v1 He1]].
        generalize (dom_ws_is_write E X e y Hwswf Hwsey); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.

        destruct Hfrxe as [? [? [wx [Hrf Hws]]]].
        left; left; left; right; split; auto.
          split.
            apply ran_ws_in_events with X e; auto. destruct Hs; auto.
            exists wx; split; auto.
            apply ws_trans with E e; auto. destruct Hs; auto.

        inversion Hrffrey as [Hrfey | Hfrey].
 
         left; right; exists e; split; auto.

        destruct Hs as [Hwswf Hrfwf].
        generalize (ran_ws_is_write E X x e Hwswf Hwsxe); intros [l1 [v1 He1]].
        generalize (dom_fr_is_read Hrfwf Hfrey); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.

        left; left; right. apply ws_trans with E e; auto. destruct Hs; auto.

        inversion Hhbxe as [Hrffrxe | Hwsxe].

          inversion Hrffrxe as [Hrfxe | Hfrxe].

            destruct Hwsrfey as [wy [Hwse ?]].
        destruct Hs as [Hwswf Hrfwf].
        destruct Hrfwf as [? [Hrfc ?]].
        generalize (ran_rf_is_read E X x e Hrfc Hrfxe); intros [l1 [v1 He1]].
        generalize (dom_ws_is_write E X e wy Hwswf Hwse); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.   

        right. destruct Hwsrfey as [wy [Hws Hrf]]; exists wy; split; auto.
          destruct Hfrxe as [? [? [wx [Hrfx Hwse]]]]; split; auto.
          split.
            apply ran_ws_in_events with X e; auto. destruct Hs; auto.            
            exists wx; split; auto. 
            apply ws_trans with E e; auto. destruct Hs; auto.

        left; right. destruct Hwsrfey as [wy [Hwse Hrfy]]; exists wy; split; auto.
            apply ws_trans with E e; auto. destruct Hs; auto.

        inversion Hhbey as [Hrffrey | Hwsey].

          inversion Hrffrey as [Hrfey | Hfrey].

        destruct Hwsrfxe as [we [Hws Hrf]].

        destruct Hs as [? [? [Hrfc ?]]].
        generalize (ran_rf_is_read E X we e Hrfc Hrf); intros [l1 [v1 He1]].
        generalize (dom_rf_is_write E X e y Hrfc Hrfey); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.

        left; left; right.
          destruct Hwsrfxe as [we [Hws Hrf]]; destruct Hfrey as [? [? [we' [Hrfe Hwsy]]]].
          destruct Hs as [? [? [? Hrfu]]]; generalize (Hrfu e we we' Hrf Hrfe); intro Heq.
          rewrite <- Heq in Hwsy. 
        apply ws_trans with E we; auto.

        destruct Hwsrfxe as [we [Hws Hrf]].
        destruct Hs as [Hwswf Hrfwf].
        destruct Hrfwf as [? [Hrfc ?]].
        generalize (ran_rf_is_read E X we e Hrfc Hrf); intros [l1 [v1 He1]].
        generalize (dom_ws_is_write E X e y Hwswf Hwsey); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.   

        destruct Hwsrfxe as [we [Hwse Hrfe]].
        destruct Hwsrfey as [wy [Hwsy Hrfy]].
        destruct Hs as [Hwswf Hrfwf].
        destruct Hrfwf as [? [Hrfc ?]].
        generalize (ran_rf_is_read E X we e Hrfc Hrfe); intros [l1 [v1 He1]].
        generalize (dom_ws_is_write E X e wy Hwswf Hwsy); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.   

    inversion Huxe as [Hhbxe | Hwsrfxe].
      inversion Hhbxe as [Hrffrxe | Hwsxe].
        inversion Hrffrxe as [Hrfxe | Hfrxe].

        destruct Hfrrfey as [wy [Hfr Hrfy]].
        destruct Hfr as [? [? [we [Hrf Hws]]]].
          destruct Hs as [? [? [? Hrfu]]]; generalize (Hrfu e we x Hrf Hrfxe); intro Heq.
          rewrite Heq in Hws. left; right; exists wy; split; auto.

        destruct Hfrrfey as [wy [Hfr Hrfy]].
        destruct Hs as [Hwswf Hrfwf].
        generalize (ran_fr_is_write Hwswf Hfrxe); intros [l1 [v1 He1]].
        generalize (dom_fr_is_read Hrfwf Hfr); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.

        destruct Hfrrfey as [wy [Hfr Hrfy]].
        destruct Hs as [Hwswf Hrfwf].
        generalize (ran_ws_is_write E X x e Hwswf Hwsxe); intros [l1 [v1 He1]].
        generalize (dom_fr_is_read Hrfwf Hfr); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.   

        destruct Hfrrfey as [wy [Hfr Hrfy]]; destruct Hwsrfxe as [we [Hws Hrf]].
        assert (ws X x wy) as Hwsxwy.
          destruct Hfr as [? [? [we' [Hrfe Hwsy]]]].
          destruct Hs as [? [? [? Hrfu]]]; generalize (Hrfu e we we' Hrf Hrfe); intro Heq.
          rewrite <- Heq in Hwsy.  
          apply ws_trans with E we; auto.
        left; right; exists wy; split; auto.

   inversion Huey as [Hhbey | Hwsrfey].
      inversion Hhbey as [Hrffrey | Hwsey].
        inversion Hrffrey as [Hrfey | Hfrey].

        destruct Hfrrfxe as [we [Hfr Hrf]].
        destruct Hs as [? [? [Hrfc ?]]].
        generalize (ran_rf_is_read E X we e Hrfc Hrf); intros [l1 [v1 He1]].
        generalize (dom_rf_is_write E X e y Hrfc Hrfey); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.       

        destruct Hfrrfxe as [we [Hfr Hrf]].
        destruct Hfrey as [? [? [we' [Hrfe Hws]]]].
          destruct Hs as [? [? [? Hrfu]]]; generalize (Hrfu e we we' Hrf Hrfe); intro Heq.
          rewrite <- Heq in Hws.
          destruct Hfr as [? [? [wx [Hrfx Hwsx]]]].
          left; left; left; right; split; auto.
            split; auto. exists wx; split; auto. 
            apply ws_trans with E we; auto.

        destruct Hfrrfxe as [we [Hfr Hrf]].
        destruct Hs as [Hwswf Hrfwf].
        destruct Hrfwf as [? [Hrfc ?]].
        generalize (ran_rf_is_read E X we e Hrfc Hrf); intros [l1 [v1 He1]].
        generalize (dom_ws_is_write E X e y Hwswf Hwsey); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.   

        destruct Hfrrfxe as [we [Hfr Hrf]]; destruct Hwsrfey as [wy [Hws Hrfy]].
        destruct Hs as [Hwswf Hrfwf].
        destruct Hrfwf as [? [Hrfc ?]].
        generalize (ran_rf_is_read E X we e Hrfc Hrf); intros [l1 [v1 He1]].
        generalize (dom_ws_is_write E X e wy Hwswf Hws); intros [l2 [v2 He2]].
         rewrite He1 in He2; inversion He2.   

        destruct Hfrrfxe as [we [Hfre Hrfe]]; destruct Hfrrfey as [wy [Hfry Hrfy]].
        destruct Hfry as [? [? [we' [Hrfe' Hwse]]]].
          destruct Hs as [? [? [? Hrfu]]]; generalize (Hrfu e we we' Hrfe Hrfe'); intro Heq.
          rewrite <- Heq in Hwse.
          right; exists wy; split; auto.
          split; auto. 
            apply dom_fr_in_events with X we; auto. 
            split; auto. destruct Hfre as [? [? [wx [Hrfx Hwsx]]]]; exists wx; split; auto.
            apply ws_trans with E we; auto.
Qed.

Lemma hb'_trans :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  tc (hb' E X) x y -> hb' E X x y.
Proof.
intros E X x y Hwf Hs Hxy.
induction Hxy; auto.
apply hb'_hb'; auto.
exists z; split; auto.
Qed.

Lemma ac_hb' :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (hb' E X).
Proof.
intros E X Hwf Hs x Hx.
generalize (hb'_trans Hwf Hs Hx); intro Hhb'.
apply (hb'_ac Hs Hhb').
Qed.

Lemma hb'_rr :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  hb' E X x y -> reads E x -> reads E y ->
  rel_seq (fr E X) (rf X) x y.
Proof.
intros E X x y Hwf Hs Hxy Hrx Hry.
inversion Hxy as [Hu | Hfrrf].
  inversion Hu as [Hhb | Hwsrf].
    inversion Hhb as [Hrffr | Hws].
      inversion Hrffr as [Hrf | Hfr].

        (*contrad Hrx reads E x*)
        destruct Hs as [? [? [Hrfc ?]]].
        generalize (dom_rf_is_write E X x y Hrfc Hrf); intros [l [v Hwx]].
        destruct Hrx as [? [lx [vx Hrx]]]. rewrite Hrx in Hwx; inversion Hwx.

        (*contrad Hry reads E y*)
        destruct Hfr as [? [? [wx [Hrf Hws]]]].
        destruct Hs as [Hwswf ?].
        generalize (ran_ws_is_write E X wx y Hwswf Hws); intros [l [v Hwy]].
        destruct Hry as [? [ly [vy Hry]]]. rewrite Hry in Hwy; inversion Hwy.

        (*contrad Hry reads E y*)
        destruct Hs as [Hwswf ?].
        generalize (ran_ws_is_write E X x y Hwswf Hws); intros [l [v Hwy]].
        destruct Hry as [? [ly [vy Hry]]]. rewrite Hry in Hwy; inversion Hwy.

        (*contrad Hrx reads E x*)
        destruct Hwsrf as [wy [Hws Hrf]].
        destruct Hs as [Hwswf ?].
        generalize (dom_ws_is_write E X x wy Hwswf Hws); intros [l [v Hwx]].
        destruct Hrx as [? [lx [vx Hrx]]]. rewrite Hrx in Hwx; inversion Hwx.

  auto.
Qed.

Lemma uni32 :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  (forall x y, (pio E) x y ->
  (rf X x y \/
   (ws X x y) \/ 
   (exists wx, rf X wx x /\ ws X wx y) \/
   (exists wy, rf X wy y /\ (ws X x wy)) \/
   (exists wx, exists wy, 
      rf X wx x /\ 
      rf X wy y /\ 
      (ws X wx wy)) \/ 
   hat E (rf X) x y)) ->
   (forall e1 e2, (pio E) e1 e2 -> ~(hb' E X e2 e1)).
Proof.
intros E X Hwf Hs Huni3 x y Hxy Hyx.
generalize (Huni3 x y Hxy); intro Hor.
inversion Hor as [Hrf | Hu].
  assert (hb' E X x x) as Hc.
    apply hb'_hb'; auto.
    exists y; split; auto.
    left; left; left; left; auto.
    apply (hb'_ac Hs Hc). 
  inversion Hu as [Hws | Hun].
  assert (hb' E X x x) as Hc.
    apply hb'_hb'; auto.
    exists y; split; auto.
    left; left; right; auto.
    apply (hb'_ac Hs Hc). 
      inversion Hun as [Hrfws1 | Huni].
        destruct Hrfws1 as [wx [Hrf Hws]].
        assert (fr E X x y) as Hfr1.
          split. 
          apply ran_rf_in_events with X wx; auto.
          destruct Hs; auto.
          split.
          apply ran_ws_in_events with X wx; auto.
          destruct Hs; auto.
          exists wx; split; auto.
  assert (hb' E X x x) as Hc.
    apply hb'_hb'; auto.
    exists y; split; auto.
    left; left; left; right; auto.
    apply (hb'_ac Hs Hc). 
        inversion Huni as [Hrfws2 | Hunio].
          assert (rel_seq (ws X) (rf X) x y) as Hwsrf2.
            destruct Hrfws2 as [wy [Hy Hx]]; exists wy; split; auto.
  assert (hb' E X x x) as Hc.
    apply hb'_hb'; auto.
    exists y; split; auto.
    left; right; auto.
    apply (hb'_ac Hs Hc). 
          inversion Hunio as [Hrfb | Hhat].
            destruct Hrfb as [wx [wy [Hrfx [Hrfy Hws]]]].
            assert (fr E X x wy) as Hfr.
              split.
              apply ran_rf_in_events with X wx; auto.
              destruct Hs; auto. 
              split. 
          apply ran_ws_in_events with X wx; auto.
          destruct Hs; auto.
              exists wx; split; auto.
  assert (hb' E X x x) as Hc.
    apply hb'_hb'; auto.
    exists y; split; auto.
    right; exists wy; split; auto.
    apply (hb'_ac Hs Hc).
      assert (reads E x) as Hrx.
      destruct Hhat as [w [Hrfx [Hrfy ?]]].
        split.
          apply ran_rf_in_events with X w; auto.
          destruct Hs; auto.
          destruct Hs as [? [? [Hrfc ?]]].
          generalize (Hrfc w x Hrfx); intros [? [? [l [? [v Hx]]]]].
          exists l; exists v; auto.
      assert (reads E y) as Hry.
      destruct Hhat as [w [Hrfx [Hrfy ?]]].
        split.
          apply ran_rf_in_events with X w; auto.
          destruct Hs; auto.
          destruct Hs as [? [? [Hrfc ?]]].
          generalize (Hrfc w y Hrfy); intros [? [? [l [? [v Hy]]]]].
          exists l; exists v; auto.
      generalize (hb'_rr Hwf Hs Hyx Hry Hrx); intros [wx [Hfr Hrf]].
      destruct Hhat as [w [Hrfx [Hrfy ?]]].
      generalize Hs; intros [? [? [? Hrfu]]].
      generalize (Hrfu x w wx Hrfx Hrf); intro Heq.
      rewrite <- Heq in Hfr.
  assert (hb' E X y y) as Hc.
    apply hb'_hb'; auto.
    exists w; split; auto.
    left; left; left; right; auto.
    left; left; left; left; auto.
    apply (hb'_ac Hs Hc). 
Qed.

Lemma uni23 :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  valid_execution E X ->
  (forall e1 e2, (pio E) e1 e2 -> ~(hb' E X e2 e1)) ->
  (forall x y, (pio E) x y ->
  (rf X x y \/
   (ws X x y) \/ 
   (exists wx, rf X wx x /\ ws X wx y) \/ (*fr x y*)
   (exists wy, rf X wy y /\ (ws X x wy)) \/ (*ws;rf x y*)
   (exists wx, exists wy, (*fr;rf x y*)
      rf X wx x /\ 
      rf X wy y /\ 
      (ws X wx wy)) \/ 
   hat E (rf X) x y)).
Proof.
intros E X Hwf Hs Hv Huni2 x y Hpio.
case_eq (action y); case_eq (action x).
  intros dx lx vx Hx dy ly vy Hy; case_eq dy; case_eq dx; intros Hdy Hdx.
(*R R*)
  generalize (rfm_init E X x); intros [wx [Hewx Hrfx]];
  generalize (rfm_init E X y); intros [wy [Hewy Hrfy]].
  destruct (eqEv_dec wx wy) as [Heq | Hdiff].

    right; right; right; right; right; unfold hat; exists wx; split; [|split]; auto.
    rewrite Heq; simpl; auto. destruct Hpio; auto.

    right; right; right; right; left; exists wx; exists wy; split; [|split]; auto.
    assert (writes E wx) as Hwwx.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hrfwf as [? [Hrfwf ?]].
      generalize (Hrfwf wx x Hrfx); intros [? [? [l [Hwx ?]]]].
      split; auto. exists l; destruct Hwx as [v Hwx]; exists v; auto.
    assert (writes E wy) as Hwwy.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hrfwf as [? [Hrfwf ?]].
      generalize (Hrfwf wy y Hrfy); intros [? [? [l [Hwy ?]]]].
      split; auto. exists l; destruct Hwy as [v Hwy]; exists v; auto.

    assert (ws X wx wy \/ ws X wy wx) as Hor.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hwswf.
      destruct_lin (H lx).
      assert (In Event (writes_to_same_loc_l (events E) lx) wx) as Hwx.
        split; auto. apply rf_implies_same_loc with E X x; auto.
        exists vx; rewrite<- Hdy; auto.
      assert (In Event (writes_to_same_loc_l (events E) lx) wy) as Hwy.
        split; auto. apply rf_implies_same_loc with E X y; auto.
        exists vy; rewrite<- Hdx; auto.
        destruct Hpio as [Hsl ?].
        unfold loc in Hsl; rewrite Hx in Hsl; rewrite Hy in Hsl; inversion Hsl; auto.
        generalize (Htot wx wy Hdiff Hwx Hwy); intro Hinv.
        inversion Hinv. destruct H1; left; auto. destruct H1; right; auto.

    inversion Hor as [Hxy | Hyx]; auto.
      assert (fr E X y wx) as Hfr.
        split; auto.
          apply ran_rf_in_events with X wy; auto.
          destruct Hs; auto.
          split. 
          apply ran_ws_in_events with X wy; auto.
          destruct Hs; auto.
            exists wy; split; auto.

    assert False as Ht.
      unfold not in Huni2; apply Huni2 with x y; auto.
      right; exists wx; auto.
    inversion Ht.

  (*W R*)
  generalize (rfm_init E X y); intros [wy [Hewy Hrfy]].
  destruct (eqEv_dec x wy) as [Heq | Hdiff].

    left; rewrite Heq; auto.

    right; right; right; left; exists wy; split; auto.
    assert (writes E x) as Hwx.
      split.
      eapply po_iico_domain_in_events; auto; destruct Hpio as [? Hpo]; apply Hpo. 
      exists lx; exists vx; subst; auto.
    assert (writes E wy) as Hwwy.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hrfwf as [? [Hrfwf ?]].
      generalize (Hrfwf wy y Hrfy); intros [? [? [l [Hwy ?]]]].
      split; auto. exists l; destruct Hwy as [v Hwy]; exists v; auto.
    assert (ws X x wy \/ ws X wy x) as Hor. 
      destruct Hs as [Hwswf Hrfwf].
      destruct Hwswf.
      destruct_lin (H lx).
      assert (In Event (writes_to_same_loc_l (events E) lx) x) as Hwwx.
        split; auto. destruct Hpio as [Hsl Hpo]; apply po_iico_domain_in_events with y; auto.  
        exists vx; rewrite<- Hdy; auto.
      assert (In Event (writes_to_same_loc_l (events E) lx) wy) as Hwy.
        split; auto. apply rf_implies_same_loc with E X y; auto.
        exists vy; rewrite<- Hdx; auto.
        destruct Hpio as [Hsl ?].
        unfold loc in Hsl; rewrite Hx in Hsl; rewrite Hy in Hsl; inversion Hsl; auto.
        generalize (Htot x wy Hdiff Hwwx Hwy); intro Hinv.
        inversion Hinv. destruct H1; left; auto. destruct H1; right; auto.

    inversion Hor as [Hxy | Hyx]; auto.
      assert (fr E X y x) as Hfr.
        split.
          apply ran_rf_in_events with X wy; auto.
          destruct Hs; auto.
        split.
          apply ran_ws_in_events with X wy; auto.
          destruct Hs; auto.
        exists wy; split; auto.
    assert False as Ht.
      unfold not in Huni2; apply Huni2 with x y; auto.
      left; left; left; right; auto.
    inversion Ht.
  
  (*R W*)
  generalize (rfm_init E X x); intros [wx [Hewx Hrfx]].
  destruct (eqEv_dec wx y) as [Heq | Hdiff].

    assert (rel_seq (hb' E X) (pio E) y y) as Hseq.
      exists x; split; auto.
        left; left; left; left; subst; auto.
    destruct Hseq as [e [Hye Hey]]; generalize (Huni2 e y Hey); intro Hnye.
    contradiction.

    right; right; left; exists wx; split; auto.
    assert (writes E wx) as Hwwx.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hrfwf as [? [Hrfwf ?]].
      generalize (Hrfwf wx x Hrfx); intros [? [? [l [Hwx ?]]]].
      split; auto. exists l; destruct Hwx as [v Hwx]; exists v; auto.
    assert (writes E y) as Hwy.
      split.
      eapply po_iico_range_in_events; auto; destruct Hpio as [? Hpo]; apply Hpo.
      exists ly; exists vy; subst; auto.
    assert (ws X wx y \/ ws X y wx) as Hor.
      destruct Hs as [Hwswf Hrfwf].
      destruct Hwswf.
      destruct_lin (H lx).
      assert (In Event (writes_to_same_loc_l (events E) lx) wx) as Hwx.
        split; auto. apply rf_implies_same_loc with E X x; auto.
        exists vx; rewrite<- Hdy; auto.
      assert (In Event (writes_to_same_loc_l (events E) lx) y) as Hwwy.
        split; auto. destruct Hpio as [Hsl Hpo]; apply po_iico_range_in_events with x; auto. 
        exists vy; rewrite<- Hdx; auto.
        destruct Hpio as [Hsl ?].
        unfold loc in Hsl; rewrite Hx in Hsl; rewrite Hy in Hsl; inversion Hsl; auto.
        generalize (Htot wx y Hdiff Hwx Hwwy); intro Hinv.
        inversion Hinv. destruct H1; left; auto. destruct H1; right; auto.

    inversion Hor as [Hxy | Hyx]; auto.
    assert False as Ht.
      unfold not in Huni2; apply Huni2 with x y; auto.
      left; right; exists wx; auto.
     inversion Ht.

  (*W W*)
    right; left.
    assert (writes E x) as Hwx.
      split.
      eapply po_iico_domain_in_events; auto; destruct Hpio as [? Hpo]; apply Hpo.
      exists lx; exists vx; subst; auto.
    assert (writes E y) as Hwy.
      split.
      eapply po_iico_range_in_events; auto; destruct Hpio as [? Hpo]; apply Hpo.
      exists ly; exists vy; subst; auto.
    assert (x <> y) as Hdiff.
      destruct (eqEv_dec x y) as [Heq | Hneq]; auto.
      subst; generalize (pio_ac Hwf Hpio); intro Ht; inversion Ht.
    assert (ws X x y \/ ws X y x) as Hor. 
      destruct Hs as [Hwswf Hrfwf].
      destruct Hwswf.
      destruct_lin (H lx).
      assert (In Event (writes_to_same_loc_l (events E) lx) x) as Hwwx.
        split; auto. destruct Hpio as [Hsl Hpo]; apply po_iico_domain_in_events with y; auto. 
        exists vx; rewrite<- Hdy; auto.
      assert (In Event (writes_to_same_loc_l (events E) lx) y) as Hwwy.
        split; auto. destruct Hpio as [Hsl Hpo]; apply po_iico_range_in_events with x; auto. 
        exists vy; rewrite<- Hdx; auto.
        destruct Hpio as [Hsl ?].
        unfold loc in Hsl; rewrite Hx in Hsl; rewrite Hy in Hsl; inversion Hsl; auto.
        generalize (Htot x y Hdiff Hwwx Hwwy); intro Hinv.
        inversion Hinv. destruct H1; left; auto. destruct H1; right; auto.

    inversion Hor as [Hxy | Hyx]; auto.
       assert False as Ht.
      unfold not in Huni2; apply Huni2 with x y; auto.
      left; left; right; auto.
     inversion Ht.
Qed. 

Lemma uni23b :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  valid_execution E X ->
  (forall e1 e2, (pio E) e1 e2 -> ~(hb' E X e2 e1)) ->
  rel_incl (pio E) (rel_union (hb' E X) (hat E (rf X))).
Proof.
intros E X Hwf Hs Hv Huni2 x y Hpio.
generalize (uni23 Hwf Hs Hv Huni2 Hpio); intro Hor.
inversion Hor.
  left; left; left; left; left; auto.
    inversion H.
      left; left; left; right; auto.
      inversion H0.
          destruct H1 as [wx [Hrf Hws]].
        left; left; left; left; right; split.
          apply ran_rf_in_events with X wx; auto.
          destruct Hs; auto.
          split. 
          apply ran_ws_in_events with X wx; auto.
          destruct Hs; auto.
          exists wx; split; auto.
        inversion H1.
          left; left; right; destruct H2 as [wy [Hrf Hws]]; exists wy; split; auto.
          inversion H2.
            destruct H3 as [wx [wy [Hrfx [Hrfy Hws]]]].
              left; right; exists wy; split; auto.
                split.
          apply ran_rf_in_events with X wx; auto.
          destruct Hs; auto.
                split. 
          apply ran_ws_in_events with X wx; auto.
          destruct Hs; auto.
                exists wx; split; auto.
              right; auto.
Qed.

Set Implicit Arguments.
Lemma rel_seq_distrib :
  forall A (r r1 r2: Rln A), 
  rel_incl (rel_seq r (rel_union r1 r2)) (rel_union (rel_seq r r1) (rel_seq r r2)).
Proof.
intros A r r1 r2 x y [e [Hxe Hor_ey]].
inversion Hor_ey.
  left; exists e; split; auto.
  right; exists e; split; auto.
Qed.

Lemma rel_seq_replace :
  forall A (r r' r'': Rln A), 
  rel_incl r' r'' ->
  rel_incl (rel_seq r r') (rel_seq r r'').
Proof.
intros A r r' r'' Hincl x y [e [Hxe Hey]].
  exists e; split; auto.
Qed.
Unset Implicit Arguments.

Lemma hb'_hat :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_incl (rel_seq (hb' E X) (hat E (rf X))) (hb' E X).
Proof.
intros E X Hwf Hs x y [e [Hxe Hey]].
case_eq (action x).
  intros dx lx vx Hx; case_eq dx; intros Hdx.

(*R*)
  assert (reads E x) as Hrx.
    split.
      apply hb'_dom_in_evts with X e; auto.
      exists lx; exists vx; auto. subst; auto.
  assert (reads E e) as Hre.
    split.
      apply hb'_ran_in_evts with X x; auto.
      destruct Hey as [w [Hrfe [Hrfy ?]]].
      destruct Hs as [? Hrfwf].
      destruct Hrfwf as [? [Hrfc ?]].
      generalize (Hrfc w e Hrfe); intros [? [? [l [? [v He]]]]]; exists l; exists v; auto.
  generalize (hb'_rr Hwf Hs Hxe Hrx Hre); intros [we [Hfr Hrf]].
  destruct Hey as [wy [Hrf_wye [Hrf_wy ?]]].
  assert (we = wy) as Heq. (*rf_uni*)
    destruct Hs as [? [? [? Hrfu]]].
    apply (Hrfu e we wy); auto.
  right; exists we; split; subst; auto.

(*W*)
  destruct Hey as [we [Hrfe [Hrfy ?]]].
  destruct (eqEv_dec we x) as [Heq | Hdiff].
    left; left; left; left; subst; auto.
  assert (ws X we x \/ ws X x we) as Hor.
      generalize Hs; intros [Hwswf Hrfwf].
      destruct Hwswf.
      destruct_lin (H0 lx).
      assert (In Event (writes_to_same_loc_l (events E) lx) x) as Hwwx.
        split; auto. apply hb'_dom_in_evts with X e; auto.  
        exists vx; rewrite<- Hdx; auto.
      assert (In Event (writes_to_same_loc_l (events E) lx) we) as Hwwe.
        split; auto. apply dom_rf_in_events with X y; auto. 
        destruct Hrfwf as [? [Hrfc ?]]; generalize (Hrfc we e Hrfe); intros [? [? [le [Hwe ?]]]].
        generalize (hb'_implies_same_loc Hwf Hs Hxe); intro Hsl.
        generalize (rf_implies_same_loc2 X we e Hs Hrfe); intro Hslwee.
        rewrite <- Hslwee in Hsl.
        unfold loc in Hsl; rewrite Hx in Hsl; destruct Hwe as [ve He]. rewrite He in Hsl; inversion Hsl.
        exists ve; auto.
        generalize (Htot we x Hdiff Hwwe Hwwx); intro Hinv.
        inversion Hinv. destruct H2; left; auto. destruct H2; right; auto.
  inversion Hor.

    assert (fr E X e x) as Hfr.
      split.
          apply ran_rf_in_events with X we; auto.
          destruct Hs; auto.
      split. 
          apply ran_ws_in_events with X we; auto.
          destruct Hs; auto.
      exists we; split; auto.
     assert (hb' E X e e) as Hc.
       apply hb'_hb'; auto; exists x; split; auto.
       left; left; left; right; auto.
     generalize (hb'_ac Hs Hc); intro Ht; inversion Ht.

    left; right; exists we; split; auto.
Qed.

Lemma hb'_pio_incl :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  valid_execution E X ->
  (forall e1 e2, (pio E) e1 e2 -> ~(hb' E X e2 e1)) ->
  rel_incl (rel_seq (hb' E X) (pio E)) (hb' E X).
Proof.
intros E X Hwf Hs Hv Huni2 x y Hseq.
generalize (uni23b Hwf Hs Hv Huni2); intro Hincl.
generalize (rel_seq_replace Hincl Hseq); intro Hrr.
generalize (rel_seq_distrib Hrr); intro Hor.
inversion Hor.
  apply hb'_hb'; auto.
  apply hb'_hat; auto.
Qed.

Lemma uni21 :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  valid_execution E X ->
  ((forall e1 e2, (pio E) e1 e2 -> ~(hb' E X e2 e1)) ->
    acyclic (rel_union (hb E X) (pio E))).
Proof.
intros E X Hwf Hs Hv Huni2.
  intros x Hx.
    generalize (hb_union_pio_cycle_implies_hb'_seq_pio_cycle Hwf Hs Hx); intros [y Hy].
    generalize (hb'_pio_incl E X Hwf Hs Hv Huni2); intro Hincl.
    generalize (tc_incl Hincl); intro Htci.
    generalize (Htci y y Hy); intro Hcy.
    generalize (ac_hb' Hwf Hs); intro Hac; unfold acyclic in Hac; unfold not in Hac; 
      apply (Hac y Hcy).
Qed.

End Uniproc.
