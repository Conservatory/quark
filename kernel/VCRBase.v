(*
   Quark is Copyright (C) 2012-2015, Quark Team.

   You can redistribute and modify it under the terms of the GNU GPL,
   version 2 or later, but it is made available WITHOUT ANY WARRANTY.

   For more information about Quark, see our web site at:
   http://goto.ucsd.edu/quark/
*)


Require Import Ynot.
Require Import Basis.
Require Import List.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import RSep.
Require Import NArith.
Require Import Arith.
Require Import VCRIO.
Require Import Message.
Require Import Sumbool.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Ltac inv H :=
  inversion H; subst; clear H.

Ltac Unify :=
  match goal with
  | H1: ?x = ?a,
    H2: ?x = ?b |- _ =>
      rewrite H1 in H2; symmetry in H2;
      inversion H2; subst; clear H2;
      try Unify
  end.

Fixpoint beq_la (la:list ascii) (la2:list ascii) : bool :=
  match la with 
  | a :: la =>
    match la2 with
      | a2 :: la2 => if ascii_dec a a2 then beq_la la la2 else false
      | nil => false 
    end
  | nil =>
    match la2 with
      | nil => true
      | _ => false
    end
  end.

Lemma la_eq_cons :
  forall (a:ascii) a' la la',
    a = a' -> la = la' -> a::la = a'::la'.
Proof.
  intros.
  rewrite H. rewrite H0. reflexivity.
Qed.

Lemma la_eq_refl :
  forall la,
    (la_eq la la).
Proof.
  induction la.
  apply nil_la.
  apply not_nil_la.
  auto.
Qed.  

Lemma la_eq_same :
  forall la la' another,
    (la_eq la another) -> (la_eq la' another) -> (la = la').
Proof.
  induction la.
  
  intros.
  inversion H. rewrite<- H2 in H0.
  inversion H0. auto.

  intros.
  destruct la'.
  inversion H0. rewrite<- H2 in H.
  inversion H.

  inversion H.
  inversion H0.
  apply la_eq_cons.
  
  rewrite<- H6 in H.
  inversion H. auto.

  eapply IHla.
  apply H4.

  rewrite<- H2 in H0.
  inversion H0.
  auto.
Qed.


Fixpoint la_ends_with_bool (la:list ascii) (sym:list ascii) : bool :=
  if (laeq la sym) then
    true
  else
    match la with
      | a :: la' => la_ends_with_bool la' sym
      | nil => false
    end.

Lemma la_ends_equal :
  forall la sym, 
    la_ends_with_bool la sym = true -> la_endswith la sym.
Proof.
  induction la.
  intros.
  simpl in H.
  destruct (laeq nil sym).
  rewrite<- e.
  apply la_endswith_same. apply nil_la.

  discriminate.

  intros.
  destruct (laeq (a :: la) sym).
  rewrite <- e.
  apply la_endswith_same.
  apply not_nil_la.
  apply la_eq_refl.

  apply la_endswith_strict.
  apply IHla.
  
  simpl in H.
  destruct (laeq (a::la) sym).
  destruct n. apply e.

  auto.
Qed.


Lemma la_ends_equal_inv :
  forall la sym, 
    la_endswith la sym -> la_ends_with_bool la sym = true.
Proof.
  induction la.

  intros.
  inversion H.
  inversion H0. simpl.
  destruct (laeq nil nil).
  auto.

  destruct n; auto.

  intros.
  simpl.
  destruct (laeq (a :: la) sym).
  auto.
  
  apply IHla.

  inversion H.
  destruct n.
  eapply la_eq_same.
  apply H0.
  apply la_eq_refl.

  auto.
Qed.


Lemma app_assoc {A}:
  forall (l0 l1 l2:list A),
    (l0 ++ l1) ++ l2 = l0 ++ (l1 ++ l2).
Proof.
  intros. induction l0. auto.

  simpl. rewrite IHl0. reflexivity.
Qed.


Theorem app_nil_r (A:Type) : forall l:list A, l ++ nil = l.
Proof.
  induction l; simpl; f_equal; auto.
Qed.


