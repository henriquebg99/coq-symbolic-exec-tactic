From Tuto0 Require Import Loader.
From Coq Require Import Lists.List.
Import ListNotations.

(*** Printing messages ***)

HelloWorld.

Lemma test : True.
Proof.
hello_world.
Abort.

(*** Printing warnings ***)

HelloWarning.

Lemma test : True.
Proof.
hello_warning.
Abort.

(*** Signaling errors ***)

Fail HelloError.

Lemma test : True.
Proof.
Fail hello_error.
Abort.

Inductive T : Set :=
| mkT (n : nat).

Lemma inj : forall n1 n2, mkT n1 = mkT n2 -> n1 = n2.
Proof.
  intros. inversion H. reflexivity. Qed.

Goal forall (l : list nat), rev l = [1; 2; 3] -> l = [3; 2; 1].
Proof.
  intros l Hrev. symb Hrev. symb H1. destruct n1 eqn:?, n0 eqn:?. symb H3.
  - 
  

Goal forall (l : list nat), length l = 1 -> l = nil -> False.
Proof.
  intros l H H'. symb H. simpl in *.  destruct l eqn: Hl.
  * simpl in *. symb H.
  * 
  symb H. symb H'.
Qed.

Lemma test : forall (n1 n2 : nat), False -> mkT n1 = mkT n2 -> False.
Proof. intros n1 n2  Hf Heq. symb Heq. injection Heq.
Abort.
