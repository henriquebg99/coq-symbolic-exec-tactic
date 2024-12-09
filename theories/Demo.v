From Tuto0 Require Import Loader.
From Coq Require Import Lists.List.
Import ListNotations.

Goal forall (l : list nat), length l = 1 -> l = nil -> False.
Proof.
  intros l H H'. symb H.
  - symb H.
  - symb H'.
Qed.

Goal forall (l: list nat), cons 0 (cons 1 l) = cons 0 (cons 2 l) -> False.
Proof. intros. symb H. Qed.
       

Goal forall (l : list nat), rev l = [1; 2; 3] -> l = [3; 2; 1].
Proof.
  intros l Hrev. symb Hrev. symb Hrev.
  - symb Hrev; try (symb Hrev).
    + symb Heqn0.
    + symb H1.
      * symb H1.
      * symb H1.
      
  

