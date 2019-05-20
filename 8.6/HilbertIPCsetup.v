(** * HilbertIPCsetup *)

(** This file is the first part of Tadeusz Litak's formalisation of W. Ruitenburg JSL 1984 paper
"On the Period of Sequences (An(p)) in Intuitionistic Propositional Calculus" *)

(** It has been compiled and guaranteed to work with
The Coq Proof Assistant, version 8.4pl6 (September 2015)
(compiled with OCaml 4.02.2) *)



(** ** Contents *)

(** This file  contains underlying definitions and the theory of a (turnstile-Hilbert-style) presentation of IPC
  used in Ruitenburg's paper. *)

(** ** The notion of a formula *)


Inductive  form   :=
  |  var :  nat -> form
  |  imp :  form -> form -> form
  |  and :  form -> form -> form
  |  or  :  form -> form -> form
  |  tt :  form
  |  ff :  form.


Hint Constructors form.


Notation "A '&' B " := (and A B) (at level 40, left associativity).
Notation "A '\v/' B " := (or A B) (at level 45, left associativity).
Notation "A '->>' B" := (imp A B) (at level 49, right associativity).



Definition p := var 0. (** The distinguished variable in polynomials. *)
Definition q := var 1.
Definition r := var 2.


(** *** Decidable equality for variables and fomulas *)

Lemma dceq_v : forall n n0,  {var n = var n0} + {var n <> var n0}.
Proof.
  induction n; destruct n0.
    - left. reflexivity.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - destruct (IHn n0) as [e | e].
      + left. inversion e. reflexivity.
      + right. intro H. inversion H. rewrite H1 in e. apply e. reflexivity.
Qed.

Lemma dceq_f: forall (A B: form), {A = B} + {A <> B}.
Proof.
  induction A; destruct B.
    (* A = var n *)
    - apply dceq_v.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    (* A = A1 ->> A2 *)
    - right. intro H. inversion H.
    - destruct (IHA1 B1) as [e1 | e1]; destruct (IHA2 B2) as [e2 | e2].
      + left. rewrite e1. rewrite e2. reflexivity.
      + right. intro H. inversion H. apply e2 in H2. apply H2.
      + right. intro H. inversion H. apply e1 in H1. apply H1.
      + right. intro H. inversion H. apply e1 in H1. apply H1.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    (* A = A1 & A2 *)
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - destruct (IHA1 B1) as [e1 | e1]; destruct (IHA2 B2) as [e2 | e2].
      + left. rewrite e1. rewrite e2. reflexivity.
      + right. intro H. inversion H. apply e2 in H2. apply H2.
      + right. intro H. inversion H. apply e1 in H1. apply H1.
      + right. intro H. inversion H. apply e1 in H1. apply H1.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    (* A = A1 \v/ A2 *)
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - destruct (IHA1 B1) as [e1 | e1]; destruct (IHA2 B2) as [e2 | e2].
      + left. rewrite e1. rewrite e2. reflexivity.
      + right. intro H. inversion H. apply e2 in H2. apply H2.
      + right. intro H. inversion H. apply e1 in H1. apply H1.
      + right. intro H. inversion H. apply e1 in H1. apply H1.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    (* A = tt *)
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - left. reflexivity.
    - right. intro H. inversion H.
    (* A = tt *)
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - left. reflexivity.
Qed.



(** ** Hilbert-style system for IPC  *)

Reserved Notation "G '|--' A" (at level 63).




Require Export Coq.Lists.List.
Export ListNotations.


Notation context := (list form).


Inductive hil : context -> form -> Prop :=
  (* axioms *)
  | hilK  : forall G A B, G |-- A ->> B ->> A
  | hilS  : forall G A B C, G |-- (A ->> B ->> C) ->> (A ->> B) ->> A ->> C
  | hilC1 : forall G A B, G |-- (A ->> B ->> A & B)
  | hilC2 : forall G A B, G |-- (A & B ->> A)
  | hilC3 : forall G A B, G |-- (A & B ->> B)
  | hilA1 : forall G A B, G |-- (A ->> A \v/ B)
  | hilA2 : forall G A B, G |-- (B ->> A \v/ B)
  | hilA3 : forall G A B C, G |-- (A ->> C) ->> (B ->> C) ->> (A \v/ B ->> C)
  | hilff : forall G A, G |-- ff ->> A
  (* Truth (redundant?) *)
  | hiltt : forall G, G |-- tt
  (* the inferrence rule *)
  | hilMP : forall G A B, G |-- (A ->> B) -> (G |-- A) -> (G |-- B)
  (* and the other stuff *)
  | hilst : forall G A,  In A G -> G |-- A
                               where "G '|--' A" := (hil G A).


Hint Constructors hil.

Ltac hilst_auto := apply hilst; simpl; tauto.

Definition KAidA (G: context) (A : form) := hilK G A (A ->> A).

Hint Resolve KAidA.

Example deriv_id: forall G A, G |-- A ->> A.
Proof.
  intros G A.
  (* A ->> A *)
  apply (hilMP G (A ->> A ->> A) (A ->> A)).
    (* (A ->> A ->> A) ->> A ->> A *)
    - apply (hilMP G (A ->> (A ->> A) ->> A) ((A ->> A ->> A) ->> A ->> A)).
      (* (A ->> (A ->> A) ->> A) ->> (A ->> A ->> A) ->> A ->> A *)
      + apply (hilS G A (A ->> A) A).
      (* A ->> (A ->> A) ->> A *)
      + apply (hilK G A (A ->> A)).
    (* A ->> A ->> A *)
    - apply (hilK G A A).
Qed.



Hint Resolve deriv_id.



Lemma hil_ded: forall G (A B : form), A :: G |-- B ->  G |-- A ->> B.
Proof.
  intros G A B H.
  induction H.
