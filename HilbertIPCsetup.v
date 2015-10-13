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
  induction n; destruct n0; try solve [left; reflexivity];
  try solve [right; intro H; inversion H].
  specialize (IHn n0). destruct IHn as [e | e].
  - left. injection e. intro H. rewrite H. trivial.
  - right. intro H. inversion H. rewrite H1 in *. exfalso. apply e. trivial.
Defined.    
                                                    
Lemma dceq_f: forall (A B: form), {A = B} + {A <> B}.
Proof.   
  induction A; destruct B; try solve [right; intro H; inversion H];
    try destruct (IHA1 B1) as [e1 | e1]; try destruct (IHA2 B2) as [e2 | e2];
    try solve [right; intro H; inversion H; contradiction];
    try solve [left;  try (rewrite e1;  rewrite e2);  reflexivity].
  apply dceq_v.
Defined.  



(** ** Hilbert-style system for IPC  *)

Reserved Notation "G '|--' A" (at level 63).




Require Export Coq.Lists.List.
Export ListNotations.


Notation context := (list form).
 

Inductive hil : context -> form -> Prop :=
 | hilst : forall G A,  In A G -> G |-- A 
 | hilK  : forall G A B, G |-- A ->> B ->> A
 | hilS  : forall G A B C, G |-- (A ->> B ->> C) ->> (A ->> B) ->> A ->> C
 | hilMP : forall G A B, G |-- (A ->> B) -> (G |-- A) -> (G |-- B)
 | hilC1 : forall G A B, G |-- (A ->> B ->> A & B)
 | hilC2 : forall G A B, G |-- (A & B ->> A)
 | hilC3 : forall G A B, G |-- (A & B ->> B)
 | hilA1 : forall G A B, G |-- (A ->> A \v/ B)
 | hilA2 : forall G A B, G |-- (B ->> A \v/ B)
 | hilA3 : forall G A B C, G |-- (A ->> C) ->> (B ->> C) ->> (A \v/ B ->> C)
 | hiltt : forall G, G |-- tt
 | hilff : forall G A, G |-- ff ->> A
                               where "G '|--' A" := (hil G A).

Hint Constructors hil.

Ltac hilst_auto := apply hilst; simpl; tauto.

Definition KAidA (G: context) (A : form) := hilK G A (A ->> A).

Hint Resolve KAidA.

Example deriv_id: forall G A, G |-- A ->> A.
Proof. 
eauto.
Defined.



Hint Resolve deriv_id.

 
  
Lemma hil_ded: forall G (A B : form), A :: G |-- B ->  G |-- A ->> B.
Proof.   
  intros.
  remember (A :: G) as G'.
  induction H; eauto.
  (* apparently, the only case that eauto cannot solve is the first one! *)
  rewrite HeqG' in H. apply in_inv in H. destruct H.
  - rewrite H. auto.
  - eauto. (*pose proof (hilst _ _ H). pose proof (hilK G A0 A). eauto.*)
Defined.

Hint Resolve hil_ded.

Lemma hil_weaken: forall G (A B : form),  G |-- A -> B :: G |-- A.
Proof.   
  intros. revert B. induction H; intro; auto.
  - hilst_auto. 
  - eapply hilMP. apply IHhil1.  apply IHhil2.
Defined.
    
                   

Lemma hil_ded_conv: forall G (A B : form),  G |-- A ->> B -> A :: G |-- B.
Proof. 
  intros. apply (hilMP _ A).
  - apply hil_weaken.  trivial.
  - hilst_auto.
Defined.
  

Definition fold_imp (G:context) (A:form) := fold_left (fun A B => B ->> A)  G A.




(* Definition G0 := [ p ; q ->> (p ->>r) ].*)

(*Compute  G0.*)

(*Compute (fold_imp G0).*)


Lemma hil_permute : forall G G' A, (G |-- A) -> (forall B, In B G <-> In B G') ->  (G' |-- A).
Proof. 
  intros. generalize dependent G'. induction H; eauto.
  intros. apply H0 in H. auto.
Defined.

(*
Hint Resolve hil_permute.
*)

Corollary hil_rev: forall G A, (G |-- A) -> (rev G |-- A).
Proof. 
  intros. eapply hil_permute in H. eassumption.  apply in_rev.
Defined.

(*Hint Resolve hil_rev.*)

Proposition list_fact :  forall (B B0 : form) G G', In B0 (B :: G ++ G') <-> In B0 (G ++ B :: G').
Proof. 
  intros; simpl; repeat (rewrite in_app_iff); split; intro H;
  destruct H; subst; simpl; try tauto.
  apply in_inv in H. tauto.
Defined.

(*
Hint Resolve list_fact.*)

Corollary hil_perm1: forall B G G' A, (B :: G ++ G' |-- A) -> (G ++ B::G' |-- A).
Proof. 
  intros. eapply hil_permute in H. eassumption.  intro. apply list_fact.
Defined.

(*
Hint Resolve hil_perm1.
*)

Lemma hil_ded_ext : forall G G' A, G ++ G' |-- A -> G' |-- fold_imp G A.
Proof.   
  induction G; simpl.
  - trivial.
  - auto.
Defined.

(*
Hint Resolve hil_ded_ext.
*)


(** *** Equivalence *)

Notation "A '<<->>' B" := ((A ->> B) & (B ->> A)) (at level 58).


Lemma split_equiv : forall G A B, (G |-- A <<->> B) <-> ((G |-- A ->> B) /\  (G |-- B ->> A)).
Proof. 
  intros; split; intros.
  - split.
    + eapply hilMP. apply hilC2. eassumption.
    + eapply hilMP. apply hilC3. eassumption.
  - inversion H. eauto.
Defined.



Ltac s_equiv :=
  match goal with
     [ H : hil ?G (?B <<->> ?C) |- _  ] => apply split_equiv in H; inversion H
  end.



Lemma ded_equiv : forall G A B, (G |-- A <<->> B) -> (G |-- A) -> (G |-- B).
Proof. 
  intros. s_equiv. eauto.
Defined.


Lemma eq_impl : forall G A B C D, G |-- (A <<->> B) -> G |-- (C <<->> D) -> G |-- (A ->> C) ->> (B ->> D).
Proof. 
  intros. repeat (s_equiv).
  apply hil_ded. apply hil_ded. apply hilMP with (A := C).
  - apply hil_weaken. apply hil_weaken. trivial.
  - apply hilMP with (A := A).
    + apply hil_weaken. hilst_auto.
    + apply hilMP with (A := B).
      * apply hil_weaken. apply hil_weaken. trivial.
      * hilst_auto.
Defined.

Lemma eq_sym: forall G A B, G |-- (A <<->> B) -> G |-- (B <<->> A).
Proof. 
  intros. s_equiv. apply split_equiv. tauto.
Defined.

Lemma eq_impl_full : forall G A B C D, G |-- (A <<->> B) -> G |-- (C <<->> D) -> G |-- (A ->> C) <<->> (B ->> D).
Proof. 
  intros. apply split_equiv. split.
  - apply eq_impl; trivial.
  - apply eq_sym in H. apply eq_sym in H0. apply eq_impl; trivial.
Defined.

Lemma hil_cut_impl : forall G A B C, G |-- A ->> B -> G |-- B ->> C -> G |-- A ->> C.
Proof.   
  intros. eapply hilMP.
  - eapply hilMP. apply hilS. apply hil_ded. apply hil_weaken. eassumption.
  - trivial.
Defined.

Lemma conj_ded : forall G A B C, G |-- A & B ->> C <-> B::A::G |-- C.
  intros. split; intros.
  - apply hilMP with (A := A & B).
    + repeat (apply hil_weaken).  trivial.
    + apply hilMP with (A := B).
      * apply hilMP with (A := A). auto. hilst_auto.
      * hilst_auto.
  - eapply hilMP. eapply hilMP. apply (hilS _ (A&B) B C) .
    + eapply hil_cut_impl.
      * apply hilC2.
      * apply hil_ded. apply hil_ded. trivial.
    + auto.
Defined.



Lemma ded_conj : forall G A B, G |-- A & B <-> G |-- A /\ G |-- B.
  intros. split; intros; eauto.
  inversion H.
  eapply hilMP; eapply hilMP; eauto.
Defined.


Lemma or_ded : forall G A B C, G |-- A \v/ B ->> C <-> G |-- A ->> C /\ G |-- B ->> C.  intros; split; intros.
  - split; eauto.                                                                       - inversion H. eauto.
Defined.
                                                                                          
Lemma ded_or : forall G A B, G |-- A \/ G |-- B -> G |-- A \v/ B .
  intros.
  inversion H; eauto.
Defined.  (* not needed? *)


Lemma ded_tt1 : forall G A, In A G -> G |-- A <<->> tt.
Proof.
   intros.
   apply split_equiv. eauto.
Defined.

Lemma ded_tt1gen : forall G A, G |-- A -> G |-- A <<->> tt.
Proof.
   intros.
   apply split_equiv. eauto.
Defined.


Lemma ded_tt2 : forall G A, In A G -> G |-- tt <<->> A.
Proof.
   intros.
   apply split_equiv. eauto.
Defined.


Lemma ded_tt2gen : forall G A, G |-- A -> G |-- tt <<->> A.
Proof.
   intros.
   apply split_equiv. eauto.
Defined.





(*  and just a  few little lemmas to simplify our life ... *)

Lemma hil_weaken_gen : forall G G' A, G |-- A -> G' ++ G |-- A.
  unfold incl. induction G'.
  - rewrite app_nil_l. trivial.
  - intros. rewrite <- app_comm_cons. apply hil_weaken. auto.
Defined.


Lemma hil_cut : forall G  A B, G |-- A -> [A] |-- B -> G |-- B.
Proof.
  intros. apply hilMP with (A:=A); auto.
  apply hil_ded. 
  apply hil_permute with (G :=  G ++ [A]).
  apply hil_weaken_gen; auto.
  intro.
  repeat (rewrite in_app_iff). simpl. tauto.
Defined.  

Lemma hil_cut_gen : forall G  G' A B, G |-- A -> A :: G' |-- B -> G ++ G' |-- B.
Proof.
  intros. apply hilMP with (A:=A).
  apply hil_weaken_gen. apply hil_ded. auto.
  apply hil_permute with (G := G' ++ G).
  apply hil_weaken_gen.
  trivial. intro.
  repeat (rewrite in_app_iff). tauto.
Defined.  


Ltac equal_lists :=  subst; simpl; intros; rewrite in_app_iff;  simpl; tauto.



Lemma hil_cut_ord : forall G A B, G |-- A -> A::G |-- B -> G |-- B.
  intros. eapply hil_permute. eapply hil_cut_gen; try (apply H).
  apply H0. equal_lists.
Qed.

Ltac rev_goal :=
  match goal with
       [ H: _ |- hil ?G ?A] => replace G with (rev (rev G)); try apply rev_involutive; try apply hil_rev; simpl rev
   end.                     



Lemma equiv_to_impl : forall G A B, G |-- A <<->> B ->  G |-- A ->> B.
Proof.
  intros. apply split_equiv in H. tauto.
Qed.  


Lemma equiv_congr_and : forall G A B C D,
   G |-- A <<->> B -> G |-- C <<->> D -> G |-- (A & C <<->> B & D).
  intros. apply split_equiv.
  split; apply conj_ded; apply ded_conj; split;
  [ idtac | idtac | apply eq_sym in H |  apply eq_sym in H0]; eapply ded_equiv;
  try solve [repeat (apply hil_weaken); eassumption];
  try solve [repeat(try hilst_auto; apply hil_weaken)].
Defined.

Lemma equiv_congr_or : forall G A B C D,
   G |-- A <<->> B -> G |-- C <<->> D -> G |-- (A \v/ C <<->> B \v/ D).
  intros. apply split_equiv. split; apply or_ded; split; eauto.
Defined.



Lemma eq_trans : forall G A B C,  G |-- A <<->> B -> G |-- B <<->> C -> G |-- A <<->> C.
  intros. repeat (s_equiv). apply split_equiv. split; eapply hil_cut_impl; eauto.
Defined. 


Lemma equiv_tt : forall (G : context) (A : form),  G |-- A <<->> tt <-> G |-- A.
  intros. split. 
  - intros. eapply ded_equiv.
    apply eq_sym. eassumption. auto.
  - apply ded_tt1gen.
Qed.


Lemma eq_id : forall G A,  G |-- A <<->> A.
  intros. apply split_equiv; split; apply deriv_id.
Qed.



Lemma hil_weaken_incl : forall G G' A, G |-- A -> incl G G' -> G' |-- A.
  unfold incl.
  intros. eapply hil_permute. eapply hil_weaken_gen.
  apply H. instantiate (1 := G'). intros.
  rewrite in_app_iff. intuition.
Qed.


(** ** Using omega *)


(** To deal with all the numerical reasoning that one needs *)

Require Export Coq.omega.Omega.

(** The tactic allows to swap instantly terms with the same numerical value,
    something useful when handling [f_p]. *)

Ltac om n1 n2 :=
  replace n1 with n2; try omega.



(* ############################################################## *)

(** ** Basic definitions and facts about substitutions *)


Fixpoint sub  (s: nat -> form)  (A : form) : form :=
  match A with
    | var i => s i
    | A ->> B => (sub s A) ->> (sub s B)
    | A & B => (sub s A) & (sub s B)
    | A \v/ B => (sub s A) \v/ (sub s B)
    | tt => tt
    | ff => ff
  end.

Fixpoint ssub (s : nat -> form) (G: context) : context :=
  match G with
    | nil => nil
    | A :: G' => (sub s A) :: (ssub s G')
  end.

Lemma In_ssub : forall G A s,  In A G -> In (sub s A) (ssub s G).
  induction G. intros.
  - inversion H.
  - intros. apply in_inv in H. inversion H.
    + subst. simpl. left. trivial.
    + apply (IHG A s) in H0. simpl. right. trivial.
Defined.

Hint Resolve In_ssub.
  
Lemma hil_sub : forall s G A, G |-- A -> (ssub s G) |-- (sub s A).
  intros. induction H; simpl; auto.
  simpl in *. eauto.
Defined.

Lemma hil_sub_equiv : forall s G A B, G |-- A <<->> B -> (ssub s G) |-- sub s A <<->> sub s B.
  intros.
  replace (sub s A <<->> sub s B) with (sub s (A <<->> B)).
  apply hil_sub. assumption.
  reflexivity.
Defined.

(*
Definition s_p (A: form) : (nat -> form) :=
  fun n => match n with
             | 0 => A
             | S n' => var (S n')
           end.
*)


Definition s_n (n:nat) (A: form) : (nat -> form) :=
  fun m  => match (eq_nat_dec n m) with
             | left _ => A
             | right _ => (var m)
           end.


Hint Unfold s_n.

Definition s_p := s_n 0.


Notation "A '{' B '}/' n " := (sub (s_n n B) A) (at level 29).

Notation "A '{' B '}/p'" := (sub (s_p B) A) (at level 29).

Notation "'ssubp' B G" := (ssub (s_p B) G) (at level 29).



(** The following fact about substitution is an important property, which can easily break down 
  if IPC is enriched with additional connectives like modalities (one would need to postulate 
  laws like A -> []A to save it). 
  It is essential in what follows though. *)

Lemma ded_subst_gen : forall A G B C n, G |-- B <<->> C -> G |-- (sub (s_n n B) A) <<->> (sub (s_n n C) A).
  unfold s_n.
  intros; induction A;  simpl in *. (* rewrite split_equiv in H;
  inversion H as [BtoC CtoB].*)
  - s_equiv. 
    destruct (eq_nat_dec n n0); subst; simpl in *;  rewrite split_equiv; split; auto.
  - (*specialize (IHA1 _ _ _ H).  specialize (IHA2 _ _ _ H).*)
    apply eq_impl_full; trivial.
  - repeat (s_equiv); apply split_equiv; split;
    apply conj_ded; apply ded_conj; split;
    eapply hilMP;
    try (eapply hil_weaken;  eapply hil_weaken; eassumption);
    hilst_auto.
  - repeat (s_equiv). apply split_equiv. split;
      apply or_ded; split; eauto.
  - eauto.
  - eauto.
Defined.
 



Lemma ded_subst : forall A G B C, G |-- B <<->> C -> G |-- (sub (s_p B) A) <<->> (sub (s_p C) A).
  intros. apply ded_subst_gen. trivial.
Defined.




Ltac simpl_spn_in H := unfold s_p in H; unfold s_n in H;  simpl in H. 

Lemma s_n_triv : forall A n, s_n n A n = A.
Proof.
  intros. unfold s_n. destruct (eq_nat_dec n n).
  - reflexivity.
  - contradict n0. reflexivity.
Defined.


Lemma s_p_Sn :  forall n B, 0 <> n -> s_p B n = var n.
  intros. apply neq_0_lt in H. induction H; auto.
Defined.

Lemma s_p_Sn' :  forall n B,  s_p B (S n) = var (S n).
  trivial.
Defined.


Lemma s_n_neq: forall n n' B, (n<>n') -> (s_n n B) n' = var n'.
  intros. unfold s_n.
  destruct (eq_nat_dec n n'); try contradiction; trivial.
Defined.  

Hint Resolve s_p_Sn.
Hint Resolve s_p_Sn'.
Hint Resolve s_n_neq.


Lemma sub_s_p_trivial2: forall B n, sub (s_p B) (s_p (var 0) n) = s_p B n.
Proof.
  intros.  destruct (eq_nat_dec 0 n); subst; simpl; auto.
  (*hm... repeat (rewrite s_p_Sn) does not work that good here *)
  apply neq_0_lt in n0. induction n0; auto.
Defined.

Lemma sub_s_p_trivial2_gen: forall B n m, sub (s_n n B) (s_n n (var n) m) = s_n n B m.
Proof.
  intros. unfold s_n.
  destruct (eq_nat_dec n m); subst; simpl; auto.
  - destruct ( eq_nat_dec m m). reflexivity . contradict n. reflexivity.
  - destruct (eq_nat_dec n m). contradiction. reflexivity .
Defined.



(** Finally, a simple yet important fact ... *)

Lemma sub_assoc : forall A B C,
                    sub (s_p B) (sub (s_p C) A) = sub (s_p (sub (s_p B) C)) A.
  induction A; simpl; auto;
    try (intros; rewrite IHA1; rewrite IHA2; reflexivity).
  - destruct n; simpl; auto.
Qed.




(* ############################################################### *)

(** ** Notion(s) of freshness *)

Require Export Coq.Bool.Bool. (* for boolean symbols etc *)

Fixpoint fresh_f_b (n: nat) (A:form) : bool :=
    match A with
      | var i => if (eq_nat_dec n i) then false else true
      | tt => true
      | ff => true
      | B & C => (fresh_f_b n B) && (fresh_f_b n C)
      | B ->> C => (fresh_f_b n B) && (fresh_f_b n C)
      | B \v/ C => (fresh_f_b n B) && (fresh_f_b n C)
    end.


(* This is using an example introduced below for bounds, still to rearrange this...
Compute fresh_f_b 0 exform1. (* => false *)
Compute fresh_f_b 1 exform1. (* => false *) 
Compute fresh_f_b 2 exform1. (* see above *)
Compute fresh_f_b 3 exform1. (* => true *)
Compute fresh_f_b 4 exform1. (* => true *)
 *)


Inductive fresh_f_p (n: nat) : form -> Prop :=
      | f_var: forall i, (n <> i) -> fresh_f_p n (var i) 
      | f_tt: fresh_f_p n tt
      | f_ff: fresh_f_p n ff
      | f_and : forall B C, fresh_f_p n B  -> fresh_f_p n C -> (fresh_f_p n (B & C))
      | f_imp  : forall B C, fresh_f_p n B  -> fresh_f_p n C -> (fresh_f_p n (B ->> C))
      | f_or : forall B C, fresh_f_p n B  -> fresh_f_p n C -> (fresh_f_p n (B \v/ C)).

Hint Constructors fresh_f_p.

Lemma freshness_form_equivalent : forall n A, (fresh_f_b n A = true <-> fresh_f_p n A).
  intros; split; intros; induction A;
  try solve [constructor];
  try (simpl in H; rewrite andb_true_iff in H; inversion H as [HA1 HA2]; apply IHA1 in HA1;  apply IHA2 in HA2; constructor; trivial);
  inversion H; subst;
  try (apply IHA1 in H2; apply IHA2 in H3; simpl; rewrite andb_true_iff; tauto).
  - unfold fresh_f_b in *. destruct (eq_nat_dec n n0).
    + inversion H.
    + constructor. trivial.
  -  unfold fresh_f_b. destruct (eq_nat_dec n n0); auto.
Defined.

Definition fresh_l_b (n: nat) (G:context) : bool :=
  (*fold_left andb (map (fresh_f_b n)  G) true.*)
  forallb (fresh_f_b n) G.


(*
Compute fresh_l_b 0 G0.
Compute fresh_l_b 1 G0.
Compute fresh_l_b 2 G0.
Compute fresh_l_b 3 G0.
Compute fresh_l_b 10 G0.
*)

Definition fresh_l_p (n: nat) := Forall (fresh_f_p n).

Lemma freshness_context_equvialent : forall n G, (fresh_l_b n G = true <-> fresh_l_p n G).
  intros; split; intros.
  - unfold fresh_l_p. induction G.
    + trivial.
    + simpl in H. rewrite andb_true_iff in H. inversion H.
      apply freshness_form_equivalent in H0. constructor; auto.
  - induction H; auto. simpl. rewrite andb_true_iff.
    apply freshness_form_equivalent in H. tauto.
Defined.
    
(*Check sub.*)

(** Negation of freshness: occurrence. *)



Inductive occurs_f_p (n: nat) : form -> Prop :=
      | oc_var: forall i, (n = i) -> occurs_f_p n (var i) 
      | oc_and1 : forall B C, occurs_f_p n B  -> (occurs_f_p n (B & C))
      | oc_and2 : forall B C, occurs_f_p n C  -> (occurs_f_p n (B & C))
      | oc_imp1 : forall B C, occurs_f_p n B  -> (occurs_f_p n (B ->> C))
      | oc_imp2 : forall B C, occurs_f_p n C  -> (occurs_f_p n (B ->> C))                                                                        | oc_or1  : forall B C, occurs_f_p n B  -> (occurs_f_p n (B \v/ C))
      | oc_or2  : forall B C, occurs_f_p n C  -> (occurs_f_p n (B \v/ C)).

Hint Constructors occurs_f_p.

Lemma fresh_not_occur : forall A n, fresh_f_p n A <-> ~(occurs_f_p n A).
Proof.
  induction A; unfold not; split; simpl; intros;
  try (inversion H0); try (inversion H); subst; auto;
  try solve [rewrite (IHA1 n) in *; rewrite  (IHA2 n) in *; contradiction];
  try (constructor; [rewrite IHA1 | rewrite IHA2]; intro; eauto).
Defined.



Lemma fresh_dec : forall A n, fresh_f_p n A \/ occurs_f_p n A.
Proof.
  intros; induction A;
  try (destruct (dec_eq_nat n n0); [right | left]); subst;  eauto;
  inversion IHA1; inversion IHA2; eauto.
Defined.  


Lemma fresh_not_occur' : forall A n, ~(fresh_f_p n A) <-> occurs_f_p n A.
Proof.
  intros. split; intros.
  - destruct (fresh_dec A n). contradiction. trivial.
  - intro. rewrite fresh_not_occur in H0. contradiction.
Defined.

(* ######################################################## *)

(** ** Guaranteeing a new fresh variable *)

(** It could be done in many ways, e.g., by the following sequence of steps:
 - extracting the list of all propositional variables in a formula
 - adding all of them together (by e.g. folding plus) and taking successor.
   Or just finding the maximum of a list and taking successor.
However, I opted for an even simpler solution: a function that scans a formula 
and produces such a maximal index directly.
Of course, neither of these methods is exactly the same as "pick the first variable not used in A",
as when the indices of variables used in A are {1, 77}, we will get 78 (even more with fold plus method)
instead of simply 0. It would be doable, but hardly worth the effort, especially that as a trade-off
we are obtaining *)

Fixpoint not_used (A: form) : nat :=
  match A with
    | var n => (S n)
    | B & C => max (not_used B) (not_used C)
    | B ->> C => max (not_used B) (not_used C)
    | B \v/ C => max (not_used B) (not_used C)
    | tt => 0
    | ff => 0
  end.


Lemma all_not_used_fresh : forall A m, (not_used A) <= m -> fresh_f_p m A.
Proof with eauto using Max.max_lub_l, Max.max_lub_r.
  induction A; simpl; intros; constructor...
    omega.
Defined.

Corollary not_used_fresh : forall A, fresh_f_p (not_used A) A.
intros. apply all_not_used_fresh. omega.
Defined.


(* ######################################################## *)

(** ** Basic results involving freshness  *)

(* ######################################################## *)


Lemma subs_fresh_form : forall f A, (forall n, ~(fresh_f_p n A) -> f n = (var n)) -> sub f A = A.
Proof.
  intros.
  induction A; simpl; try (rewrite IHA1); try (rewrite IHA2); try reflexivity;
  try (intros; apply H; intro);
  try (inversion H1; contradiction).
  - destruct (eq_nat_dec 0 n); subst;
       inversion H0; contradict H2; reflexivity.
Defined.


(** The two facts below do not explicitly mention freshness, yet [subs_fresh_form] does wonders for them. *)
 
Corollary sub_s_p_trivial0 : forall A, (sub (s_p (var 0)) A = A).
Proof.
  intros. 
  apply subs_fresh_form. intros. destruct (eq_nat_dec 0 n); subst; auto.
Defined.


Corollary sub_s_p_trivial_gen : forall A n, (sub (s_n n (var n)) A = A).
Proof.
  intros. unfold s_n.
  apply subs_fresh_form. intros. destruct (eq_nat_dec n n0); subst;  auto.
Defined.  

Hint Resolve sub_s_p_trivial0.
Hint Resolve sub_s_p_trivial_gen.



Lemma trivial_sub : forall A B v, (fresh_f_p v A) -> sub (s_n v B) A = A.
  intros.
  apply subs_fresh_form.
  intros. unfold s_n. destruct (eq_nat_dec v n); try (rewrite e in *); try contradiction. reflexivity.
Defined.



Lemma freshcon : forall G A v, Forall (fresh_f_p v) G -> ssub (s_n v A) G = G.
  induction G; intros; try reflexivity.
  inversion_clear H. apply IHG with (A:=A) in H1. simpl.
  rewrite H1. rewrite (trivial_sub a A v). reflexivity. assumption.
Defined.






(*  Here is another important fact about freshness,
   wich I am going to use, e.g., in Lemma 1.7: *)


Lemma freshness_s_p : forall A B, fresh_f_p 0 B -> fresh_f_p 0 (sub (s_p B) A).
Proof.
  induction A;  subst; simpl; auto.
    destruct (eq_nat_dec 0 n); subst; simpl; auto.
    intros.
    rewrite s_p_Sn; auto.
Defined.


Lemma fresh_sub : forall A B n, fresh_f_p n A -> fresh_f_p n B -> (fresh_f_p n (sub (s_p B) A)).
Proof.
  induction A; intros; simpl; auto;
  try ( constructor; inversion H; subst;  auto). 
  - destruct n; auto.
Defined.

Lemma fresh_sub_gen : forall A B n m, fresh_f_p n A -> fresh_f_p n B -> (fresh_f_p n (sub (s_n m B) A)).
Proof.
  unfold s_n.
  induction A; intros; simpl; auto;
  try ( constructor; inversion H; subst;  auto). 
  - destruct (eq_nat_dec m n); auto.
Defined.

(** *** Iterated substitution *)


Fixpoint f_p (A : form) (n : nat) : form :=
  match n with
    | 0 => var 0
    | S n' => sub (s_p (f_p A n')) A
  end.

Example f_p_one : forall A, f_p A 1 = A.
  intro.
  (*remember (f_p A 1) as A'.*)
  induction A;  auto;
   try solve [rewrite <- IHA1 at 2; rewrite <- IHA2 at 2; auto].
  subst; simpl; destruct n; auto.
Defined.  



Lemma f_p_1 : forall A, A = f_p A 1.
Proof.
  intros. simpl.  rewrite sub_s_p_trivial0. reflexivity.
Defined.

Hint Resolve f_p_1.


Lemma sub_f_p_trivial : forall A m, fresh_f_p 0 A -> f_p A (S m) = A.
Proof.
  intros; simpl.  apply subs_fresh_form.
  destruct n; intros.
  - contradiction.
  - reflexivity.
Defined.

   



Lemma  interaction_sub_s_p1 : forall n A B, sub (s_p B) (sub (s_p (f_p A n)) A) =
                                            sub (s_p (sub (s_p B) (f_p A n))) A.
Proof.
  induction A; simpl; auto;
  try (intros; do 2 (rewrite sub_assoc); reflexivity).
  + simpl. destruct n; destruct n0; simpl; auto.
Qed.
    

Lemma interaction_sub_s_p2 : forall m A B, sub (s_p B) (f_p A (S m)) =
                                          sub (s_p (sub (s_p B) (f_p A m))) A.
Proof.
  destruct m.
  - intros. rewrite <- f_p_1. reflexivity. 
  - intros. replace (f_p A (S (S m))) with (sub (s_p (f_p A (S m))) A); try reflexivity.
    apply interaction_sub_s_p1.
Defined.


Lemma f_p_unfold : forall A m, sub (s_p (f_p A m)) A = f_p A (S m).
Proof.
   reflexivity.
Defined.



Lemma f_p_unfold_gen: forall A i k, sub (s_p (f_p A i)) (f_p A (S k)) = f_p A (i + (S k)).
Proof.
  induction k.
  - om (i + 1) (S i). rewrite <- f_p_1. reflexivity.
  - om (i + S (S k))  (S (i + (S k))).
    simpl. rewrite <- IHk. simpl.
    replace (sub (s_p (f_p A k)) A) with (f_p A (S k)); try reflexivity.
    rewrite interaction_sub_s_p1.
    reflexivity.
Defined.


Lemma f_p_unfold_subst :  forall A B m n,  sub (s_p (sub (s_p B) (f_p A n))) (f_p A m) =
                                            sub (s_p B) (f_p A (m + n)).
Proof.
  induction m.
  - reflexivity .
  - intro. rewrite interaction_sub_s_p2.
    rewrite IHm. om (S m + n) (S(m+n)).
    rewrite <- f_p_unfold.
    rewrite interaction_sub_s_p1.
    reflexivity.
Defined.


Lemma fresh_for_f_p : forall A v m, fresh_f_p v A -> fresh_f_p v (f_p A (S m)).
Proof.
  intros. 
  induction m.
  - rewrite <- f_p_1. assumption.
  - rewrite <- f_p_unfold.
    remember (f_p A (S m)) as B.
    destruct A; simpl; auto;
    try (subst B; inversion IHm; inversion H; subst; constructor; apply fresh_sub; auto).
    + destruct n; simpl; auto.
Defined.


Lemma substituting_with_fresh : forall A B v n, fresh_f_p v A -> (sub (s_n v B) (sub (s_n n (var v)) A)) = sub (s_n n B) A.
Proof.
  intros. 
  induction A; simpl;
  try (inversion H; subst); try (rewrite IHA1; trivial);
  try (rewrite IHA2; trivial); auto.
  - unfold s_n. destruct ( eq_nat_dec n n0); simpl.
    + destruct (eq_nat_dec v v). reflexivity . contradict n1; reflexivity .
    + destruct (eq_nat_dec v n0); try reflexivity .
      inversion H; subst. contradict H1. reflexivity .
 Defined.




Lemma fresh_for_f_p_gen :
     forall A v,
       fresh_f_p v A -> fresh_f_p v p -> forall i, fresh_f_p v (f_p A i).
  destruct i; simpl. assumption.
  rewrite f_p_unfold. apply fresh_for_f_p. trivial.
  Qed.




(* ##################################################### *)
(* ##################################################### *)




(** ** Decidability of deducibility *)


(** This is needed in two crucial places in the proof of the main Theorem 1.4. *)
(** This is also the only place where we need classical logic. *)
(** One could rid of this and turn the proof into a wholly constructive one
 by,e g., moving from Hilbert-style to sequent-calculus presentation and 
 incorporating a syntactic proof of cut-elimination for a variant LJ, some of which are available in Coq.
 This would yield decidability of turnstile via the subformula property. *)

(** We are not taking this ambitious option here. *)

(** But in order not to contaminate the whole development with classical metatheory, 
    we enclose it in a module, so that user can easily verify that the excluded middle for deducibility
    (and axioms of classical logic in general) are only use in those two specific places in
    Ruitenburg's proof of Theorem 1.4. *)

Module DecidEquiv.

Require Import Coq.Logic.Classical_Prop.


Lemma decid_equiv : forall G A, (G |-- A) \/ ~(G |-- A).
  intros. apply classic.
Qed.

End DecidEquiv.




      



(* ################################################################ *)

(** ** Case and subcase notation *)

(** It is widely available, see e.g. _Software Foundations_ book.
  The version here was downloaded directly from Coq documentation. 
  The interesting thing in our developement is that we use in the proof of the main result
  (Theorem 1.4) jointly with Coq's bullet notation with a surprisingly satisfying efect.  *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.


Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


(* ################################################################ *)
(* ################################################################ *)
(* ################################################################ *)

(** ** Section 1.2 *)


(** It is so basic I decided to put it in the introductory file *)


Lemma rui_1_2_i : forall A i k, [f_p A i ; sub (s_p tt) A] |-- f_p A (i + k).
  induction k.
  - rewrite <- plus_n_O. hilst_auto.
  - rewrite <- plus_n_Sm. simpl.
    eapply ded_equiv.
    + apply ded_subst with (B := tt). eauto.
    + hilst_auto.
Defined.






Corollary rui_1_2_i_col1 : forall A n, [sub (s_p tt) A] |-- f_p A n ->> f_p A (S n).
intros. apply hil_ded. om (S n) (n + 1).  apply rui_1_2_i. 
Defined.

Corollary rui_1_2_i_col2 : forall A B n,  [f_p A (S n) ->> f_p A n; B; sub (s_p tt) A ] |-- f_p A (S n) <<->> f_p A n.
  intros. apply split_equiv. split. 
   - hilst_auto.
   - apply hil_weaken.  apply hil_weaken. apply rui_1_2_i_col1.
Defined.


Corollary rui_1_2_i_col2_gen_aux : forall A B n k,  [f_p A (S n) ->> f_p A n; B; sub (s_p tt) A ] |-- f_p A (k + S n) <<->> f_p A (k + n).
  induction k; simpl.
  -  apply rui_1_2_i_col2.
  -  apply ded_subst. trivial.
Defined.
 

Corollary rui_1_2_i_col2_gen : forall A B n k,  [f_p A (S n) ->> f_p A n; B; sub (s_p tt) A ] |-- f_p A (k + S n) <<->> f_p A n.
  induction k.
  -  simpl. apply rui_1_2_i_col2.
  -  apply eq_trans with (B := f_p A (k + S n)); trivial.
     replace (k + S n) with (S k + n). apply rui_1_2_i_col2_gen_aux. omega.
Defined.
     
    
Require Import Compare_dec.


Lemma rui_1_2_ii : forall A i n, [ f_p A i; sub (s_p tt) A ] |-- (f_p A (S n) ->> f_p A n) ->> f_p A n.
  intros. apply hil_ded.
  destruct (le_le_S_dec i n);
  destruct (NPeano.Nat.le_exists_sub _ _ l) as [k [Hk _]].
  - rewrite plus_comm in Hk. subst. apply hil_weaken. apply rui_1_2_i.
  - eapply ded_equiv.
    apply rui_1_2_i_col2_gen. instantiate (1 := k). rewrite Hk. hilst_auto.
Defined.


(* ############################################## *)


(** End of Section 1.2 in Ruitenburg paper *)

