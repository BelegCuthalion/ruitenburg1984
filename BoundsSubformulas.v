(** * BoundsSubformulas *)

(** This file is a part of Tadeusz Litak's formalisation of W. Ruitenburg JSL 1984 paper 
"On the Period of Sequences (An(p)) in Intuitionistic Propositional Calculus". *)

(** It has been compiled and guaranteed to work with
The Coq Proof Assistant, version 8.4pl6 (September 2015)
(compiled with OCaml 4.02.2) *)



(** ** Contents *)

(** This file contains auxiliary apparatus for Theorem 1.4 (notion of bound etc.),
    roughly corresponding to Definition 1.3 in that paper. *)



Require Export HilbertIPCsetup.


(* ############################################## *)





(* ############################################## *)


(** Preparing to define what a bound is *)


Require Export Coq.Sets.Finite_sets_facts. 
Require Export Coq.Sets.Image.

Arguments Singleton [U] _ _.
Arguments Add [U] _ _ _.
Arguments Union [U] _ _ _.
Arguments Included [U] _ _ .
Arguments cardinal [U] _ _ .
Arguments In [U] _ _ .
Arguments Subtract [U] _ _ _.


Definition App (A : form)  U := Add U A.

Hint Unfold App.

Check App.

Hint Constructors Union.

Ltac u_left := apply Union_introl; auto; try solve [constructor].
Ltac u_right := apply Union_intror; auto; try solve [constructor].


(** ** Subformulas and BoundSubformulas *)

(** We need the notion of a subformula and some facts about them in future developement. *)

(** We have not put these in the first file, as they were not needed so far. *)



Fixpoint Subformulas (A : form) : Ensemble form :=
  match A with
    | var n => Singleton (var n)
    | A ->> B => App (A ->> B) (Union (Subformulas A) (Subformulas B))
    | A & B => App (A & B) (Union (Subformulas A) (Subformulas B))
    | A \v/ B => App (A \v/ B) (Union (Subformulas A) (Subformulas B))
    | tt => Singleton tt
    | ff => Singleton ff
  end.


Definition BoundSubformulas' (A : form) : Ensemble form :=
  fun B => (B = tt) \/ ((Subformulas A B) /\ ((exists n, B = (var n) \/ exists C1 C2, B = C1 ->> C2))).


Fixpoint BoundSubformulas (A : form) : Ensemble form :=
  match A with
    | var n => App tt (Singleton (var n))
    | A ->> B => App (A ->> B) (Union (BoundSubformulas A) (BoundSubformulas B))
    | A & B =>  (Union (BoundSubformulas A) (BoundSubformulas B))
    | A \v/ B => (Union (BoundSubformulas A) (BoundSubformulas B))
    | tt => Singleton tt
    | ff => Singleton tt
  end.


Lemma BS_are_Subformulas : forall A,  Included (BoundSubformulas A) (App tt (Subformulas A)).
  unfold Included, In, App. (* BoundSubformulas.*)
  simpl.
  intros A B Hip. 
  induction A; auto; inversion Hip; try (inversion H); try (apply IHA1 in H1; inversion H1);
  try (apply IHA2 in H1; inversion H1);
  subst; simpl;
  try (apply IHA1 in H); try (apply IHA2 in H) ; try (inversion H);
  try solve [u_left; u_left];
  try solve [u_left; u_right];
  try solve [u_right];
  try solve [u_right; u_left].
Defined.

  
Lemma Subformulas_are_finite : forall A, Finite form (Subformulas A).
  intros. induction A; simpl; try apply Add_preserves_Finite;
          try apply Union_preserves_Finite;
          try apply Singleton_is_finite;
          auto.
Qed.



Lemma BS_finite: forall A, Finite form (BoundSubformulas A).
  intros.  eapply (Finite_downward_closed).
  apply Add_preserves_Finite.
  apply Subformulas_are_finite.
  apply BS_are_Subformulas.
Defined.  

(**
There is a minor discrepancy between the definition of [Bound] used here and the one used by Ruitenburg.
His definition does not impose that all elements of a bound already have [p] substituted with [tt].
Of course, if [b] is a bound in his sense, then [b{tt/p}] is a bound both in the present sense and in his sense,
whereas not everything that is a bound in Ruitenburg's definition would be a bound now;   
in this sense, the present definition is narrower.
*)

Definition Bound (G: context) (A : form) (b : Ensemble form) :=
(*  (forall B: form, In b B -> exists C, In (BoundSubformulas A) C /\ G |-- sub (s_p tt) C <<->> B) /\ *)
  forall C: form, In (BoundSubformulas A) C -> exists B, In b B /\ G |-- sub (s_p tt) C <<->> B.

Definition ExactBound (G: context) (A : form) (b : Ensemble form) :=
  (forall B: form, In b B -> exists C, In (BoundSubformulas A) C /\ G |-- sub (s_p tt) C <<->> B) /\ 
  Bound G A b.


Fixpoint context_to_set (G : context) : Ensemble form :=
  match G with
    | nil => Empty_set form
    | hd :: tl => Add (context_to_set tl) hd
  end.

Lemma context_to_set_increases1 : forall G1 G2 B, In (context_to_set G1) B -> In (context_to_set (G1 ++ G2)) B.
  induction G1; intros.
  - inversion H.
  - inversion H; subst.
    + simpl.  u_left.
    + inversion_clear H0. rewrite <- app_comm_cons. simpl. u_right. 
Qed.



Lemma context_to_set_increases2 : forall G1 G2 B, In (context_to_set G2) B -> In (context_to_set (G1 ++ G2)) B.
  induction G1; intros.
  - rewrite app_nil_l. trivial.
  - apply IHG1 in H. rewrite <- app_comm_cons. simpl. u_left.
Qed.


Lemma context_to_set_dist: forall G1 G2 B, In (context_to_set (G1 ++ G2)) B <->
                                           In (context_to_set G1) B \/ In (context_to_set G2) B.
  induction G1; simpl; intros; split; try tauto.
  - intro. inversion H as [H' | H']. inversion H'. trivial.
  - intro. inversion H; subst.
    + apply IHG1 in H0. inversion H0.
      *  left. u_left.
      * right. trivial.
    + inversion H0; subst. left. u_right.
  - intro. inversion H; subst; unfold Add. inversion H0; subst.
    + apply context_to_set_increases1  with (G2 := G2) in H1. u_left.
    + u_right.
    + apply context_to_set_increases2  with (G1 := G1) in H0. u_left.
Qed.
      
Ltac simpl_spn := unfold s_p; unfold s_n;  simpl; eauto.      


Ltac ctx_set H1 :=
  match goal with
      [H: In (context_to_set (?G1 ++ ?G2)) ?B |- _ ] => apply context_to_set_dist in H; inversion H as [H1 | H1]
   end.                                                                                                         



Lemma Included_Bound : forall G A S1 S2,  Bound G A S1 -> Included S1 S2 -> Bound G A S2.
  unfold Bound, Included. intros.
  specialize (H C H1).
  inversion H as [B [InS EqS]].
  exists B.
  split; trivial.
  apply H0 in InS. trivial.
Qed.

Lemma Same_Set_Bound :  forall  G A S1 S2, Bound G A S1 -> Same_set form S1 S2 -> Bound G A S2.
  unfold Same_set.
  intros. inversion H0.
  eapply Included_Bound; eassumption.
Qed.

Lemma Same_Set_ExactBound :  forall  G A S1 S2, ExactBound G A S1 -> Same_set form S1 S2 -> ExactBound G A S2.
  unfold ExactBound, Same_set. intros; split; intros;
  inversion H; 
  inversion H0.
  - apply H5 in H1. apply H2 in H1. trivial.
  - eapply Included_Bound; eassumption. (*apply H3 in H1. inversion H1. exists x. inversion H6; auto.*)
Qed.


(*
Lemma dup_rem_Same : forall G, Same_set form (context_to_set G) (context_to_set (dup_rem G)).
  unfold Same_set, Included.
  induction G; intros; split; intros; simpl in H; try inversion H; subst;
  inversion IHG;   try (apply H1 in H0); simpl;
  try destruct (in_dec dceq_f a G); simpl in *; trivial; try solve [u_left].
  - inversion H0; subst. apply H1. apply in_split in i.
    inversion i as [l1 [l2 hip]]. rewrite hip in *. simpl in *.
    rewrite context_to_set_dist. right. simpl. u_right.
  - inversion H0; subst. u_right.
  - inversion H; subst.  apply H1 in H2. u_left. inversion_clear H2. u_right.
Qed.
    
Lemma dup_rem_Bound : forall  G A G', Bound G A (context_to_set G') ->   Bound G A (context_to_set (dup_rem G')).
  intros. eapply Same_Set_Bound. eassumption. apply dup_rem_Same.
Qed.
*)


Lemma Singleton_eq : forall (U : Type) (x y : U), In (Singleton x) y <-> x = y.
  intros. split. apply Singleton_inv. apply Singleton_intro.
Defined.


      



Lemma IncludedBound : forall G A B b, Included (BoundSubformulas B) (BoundSubformulas A)
                                      -> Bound G A b -> Bound G B b.
  unfold Included, Bound.
  intros. specialize (H C H1).
  specialize (H0 C H). trivial.
Qed.



Lemma Bound_for_Bound_upward : forall b A G G', Bound G A b -> incl G G' -> Bound G' A b.
Proof.
  unfold Bound, incl.
  intros. specialize (H C H1).
  inversion H as [B [HBa HBb]].
  exists B. split; trivial.
  eapply hil_permute. eapply hil_weaken_gen.
  apply HBb. instantiate (1 := G').
  intros. rewrite in_app_iff. intuition.
Qed.


(** Interestingly, the following useful facts about Union do not seem provided by Ensembles ... *)

Lemma Incl_Union_l : forall U (A B C: Ensemble U), Included (Union A B) C -> Included A C.
  unfold Included. intros.
  apply Union_introl with (C:=B) in H0.
  apply H in H0. trivial.
Qed.
  
Lemma Incl_Union_r : forall U  (A B C: Ensemble U),  Included (Union A B) C -> Included B C.
  unfold Included. intros.
  apply Union_intror with (B:=A) in H0.
  apply H in H0. trivial.
Qed.


  
Lemma Included_refl: forall U (A:Ensemble U), Included A A.
  unfold Included. intros. trivial.
Qed.

Arguments Incl_Union_l [U] _ _ _ _ _ _.
Arguments Incl_Union_r [U] _ _ _ _ _ _.
Arguments Included_refl [U] _ _ _.

(* ##################################################### *)

(** *** Inductive definition of subformula *)

Inductive Sfm_ind : form -> form -> Prop := 
  | sfm_li : forall A B, Sfm_ind A (A ->> B)
  | sfm_ri : forall A B, Sfm_ind B (A ->> B)
  | sfm_la : forall A B, Sfm_ind A (A & B)
  | sfm_ra : forall A B, Sfm_ind B (A & B)                                 
  | sfm_lo : forall A B, Sfm_ind A (A \v/ B)
  | sfm_ro : forall A B, Sfm_ind B (A \v/ B)
  | sfm_rfl : forall A, Sfm_ind A A
  | sfm_tra : forall A B C,  Sfm_ind A B -> Sfm_ind B C -> Sfm_ind A C.                               
                    
Hint Constructors Sfm_ind.

Lemma Sfm_ens_ind : forall B A, (Subformulas B) A -> Sfm_ind A B.
  induction B; simpl; intros; inversion H; subst; auto;
  try (inversion_clear H0); try (apply IHB1 in H1); try (apply IHB2 in H1);
                           try (eapply sfm_tra; try eassumption; auto).
Defined.


Lemma Subformulas_reflexive : forall A, (Subformulas A) A.
  induction A; simpl; try solve [constructor]; try solve [u_right].
Defined.  

Lemma Subformulas_transitive : forall C A B, (Subformulas B) A -> (Subformulas C) B -> (Subformulas C) A.
  induction C; simpl; intros; inversion H0; subst B; try (inversion H1; subst);
  try solve [inversion H; constructor];
  try specialize (IHC1 A x H H2);
  try specialize (IHC2 A x H H2);
  try solve [u_left];
  try solve [u_right];
  inversion H; inversion H2; subst;
  try solve [u_left];
  try solve [u_right].
Defined.    
  

Lemma Sfm_ind_ens : forall B A,  Sfm_ind A B -> (Subformulas B) A.
  intros.
  induction H; simpl;
  unfold App, Add;
  try solve [u_left; u_left; apply Subformulas_reflexive];
  try solve [u_left; u_right; apply Subformulas_reflexive].
  - apply Subformulas_reflexive.
  - eapply Subformulas_transitive; eassumption.
Defined.    

Lemma Sfm_equivalent : forall A B,  (Subformulas B) A <-> Sfm_ind A B.
  intros. split. apply Sfm_ens_ind. apply Sfm_ind_ens.
Defined.


Lemma Inherited_freshness :  forall B C v, fresh_f_p v B -> Subformulas B C -> fresh_f_p v C.
  intros.
  apply Sfm_equivalent in H0.
  induction H0; auto;
  inversion H; subst; auto.
Defined.

(* ######################################## *)

(** *** Bounds and subformulas *)



Lemma BoundVar : forall B n, Subformulas B (var n) -> BoundSubformulas B (var n).
  intros. induction B; simpl in *;
  try solve [u_left];
  inversion H; inversion H0; try (apply IHB1 in H2); try (apply IHB2 in H2); try solve [u_left]; try solve [u_right].
Defined.


Lemma BoundImp : forall B C1 C2, Subformulas B (C1 ->> C2) -> BoundSubformulas B (C1 ->> C2).
  intros. induction B; simpl in *; try (inversion H); subst; unfold App in *;
  inversion H0; try (apply IHB1 in H1); try (apply IHB2 in H1);
  try solve [u_right]; try solve [u_left].
Defined.

