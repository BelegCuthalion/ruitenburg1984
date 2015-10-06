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
(*  (forall B: form, In form b B -> exists C, In form (BoundSubformulas A) C /\ G |-- sub (s_p tt) C <<->> B) /\ *)
  forall C: form, In form (BoundSubformulas A) C -> exists B, In form b B /\ G |-- sub (s_p tt) C <<->> B.

Definition ExactBound (G: context) (A : form) (b : Ensemble form) :=
  (forall B: form, In form b B -> exists C, In form (BoundSubformulas A) C /\ G |-- sub (s_p tt) C <<->> B) /\ 
  Bound G A b.


Fixpoint context_to_set (G : context) : Ensemble form :=
  match G with
    | nil => Empty_set form
    | hd :: tl => Add (context_to_set tl) hd
  end.

Lemma context_to_set_increases1 : forall G1 G2 B, In form (context_to_set G1) B -> In form (context_to_set (G1 ++ G2)) B.
  induction G1; intros.
  - inversion H.
  - inversion H; subst.
    + simpl.  u_left.
    + inversion_clear H0. rewrite <- app_comm_cons. simpl. u_right. 
Qed.



Lemma context_to_set_increases2 : forall G1 G2 B, In form (context_to_set G2) B -> In form (context_to_set (G1 ++ G2)) B.
  induction G1; intros.
  - rewrite app_nil_l. trivial.
  - apply IHG1 in H. rewrite <- app_comm_cons. simpl. u_left.
Qed.


Lemma context_to_set_dist: forall G1 G2 B, In form (context_to_set (G1 ++ G2)) B <->
                                           In form (context_to_set G1) B \/ In form (context_to_set G2) B.
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
      [H: In form (context_to_set (?G1 ++ ?G2)) ?B |- _ ] => apply context_to_set_dist in H; inversion H as [H1 | H1]
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



Lemma Singleton_eq : forall (U : Type) (x y : U), In U (Singleton x) y <-> x = y.
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

Lemma Incl_Union_l : forall (A B C: Ensemble form), Included (Union A B) C -> Included A C.
  unfold Included. intros.
  apply Union_introl with (C:=B) in H0.
  apply H in H0. trivial.
Qed.
  
Lemma Incl_Union_r : forall  (A B C: Ensemble form),  Included (Union A B) C -> Included B C.
  unfold Included. intros.
  apply Union_intror with (B:=A) in H0.
  apply H in H0. trivial.
Qed.


  
Lemma Included_refl: forall (A:Ensemble form), Included A A.
  unfold Included. intros. trivial.
Qed.


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



(*
(** ** Bounds as lists **)


(** *** Maximal bound with redundancies. *)
(** 
  Note that Ruitenburg's definition enforces non-emptiness 
  and presence of tt even when the formula is a
  propositional constant or a variable different from p. *)

Fixpoint mb_red (A : form) : list form :=
match A with
    | var i => [sub (s_p tt) (var i) ; tt]
    | B ->> C => sub (s_p tt) (B ->> C) :: (mb_red B ++ mb_red C)
    | B & C => (mb_red B ++ mb_red C)
    | B \v/ C => (mb_red B ++ mb_red C)
    | tt => [tt]
    | ff => [tt]
end.



    
Definition max_bound A := dup_rem (mb_red A).
    
(** Some example formulas *)


Definition exform1 := (q ->> p ->>r) & ((p ->> r) ->> p \v/ r).

(** [Compute mb_red exform1.]*)

(** wth substitution:
       [var 1 ->> tt ->> var 2; var 1; tt ->> var 2; tt; 
       var 2; (tt ->> var 2) ->> tt \v/ var 2; tt ->> var 2; tt; 
       var 2; tt; var 2] *)

(** w/o substitution:
       [var 1 ->> var 0 ->> var 2; var 1; var 0 ->> var 2; 
       var 0; var 2; (var 0 ->> var 2) ->> var 0 \v/ var 2; 
       var 0 ->> var 2; var 0; var 2; var 0; var 2] *)


(** [Compute max_bound exform1].*)


(** wth substitution:
       [var 1 ->> tt ->> var 2; var 1; (tt ->> var 2) ->> tt \v/ var 2;
       tt ->> var 2; tt; var 2] *)
   
(** w/o substitution:
      [var 1 ->> var 0 ->> var 2; var 1;
       (var 0 ->> var 2) ->> var 0 \v/ var 2; var 0 ->> var 2; 
       var 0; var 2] *)




Lemma mb_red_is_Bound :
  forall G A, Bound G A (context_to_set (mb_red A)).
Proof.
    unfold Bound. (* Sept 5: split.
  {
  induction A; intros; simpl in *; try (inversion H); try (inversion H0); subst; (*try (inversion_clear H);*)
               try (ctx_set Hnew;
                          try (apply IHA1 in Hnew); try (apply IHA2 in Hnew);
                          inversion_clear Hnew as [C [inC equivC]];
                          exists C; split; trivial; try solve [u_left]; try solve [u_right]);
               try solve [inversion H0; (*exists (A1 ->> A2).*) eexists; split; try solve [u_right];
                          try solve [u_left]; try solve [constructor];
                          simpl;  apply split_equiv; split; apply deriv_id].
  
(*  try (ctx_set Hnew); try apply IHA1 in Hnew; try apply IHA2 in Hnew;
  try (inversion_clear Hnew as [C [inC [equivC hipC]]]).*)
  (*try destruct (context_to_set_dist H0) as [H | H]; try apply IHA1 in *)
  - inversion H2.
  - inversion_clear H2. exists tt; split; try split.
           + u_right.
           + eauto.
(*             
           + intros. inversion_clear H; inversion_clear H0. simpl.
             destruct n.
             
             * exists tt. split. u_right.  simpl_spn.
             * exists (var (S n)). split; try simpl_spn. u_right.  
             * exists tt. split. u_left. u_right. simpl_spn.
*)
- destruct n. 
  + exists tt. split; try split.
           * u_right. 
           * simpl_spn.
(*             
           * intros. inversion_clear H; inversion_clear H0; exists tt; split; try simpl_spn.
             u_left. u_right.
             u_right. *)
 + exists (var (S n)). split; try split; try solve [simpl_spn]. u_left.
 (*                   
          intros.  inversion_clear H; inversion_clear H0.
          exists (var (S n)); split; try simpl_spn;
          try solve [u_right].
          exists tt; split; simpl_spn. u_left. u_right.
  *)
} Sept 5 *)
  induction A; simpl; intros; try (inversion H); try (inversion H0); subst;
  try (destruct (IHA1 _  H2) as [B [inB eqB]]); try (destruct (IHA2 _  H2) as [B [inB eqB]]);
  try (destruct (IHA1 _  H0) as [B [inB eqB]]); try (destruct (IHA2 _  H0) as [B [inB eqB]]); 
  try (exists B; split; trivial; try (u_left));
  try solve  [apply context_to_set_increases1; trivial];  try solve  [apply context_to_set_increases2; trivial].
  - destruct n.
    + exists tt. simpl_spn. split; eauto. u_right.
    + exists (var (S n)). simpl_spn. split; eauto. u_right.
 - exists tt.  split. u_left. u_right. simpl_spn.
 - inversion_clear H0; inversion_clear H; inversion_clear H0;
   exists (sub (s_p tt) (A1 ->> A2)); split;
            try u_right;
            apply split_equiv; split; apply deriv_id.
 - exists tt. split. u_right. simpl_spn.
 - exists tt; split; try u_right; simpl_spn.
 Qed.                 
(*
  unfold Bound.  split.
  {
    induction A; intros; simpl in *; try (inversion H); try (inversion H0); subst;
    try (inversion_clear H);
               try (ctx_set Hnew;
                          try (apply IHA1 in Hnew); try (apply IHA2 in Hnew);
                          inversion_clear Hnew as [C [inC equivC]];
                          exists C; split; trivial; try solve [u_left]; try solve [u_right]);
               try solve [inversion H0; (*exists (A1 ->> A2).*) eexists; split; try solve [u_right];
                          try solve [u_left]; try solve [constructor];
                          simpl;  apply split_equiv; split; apply deriv_id];
               try (inversion H2; subst);
               try solve [exists tt; split; try split; try solve [u_right]; try solve [simpl_spn]].
   -  
(*  try (ctx_set Hnew); try apply IHA1 in Hnew; try apply IHA2 in Hnew;
  try (inversion_clear Hnew as [C [inC [equivC hipC]]]).*)
    (*try destruct (context_to_set_dist H0) as [H | H]; try apply IHA1 in *)
    (*
    exists tt; split; try split.
           + tauto. 
           + eauto.*)
(*             
           + intros. inversion_clear H; inversion_clear H0. simpl.
             destruct n.
             
             * exists tt. split. u_right.  simpl_spn.
             * exists (var (S n)). split; try simpl_spn. u_right.  
             * exists tt. split. u_left. u_right. simpl_spn.
*)
    - destruct n; exists tt; split; try split; try solve [u_right]; try solve [simpl_spn].
    -   
(*             
           * intros. inversion_clear H; inversion_clear H0; exists tt; split; try simpl_spn.
             u_left. u_right.
             u_right. *)
   + exists (var (S n)). split; try split; try solve [simpl_spn].
                    
 (*                   
          intros.  inversion_clear H; inversion_clear H0.
          exists (var (S n)); split; try simpl_spn;
          try solve [u_right].
          exists tt; split; simpl_spn. u_left. u_right.
  *)
}
  induction A; simpl; intros; try (inversion H); try (inversion H0); subst;
  try (destruct (IHA1 _  H2) as [B [inB eqB]]); try (destruct (IHA2 _  H2) as [B [inB eqB]]);
  try (destruct (IHA1 _  H0) as [B [inB eqB]]); try (destruct (IHA2 _  H0) as [B [inB eqB]]); 
  try (exists B; split; trivial; try (u_left));
  try solve  [apply context_to_set_increases1; trivial];  try solve  [apply context_to_set_increases2; trivial].
  - destruct n.
    + exists tt. simpl_spn. split; eauto. u_right.
    + exists (var (S n)). simpl_spn. split; eauto. u_right.
 - exists tt.  split. u_left. u_right. simpl_spn.
 - inversion_clear H0; inversion_clear H; inversion_clear H0;
   exists (sub (s_p tt) (A1 ->> A2)); split;
            try u_right;
            apply split_equiv; split; apply deriv_id.
 - exists tt. split. u_right. simpl_spn.
 - exists tt; split; try u_right; simpl_spn.
 Qed.                  
*)


Lemma mb_red_is_ExactBound :
  forall G A, ExactBound G A (context_to_set (mb_red A)).
Proof.
  intros. split; try apply mb_red_is_Bound.
  induction A; intros; simpl in *; try (inversion H); try (inversion H0); subst; (*try (inversion_clear H);*)
               try (ctx_set Hnew;
                          try (apply IHA1 in Hnew); try (apply IHA2 in Hnew);
                          inversion_clear Hnew as [C [inC equivC]];
                          exists C; split; trivial; try solve [u_left]; try solve [u_right]);
               try solve [inversion H0; (*exists (A1 ->> A2).*) eexists; split; try solve [u_right];
                          try solve [u_left]; try solve [constructor];
                          simpl;  apply split_equiv; split; apply deriv_id].
  
(*  try (ctx_set Hnew); try apply IHA1 in Hnew; try apply IHA2 in Hnew;
  try (inversion_clear Hnew as [C [inC [equivC hipC]]]).*)
  (*try destruct (context_to_set_dist H0) as [H | H]; try apply IHA1 in *)
  - inversion H2.
  - inversion_clear H2. exists tt; split; try split.
           + u_right.
           + eauto.
(*             
           + intros. inversion_clear H; inversion_clear H0. simpl.
             destruct n.
             
             * exists tt. split. u_right.  simpl_spn.
             * exists (var (S n)). split; try simpl_spn. u_right.  
             * exists tt. split. u_left. u_right. simpl_spn.
*)
  - destruct n. 
    + exists tt. split; try split.
           * u_right. 
           * simpl_spn.
(*             
           * intros. inversion_clear H; inversion_clear H0; exists tt; split; try simpl_spn.
             u_left. u_right.
             u_right. *)
    + exists (var (S n)). split; try split; try solve [simpl_spn]. u_left.
 (*                   
          intros.  inversion_clear H; inversion_clear H0.
          exists (var (S n)); split; try simpl_spn;
          try solve [u_right].
          exists tt; split; simpl_spn. u_left. u_right. *)
Qed.  






Lemma  max_bound_is_Bound :
  forall G A, Bound G A (context_to_set (max_bound A)).
  unfold max_bound. intros. apply dup_rem_Bound. apply mb_red_is_Bound.
Qed.






(* 

Require Import List Ensembles.

Fixpoint list_to_set {A:Type} (l : list A) {struct l}: Ensemble A :=
  match l with
    | nil => Empty_set A
    | hd :: tl => Add A (list_to_set tl) hd
  end.


 forall A, Included (context_to_set (mb_red A)) (MaxBound A).
  unfold MaxBound, Included, In. 
  induction A;  simpl; intros B hip;
  unfold App; simpl;
  try (rewrite Im_add); try (inversion hip); subst;
  try (inversion H; subst; try (inversion H0; subst)).
  - u_right.
  - u_left. 
    rewrite subs_fresh_form.
    
Definition Bound (G: context) (A : form) (b : Ensemble form) :=
  forall B: form, In form b B <-> exists C, In form (MaxBound A) C /\ G |-- C <<->> B.
*)



(*

Definition SetForm := Coq.MSets.MSetList.Make form ...
*)
(*
Definition bound (b: Ensemble form) (p : Finite form b) (A : form) (G : context) :=
  Forall (fun C => Exists (fun B => G |-- sub (s_p tt) B <<->> sub (s_p tt) C) b) (mb_red A).
*)





(* ######################################## *)

(** *** Bounds as Lists *)


Definition bound (b: list form) (A : form) (G : context) :=
   Forall (fun C => Exists (fun B => G |-- sub (s_p tt) B <<->> sub (s_p tt) C) b) (mb_red A).

(*
Lemma bound_Bound : forall (b: list form) (A : form) (G : context), Bound G A (context_to_set b) ->
                                                                    bound b A G.
  unfold Bound, bound.
  assert (tt_in: forall n, In form (App tt (Singleton (var n))) tt) by (intros; u_right).
  assert (varn_in: forall n, In form (App tt (Singleton (var n))) (var n)) by (intros; u_left).
  induction A; simpl; intros; inversion H as [inL inR].
  -  constructor.
     + specialize (tt_in n). specialize (varn_in n).
       apply inR in tt_in. apply inR in varn_in.
       destruct n; simpl.
       * inversion tt_in as [B [ttBin ttBeq]]. Print Exists.
       *)





(** Ruitenburg : observe that ... [a bound] ... always exists *) 

(**
Lemma  max_bound_is_bound : forall G A, bound (max_bound A) A G.
Proof with eauto using dup_rem_incl, incl_dup_rem.
  unfold bound, max_bound. intro G. 
  induction A;  split; eauto; 
  try rewrite Forall_forall in *; 
  intros; try apply no_dup_rem.
  rewrite Exists_exists;
  try solve [ destruct (in_app_or _ _ _ H) as [inA | inA]; eauto].
  - inversion H as [H0 | [H1 | H2]].
    + subst. exists (s_p tt n); split...
    + subst. exists tt. simpl. eauto.
    + inversion H2.
  - inversion H.
    + subst. exists (sub (s_p tt) A1 ->> sub (s_p tt) A2).  simpl. eauto.
    + destruct (in_app_or _ _ _ H0) as [inA | inA]; eauto.
Defined.
 *)

Lemma upward_bound_for_bound : forall b b' A G, bound b A G -> incl b b' -> bound b' A G.
  unfold bound, incl. intros.  rewrite Forall_forall in *.  intros.
  apply H in H1.  rewrite Exists_exists in *.
  inversion H1 as [D [inb Gded]]. exists D. eauto.
Defined.

(** But there is also another obvious sense in which "bounds" are monotone. *)

Lemma bound_for_bound_upward : forall b A G G', bound b A G -> incl G G' -> bound b A G'.
Proof with eauto using Forall_forall.
  unfold bound.  
  intros. apply Forall_forall. intros.
  rename x into B.
  apply Exists_exists.
  (*rewrite Forall_forall in H. <-- it didn't work before I changed context from  "Definition" to "Notation".*)
  pose proof (Forall_forall  (fun C : form =>
                                Exists (fun B : form => G |-- sub (s_p tt) B  <<->> sub (s_p tt) C ) b) (mb_red A)) as [F1 F2].
  pose proof (F1 H B H1).
  apply Exists_exists in H2.
  destruct H2 as [C [HIn Hded]].
  exists C; split; trivial.
  eauto using hil_weaken_incl.
Defined.
  
  
Lemma set_bound_incl : forall A, incl (mb_red A) (max_bound A).
  unfold max_bound.  intro. apply dup_rem_incl.
Defined.

(*
Lemma set_bound_is_bound : forall G A, bound (max_bound A) A G.
  intros. eapply upward_bound_for_bound. apply mb_red_bound. apply set_bound_incl.
Defined.
*)

(** But we can do better than that! *)

Fixpoint t_optimize (A : form) : form :=
  match A with
    | tt ->> C => (t_optimize C)
    | C ->> tt => tt
    | B ->> C => (t_optimize B) ->> (t_optimize C)
    | B & tt => (t_optimize B)
    | tt & B => (t_optimize B)
    | B & C => (t_optimize B) & (t_optimize C)                  
    | B \v/ tt => tt
    | tt \v/ B => tt
    | B \v/ C => (t_optimize B) \v/ (t_optimize C)
    | B => B
  end.


Lemma t_optimize_correct : forall A G, G |-- A <<->> t_optimize A.
  induction A; intros.
  - simpl; eauto.
  - destruct (dceq_f tt A1); destruct (dceq_f tt A2); subst.
    + simpl; eauto.
    + simpl. apply eq_trans with (B := A2).
      * apply split_equiv. split; eauto.
      * trivial.
    + replace (t_optimize (A1 ->> tt)) with tt; eauto. 
      destruct A1; reflexivity.
    + replace (t_optimize (A1 ->> A2)) with (t_optimize A1 ->> t_optimize A2).
      * apply eq_impl_full; trivial.
      * destruct A1; simpl; destruct A2; simpl; try reflexivity;
        try (contradict n0; reflexivity);
        try (contradict n; reflexivity).
   -  destruct (dceq_f tt A1); destruct (dceq_f tt A2); 
      subst.
      + eauto.
      + apply eq_trans with (B := A2).
        * eauto.
        * replace (t_optimize (tt & A2)) with (t_optimize A2). trivial.
          destruct A2; try reflexivity.
      + apply eq_trans with (B := A1).
        * apply split_equiv. eauto.
        * replace (t_optimize (A1 & tt)) with (t_optimize A1). trivial.
          destruct A1; try reflexivity.
      + replace (t_optimize (A1 & A2)) with (t_optimize A1 & t_optimize A2).
        * apply equiv_congr_and; trivial.
        * destruct A1; simpl; destruct A2; simpl; try reflexivity;
        try (contradict n0; reflexivity);
        try (contradict n; reflexivity).
   - destruct (dceq_f tt A1); destruct (dceq_f tt A2); 
      subst.
      + eauto.
      + apply eq_trans with (B := tt).
        * eauto.
        * replace (t_optimize (tt \v/ A2)) with (t_optimize tt). trivial.
          destruct A2; try reflexivity.
      + apply eq_trans with (B := tt).
        * apply split_equiv. eauto.
        * replace (t_optimize (A1 \v/ tt)) with (t_optimize tt). simpl. trivial.
          destruct A1; try reflexivity.
      + replace (t_optimize (A1 \v/ A2)) with (t_optimize A1 \v/ t_optimize A2).
        * apply equiv_congr_or; trivial.
        * destruct A1; simpl; destruct A2; simpl; try reflexivity;
        try (contradict n0; reflexivity);
        try (contradict n; reflexivity).
   - simpl. eauto.
   - simpl. eauto.
Qed.



Lemma map_bound_for_bound : forall G A b (f : form -> form), (forall B, [] |-- B <<->> f B) -> bound b A G -> bound (map f b) A G.
  unfold bound. intros. rewrite Forall_forall in *.  intros.
  apply H0 in H1.  rewrite Exists_exists in *.
  inversion H1 as [D [inb Gded]]. exists (f D). split.
  - apply in_map. trivial.
  - apply eq_trans with (B := sub (s_p tt) D); try trivial.
    rewrite <- (app_nil_r G). apply hil_weaken_gen.
    (** Now logically one would do
      [replace (sub (s_p tt) (f D) <<->> sub (s_p tt) D) with (sub (s_p tt) (f D <<->> D)). replace []  with (ssub (s_p tt) [])]
      but some absurd error in Coq code produces "Error: Terms do not have convertible types". So instead I do roundabout... *)
    assert ((ssub (s_p tt) []) |-- sub (s_p tt) (f D <<->> D)).
    {
          eapply (hil_sub (s_p tt)). apply eq_sym. trivial.
    }
    simpl in H2. trivial.
Qed.


Lemma List_In_context_to_set : forall b A, List.In A b -> In form (context_to_set b) A.
  induction b; intros.
  - inversion H.
  - apply in_inv in H. inversion H.
    + subst. constructor 2. constructor.
    + constructor. apply IHb. trivial.
Qed.


Lemma context_to_set_List_In : forall b A, In form (context_to_set b) A ->  List.In A b.
  induction b; simpl; intros.
  - inversion H.
  - apply Union_inv in H. inversion H.
    + right. apply IHb. trivial.
    + inversion H0. subst. left. reflexivity.
Qed.

Lemma Bound_is_bound: forall G A b, Bound G A (context_to_set b) -> bound b A G.
  unfold Bound, bound.
  intros. rewrite Forall_forall.
  intros B hB.
  pose proof (List_In_context_to_set _ _ hB) as hB'.
  rewrite Exists_exists.
  pose proof (mb_red_is_ExactBound G A) as [hEx1 hEx2].
  destruct (hEx1 B hB') as [C [inC eqC]]. clear hEx1.
  destruct (H C inC) as [B' [inB' eqB']]. clear H.
  exists B'. split.
  - apply context_to_set_List_In. trivial.
  -  (** hm .. we want  G |-- B' {tt }/p <<->> B {tt }/p, but we only get G |-- B' <--> B! *)
     (** Things provable in a context are not closed under sbst. Consider
         ~p |-- (p ->  \bot) <-> \top ... *)


  
Definition basic_bound (A: form) := dup_rem (map t_optimize (mb_red A)).




Lemma basic_bound_is_bound : forall G A, bound (basic_bound A) A G.
  unfold basic_bound. intros.
  eapply upward_bound_for_bound. apply map_bound_for_bound.
  intros. apply t_optimize_correct. apply mb_red_bound.
  apply dup_rem_incl.
Defined.

(*Compute basic_bound exform1.*)
(* => [var 1 ->> var 2; var 1; var 2 ->> tt; var 2; tt] *)
(* whoa, this is funny... what [var 2 ->> tt] is doing here?? Compare with *)

(*Compute map t_optimize [var 1 ->> var 2; var 1; var 2 ->> tt; tt; var 2].*)
(* => [var 1 ->> var 2; var 1; tt; tt; var 2] *)

(*Compute mb_red exform1.*)
(* => [var 1 ->> tt ->> var 2; var 1; tt; tt ->> var 2; tt; tt; 
       var 2; tt; (tt ->> var 2) ->> tt \v/ var 2; 
       tt ->> var 2; tt; tt; var 2; tt; tt; tt; var 2; tt] *)

(*Compute map t_optimize (mb_red exform1).*)
(* => [var 1 ->> var 2; var 1; tt; var 2; tt; tt; 
       var 2; tt; var 2 ->> tt; var 2; tt; tt; var 2; tt; tt; tt; 
       var 2; tt] *)

(* ah, got that! the disputable formula arose from  (tt ->> var 2) ->> tt \v/ var 2 *)
(* one pass of [t_optimize] does not suffice to get optimal form *)

(* ############################################################# *)

(* ... and of course other simplifications are possible relative to a chosen G:
  for example, replacing occurrences of formulas from the context with top ... *)

(* One more property that could prove useful in what follows... *)

Lemma mb_red_nonempty : forall A, exists B, List.In B (mb_red A).
Proof.
  induction A; simpl; 
  try (eexists; tauto);
  try inversion IHA1;
  try inversion IHA2;
  eexists;
  try rewrite in_app_iff;
  eauto.
Defined.
  
Lemma bound_nonempty : forall b A G, bound b A G -> b <> [].
  unfold bound. unfold not. intros. subst. rewrite Forall_forall in H.
  destruct (mb_red_nonempty A).
  apply H in H0.
  eapply Exists_nil. eassumption.
Defined.



*)