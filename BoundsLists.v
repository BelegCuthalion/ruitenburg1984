(** * BoundsLists *)

(** This file is a part of Tadeusz Litak's formalisation of W. Ruitenburg JSL 1984 paper 
"On the Period of Sequences (An(p)) in Intuitionistic Propositional Calculus". *)

(** It has been compiled and guaranteed to work with
The Coq Proof Assistant, version 8.4pl6 (September 2015)
(compiled with OCaml 4.02.2) *)


(** ** Contents *)

(** This file, which is not used in the proof of crucial results (including Theorem 1.4) contains computational approach to bounds in terms of lists. *)

Require Export BoundsSubformulas.


(* ** Bounds as lists **)


(** ** Duplicate removal *)




(** An important function on lists ... *)





Fixpoint dup_rem (G : list form) : list form :=
  match G with
    | nil => nil
    | A :: G' =>  if (in_dec dceq_f A G') then dup_rem G' else A :: dup_rem G'
  end.


(** Basic facts about duplicate removals *)

Lemma dup_rem_incl : forall G, incl G (dup_rem G).
  unfold incl. induction G; simpl; intros; inversion H; subst;
    try (rename a0 into a);  destruct (in_dec dceq_f a); auto; simpl.
  - tauto.
  - auto.
Defined.

Lemma incl_dup_rem : forall G, incl (dup_rem G) G.
  unfold incl. induction G; simpl; intros.
  - apply H.
  - destruct (in_dec dceq_f a G); auto.
    inversion H; subst; auto.
Defined.


Lemma no_dup_rem : forall G, NoDup (dup_rem G).
  induction G; simpl; try constructor.
  destruct ( in_dec dceq_f a G); trivial.
  constructor; trivial.
  pose proof (incl_dup_rem G).
  intro. unfold incl in H.
  apply H in H0. contradiction.
Defined.





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








(*

Definition SetForm := Coq.MSets.MSetList.Make form ...
*)





(* ######################################## *)

(** *** Bounds as Lists *)


Definition bound (b: list form) (A : form) (G : context) :=
  Forall (fun C => Exists (fun B => G |--  B <<->>  C /\ [] |-- B <<->> sub (s_p tt) B) b) (mb_red A).
  

(*
Lemma bound_Bound : forall (b: list form) (A : form) (G : context), Bound G A (context_to_set b) ->
                                                                    bound b A G.
  unfold Bound, bound.
  assert (tt_in: forall n, In (App tt (Singleton (var n))) tt) by (intros; u_right).
  assert (varn_in: forall n, In (App tt (Singleton (var n))) (var n)) by (intros; u_left).
  induction A; simpl; intros; inversion H as [inL inR].
  -  constructor.
     + specialize (tt_in n). specialize (varn_in n).
       apply inR in tt_in. apply inR in varn_in.
       destruct n; simpl.
       * inversion tt_in as [B [ttBin ttBeq]]. Print Exists.
       *)





(** Ruitenburg : observe that ... [a bound] ... always exists *) 

(*
Lemma  max_bound_is_bound : forall G A, bound (max_bound A) A G.
Proof with eauto using dup_rem_incl, incl_dup_rem.
  unfold bound, max_bound. intro G. 
  induction A; try split; eauto; 
  try rewrite Forall_forall in *; 
  intros; try apply no_dup_rem.
  rewrite Exists_exists;
  try solve [ destruct (in_app_or _ _ _ H) as [inA | inA]; eauto].
  - inversion H as [H0 | [H1 | H2]].
    + subst. exists (sub (s_p tt) (var n)); split... apply dup_rem_incl in H. trivial. split. eauto. simpl. ???
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
Proof.
  unfold bound.  
  intros. rewrite Forall_forall in *. intros.
  rename x into B.
  specialize (H B H1).
  rewrite Exists_exists in *.
  destruct H as [C [hIn [heqv heql]]].
  exists C. split; try split; trivial;
  eapply hil_weaken_incl; eassumption.
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


Lemma t_optimize_correct_1 : forall A G, G |-- A <<->> t_optimize A.
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



Lemma t_optimize_correct_2 : forall B, [] |-- B <<->> sub (s_p tt) B -> [] |-- (t_optimize B) <<->> (sub (s_p tt) (t_optimize B)).
  intros.
  pose proof (t_optimize_correct_1 B []) as eq1.
  pose proof (eq_trans _ _ _ _ (eq_sym _ _ _ eq1) H) as eq2.
  apply (hil_sub_equiv (s_p tt)) in eq1; simpl in eq1.
  eapply eq_trans. apply eq2. apply eq1.
Qed.
  
    
Lemma map_bound_for_bound : forall G A b (f : form -> form), (forall B, [] |-- (B <<->> f B)) -> (forall B, [] |-- B <<->> sub (s_p tt) B -> [] |-- (f B) <<->> (sub (s_p tt) (f B))) -> bound b A G -> bound (map f b) A G.
  unfold bound. intros. rewrite Forall_forall in *.  intros.
  apply H1 in H2.  rewrite Exists_exists in *.
  inversion H2 as [D [inb Gded]].
  exists (f D). split.
  - apply in_map. trivial.
  - destruct Gded as [Gdr Gdl]. split.
    + apply eq_trans with (B := D); try trivial.
      apply eq_sym. eapply hil_weaken_incl. apply H.
      unfold incl. intros. inversion H3.
    + apply H0. (*eapply hil_weaken_incl. apply Gdl.
      unfold incl. intros.*) assumption.
Qed.


Lemma List_In_context_to_set : forall b A, List.In A b -> In (context_to_set b) A.
  induction b; intros.
  - inversion H.
  - apply in_inv in H. inversion H.
    + subst. constructor 2. constructor.
    + constructor. apply IHb. trivial.
Qed.


Lemma context_to_set_List_In : forall b A, In (context_to_set b) A ->  List.In A b.
  induction b; simpl; intros.
  - inversion H.
  - apply Union_inv in H. inversion H.
    + right. apply IHb. trivial.
    + inversion H0. subst. left. reflexivity.
Qed.


Lemma mb_red_subst: forall A B, List.In B (mb_red A) -> B = sub (s_p tt) B.
  intros. induction A; simpl in H;
          try (rewrite in_app_iff in H);
          try (inversion H; subst; auto; inversion H0).
  - inversion_clear H as [H' | [H' | H']]; subst; try reflexivity.
    + unfold s_p. unfold s_n. destruct n; simpl; reflexivity.
    + inversion H'.
  - inversion_clear H as [H' | [H' | H']]; subst; simpl.
    + rewrite subs_fresh_form with (A := sub (s_p tt) A1).
      *
      {
        rewrite subs_fresh_form with (A := sub (s_p tt) A2).
        - reflexivity.
        - intros. destruct n.
          + contradict H. apply freshness_s_p. constructor.
          + reflexivity.
      }
      *
      {
        intros. destruct n.
        - contradict H. apply freshness_s_p. constructor.
        - reflexivity.
      }
    + auto.
    + auto.
Qed.




Lemma Bound_mb_red : forall A B, In (BoundSubformulas A) B -> List.In (sub (s_p tt) B) (mb_red A).
  induction A; simpl; intros; try (apply Union_inv in H); try solve [intuition].
  - inversion_clear H; inversion_clear H0; unfold s_p.
    + destruct n; simpl; intuition.
    + simpl. intuition.
  - inversion_clear H.
    + apply Union_inv in H0. rewrite in_app_iff. intuition.
    + inversion_clear H0. intuition.
  - inversion_clear H. simpl. intuition.
  - inversion_clear H. simpl. intuition.
 Qed.
 

Lemma bound_is_Bound : forall b A G, bound b A G -> Bound G A (context_to_set b).
  unfold bound, Bound. intros.
  apply Bound_mb_red in H0.
  rewrite Forall_forall in H.
  specialize (H _ H0).
  rewrite Exists_exists in H.
  destruct H as [B [lIn [eqv eql]]].
  exists B. split.
  - apply List_In_context_to_set. assumption.
  - apply eq_sym. assumption.
Qed.


Lemma mb_red_is_bound : forall A, bound (mb_red A) A [].
  unfold bound. intro.
  rewrite Forall_forall.
  intros.
  rename x into B.
  rewrite Exists_exists.
  exists B. intuition.
  - eauto.
  - rewrite <- mb_red_subst with (A := A) (B:=B); eauto.
Qed.






(** ... the lemma below can be now more easily obtained as a corollary ... *)

Lemma mb_red_is_Bound :
  forall G A, Bound G A (context_to_set (mb_red A)).
Proof.
  intros.
  apply bound_is_Bound.
  eapply  bound_for_bound_upward.
  apply mb_red_is_bound.
  unfold incl. intros. inversion H.
 Qed.                 


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
  - inversion H2.
  - inversion_clear H2. exists tt; split; try split.
           + u_right.
           + eauto.
  - destruct n. 
    + exists tt. split; try split.
           * u_right. 
           * simpl_spn.
    + exists (var (S n)). split; try split; try solve [simpl_spn]. u_left.
Qed.  





(*
Lemma  max_bound_is_Bound :
  forall G A, Bound G A (context_to_set (max_bound A)).
  unfold max_bound. intros. apply dup_rem_Bound. apply mb_red_is_Bound.
Qed.
*)



(*
Lemma Bound_is_bound: forall G A b, ExactBound G A (context_to_set b) -> bound b A G.
  unfold ExactBound, Bound, bound.
  intros. rewrite Forall_forall.
  intros B hB.
  pose proof (List_In_context_to_set _ _ hB) as hB'.
  rewrite Exists_exists.
  pose proof (mb_red_is_ExactBound G A) as [hEx1 hEx2].
  destruct (hEx1 B hB') as [C [inC eqC]]. clear hEx1.
  destruct H as [Hl Hr].
  destruct (Hr C inC) as [B' [inB' eqB']]. clear Hr.
  destruct (Hl _ inB') as [C' [inC' eqC']].
  (*rewrite (mb_red_subst A B) in eqC.*)
  exists B'. split; try split.
  - apply context_to_set_List_In. trivial.
  - eapply eq_trans. apply eq_sym. apply eqB'. apply eqC.
  - ??? *)
    



(**  ** Finiteness and cardinality *)


Lemma Finite_context_to_set : forall b, Finite form (context_to_set b).
  induction b; simpl.
  - constructor.
  - apply Add_preserves_Finite. assumption.
Qed.

Lemma cardinal_context_to_set : forall b n, cardinal (context_to_set b) n -> n <= length b.
  induction b; simpl; intros.
  - inversion H. omega. contradict H0. apply Add_not_Empty.
  - destruct (finite_cardinal _ _  (Finite_context_to_set b)) as [n' Hn'].
    specialize (IHb n' Hn').
    pose proof (card_Add_gen _ _ _ _ _ Hn' H).
    omega.
Qed.


(*
Lemma bound_Bound_Inc : forall b A G n, bound b A G -> n = length b ->
                                    exists B, Included (context_to_set b) B /\ Bound G A B /\ cardinal B n.
  intros. 
  pose proof (bound_is_Bound _ _ _ H) as HbB.
  destruct (finite_cardinal _ _  (Finite_context_to_set b)) as [n' Hn'].
  pose proof (cardinal_context_to_set _ _ Hn').
*)  


Definition basic_bound (A: form) := dup_rem (map t_optimize (mb_red A)).




Lemma basic_bound_is_bound : forall G A, bound (basic_bound A) A G.
  unfold basic_bound. intros.
  eapply upward_bound_for_bound; try apply dup_rem_incl.
  apply map_bound_for_bound; intros.
  apply t_optimize_correct_1.
  apply t_optimize_correct_2. assumption.
  eapply bound_for_bound_upward.
  apply mb_red_is_bound.
  unfold incl. intros B H. inversion H.
Defined.




(*
Compute basic_bound exform1.
(* => [var 1 ->> var 2; var 1; var 2 ->> tt; var 2; tt] *)
(* You may ask what [var 2 ->> tt] is doing here? Compare with *)

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

(* As one can guess, the disputable formula arose from  (tt ->> var 2) ->> tt \v/ var 2 *)
(* one pass of [t_optimize] does not suffice to get optimal form *)
*)


(** Let us improve on this then ... *)


Fixpoint frm_dep (A : form) : nat :=
  match A with
    | var n => 0
    | B ->> C => (max (frm_dep B) (frm_dep C)) + 1
    | B & C => (max (frm_dep B) (frm_dep C)) + 1
    | B \v/ C => (max (frm_dep B) (frm_dep C)) + 1
    | tt => 0
    | ff => 0
  end.

(*
Compute frm_dep exform1.
*)


Fixpoint iterator (n : nat) : forall X : Type, (X -> X) -> X -> X :=
  match n with
    | 0 => fun (X : Type) (f : X -> X) => f 
    | S n' => fun X f x => f ((iterator n') X f x)                                         
  end.     


(*
Fixpoint iterator_form (n : nat) : (form -> context) -> form -> context :=
  match n with
    | 0 => fun f A => f A
    | S n' => fun f A => map f ((iterator_form n') f A)                                         
  end. 
*)


Definition optimized_bound_param (A : form) (n : nat) :=  dup_rem (map (iterator n _ t_optimize) (mb_red A)).

Definition optimized_bound (A : form) :=  optimized_bound_param A (frm_dep A).
                                            
(*
Compute optimized_bound exform1.
(* => [var 1 ->> var 2; var 1; var 2; tt] *)
*)


Lemma optimized_bound_param_is_bound : forall G A n,  bound (optimized_bound_param A n) A G.
  unfold optimized_bound_param.
  induction n; intros ; simpl. 
  - apply basic_bound_is_bound.
  - unfold bound in *. rewrite Forall_forall in *.
    intros C H. apply IHn in H. clear IHn. rewrite Exists_exists in *.
    destruct H as [B [inB eqB]].
    exists (t_optimize B).
    destruct eqB as [BC Btt].
    split; try split.
    + apply dup_rem_incl.  apply incl_dup_rem in inB. rewrite in_map_iff in *.
      destruct inB as [B' [itB' inB']]. exists B'. split; trivial.
      rewrite itB'. reflexivity.
    + eapply eq_trans. apply eq_sym. apply t_optimize_correct_1. assumption.
    + apply t_optimize_correct_2. assumption.
Defined.


Lemma optimized_bound_is_bound : forall G A,  bound (optimized_bound A) A G.
  intros. apply optimized_bound_param_is_bound.
Defined.

(* ############################################################# *)

(* ... and of course other simplifications are possible relative to a chosen G:
  for example, replacing occurrences of formulas from the context with top ... *)



(* ############################################################# *)

(** ** Checking the size of f_p *)

(** Computing f_p can get very expensive. Here is a function that allows to estimate its size. *)

Fixpoint frm_len (A : form) : nat :=
  match A with
    | var n => 1
    | B ->> C => (frm_len B) + (frm_len C) + 1
    | B & C => (frm_len B) + (frm_len C) + 1
    | B \v/ C => (frm_len B) + (frm_len C) + 1
    | tt => 1
    | ff => 1
  end.


Fixpoint p_occ (A : form) : nat :=
  match A with
    | var n => match n with
                 | 0 => 1
                 | S n' => 0
                end
    | B ->> C => (p_occ B) + (p_occ C) 
    | B & C => (p_occ B) + (p_occ C) 
    | B \v/ C => (p_occ B) + (p_occ C)
    | tt => 0
    | ff => 0
  end.

Lemma pocc_shorter_length : forall A, p_occ A <= frm_len A.
  induction A; try (simpl; omega).
  destruct n; simpl; omega.
Qed.

  

Lemma length_subst : forall A B, 
                       frm_len (sub (s_p B) A) = p_occ A * (frm_len B) + frm_len A - p_occ A.
  induction A; simpl;
  try
    ( intros; rewrite IHA1, IHA2; rewrite mult_plus_distr_r;
    pose proof (pocc_shorter_length A1); pose proof (pocc_shorter_length A2);
    remember (p_occ A1 * frm_len B) as A1B;
    remember ( p_occ A2 * frm_len B) as A2B; 
    do 2 (rewrite NPeano.Nat.add_assoc; omega));
    try (intros; reflexivity). 
  - unfold s_p. unfold s_n. destruct n; simpl; intros; omega.
Qed.    

Lemma p_occ_subst : forall A B, 
                      p_occ (sub (s_p B) A) = p_occ A * p_occ B.
  induction A; intros;
  try (simpl; rewrite IHA1, IHA2;  rewrite mult_plus_distr_r; omega);
  try reflexivity.  
  - unfold s_p. unfold s_n. destruct n; simpl; intros; omega.
Qed.
   


Fixpoint length_of_f_p (A : form) (n : nat) :=
  match n with
    | 0 => (1,1)
    | S n' => let (l,o) := (length_of_f_p A n') in
              let pA := (p_occ A) in
              (pA * l + (frm_len A) - pA, pA * o)
  end.




Lemma length_of_f_p_correct : forall A n, let (len,occ) := (length_of_f_p A n) in frm_len (f_p A n) = len /\  p_occ (f_p A n) = occ.
Proof.
  induction n; simpl.
  - tauto.
  -  rewrite length_subst, p_occ_subst; simpl.
     destruct (length_of_f_p A n) as (len', occ').
     destruct IHn as [eql eqr]. rewrite eql, eqr.
     tauto.
Qed.