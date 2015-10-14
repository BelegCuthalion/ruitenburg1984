(** * Ruitenburg1984Aux *)


(** This file is a part of Tadeusz Litak's formalisation of W. Ruitenburg JSL 1984 paper 
"On the Period of Sequences (An(p)) in Intuitionistic Propositional Calculus" *)

(** It has been compiled and guaranteed to work with
The Coq Proof Assistant, version 8.4pl6 (September 2015)
(compiled  with OCaml 4.02.2) *)



(** ** Contents *)

(** This file  contains auxiliary lemmas of Ruitenburg's paper other than 1.2,
namely,  1.6, 1.7 and 1.8.

They do not require  the IPC-specific construction of bounds
and would hold in extensions of IPC where [ded_subst] and [ded_subst_gen]
remain valid.

*)


Require Export HilbertIPCsetup.


(* ############################################## *)
(* ################################################# *)

(** ** Lemmma 1.6. *)


(* ############################################### *)


Lemma rui_1_6 : forall A m, (forall i, [f_p A i ; sub (s_p tt) A] |-- f_p A m) ->
                            [sub (s_p tt) A] |-- f_p A m <<->> f_p A (m+1).
  intros. apply split_equiv; split.
  - apply hil_ded. apply rui_1_2_i.
  - auto.
Defined.


(* ################################################################# *)

(** ** Lemma 1.7 *)

(* ################################################################# *)

(** Ruitenburg is often using a phrase "use substitution", especially in steps marked by hash 
    in Lemmas 1.7 and Lemma 1.8. Here is a lemma generalising some of this reasoning. *)

Lemma generalizing_some_hash_steps : forall A m k, [f_p A m] |-- f_p A (m + k) <<->> sub (s_p tt) (f_p A k).
Proof.
  induction k.
  - simpl. om (m + 0)  m. apply ded_tt1. simpl. tauto.
  - replace (f_p A (m + S k)) with (sub (s_p (f_p A (m + k))) A).
    replace (sub (s_p tt) (f_p A (S k))) with (sub (s_p (sub (s_p tt) (f_p A k))) A).
    apply ded_subst. assumption.
    simpl. rewrite interaction_sub_s_p1. reflexivity.
    destruct k.
    + om (m + 0) m. rewrite <- f_p_unfold_gen. rewrite f_p_one.
      reflexivity.
    + rewrite  <- f_p_unfold_gen.  om (m + S (S  k)) (m + S k + 1).
      rewrite  <- f_p_unfold_gen. rewrite f_p_one. rewrite f_p_unfold_gen.
      reflexivity.
Defined.




(** The lemma below is a generalization of a step marked  * in the proof of Lemma 1.7 (i) *)

Lemma star_step_rui_1_7 : forall A m, [ sub (s_p tt) (f_p A m) ; sub (s_p tt) (f_p A (m + 1))] |--  sub (s_p tt) A.
  intros. eapply ded_equiv.
  - apply (ded_subst _ _ (sub (s_p tt) (f_p A m))). apply ded_tt1; simpl; tauto.
  - replace (sub (s_p (sub (s_p tt) (f_p A m))) A) with (sub (s_p tt) (f_p A (m + 1))). hilst_auto.
    om (m + 1)  (S m). simpl. apply  interaction_sub_s_p2.
Defined.
 
  
(** The lemma below is used several times in Lemma 1.7.
   It is a corollary of Lemma 1.2(i) which is at the same time a key ingredient of
   the "hash step" below. *)

Lemma hash_substep_rui_1_7 : forall m A, [sub (s_p tt) A] |-- sub (s_p tt) (f_p A m).
Proof.
  intros.
  eapply hil_permute.
    - instantiate (1:= ssub (s_p tt) [f_p A 1; sub (s_p tt) A]).
      destruct m.
      + simpl. auto.
      + apply hil_sub.  apply rui_1_2_i.
    - simpl. rewrite sub_s_p_trivial0.  rewrite subs_fresh_form with (A:=(sub (s_p tt) A)).
      tauto. intros.
      destruct (eq_nat_dec 0 n); subst; auto.
      intros. contradict H. 
      apply freshness_s_p; auto.
Defined.






Lemma hash_substep_rui_1_7_G : forall G m A, G |-- sub (s_p tt) A ->> sub (s_p tt) (f_p A m).
Proof.
  intros. 
  apply hil_ded. apply hil_cut with (A := (sub (s_p tt) A)).
  hilst_auto.
  apply hash_substep_rui_1_7.
Defined.



(** The lemma below is a generalization of a step marked  with hash in the proof of Lemma 1.7 (i) *)

Lemma hash_step_rui_1_7 : forall A m, [ sub (s_p tt) (f_p A (m + 1))] |-- sub (s_p tt) (f_p A m) <<->> sub (s_p tt) A .
  intros. apply split_equiv. split.
  - apply hil_ded. apply star_step_rui_1_7.
  - apply hil_ded. replace ([sub (s_p tt) A; sub (s_p tt) (f_p A (m + 1))]) with
                   (rev [sub (s_p tt) (f_p A (m + 1)); sub (s_p tt) A]); auto.
    eapply hil_permute; [apply hil_weaken | apply in_rev].
    apply hash_substep_rui_1_7.
Defined.

Lemma hash_step_rui_1_7_subst : forall A m, [ sub (s_p tt) (f_p A (m + 1))] |-- sub (s_p tt) (f_p A 2).
  intros. eapply ded_equiv; try hilst_auto.
  rewrite interaction_sub_s_p2.
  om (m + 1) (S m). 
  rewrite interaction_sub_s_p2.
  apply ded_subst. rewrite <- f_p_1.
  rewrite <- interaction_sub_s_p2.
  om (S m)  (m + 1). 
  apply hash_step_rui_1_7.
Defined.


    
(** So far, so good. But now we are reaching rather strange place in proof of Lemma 1.7 (i), that 
 is not sufficiently explained in the paper. Its counterpart in (ii) is marked with dollar sign, but no such explanation
 accompanies the step in (i) and it seems far from trivial. In the end, the best one can do
 is to provide a suitable variant of Lemma 1.2(i), which is not exactly a corollary : and then 
 use it to provide a suitable instance with top substitution. *)




Lemma rui_1_2_i_variant2 : forall A i k, [f_p A  i ; sub (s_p tt) (f_p A 2)] |-- f_p A (i +  2 * k).
  induction k.
  - om (i + 2 * 0) i.
    hilst_auto. 
  - om (i + 2 * (S k)) ((i + 2 * k) + 2).
    eapply ded_equiv.
    * rewrite <- f_p_unfold_gen.
      apply ded_subst.
      instantiate (1 := tt).
      apply ded_tt2gen; trivial.
    *  hilst_auto.
Defined.

(** We can use this for a similar purposed that 1.2(i) was used in "hash substep" *)




Lemma hash_substep_rui_1_7variant2 : forall m A, [sub (s_p tt) (f_p A 2)] |-- sub (s_p tt) (f_p A (2 * m)).
Proof.
  intros.
  eapply hil_permute.
    - instantiate (1:= ssub (s_p tt) [f_p A 2; sub (s_p tt)  (f_p A 2)]).
      destruct m.
      + simpl. auto.
      + apply hil_sub.  om (2 * S m) (2 + 2*m).
        apply rui_1_2_i_variant2.
    - simpl. rewrite sub_s_p_trivial0.
      rewrite subs_fresh_form with (A:=(sub (s_p tt) (sub (s_p A) A))).
      tauto. intros.
      destruct (eq_nat_dec 0 n); subst; auto.
      intros. contradict H. 
      apply freshness_s_p; auto.
Defined.



Lemma hash_substep_rui_1_7variant2_G : forall G m A, G |-- sub (s_p tt) (f_p A 2) ->> sub (s_p tt) (f_p A (2 * m)).
Proof.
  intros. 
  apply hil_ded. apply hil_cut with (A := (sub (s_p tt) (f_p A 2))).
  hilst_auto.
  apply hash_substep_rui_1_7variant2.
Defined.







Lemma rui_1_7_i :  forall A m n, [ sub (s_p tt) (f_p A (2*m + 1))] |--  sub (s_p tt) (f_p A n).
  intros. eapply hilMP; try apply hash_substep_rui_1_7_G. 
  eapply ded_equiv.  apply hash_step_rui_1_7.
  eapply hil_cut. apply hash_step_rui_1_7_subst.
  apply  hash_substep_rui_1_7variant2.
Defined.


(** Ruitenburg's observation: "with Lemma 1.7 we can prove theorems like ... " *)

Corollary cycle_variable_free : forall A, [] |-- sub (s_p tt) A <<->> sub (s_p tt) (f_p A 3).
Proof.
  intros. apply split_equiv; split.
  - apply hil_ded. rewrite (f_p_1 A) at 1.
    om 1 (2*0 + 1).
    apply rui_1_7_i.
  - apply hil_ded.  rewrite (f_p_1 A) at 2.
    om 3 (2*1 + 1).
    apply rui_1_7_i.
Defined.    

(**  As it turns out, we only needed Lemma 1.7 for the above corollary.
     More corollaries possible along this line ... *) 

Corollary cycle_variable_free2 : forall A, [] |-- sub (s_p tt) (f_p A 2) <<->> sub (s_p tt) (f_p A 4).
Proof.
  intros. rewrite (interaction_sub_s_p2 1).
  rewrite (interaction_sub_s_p2 3).
  apply ded_subst.
  rewrite <- f_p_1.
  apply cycle_variable_free.
Defined.

(** There is a general form. *)


 
Corollary cycle_variable_free_gen : forall A k n, [] |-- sub (s_p tt) (f_p A (S n)) <<->> sub (s_p tt) (f_p A ((S n) + 2*k)).
Proof.
  induction k.
  - intros. simpl. om (n+0) n. eauto.
  - induction n.
    + apply eq_trans with (B :=  sub (s_p tt) (f_p A (1 + 2 * k))).
      * apply IHk.
      * replace (sub (s_p tt) (f_p A (1 + 2 * k))) with (sub (s_p (sub (s_p tt) A)) (f_p A (2 * k))).
        replace (sub (s_p tt) (f_p A (1 + 2 * S k))) with (sub (s_p (sub (s_p tt) (f_p A 3))) (f_p A (2 * k))).
        apply ded_subst.
        apply cycle_variable_free.
        om (1 + 2 * S k) (2 *  k + 3).
        apply f_p_unfold_subst.
        om (1 + 2 * k) (2 * k + 1).
        rewrite (f_p_1 A) at 1.
        apply f_p_unfold_subst.
    + replace (sub (s_p tt) (f_p A (S (S n)))) with (sub (s_p (sub (s_p tt) (f_p A (S n)))) A).
      replace (sub (s_p tt) (f_p A  (S (S n) + 2 * S k))) with (sub (s_p (sub (s_p tt) (f_p A (S n + 2 * S k)))) A).
      apply ded_subst. assumption.
      rewrite (f_p_1 A) at 2.
      om (S (S n) + 2 * S k) (1 + ((S n) + 2 * S k)).
      apply f_p_unfold_subst.
      om (S (S n)) (1 + (S n)).
      rewrite (f_p_1 A) at 2.
      apply f_p_unfold_subst.
Defined.
      
(** In Ruitenburg's version, the second part of 1.7 was slightly more tricky.
    "Observe that 1.7ii) is not an easy corollary of 1.7i)".
     Here is a formalization of his original proof... *) 

Lemma rui_1_7_ii :  forall A m n, [ sub (s_p tt) (f_p A (2*m + 2))] |--  sub (s_p tt) (f_p A (2 *n)).
  intros.  eapply hilMP; try apply hash_substep_rui_1_7variant2_G.
  apply ded_equiv with (A := (sub (s_p (sub (s_p tt) (f_p A (2* m + 1)))) A)). (*A := (sub (s_p (sub (s_p (sub (s_p tt) (f_p A (2* m)))) A)) A)*)
  - replace (sub (s_p tt) (f_p A 2)) with (sub (s_p (sub (s_p tt) A)) A).
    + apply ded_subst. om (2 * m + 2) (2 * m + 1 + 1). apply hash_step_rui_1_7.
    + rewrite (f_p_1 A) at 1. 
      repeat (rewrite interaction_sub_s_p2).
      reflexivity.
  - om (2 * m + 2) (S(2*m + 1)).
    rewrite <- interaction_sub_s_p2.
    hilst_auto.
Defined.

(* However, with our new powerful corollary of Lemma 1.7(i) we can actually derive 1.7(ii)! 
or can we ... *)
Lemma rui_1_7_ii' :  forall A m n, [ sub (s_p tt) (f_p A (2*m + 2))] |--  sub (s_p tt) (f_p A (2 *n)).
Proof.
  intros.
  destruct (le_le_S_dec (m + 1)  n);
    destruct (NPeano.Nat.le_exists_sub _ _ l) as [k [Hk _]]. (* rewrite Hk. *)
  - rewrite Hk.
    om (2 * (k + (m + 1))) (2 * m + 2 + 2 * k).
    destruct k.
    + om (2 * m + 2 + 2 * 0) (2 * m + 2). hilst_auto.
    + om (2 * m + 2) (S(2*m + 1)). apply hil_ded_conv. apply equiv_to_impl.
      apply  cycle_variable_free_gen.
  - om (2 * m + 2) (2 * (m + 1)). rewrite Hk.
    om (2 * (k + S n)) (2 * n + 2 * k + 2).
    destruct n.
    + simpl. unfold s_p. simpl.
      rewrite s_n_triv. auto.
    + om  (2 * S n + 2 * k + 2)  (S (2 * n + 1) + 2 * (k + 1)).
      apply hil_ded_conv. apply equiv_to_impl. apply eq_sym.
      om (2 * S n) (S (2 * n + 1)).
      apply  cycle_variable_free_gen.
Qed.

(* ############################################## *)

(** ** Lemma 1.8 *)


(* ############################################## *)


(** Ruitenburg: "Observe that [*] is equivalent to..." *)

Lemma star_equivalent_rui_1_8 : forall A m, [sub (s_p tt) A] |--  (f_p A m)  <<->>  (f_p A (m + 1)) <->
                                            forall k, [sub (s_p tt) A] |--  (f_p A m)  <<->>  (f_p A (m + k) ).
Proof.
  intros. split; intros; trivial.
  induction k.
    - om (m + 0)  m. eauto.
    - apply eq_trans with (B := (f_p A (m + 1))); trivial.
      replace (f_p A (m + 1)) with (sub (s_p (f_p A m)) A).
      replace (f_p A (m + S k)) with (sub (s_p (f_p A (m + k))) A).
      apply ded_subst; trivial.
      om (m + S k) (S(m + k)). apply f_p_unfold.
      om (m + 1) (S m). apply f_p_unfold.
Defined.




    

Lemma rui_1_8_first_half_1 : forall A m, (*[sub (s_p tt) A] |--  (f_p A m)  <<->>  (f_p A (m + 1)) ->*)
                                         [f_p A (m+1); f_p A m] |-- f_p A (m + 2).
Proof.
  intros. (*replace ([f_p A (m+1); f_p A m]) with (rev [f_p A m; f_p A (m+1)]).
  apply hil_rev.
  replace ( [f_p A m; f_p A (m + 1)]) with ([f_p A m] ++ [f_p A (m + 1)]); try reflexivity.*) 
  apply hilMP with (A := (sub (s_p tt) A)).
  (*forall (A : form) (i k : nat), [f_p A i; sub (s_p tt) A] |-- f_p A (i + k)*)
  - (*rewrite <- rev_involutive with (A :=  ([f_p A (m+1); f_p A m])).
    Hah! I got a genuine Coq error: "Anomaly: type_of: Not an arity. Please report."*)
    replace ([f_p A (m+1); f_p A m]) with (rev [f_p A m; f_p A (m+1)]); try reflexivity .
    apply hil_rev. apply hil_weaken.
    apply hil_ded.
    replace ([sub (s_p tt) A; f_p A (m + 1)]) with (rev [ f_p A (m + 1); sub (s_p tt) A]);
    try reflexivity.
    apply hil_rev. replace (m + 2) with (m + 1 + 1); try omega.
    apply rui_1_2_i.  (** Note that Ruitenburg's comment "use substitution"  is rather unhelpful here *)
  - apply hil_ded_conv.
    eapply hilMP. apply hilC2.
    om (m + 1) (S m).
    rewrite <- f_p_unfold.
    apply ded_subst. apply ded_tt1; simpl; tauto.
Defined.





                                                       
(** Note Ruitenburg's use of "(2)"  in the proof below is rather confusing. *)

Lemma rui_1_8_first_half_3 : forall A m, [sub (s_p tt) A] |--  (f_p A m)  <<->>  (f_p A (m + 1)) ->
                                         (*[f_p A (m + 2)] |-- f_p A m*)
                                         [f_p A (m + 1)] |--  f_p A (m + 2) ->> f_p A m.              
Proof.
  intros.
  (*apply hilMP with (A :=  (f_p A (m + 1))).
  -*) apply hil_ded.
    apply hilMP with (A :=  (f_p A (m + 1))).
    +  apply hil_cut with (A := (sub (s_p tt) A)).
       * (*(*apply hil_weaken.*) rev_goal. simpl.*)
         apply hil_ded_conv.
         apply equiv_to_impl. rewrite <- (f_p_one A) at 3.
         rewrite <- (f_p_one A) at 4.
         om (m + 2)  (m + 1 + 1). 
         apply generalizing_some_hash_steps. 
       * eauto.
    + hilst_auto.
Defined.
    
      
Lemma rui_1_8_first_half : forall A m, [sub (s_p tt) A] |--  (f_p A m)  <<->>  (f_p A (m + 1)) ->
                                       [f_p A (m+1)] |--  f_p A (m + 3).
Proof.
  intros. apply ded_equiv with (A := f_p A (m + 1)); try  hilst_auto.
  om (m + 3) ((m + 2) + 1).
  rewrite <- f_p_unfold_gen at 2.
  rewrite <- f_p_unfold_gen at 2.
  rewrite <- (f_p_unfold_gen _ (m + 2)).
  apply ded_subst.
  apply split_equiv; split.
  -  apply hil_ded. rev_goal. 
     apply rui_1_8_first_half_1.
  -  apply rui_1_8_first_half_3; assumption.
Defined.



  
Lemma rui_1_8_second_half_3 : forall A m, [f_p A (m + 3)] |-- (f_p A m) ->> (f_p A (m + 2)).
Proof.
  intros.
  apply hil_ded.
  apply hilMP with (A := (sub (s_p tt) (f_p A 2))).
  - apply equiv_to_impl. rev_goal. apply hil_weaken.
    rewrite <- f_p_unfold_gen.
    apply ded_subst.
    apply ded_tt2. simpl; tauto.
  - apply hil_cut with (A := (sub (s_p tt) (f_p A 3))).
    + rev_goal. apply hil_ded_conv. apply equiv_to_impl.
      (*replace m with (m + 0) at 1; try omega.*)
      apply generalizing_some_hash_steps. (** Ruitenburg's "use substitution" again... *)
    + om 3  (2 + 1).
      apply hash_step_rui_1_7_subst. (** Note we need just this, rather than full Lemma 1.7 ... *)
Defined.


Lemma rui_1_8_second_half_2 :  forall A m, [sub (s_p tt) A] |--  (f_p A m)  <<->>  (f_p A (m + 1)) ->
                                           [f_p A (m + 3)] |-- (f_p A (m + 2)) ->>  (f_p A m).
Proof.
  intros. apply hil_ded.
  rewrite star_equivalent_rui_1_8 in H.
  apply hilMP with (A := (sub (s_p tt) A)).
  - apply hil_ded. apply ded_equiv with (A := (f_p A (m + 2))).
    + rev_goal. apply hil_weaken. apply hil_weaken.
      apply eq_sym.
      trivial.
    + hilst_auto.
  - apply ded_equiv with (A := (sub (s_p (f_p A (m + 2))) A)).
    apply ded_subst. apply ded_tt1. simpl; tauto.
    rewrite f_p_unfold.
    om (S(m+2)) (m+3).
    hilst_auto.
Defined.


Lemma rui_1_8_second_half : forall A m, [sub (s_p tt) A] |--  (f_p A m)  <<->>  (f_p A (m + 1)) ->
                                        [f_p A (m+3)] |--  f_p A (m + 1).
Proof.
  intros. apply ded_equiv with (A := (f_p A (m+3))).
  - replace (m + 3) with (m + 2 + 1) at 2; try omega.
    replace (m + 3) with (m + 2 + 1) at 2; try omega.
    repeat (rewrite <- (f_p_unfold_gen _ _ 0)).
    apply ded_subst.
    apply split_equiv; split.
    + apply rui_1_8_second_half_2. trivial.
    + apply rui_1_8_second_half_3.
  - hilst_auto.
Defined.


(** Cue for a small grand finale... of the proof of Lemma 1.8 (even this one turned out longer than expected ... )*)


Lemma rui_1_8 : forall A m, [sub (s_p tt) A] |--  (f_p A m)  <<->>  (f_p A (m + 1)) ->
                            [] |-- f_p A (m+1) <<->>  f_p A (m + 3).
Proof.
  intros. apply split_equiv; split.
  - apply hil_ded.
    apply rui_1_8_first_half. trivial.
  - apply hil_ded.
    apply rui_1_8_second_half. trivial.
Defined.

  
