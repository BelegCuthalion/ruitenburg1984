(** * Ruitenburg1984Main *)


(** This file is a part of Tadeusz Litak's formalisation of W. Ruitenburg JSL 1984 paper 
"On the Period of Sequences (An(p)) in Intuitionistic Propositional Calculus" *)

(** It has been compiled and guaranteed to work with
The Coq Proof Assistant, version 8.4pl6 (September 2015)
(compiled  with OCaml 4.02.2) *)



(** ** Contents *)

(** This file contains  the main Theorem 1.9.

*)


Require Export Ruitenburg1984KeyTheorem.
Require Export Ruitenburg1984Aux.

(** The latter file is not used in Corollary 1.5, only in Corollary 1.9 *)


(** ** Corollary 1.5 *)
  

Corollary rui_1_4': forall A b n, (Bound  [] A b) -> cardinal b n ->
                              forall i v,
                                let v' := S v in
                                fresh_f_p v' A ->
                                          let G' :=  [f_p A i ; sub (s_p tt) A]  in
                                          let G'' :=  (f_p A (2*n) ->> (var v'))::G'  in
                 G'' |-- (sub (s_p (var v')) A <<->> sub (s_p tt) A) & (sub (s_p tt) A ->> (var v')) \/
                 G'' |-- sub (s_p (var v')) A <<->>  (var v') \/
                 G'' |-- sub (s_p (var v')) A.
Proof.
  intros.
  (*remember (basic_bound A) as b.*)
  assert (Hbb: Bound [f_p A i ; sub (s_p tt) A ] A (App tt b)).
  {
    apply Included_Bound with (S1:=b). (* with (b := basic_bound A).*)
    (*apply basic_bound_is_bound.*)
    - apply Bound_for_Bound_upward with (G := []).
      + trivial.
      + unfold incl. intros. inversion H2.
    - apply Union_increases_l. 
  }
  assert (Hfresh:fresh_l_p v' [p; A ; A]).
  {
    unfold fresh_l_p.
    rewrite Forall_forall.
    intros B HB.
    inversion_clear HB as [hA | [hA | hG']]. (*; try rewrite <- hA; auto.*)
    - rewrite <- hA. subst v'. constructor. omega.
    - rewrite <- hA. trivial.
    - inversion hG'. rewrite <- H2. trivial. inversion H2.
  }
  apply rui_1_4; trivial.
  - apply Included_refl.
  - exists b. split; trivial.
Defined.  
  

Corollary rui_1_5: forall A b i n, (Bound [] A b) -> cardinal b n -> let m:= (2 * n + 1) in [sub (s_p tt) A; f_p A i] |-- f_p A m.
Proof.
  intros.
  pose (v := (not_used A)).
  remember (S v) as v'.
  assert (Hv': fresh_f_p (S v) A).
  {
    apply all_not_used_fresh. subst v. omega.
  }
  remember (2 * n) as o.
  assert (freshv': forall n', fresh_f_p v' (f_p A n')).
  {
    rewrite <- Heqv' in *.
    destruct n'.
    - simpl. constructor. omega.
    - apply fresh_for_f_p. trivial.
  }
  assert (fresh_ass: forall n' o',  ~ fresh_f_p o' (f_p A n') -> s_n v' (f_p A n') o' = var o').
  {
    rewrite <- Heqv' in *.
    intros. unfold s_n. specialize (freshv' n').
    destruct (eq_nat_dec v' o'); try rewrite e in *. 
    - contradiction.
    - reflexivity .
  }
  assert (fpAn : sub (s_n v' (f_p A o)) (f_p A o)  = f_p A o).
  {
    apply subs_fresh_form; intro n'; apply fresh_ass.
  }
  assert (snv': s_n v' (f_p A o) v' = f_p A o) by apply s_n_triv.
  assert (spAtt: sub (s_n v' (f_p A o)) (sub (s_p tt) A)  = sub (s_p tt) A).
  {
     apply subs_fresh_form with (A := sub (s_p tt) A).
      intros. apply s_n_neq.
      pose proof (fresh_sub _ tt _ (freshv' 1) (f_tt v')) as hfr.
      rewrite <- f_p_1 in hfr. intro nonsense. rewrite nonsense in *. contradiction.
  }
  assert (fpUnch: sub (s_n v' (f_p A o)) (f_p A i)  = f_p A i).
  {
    apply subs_fresh_form; intro n''. intros. apply s_n_neq.
      specialize (freshv' i). intro nonsense. rewrite nonsense in *.
      contradiction.
  }
  assert (sv': sub (s_n v' (f_p A o )) (sub (s_p (var v')) A)  = f_p A m).
  {
    subst m.
    rewrite <- f_p_unfold_gen. rewrite (f_p_1 A) at 2.
    apply substituting_with_fresh. trivial.
  }
  assert
    (Hcon: ssub (s_n v' (f_p A o)) [f_p A o ->> var v'; f_p A i; sub (s_p tt) A] = [f_p A o ->> f_p A o; f_p A i; sub (s_p tt) A]).
  {
    rewrite <- Heqv' in *.
    simpl. apply f_equal2; apply f_equal2.
    - apply fpAn.
    - apply snv'.
    - apply fpUnch.
    - apply f_equal2. apply spAtt.
      reflexivity.
  }
  pose proof (rui_1_4' A b n H H0 i v Hv') as [Hip | [Hip | Hip]];
    rewrite <- Heqv' in *; rewrite <- Heqo in *; subst m;
    apply (hil_sub (s_n v' (f_p A o))) in Hip; rewrite Hcon in Hip;
    simpl in Hip; try rewrite spAtt in Hip; try rewrite snv' in Hip;
    try rewrite sv' in Hip; rev_goal;
    rewrite <- (app_nil_l [f_p A i; sub (s_p tt) A ] );
    apply hil_cut_gen with (A := (f_p A o ->> f_p A o)); auto.
  - rewrite ded_conj in Hip. inversion Hip as [H1 _].
    apply  eq_sym in H1.
    eapply (ded_equiv _ _ _ H1). hilst_auto.
  - apply eq_sym in Hip. apply ded_equiv with (A := f_p A o); trivial.
    eapply hilMP. apply hil_weaken.
    apply rui_1_2_ii. (** <-- this is the trick *)
    om (S o) (o + 1). apply split_equiv in Hip. tauto.
Defined.


(** ** Main theorem *)

(** ... in a version for bounds and in a version for lists. *)

Theorem rui_1_9_Ens:
  forall A b m, (Bound [] A b) ->
                cardinal b m ->
                [] |-- f_p A (2 * m + 2) <<->>  f_p A (2 * m + 4).
Proof.
  intros.
  om (2*m + 2) (2*m + 1 + 1).
  om (2*m + 4) (2*m + 1 + 3).  
  apply rui_1_8.
  apply rui_1_6.
  intros. rev_goal.
  (* subst m. *)
  apply rui_1_5 with (b := b);
  trivial.
Defined.

  


Theorem rui_1_9_list: forall A b, (bound b A []) -> exists m, m <= length b /\
                                               [] |-- f_p A (2 * m + 2) <<->>  f_p A (2 * m + 4).
Proof.
  intros.
  destruct (finite_cardinal _ _  (Finite_context_to_set b)) as [n' Hn'].
  pose proof (bound_is_Bound b A []  H) as indeed.
  exists n'. split.
  - apply cardinal_context_to_set. assumption.
  (*inversion indeed as [B [h1B [h2B h3B]]].*)
  - apply rui_1_9_Ens with (b := (context_to_set b)); trivial.
Defined.


(*
Corollary rui_1_9_bound : forall A,  let m:= length (basic_bound A) in
                                     [] |-- f_p A (2 * m + 2) <<->>  f_p A (2 * m + 4).
Proof.
  intros. apply rui_1_9. apply basic_bound_is_bound.
Defined.  
*)


