(** * Ruitenburg1984KeyTheorem *)


(** This file is a part of Tadeusz Litak's formalisation of W. Ruitenburg JSL 1984 paper 
"On the Period of Sequences (An(p)) in Intuitionistic Propositional Calculus" *)

(** It has been compiled and guaranteed to work with
The Coq Proof Assistant, version 8.4pl6 (September 2015)
(compiled  with OCaml 4.02.2) *)



(** ** Contents *)

(** This file contains the crucial Theorem 1.4 and the "Rieger-Nishimura" result it relies on.

*)


Require Export BoundsSubformulas.



       



(* ######################################## *)

(** ** "Rieger-Nishimura" Lemma *)


(** Ruitenburg in the base case of his Theorem 1.4:
    "for all proposition variables a \neg p it follows that each subformula B(q) of A(q) is equivalent to a formula of the Rieger-Nishimura lattice."
 What is used in that proof is a specific result about formulas equivalent (in a given context) to one-variable ones,
 which can indeed be derived from the Rieger-Nishimura result, but can be also shown directly, which is what we're going to do here. *)


(** *** Some tactics **)

(** The tactic below is useful for applying transitivity of subformulas ... *)

Ltac subfo SfC C1 C2 con1 con2 :=
    rewrite Sfm_equivalent in SfC;
    pose proof (con1 C1 C2) as hC1'; pose proof (con2 C1 C2) as hC2';
    pose proof (sfm_tra _ _ _ hC1' SfC) as hC1;  pose proof (sfm_tra _ _ _ hC2' SfC) as hC2;
    rewrite <- Sfm_equivalent in *;
    clear hC1'; clear hC2'; clear SfC.

(** The next tactics is actually somewhat redundant. It is modelled after 
    [subst_it] and [subst_short] in the proof of the main result below, 
    but unlike these two in the end it got used in only one subcase of 
    of the inductive proof. Still, it is used twice in that particular spot,
    so its introduction can be justified by the famous rule "two or more, use a for". *)

Ltac subst_quick H1 t :=
                  apply t in H1;
                  unfold s_p in H1;
                  simpl in H1; 
                  try rewrite substituting_with_fresh in H1; trivial;
                  rewrite freshcon in H1; trivial;
                  try (rewrite s_n_triv in H1);
                  simpl in H1;
                  fold s_p in H1.

(** *** The "Rieger-Nishimura" result itself *)

Lemma  Rieger_Nishimura_corollary :forall G B v, fresh_l_p v (B :: G) ->  
                ( forall C : form,
                (BoundSubformulas B) C ->
                G |-- sub (s_p tt) C  ) ->
                forall  C,  (Subformulas B) C ->  G |-- (sub (s_p (var v)) C) ->> ff \/  
                                                  G |-- sub (s_p (var v)) C <<->> (var v)  \/
                                                  G |-- sub (s_p (var v)) C.
  intros G B v H H0.   
  induction C; intros SfC; simpl in *.
  - pose proof (BoundVar _ _ SfC) as HBn. apply H0 in HBn.
    unfold s_p in *. unfold s_n in *.
    destruct v; destruct n; simpl in *.
    + right. left. eauto.
    + right. right. trivial.
    + right. left. eauto.
    + right. right. trivial.
  - pose proof (BoundImp _ _ _ SfC) as HImp. apply H0 in HImp.
    inversion_clear H.
    simpl in HImp.
    subfo SfC C1 C2 sfm_li sfm_ri.
    pose proof (Inherited_freshness _ _ _ H1 hC1) as freshC1.
    pose proof (Inherited_freshness _ _ _ H1 hC2) as freshC2.    
    clear H0.
    specialize (IHC1 hC1). specialize (IHC2 hC2).
    clear hC1. clear hC2. 
    inversion_clear IHC1 as [HC1 | [HC1 | HC1]].
    + right. right. apply hil_cut_impl with (B := ff); trivial.
    + inversion_clear IHC2 as [HC2 | [HC2 | HC2]].         
      * subst_quick HC1 (hil_sub (s_n v tt)).
        subst_quick HC2 (hil_sub (s_n v tt)).
        (** Okay, now we get G |-- ff. Doesn't matter then which one we choose. *)
        left. apply hilMP with (A := ff); trivial.
        eapply hilMP. apply HC2.
        eapply hilMP. apply HImp.
        eapply ded_equiv.  apply eq_sym. apply HC1.
        trivial.
      * right. right. 
        {
          eapply ded_equiv.
          - apply eq_impl_full; apply eq_sym.
            + apply HC1.
            + apply HC2.
          - trivial.
        }
      * right. right. apply hil_ded. apply hil_weaken. trivial.
    + inversion_clear IHC2 as [HC2 | [HC2 | HC2]].
      * left. eapply hil_cut_impl; try eassumption.
        apply hil_ded. eapply hilMP. hilst_auto.
        apply hil_weaken. trivial.
      * right. left. 
        {
          apply eq_trans with (B := tt ->> (var v)). 
          - apply eq_impl_full. 
            + apply ded_tt1gen; trivial.
            + apply HC2.
          - apply ded_conj; split.
            + apply hil_ded. eapply hilMP.
              * hilst_auto.
              * trivial.
            + trivial.
        }
      * right. right. apply hil_ded. apply hil_weaken. trivial.
  - subfo SfC C1 C2 sfm_la sfm_ra.
    specialize (IHC1 hC1). specialize (IHC2 hC2).
    clear H0. clear hC1. clear hC2.
    inversion_clear IHC1 as [HC1 | [hC1 | hC1]].
    + left. eapply hil_cut_impl; try eassumption. trivial.
    + inversion_clear IHC2 as [HC2 | [hC2 | hC2]].
      * left. eapply hil_cut_impl; try eassumption. trivial.
      * right. left.
        {
          eapply eq_trans.
          - eapply equiv_congr_and; eassumption.
          - apply ded_conj; split; trivial.
            apply hil_ded. apply ded_conj. split; hilst_auto.
        }
      * right. left. 
        {
          eapply eq_trans.
          - eapply equiv_congr_and; try eassumption.
            apply ded_tt1gen. trivial.
          - apply ded_conj; split; trivial.
            apply hil_ded. apply ded_conj. split. hilst_auto. trivial.
        }
    + inversion_clear IHC2 as [HC2 | [hC2 | hC2]].
      * left. eapply hil_cut_impl; try eassumption. trivial.
      * right. left.
        {
          eapply eq_trans.
          - eapply equiv_congr_and; try eassumption.
            apply ded_tt1gen. trivial.
          - apply ded_conj; split; trivial.
            apply hil_ded. apply ded_conj. split. trivial. hilst_auto.
        }
      * right. right. apply ded_conj. tauto.
  - subfo SfC C1 C2 sfm_lo sfm_ro.
    specialize (IHC1 hC1). specialize (IHC2 hC2).
    clear H0. clear hC1. clear hC2.
    inversion_clear IHC1 as [HC1 | [hC1 | HC1]].
    + inversion_clear IHC2 as [HC2 | [HC2 | HC2]].
      * left. eapply hilMP. eapply hilMP.
        apply hilA3. trivial. trivial.
      * right. left. apply ded_conj.
        {
          split.
          - eapply hilMP. eapply hilMP. apply hilA3.
            apply hil_cut_impl with (B := ff); trivial.
            apply equiv_to_impl. trivial.
          - apply hil_ded. eapply hilMP. apply hilA2.
            eapply ded_equiv.
            + apply hil_weaken. apply eq_sym. eassumption.
            + hilst_auto.
        }
      * right. right. eapply hilMP. apply hilA2. trivial.
   + inversion_clear IHC2 as [HC2 | [HC2 | HC2]].
      * right. left. apply ded_conj.
        {
          split.
          - eapply hilMP. eapply hilMP. apply hilA3.
            apply equiv_to_impl. trivial.
            apply hil_cut_impl with (B := ff); trivial.
          - apply hil_ded. eapply hilMP. apply hilA1.
            eapply ded_equiv.
            + apply hil_weaken. apply eq_sym. eassumption.
            + hilst_auto.
        }
      * right. left. eapply eq_trans.
        apply equiv_congr_or; try eassumption.
        apply ded_conj. split; trivial. eauto.
      * right. right. eapply hilMP. apply hilA2. trivial.
    + right. right. eapply hilMP. apply hilA1. trivial.
  - right. right. trivial.
  - left. trivial.
Qed.


(* ###################################################### *)
(* ###################################################### *)

(* ###################################################### *)


(** ** Theorem 1.4 *)

    
(** *** Some tactics *)


Ltac subfreshen v A H :=   apply (hil_sub (s_n v A)) in H;
          rewrite freshcon in H; trivial; simpl in H;
        unfold s_p in H;
        rewrite substituting_with_fresh in H; trivial.


(** Tactics [subst_it] and [subst_short] are powerful macros which
        repeatedly prove useful for substitutions of derivable tautologies
        in the proof of Lemma 1.4 --- and are unlikely to be useful anywhere outside the proof.
        It is worth comparing them with [subst_quick] above.
        Tactic [freshB] is purely auxiliary. 
        Tactics [rui_1_2_i_app] helps with some applications of Lemma 1.2, 
        but there is nothing special about it. *)

Ltac subst_it H1 t H0 := 
            apply t in H1;
            simpl in H1; unfold s_p in H1;
            try rewrite substituting_with_fresh in H1; trivial;
            do 2 (fold s_p in H1); rewrite s_n_triv in H1;
            do 2 (try (rewrite f_p_unfold in H1));
            rewrite s_n_neq in H1; try solve [inversion H0; trivial];
            rewrite freshcon in H1; trivial.

 Ltac freshB B := subst B; constructor; apply fresh_sub; trivial.

Ltac subst_short H1 t B :=
                  apply t in H1;
                  simpl in H1; unfold s_p in H1;
                  try rewrite substituting_with_fresh in H1; trivial;
                  do 2 (fold s_p in H1); rewrite s_n_triv in H1;
                  do 2 (try (rewrite f_p_unfold in H1));
                  rewrite freshcon in H1; trivial;
                  do 4 (try (rewrite trivial_sub in H1; trivial));
                  try (rewrite trivial_sub in H1;
                       [idtac | solve [apply fresh_sub_gen; trivial]]);
                  try (freshB B);
                  try (apply fresh_sub; trivial; constructor).
  


Ltac rui_1_2_i_app G := eapply hil_permute; try (eapply hil_weaken_gen with (G' := G));
            (** here we use Lemma 1.2 i *)
                        try (apply rui_1_2_i_col1);
                        try equal_lists.





(* ###################################################### *)
(** *** Main result *)

(** And now the crucial result itself! *)

Theorem rui_1_4: forall n G A B,
                      Included (BoundSubformulas B) (BoundSubformulas A) -> 
                      forall i v,
                      let G' :=  (f_p A i) :: sub (s_p tt) A :: G in
                      (exists b,  
                        let b' := (App tt b) in
                        Bound G' A b' /\ cardinal b n) ->
                        fresh_l_p v (p::B::A::G) ->
                        ((f_p A (2*n)) ->> (var v))::G' |-- (sub (s_p (var v)) B <<->> sub (s_p tt) B) & (sub (s_p tt) B ->> (var v)) \/
                        ((f_p A (2*n)) ->> (var v))::G' |-- sub (s_p (var v)) B <<->>  (var v) \/
                        ((f_p A (2*n)) ->> (var v))::G' |-- sub (s_p (var v)) B.
Proof.
  intro n. 
  induction n; simpl.
  - Case "n = 0". unfold App. intros.
    inversion_clear H0 as [b [HbBBoundSub Hbcard]].
    apply IncludedBound with (B := B) in HbBBoundSub; trivial.
    clear H.
    inversion Hbcard; subst; simpl in *.
    rewrite Empty_set_zero' in *.
    clear Hbcard.
    unfold Bound in HbBBoundSub.
    assert (Htt : forall C,
                (BoundSubformulas B) C ->
                 f_p A i :: sub (s_p tt) A :: G |-- sub (s_p tt) C  ).
    {
      intros. specialize (HbBBoundSub C H).
      inversion HbBBoundSub as [htt [ttistt mainhip]] .
      inversion ttistt. subst htt.
      eauto.
    }
    inversion_clear H1. inversion_clear H0. inversion_clear H2.
    destruct i. (** The case of i = 0 not explicitly discussed in the original paper! *)
    + simpl in *.  left. apply ded_conj. split.
      * apply ded_subst. rewrite equiv_tt.
        eapply hilMP. hilst_auto. hilst_auto.
      * apply hil_ded. apply hil_weaken.
        eapply hilMP. hilst_auto. hilst_auto.
    + assert (Hfresh: fresh_l_p v (f_p A (S i) :: sub (s_p tt) A :: G)).
      {
        constructor.
        -  apply fresh_for_f_p; trivial.
        -  constructor; trivial.
           apply fresh_sub; trivial.         
      }
      assert (Hfresh_gen: fresh_l_p v (B :: f_p A (S i) :: sub (s_p tt) A :: G)) by (constructor; trivial).
      pose proof (Rieger_Nishimura_corollary _ B v Hfresh_gen Htt _ (Subformulas_reflexive _ )) as cor.
      clear Hfresh_gen.
      inversion cor as [Hc | [Hc | Hc]]; clear cor. 
      * left. apply hil_weaken. apply ded_conj; split.
        apply split_equiv; split;
        apply hil_cut_impl with (B := ff);
        trivial.
        subfreshen v tt Hc.
        subfreshen v tt Hc.         
        apply hil_cut_impl with (B := ff);
        trivial.
      * right. left. apply hil_weaken. trivial.
      * right. right. apply hil_weaken. trivial.
  - Case "Inductive step on n".
    intros G A B Hinc i v Hbound Hfresh.
    induction B;
          inversion_clear Hfresh; inversion_clear H0;
          inversion_clear H2;
          try (inversion_clear H1;
          replace (n + S (n + 0)) with (S (2 * n)) in *; try omega;
          rewrite f_p_unfold in *;
          simpl in Hinc;
          unfold App, Add in Hinc;
          first [ (pose proof Hinc as Hinc';
          clear Hinc;
          pose proof (Incl_Union_l _ _ _ Hinc') as Hinc;
          pose proof (Incl_Union_r _ _ _ Hinc') as Hinc1to2;
          pose proof (Incl_Union_l _ _ _ Hinc) as Hinc1;
          pose proof (Incl_Union_r _ _ _ Hinc) as Hinc2) |
          (pose proof (Incl_Union_l _ _ _ Hinc) as Hinc1;
           pose proof (Incl_Union_r _ _ _ Hinc) as Hinc2)];
          assert (Hf1: fresh_l_p v (p :: B1 :: A :: G)) by (constructor; trivial; constructor; trivial; constructor; trivial);
          assert (Hf2: fresh_l_p v (p :: B2 :: A :: G)) by (constructor; trivial; constructor; trivial; constructor; trivial);
          specialize (IHB1 Hinc1 Hf1); specialize (IHB2 Hinc2 Hf2);
          remember (f_p A (S (S (2 * n))) ->> var v :: f_p A i :: sub (s_p tt) A :: G) as G';
          pose proof (fresh_for_f_p_gen A v H0 H) as f_f_p).
    + SCase "B is a variable...".
      destruct n0.
      * SSCase "... in fact, p itself".
        right. left. simpl.
        unfold s_p. rewrite s_n_triv. eauto.
      * SSCase "(bracketed) ... namely, a = var (S n0)".
        {
        pose proof (DecidEquiv.decid_equiv (f_p A i :: sub (s_p tt) A  :: G) (var (S n0))) as HDedn.
        destruct HDedn.
        - SSSCase "Gamma_s |-- a".
          right. right. apply hil_weaken.
          rewrite (subs_fresh_form (s_p (var v))). trivial.
          intros n1 Hnfresh.
          rewrite fresh_not_occur' in Hnfresh.
          inversion Hnfresh; subst.
          apply s_p_Sn'.
        - SSSCase "Gamma_s |-/- a".
          inversion_clear Hbound as [b [HbAbound Hbcard]].
          pose proof (IncludedBound _ _ _ _ Hinc HbAbound) as HvarBound.
          assert (HC: exists C, (In b C) /\ f_p A i :: sub (s_p tt) A  :: G |-- var (S n0) <<->> C).
          {
            unfold Bound in HvarBound. 
            pose proof (BoundVar (var (S n0)) (S n0) (In_singleton form (var (S n0)))) as Hvar.
            specialize (HvarBound (var (S n0)) Hvar).
            destruct HvarBound as [B [Hin Hded]].
            destruct Hin as [C | ttw].
            - exists C. tauto.
            - inversion H4; subst. rewrite equiv_tt in Hded.
              simpl in Hded.
              rewrite s_p_Sn' in Hded.
              contradiction.
          }
          inversion_clear HC as [C [HCin HCequiv]].
          assert (IHnInstance : let G' := f_p A i :: sub (s_p tt) A :: var (S n0) :: G in
        (exists b0 : Ensemble form,
           let b' := App tt b0 in Bound G' A b' /\ cardinal b0 n)).
          {
            exists (Subtract b C). split.
            - unfold Bound. intros. unfold Bound in HbAbound.
              destruct (HbAbound C0 H4) as [B' [hBIn Hdedeq]].
              clear IHn.
              destruct (dceq_f  C B'); subst.
              + exists tt; split; try u_right.
                       apply eq_trans with (B := (var (S n0))).
                       * apply eq_sym in HCequiv. 
                         apply eq_trans with (B := B');
                         eapply hil_permute; try (apply hil_weaken; eassumption);
                         try (instantiate (1 := var (S n0)); simpl; tauto).
                         instantiate (1 := var (S n0)); simpl; tauto.
                         instantiate (1 := var (S n0)); simpl; tauto.
                       * apply ded_tt1. simpl. tauto.
              + exists B'. split.
                       * inversion hBIn; subst.
                         u_left. apply Subtract_intro; trivial.
                         u_right.
                       * eapply hil_permute. apply hil_weaken. eassumption.
                         try (instantiate (1 := var (S n0)); simpl; tauto).
            - om n (pred (S n)). apply card_soustr_1; trivial.
          }
          specialize (IHn (var (S n0)::G) A A (Included_refl _) i v). 
          apply IHn in IHnInstance; clear IHn;
          try solve [constructor; trivial; constructor; trivial;
          constructor; trivial; constructor; trivial].
          simpl in *. rewrite s_p_Sn' in *.            
          rewrite f_p_unfold.
          replace (s_p tt (S n0)) with (var (S n0)) in *;
              try solve [rewrite s_p_Sn; trivial; omega].
          replace (n + (n + 0)) with (2 * n) in *; try omega.
          inversion_clear IHnInstance as [hip | [hip | hip]];
            left; 
            rewrite ded_conj; split; try solve [apply eq_id].
          + SSSSCase "IH yields (i)".
            rewrite ded_conj in hip; inversion_clear hip.
            apply eq_sym in H4.
            apply ded_equiv with (A := (sub (s_p tt) A))
                                     (B := (sub (s_p (var v)) A)) in H4;
              try hilst_auto.
            subst_it H4 (hil_sub (s_n v (f_p A (S (2 * n))))) H1.
            do 3 (rewrite subs_fresh_form in H4;
                  try (intros; apply s_n_neq; intro con2;
                       subst; try (apply H6); try (apply fresh_sub_gen; auto));
                 try solve [try (destruct i); try (destruct n); try (try solve [simpl; trivial];
            apply fresh_for_f_p; trivial)]).    
            (** Seems we have a point not mentioned openly in 
                    Ruitenburg: what if i : = 0
                i.e., f_p A i = p ? 
             or what if p does not appear in A but is equal to v? 
             of course, these cases seem rather trivial, 
             but still need to be taken care of in formalization...
             This is why I added explicit assumption that v is fresh for p*)
            (** It is also not immediately obvious  in the original paper 
                where does one use rui_1_2.
                The development below should make it clear. *)
            replace (n + (n + 0)) with (2 * n) in H4;
                try omega.
            om (S (n + S (n + 0))) (S (S (2 *n))).
            apply hil_cut_impl with (B := (f_p A (S (S (2 * n))))).
            apply hil_ded. eapply hil_permute. apply hil_weaken with (B := (f_p A (S (S (2 * n))) ->> var v)).
            apply hil_cut_gen with (A :=  (f_p A (2 * n) ->> f_p A (S (2 * n)))). 
            apply rui_1_2_i_col1. eassumption.
            simpl. tauto.
            hilst_auto.
          + SSSSCase "IH yields (ii)".
            apply hil_ded. eapply hilMP. hilst_auto.
            rewrite f_p_unfold. om (S (n + S (n + 0))) (S (S (2 *n))).
            subst_it hip (hil_sub (s_n v (f_p A (S (2 * n))))) H1.
            do 3 (rewrite subs_fresh_form in hip);
                  try (intros; apply s_n_neq; intro con2;
                       subst; try (apply H4); try (apply fresh_sub_gen; auto);
                 try solve [try (destruct i); try (destruct n); try (try solve [simpl; trivial];
                                                                     apply fresh_for_f_p; trivial)]).
            replace (n + (n + 0)) with (2 * n) in hip; try omega.
            apply split_equiv in hip.
            destruct hip as [rui_prema _].
            (** strictly speaking, rui_premb is not necessary here. The job would get done by rui_1_2_i,
                but it is simpler not having to use weakening etc. *)
            apply hil_ded_conv. apply hil_weaken. apply hil_ded.
            remember (var (S n0) :: f_p A i :: sub (s_p tt) A :: G) as G'.
            assert (cor1_2_i : G' |-- (f_p A (2 * n) ->> f_p A (S (2 * n)))).
            {
              eapply hil_permute. eapply hil_weaken_gen.
              apply hil_ded.
              om (S (2*n)) (2*n + 1).
              apply rui_1_2_i. instantiate (1 := G').
              equal_lists.
            }
            eapply hilMP. eapply hil_permute.
            eapply hil_weaken_gen.
            apply hil_ded.
            om (S (S(2*n))) (S(2*n) + 1).
            apply rui_1_2_i.
            instantiate (1 := ( var (S n0) :: f_p A i :: G)).
            equal_lists.
            assert (prem_rui : G' |-- f_p A (S (S (2 * n))) ->> f_p A (S (2 * n))).
            {
              eapply hil_permute. eapply hil_cut_gen.
              - apply cor1_2_i.
              - apply rui_prema.
              - equal_lists.
            }
            eapply hilMP; [idtac | apply prem_rui].
            eapply hil_permute.
            apply hil_weaken_gen.
            apply rui_1_2_ii.
            instantiate (1 := i). instantiate (1 := G'). subst.
            equal_lists.
          + SSSSCase "IH yields (iii)".
            subst_it hip (hil_sub (s_n v (f_p A (S (2 * n))))) H1.
            do 3 (rewrite subs_fresh_form in hip);
                  try (intros; apply s_n_neq; intro con2;
                       subst; try (apply H4); try (apply fresh_sub_gen; auto);
                 try solve [try (destruct i); try (destruct n); try (try solve [simpl; trivial];
                                                                     apply fresh_for_f_p; trivial)]).            
            replace (n + (n + 0)) with (2 * n) in *; try omega.
            apply hil_ded. eapply hilMP.
            hilst_auto.
            rewrite f_p_unfold.
            om (S (n + S (n + 0)))  (S (S (2 * n))).
            remember (var (S n0) ::  f_p A (S (S (2 * n))) ->> var v :: f_p A i :: sub (s_p tt) A :: G) as G'.
            assert (cor1_2_i : G' |-- (f_p A (2 * n) ->> f_p A (S (2 * n)))).
            {
              eapply hil_permute. eapply hil_weaken_gen.
              apply hil_ded.
              om (S (2*n)) (2*n + 1).
              apply rui_1_2_i. instantiate (1 := G').
              equal_lists.
            }            
            eapply hil_permute.
            eapply hil_cut_gen.
            apply cor1_2_i.
            apply hip.
            equal_lists.
        }
    + SCase "B = B1 ->> B2".
      inversion_clear IHB2 as [HB2 | [HB2 | HB2]]; [idtac | clear IHn | clear IHn].
      * SSCase "(bracketed) B2 satisfies (i)".
        inversion_clear Hbound as [b [HbAbound Hbcard]].
        unfold Included in Hinc1to2.
        specialize (Hinc1to2 (B1 ->> B2)).
        rewrite  Singleton_eq   in Hinc1to2. specialize (Hinc1to2 eq_refl).
        pose proof (IncludedBound _ _ _ _ Hinc1 HbAbound) as HB1Bound.
        pose proof (IncludedBound _ _ _ _ Hinc2 HbAbound) as HB2Bound.
        remember (f_p A i :: sub (s_p tt) A  :: G) as Gs.
        pose proof (DecidEquiv.decid_equiv Gs (sub (s_p tt) (B1 ->> B2))) as decfact; simpl in decfact.
        {
          inversion_clear IHB1 as [HB1 | [HB1 | HB1]].
          - SSSCase "B1 satisfies (i) [induction!]".
            rewrite ded_conj in *. inversion_clear HB1. inversion_clear HB2.
            inversion_clear decfact as [decyes | decno].
            + SSSSCase "decyes: prove (iii)". right. right. simpl.
              eapply hil_cut_impl. apply equiv_to_impl. eassumption.
              eapply hil_cut_impl. subst G'.  apply hil_weaken. apply decyes.
              apply equiv_to_impl. apply eq_sym. trivial.
            + SSSSCase "decno: use IH to show (i)".
              left. simpl. split. apply eq_impl_full; trivial.
              remember ((sub (s_p tt) B1) ->> (sub (s_p tt) B2)) as B.
              unfold Bound in HbAbound. pose proof (HbAbound _ Hinc1to2) as HbB.
              inversion HbB as [C [inbC' eqBC]].              
              assert (inBC: In b C). 
              {
                apply Union_inv in inbC'. simpl in eqBC.
                destruct inbC' as [trueC | falseC]; subst B.
                - subst Gs. tauto.
                - rewrite Singleton_eq in falseC. subst C.
                  rewrite equiv_tt in eqBC. contradiction.
              }
              clear inbC'. clear HbB.
              remember (f_p A i :: sub (s_p tt) A :: B :: G) as Gs'.
              assert (IHnInstance : exists b0 : Ensemble form,
                              let b' := App tt b0 in Bound Gs' A b' /\ cardinal b0 n).
              {
                exists (Subtract b C). split.
                - unfold Bound. intros C' HC'. apply HbAbound in HC'.
                  inversion HC' as [B0 [inB0 eqB0]].
                  destruct (dceq_f B0 C).
                  + exists tt. split.
                    * u_right.
                    * subst Gs'. subst Gs.  eapply eq_trans.
                      eapply hil_permute.
                      apply hil_weaken. apply eqB0.
                      instantiate (1 := B). simpl. tauto.
                      subst C.  simpl in eqBC. apply ded_tt1gen.
                      eapply ded_equiv. eapply hil_permute. apply  hil_weaken. apply eqBC.
                      instantiate (1 := B). simpl. tauto.
                      subst B. hilst_auto.                    
                  + exists B0. split.
                    * apply Add_inv in inB0. inversion inB0. apply Add_intro1.
                      apply Subtract_intro. trivial. intro heh. symmetry in heh. auto.
                      u_right. auto using Singleton_intro.
                    * subst Gs'. subst Gs.  eapply hil_permute. apply hil_weaken. eassumption.
                      instantiate (1 := B). simpl. tauto.                   
                - subst B. om n (pred (S n)). apply card_soustr_1; trivial. 
              }
              specialize (IHn (B::G) A A (Included_refl _) i v). 
              subst Gs'.
              apply IHn in IHnInstance; clear IHn;
              (** killing freshness subgoal *)
              try (constructor; trivial; constructor; trivial;
              constructor; trivial; constructor; trivial;
              freshB B).
              apply hil_cut_impl with (B := (f_p A (S (S (2 * n)))));
                try solve [subst G'; hilst_auto].
              inversion_clear IHnInstance as [hip | [hip | hip]];
                subst_short hip (hil_sub (s_n v (f_p A (S (2 * n))))) B;
                subst G'; subst Gs;
                (** getting rid of a superfluous hypothesis *)
                apply hil_weaken; apply hil_ded;
                om (S (S (2 * n))) (S (S (n + (n + 0)))).
              * SSSSSCase "IH yields (i): using Lemma 1.2 i".
                apply ded_conj in hip; inversion_clear hip as [hip1 _].            
                apply ded_equiv with (A := sub (s_p tt) A). apply eq_sym.
                apply hil_cut_ord with (A := (f_p A (n + (n + 0)) ->> f_p A (S (n + (n + 0))))).
                rui_1_2_i_app (B :: f_p A i :: G).                
                eapply hil_permute. apply hip1. simpl. tauto.
                hilst_auto.
              * SSSSSCase "IH yields (ii): using Lemma 1.2 i and ii".
                eapply ded_equiv. eapply hil_cut_ord with (A := (f_p A (n + (n + 0)) ->> f_p A (S (n + (n + 0))))).
                rui_1_2_i_app (B :: f_p A i :: G).               
                eapply hil_permute. apply eq_sym. apply hip. simpl. tauto.
                eapply hilMP. eapply hil_permute. eapply hil_weaken_gen.
                (** here we use Lemma 1.2 ii *)
                apply rui_1_2_ii. instantiate (1 := i). instantiate (1 := (B::G)).
                equal_lists. eapply hil_cut_ord with (A := (f_p A (n + (n + 0)) ->> f_p A (S (n + (n + 0))))).
                rui_1_2_i_app (B :: f_p A i :: G).
                apply equiv_to_impl. eapply hil_permute.
                apply hip. simpl. tauto.
              * SSSSSCase "IH yields (iii)".
                eapply hil_cut_ord with (A := (f_p A (n + (n + 0)) ->> f_p A (S (n + (n + 0))))).
                rui_1_2_i_app (B :: f_p A i :: G).
                eapply hil_permute. apply hip.
                simpl. tauto.
          - SSSCase "B1 satisfies (ii) [induction!]".
            rewrite ded_conj in *. inversion_clear HB1. inversion_clear HB2.
            inversion_clear decfact as [decyes | decno].
            + SSSSCase "decyes: prove (iii)". right. right. simpl.
              subst G'. subst Gs.
              subst_short H5 (hil_sub (s_n v tt)) A. (** last argument is dummy *)
              eapply hil_ded. apply hil_weaken.
              eapply hilMP. apply equiv_to_impl.  apply eq_sym.
              apply H6.  apply hil_weaken.
              eapply hilMP. apply decyes.
              eapply hilMP. apply hil_cut_ord with (A :=  (f_p A (S (S (n + (n + 0)))) ->> tt)).
              auto. apply H5. auto.
            + SSSSCase "decno: use IH to show (i)".
              subst G'. rewrite HeqGs in *.
              pose proof H5 as H5'. (** In the most involved case of difficult subconjunct of 
                                the difficult conjunct below, we will need the original 
                                equivalence between the variable and the  antecedent of implication,
                                hence we keep a copy.
                                Otherwise, however, all we will need is substitution with tt: *)                               
              subst_short  H5 (hil_sub (s_n v tt)) A. (** last argument is dummy *)
              left.  apply and_comm.
              (** We flip the order of conjuncts, doing the easier part first.
               Note that the "easier part" was the difficult one in the previous subcase,
               whereas the one which is difficult one was solved immediately before;
               this is why we will be one nesting level deeper in this subcase. *) 
              split.
              * SSSSSCase "Easy conjunct: (B1 {tt }/p ->> B2 {tt }/p) ->> var v". 
                apply hil_cut_impl with (B := (sub (s_p tt) B2)); trivial.
                eapply hilMP with (A := (sub (s_p tt) B1)).
                apply hil_ded. apply hil_ded.
                eapply hilMP. hilst_auto. hilst_auto.
                apply hil_weaken. apply hilMP with (A := tt).
                eapply hil_cut_ord; try apply H5.
                auto. auto.
              * SSSSSCase "(bracketed) Difficult conjunct:  B1 {var v }/p ->> B2 {var v }/p <<->> B1 {tt }/p ->> B2 {tt }/p".
                {
                  simpl sub.
                  replace (S (S (n + (n + 0)))) with (S (S (2 * n))) in H5;
                    try omega.
                  apply ded_conj. apply and_comm.
                  (** flipping conjuncts again to do the easy one first ... *)
                  split.
                  - SSSSSSCase "easy subconjunct: B(T) -> B(v)".
                    apply hil_cut_impl with (B := (sub (s_p tt) B2)).
                    + eapply hilMP with (A := (sub (s_p tt) B1)).
                      apply hil_ded. apply hil_ded.
                      eapply hilMP. hilst_auto. hilst_auto.
                      apply hil_weaken. apply hilMP with (A := tt).
                      eapply hil_cut_ord; try apply H5.
                      auto. auto.
                    + apply hil_ded. apply hil_ded.
                      apply hil_weaken.
                      apply hil_ded_conv. apply equiv_to_impl. apply eq_sym. trivial.
                  - SSSSSSCase "difficult subconjunct: B(v) -> B(T) (IH used here)".
                    (** Now we have a long block where we just 
                        follow the same sequence of steps as the last time we used IH. *)
                    unfold Bound in HbAbound. pose proof (HbAbound _ Hinc1to2) as HbB.
                    inversion_clear HbB as [C [inbC' eqBC]].              
                    assert (inBC: In b C). (*/\ f_p A i :: sub (s_p tt) A  :: G |-- B <<->> C).*)
                    {
                      apply Union_inv in inbC'. simpl in eqBC.
                      destruct inbC' as [trueC | falseC].
                      - tauto.
                      - rewrite Singleton_eq in falseC. subst C.
                        rewrite equiv_tt in eqBC. contradiction.
                    }
                    clear inbC'.
                    remember ((sub (s_p tt) B1) ->> (sub (s_p tt) B2)) as B.
                    remember (f_p A i :: sub (s_p tt) A :: B :: G) as Gs'.
                    assert (IHnInstance : exists b0 : Ensemble form,
                              let b' := App tt b0 in Bound Gs' A b' /\ cardinal b0 n).
                    {
                      exists (Subtract b C). split.
                      - unfold Bound. intros C' HC'. apply HbAbound in HC'.
                        inversion HC' as [B0 [inB0 eqB0]].
                        destruct (dceq_f B0 C).
                        + exists tt. split.
                          * u_right.
                          * subst Gs'.   eapply eq_trans.
                            eapply hil_permute.
                            apply hil_weaken. apply eqB0.
                            instantiate (1 := B). simpl. tauto.
                            subst C.  simpl in eqBC. apply ded_tt1gen.
                            eapply ded_equiv. eapply hil_permute. apply  hil_weaken. apply eqBC.
                            instantiate (1 := B). simpl. tauto.
                            subst B. hilst_auto.                    
                        + exists B0. split.
                          * apply Add_inv in inB0. inversion inB0. apply Add_intro1.
                            apply Subtract_intro. trivial. intro heh. symmetry in heh. auto.
                            u_right. auto using Singleton_intro.
                          * subst Gs'.  eapply hil_permute. apply hil_weaken. eassumption.
                            instantiate (1 := B). simpl. tauto.                   
                      - subst B. om n (pred (S n)). apply card_soustr_1; trivial. 
                    }
                    specialize (IHn (B::G) A A (Included_refl _) i v). 
                    subst Gs'.
                    apply IHn in IHnInstance; clear IHn;
                    (** killing freshness subgoal *)
                        try (constructor; trivial; constructor; trivial;
                             constructor; trivial; constructor; trivial;
                             freshB B).
                    rewrite HeqB in *.
                    apply hil_ded. apply hil_ded. apply hil_weaken.
                    apply ded_equiv with (A := (sub (s_p (var v)) B2)).         
                    do 1 (apply hil_weaken). assumption.
                    eapply hilMP. hilst_auto. 
                    eapply hilMP. do 1 (apply hil_weaken). eassumption. (** This is where we use H5', a copy of 
                                original H5 which we wisely created above. *)
                    apply hilMP with (A := (f_p A (S (S (2 * n))))). hilst_auto.
                    (** Ruitenburg: "Then Gs |-- B(T) -> A^{2n-1}(p)" *)
                    (** The whole use of induction in this particular subcase is hidden in this assertion! 
                        The assertion also uses 1.2 (ii) *)
                    assert (hip1_improved: Gs |-- B ->> f_p A (S (2 * n))).
                    {
                      subst Gs. rewrite HeqB in *.
                      apply hil_ded. 
                      inversion_clear IHnInstance as [hip | [hip | hip]];
                        subst_short hip (hil_sub (s_n v (f_p A (2 * n)))) B;
                        replace (n + (n + 0)) with (2 * n) in hip;
                        try omega.
                      - SSSSSSSCase "IH yields (i)".
                        rewrite ded_conj in hip. inversion_clear hip as [hip1 hip2].
                        eapply ded_equiv. eapply hil_permute.
                        apply hil_cut_ord with (A := (f_p A (2 * n) ->> f_p A (2 * n))). auto.
                        apply eq_sym. apply hip1.
                        simpl. tauto. hilst_auto.
                      - SSSSSSSCase "IH yields (ii)".
                        apply ded_equiv with (A := (f_p A (2 * n))).
                        + apply hil_cut_ord with (A := (f_p A (2 * n) ->> f_p A (2 * n))).
                          * auto.
                          * apply eq_sym. eapply hil_permute. apply hip. simpl. tauto.
                        + eapply hilMP.
                          * eapply hil_permute. apply hil_weaken_gen.
                            apply rui_1_2_ii. instantiate (1 := i).
                            instantiate (1 := B :: G). subst B.
                            equal_lists.
                          * apply equiv_to_impl. apply hil_cut_ord with (A := (f_p A (2 * n) ->> f_p A (2 * n))).
                            auto.
                            eapply hil_permute. apply hip. simpl. tauto.
                      - SSSSSSSCase "IH yields (iii)".
                        apply hil_cut_ord with (A := (f_p A (2 * n) ->> f_p A (2 * n))).
                        auto.
                        eapply hil_permute. apply hip. simpl. tauto.
                    }
                    clear IHnInstance.
                    remember (sub (s_p (var v)) B1 ->> sub (s_p (var v)) B2 :: f_p A (S (S (2 * n))) ->> var v::Gs) as Gs'.
                    assert (rui1_2_premise : Gs' |-- f_p A (S (S (2 * n))) ->>  f_p A (S (2 * n))).
                    {
                      apply hil_cut_impl with (B := B).
                      - apply hil_cut_impl with (B := (var v)).
                        + subst Gs'. hilst_auto.
                        + rewrite HeqB. do 2 (apply hil_ded).
                          subst Gs'. subst Gs.
                          apply hil_weaken. apply hil_ded_conv.
                          apply hil_cut_impl with (B := sub (s_p (var v)) B1).
                          * apply hil_weaken. trivial.
                          * apply hil_cut_impl with (B := sub (s_p (var v)) B2).
                            hilst_auto. apply equiv_to_impl. apply hil_weaken.
                            trivial.
                      - subst Gs'. do 2 (apply hil_weaken). trivial. (** this is where we use 
                                                        the previous lemma. *)
                    }
                    subst Gs'. subst Gs.
                    apply ded_equiv with (A :=  f_p A (S (2 * n))).
                    + eapply hil_cut_ord.
                      apply  rui1_2_premise.
                      apply eq_sym.
                      eapply hil_permute. apply hil_weaken_gen.
                      apply rui_1_2_i_col2.
                      instantiate (1 := sub (s_p (var v)) B1 ->> sub (s_p (var v)) B2).
                      instantiate (1 :=  f_p A (S (S (2 * n))) ->> var v :: f_p A i :: G).
                      equal_lists.
                    + apply hilMP with (A := (f_p A (S (S (2 * n))) ->> f_p A (S (2 * n))));
                        trivial.
                      eapply hil_permute. apply hil_weaken_gen.
                      apply rui_1_2_ii.
                      instantiate (1 := i).
                      instantiate (1 := sub (s_p (var v)) B1 ->> sub (s_p (var v)) B2
                                            :: f_p A (S (S (2 * n))) ->> var v :: G).
                      equal_lists.
                }
          - SSSCase "B1 satisfies (iii) -> (i) (no induction)".
            left. rewrite ded_conj in *.
            inversion_clear HB2. simpl.
            clear decfact.
            split; rewrite HeqG' in *.
            + apply split_equiv. split.
              * do 2 (apply hil_ded). eapply ded_equiv.
                do 2 (apply hil_weaken).  apply H1.
                eapply hilMP.  hilst_auto.
                do 2 (apply hil_weaken). trivial.
              * do 2 (apply hil_ded). eapply ded_equiv.
                apply eq_sym.
                do 2 (apply hil_weaken).  apply H1.
                eapply hilMP.  hilst_auto.
                do 3 (apply hil_weaken).
                rewrite HeqGs in HB1.
                subst_short HB1 (hil_sub (s_n v tt)) A. (** last argument is dummy *)
                rewrite <- HeqGs in HB1.
                apply hil_cut_ord with (A :=  f_p A (S (S (n + (n + 0)))) ->> tt).
                auto. trivial.
            + rewrite HeqGs in HB1.
              subst_short HB1 (hil_sub (s_n v tt)) A. (** last argument is dummy *)
              rewrite <- HeqGs in HB1. apply hil_ded.
              apply hilMP with (A := sub (s_p tt) B2);
                try solve [apply hil_weaken; trivial].
              apply hilMP with (A := sub (s_p tt) B1);
                try hilst_auto.
              do 2 (apply hil_weaken). eapply hil_cut_ord; try apply HB1. auto.
        }
      * SSCase "(bracketed) B2 satisfies (ii)".
        {
        inversion_clear IHB1 as [HB1 | [HB1 | HB1]].
          - SSSCase "B1 satisfies (i) -> prove (iii)".
            right. right. simpl.
            rewrite ded_conj in HB1. inversion_clear HB1.
            eapply hil_cut_impl. apply equiv_to_impl in H1. apply H1.
            eapply hil_cut_impl. apply H5.
            apply split_equiv in HB2; inversion_clear HB2.
            trivial.
          - SSSCase "B1 satisfies (ii) -> prove (iii)".
            right. right. simpl.
            apply split_equiv. apply eq_sym in HB1.
            eapply eq_trans; eassumption.
          - SSSCase "B1 satisfies (iii) -> prove (ii)".
            right. left. simpl.
            apply split_equiv. split.
            + apply hil_ded. eapply ded_equiv.
              * apply hil_weaken. eassumption. 
              * eapply hilMP. hilst_auto. apply hil_weaken. trivial.
            + apply hil_ded. eapply hilMP. apply hilK.
              apply eq_sym in HB2. eapply ded_equiv. apply hil_weaken. eassumption. hilst_auto.
        }
      * SSCase "B2 satisfies (iii) -> prove (iii)".
        right. right. simpl. eauto.
    + SCase "B = B1 & B2".
      inversion_clear IHB1 as [H1 | [H1 | H1]].
      clear IHn. (** conjunction does not require IH at all. *)
      (** Inductive step for conjunction. *)
      * SSCase "(bracketed) B1 satisfies (i) -> prove (i)".
        left. (** case (i) in Ruitenburg's table: all entries are (i), so we can go left. *)
        {
        inversion_clear IHB2; rewrite ded_conj in *;
        inversion_clear H1; inversion_clear H5; simpl.
        - SSSCase "B2 satisfies (i)".
          split. apply equiv_congr_and; trivial.
          apply hil_cut_impl with (B := (sub (s_p tt) B1)); auto.
        - SSSCase "B2 satisfies (ii)".
          inversion_clear H1. split; [idtac | eauto].
          apply ded_conj; split.
          + apply conj_ded. apply ded_conj; split.
            apply hil_weaken. apply hil_ded_conv. eauto.
            apply hil_weaken. apply hil_weaken.
            subst.
            subst_short H8 (hil_sub (s_n v tt)) A. (** last argument is dummy *)               
            remember ( f_p A i :: sub (s_p tt) A :: G) as G'.
            apply hil_weaken.
            apply hilMP with (A := tt).
            eapply hil_permute. eapply hil_cut_gen.
            instantiate (2 := G'). instantiate (1 := (f_p A (S (S (n + (n + 0)))) ->> tt)).
            auto. apply H8.
            equal_lists. auto.
          + apply conj_ded. apply ded_conj; split.
            apply hil_weaken. apply hil_ded_conv.
            apply split_equiv in H6; inversion H6. trivial.
            eapply hilMP.
            apply hil_weaken. apply hil_weaken. apply H8.
            eapply hilMP. apply hil_weaken. apply hil_weaken. apply H7.
            hilst_auto.
        - SSSCase "B2 satisfies (iii)".
          split; [idtac | eauto].
          apply equiv_congr_and; trivial.
          apply split_equiv. split.
          apply hil_ded. apply hil_weaken.
          rewrite HeqG' in *.
          subst_short H1 (hil_sub (s_n v tt)) A. (** last argument is dummy *)
          apply hil_weaken.
          apply hil_cut_ord with (A := (f_p A (S (S (n + (n + 0)))) ->> tt)).
          auto. trivial.
          apply hil_ded. apply hil_weaken. trivial.
        }
      * SSCase "(bracketed) B1 satisfies (ii)".
        {
         inversion_clear IHB2 as [HB2 | [HB2 | HB2]]. 
         - SSSCase "B2 satisfies (i) -> prove (i)".
           rewrite ded_conj in *;
             inversion_clear HB2 as [HB2a HB2b].
           rewrite ded_conj in HB2a;
             inversion_clear HB2a as [B2vt B2tv].
           inversion_clear H1 as [B1v vB2].
           left. simpl. split.
           + rewrite split_equiv; split;
             apply conj_ded;  apply ded_conj;
             split.
             * subst.
                 subst_short vB2 (hil_sub (s_n v tt)) A. (** last argument is dummy *)
                 do 3 (apply hil_weaken).
                 apply hil_cut_ord with (A := (f_p A (S (S (n + (n + 0)))) ->> tt));
                   eauto.
             * apply hil_ded_conv. apply hil_weaken. trivial.
             * eapply hilMP.  apply hil_weaken. apply hil_weaken.
               eassumption.
               eapply hilMP. do 2 (apply hil_weaken).
               apply HB2b. hilst_auto.
             * eapply hilMP. do 2 (apply hil_weaken).
               eassumption. hilst_auto.
           + eapply hil_cut_impl. apply hilC3. trivial.
         - SSSCase "B2 satisfies (ii) -> prove (ii)".
           right. left. simpl.
           eapply eq_trans.
           apply equiv_congr_and; eassumption. eauto.
         - SSSCase "B2 satisfies (iii) -> prove (ii)".
           right. left. simpl.
           eapply eq_trans.
           + apply equiv_congr_and.
             * eassumption.
             * apply equiv_tt. trivial.
           + apply split_equiv. split; eauto.
        }
      * SSCase "(bracketed) B1 satisfies (iii)".
        {
          inversion_clear IHB2 as [HB2 | [HB2 | HB2]].
          - SSSCase "B2 satisfies (i) -> prove (i)".
            left. rewrite ded_conj in *.
            inversion_clear HB2 as [B2eq B2var].
            split; simpl.
            + rewrite split_equiv; split;
              rewrite conj_ded; apply ded_conj; split.
              * subst. do 3 (apply hil_weaken).
                subst_short H1 (hil_sub (s_n v tt)) A.
                apply hil_cut_ord with (A := (f_p A (S (S (n + (n + 0)))) ->> tt)).
                auto. assumption.
              * eapply ded_equiv. do 2 (apply hil_weaken).
                eassumption. hilst_auto.
              * do 2 (apply hil_weaken). trivial.
              * apply eq_sym in B2eq.
                eapply ded_equiv. do 2 (apply hil_weaken).
                eassumption. hilst_auto.
            + eapply hil_cut_impl. apply hilC3.
              trivial.
          - SSSCase "B2 satisfies (ii) -> prove (ii)".
            right. left. simpl.
            eapply eq_trans.
            + apply equiv_congr_and. 
              rewrite equiv_tt. trivial. eassumption.
            + apply split_equiv; split; eauto.
          - SSSCase "B2 satisfies (iii) -> prove (iii)".
            right. right. simpl. rewrite ded_conj. tauto.
        }
    + SCase "B = B1 \v/ B2".
      clear IHn. (** no need for IH when disjunction is concerned. *)
      inversion_clear IHB1 as [HB1 | [HB1 | HB1]].
      * SSCase "(bracketed) B1 satisfies (i)".
        {
          inversion_clear IHB2 as [HB2 | [HB2 | HB2]].
          - SSSCase "B2 satisfies (i) -> prove (i)".
            left. simpl. rewrite ded_conj in *.
            inversion HB1. inversion HB2.
            split.
            + apply equiv_congr_or; trivial.
            + eapply hilMP. eapply hilMP. apply hilA3.
              trivial. trivial.
          - SSSCase "B2 satisfies (ii) -> prove (ii)".
            right. left. simpl. rewrite ded_conj in HB1. inversion_clear HB1.
            rewrite split_equiv in *. inversion_clear HB2. inversion_clear H1.
            split.
            + eapply hilMP. eapply hilMP. apply hilA3.
              eapply hil_cut_impl; eassumption.
              trivial.
            + eapply hil_cut_impl. eassumption. apply hilA2.
          - SSSCase "B3 satisfies (iii) -> prove (iii)".
            right. right. simpl. eauto.
        }
      * SSCase "B1 satisfies (ii)".
        {
          inversion_clear IHB2 as [HB2 | [HB2 | HB2]].
          - SSSCase "B2 satsifies (i)  -> prove (ii)".
            right. left. simpl.
            rewrite ded_conj in HB2. inversion_clear HB2.
            rewrite split_equiv in *. inversion_clear HB1. inversion_clear H1.
            split.
            + eapply hilMP. eapply hilMP.  apply hilA3.
              trivial.
              eapply hil_cut_impl. eassumption. trivial.
            + eapply hil_cut_impl. eassumption. apply hilA1.
          - SSSCase "B2 satisfies (ii) -> prove (ii)".
            right. left. simpl.
            eapply eq_trans. eapply equiv_congr_or.
            eassumption. eassumption. eauto.
          - SSSCase "B2 satisfies (iii) -> prove (iii)".
            right. right. simpl. eauto.
        }
      * SSCase "B1 satisfies (iii) -> prove (iii)".
        right. right. simpl. eauto.
    + SCase "B = tt".
      right. right. simpl. auto.
    + SCase "B = ff".
      left. simpl. apply ded_conj. split; auto. eauto.
Qed.


(*
Lemma bound_Bound : forall b A G n, bound b A G -> n = length b ->
                                    exists B, Included (context_to_set b) B /\ Bound G A B /\ cardinal B n.
Admitted.
*)

(*

(** The version below uses bounds-as-lists, to which we are switching now. *)
      
Corollary rui_1_4' : forall b G A B i v,
                 let G' :=  (f_p A i) :: sub (s_p tt) A :: G in
                 let n := length b in
                 let b' := b ++ [tt] in
                 bound b' A G' -> bound b' B G' ->
                 fresh_l_p v (p::B::A::G) ->
                 ((f_p A (2*n)) ->> (var v))::G' |-- (sub (s_p (var v)) B <<->> sub (s_p tt) B) & (sub (s_p tt) B ->> (var v)) \/
                 ((f_p A (2*n)) ->> (var v))::G' |-- sub (s_p (var v)) B <<->>  (var v) \/
                 ((f_p A (2*n)) ->> (var v))::G' |-- sub (s_p (var v)) B.
Proof.  
  (*unfold bound.*)
  intros. 
(*
  pose proof (bound_Bound b' B G' (S n) H0) as HbB.
  replace  b' with (b ++ [tt])  in HbB; trivial.
  replace n with (length b) in HbB; trivial.
  rewrite app_length in HbB. simpl in HbB.
  replace (length b + 1) with (S (length b)) in HbB; try omega.
  specialize (HbB refl_equal).
  apply rui_1_4. *)
  induction b; intros; rewrite Forall_forall in *.
  - simpl in *.   (*remember B as B'.*) destruct B; simpl in *.
    + destruct (eq_nat_dec 0 n); subst; simpl.
      * rewrite (s_n_triv _ 0). eauto.
      * specialize (H0 (var n) (or_introl (s_p_Sn n tt n0))).
        rewrite Exists_exists in H0. inversion H0 as [BB [hB1 hB2]]. inversion hB1; subst.
        right. right. apply hil_weaken. simpl. rewrite (s_p_Sn _ _ n0) in *.
        rewrite (subs_fresh_form _ (var n)) in hB2.
        eapply ded_equiv. eassumption. simpl. auto. intros.
        rewrite fresh_not_occur' in H2. inversion H2; subst.
        apply (s_p_Sn _ _ n0).
        inversion H2.
    + specialize (H0 (sub (s_p tt) B1 ->> sub (s_p tt) B2) (or_introl (eq_refl _ ))).
      rewrite Exists_exists in H0.  inversion H0 as [BB [hB1 hB2]].  inversion hB1; subst.
      right. right. apply hil_weaken. simpl. 
Admitted.
*)


(** ** Corollary 1.5 *)



(*
Corollary rui_1_4'': forall A b, (bound b A []) -> let n:= length b in
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
  assert (Hbb: bound (b ++ [tt]) A ([f_p A i ; sub (s_p tt) A ])).
  {
    apply upward_bound_for_bound with (b:=b). (* with (b := basic_bound A).*)
    (*apply basic_bound_is_bound.*)
    - apply bound_for_bound_upward with (G := []).
      + trivial.
      + unfold incl. intros. inversion H1.
    - apply incl_appl. apply incl_refl.
        (*
    apply Forall_forall.
    unfold incl. intro.
    rewrite in_app_iff. tauto.
    *)
  }
  assert (Hfresh:fresh_l_p v' [A ; A]).
  {
    unfold fresh_l_p.
    rewrite Forall_forall.
    intros B HB.
    destruct HB as [hA | [hA | hG']]; try rewrite <- hA; auto.
    subst G'.
    inversion hG'.
    (*
    destruct hG' as [hA | ; try rewrite <- hA in *; auto.
    -  destruct i.
       + simpl. constructor. subst v'. omega.
       + om (2 * S n) (S(S(2 * n))).
         apply fresh_for_f_p. auto.
    - apply fresh_sub; auto.
    - inversion hA.
    *)
  }
  apply rui_1_4'; try rewrite Heqb; auto. (*apply Hbb. apply Hbb.*)
Defined.  
  

Corollary rui_1_5: forall A b i, (bound b A []) -> let m:= (2 * length b + 1) in [sub (s_p tt) A; f_p A i] |-- f_p A m.
Proof.
  intros.
  pose (v := (not_used A)).
  remember (S v) as v'.
  assert (Hv': fresh_f_p (S v) A).
  {
    apply all_not_used_fresh. subst v. omega.
  }
  remember (2 * length b) as n.
  assert (freshv': forall n', fresh_f_p v' (f_p A n')).
  {
    rewrite <- Heqv' in *.
    destruct n'.
    - simpl. constructor. omega.
    - apply fresh_for_f_p. trivial.
  }
  assert (fresh_ass: forall n' o,  ~ fresh_f_p o (f_p A n') -> s_n v' (f_p A n') o = var o).
  {
    rewrite <- Heqv' in *.
    intros. unfold s_n. specialize (freshv' n').
    destruct (eq_nat_dec v' o); try rewrite e in *. 
    - contradiction.
    - reflexivity .
  }
  assert (fpAn : sub (s_n v' (f_p A n)) (f_p A n)  = f_p A n).
  {
    apply subs_fresh_form; intro n'; apply fresh_ass.
  }
  assert (snv': s_n v' (f_p A n) v' = f_p A n) by apply s_n_triv.
  assert (spAtt: sub (s_n v' (f_p A n)) (sub (s_p tt) A)  = sub (s_p tt) A).
  {
     apply subs_fresh_form with (A := sub (s_p tt) A).
      intros. apply s_n_neq.
      pose proof (fresh_sub _ tt _ (freshv' 1) (f_tt v')) as hfr.
      rewrite <- f_p_1 in hfr. intro nonsense. rewrite nonsense in *. contradiction.
  }
  assert (fpUnch: sub (s_n v' (f_p A n)) (f_p A i)  = f_p A i).
  {
    apply subs_fresh_form; intro n'. intros. apply s_n_neq.
      specialize (freshv' i). intro nonsense. rewrite nonsense in *.
      contradiction.
  }
  assert (sv': sub (s_n v' (f_p A n )) (sub (s_p (var v')) A)  = f_p A (n + 1)).
  {
    rewrite <- f_p_unfold_gen. rewrite (f_p_1 A) at 2.
    apply substituting_with_fresh. trivial.
  }
  assert
    (Hcon: ssub (s_n v' (f_p A n)) [f_p A n ->> var v'; f_p A i; sub (s_p tt) A] = [f_p A n ->> f_p A n; f_p A i; sub (s_p tt) A]).
  {
    rewrite <- Heqv' in *.
    simpl. apply f_equal2; apply f_equal2.
    - apply fpAn.
    - apply snv'.
    - apply fpUnch.
    - apply f_equal2. apply spAtt.
      reflexivity.
  }
  pose proof (rui_1_4'' A b H i v Hv') as [Hip | [Hip | Hip]];
    rewrite <- Heqv' in *; rewrite <- Heqn in *; subst m;
    apply (hil_sub (s_n v' (f_p A n))) in Hip; rewrite Hcon in Hip;
    simpl in Hip; try rewrite spAtt in Hip; try rewrite snv' in Hip;
    try rewrite sv' in Hip; rev_goal;
    rewrite <- (app_nil_l [f_p A i; sub (s_p tt) A ] );
    apply hil_cut_gen with (A := (f_p A n ->> f_p A n)); auto.
  - rewrite ded_conj in Hip. inversion Hip as [H1 _].
    apply  eq_sym in H1.
    eapply (ded_equiv _ _ _ H1). hilst_auto.
  - apply eq_sym in Hip. apply ded_equiv with (A := f_p A n); trivial.
    eapply hilMP. apply hil_weaken.
    apply rui_1_2_ii. (** <-- this is the trick *)
    om (S n) (n + 1). apply split_equiv in Hip. tauto.
Defined.

Require Export Ruitenburg1984Aux.

Theorem rui_1_9: forall A b, (bound b A []) -> let m:= length b in
                                               [] |-- f_p A (2 * m + 2) <<->>  f_p A (2 * m + 4).
Proof.
  intros.
  om (2*m + 2) (2*m + 1 + 1).
  om (2*m + 4) (2*m + 1 + 3).  
  apply rui_1_8.
  apply rui_1_6.
  intros. rev_goal.
  subst m.
  apply rui_1_5.
  trivial.
Defined.

(*
Corollary rui_1_9_bound : forall A,  let m:= length (basic_bound A) in
                                     [] |-- f_p A (2 * m + 2) <<->>  f_p A (2 * m + 4).
Proof.
  intros. apply rui_1_9. apply basic_bound_is_bound.
Defined.  
*)


*)