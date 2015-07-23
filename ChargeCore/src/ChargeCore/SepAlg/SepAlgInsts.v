Require Import UUSepAlg SepAlg Rel.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section SAProd.
  Context A B `{HA: SepAlg A} `{HB: SepAlg B}.

  Instance SepAlgOps_prod: SepAlgOps (A * B) := {|
    sa_unit ab := sa_unit (fst ab) /\ sa_unit (snd ab);
    sa_mul a b c :=
      sa_mul (fst a) (fst b) (fst c) /\
      sa_mul (snd a) (snd b) (snd c)
   |}.

  Definition SepAlg_prod: SepAlg (A * B).
  Proof.
    esplit.
    - intros * [Hab Hab']. split; apply sa_mulC; assumption.
    - intros * [Habc Habc'] [Hbc Hbc'].
      destruct (sa_mulA Habc Hbc) as [exA []].
      destruct (sa_mulA Habc' Hbc') as [exB []].
      exists (exA, exB). split; split; assumption.
    - intros [a b].
      destruct (sa_unit_ex a) as [ea [Hea Hmulea]].
      destruct (sa_unit_ex b) as [eb [Heb Hmuleb]].
      exists (ea,eb). split; split; assumption.
    - intros * [Hunita Hunitb] [Hmula Hmulb].
      split; eapply sa_unit_eq; eassumption.
    - intros ab ab' [Hab Hab']. simpl. rewrite Hab, Hab'. reflexivity.
    - intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] Heq [H1 H2].
      unfold Equivalence.equiv in Heq; destruct Heq; simpl in *.
      rewrite <- H, <- H0; intuition.
  Qed.
  
  Lemma subheap_prod (a a' : A) (b b' : B) : subheap (a, b) (a', b') <-> subheap a a' /\ subheap b b'.
  Proof.
  	split; [intros [c [H1 H2]]| intros [[c H1] [d H2]]]; simpl in *.
  	+ destruct c as [c d]; simpl in *; split.
  	  * exists c. apply H1.
  	  * exists d. apply H2.
  	+ exists (c, d); simpl; split.
  	  * apply H1.
  	  * apply H2.
  Qed.

  Lemma sa_mul_split (a b c : A) (a' b' c' : B) : sa_mul (a, a') (b, b') (c, c') <-> sa_mul a b c /\ sa_mul a' b' c'.
  Proof.
    split; intros; simpl in *; auto.
  Qed.
  
End SAProd.

Section UUSAProd.
	Context A B `{HA : UUSepAlg A} `{HB: UUSepAlg B}.
	
	Local Existing Instance SepAlgOps_prod.
	Local Existing Instance SepAlg_prod.
	
	Instance UUSepAlg_prod : UUSepAlg (A * B).
	Proof.
		split.
		+ apply _.
		+ intros. destruct H as [H1 H2]. destruct u; simpl in *.
		  split; apply uusa_unit; assumption.
	Qed.
	
End UUSAProd.

Section SASum.
  Context A B `{HA: SepAlg A} `{HB: SepAlg B}.

  Global Instance SepAlgOps_sum: SepAlgOps (A + B) := {|
    sa_unit ab :=
      match ab with
      | inl a => sa_unit a
      | inr b => sa_unit b
      end;
    sa_mul a b c :=
      match a , b , c with
      | inl a , inl b , inl c => sa_mul a b c
      | inr a , inr b , inr c => sa_mul a b c
      | _ , _ , _ => False
      end
   |}.

  Global Instance SepAlg_sum: SepAlg (A + B).
  Proof.
    esplit.
    - intros [] [] []; simpl; auto; intros; apply sa_mulC; assumption.
    - intros [] [] [] [] []; simpl; intros ? Habc Hbc; try tauto.
      + destruct (sa_mulA Habc Hbc) as [exA []].
        exists (inl exA). split; assumption.
      + destruct (sa_mulA Habc Hbc) as [exB []].
        exists (inr exB). split; assumption.
    - intros [a|b].
      + destruct (sa_unit_ex a) as [ea [Hea Hmulea]].
        exists (inl ea). split; assumption.
      + destruct (sa_unit_ex b) as [eb [Heb Hmuleb]].
        exists (inr eb). split; assumption.
    - intros [] [] []; simpl; try tauto;
        intros; unfold rel, Rel_sum; eapply sa_unit_eq; eassumption.
    - intros [] []; simpl; unfold rel, Equivalence.equiv, Rel_sum; intros ? H;
        now try rewrite H.
    - intros [] [] [] [] Heq Hab; unfold Equivalence.equiv, rel in *; simpl in *;
      now try rewrite <- Heq.
  Qed.
End SASum.

Require Import List Morphisms.

Module SAFin.
Section SAFin.
  Context (T: Type). (* TODO: Equiv T *)
  Context A `{HA: SepAlg A}.

  (* A function where only a finite number of elements map to non-unit. *)
  Record finfun := {
    ff_fun :> T -> A;
    ff_fin: exists l, forall t, ~ In t l -> sa_unit (ff_fun t)
  }.

  Global Instance Equiv_finfun: Rel finfun :=
    fun f f' => forall t, rel (f t) (f' t).

  Global Instance Equivalence_finfun: Equivalence rel.
  Proof.
    split.
    - intros f t. reflexivity.
    - intros f f' H t. symmetry. apply H.
    - intros f1 f2 f3 H12 H23 t.
      etransitivity; [apply H12 | apply H23].
  Qed.

  Global Instance SepRelOps_fin: SepAlgOps finfun := {
    sa_unit f := forall t, sa_unit (f t);
    sa_mul f1 f2 f := forall t, sa_mul (f1 t) (f2 t) (f t)
  }.

  (* This is a sound axiom to add to Coq, and it's even provable for
     countable A, but it papers over some constructivity issues in
     these definitions. Instead of adding this axiom, we should either
     - Make ff_fun non-constructive; i.e., make it a functional relation.
     - Require that the sr_mulA and sr_unit_ex witnesses for A use sig instead
       of ex.
   *)
  Hypothesis indefinite_description : forall (P : A->Prop),
   ex P -> sig P.

  Global Instance SepAlg_fin: SepAlg finfun.
  Proof.
    admit.
    (*
    esplit.
    - intros a b c H t. specialize (H t). now apply sa_mulC in H.
    - intros a b c ab abc Hab Habc.
      set (f := (fun t => proj1_sig (indefinite_description (
                                         sa_mulA (Hab t) (Habc t))))).
      refine (ex_intro _ (@Build_finfun f _) _).
      esplit; intros t; simpl; unfold f; clear f.
      + set (rec := (sa_mulA (Hab t) (Habc t))).
        destruct (indefinite_description rec) as [a' [Hbc Htmp]].
        intros H. simpl. admit.
      + set (rec := (sa_mulA (Hab t) (Habc t))).
        destruct (indefinite_description rec) as [a' [Htmp Habc']].
        simpl. assumption.
    - intros f.
      set (e0 := (fun t => proj1_sig (indefinite_description (
                                         sa_unit_ex (f t))))).
      refine (ex_intro _ (@Build_finfun e0 _) _).
      split; intros t; simpl; unfold e0; clear e0.
      + set (rec := sa_unit_ex (f t)).
        destruct (indefinite_description rec) as [eA [Hunit Hmul]].
        simpl. assumption.
      + set (rec := sa_unit_ex (f t)).
        destruct (indefinite_description rec) as [eA [Hunit Hmul]].
        simpl. assumption.
    - intros a a' e0 Hunit Hmul. intros t.
      eapply sa_unit_eq; [apply Hunit | apply Hmul].
    - intros f f' Hf. split; intros H t.
      + rewrite <-(Hf t). apply H.
      + rewrite (Hf t). apply H.
    - intros f f' g g' Hf Hg t. 
      + rewrite <-(Hf t). apply Hg.
  Grab Existential Variables.
  * exists nil. intros t _.
    unfold e0; clear e0.
    set (rec := sa_unit_ex (f t)).
    destruct (indefinite_description rec) as [e0 [Hunit Hmul]].
    assumption.
  * destruct (ff_fin b) as [lb Hlb].
    destruct (ff_fin c) as [lc Hlc].
    exists (lb ++ lc). intros t Hnotin.
    assert (Hnotin_b: ~ In t lb).
    { intros Hin. apply Hnotin. apply in_or_app. now left. }
    assert (Hnotin_c: ~ In t lc).
    { intros Hin. apply Hnotin. apply in_or_app. now right. }
    specialize (Hlb _ Hnotin_b). clear Hnotin_b Hnotin.
    specialize (Hlc _ Hnotin_c). clear Hnotin_c. unfold f; clear f.
    set (rec := (sa_mulA (Hab t) (Habc t))).
    destruct (indefinite_description rec) as [a' [Hbc Habc']].
    simpl. now rewrite (sa_unit_eq Hlc Hbc).
*)
  Admitted.
End SAFin.
End SAFin.