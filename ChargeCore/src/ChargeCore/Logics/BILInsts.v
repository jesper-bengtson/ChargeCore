Require Import Setoid Morphisms RelationClasses Program.Basics.
Require Import ILogic BILogic ILInsts Pure.
Require Import Rel SepAlg.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section BISepAlg.
  Context {A} `{sa : SepAlg A}.
  Context {B : Type} `{IL: ILogic B}.
  Context {HPre : PreOrder (@rel A _)}.

  Open Scope sa_scope.
  
  Local Transparent ILPre_Ops.

  Global Program Instance SABIOps: BILOperators (ILPreFrm rel B) := {
    empSP := mkILPreFrm (fun x => Exists a : (sa_unit x), ltrue) _;
    sepSP P Q :=  mkILPreFrm (fun x => Exists x1, Exists x2, Exists H : sa_mul x1 x2 x,
                                                (ILPreFrm_pred P) x1 //\\ (ILPreFrm_pred Q) x2) _;
    wandSP P Q := mkILPreFrm (fun x => Forall x1, Forall x2, Forall H : sa_mul x x1 x2,  
                                                 (ILPreFrm_pred P) x1 -->> (ILPreFrm_pred Q) x2) _
  }.
  Next Obligation.
  	apply lexistsL; intro H1. eapply lexistsR. rewrite <- H. assumption. apply ltrueR.
  Qed.
  Next Obligation.
  	apply lexistsL; intro a; apply lexistsL; intro b; apply lexistsL; intro Hab.
  	apply lexistsR with a; apply lexistsR with b. eapply lexistsR. eapply sa_mul_monR; eassumption. reflexivity.
  Qed.
  Next Obligation.
	apply lforallR; intro a; apply lforallR; intro b; apply lforallR; intro Hab.
	apply lforallL with a; apply lforallL with b. apply lforallL. eapply sa_mul_mon; [symmetry|]; eassumption.
	reflexivity.
  Qed.

  Instance SABILogic : BILogic (ILPreFrm rel B). 
    split.
    + apply _.
    + intros P Q x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro H'; apply sa_mulC in H'.
      apply lexistsR with x2; apply lexistsR with x1; apply lexistsR with H'; apply landC.
    + intros P Q R x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
      repeat setoid_rewrite landexistsD.
      apply lexistsL; intro x3. apply lexistsL; intro x4; apply lexistsL; intro Hx1.
      destruct (sa_mulA Hx1 Hx) as [x5 [Hx2 Hx5]].
      apply lexistsR with x3; apply lexistsR with x5; apply lexistsR with Hx5.
      rewrite landA. apply landR; [apply landL1; reflexivity| apply landL2].
      apply lexistsR with x4. apply lexistsR with x2; apply lexistsR with Hx2.
      reflexivity.
    + intros P Q R; split; intros H x; simpl.
      - apply lforallR; intro x1; apply lforallR; intro x2; apply lforallR; intro Hx1.
        apply limplAdj.
        specialize (H x2); simpl in H.
        rewrite <- H.
        apply lexistsR with x; apply lexistsR with x1; apply lexistsR with Hx1. reflexivity.
      - apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
        specialize (H x1); simpl in H.
        rewrite H.
		apply landAdj.
        apply lforallL with x2; apply lforallL with x; apply lforallL with Hx.
        reflexivity.
    + intros P Q R H x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
      repeat eapply lexistsR; [eassumption|].
      rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
        rewrite landC, landexistsD. apply lexistsL; intro Horg.
        apply landL2.
        apply sa_unit_eq in Hx. rewrite <- Hx. reflexivity. assumption.
      - destruct (sa_unit_ex x) as [u [H1 H2]].
        apply lexistsR with x; apply lexistsR with u; apply lexistsR with H2.
        apply landR; [reflexivity| apply lexistsR; [assumption | apply ltrueR]].
  Qed.

  Global Instance pureop_bi_sepalg : PureOp := { 
    pure := fun (P : ILPreFrm rel B) => forall h h', (ILPreFrm_pred P) h |-- (ILPreFrm_pred P) h'
  }.

  Global Instance pure_bi_sepalg : Pure pureop_bi_sepalg.
  Proof.
    constructor.
    { unfold pure; simpl; constructor.
      { unfold sepSP; simpl; intros.
        destruct (sa_unit_ex t).
        apply lexistsR with x.
        apply lexistsR with t.
        destruct H0.
        apply sa_mulC in H1.
        eapply lexistsR; eauto.
        rewrite H. reflexivity. }
      constructor.
      { unfold sepSP; simpl; intros.
        repeat (eapply lexistsL; intros).
        rewrite H. rewrite H0. reflexivity. }
      constructor.
      { split; intros; unfold sepSP; simpl; intros.
        { repeat (eapply lexistsL; intros).
          apply landR. do 2 apply landL1. auto.
          eapply lexistsR.
          eapply lexistsR.
          eapply lexistsR. eassumption.
          eapply landR. apply landL1. apply landL2. reflexivity.
          apply landL2. reflexivity. }
        { rewrite landC.
          rewrite landexistsDL.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL.
          repeat (eapply lexistsL; intros).
          do 3 eapply lexistsR.
          eassumption.
          rewrite H.
          rewrite landC. rewrite landA. reflexivity. } }
      constructor.
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        destruct (sa_unit_ex x).
        destruct H0.
        eapply lforallL with x1.
        apply lforallL with x.
        eapply lforallL.
        rewrite x0. auto.
        apply limplAdj. apply limplL. apply H. apply landL1. reflexivity. }
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        eapply lforallL. eapply lforallL. reflexivity.
        apply limplAdj. apply limplL; auto. apply landL1. auto. } }
    { red. red. unfold pure; simpl. 
      intros. setoid_rewrite H.
      reflexivity. }
  Qed.

End BISepAlg.

Section BISepAlg2.
  Context {A} `{sa : SepAlg A}.
  Context {B} `{BIL: BILogic B}.
  Context {HPre : PreOrder (@rel A _)}.
  Context {HIL : ILogic B
  }.

  Open Scope sa_scope.
  
  Local Transparent ILPre_Ops.

  Global Program Instance SABIOps2: BILOperators (ILPreFrm rel B) := {
    empSP := mkILPreFrm (fun x => Exists a : (sa_unit x), empSP) _;
    sepSP P Q :=  mkILPreFrm (fun x => Exists x1, Exists x2, Exists H : sa_mul x1 x2 x,
                                                (ILPreFrm_pred P) x1 ** (ILPreFrm_pred Q) x2) _;
    wandSP P Q := mkILPreFrm (fun x => Forall x1, Forall x2, Forall H : sa_mul x x1 x2,  
                                                 (ILPreFrm_pred P) x1 -* (ILPreFrm_pred Q) x2) _
  }.
  Next Obligation.
  	apply lexistsL; intro H1. eapply lexistsR. rewrite <- H. assumption. reflexivity.
  Qed.
  Next Obligation.
  	apply lexistsL; intro a; apply lexistsL; intro b; apply lexistsL; intro Hab.
  	apply lexistsR with a; apply lexistsR with b. eapply lexistsR. eapply sa_mul_monR; eassumption. reflexivity.
  Qed.
  Next Obligation.
	apply lforallR; intro a; apply lforallR; intro b; apply lforallR; intro Hab.
	apply lforallL with a; apply lforallL with b. apply lforallL. eapply sa_mul_mon; [symmetry|]; eassumption.
	reflexivity.
  Qed.

  Global Instance SABILogic2 : BILogic (ILPreFrm rel B). 
    split.
    + apply _.
    + intros P Q x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro H'; apply sa_mulC in H'.
      apply lexistsR with x2; apply lexistsR with x1; apply lexistsR with H'. apply sepSPC.
    + intros P Q R x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx. 
      rewrite sepSPC. do 3 setoid_rewrite <- bilexistssc.
      apply lexistsL; intro x3; apply lexistsL; intro x4; apply lexistsL; intro Hx1.
      destruct (sa_mulA Hx1 Hx) as [x5 [Hx2 Hx5]].
      apply lexistsR with x3; apply lexistsR with x5; apply lexistsR with Hx5; apply lexistsR with x4;
      apply lexistsR with x2; apply lexistsR with Hx2.
      rewrite sepSPC, sepSPA. reflexivity.
    + intros P Q R; split; intros H x; simpl.
      - apply lforallR; intro x1; apply lforallR; intro x2; apply lforallR; intro Hx1.
        apply wandSepSPAdj. 
        specialize (H x2); simpl in H.
        rewrite <- H.
        apply lexistsR with x; apply lexistsR with x1; apply lexistsR with Hx1. reflexivity.
      - apply lexistsL; intro x1. apply lexistsL; intro x2; apply lexistsL; intro Hx.
        specialize (H x1); simpl in H.
        setoid_rewrite H.
        rewrite sepSPC. do 3 setoid_rewrite bilforallscR.
        apply lforallL with x2; apply lforallL with x; apply lforallL with Hx.
        rewrite sepSPC.
        apply wandSepSPAdj. reflexivity.
    + intros P Q R H x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
      apply lexistsR with x1; apply lexistsR with x2; apply lexistsR with Hx.      
      rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - setoid_rewrite <- bilexistssc. 
        apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx; apply lexistsL; intro H2.
        rewrite empSPR. 
        apply sa_unit_eq in Hx. rewrite <- Hx. reflexivity. assumption.
      - destruct (sa_unit_ex x) as [u [H1 H2]].
        setoid_rewrite <- bilexistssc.
        apply lexistsR with x; apply lexistsR with u; apply lexistsR with H2; apply lexistsR with H1. 
        rewrite empSPR. reflexivity.
  Qed.

  Context {POB : @PureOp B}.
  Context {PureB : Pure POB}.

  Global Instance pureop_bi_sepalg2 : PureOp := { 
    pure := fun (P : ILPreFrm rel B) => 
        (forall h, pure ((ILPreFrm_pred P) h)) /\
    	(forall h h', (ILPreFrm_pred P) h |-- (ILPreFrm_pred P) h')
  }.

  Global Instance pure_bi_sepalg2 : Pure pureop_bi_sepalg2.
  Proof.
    constructor.
    { unfold pure; simpl; intros; constructor.
      { unfold sepSP; simpl; intros.
        destruct H as [H H1].
        pose proof (@pure_axiom B _ _ _ PureB _ (H t)) as H2.
        destruct H2 as [H2 _].
        destruct (sa_unit_ex t) as [x [Hx Htx]].
        apply lexistsR with x.
        apply lexistsR with t.
        apply sa_mulC in Htx.
        eapply lexistsR with Htx.
        rewrite H2, (H1 t x); reflexivity. }
      constructor.
      { unfold sepSP; simpl; intros.
        repeat (eapply lexistsL; intros).
        destruct H as [H1 H2]; destruct H0 as [H3 H4].
        rewrite (H2 x t), (H4 x0 t).
        specialize (H1 t). specialize (H3 t).
        pose proof (@pure_axiom B _ _ _ PureB _ H1).
        destruct H as [_ [H _]].
        rewrite H. reflexivity. assumption. }
      constructor.
      { split; intros; unfold sepSP; simpl; intros.
        { repeat (eapply lexistsL; intros).
          destruct H as [H H1].
          pose proof (@pure_axiom B _ _ _ PureB) _ (H x) as H2.
          destruct H2 as [_ [_ [H2 _]]].
          rewrite H2.
          apply landR; [apply landL1; auto | apply landL2].
          do 3 eapply lexistsR; [eassumption|reflexivity]. }
        { rewrite landC.
          rewrite landexistsDL.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL.
          repeat (eapply lexistsL; intros).
          do 3 eapply lexistsR.
          eassumption. destruct H as [H H1].
          rewrite (H1 t x).
          pose proof (@pure_axiom B _ _ _ PureB) _ (H x) as H2.
          destruct H2 as [_ [_ [H2 _]]].
          destruct (H2 (Q x) (R x0)) as [_ H3].
          rewrite landC. assumption.
	   } }
      constructor.
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        destruct (sa_unit_ex x).
        destruct H0.
        eapply lforallL with x1.
        apply lforallL with x.
        eapply lforallL.
        rewrite x0. auto.
        destruct H as [H H2].
        pose proof (@pure_axiom B _ _ _ PureB) _ (H x1) as H3.
        destruct H3 as [_ [_ [_ [H3 _]]]].
        rewrite H3.
        apply limplAdj. apply limplL. apply H2. apply landL1. reflexivity. }
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        eapply lforallL. eapply lforallL. reflexivity.
        destruct H as [H H2].
        pose proof (@pure_axiom B _ _ _ PureB) _ (H x) as H3.
        destruct H3 as [_ [_ [_ [_ H3]]]].
        destruct H0 as [H4 H5].
        rewrite <- H3; [|auto].
        apply limplAdj. apply limplL; auto. apply landL1; auto. } }
    { red. red. unfold pure; simpl; intros.
      destruct PureB. repeat setoid_rewrite H; reflexivity. }
  Qed.

End BISepAlg2.


Require Import ILEmbed.

(* not sure about this *)
Definition setrel {A} (rel: relation A) : relation (A -> Prop) :=
  fun P Q => forall a, Q a -> exists a', P a' /\ rel a' a.

Module BIViews.
Section BIViews.
  Context {A} `{sr : SepAlg A}.
  Context {B} `{IL: ILogic B}.
  Context {EO: EmbedOp Prop B} {Emb: Embed Prop B}.
  Context (rel: relation A) {HPre : PreOrder rel}.
  Context {HPre_equiv: PreOrder (Equivalence.equiv)}. (* redundant but practical *)
  (* This property is weaker than Proper (rel ++> impl) (sr_mul a b) *)
  Context (Hmul_K: forall x1 x2 x x', sa_mul x1 x2 x -> rel x x' ->
                                      exists x1' x2', rel x1 x1' /\ rel x2 x2'
                                                      /\ sa_mul x1' x2' x').
  Context (Hunit_proper: Proper (rel ++> impl) sa_unit).
  Context (Hrel_proper: Proper (Equivalence.equiv ==> Equivalence.equiv ==> iff) rel).

  (* beware: cyclic *)
  Instance: subrelation impl lentails.
  Proof. reflexivity. Qed.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.
  Local Existing Instance EmbedILPreDropOp.
  Local Existing Instance EmbedILPreDrop.

  Program Instance SRBIOps: BILOperators (ILPreFrm rel B) := {
    empSP := mkILPreFrm (fun x => embed (sa_unit x)) _;
    sepSP P Q := mkILPreFrm (fun x =>
        Exists x1, Exists x2,
        sa_mul x1 x2 x /\\ (ILPreFrm_pred P) x1 //\\ (ILPreFrm_pred Q) x2) _;
    wandSP P Q := mkILPreFrm (fun x2 =>
        Forall x2', Forall x1, Forall x,
        rel x2 x2' ->> sa_mul x1 x2' x ->> (ILPreFrm_pred P) x1 -->> (ILPreFrm_pred Q) x) _
  }.
  Next Obligation.
    intros.
    apply embed_sound.
    apply Hunit_proper.
    apply H.
  Qed.
  Next Obligation.
    apply lexistsL; intro x1; apply lexistsL; intro x2. apply lpropandL; intro Hmulx.
    destruct (Hmul_K Hmulx H) as [x1' [x2' [Hrelx1 [Hrelx2 Hmulx']]]].
    apply lexistsR with x1'; apply lexistsR with x2'. apply lpropandR; [assumption|].
    rewrite Hrelx1, Hrelx2. reflexivity.
  Qed.
  Next Obligation.
    intros. setoid_rewrite H. reflexivity.
  Qed.

  Local Transparent ILPre_Ops.

  Instance SRBILogic : BILogic (ILPreFrm rel B).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2. apply lpropandL; intros Hmul. apply sa_mulC in Hmul.
      apply lexistsR with x2; apply lexistsR with x1. apply lpropandR; [assumption|]. apply landC.
    + intros P Q R x; simpl.
      apply lexistsL; intro xPQ'; apply lexistsL; intro xR. apply lpropandL; intro HmulPQ_R.
      repeat setoid_rewrite landexistsD.
      apply lexistsL; intro xP; apply lexistsL; intro xQ. unfold lembedand. rewrite landA. apply lpropandL; intro HmulPQ.
      destruct (sa_mulA HmulPQ HmulPQ_R) as [xQR [HmulQR HmulP_QR]].
      apply lexistsR with xP; apply lexistsR with xQR. apply lpropandR; [assumption|].
      rewrite landA. apply landR; [apply landL1; reflexivity|]. 
      apply lexistsR with xQ; apply lexistsR with xR. apply lpropandR; [assumption|]. 
      apply landL2. reflexivity.
    + intros P Q R. split; intros H.
      * simpl. intros xP. apply lforallR; intro xP'; apply lforallR; intro xQ; apply lforallR; intro xR'. 
      	apply lpropimplR; intro Hrel_xP.
      	apply lpropimplR; intro Hmul_xR'.
        apply limplAdj. rewrite <-H. simpl.
        apply lexistsR with xP'; apply lexistsR with xQ. apply lpropandR; [now apply sa_mulC|].
        now rewrite Hrel_xP.
      * simpl. intros xR. apply lexistsL; intro xP; apply lexistsL; intro xQ. apply lpropandL; intro Hmul_xR.
        apply landAdj. rewrite -> H. simpl. apply lforallL with xP; apply lforallL with xQ; apply lforallL with xR.
        apply lpropimplL; [reflexivity|]. apply lpropimplL; [now apply sa_mulC|].
        reflexivity.
    + intros. simpl. setoid_rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - apply lexistsL; intro x1; apply lexistsL; intro x2. apply lpropandL; intro Hx12.
        rewrite landC. apply landAdj.
        apply embedPropL; intros Hex2. apply limplValid.
        cancel1. rewrite (sa_unit_eq Hex2 Hx12). reflexivity.
      - destruct (sa_unit_ex x) as [ex [Hunit Hmul]].
        apply lexistsR with x; apply lexistsR with ex. apply lpropandR; [assumption|].
        apply landR; [reflexivity|].
        etransitivity; [apply ltrueR|]. apply embedPropR. assumption.
  Qed.

  Program Definition SRBIAtom (a: A) : ILPreFrm rel B :=
    mkILPreFrm (fun a' => embed (rel a a')) _.
  Next Obligation.
    apply embed_sound.
    intros H1.
    transitivity t; assumption.
  Qed.

  Global Instance SRBIAtom_Proper: Proper (rel --> lentails) SRBIAtom.
  Proof.
    intros a a' Ha t. simpl. rewrite <-Ha. reflexivity.
  Qed.

  Lemma SRBIAtom_mul a b
    (Hmul_proper: Proper (rel ++> rel ++> setrel rel) sa_mul):
    SRBIAtom a ** SRBIAtom b -|- Exists c, sa_mul a b c /\\ SRBIAtom c.
  Proof.
    split.
    - simpl. intros x.
      apply lexistsL; intro a'; apply lexistsL; intro b'. apply lpropandL; intros Hmulab'.
      apply landAdj. apply embedPropL; intros Hrela.
      apply limplValid. apply embedPropL; intros Hrelb.
      destruct (Hmul_proper _ _ Hrela _ _ Hrelb _ Hmulab')
        as [ab [Hmulab Hrelab]].
      apply lexistsR with ab. apply landR; apply embedPropR; assumption.
    - apply lexistsL; intro c. apply landAdj.
      apply embedPropL; intros Hmulc. apply limplValid. (* tactic fails *)
      simpl. intros x. apply embedPropL; intros Hrelc.
      destruct (Hmul_K Hmulc Hrelc) as [x1' [x2' [Hrelx1 [Hrelx2 Hmulx']]]].
      apply lexistsR with x1'; apply lexistsR with x2'. apply lpropandR; [assumption|].
      apply landR; apply embedPropR; assumption.
   Qed.

  Lemma SRBIAtom_emp: Exists e, sa_unit e /\\ SRBIAtom e -|- empSP.
  Proof.
    split; intros x; simpl.
    - apply lexistsL; intro e'.
      apply landAdj. apply embedPropL; intros He'. apply limplValid.
      apply embedPropL; intros Hrele'. apply embedPropR.
      rewrite <-Hrele'. assumption.
    - apply embedPropL; intros Hx.
      apply lexistsR with x. apply landR; apply embedPropR; [assumption|reflexivity].
  Qed.

End BIViews.
End BIViews.

Module BISepRel.
Section BISepRel.
  Context {A} `{sr : SepAlg A}.
  Context {B} `{IL: ILogic B}.
  Context {EO: EmbedOp Prop B} {Emb: Embed Prop B}.
  Context (rel: relation A) {HPre : PreOrder rel}.
  Context {HPre_equiv: PreOrder Equivalence.equiv}. (* redundant but practical *)
  Context (Hmul_proper: Proper (rel ++> rel ++> setrel rel) sa_mul).
  Context (Hrel_proper: Proper (Equivalence.equiv ==> Equivalence.equiv ==> iff) rel).
  (* Pym requires the relation to be a partial order wrt. equiv.
     Pym has the assertions closed under reverse rel *)

  (* beware: cyclic *)
  Instance: subrelation impl lentails.
  Proof. reflexivity. Qed.

  Local Existing Instance ILPre_ILogic.
  Local Existing Instance EmbedILPreDropOp.
  Local Existing Instance EmbedILPreDrop.

  Program Instance SRBIOps: BILOperators (ILPreFrm rel B) := {
    empSP := mkILPreFrm (fun x => embed (exists e, sa_unit e /\ rel e x)) _;
    sepSP P Q := mkILPreFrm (fun x =>
        Exists x1, Exists x2, Exists x12,
        sa_mul x1 x2 x12 /\\ rel x12 x /\\ (ILPreFrm_pred P) x1 //\\ (ILPreFrm_pred Q) x2) _;
    wandSP P Q := mkILPreFrm (fun x2 =>
        Forall x1, Forall x, sa_mul x1 x2 x ->> (ILPreFrm_pred P) x1 -->> (ILPreFrm_pred Q) x) _
  }.
  Next Obligation.
    intros.
    apply embed_sound.
    setoid_rewrite H. reflexivity.
  Qed.
  Next Obligation.
    intros. 
    cancel1; intros x1.
    cancel1; intros x2.
    cancel1; intros x3.
    repeat (apply landR).
    + apply landL1. reflexivity.
    + apply landL2; apply landL1; apply embed_sound; rewrite H; reflexivity.
    + apply landL2; apply landL2; apply landL1; reflexivity.
    + apply landL2; apply landL2; apply landL2; reflexivity.
  Qed.
  Next Obligation.
    cancel1; intros x1. apply lforallR; intro x'.
    apply lpropimplR; intro Hmul_x'.
    destruct (Hmul_proper (reflexivity x1) H Hmul_x')
      as [x [Hmul_x Hrel_x]].
    apply lforallL with x. apply lpropimplL; [assumption|]. now rewrite Hrel_x.
  Qed.

  Local Transparent ILPre_Ops.

  Instance SRBILogic : BILogic (ILPreFrm rel B).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro x12. 
      apply lpropandL; intros Hmul.
      apply lpropandL; intros Hrel. apply sa_mulC in Hmul.
      apply lexistsR with x2; apply lexistsR with x1; apply lexistsR with x12.
      do 2 (apply lpropandR; [assumption|]). apply landC.
    + intros P Q R x; simpl.
      apply lexistsL; intro xPQ'; apply lexistsL; intro xR; apply lexistsL; intro xPQ_R. 
      apply lpropandL; intros HmulPQ_R.
      apply lpropandL; intros HrelPQ_R.
      repeat setoid_rewrite landexistsD.
      apply lexistsL; intro xP; apply lexistsL; intro xQ; apply lexistsL; intro xPQ. unfold lembedand. rewrite landA.
      apply lpropandL; intros HmulPQ. rewrite landA.
      apply lpropandL; intros HrelPQ.
      destruct (Hmul_proper HrelPQ (reflexivity xR) HmulPQ_R)
        as [xPQ_R' [HmulPQ_R' HrelPQ_R']].
      destruct (sa_mulA HmulPQ HmulPQ_R') as [xQR [HmulQR HmulP_QR]].
      apply lexistsR with xP; apply lexistsR with xQR; apply lexistsR with xPQ_R'. apply lpropandR; [assumption|].
      apply lpropandR; [etransitivity; eassumption|].
      rewrite landA; apply landR; [apply landL1; reflexivity | apply landL2].
      apply lexistsR with xQ; apply lexistsR with xR; apply lexistsR with xQR. 
      apply lpropandR; [assumption|]; apply lpropandR; reflexivity.
    + intros P Q R. split; intros H.
      * simpl. intros xP. apply lforallR; intro xQ; apply lforallR; intro xR. apply lpropimplR; intros Hmul_xR. apply limplAdj.
        specialize (H xR). rewrite <-H. simpl. apply lexistsR with xP; apply lexistsR with xQ; apply lexistsR with xR.
        apply lpropandR; [now apply sa_mulC|]. apply lpropandR; reflexivity.
      * simpl. intros xR'. apply lexistsL; intro xP; apply lexistsL; intro xQ; apply lexistsL; intro xR. 
        apply lpropandL; intros Hmul_xR.
        apply lpropandL; intros Hrel_xR.
        apply landAdj. rewrite ->H. simpl. apply lforallL with xQ; apply lforallL with xR.
        apply lpropimplL; [now apply sa_mulC|]. now rewrite Hrel_xR.
    + intros. simpl. setoid_rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro x12. 
        apply lpropandL; intros Hx12.
        apply lpropandL; intros Hrelx12.
        rewrite landC. apply landAdj.
        apply embedPropL; intros [ex2 [Hex2 Hrelex2]].
        apply limplValid. rewrite <-Hrelx12.
        destruct (Hmul_proper (reflexivity x1) Hrelex2 Hx12)
          as [x' [Hmulx' Hrelx']].
        rewrite (sa_unit_eq Hex2 Hmulx') in Hrelx'. rewrite <-Hrelx'.
        reflexivity.
      - destruct (sa_unit_ex x) as [ex [Hunit Hmul]].
        apply lexistsR with x; apply lexistsR with ex; apply lexistsR with x. apply lpropandR; [assumption|].
        apply lpropandR; [reflexivity|]. apply landR; [reflexivity|].
        etransitivity; [apply ltrueR|].
        apply embedPropR. exists ex. split; [assumption|reflexivity].
  Qed.

  Program Definition SRBIAtom (a: A) : ILPreFrm rel B :=
    mkILPreFrm (fun a' => embed (rel a a')) _.
  Next Obligation.
    intros. apply embed_sound. rewrite H. reflexivity.
  Qed.

  Global Instance SRBIAtom_Proper: Proper (rel --> lentails) SRBIAtom.
  Proof.
    intros a a' Ha t. simpl. rewrite <-Ha. reflexivity.
  Qed.

  Lemma SRBIAtom_mul a b:
    SRBIAtom a ** SRBIAtom b -|- Exists c, sa_mul a b c /\\ SRBIAtom c.
  Proof.
    split.
    - simpl. intros x.
      apply lexistsL; intro a'; apply lexistsL; intro b'; apply lexistsL; intro ab'. 
      apply lpropandL; intros Hmulab'.
      apply lpropandL; intros Hrelab'.
      apply landAdj. apply embedPropL; intros Hrela.
      apply limplValid. apply embedPropL; intros Hrelb.
      destruct (Hmul_proper Hrela Hrelb Hmulab') as [ab [Hmulab Hrelab]].
      apply lexistsR with ab. apply landR.
      + apply embedPropR. assumption.
      + apply embedPropR. etransitivity; eassumption.
    - apply lexistsL; intro c. apply landAdj.
      apply embedPropL; intros Hmulc. apply limplValid. (* tactic fails *)
      simpl. intros x. apply embedPropL; intros Hrelc.
      apply lexistsR with a; apply lexistsR with b; apply lexistsR with c. 
      apply lpropandR; [assumption|]. apply lpropandR; [assumption|].
      apply landR; apply embedPropR; reflexivity.
   Qed.

  Lemma SRBIAtom_emp: Exists e, sa_unit e /\\ SRBIAtom e -|- empSP.
  Proof.
    split; intros x; simpl.
    - apply lexistsL; intro e'.
      apply landAdj. apply embedPropL; intros He'. apply limplValid.
      apply embedPropL; intros Hrele'. apply embedPropR.
      exists e'. split; assumption.
    - apply embedPropL; intros [e' [He' Hrele']].
      apply lexistsR with e'. apply landR; apply embedPropR; assumption.
  Qed.

End BISepRel.
End BISepRel.


Section BILPre.
  Context T (ord: relation T) {HPre: PreOrder ord}.
  Context {A : Type} `{HBI: BILogic A}.
  Context {HIL : ILogic A}.

  Program Instance BILPre_Ops : BILOperators (ILPreFrm ord A) := {|
    empSP      := mkILPreFrm (fun t => empSP) _;
    sepSP  P Q := mkILPreFrm (fun t => (ILPreFrm_pred P) t ** (ILPreFrm_pred Q) t) _;
    wandSP P Q := mkILPreFrm (fun t => Forall t', Forall H : ord t t', (ILPreFrm_pred P) t' -* (ILPreFrm_pred Q) t') _
  |}.
  Next Obligation.
    intros; rewrite H; reflexivity.
  Qed.
  Next Obligation.
    intros.
    apply lforallR; intro x; apply lforallR; intro Hx. rewrite <- H in Hx.
    apply lforallL with x; apply lforallL with Hx; reflexivity.
  Qed.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.

  Local Transparent ILPre_Ops.

  Instance BILPreLogic : BILogic (ILPreFrm ord A).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl; apply sepSPC.
    + intros P Q R x; simpl; apply sepSPA.
    + intros P Q R; split; intros H t; simpl.
      * apply lforallR; intro t'; apply lforallR; intro H1.
        transitivity ((ILPreFrm_pred P) t'); [apply ILPreFrm_closed; assumption|].
        apply wandSepSPAdj; apply H. 
      *  apply wandSepSPAdj; specialize (H t); unfold wandSP in H; simpl in H.
         rewrite H. apply lforallL with t; apply lforallL; reflexivity.
    + intros P Q R H x; simpl; apply bilsep; apply H. 
    + intros P; split; intros x; simpl; apply empSPR.
  Qed.

  Context {POA : @PureOp A} {PA : Pure POA}.

  Instance PureBILPreOp : @PureOp (ILPreFrm ord A) := {
    pure := fun a => forall t, pure ((ILPreFrm_pred a) t)
  }.

  Instance PureBILPre : Pure (PureBILPreOp).
  Proof.
    constructor.
    { repeat split; intros; intro t; simpl.
      * eapply pureandsc; eauto. 
      * eapply purescand; eauto.
      * eapply pureandscD; eauto.
      * eapply pureandscD; eauto.
      * apply lforallR; intro t'; apply lforallR; intro Ht.
        apply lforallL with t'; apply lforallL with Ht.
        eapply puresiimpl; eauto.
      * apply lforallR; intro t'; apply lforallR; intro Ht.
        apply lforallL with t'; apply lforallL with Ht.
        eapply pureimplsi; eauto. }
    { do 2 red. unfold pure; simpl. intros.
      split.
      { intros. eapply pure_proper. 2: eapply H0. symmetry.
        instantiate (1 := t).
        red in H. red. unfold lentails in H. simpl in H.
        intuition. }
      { intros. eapply pure_proper. 2: eapply H0. symmetry.
        instantiate (1 := t).
        red in H. red. unfold lentails in H. simpl in H.
        intuition. } }
  Qed.

  Instance pureBILPre (a : ILPreFrm ord A) (H : forall t, pure ((ILPreFrm_pred a) t)) : pure a.
  Proof.
    simpl; apply H.
  Qed.

End BILPre.

Section BILogic_Fun.
  Context (T: Type).
  Context {A : Type} `{BIL: BILogic A}.
  Context {HIL : ILogic A}.

  Local Transparent ILFun_Ops.

  Program Definition BILFun_Ops : BILOperators ((fun x y => x -> y) T A) := {|
    empSP         := fun t => empSP;
    sepSP     P Q := fun t => P t ** Q t;
    wandSP    P Q := fun t => P t -* Q t
  |}.
  
  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.
  Local Existing Instance BILFun_Ops.

  Program Definition BILFunLogic : @BILogic ((fun x y => x -> y) T A) (@ILFun_Ops T A _) BILFun_Ops. 
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl; apply sepSPC1.
    + intros P Q R x; simpl; apply sepSPA.
    + intros P Q R; split; intros H x; simpl;
      apply wandSepSPAdj; apply H.
    + intros P Q R H x; simpl; apply bilsep; apply H.
    + intros P; split; intros x; simpl; apply empSPR.
  Qed.

  Context {POA : @PureOp A} {PA : Pure POA}.

  Instance PureBILFunOp : @PureOp ((fun x y => x -> y) T A) := {
    pure := fun a => forall t, pure (a t)
  }.

  Instance PureBILFun : Pure (PureBILFunOp).
  Proof.
    constructor.
    { intros. repeat split; intros; intro t; simpl.
      * eapply pureandsc; eauto.
      * eapply purescand; eauto.
      * eapply pureandscD; eauto.
      * eapply pureandscD; eauto.
      * eapply puresiimpl; eauto.
      * eapply pureimplsi; eauto. }
    { do 2 red; simpl; intros.
      red in H. simpl in H.
      split.
      { intros. eapply pure_proper.
        2: eapply H0. split. intuition. intuition. }
      { intros. eapply pure_proper.
        2: eapply H0. split. intuition. intuition. } }
  Qed.

  Instance pureBILFun (a : (fun x y => x -> y) T A) (H : forall t, pure (a t)) : @pure _ PureBILFunOp a.
  Proof.
    simpl; apply H.
  Qed.

End BILogic_Fun.

Global Opaque BILPre_Ops.
Global Opaque BILFun_Ops.
Global Opaque SABIOps.
Global Opaque SABIOps2.
