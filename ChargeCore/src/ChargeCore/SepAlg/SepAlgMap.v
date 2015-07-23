Require Import Containers.Maps.
Require Import Coq.Strings.String Ascii.
Require Import Compare_dec.
Require Import OrderedType.
Require Import SepAlg UUSepAlg.
(* This requires the Containers library from 
   http://coq.inria.fr/pylons/contribs/view/Containers/v8.4 *)
Require Import MapInterface MapFacts.
Require Import BILInsts.

(* String is an ordered type *)

Definition ascii_lt a b := nat_of_ascii a <<< nat_of_ascii b.
Definition ascii_compare a b := nat_compare (nat_of_ascii a) (nat_of_ascii b).

Instance StrictOrderAscii : StrictOrder ascii_lt eq.
Proof.
  split.
  + intros a b c Hab Hac. unfold ascii_lt in *. etransitivity; eassumption.
  + intros a b H Hab. unfold ascii_lt in H. rewrite Hab in H. apply lt_antirefl in H. assumption.
Qed.

Lemma nat_of_ascii_inj (a b : ascii) (H : nat_of_ascii a = nat_of_ascii b) : a = b.
Proof.
  assert (ascii_of_nat(nat_of_ascii a) = ascii_of_nat(nat_of_ascii b)) as H1
         by (rewrite H; reflexivity).
  do 2 rewrite ascii_nat_embedding in H1. assumption.
Qed.
 
Instance OrderedTypeAscii : OrderedType ascii := {
   _eq := Equivalence.equiv;
   _lt := ascii_lt;
   _cmp := ascii_compare
}.
Proof.
  intros x y.
  unfold ascii_compare, ascii_lt.
  destruct (compare_dec (nat_of_ascii x) (nat_of_ascii y)).
  + assert (nat_compare (nat_of_ascii x) (nat_of_ascii y) = Lt) as H1 by (apply nat_compare_lt; assumption).
    rewrite H1. apply compare_spec_lt. assumption.
  + assert (nat_compare (nat_of_ascii x) (nat_of_ascii y) = Eq) as H1 by (apply nat_compare_eq_iff; assumption).
    rewrite H1. apply compare_spec_eq. apply nat_of_ascii_inj. assumption.
  + assert (nat_compare (nat_of_ascii x) (nat_of_ascii y) = Gt) as H1 by (apply nat_compare_gt; assumption).
    rewrite H1. apply compare_spec_gt. assumption.
Qed.

Inductive string_lt : string -> string -> Prop :=
| s_emp a s : string_lt EmptyString (String a s)
| s_neq a b s t : a <<< b -> string_lt (String a s) (String b t)
| s_eq a b s t : a === b -> string_lt s t -> string_lt (String a s) (String b t).

Fixpoint string_compare s t := 
  match s, t with
      | EmptyString, EmptyString => Eq
      | EmptyString, String _ _ => Lt
      | String _ _, EmptyString => Gt
      | String a s, String b t =>
        match a =?= b with
          | Eq => string_compare s t 
          | c => c
        end
  end.
  
Lemma string_lt_empty a s (H: string_lt (String a s) "") : False.
Proof.
  remember (String a s) as s'; remember EmptyString as e. destruct H.
  + inversion Heqs'.
  + inversion Heqe.
  + inversion Heqe.
Qed.

Inductive stringEq : string -> string -> Prop :=
| s_empty : stringEq EmptyString EmptyString 
| s_cons a b s t : a === b -> stringEq s t -> stringEq (String a s) (String b t).                       

Instance StringEqEquiv : Equivalence stringEq.
Proof.
  split.
  + unfold Reflexive; intros x; induction x.
    apply s_empty. apply s_cons; [reflexivity | assumption].
  + unfold Symmetric; intros x y Hxy.
    induction Hxy. apply s_empty.
    apply s_cons; [symmetry|]; assumption.
  + unfold Transitive; intros x y z Hxy Hyz. generalize dependent z; 
    induction Hxy; intros; inversion Hyz.
    apply s_empty.
    inversion Hyz; subst.
    apply s_cons. transitivity b; assumption.
    apply IHHxy. assumption.
Qed.

Instance StrictOrderString : StrictOrder string_lt stringEq.
Proof.
  split.
  + intros a b c Hab Hac. generalize dependent c. induction Hab. 
    * intros c Hac. destruct c. apply string_lt_empty in Hac. destruct Hac.
      apply s_emp.
    * intros c Hac. destruct c. apply string_lt_empty in Hac. destruct Hac.
      inversion Hac; subst.
      - apply s_neq. etransitivity; eassumption.
      - apply s_neq. rewrite H3 in H. assumption.
    * intros c Hac. destruct c.  apply string_lt_empty in Hac. destruct Hac.
      inversion Hac; subst.
      - apply s_neq. rewrite <- H in H1. assumption.
      - apply s_eq. etransitivity; eassumption. apply IHHab; assumption.
  + intros x y Hxy H; induction Hxy.
    * inversion H.
    * inversion H; subst; rewrite H4 in H0. apply lt_antirefl in H0. destruct H0.
    * apply IHHxy. inversion H; subst. apply H6.
Qed.

Instance OrderedTypeString : OrderedType string := {
   _eq := stringEq;
   _lt := string_lt;
   _cmp := string_compare
}.
Proof.  
  intros x. induction x.
  + intros y. destruct y; simpl; try (repeat constructor).
  + intros y. destruct y; simpl; try (repeat constructor).    
    destruct (compare_dec a a0).
    * apply compare_spec_lt. apply s_neq. assumption.
    * eapply compare_spec_ind; [| | | apply IHx]; intros H1.
      - apply compare_spec_lt. apply s_eq; assumption.
      - apply compare_spec_eq. apply s_cons; assumption.
      - apply compare_spec_gt. apply s_eq; [symmetry|]; assumption.
    * apply compare_spec_gt. apply s_neq; assumption.
Qed.

Section SepAlgMap.
  Context {K} `{H: FMap K}.
  Context `{Spec: FMapSpecs K}.

  Instance MapSepAlgOps A : SepAlgOps (Map [K, A]) := {
    sa_unit m := Empty m;
    sa_mul :=  fun a b c => 
                 forall k, match find k c with
                             | Some y  => (MapsTo k y a /\ ~ In k b) \/ 
                                          (MapsTo k y b /\ ~ In k a)
                             | None => ~ In k a /\ ~ In k b
                           end
  }.

  Definition map_unit {A : Type} : Map [K, A] := empty A.

  Lemma sa_mul_add {A : Type} {a b c : Map [K, A]} {k : K} {y : A}
    (Habc : sa_mul a b c) (Hnotin : ~ In k b) :
      sa_mul (add k y a) b (add k y c).
  Proof.
    simpl in *; intros l.
    destruct (eqb_dec k l) as [e | e].
    rewrite add_eq_o; [|assumption].
    left; split.
    rewrite find_mapsto_iff. rewrite add_eq_o; [reflexivity | assumption].
    rewrite <- e. assumption.
    rewrite add_neq_o; [|assumption].
    specialize (Habc l); destruct (find l c).
    destruct Habc as [Habc | Habc].
    left. rewrite add_neq_mapsto_iff; assumption.
    right. rewrite add_neq_in_iff; assumption.
    rewrite add_neq_in_iff; assumption.
  Qed.

  Lemma sa_mul_remove {A : Type} {a b c : Map [K, A]} {k : K}
    (Habc : sa_mul a b c) (Hnotin : ~ In k b) :
      sa_mul (remove k a) b (remove k c).
  Proof.
    simpl in *; intros l.
    destruct (eqb_dec k l) as [e | e].
    * rewrite remove_eq_o; [| assumption].
      split; [| rewrite <- e; assumption ].
      intro Hfail; destruct Hfail as [? Hfail].
      rewrite e in Hfail. apply find_mapsto_iff in Hfail.
      rewrite remove_eq_o in Hfail; [| reflexivity ].
      inversion Hfail.
    * rewrite remove_neq_o; [| assumption ].
      specialize (Habc l).
      destruct (find l c).
      + destruct Habc.
        - left. split; [ | apply H2 ].
          apply remove_mapsto_iff; split; [ assumption | apply H2].
        - right. split; [ apply H2 |].
          intro Hfail.
          destruct H2 as [_ H2]; apply H2.
          destruct Hfail as [? Hfail].
          exists x. apply remove_mapsto_iff in Hfail. apply Hfail. 
      + split; [ | apply Habc].
        intro Hfail. destruct Habc as [Habc _]; apply Habc.
        destruct Hfail as [? Hfail].
        exists x; apply remove_mapsto_iff in Hfail. apply Hfail.
  Qed.
   
  Lemma sa_mul_inL {A : Type} {a b c : Map [K, A]} {k : K} 
        (Habc : sa_mul a b c) (Hin: In k a) : ~ In k b /\ In k c.
  Proof.        
    simpl in Habc.
    specialize (Habc k).
    remember (find k c) as o; destruct o; intuition.
    rewrite in_find_iff. rewrite <- Heqo. congruence.
  Qed.

  Lemma subheap_add {A : Type} k v (a b : Map [K, A]) (Hsub : subheap a b) 
        (Hin : In k a) :
    subheap (add k v a) (add k v b). 
  Proof.
    destruct Hsub as [c Hsub]; destruct (sa_mul_inL Hsub Hin).
    exists c. apply sa_mul_add; assumption.
  Qed.        

  Lemma sa_mul_inR {A : Type} {a b c : Map [K, A]} {k : K}
        (Habc : sa_mul a b c) (Hin: In k c) :
    (In k a /\ ~ In k b) \/ (In k b /\ ~ In k a).
  Proof.
    simpl in Habc. specialize (Habc k).
    rewrite in_find_iff in Hin.
    destruct (find k c); [|intuition].
    destruct Habc as [[H2 H3] | [H2 H3]]; [left | right]; split; try assumption;
    rewrite in_find_iff;
    rewrite find_mapsto_iff in H2; rewrite H2; intuition.
  Qed.

  Lemma sa_mul_swapL {A : Type} {a b c : Map [K, A]} {k : K} {v: A}
        (Habc : sa_mul a b c) (Hmapsto: MapsTo k v c) :
        sa_mul (add k v a) (remove k b) c.
  Proof.
    simpl. intro k'.
    simpl in Habc. specialize (Habc k').
	destruct (eq_dec k k') as [Heq | Hneq].
	+ eapply MapsTo_iff in Hmapsto; [| symmetry in Heq; apply Heq].
	  apply find_mapsto_iff in Hmapsto. rewrite Hmapsto in Habc.
      rewrite Hmapsto.
      left. split.
      apply add_1; apply Heq.
      apply remove_1; apply Heq.
    + destruct (find k' c).
      * destruct Habc as [Habc | Habc]; destruct Habc as [Habc_mapsto Habc_notin].
        - left. split.
          eapply add_neq_mapsto_iff; assumption.
          intro Hcounter. apply Habc_notin.
          eapply remove_neq_in_iff; [apply Hneq | apply Hcounter].
        - right. split.
          apply remove_neq_mapsto_iff; assumption.
          intro Hcounter. apply Habc_notin.
          eapply add_neq_in_iff; [apply Hneq | apply Hcounter].
       * destruct Habc as [Habc_a Habc_b].
         split.
         intro Hcounter. apply Habc_a.
         eapply add_neq_in_iff; [apply Hneq | apply Hcounter].
         intro Hcounter. apply Habc_b.
         eapply remove_neq_in_iff; [apply Hneq | apply Hcounter].
  Qed.

  Lemma subheap_addL {A: Type} {h h': Map [K, A]} {k: K} {v: A}
    (Hmapsto: MapsTo k v h) (Hsubheap: subheap h' h) :
    subheap (add k v h') h.
  Proof.
    unfold subheap in *. destruct Hsubheap as [h'' Hsubheap].
    assert (sa_mul h' h'' h) as Hsubheap' by assumption.
    eapply sa_mul_inR in Hsubheap'; [| unfold In; exists v; apply Hmapsto].
    destruct Hsubheap' as [Hsubheap' | Hsubheap']; destruct Hsubheap' as [Hin Hnotin].
    + exists h''.
      simpl. intro k'. simpl in Hsubheap. specialize (Hsubheap k').
      destruct (eq_dec k k') as [Heq | Hneq].
      * eapply MapsTo_iff in Hmapsto; [| symmetry in Heq; apply Heq].
        apply find_mapsto_iff in Hmapsto. rewrite Hmapsto in Hsubheap.
        rewrite Hmapsto.
        left. split.
        apply add_1; (apply Heq).
        intro Hcounter. apply Hnotin.
        eapply In_iff; [apply Heq | apply Hcounter ].
      * destruct (find k' h).
        - destruct Hsubheap as [Hsubheap | Hsubheap]; destruct Hsubheap as [Hsh_mapsto Hsh_notin].
          left. split.
          eapply add_neq_mapsto_iff; assumption.
          apply Hsh_notin.
          right. split.
          apply Hsh_mapsto.
          intro Hcounter. apply Hsh_notin.
          apply -> add_neq_in_iff; [apply Hcounter | apply Hneq].
        - destruct Hsubheap as [Hnotin_h' Hnotin_h''].
          split.
          intro Hcounter. apply Hnotin_h'.
          eapply add_neq_in_iff; [apply Hneq | apply Hcounter].
          apply Hnotin_h''.
    + exists (remove k h'').
      apply sa_mul_swapL; assumption.
  Qed.

  Lemma sa_mul_mapstoL {A : Type} {a b c : Map [K, A]} {k : K} {y : A}
        (Habc: sa_mul a b c) (Hc: MapsTo k y a) : MapsTo k y c /\ ~ In k b.
  Proof.
    simpl in Habc; specialize (Habc k).
    rewrite find_mapsto_iff in Hc. remember (find k c) as o; destruct o.
    + destruct Habc as [[H2 H3] | [H2 H3]].
      * rewrite find_mapsto_iff in H2; rewrite H2 in Hc. inversion Hc; subst.
        rewrite find_mapsto_iff; split; auto.
      * rewrite not_find_in_iff in H3. congruence.
    + destruct Habc as [H2 _].
      rewrite not_find_in_iff in H2; congruence.
  Qed.
    
  Lemma sa_mul_mapstoR {A : Type} {a b c : Map [K, A]} {k : K} {y : A}
        (Habc: sa_mul a b c) (Hc: MapsTo k y c) :
    (MapsTo k y a /\ ~ In k b) \/ (MapsTo k y b /\ ~ In k a).
  Proof.
    simpl in Habc.
    specialize (Habc k).
    rewrite find_mapsto_iff in Hc. destruct (find k c); inversion Hc; subst.
    assumption.
  Qed.
    
  Lemma sa_mul_mapstoRT {A : Type} {a b c : Map [K, A]} {k : K} {y : A}
        (Habc: sa_mul a b c) (Hc: MapsTo k y c) :
    (MapsTo k y a /\ ~ In k b) + (MapsTo k y b /\ ~ In k a).
  Proof.
	admit. (* THIS IS NOT CORRECT!!! *)
  Admitted.
    
  Lemma map_sa_mul_notinR {A : Type} {a b c : Map [K, A]} {k : K}
        (Habc: sa_mul a b c) (Hc: ~ In k c) :
    ~ In k a /\ ~ In k b.
  Proof.
    simpl in Habc.
    specialize (Habc k).
    rewrite not_find_in_iff in Hc.
    rewrite Hc in Habc; apply Habc.
  Qed.
        
  
        
  Lemma find_fold_none A x (a b : dict K A) :
    find x (fold add a b) = None <->
    find x a = None /\ find x b = None.
  Proof.
    apply fold_rec_weak.
    intros. rewrite <- H2. apply H3.
    rewrite empty_o. intuition.
    intros.
    repeat rewrite add_o.
    destruct (k == x);
    intuition congruence.
  Qed.

 Lemma find_fold_some_left A x (a b : dict K A) y :
   find x (fold add a b) = Some y ->
   find x a = Some y \/ find x b = Some y.
 Proof.
   apply fold_rec_weak.
   intros. rewrite <- H2. apply H3. apply H4.
   rewrite empty_o. intuition. 
   intros. rewrite add_o.
   destruct (eq_dec k x). rewrite add_eq_o in H4; intuition.
   rewrite add_neq_o in H4; intuition.
 Qed. 

 Lemma find_fold_some_right A x (a b : dict K A) y :
   (find x a = Some y /\ find x b = None) \/ 
   (find x b = Some y /\ find x a = None) ->
   find x (fold add a b) = Some y.
 Proof.
   apply fold_rec.
   + intros m Hm [[H2 H3] | [H2 H3]].
     unfold Empty in Hm.
     assert False. eapply Hm. rewrite find_mapsto_iff. apply H2. destruct H4.
     apply H2.
   + intros k e c m' m'' Ha Hm' Hm'' IH [[H2 H3] | [H2 H3]];
     unfold Add in Hm''; rewrite find_mapsto_iff in Ha;
     rewrite add_o; destruct (eq_dec k x).
     * rewrite Hm'' in H2. rewrite add_eq_o in H2; assumption.
     * rewrite Hm'' in H2. rewrite add_neq_o in H2; intuition.
     * rewrite Hm'' in H3. rewrite add_eq_o in H3. inversion H3. assumption.
     * apply IH; rewrite Hm'' in H3. rewrite add_neq_o in H3; intuition.
 Qed. 
 
 Lemma find_not_not A (a : Map [K, A]) x (Haoeu : ~~(a [x] = None)) : a [x] = None.
 Proof.
   remember (a [x]) as o.
   destruct o; simpl in *; intuition congruence.
 Qed.

 

 Ltac SepOpSolve :=
    match goal with
      | H : sa_mul _ _ _ |- _ => unfold sa_mul in H; simpl in H; SepOpSolve
      | H : ~ (find ?k ?d) <> None |- _ => apply find_not_not in H; SepOpSolve
      | H : (match find ?k ?d with | Some _ => _ | None => _ end) |- _ =>
        let e := fresh "e" in let y := fresh "y" in remember (find k d) as e;
            destruct e as [y |]; SepOpSolve
      | H : _ \/ _ |- _ => destruct H as [H | H]; SepOpSolve
      | H : _ /\ _ |- _ => let H1 := fresh "H" in destruct H as [H H1]; SepOpSolve
      | |- context [match find ?x (fold add ?a ?b) with | Some _ => _ | None => _ end] =>
        let e := fresh "e" in 
        let H := fresh "Heq" e in 
        remember (find x (fold add a b)) as e;
        symmetry in H; destruct e;
        [apply find_fold_some_left in H |
         rewrite find_fold_none in H]; SepOpSolve
      | H : forall x : K, _ |- _ => 
                   match goal with
                       | x : K |- _ => specialize (H x)
                   end; SepOpSolve
      | |- context [find _ (fold add _ _) = None] =>
        rewrite find_fold_none; SepOpSolve
      | |- context [MapsTo _ _ _] => repeat rewrite find_mapsto_iff; SepOpSolve
      | |- context [In _ _] => repeat rewrite in_find_iff; SepOpSolve
      | H : context [MapsTo _ _ _] |- _ => rewrite find_mapsto_iff in H; SepOpSolve
      | H : context [In _ _] |- _ => rewrite in_find_iff in H; SepOpSolve
      | |- context [find _ (fold add _ _) = Some _] =>
        first [intuition congruence | 
        try (erewrite find_fold_some_right; intuition congruence)]
      | _ => subst; try intuition congruence
    end.
 
 Require Import SepAlg Rel.

  Definition MapEquiv A : Rel (Map [K, A]) := Equal.
  Local Existing Instance MapEquiv.

  Definition MapSepAlg A : SepAlg (Map [K, A]).
  Proof.
  	esplit. 
    + intros * H3 k; SepOpSolve.  
    + intros * H2 H3.
      exists (fold add b c).
      split; intro x; SepOpSolve.
    + intros *. exists (empty A); split.
      * unfold sa_unit; simpl; apply empty_1.
      * simpl; intros. remember (a [k]) as o. destruct o.
        - rewrite find_mapsto_iff, empty_in_iff; intuition.
        - rewrite in_find_iff, empty_in_iff; intuition.
    + intros * H2 H3 k. 
      unfold sa_mul, sa_unit in *; simpl in *.
      SepOpSolve. unfold Empty in H2. specialize (H2 k y). SepOpSolve.
    + intros a b Hab. split; intros H2 k x H3; simpl in H2; specialize (H2 k x);
      unfold Equivalence.equiv, rel, MapEquiv, Equal in Hab;
	  apply H2; SepOpSolve.
	+ intros * H2 H3 k. simpl in *. SepOpSolve.
  Qed.
  
  Local Existing Instance MapSepAlg.

  Definition UUMapSepAlg A : @UUSepAlg (Map [K, A]) _ _.
  Proof.
  	split.
  	+ apply MapSepAlg.
  	+ intros m u Hu x. simpl in Hu. remember (m [x]) as e. destruct e.
  	  * left. rewrite find_mapsto_iff, in_find_iff. split; [intuition | intros H2; apply H2].
  	    rewrite elements_o; apply elements_Empty in Hu. rewrite Hu. reflexivity.
  	  * rewrite in_find_iff. split. intros H2. congruence.
  	    rewrite in_find_iff. intros H2. apply H2.
  	    apply elements_Empty in Hu. rewrite elements_o, Hu. reflexivity.
  Qed.

  Lemma sa_mul_Disjoint {A : Type} {a b c : Map [K, A]}
        (Habc: sa_mul a b c) : Disjoint a b.
  Proof.
    unfold Disjoint.
    intros k Hcounter.
    destruct Hcounter as [Hina Hinb].
    eapply sa_mul_inL in Habc; [| apply Hina]; destruct Habc as [Hnotinb Hinc].
    auto.
  Qed.

  Lemma Disjoint_sa_mul {A : Type} {a b : Map [K, A]}
        (Hdisjoint: Disjoint a b) : sa_mul a b (update a b).
  Proof.
    unfold Disjoint.
    simpl.
    intro k.
    remember (find k (update a b)).
    unfold Disjoint in Hdisjoint; specialize (Hdisjoint k).
    destruct o.
    * symmetry in Heqo; apply find_mapsto_iff in Heqo.
      apply update_mapsto_iff in Heqo.
      destruct Heqo as [Hmapsto | [Hmapsto Hnotin]].
      + right. split; [ assumption |].
        intro Hcounter; apply Hdisjoint.
        split; [assumption |].
        unfold In; exists a0; assumption.
      + left; auto.
    * symmetry in Heqo; apply not_find_in_iff in Heqo.
      split; intro Hcounter; apply Heqo; clear Heqo.
      + apply update_in_iff; auto.
      + apply update_in_iff; auto.
  Qed.

  Lemma sa_mul_Partition {A : Type} {a b c : Map [K, A]} :
        sa_mul a b c <-> Partition c a b.
  Proof.
    split.
    * intro Habc. unfold Partition.
      split; [eapply sa_mul_Disjoint; apply Habc |].
      intros k v.
      split; intro.
      + eapply sa_mul_mapstoR in H2; [| apply Habc].
        destruct H2 as [[Hmapsto Hnotin] | [Hmapsto Hnotin]]; auto.
      + destruct H2 as [Hina | Hinb].
        - eapply sa_mul_mapstoL in Hina; [| apply Habc]; destruct Hina as [Hina _].
          assumption.
        - apply sa_mulC2 in Habc.
          eapply sa_mul_mapstoL in Hinb; [| eapply Habc]; destruct Hinb as [Hinb _].
          assumption.
    * intro Hpartition.
      unfold Partition in Hpartition; destruct Hpartition as [Hdisjoint Hmapsto].
      unfold Disjoint in Hdisjoint.
      simpl; intro k.
      remember (find k c); destruct o.
      + symmetry in Heqo; apply find_mapsto_iff in Heqo.
        specialize (Hmapsto k a0).
        specialize (Hdisjoint k).
        apply Hmapsto in Heqo.
        destruct Heqo.
        - left. split; [ assumption |].
          intro Hcounter. apply Hdisjoint.
          split; [| assumption].
          unfold In. exists a0. assumption.
        - right. split; [ assumption |].
          intro Hcounter. apply Hdisjoint.
          split; [assumption |].
          unfold In. exists a0. assumption.
      + symmetry in Heqo; apply not_find_in_iff in Heqo.
        split; intro Hcounter; apply Heqo; clear Heqo.
        - unfold In in Hcounter; destruct Hcounter as [e Hcounter].
          unfold In. exists e.
          apply Hmapsto. left; apply Hcounter.
        - unfold In in Hcounter; destruct Hcounter as [e Hcounter].
          unfold In. exists e.
          apply Hmapsto. right; assumption.
  Qed.

  Lemma sa_mul_MapResEq {A : Type} {a b c c' : Map [K, A] }
    (Habc : sa_mul a b c) (Habc' : sa_mul a b c') :
    c === c'.
  Proof.
    simpl in *.
    unfold "===". unfold Equal.
    intro k.
    specialize (Habc k); specialize (Habc' k).
    remember (find k c) as fc.
    remember (find k c') as fc'.
    destruct fc; destruct fc'.
    * destruct Habc as [[Habc_a Habc_b] | [Habc_a Habc_b]];
      destruct Habc' as [[Habc'_a Habc'_b] |[Habc'_a Habc'_b]].
      - apply find_mapsto_iff in Habc_a; apply find_mapsto_iff in Habc'_a.
        rewrite Habc_a in Habc'_a. assumption.
      - exfalso; apply Habc'_b.
        unfold In; exists a0; assumption.
      - exfalso; apply Habc'_b.
        unfold In; exists a0; assumption.
      - apply find_mapsto_iff in Habc_a; apply find_mapsto_iff in Habc'_a.
        rewrite Habc_a in Habc'_a. assumption.
    * destruct Habc as [[Habc_a Habc_b]|[Habc_a Habc_b]];
      destruct Habc' as [Habc'_a Habc'_b].
      + exfalso; apply Habc'_a.
        unfold In; exists a0; assumption.
      + exfalso; apply Habc'_b.
        unfold In; exists a0; assumption.
    * destruct Habc' as [[Habc'_a Habc'_b]|[Habc'_a Habc'_b]];
      destruct Habc as [Habc_a Habc_b].
      + exfalso; apply Habc_a.
        unfold In; exists a0; assumption.
      + exfalso; apply Habc_b.
        unfold In; exists a0; assumption.
    * reflexivity.
Qed.

Lemma map_sa_mul_combined_subheap {A : Type} {a a1 a2 b : Map [K, A]}
    (Hamul: sa_mul a1 a2 a) (Ha1sub: subheap a1 b) (Ha2sub: subheap a2 b) :
    subheap a b.
  Proof.
    destruct Ha1sub as [a1' Ha1sub].
    destruct Ha2sub as [a2' Ha2sub].
    exists (restrict a1' a2').
    intro k. specialize (Ha1sub k); specialize (Ha2sub k).
    remember (find k b); destruct o.
    destruct Ha1sub as [[Ha1subMT Ha1subNin] | [Ha1subMT Ha1subNin]].
    eapply sa_mul_mapstoL in Hamul; [| apply Ha1subMT]; destruct Hamul as [HaMT HaNin].
    destruct Ha2sub as [[Ha2subMT _] | [Ha2subMT _]]; [exfalso; apply HaNin; exists a0; apply Ha2subMT |]. 
    left; split; [assumption |].
    intro Hfail; apply Ha1subNin; apply restrict_in_iff in Hfail; apply Hfail.
    destruct Ha2sub as [[Ha2subMT Ha2subNin] | [Ha2subMT Ha2subNin]].
    apply sa_mulC in Hamul; eapply sa_mul_mapstoL in Hamul; [| apply Ha2subMT]; destruct Hamul as [Hamul _].
    left; split; [assumption | ].
    intro Hfail; apply Ha2subNin; apply restrict_in_iff in Hfail; apply Hfail.
    right; split; [apply restrict_mapsto_iff; split; [assumption | exists a0; assumption] |].
    intro Hfail; eapply sa_mul_inR in Hamul; [| apply Hfail]; destruct Hamul; intuition.
    split; intro Hfail;
      [  eapply sa_mul_inR in Hamul; [| apply Hfail]; destruct Hamul; intuition
      | apply restrict_in_iff in Hfail; intuition].
Qed.

End SepAlgMap.