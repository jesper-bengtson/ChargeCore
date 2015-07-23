Require Import Setoid Morphisms Rel.
Require Import SepAlg UUSepAlg String List.
Require Import Program.Basics Program.Tactics Program.Syntax.
Require Import OrderedType.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Inductive partial (A : Type) :=
| Undefined : partial A
| Defined : A -> partial A.

Implicit Arguments Undefined [[A]].
Implicit Arguments Defined [[A]].

Section PartialFun.

  (* A partial function is a function from X -> option Y where X equality of members
     of type X is decidable. *)

  Context {X Y : Type} {HDec: DecidableEq X}.

  Definition pfun := X -> partial Y.

  Definition pfun_eq (f1 f2 : pfun) := forall s, f1 s = f2 s.
  Global Instance pfunEquiv : Rel pfun | 0 := {rel := pfun_eq}.
  Global Instance EquivalencePfun : Equivalence rel.
  Proof. 
    split; intuition congruence.
  Qed.

  Definition emptyFun : pfun := fun _ => Undefined.
  
  Definition pfun_update (f : pfun) (x : X) (y : Y) :=
    fun z => if dec_eq x z then Defined y else f z.

  Lemma update_shadow (f : pfun) (x : X) (y1 y2 : Y) :
    pfun_update (pfun_update f x y1) x y2 === pfun_update f x y2.
  Proof.
      unfold pfun_update; intro z; destruct (dec_eq x z); reflexivity.
  Qed.

  Lemma update_lookup (f : pfun) (x : X) (y : Y) :
    (pfun_update f x y) x = Defined y.
  Proof.
    unfold pfun_update. 
    destruct (dec_eq x x); [reflexivity| congruence].
  Qed.

  Lemma update_lookup_neq (f : pfun) (x z : X) (y : Y) (H: x <> z) :
    (pfun_update f x y) z = f z.
  Proof.
    unfold pfun_update.
    destruct (dec_eq x z); [congruence| reflexivity].
  Qed.

  Lemma update_commute (f : X -> partial Y) (x1 x2 : X) (y1 y2 : Y) (H : x1 <> x2) :
    pfun_update (pfun_update f x1 y1) x2 y2 === pfun_update (pfun_update f x2 y2) x1 y1.
  Proof.
    unfold pfun_update; intro z.
    destruct (dec_eq x2 z); destruct (dec_eq x1 z); try reflexivity.
    subst. firstorder.
  Qed.

  Ltac SepOpSolve :=
    match goal with
      | H : (match ?f ?x with | Defined _ => _ | Undefined => _ end) |- _ =>
        let e := fresh "e" in let y := fresh "y" in remember (f x) as e;
            destruct e as [y |]; SepOpSolve
      | H : _ \/ _ |- _ => destruct H as [H | H]; SepOpSolve
      | H : _ /\ _ |- _ => let H1 := fresh "H" in destruct H as [H H1]; SepOpSolve
      | H : ?f ?x = _ |- context [match ?f ?x with | Defined _ => _ | Undefined => _ end] =>
        rewrite H; SepOpSolve
      | H : forall x : X, _ |- _ => 
                   match goal with
                       | x : X |- _ => specialize (H x)
                   end; SepOpSolve
      | _ => subst; try intuition congruence
    end.

  (* We can create a separation algebra for partial functions with the following
     definitions for sa_unit and sa_mul *)

  Global Instance PFunSepAlgOps : SepAlgOps (X -> partial Y) := {
     sa_unit f := f === emptyFun;
     sa_mul    := fun a b c => forall x,
                    match c x with
                      | Defined y => (a x = Defined y /\ b x = Undefined) \/ 
                                     (b x = Defined y /\ a x = Undefined)
                      | Undefined => a x = Undefined /\ b x = Undefined
                    end

  }.

  (* Proving that partial functions actually form a separation algebra is straightforward
     modulo some LTac magic. *)

  Global Instance PFunSepAlg : SepAlg (X -> partial Y).
  Proof.
  	esplit; simpl.
	+ intros * H x. SepOpSolve.
	+ intros * H1 H2.
      exists (fun x => 
                  match b x with
                    | Defined y => Defined y
                    | Undefined => c x
                  end).
      split; intro x; SepOpSolve.
    + intros; exists emptyFun. split; [reflexivity | intros x].
      remember (a x) as p; destruct p; simpl; intuition.
    + intros * H H1. unfold equiv, rel, pfunEquiv, pfun_eq, emptyFun in H; simpl in H.
      intros k. SepOpSolve. 
	+ intros a b Hab; split; intros H1 x; unfold emptyFun in *; specialize (H1 x); simpl in H1;
	  SepOpSolve.
	+ intros * Hab H1 x; SepOpSolve.
 Qed.

  Definition UUMapSepAlg : @UUSepAlg (X -> partial Y) _ _.
  Proof.
  	split.
  	+ apply _.
  	+ intros m u Hu x. simpl in Hu. remember (m x) as e. destruct e.
  	  * split; [intuition|]. specialize (Hu x). intuition.
  	  * left; split; [intuition|]. specialize (Hu x); intuition.
  Qed.  

End PartialFun.

