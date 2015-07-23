Require Import Stack Rel.
Require Import List OrderedType FunctionalExtensionality.

Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section Expr.
  Definition OpenType := Type. (* To combat universe inconsistencies *)

  Context {A val : OpenType} {HR : RelDec (@eq A)} {HROk : RelDec_Correct HR}.
  Context {V : ValNull val}.

  Definition open B : Type := stack A val -> B.

  Program Definition lift {A B} (f : A -> B) (a : open A) : open B := 
    fun x => f (a x).

  Definition expr := open val.

  Global Instance OpenEquiv {X} : Rel (open X) := { rel e1 e2 := forall s, e1 s = e2 s }.
  Instance OpenEquivalence {X} : Equivalence (@rel (open X) _).
  Proof.
    split; intuition congruence.
  Qed.
  
  Definition open_const {B : Type} (b : B) : open B := fun s => b.
  
  Definition V_expr (v : val) : expr := fun s => v.
  Definition var_expr (x : A) : expr := fun s => s x.
  Definition empty_open : expr := fun x => null.

  Definition uncurry {A B C} (f : A -> B -> C) : (A * B) -> C := 
    fun x => f (fst x) (snd x).
  Definition curry {A B C} (f : A * B -> C) : A -> B -> C :=
    fun x y => f (x, y).
  Program Definition opair {B C} (b : open B) (c : open C) : open ((B * C)%type) :=
    fun x => (b x, c x).

  Fixpoint Tprod (Ts : list Type) : Type :=
    match Ts with
      | nil => unit
      | cons T Ts => (T * Tprod Ts)%type
    end.

  Fixpoint my_arrows (Ts : list Type) (R : Type) : Type := 
    match Ts with
      | nil => R
      | T :: Ts => T -> my_arrows Ts R
    end.

  Class MyEq {A} (P Q : A) := {
    term_eq : P = Q
  }.

  Global Instance MyEqNil {A} : MyEq A (my_arrows nil A) | 20.
  Proof.
    simpl. split. reflexivity.
  Defined.

  Global Instance MyEqCons {A B Ts R} (H : MyEq B (my_arrows Ts R)) : 
    MyEq (A -> B) (my_arrows (A::Ts) R) | 10.
  Proof.
    split. simpl.
    destruct H.
    rewrite term_eq0.
    reflexivity.
  Defined.

  Fixpoint curry_fun Ts R : my_arrows Ts R -> (Tprod Ts) -> R :=
    match Ts with
      | nil => fun f => fun _ => f
      | T :: Ts => fun f x => curry_fun (f (fst x)) (snd x)
    end.

  Fixpoint uncurry_open Ts R :
    (open (Tprod Ts) -> open R) -> my_arrows (map open Ts) (@open R) :=
    match Ts with 
      | nil => fun f => f (fun x => tt)
      | T :: Ts =>  fun f => fun x => uncurry_open (fun y => f (opair x y))
    end.

  Program Definition liftn {T Ts R} {H: MyEq T (my_arrows Ts R)} (f : T) :=
    uncurry_open (lift (curry_fun (eq_rect T (@id Type) f _ (@term_eq _ _ _ H)))).

End Expr.

Notation "'`' x" := (liftn x) (at level 9).
Notation "'`(' x ')'" := (liftn x) (only parsing).
Notation "x '/V'" := (var_expr x) (at level 9, format "x /V").

Section SimultAdd.
  Context {A val} {HR : RelDec (@eq A)} {V: ValNull val}.

  Definition simult_add_pair_list_stack lst (s s' : stack A val) :=
    fold_right (fun v:A * expr => fun s' => stack_add (fst v) (snd v s) s') s' lst.

End SimultAdd.

  Notation " xs ':@:' s '+:+' s' " := (simult_add_pair_list_stack xs s s')
                                        (at level 69, right associativity).
