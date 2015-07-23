Require Import SepAlg Rel OrderedType.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section UUSepAlg.
	Context {A : Type} `{SA : SepAlg A}.
	
	Class UUSepAlg := {
	    uusa          :> SepAlg A;
		uusa_unit a u : sa_unit u -> sa_mul a u a
	}.
	
End UUSepAlg.

Section SepAlgUniqueUnit.
	Context {A : Type} `{SA : UUSepAlg A}.

	Lemma sep_alg_unique_unit u1 u2 (Hu1 : sa_unit u1) (Hu2 : sa_unit u2) : u1 === u2.
	Proof.
		pose proof (uusa_unit u1 Hu2) as H.
		apply sa_mulC in H. apply sa_unit_eq in H; eassumption.
	Qed.
	
End SepAlgUniqueUnit.

Implicit Arguments UUSepAlg [[e] [SAOps]].