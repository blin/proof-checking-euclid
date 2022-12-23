Require Import ProofCheckingEuclid.euclidean_axioms.

Ltac InCirc_Centre C J CI_J_C_CR :=
	unfold InCirc;
	(*
		I can't figure out how to eexist these two variables
		without them being shelved and later being hard to get rid of.
	*)
	exists C, C;
	repeat eexists;
	repeat match goal with
		| |- CI _ _ _ _ => exact CI_J_C_CR
	end;
	left;
	reflexivity
	.

Ltac OutCirc_Beyond_Perimeter B J CI_J_C_CR BetS_C_R_B Cong_CR_CR :=
	unfold OutCirc;
	repeat eexists;
	repeat match goal with
		| |- CI _ _ _ _ => exact CI_J_C_CR
	end;
	repeat match goal with
		| |- BetS _ _ _ => exact BetS_C_R_B
	end;
	repeat match goal with
		| |- Cong _ _ _ _ => exact Cong_CR_CR
	end
	.

Ltac OnCirc_Radius C R CI_J_C_CR Cong_CR_CR :=
	unfold OnCirc;
	repeat eexists;
	repeat match goal with
		| |- CI _ _ _ _ => exact CI_J_C_CR
	end;
	repeat match goal with
		| |- Cong _ _ _ _ => exact Cong_CR_CR
	end
	.
