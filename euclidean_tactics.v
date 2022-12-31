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

Ltac InCirc_Within_Radius P J CI_J_U_VW BetS_U_Y_X Cong_UX_VW Cong_UP_UY :=
	unfold InCirc;
	repeat eexists;
	repeat match goal with
		| |- CI _ _ _ _ => exact CI_J_U_VW
	end;
	right;
	repeat split;
	repeat match goal with
		| |- BetS _ _ _ => exact BetS_U_Y_X
	end;
	repeat match goal with
		| |- Cong _ _ _ _ => exact Cong_UX_VW
	end;
	repeat match goal with
		| |- Cong _ _ _ _ => exact Cong_UP_UY
	end
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
