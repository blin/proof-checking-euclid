Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.euclidean_axioms.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_n_ncol_col :
	forall A B C,
	~ nCol A B C ->
	Col A B C.
Proof.
	intros A B C.
	intros Col_A_B_C.

	unfold nCol in Col_A_B_C.
	unfold neq in Col_A_B_C.

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [eq_A_B | Col_A_B_C].
	{
		apply Classical_Prop.NNPP in eq_A_B.
		pose proof (by_def_Col_from_eq_A_B A B C eq_A_B) as Col_A_B_C.
		exact Col_A_B_C.
	}

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [eq_A_C | Col_A_B_C].
	{
		apply Classical_Prop.NNPP in eq_A_C.
		pose proof (by_def_Col_from_eq_A_C A B C eq_A_C) as Col_A_B_C.
		exact Col_A_B_C.
	}

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [eq_B_C | Col_A_B_C].
	{
		apply Classical_Prop.NNPP in eq_B_C.
		pose proof (by_def_Col_from_eq_B_C A B C eq_B_C) as Col_A_B_C.
		exact Col_A_B_C.
	}

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [BetS_A_B_C | Col_A_B_C].
	{
		apply Classical_Prop.NNPP in BetS_A_B_C.
		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_B_C) as Col_A_B_C.
		exact Col_A_B_C.
	}

	apply Classical_Prop.not_and_or in Col_A_B_C.
	destruct Col_A_B_C as [BetS_A_C_B | BetS_B_A_C].
	{
		apply Classical_Prop.NNPP in BetS_A_C_B.
		pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_A_C_B) as Col_A_B_C.
		exact Col_A_B_C.
	}
	{
		apply Classical_Prop.NNPP in BetS_B_A_C.
		pose proof (by_def_Col_from_BetS_B_A_C _ _ _ BetS_B_A_C) as Col_A_B_C.
		exact Col_A_B_C.
	}

Qed.

End Euclid.
