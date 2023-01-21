Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABD_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_supporting_n_ncol_col.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinear_ABC_ABD_BCD :
	forall A B C D,
	Col A B C ->
	Col A B D ->
	neq A B ->
	Col B C D.
Proof.
	intros A B C D.
	intros Col_A_B_C.
	intros Col_A_B_D.
	intros neq_A_B.

	(* get rid of eq_A_B early to reduce number of permutations *)
	destruct Col_A_B_C as [eq_A_B | Col_A_B_C].
	contradiction neq_A_B.
	destruct Col_A_B_D as [eq_A_B | Col_A_B_D].
	contradiction neq_A_B.

	unfold Col.

	destruct Col_A_B_C as [eq_A_C | [eq_B_C | [BetS_B_A_C | [BetS_A_B_C | BetS_A_C_B]]]].
	{
		(* case eq_A_C *)
		destruct Col_A_B_D as [ eq_A_D | [ eq_B_D | [ BetS_B_A_D | [ BetS_A_B_D | BetS_A_D_B]]]].
		{
			(* case eq_A_D *)
			assert (eq_C_D := eq_A_D).
			replace A with C in eq_C_D.
			one_of_disjunct eq_C_D.
		}
		{
			(* case eq_B_D *)
			one_of_disjunct eq_B_D.
		}
		{
			(* case BetS_B_A_D *)
			assert (BetS_B_C_D := BetS_B_A_D).
			replace A with C in BetS_B_C_D.
			one_of_disjunct BetS_B_C_D.
		}
		{
			(* case BetS_A_B_D *)
			assert (BetS_C_B_D := BetS_A_B_D).
			replace A with C in BetS_C_B_D.
			one_of_disjunct BetS_C_B_D.
		}
		{
			(* case BetS_A_D_B *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_B) as BetS_B_D_A.
			assert (BetS_B_D_C := BetS_B_D_A).
			replace A with C in BetS_B_D_C.
			one_of_disjunct BetS_B_D_C.
		}
	}
	{
		(* case eq_B_C *)
		one_of_disjunct eq_B_C.
	}
	{
		(* case BetS_B_A_C *)
		destruct Col_A_B_D as [ eq_A_D | [ eq_B_D | [ BetS_B_A_D | [ BetS_A_B_D | BetS_A_D_B]]]].
		{
			(* case eq_A_D *)
			assert (BetS_B_D_C := BetS_B_A_C).
			replace A with D in BetS_B_D_C.
			one_of_disjunct BetS_B_D_C.
		}
		{
			(* case eq_B_D *)
			one_of_disjunct eq_B_D.
		}
		{
			(* case BetS_B_A_D *)
			assert (~ nCol B C D) as Col_B_C_D.
			{
				intros nCol_B_C_D.
				unfold nCol in nCol_B_C_D.
				destruct nCol_B_C_D as (_ & _ & neq_C_D & nBetS_B_C_D & nBetS_B_D_C & _).
				assert (~ BetS A C D) as nBetS_A_C_D.
				{
					intros BetS_A_C_D.
					pose proof (
						lemma_orderofpoints_ABD_BCD_ACD _ _ _ _ BetS_B_A_D BetS_A_C_D
					) as BetS_B_C_D.
					contradiction nBetS_B_C_D.
				}
				assert (~ BetS A D C) as nBetS_A_D_C.
				{
					intros BetS_A_D_C.
					pose proof (
						lemma_orderofpoints_ABD_BCD_ACD _ _ _ _ BetS_B_A_C BetS_A_D_C
					) as BetS_B_D_C.
					contradiction nBetS_B_D_C.
				}
				pose proof (
					lemma_outerconnectivity _ _ _ _ BetS_B_A_C BetS_B_A_D nBetS_A_C_D nBetS_A_D_C
				) as eq_C_D.
				contradiction neq_C_D.
			}
			apply lemma_supporting_n_ncol_col in Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_A_B_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_C) as BetS_C_A_B.
			pose proof (
				lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_C_A_B BetS_A_B_D
			) as BetS_C_B_D.
			one_of_disjunct BetS_C_B_D.
		}
		{
			(* case BetS_A_D_B *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_B) as BetS_B_D_A.
			pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_B_D_A BetS_B_A_C) as BetS_B_D_C.
			one_of_disjunct BetS_B_D_C.
		}
	}
	{
		(* case BetS_A_B_C *)
		destruct Col_A_B_D as [ eq_A_D | [ eq_B_D | [ BetS_B_A_D | [ BetS_A_B_D | BetS_A_D_B]]]].
		{
			(* case eq_A_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_C) as BetS_C_B_A.
			assert (BetS_C_B_D := BetS_C_B_A).
			replace A with D in BetS_C_B_D.
			one_of_disjunct BetS_C_B_D.
		}
		{
			(* case eq_B_D *)
			one_of_disjunct eq_B_D.
		}
		{
			(* case BetS_B_A_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_D) as BetS_D_A_B.
			pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_D_A_B BetS_A_B_C) as BetS_D_B_C.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_C) as BetS_C_B_D.
			one_of_disjunct BetS_C_B_D.
		}
		{
			(* case BetS_A_B_D *)
			assert (~ nCol B C D) as Col_B_C_D.
			{
				intros nCol_B_C_D.
				unfold nCol in nCol_B_C_D.
				destruct nCol_B_C_D as (_ & _ & neq_C_D & nBetS_B_C_D & nBetS_B_D_C & _).
				pose proof (
					lemma_outerconnectivity _ _ _ _ BetS_A_B_C BetS_A_B_D nBetS_B_C_D nBetS_B_D_C
				) as eq_C_D.
				contradiction neq_C_D.
			}
			apply lemma_supporting_n_ncol_col in Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_A_D_B *)
			pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_D_B BetS_A_B_C) as BetS_D_B_C.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_C) as BetS_C_B_D.
			one_of_disjunct BetS_C_B_D.
		}
	}
	{
		(* case BetS_A_C_B *)
		destruct Col_A_B_D as [ eq_A_D | [ eq_B_D | [ BetS_B_A_D | [ BetS_A_B_D | BetS_A_D_B]]]].
		{
			(* case eq_A_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
			assert (BetS_B_C_D := BetS_B_C_A).
			replace A with D in BetS_B_C_D.
			one_of_disjunct BetS_B_C_D.
		}
		{
			(* case eq_B_D *)
			one_of_disjunct eq_B_D.
		}
		{
			(* case BetS_B_A_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
			pose proof (
				lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_B_C_A BetS_B_A_D
			) as BetS_B_C_D.
			one_of_disjunct BetS_B_C_D.
		}
		{
			(* case BetS_A_B_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_D) as BetS_D_B_A.
			pose proof (
				lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_C_B BetS_A_B_D
			) as BetS_C_B_D.
			one_of_disjunct BetS_C_B_D.
		}
		{
			(* case BetS_A_D_B *)
			assert (~ nCol B C D) as Col_B_C_D.
			{
				intros nCol_B_C_D.
				unfold nCol in nCol_B_C_D.
				destruct nCol_B_C_D as (_ & _ & neq_C_D & nBetS_B_C_D & nBetS_B_D_C & _).
				pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
				pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_B) as BetS_B_D_A.
				pose proof (
					axiom_connectivity _ _ _ _ BetS_B_C_A BetS_B_D_A nBetS_B_C_D nBetS_B_D_C
				) as eq_C_D.
				contradiction neq_C_D.
			}
			apply lemma_supporting_n_ncol_col in Col_B_C_D.
			exact Col_B_C_D.
		}
	}
Qed.

End Euclid.
