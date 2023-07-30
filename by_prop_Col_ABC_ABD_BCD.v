Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_n_nCol.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABD_BCD_ACD.
Require Import ProofCheckingEuclid.lemma_outerconnectivity.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_Col_ABC_ABD_BCD :
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
	contradict eq_A_B.
	exact neq_A_B.
	destruct Col_A_B_D as [eq_A_B | Col_A_B_D].
	contradict eq_A_B.
	exact neq_A_B.

	destruct Col_A_B_C as [eq_A_C | [eq_B_C | [BetS_B_A_C | [BetS_A_B_C | BetS_A_C_B]]]].
	{
		(* case eq_A_C *)
		destruct Col_A_B_D as [ eq_A_D | [ eq_B_D | [ BetS_B_A_D | [ BetS_A_B_D | BetS_A_D_B]]]].
		{
			(* case eq_A_D *)
			assert (eq C D) as eq_C_D by (rewrite <- eq_A_C; exact eq_A_D).
			pose proof (by_def_Col_from_eq_B_C B C D eq_C_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case eq_B_D *)
			pose proof (by_def_Col_from_eq_A_C B C D eq_B_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_B_A_D *)
			assert (BetS B C D) as BetS_B_C_D by (rewrite <- eq_A_C; exact BetS_B_A_D).
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_A_B_D *)
			assert (BetS C B D) as BetS_C_B_D by (rewrite <- eq_A_C; exact BetS_A_B_D).
			pose proof (by_def_Col_from_BetS_B_A_C _ _ _ BetS_C_B_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_A_D_B *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_B) as BetS_B_D_A.
			assert (BetS B D C) as BetS_B_D_C by (rewrite <- eq_A_C; exact BetS_B_D_A).
			pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_B_D_C) as Col_B_C_D.
			exact Col_B_C_D.
		}
	}
	{
		(* case eq_B_C *)
		pose proof (by_def_Col_from_eq_A_B B C D eq_B_C) as Col_B_C_D.
		exact Col_B_C_D.
	}
	{
		(* case BetS_B_A_C *)
		destruct Col_A_B_D as [ eq_A_D | [ eq_B_D | [ BetS_B_A_D | [ BetS_A_B_D | BetS_A_D_B]]]].
		{
			(* case eq_A_D *)
			assert (BetS B D C) as BetS_B_D_C by (rewrite <- eq_A_D; exact BetS_B_A_C).
			pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_B_D_C) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case eq_B_D *)
			pose proof (by_def_Col_from_eq_A_C B C D eq_B_D) as Col_B_C_D.
			exact Col_B_C_D.
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

					pose proof (lemma_orderofpoints_ABD_BCD_ACD _ _ _ _ BetS_B_A_D BetS_A_C_D) as BetS_B_C_D.

					contradict BetS_B_C_D.
					exact nBetS_B_C_D.
				}
				assert (~ BetS A D C) as nBetS_A_D_C.
				{
					intros BetS_A_D_C.

					pose proof (lemma_orderofpoints_ABD_BCD_ACD _ _ _ _ BetS_B_A_C BetS_A_D_C) as BetS_B_D_C.

					contradict BetS_B_D_C.
					exact nBetS_B_D_C.
				}
				pose proof (lemma_outerconnectivity _ _ _ _ BetS_B_A_C BetS_B_A_D nBetS_A_C_D nBetS_A_D_C) as eq_C_D.
				contradict eq_C_D.
				exact neq_C_D.
			}
			apply by_def_Col_from_n_nCol in Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_A_B_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_C) as BetS_C_A_B.
			pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_C_A_B BetS_A_B_D) as BetS_C_B_D.
			pose proof (by_def_Col_from_BetS_B_A_C _ _ _ BetS_C_B_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_A_D_B *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_B) as BetS_B_D_A.
			pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_B_D_A BetS_B_A_C) as BetS_B_D_C.
			pose proof (by_def_Col_from_BetS_A_C_B _ _ _ BetS_B_D_C) as Col_B_C_D.
			exact Col_B_C_D.
		}
	}
	{
		(* case BetS_A_B_C *)
		destruct Col_A_B_D as [ eq_A_D | [ eq_B_D | [ BetS_B_A_D | [ BetS_A_B_D | BetS_A_D_B]]]].
		{
			(* case eq_A_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_C) as BetS_C_B_A.
			assert (BetS C B D) as BetS_C_B_D by (rewrite <- eq_A_D; exact BetS_C_B_A).
			pose proof (by_def_Col_from_BetS_B_A_C _ _ _ BetS_C_B_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case eq_B_D *)
			pose proof (by_def_Col_from_eq_A_C B C D eq_B_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_B_A_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_D) as BetS_D_A_B.
			pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_D_A_B BetS_A_B_C) as BetS_D_B_C.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_C) as BetS_C_B_D.
			pose proof (by_def_Col_from_BetS_B_A_C _ _ _ BetS_C_B_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_A_B_D *)
			assert (~ nCol B C D) as Col_B_C_D.
			{
				intros nCol_B_C_D.

				unfold nCol in nCol_B_C_D.
				destruct nCol_B_C_D as (_ & _ & neq_C_D & nBetS_B_C_D & nBetS_B_D_C & _).
				pose proof (lemma_outerconnectivity _ _ _ _ BetS_A_B_C BetS_A_B_D nBetS_B_C_D nBetS_B_D_C) as eq_C_D.

				contradict eq_C_D.
				exact neq_C_D.
			}
			apply by_def_Col_from_n_nCol in Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_A_D_B *)
			pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_D_B BetS_A_B_C) as BetS_D_B_C.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_B_C) as BetS_C_B_D.
			pose proof (by_def_Col_from_BetS_B_A_C _ _ _ BetS_C_B_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
	}
	{
		(* case BetS_A_C_B *)
		destruct Col_A_B_D as [ eq_A_D | [ eq_B_D | [ BetS_B_A_D | [ BetS_A_B_D | BetS_A_D_B]]]].
		{
			(* case eq_A_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
			assert (BetS B C D) as BetS_B_C_D by (rewrite <- eq_A_D; exact BetS_B_C_A).
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case eq_B_D *)
			pose proof (by_def_Col_from_eq_A_C B C D eq_B_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_B_A_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
			pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_B_C_A BetS_B_A_D) as BetS_B_C_D.
			pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_D) as Col_B_C_D.
			exact Col_B_C_D.
		}
		{
			(* case BetS_A_B_D *)
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_C_B) as BetS_B_C_A.
			pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_D) as BetS_D_B_A.
			pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_A_C_B BetS_A_B_D) as BetS_C_B_D.
			pose proof (by_def_Col_from_BetS_B_A_C _ _ _ BetS_C_B_D) as Col_B_C_D.
			exact Col_B_C_D.
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
				pose proof (axiom_connectivity _ _ _ _ BetS_B_C_A BetS_B_D_A nBetS_B_C_D nBetS_B_D_C) as eq_C_D.

				contradict eq_C_D.
				exact neq_C_D.
			}
			apply by_def_Col_from_n_nCol in Col_B_C_D.
			exact Col_B_C_D.
		}
	}
Qed.

End Euclid.
