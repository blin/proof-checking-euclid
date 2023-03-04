Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_BAC.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

(* TODO: rename to lemma_line_intersection_unique_cut *)
Lemma lemma_twolines :
	forall A B C D E F,
	Cut A B C D E ->
	Cut A B C D F ->
	nCol B C D ->
	eq E F.
Proof.
	intros A B C D E F.
	intros Cut_AB_CD_E.
	intros Cut_AB_CD_F.
	intros nCol_B_C_D.

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_B_C_D) as n_Col_B_C_D.

	destruct Cut_AB_CD_E as (BetS_A_E_B & BetS_C_E_D & _ & _).
	destruct Cut_AB_CD_F as (BetS_A_F_B & BetS_C_F_D & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_E_D) as BetS_D_E_C.
	pose proof (lemma_betweennotequal _ _ _ BetS_D_E_C) as (_ & _ & neq_D_C).
	pose proof (lemma_betweennotequal _ _ _ BetS_C_E_D) as (_ & _ & neq_C_D).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_B) as (_ & _ & neq_A_B).

	assert (Col A E B) as Col_A_E_B by (unfold Col; one_of_disjunct BetS_A_E_B).
	assert (Col A F B) as Col_A_F_B by (unfold Col; one_of_disjunct BetS_A_F_B).
	assert (Col C E D) as Col_C_E_D by (unfold Col; one_of_disjunct BetS_C_E_D).
	assert (Col C F D) as Col_C_F_D by (unfold Col; one_of_disjunct BetS_C_F_D).

	pose proof (lemma_collinearorder _ _ _ Col_A_E_B) as (_ & _ & _ & Col_A_B_E & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_F_B) as (_ & _ & _ & Col_A_B_F & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_E_D) as (_ & _ & _ & Col_C_D_E & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_F_D) as (_ & _ & _ & Col_C_D_F & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_E Col_A_B_F neq_A_B) as Col_B_E_F.
	pose proof (lemma_collinearorder _ _ _ Col_B_E_F) as (_ & Col_E_F_B & _).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_D_E Col_C_D_F neq_C_D) as Col_D_E_F.
	pose proof (lemma_collinearorder _ _ _ Col_D_E_F) as (_ & Col_E_F_D & _).

	pose proof (lemma_collinear_ABC_BAC _ _ _ Col_C_D_E) as Col_D_C_E.
	pose proof (lemma_collinear_ABC_BAC _ _ _ Col_C_D_F) as Col_D_C_F.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_D_C_E Col_D_C_F neq_D_C) as Col_C_E_F.
	pose proof (lemma_collinearorder _ _ _ Col_C_E_F) as (_ & Col_E_F_C & _).

	assert (~ neq E F) as eq_E_F.
	{
		intros neq_E_F.

		assert (~ eq F B) as neq_F_B.
		{
			intros eq_F_B.

			assert (Col F C D) as Col_F_C_D by (unfold Col; one_of_disjunct BetS_C_F_D).
			assert (Col B C D) as Col_B_C_D by (rewrite <- eq_F_B; exact Col_F_C_D).

			contradict Col_B_C_D.
			exact n_Col_B_C_D.
		}

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_F_B Col_E_F_C neq_E_F) as Col_F_B_C.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_F_B Col_E_F_D neq_E_F) as Col_F_B_D.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_B_C Col_F_B_D neq_F_B) as Col_B_C_D.

		contradict Col_B_C_D.
		exact n_Col_B_C_D.
	}
	apply Classical_Prop.NNPP in eq_E_F.
	exact eq_E_F.
Qed.

End Euclid.
