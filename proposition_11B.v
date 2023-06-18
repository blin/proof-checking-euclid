Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_ABE_CDE.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_collinearright.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_notperp.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_planeseparation.
Require Import ProofCheckingEuclid.lemma_pointreflectionisometry.
Require Import ProofCheckingEuclid.lemma_right_triangle_NC.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.
Require Import ProofCheckingEuclid.lemma_rightreverse.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_C_B.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_midpoint.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_os.
Require Import ProofCheckingEuclid.lemma_s_right_triangle.
Require Import ProofCheckingEuclid.lemma_samesidesymmetric.
Require Import ProofCheckingEuclid.proposition_10.
Require Import ProofCheckingEuclid.proposition_12.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_11B :
	forall A B C P,
	BetS A C B ->
	nCol A B P ->
	exists X, RightTriangle A C X /\ OS X A B P.
Proof.
	intros A B C P.
	intros BetS_A_C_B.
	intros nCol_A_B_P.

	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (lemma_s_col_eq_A_C A B A eq_A_A) as Col_A_B_A.

	pose proof (lemma_betweennotequal _ _ _ BetS_A_C_B) as (_ & _ & neq_A_B).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_C_B) as (_ & neq_A_C & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_A_C_B) as (neq_C_B & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_A_B) as neq_B_A.
	pose proof (lemma_inequalitysymmetric _ _ neq_A_C) as neq_C_A.

	pose proof (lemma_s_col_BetS_A_C_B A B C BetS_A_C_B) as Col_A_B_C.
	pose proof (lemma_collinearorder _ _ _ Col_A_B_C) as (Col_B_A_C & Col_B_C_A & Col_C_A_B & Col_A_C_B & Col_C_B_A).

	pose proof (lemma_notperp _ _ _ _ BetS_A_C_B nCol_A_B_P) as (M & nCol_A_B_M & SS_M_P_A_B & n_RightTriangle_A_C_M).

	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_M) as n_Col_A_B_M.

	pose proof (lemma_samesidesymmetric _ _ _ _ SS_M_P_A_B) as (SS_P_M_A_B & _ & _).

	pose proof (proposition_12 _ _ _ nCol_A_B_M) as (Q & Perp_at_M_Q_A_B_Q).
	destruct Perp_at_M_Q_A_B_Q as (E & _ & Col_A_B_Q & Col_A_B_E & RightTriangle_E_Q_M).

	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_A_B_Q Col_A_B_C neq_A_B) as Col_B_Q_C.
	pose proof (lemma_collinearorder _ _ _ Col_B_Q_C) as (_ & Col_Q_C_B & _ & _ & _).

	pose proof (lemma_collinearorder _ _ _ Col_A_B_E) as (Col_B_A_E & _ & _ & _ & _).
	pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_C Col_A_B_Q Col_A_B_E) as Col_C_Q_E.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_B_A_E Col_B_A_C neq_B_A) as Col_A_E_C.
	pose proof (lemma_collinearorder _ _ _ Col_A_E_C) as (_ & Col_E_C_A & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_Q_E) as (_ & _ & _ & _ & Col_E_Q_C).

	epose proof (lemma_right_triangle_NC _ _ _ RightTriangle_E_Q_M) as nCol_E_Q_M.
	pose proof (lemma_NCdistinct _ _ _ nCol_E_Q_M) as (neq_E_Q & neq_Q_M & neq_E_M & neq_Q_E & neq_M_Q & neq_M_E).


	assert (~ eq C Q) as n_eq_C_Q.
	{
		intro eq_C_Q.

		assert (RightTriangle E C M) as RightTriangle_E_C_M by (rewrite eq_C_Q; exact RightTriangle_E_Q_M).
		pose proof (lemma_collinearright _ _ _ _ RightTriangle_E_C_M Col_E_C_A neq_A_C) as RightTriangle_A_C_M.

		contradict RightTriangle_A_C_M.
		exact n_RightTriangle_A_C_M.
	}
	assert (neq_C_Q := n_eq_C_Q).

	pose proof (lemma_inequalitysymmetric _ _ neq_C_Q) as neq_Q_C.

	pose proof (lemma_collinearright _ _ _ _ RightTriangle_E_Q_M Col_E_Q_C neq_C_Q) as RightTriangle_C_Q_M.
	epose proof (lemma_right_triangle_NC _ _ _ RightTriangle_C_Q_M) as nCol_C_Q_M.
	pose proof (lemma_NCdistinct _ _ _ nCol_C_Q_M) as (_ & _ & neq_C_M & _ & _ & neq_M_C).
	pose proof (lemma_NCorder _ _ _ nCol_C_Q_M) as (nCol_Q_C_M & nCol_Q_M_C & nCol_M_C_Q & nCol_C_M_Q & nCol_M_Q_C).

	pose proof (proposition_10 _ _ neq_Q_C) as (G & BetS_Q_G_C & Cong_G_Q_G_C).

	pose proof (lemma_betweennotequal _ _ _ BetS_Q_G_C) as (_ & neq_Q_G & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_Q_G_C) as (neq_G_C & _ & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_Q_G) as neq_G_Q.
	pose proof (lemma_inequalitysymmetric _ _ neq_G_C) as neq_C_G.

	pose proof (lemma_s_col_BetS_A_B_C Q G C BetS_Q_G_C) as Col_Q_G_C.
	pose proof (lemma_collinearorder _ _ _ Col_Q_G_C) as (Col_G_Q_C & Col_G_C_Q & Col_C_Q_G & Col_Q_C_G & Col_C_G_Q).

	pose proof (lemma_collinear_ABC_ABD_ABE_CDE _ _ _ _ _ neq_A_B Col_A_B_Q Col_A_B_C Col_A_B_A) as Col_Q_C_A.
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_Q_C_A Col_Q_C_G neq_Q_C) as Col_C_A_G.
	pose proof (lemma_collinearorder _ _ _ Col_C_A_G) as (_ & _ & Col_G_C_A & _ & _).
	pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_C_A_G Col_C_A_B neq_C_A) as Col_A_G_B.
	pose proof (lemma_collinearorder _ _ _ Col_A_G_B) as (_ & _ & _ & Col_A_B_G & _).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_G_Q_G_C) as (_ & Cong_Q_G_G_C & _).
	pose proof (lemma_s_midpoint _ _ _ BetS_Q_G_C Cong_Q_G_G_C) as Midpoint_Q_G_C.

	pose proof (lemma_collinearright _ _ _ _ RightTriangle_C_Q_M Col_C_Q_G neq_G_Q) as RightTriangle_G_Q_M.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_G_Q_M) as RightTriangle_M_Q_G.

	epose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_Q_C_M Col_Q_C_G neq_Q_G) as nCol_Q_G_M.
	pose proof (lemma_NCdistinct _ _ _ nCol_Q_G_M) as (_ & neq_G_M & _ & _ & neq_M_G & _).

	pose proof (lemma_extension M Q M Q neq_M_Q neq_M_Q) as (J & BetS_M_Q_J & Cong_Q_J_M_Q).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_M_Q_J) as BetS_J_Q_M.
	pose proof (lemma_betweennotequal _ _ _ BetS_J_Q_M) as (_ & neq_J_Q & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_J_Q) as neq_Q_J.
	pose proof (lemma_betweennotequal _ _ _ BetS_M_Q_J) as (_ & _ & neq_M_J).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_Q_J_M_Q) as Cong_M_Q_Q_J.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_Q_J_M_Q) as (_ & Cong_J_Q_M_Q & _).

	pose proof (lemma_rightreverse _ _ _ _ RightTriangle_M_Q_G BetS_M_Q_J Cong_M_Q_Q_J) as Cong_M_G_J_G.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_G_J_G) as Cong_J_G_M_G.
	pose proof (lemma_s_right_triangle _ _ _ _ BetS_J_Q_M Cong_J_Q_M_Q Cong_J_G_M_G neq_Q_G) as RightTriangle_J_Q_G.
	epose proof (lemma_right_triangle_NC _ _ _ RightTriangle_J_Q_G) as nCol_J_Q_G.
	pose proof (lemma_NCdistinct _ _ _ nCol_J_Q_G) as (_ & _ & neq_J_G & _ & _ & neq_G_J).

	pose proof (lemma_extension J G J G neq_J_G neq_J_G) as (K & BetS_J_G_K & Cong_G_K_J_G).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_G_K_J_G) as Cong_J_G_G_K.
	pose proof (lemma_s_midpoint _ _ _ BetS_J_G_K Cong_J_G_G_K) as Midpoint_J_G_K.

	pose proof (lemma_extension M G M G neq_M_G neq_M_G) as (H & BetS_M_G_H & Cong_G_H_M_G).

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_G_H_M_G) as Cong_M_G_G_H.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_G_H_M_G) as (Cong_H_G_G_M & _ & _).
	
	pose proof (lemma_s_os _ _ _ _ _ BetS_M_G_H Col_A_B_G nCol_A_B_M) as OS_M_A_B_H.
	pose proof (lemma_planeseparation _ _ _ _ _ SS_P_M_A_B OS_M_A_B_H) as OS_P_A_B_H.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_P_A_B_H) as OS_H_A_B_P.

	pose proof (lemma_s_midpoint _ _ _ BetS_M_G_H Cong_M_G_G_H) as Midpoint_M_G_H.

	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_M_G_H Midpoint_Q_G_C neq_M_Q) as Cong_M_Q_H_C.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_Q_G_C Midpoint_J_G_K neq_Q_J) as Cong_Q_J_C_K.
	pose proof (lemma_pointreflectionisometry _ _ _ _ _ Midpoint_M_G_H Midpoint_J_G_K neq_M_J) as Cong_M_J_H_K.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_M_Q_H_C) as Cong_H_C_M_Q.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_M_G_J_G) as (_ & Cong_G_M_J_G & _).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_H_G_G_M Cong_G_M_J_G) as Cong_H_G_J_G.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_H_G_J_G Cong_J_G_G_K) as Cong_H_G_G_K.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_H_G_G_K) as (_ & _ & Cong_H_G_K_G).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_H_C_M_Q Cong_M_Q_Q_J) as Cong_H_C_Q_J.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_H_C_Q_J Cong_Q_J_C_K) as Cong_H_C_C_K.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_H_C_C_K) as (_ & _ & Cong_H_C_K_C).

	pose proof (lemma_betweennesspreserved _ _ _ _ _ _ Cong_M_Q_H_C Cong_M_J_H_K Cong_Q_J_C_K BetS_M_Q_J) as BetS_H_C_K.

	pose proof (lemma_s_right_triangle _ _ _ _ BetS_H_C_K Cong_H_C_K_C Cong_H_G_K_G neq_C_G) as RightTriangle_H_C_G.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_H_C_G) as RightTriangle_G_C_H.
	pose proof (lemma_collinearright _ _ _ _ RightTriangle_G_C_H Col_G_C_A neq_A_C) as RightTriangle_A_C_H.

	exists H.
	split.
	exact RightTriangle_A_C_H.
	exact OS_H_A_B_P.
Qed.

End Euclid.
