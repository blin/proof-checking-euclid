Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_C_B.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_B_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.by_def_LtA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_isosceles.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Lt_congruence.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_ABD.
Require Import ProofCheckingEuclid.lemma_partnotequalwhole.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_trichotomy_asymmetric :
	forall A B C D,
	Lt A B C D ->
	~ Lt C D A B.
Proof.
	intros A B C D.
	intros Lt_AB_CD.

	destruct Lt_AB_CD as (E & BetS_C_E_D & Cong_CE_AB).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_CE_AB) as Cong_AB_CE.

	assert (~ Lt C D A B) as n_Lt_CD_AB.
	{
		intro Lt_CD_AB.

		pose proof (by_prop_Lt_congruence _ _ _ _ _ _ Lt_CD_AB Cong_AB_CE) as Lt_CD_CE.
		destruct Lt_CD_CE as (F & BetS_C_F_E & Cong_CF_CD).

		pose proof (lemma_orderofpoints_ABC_ACD_ABD _ _ _ _ BetS_C_F_E BetS_C_E_D) as BetS_C_F_D.
		pose proof (lemma_partnotequalwhole _ _ _ BetS_C_F_D) as n_Cong_CF_CD.

		contradict Cong_CF_CD.
		exact n_Cong_CF_CD.
	}

	exact n_Lt_CD_AB.
Qed.

End Euclid.
