Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Square.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_equaltoright.
Require Import ProofCheckingEuclid.by_prop_SameSide_not_OppositeSide .
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_crisscross.
Require Import ProofCheckingEuclid.lemma_s_conga_sss.
Require Import ProofCheckingEuclid.lemma_twoperpsparallel.
Require Import ProofCheckingEuclid.proposition_33.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_road_to_reality_2_7 :
	forall A B C D,
	RightTriangle A B C ->
	RightTriangle B C D ->
	Cong A B B C ->
	Cong B C C D ->
	SameSide D A B C ->
	Square A B C D.
Proof.
	intros A B C D.
	intros RightTriangle_ABC.
	intros RightTriangle_BCD.
	intros Cong_AB_BC.
	intros Cong_BC_CD.
	intros SameSide_D_A_BC.

	pose proof (cn_congruencereverse A C) as Cong_AC_CA.
	pose proof (cn_congruencereverse B D) as Cong_BD_DB.

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AB_BC Cong_BC_CD) as Cong_AB_CD.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_CD) as (Cong_BA_DC & Cong_BA_CD & Cong_AB_DC).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AB_CD) as Cong_CD_AB.

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_D_A_BC) as (SameSide_A_D_BC & SameSide_D_A_CB & SameSide_A_D_CB).
	pose proof (by_prop_SameSide_not_OppositeSide _ _ _ _ SameSide_A_D_BC) as n_OppositeSide_A_BC_D.

	pose proof (lemma_twoperpsparallel _ _ _ _ RightTriangle_ABC RightTriangle_BCD SameSide_A_D_BC) as Par_AB_CD.
	pose proof (by_prop_Par_flip _ _ _ _ Par_AB_CD) as (Par_BA_CD & Par_AB_DC & Par_BA_DC).

	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

	assert (~ Cross A D B C) as n_Cross_AD_BC.
	{
		intros Cross_AD_BC.

		destruct Cross_AD_BC as (M & BetS_A_M_D & BetS_B_M_C).

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_M_C) as Col_B_M_C.
		pose proof (by_prop_Col_order _ _ _ Col_B_M_C) as (Col_M_B_C & Col_M_C_B & Col_C_B_M & Col_B_C_M & Col_C_M_B).

		pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_M_D Col_B_C_M nCol_B_C_A) as OppositeSide_A_BC_D.

		contradict OppositeSide_A_BC_D.
		exact n_OppositeSide_A_BC_D.
	}

	pose proof (lemma_crisscross _ _ _ _ Par_AB_DC n_Cross_AD_BC) as Cross_AC_DB.

	assert (Cross_AC_DB_2 := Cross_AC_DB).
	destruct Cross_AC_DB_2 as (M & BetS_A_M_C & BetS_D_M_B).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_M_B) as BetS_B_M_D.

	pose proof (proposition_33 _ _ _ _ _ Par_AB_DC Cong_AB_DC BetS_A_M_C BetS_B_M_D) as (_ & Cong_AD_BC).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AD_BC) as Cong_BC_AD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BC_AD) as (Cong_CB_DA & Cong_CB_AD & Cong_BC_DA).

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AB_BC Cong_BC_DA) as Cong_AB_DA.

	pose proof (lemma_s_conga_sss _ _ _ _ _ _ Cong_AB_CD  Cong_AC_CA Cong_BC_DA nCol_A_B_C) as CongA_ABC_CDA.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABC_CDA) as CongA_CDA_ABC.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_ABC CongA_CDA_ABC) as RightTriangle_CDA.

	pose proof (lemma_s_conga_sss _ _ _ _ _ _ Cong_BC_DA Cong_BD_DB Cong_CD_AB nCol_B_C_D) as CongA_BCD_DAB.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_BCD_DAB) as CongA_DAB_BCD.
	pose proof (by_prop_RightTriangle_equaltoright _ _ _ _ _ _ RightTriangle_BCD CongA_DAB_BCD) as RightTriangle_DAB.

	pose proof (by_def_Square _ _ _ _ Cong_AB_CD Cong_AB_BC Cong_AB_DA RightTriangle_DAB RightTriangle_ABC RightTriangle_BCD RightTriangle_CDA) as Square_A_B_C_D.

	exact Square_A_B_C_D.
Qed.

End Euclid.
