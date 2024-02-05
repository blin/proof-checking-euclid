Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_CongTriangles.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_flip.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_NC .
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_diagonalsmeet.
Require Import ProofCheckingEuclid.lemma_s_conga_sss .
Require Import ProofCheckingEuclid.proposition_26A.
Require Import ProofCheckingEuclid.proposition_29B.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_34 :
	forall A B C D,
	Parallelogram A C D B ->
	Cong A B C D /\ Cong A C B D /\ CongA C A B B D C /\ CongA A B D D C A /\ CongTriangles C A B B D C.
Proof.
	intros A B C D.
	intros Parallelogram_A_C_D_B.

	pose proof (cn_congruencereverse A D) as Cong_AD_DA.
	pose proof (cn_congruencereverse B C) as Cong_BC_CB.
	pose proof (cn_congruencereverse C B) as Cong_CB_BC.

	assert (Parallelogram_A_C_D_B_2 := Parallelogram_A_C_D_B).
	destruct Parallelogram_A_C_D_B_2 as (Par_AC_DB & Par_AB_CD).

	pose proof (by_prop_Par_flip _ _ _ _ Par_AC_DB) as (_ & Par_AC_BD & _).

	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_nCol_order _ _ _ nCol_B_C_D) as (nCol_C_B_D & nCol_C_D_B & nCol_D_B_C & nCol_B_D_C & nCol_D_C_B).

	pose proof (by_def_Triangle _ _ _ nCol_A_B_C) as Triangle_ABC.
	pose proof (by_def_Triangle _ _ _ nCol_D_C_B) as Triangle_DCB.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_C_A) as CongA_BCA_ACB.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_C_D) as CongA_BCD_DCB.

	pose proof (lemma_diagonalsmeet _ _ _ _ Parallelogram_A_C_D_B) as (M & BetS_A_M_D & BetS_C_M_B).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_C_M_B) as Col_C_M_B.
	pose proof (by_prop_Col_order _ _ _ Col_C_M_B) as (Col_M_C_B & Col_M_B_C & Col_B_C_M & Col_C_B_M & Col_B_M_C).

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_M_D Col_B_C_M nCol_B_C_A) as OppositeSide_A_BC_D.
	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_A_M_D Col_C_B_M nCol_C_B_A) as OppositeSide_A_CB_D.

	pose proof (proposition_29B _ _ _ _ Par_AB_CD OppositeSide_A_BC_D) as CongA_ABC_BCD.
	pose proof (proposition_29B _ _ _ _ Par_AC_BD OppositeSide_A_CB_D) as CongA_ACB_CBD.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_BCD CongA_BCD_DCB) as CongA_ABC_DCB.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BCA_ACB CongA_ACB_CBD) as CongA_BCA_CBD.

	pose proof (proposition_26A _ _ _ _ _ _ Triangle_ABC Triangle_DCB CongA_ABC_DCB CongA_BCA_CBD Cong_BC_CB) as (Cong_AB_DC & Cong_AC_DB & CongA_BAC_CDB).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_DC) as (Cong_BA_CD & Cong_BA_DC & Cong_AB_CD).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AC_DB) as (Cong_CA_BD & Cong_CA_DB & Cong_AC_BD).
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AC_DB) as Cong_DB_AC.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_DB_AC) as (Cong_BD_CA & Cong_BD_AC & Cong_DB_CA).

	pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_BAC_CDB) as CongA_CAB_BDC.

	pose proof (by_def_CongTriangles _ _ _ _ _ _ Cong_CA_BD Cong_AB_DC Cong_CB_BC) as CongTriangles_CAB_BDC.

	pose proof (lemma_s_conga_sss _ _ _ _ _ _ Cong_AB_DC Cong_AD_DA Cong_BD_CA nCol_A_B_D) as CongA_ABD_DCA.

	split.
	exact Cong_AB_CD.
	split.
	exact Cong_AC_BD.
	split.
	exact CongA_CAB_BDC.
	split.
	exact CongA_ABD_DCA.
	exact CongTriangles_CAB_BDC.
Qed.

End Euclid.
