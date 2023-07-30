Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_LtA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_E_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_distinct.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_angletrichotomy.
Require Import ProofCheckingEuclid.lemma_s_ncol_ABD_col_ABC_ncol_ACD.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.proposition_03.
Require Import ProofCheckingEuclid.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma proposition_06a :
	forall A B C,
	Triangle A B C ->
	CongA A B C A C B ->
	~ Lt A C A B.
Proof.
	intros A B C.
	intros Triangle_ABC.
	intros CongA_ABC_ACB.

	assert (nCol A B C) as nCol_A_B_C by (unfold Triangle in Triangle_ABC; exact Triangle_ABC).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & _ & _ & nCol_A_C_B & nCol_C_B_A).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_B_C) as CongA_ABC_ABC.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_C_B) as CongA_ACB_BCA.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_C_B_A) as CongA_CBA_ABC.

	pose proof (by_prop_CongA_distinct _ _ _ _ _ _ CongA_ABC_ACB) as (neq_A_B & neq_B_C & neq_A_C & _ & neq_C_B & _).

	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_A_C) as neq_C_A.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_A) as OnRay_CA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_B) as OnRay_CB_B.

	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (cn_congruencereverse B A) as Cong_BA_AB.
	pose proof (cn_congruencereverse B C) as Cong_BC_CB.

	assert (~ Lt A C A B) as n_Lt_AC_AB.
	{
		intros Lt_AC_AB.

		pose proof (proposition_03 _ _ _ _ _ _ Lt_AC_AB Cong_BA_AB) as (D & BetS_B_D_A & Cong_BD_AC).

		pose proof (by_prop_BetS_notequal _ _ _ BetS_B_D_A) as (_ & neq_B_D & _).

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_D_A) as Col_B_D_A.
		pose proof (by_prop_Col_order _ _ _ Col_B_D_A) as (_ & _ & _ & Col_B_A_D & _).

		pose proof (by_def_OnRay_from_BetS_A_E_B _ _ _ BetS_B_D_A neq_B_A) as OnRay_BA_D.
		pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ABC_ABC OnRay_BA_D OnRay_BC_C) as CongA_ABC_DBC.
		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_ABC_DBC) as CongA_DBC_ABC.
		pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_DBC_ABC CongA_ABC_ACB) as CongA_DBC_ACB.

		pose proof (by_prop_Cong_flip _ _ _ _ Cong_BD_AC) as (_ & _ & Cong_BD_CA).

		pose proof (lemma_s_ncol_ABD_col_ABC_ncol_ACD _ _ _ _ nCol_B_A_C Col_B_A_D neq_B_D) as nCol_B_D_C.
		pose proof (by_prop_nCol_order _ _ _ nCol_B_D_C) as (_ & _ & _ & nCol_B_C_D & _).
		pose proof (by_prop_CongA_reflexive _ _ _ nCol_B_C_D) as CongA_BCD_BCD.

		pose proof (proposition_04 _ _ _ _ _ _ Cong_BD_CA Cong_BC_CB CongA_DBC_ACB) as (_ & _ & CongA_BCD_CBA).
		pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BCD_CBA CongA_CBA_ABC) as CongA_BCD_ABC.
		pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BCD_ABC CongA_ABC_ACB) as CongA_BCD_ACB.
		pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BCD_ACB CongA_ACB_BCA) as CongA_BCD_BCA.
		pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_BCD_BCA) as CongA_BCA_BCD.

		pose proof (by_def_LtA _ _ _ _ _ _ _ _ _ BetS_B_D_A OnRay_CB_B OnRay_CA_A CongA_BCD_BCD) as LtA_BCD_BCA.
		pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_BCD_BCA CongA_BCA_BCD) as LtA_BCA_BCA.
		pose proof (lemma_angletrichotomy _ _ _ _ _ _ LtA_BCA_BCA) as n_LtA_BCA_BCA.

		contradict LtA_BCA_BCA.
		exact n_LtA_BCA_BCA.
	}

	exact n_Lt_AC_AB.

Qed.

End Euclid.
