Require Import ProofCheckingEuclid.by_def_Cross.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_crossimpliesopposite.
Require Import ProofCheckingEuclid.proposition_04.
Require Import ProofCheckingEuclid.proposition_27B.
Require Import ProofCheckingEuclid.proposition_29B.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_33 :
	forall A B C D M,
	Par A B C D ->
	Cong A B C D ->
	BetS A M D ->
	BetS B M C ->
	Par A C B D /\ Cong A C B D.
Proof.
	intros A B C D M.
	intros Par_AB_CD.
	intros Cong_AB_CD.
	intros BetS_A_M_D.
	intros BetS_B_M_C.

	pose proof (cn_congruencereflexive B C) as Cong_BC_BC.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_BC_BC) as (_ & _ & Cong_BC_CB).

	pose proof (by_prop_Par_NC _ _ _ _ Par_AB_CD) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_C_B) as CongA_ACB_BCA.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_C_D) as CongA_BCD_DCB.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_CD) as (_ & Cong_BA_CD & _).

	pose proof (by_def_Cross _ _ _ _ _ BetS_A_M_D BetS_B_M_C) as Cross_AD_BC.
	pose proof (lemma_crossimpliesopposite _ _ _ _ Cross_AD_BC nCol_A_B_C) as (OppositeSide_A_BC_D & OppositeSide_A_CB_D & _ & _).

	pose proof (proposition_29B _ _ _ _ Par_AB_CD OppositeSide_A_BC_D) as CongA_ABC_BCD.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_BCD CongA_BCD_DCB) as CongA_ABC_DCB.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_BA_CD Cong_BC_CB CongA_ABC_DCB) as (Cong_AC_DB & _ & CongA_BCA_CBD).

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AC_DB) as (_ & _ & Cong_AC_BD).

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ACB_BCA CongA_BCA_CBD) as CongA_ACB_CBD.

	pose proof (proposition_27B _ _ _ _ CongA_ACB_CBD OppositeSide_A_CB_D) as Par_AC_BD.

	split.
	exact Par_AC_BD.
	exact Cong_AC_BD.
Qed.

End Euclid.
