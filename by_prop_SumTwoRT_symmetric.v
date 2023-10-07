Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_NC.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Supp_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_SumTwoRT_symmetric :
	forall A B C D E F,
	SumTwoRT A B C D E F ->
	SumTwoRT D E F A B C.
Proof.
	intros A B C D E F.
	intros SumTwoRT_A_B_C_D_E_F.

	destruct SumTwoRT_A_B_C_D_E_F as (a & b & c & d & e & Supp_a_b_c_d_e & CongA_A_B_C_a_b_c & CongA_D_E_F_d_b_e).

	pose proof (by_prop_Supp_symmetric _ _ _ _ _ Supp_a_b_c_d_e) as Supp_e_b_d_c_a.

	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_A_B_C_a_b_c) as nCol_a_b_c.
	pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_D_E_F_d_b_e) as nCol_d_b_e.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_a_b_c) as CongA_a_b_c_c_b_a.
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_d_b_e) as CongA_d_b_e_e_b_d.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_D_E_F_d_b_e CongA_d_b_e_e_b_d) as CongA_D_E_F_e_b_d.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_a_b_c CongA_a_b_c_c_b_a) as CongA_A_B_C_c_b_a.

	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_e_b_d_c_a CongA_D_E_F_e_b_d CongA_A_B_C_c_b_a) as SumTwoRT_D_E_F_A_B_C.

	exact SumTwoRT_D_E_F_A_B_C.
Qed.

End Euclid.
