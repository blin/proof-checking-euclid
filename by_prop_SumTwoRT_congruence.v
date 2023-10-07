Require Import ProofCheckingEuclid.by_def_SumTwoRT.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_SumTwoRT_congruence :
	forall A B C D E F P Q R,
	SumTwoRT A B C D E F ->
	CongA A B C P Q R ->
	SumTwoRT P Q R D E F.
Proof.
	intros A B C D E F P Q R.
	intros SumTwoRT_A_B_C_D_E_F.
	intros CongA_A_B_C_P_Q_R.

	destruct SumTwoRT_A_B_C_D_E_F as (a & b & c & d & e & Supp_a_b_c_d_e & CongA_A_B_C_a_b_c & CongA_D_E_F_d_b_e).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_A_B_C_P_Q_R) as CongA_P_Q_R_A_B_C.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_P_Q_R_A_B_C CongA_A_B_C_a_b_c) as CongA_P_Q_R_a_b_c.
	pose proof (by_def_SumTwoRT _ _ _ _ _ _ _ _ _ _ _ Supp_a_b_c_d_e CongA_P_Q_R_a_b_c CongA_D_E_F_d_b_e) as SumTwoRT_P_Q_R_D_E_F.

	exact SumTwoRT_P_Q_R_D_E_F.
Qed.

End Euclid.

