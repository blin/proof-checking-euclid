Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_supplements_conga.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supplements_SumTwoRT :
	forall A B C D E F J K L P Q R,
	SumTwoRT A B C P Q R ->
	CongA A B C J K L ->
	SumTwoRT J K L D E F ->
	CongA P Q R D E F /\ CongA D E F P Q R.
Proof.
	intros A B C D E F J K L P Q R.
	intros SumTwoRT_A_B_C_P_Q_R.
	intros CongA_A_B_C_J_K_L.
	intros SumTwoRT_J_K_L_D_E_F.

	destruct SumTwoRT_A_B_C_P_Q_R as (a & b & e & c & d & Supp_a_b_c_d_e & CongA_A_B_C_a_b_c & CongA_P_Q_R_d_b_e).
	destruct SumTwoRT_J_K_L_D_E_F as (j & k & n & l & m & Supp_j_k_l_m_n & CongA_J_K_L_j_k_l & CongA_D_E_F_m_k_n).

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_A_B_C_a_b_c) as CongA_a_b_c_A_B_C.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_D_E_F_m_k_n) as CongA_m_k_n_D_E_F.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_a_b_c_A_B_C CongA_A_B_C_J_K_L) as CongA_a_b_c_J_K_L.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_a_b_c_J_K_L CongA_J_K_L_j_k_l) as CongA_a_b_c_j_k_l.

	pose proof (lemma_supplements_conga _ _ _ _ _ _ _ _ _ _ CongA_a_b_c_j_k_l Supp_a_b_c_d_e Supp_j_k_l_m_n) as CongA_d_b_e_m_k_n.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_P_Q_R_d_b_e CongA_d_b_e_m_k_n) as CongA_P_Q_R_m_k_n.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_P_Q_R_m_k_n CongA_m_k_n_D_E_F) as CongA_P_Q_R_D_E_F.
	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_P_Q_R_D_E_F) as CongA_D_E_F_P_Q_R.

	split.
	exact CongA_P_Q_R_D_E_F.
	exact CongA_D_E_F_P_Q_R.
Qed.

End Euclid.
