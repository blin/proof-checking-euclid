Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_s_ss.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_samesidesymmetric :
	forall A B P Q,
	SS P Q A B ->
	SS Q P A B /\ SS P Q B A /\ SS Q P B A.
Proof.
	intros A B P Q.
	intros SS_P_Q_AB.

	destruct SS_P_Q_AB as (G & E & F & Col_A_B_E & Col_A_B_F & BetS_P_E_G & BetS_Q_F_G & nCol_A_B_P & nCol_A_B_Q).
	pose proof (
		lemma_s_ss
		_ _ _ _
		_ _ _
		Col_A_B_F
		Col_A_B_E
		BetS_Q_F_G
		BetS_P_E_G
		nCol_A_B_Q
		nCol_A_B_P
	) as SS_Q_P_AB.

	pose proof (lemma_collinearorder _ _ _ Col_A_B_E) as (Col_B_A_E & _ & _ & _ & _).
	pose proof (lemma_collinearorder _ _ _ Col_A_B_F) as (Col_B_A_F & _ & _ & _ & _).

	pose proof (lemma_NCorder _ _ _ nCol_A_B_P) as (nCol_B_A_P & nCol_B_P_A & nCol_P_A_B & nCol_A_P_B & nCol_P_B_A).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_Q) as (nCol_B_A_Q & nCol_B_Q_A & nCol_Q_A_B & nCol_A_Q_B & nCol_Q_B_A).

	pose proof (
		lemma_s_ss
		_ _ _ _
		_ _ _
		Col_B_A_F
		Col_B_A_E
		BetS_Q_F_G
		BetS_P_E_G
		nCol_B_A_Q
		nCol_B_A_P
	) as SS_Q_P_BA.

	pose proof (
		lemma_s_ss
		P Q B A
		_ _ _
		Col_B_A_E
		Col_B_A_F
		BetS_P_E_G
		BetS_Q_F_G
		nCol_B_A_P
		nCol_B_A_Q
	) as SS_P_Q_BA.

	split.
	exact SS_Q_P_AB.
	split.
	exact SS_P_Q_BA.
	exact SS_Q_P_BA.

Qed.

End Euclid.
