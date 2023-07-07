Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_oppositesidesymmetric.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_os.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crossimpliesopposite :
	forall A B C D,
	Cross A B C D ->
	nCol A C D ->
	OS A C D B /\ OS A D C B /\ OS B C D A /\ OS B D C A.
Proof.
	intros A B C D.
	intros Cross_AB_CD.
	intros nCol_A_C_D.


	destruct Cross_AB_CD as (M & BetS_A_M_B & BetS_C_M_D).

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_C_M_D) as Col_C_M_D.
	pose proof (lemma_collinearorder _ _ _ Col_C_M_D) as (_ & _ & _ & Col_C_D_M & _).
	pose proof (lemma_collinearorder _ _ _ Col_C_D_M) as (Col_D_C_M & _ & _ & _ & _).

	pose proof (lemma_NCorder _ _ _ nCol_A_C_D) as (_ & nCol_C_D_A & _ & _ & _).
	pose proof (lemma_NCorder _ _ _ nCol_C_D_A) as (nCol_D_C_A & _ & _ & _ & _).

	pose proof (lemma_s_os _ _ _ _ _ BetS_A_M_B Col_C_D_M nCol_C_D_A) as OS_A_CD_B.
	pose proof (lemma_s_os _ _ _ _ _ BetS_A_M_B Col_D_C_M nCol_D_C_A) as OS_A_DC_B.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_A_CD_B) as OS_B_CD_A.
	pose proof (lemma_oppositesidesymmetric _ _ _ _ OS_A_DC_B) as OS_B_DC_A.

	split.
	exact OS_A_CD_B.
	split.
	exact OS_A_DC_B.
	esplit.
	exact OS_B_CD_A.
	exact OS_B_DC_A.
Qed.

End Euclid.
