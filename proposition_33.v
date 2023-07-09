Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_crossimpliesopposite.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_parallelNC.
Require Import ProofCheckingEuclid.lemma_s_cross.
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
	intros Par_A_B_C_D.
	intros Cong_A_B_C_D.
	intros BetS_A_M_D.
	intros BetS_B_M_C.

	pose proof (cn_congruencereflexive B C) as Cong_B_C_B_C.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_B_C_B_C) as (_ & _ & Cong_B_C_C_B).

	pose proof (lemma_parallelNC _ _ _ _ Par_A_B_C_D) as (nCol_A_B_C & nCol_A_C_D & nCol_B_C_D & nCol_A_B_D).
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_A_C_B) as CongA_A_C_B_B_C_A.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_C_D) as CongA_B_C_D_D_C_B.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_B_C_D) as (_ & Cong_B_A_C_D & _).

	epose proof (lemma_s_cross _ _ _ _ _ BetS_A_M_D BetS_B_M_C) as Cross_A_D_B_C.
	epose proof (lemma_crossimpliesopposite _ _ _ _ Cross_A_D_B_C nCol_A_B_C) as (OS_A_B_C_D & OS_A_C_B_D & _ & _).

	pose proof (proposition_29B _ _ _ _ Par_A_B_C_D OS_A_B_C_D) as CongA_A_B_C_B_C_D.

	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_B_C_B_C_D CongA_B_C_D_D_C_B) as CongA_A_B_C_D_C_B.
	pose proof (proposition_04 _ _ _ _ _ _ Cong_B_A_C_D Cong_B_C_C_B CongA_A_B_C_D_C_B) as (Cong_A_C_D_B & _ & CongA_B_C_A_C_B_D).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_A_C_D_B) as (_ & _ & Cong_A_C_B_D).

	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ CongA_A_C_B_B_C_A CongA_B_C_A_C_B_D) as CongA_A_C_B_C_B_D.

	pose proof (proposition_27B _ _ _ _ CongA_A_C_B_C_B_D OS_A_C_B_D) as Par_A_C_B_D.

	split.
	exact Par_A_C_B_D.
	exact Cong_A_C_B_D.
Qed.

End Euclid.
