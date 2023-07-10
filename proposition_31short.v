Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_31.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_31short :
	forall A B C D,
	BetS B D C ->
	nCol B C A ->
	exists X Y Z, BetS X A Y /\ CongA X A D A D C /\ Par X Y B C /\ BetS X Z C /\ BetS A Z D.
Proof.
	intros A B C D.
	intros BetS_B_D_C.
	intros nCol_B_C_A.

	pose proof (proposition_31 _ _ _ _ BetS_B_D_C nCol_B_C_A) as (
		E &
		F &
		S &
		BetS_E_A_F &
		CongA_FAD_ADB &
		CongA_FAD_BDA &
		CongA_DAF_BDA &
		CongA_EAD_ADC &
		CongA_EAD_CDA &
		CongA_DAE_CDA &
		Par_EF_BC &
		Cong_EA_DC &
		Cong_AF_BD &
		Cong_AS_SD &
		Cong_ES_SC &
		Cong_BS_SF &
		BetS_E_S_C &
		BetS_B_S_F &
		BetS_A_S_D
	).
	exists E, F, S.
	split.
	exact BetS_E_A_F.
	split.
	exact CongA_EAD_ADC.
	split.
	exact Par_EF_BC.
	split.
	exact BetS_E_S_C.
	exact BetS_A_S_D.
Qed.

End Euclid.

