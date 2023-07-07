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
		CongA_F_A_D_A_D_B &
		CongA_F_A_D_B_D_A &
		CongA_D_A_F_B_D_A &
		CongA_E_A_D_A_D_C &
		CongA_E_A_D_C_D_A &
		CongA_D_A_E_C_D_A &
		Par_E_F_B_C &
		Cong_E_A_D_C &
		Cong_A_F_B_D &
		Cong_A_S_S_D &
		Cong_E_S_S_C &
		Cong_B_S_S_F &
		BetS_E_S_C &
		BetS_B_S_F &
		BetS_A_S_D
	).
	exists E, F, S.
	split.
	exact BetS_E_A_F.
	split.
	exact CongA_E_A_D_A_D_C.
	split.
	exact Par_E_F_B_C.
	split.
	exact BetS_E_S_C.
	exact BetS_A_S_D.
Qed.

End Euclid.

