Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma by_prop_CongA_ABCequalsCBA :
	forall A B C,
	nCol A B C ->
	CongA A B C C B A.
Proof.
	intros A B C.
	intros nCol_A_B_C.

	pose proof (
		by_prop_nCol_distinct _ _ _ nCol_A_B_C
	) as (neq_A_B & neq_B_C & _ & neq_B_A & neq_C_B & _).
	pose proof (lemma_extension _ _ _ _ neq_B_A neq_C_B) as (E & BetS_B_A_E & Cong_AE_CB).
	pose proof (lemma_extension _ _ _ _ neq_B_C neq_A_B) as (F & BetS_B_C_F & Cong_CF_AB).

	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_CF_AB) as (Cong_BA_FC & _).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_F) as BetS_F_C_B.
	pose proof (
		cn_sumofparts _ _ _ _ _ _ Cong_BA_FC Cong_AE_CB BetS_B_A_E BetS_F_C_B
	) as Cong_BE_FB.
	pose proof (cn_congruencereverse F B) as Cong_FB_BF.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BE_FB Cong_FB_BF) as Cong_BE_BF.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BE_BF) as Cong_BF_BE.
	pose proof (cn_congruencereverse E F) as Cong_EF_FE.

	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_A_E neq_B_A) as OnRay_BA_E.
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_B_C_F neq_B_C) as OnRay_BC_F.

	pose proof (
		by_def_CongA
		_ _ _ _ _ _ _ _ _ _
		OnRay_BA_E
		OnRay_BC_F
		OnRay_BC_F
		OnRay_BA_E
		Cong_BE_BF
		Cong_BF_BE
		Cong_EF_FE
		nCol_A_B_C
	) as CongA_ABC_CBA.

	exact CongA_ABC_CBA.
Qed.

End Euclid.
