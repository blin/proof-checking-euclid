Require Import ProofCheckingEuclid.by_def_Lt.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_lessthancongruence.
Require Import ProofCheckingEuclid.lemma_lessthantransitive.
Require Import ProofCheckingEuclid.lemma_partnotequalwhole.
Require Coq.Logic.Classical_Prop.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_midpointunique :
	forall A B C D,
	Midpoint A B C ->
	Midpoint A D C ->
	eq B D.
Proof.
	intros A B C D.
	intros Midpoint_A_B_C.
	intros Midpoint_A_D_C.

	destruct Midpoint_A_B_C as (BetS_A_B_C & Cong_AB_BC).
	destruct Midpoint_A_D_C as (BetS_A_D_C & Cong_AD_DC).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_C) as BetS_C_B_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_D_C) as BetS_C_D_A.

	pose proof (cn_congruencereflexive A B) as Cong_AB_AB.
	pose proof (cn_congruencereflexive A D) as Cong_AD_AD.
	pose proof (cn_congruencereflexive C B) as Cong_CB_CB.
	pose proof (cn_congruencereflexive C D) as Cong_CD_CD.
	pose proof (cn_congruencereverse C B) as Cong_CB_BC.
	pose proof (cn_congruencereverse C D) as Cong_CD_DC.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_AB_BC) as (_ & _ & Cong_AB_CB).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AD_DC) as (_ & _ & Cong_AD_CD).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AB_BC) as Cong_BC_AB.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AD_DC) as Cong_DC_AD.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_CD_DC) as Cong_DC_CD.

	pose proof (lemma_congruenceflip _ _ _ _ Cong_DC_AD) as (_ & Cong_CD_AD & _).

	assert (~ BetS C D B) as nBetS_C_D_B.
	{
		intros BetS_C_D_B.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_D_B) as BetS_B_D_C.
		pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_A_B_C BetS_B_D_C) as BetS_A_B_D.
		pose proof (by_def_Lt _ _ _ _ _ BetS_A_B_D Cong_AB_AB) as Lt_AB_AD.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_AB_AD Cong_AD_CD) as Lt_AB_CD.

		pose proof (by_def_Lt _ _ _ _ _ BetS_C_D_B Cong_CD_CD) as Lt_CD_CB.
		pose proof (lemma_lessthantransitive _ _ _ _ _ _ Lt_AB_CD Lt_CD_CB) as Lt_AB_CB.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_AB_CB Cong_CB_BC) as Lt_AB_BC.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_AB_BC Cong_BC_AB) as Lt_AB_AB.

		destruct Lt_AB_AB as (E & BetS_A_E_B & Cong_AE_AB).
		pose proof (lemma_partnotequalwhole _ _ _ BetS_A_E_B) as nCong_AE_AB.

		contradict Cong_AE_AB.
		exact nCong_AE_AB.
	}

	assert (~ BetS C B D) as nBetS_C_B_D.
	{
		intros BetS_C_B_D.

		pose proof (axiom_betweennesssymmetry _ _ _ BetS_C_B_D) as BetS_D_B_C.
		pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_A_D_C BetS_D_B_C) as BetS_A_D_B.
		pose proof (by_def_Lt _ _ _ _ _ BetS_A_D_B Cong_AD_AD) as Lt_AD_AB.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_AD_AB Cong_AB_CB) as Lt_AD_CB.

		pose proof (by_def_Lt _ _ _ _ _ BetS_C_B_D Cong_CB_CB) as Lt_CB_CD.
		pose proof (lemma_lessthantransitive _ _ _ _ _ _ Lt_AD_CB Lt_CB_CD) as Lt_AD_CD.
		pose proof (lemma_lessthancongruence _ _ _ _ _ _ Lt_AD_CD Cong_CD_AD) as Lt_AD_AD.

		destruct Lt_AD_AD as (F & BetS_A_F_D & Cong_AF_AD).
		pose proof (lemma_partnotequalwhole _ _ _ BetS_A_F_D) as nCong_AF_AD.

		contradict Cong_AF_AD.
		exact nCong_AF_AD.
	}

	pose proof (
		axiom_connectivity
		_ _ _ _
		BetS_C_B_A
		BetS_C_D_A
		nBetS_C_B_D
		nBetS_C_D_B
	) as eq_B_D.

	exact eq_B_D.
Qed.

End Euclid.
