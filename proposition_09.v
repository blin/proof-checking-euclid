Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.euclidean_tactics.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinear_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_onray_impliescollinear.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_s_conga.
Require Import ProofCheckingEuclid.lemma_s_n_col_ncol.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.proposition_10.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_09 : 
	forall A B C,
	nCol B A C ->
	exists X, CongA B A X X A C /\ InAngle B A C X.
Proof.
	intros A B C.
	intros nCol_B_A_C.

	pose proof (lemma_NCorder _ _ _ nCol_B_A_C) as (nCol_A_B_C & nCol_A_C_B & nCol_C_B_A & nCol_B_C_A & nCol_C_A_B).

	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.

	pose proof (lemma_layoff _ _ _ _ neq_A_C neq_A_B) as (E & OnRay_AC_E & Cong_AE_AB).

	pose proof (lemma_onray_impliescollinear _ _ _ OnRay_AC_E) as Col_A_C_E.
	pose proof (lemma_onray_strict _ _ _ OnRay_AC_E) as neq_A_E.
	pose proof (lemma_inequalitysymmetric _ _ neq_A_E) as neq_E_A.
	pose proof (lemma_collinearorder _ _ _ Col_A_C_E) as (_ & _ & Col_E_A_C & _ & _).

	assert (~ eq B E) as neq_B_E.
	{
		intros eq_B_E.

		assert (Col A B E) as Col_A_B_E by (unfold Col; one_of_disjunct eq_B_E).

		pose proof (lemma_collinearorder _ _ _ Col_A_B_E) as (_ & _ & Col_E_A_B & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_A_B Col_E_A_C neq_E_A) as Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}

	pose proof (proposition_10 _ _ neq_B_E) as (F & BetS_B_F_E & Cong_FB_FE).

	pose proof (cn_congruencereflexive A F) as Cong_AF_AF.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_AE_AB) as Cong_AB_AE.
	pose proof (lemma_doublereverse _ _ _ _ Cong_FB_FE) as (Cong_EF_BF & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_EF_BF) as Cong_BF_EF.

	assert (~ Col B A F) as n_Col_B_A_F.
	{
		intros Col_B_A_F.

		assert (Col B F E) as Col_B_F_E by (unfold Col; one_of_disjunct BetS_B_F_E).
		pose proof (lemma_collinearorder _ _ _ Col_B_F_E) as (Col_F_B_E & _ & _ & _ & _).

		pose proof (lemma_collinearorder _ _ _ Col_B_A_F) as (_ & _ & Col_F_B_A & _ & _).

		pose proof (lemma_betweennotequal _ _ _ BetS_B_F_E) as (_ & neq_B_F & _).

		pose proof (lemma_inequalitysymmetric _ _ neq_B_F) as neq_F_B.
		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_F_B_E Col_F_B_A neq_F_B) as Col_B_E_A.
		pose proof (lemma_collinearorder _ _ _ Col_B_E_A) as (_ & Col_E_A_B & _ & _ & _).

		pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_E_A_B Col_E_A_C neq_E_A) as Col_A_B_C.

		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (lemma_s_n_col_ncol _ _ _ n_Col_B_A_F) as nCol_B_A_F.
	pose proof (lemma_NCdistinct _ _ _ nCol_B_A_F) as (_ & neq_A_F & neq_B_F & _ & neq_F_A & neq_F_B).

	pose proof (lemma_s_onray_assert_ABB _ _ neq_A_B) as OnRay_AB_B.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_A_F) as OnRay_AF_F.

	pose proof (
		lemma_s_conga
		B A F C A F
		_ _ _ _
		OnRay_AB_B
		OnRay_AF_F
		OnRay_AC_E
		OnRay_AF_F
		Cong_AB_AE
		Cong_AF_AF
		Cong_BF_EF
		nCol_B_A_F
	) as CongA_BAF_CAF.

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_BAF_CAF) as CongA_CAF_BAF.
	assert (CongA_CAF_BAF2 := CongA_CAF_BAF).
	destruct CongA_CAF_BAF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nCol_C_A_F).
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_A_F) as CongA_CAF_FAC.
	pose proof (lemma_equalanglestransitive _ _ _ _ _ _ F A C CongA_BAF_CAF CongA_CAF_FAC) as CongA_BAF_FAC.

	assert (InAngle B A C F) as InAngle_BAC_F.
	unfold InAngle.
	exists B, E.
	split.
	exact OnRay_AB_B.
	split.
	exact OnRay_AC_E.
	exact BetS_B_F_E.

	exists F.
	split.
	exact CongA_BAF_FAC.
	exact InAngle_BAC_F.
Qed.

End Euclid.
