Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_21helper.
Require Import ProofCheckingEuclid.lemma_ABCequalsCBA.
Require Import ProofCheckingEuclid.lemma_NCdistinct.
Require Import ProofCheckingEuclid.lemma_NChelper.
Require Import ProofCheckingEuclid.lemma_NCorder.
Require Import ProofCheckingEuclid.lemma_TTflip.
Require Import ProofCheckingEuclid.lemma_TTflip2.
Require Import ProofCheckingEuclid.lemma_TTorder.
Require Import ProofCheckingEuclid.lemma_TTtransitive.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence.
Require Import ProofCheckingEuclid.lemma_angleorderrespectscongruence_smaller.
Require Import ProofCheckingEuclid.lemma_angleordertransitive.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_collinearorder.
Require Import ProofCheckingEuclid.lemma_equalangleshelper.
Require Import ProofCheckingEuclid.lemma_equalanglesreflexive.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_s_col_BetS_A_B_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_A_C.
Require Import ProofCheckingEuclid.lemma_s_col_eq_B_C.
Require Import ProofCheckingEuclid.lemma_s_ncol_triangle.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_ABB.
Require Import ProofCheckingEuclid.lemma_s_onray_assert_bets_ABE.
Require Import ProofCheckingEuclid.proposition_16.
Require Import ProofCheckingEuclid.proposition_20.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_21 :
	forall A B C D E,
	Triangle A B C ->
	BetS A E C ->
	BetS B D E ->
	TT B A A C B D D C /\ LtA B A C B D C.
Proof.
	intros A B C D E.
	intros Triangle_ABC.
	intros BetS_A_E_C.
	intros BetS_B_D_E.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq E E) as eq_E_E by (reflexivity).
	pose proof (lemma_s_col_eq_A_C A C A eq_A_A) as Col_A_C_A.
	pose proof (lemma_s_col_eq_A_C E B E eq_E_E) as Col_E_B_E.
	pose proof (lemma_s_col_eq_B_C A C C eq_C_C) as Col_A_C_C.
	pose proof (lemma_s_col_eq_B_C E B B eq_B_B) as Col_E_B_B.

	pose proof (lemma_s_ncol_triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (lemma_NCorder _ _ _ nCol_A_B_C) as (nCol_B_A_C & nCol_B_C_A & nCol_C_A_B & nCol_A_C_B & nCol_C_B_A).
	pose proof (lemma_NCdistinct _ _ _ nCol_A_B_C) as (neq_A_B & neq_B_C & neq_A_C & neq_B_A & neq_C_B & neq_C_A).

	pose proof (lemma_betweennotequal _ _ _ BetS_A_E_C) as (neq_E_C & neq_A_E & _).
	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_A_E_C) as Col_A_E_C.

	pose proof (lemma_collinearorder _ _ _ Col_A_E_C) as (Col_E_A_C & Col_E_C_A & Col_C_A_E & Col_A_C_E & Col_C_E_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_D_E) as BetS_E_D_B.
	pose proof (lemma_betweennotequal _ _ _ BetS_B_D_E) as (_ & neq_B_D & _).
	pose proof (lemma_betweennotequal _ _ _ BetS_E_D_B) as (_ & neq_E_D & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_B_D) as neq_D_B.

	pose proof (lemma_s_col_BetS_A_B_C _ _ _ BetS_E_D_B) as Col_E_D_B.
	pose proof (lemma_collinearorder _ _ _ Col_E_D_B) as (Col_D_E_B & Col_D_B_E & Col_B_E_D & Col_E_B_D & Col_B_D_E).

	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_C_B Col_A_C_A Col_A_C_E neq_A_E) as nCol_A_E_B.
	pose proof (lemma_NCorder _ _ _ nCol_A_E_B) as (nCol_E_A_B & nCol_E_B_A & nCol_B_A_E & nCol_A_B_E & nCol_B_E_A). (* wanted nCol_A_B_E *)
	pose proof (lemma_NChelper _ _ _ _ _ nCol_A_C_B Col_A_C_E Col_A_C_C neq_E_C) as nCol_E_C_B.
	pose proof (lemma_NCorder _ _ _ nCol_E_C_B) as (nCol_C_E_B & nCol_C_B_E & nCol_B_E_C & nCol_E_B_C & nCol_B_C_E). (* wanted nCol_E_B_C *)
	pose proof (lemma_NChelper _ _ _ _ _ nCol_E_B_C Col_E_B_E Col_E_B_D neq_E_D) as nCol_E_D_C.
	pose proof (lemma_NCorder _ _ _ nCol_E_D_C) as (nCol_D_E_C & nCol_D_C_E & nCol_C_E_D & nCol_E_C_D & nCol_C_D_E). (* wanted nCol_E_C_D *)
	pose proof (lemma_NChelper _ _ _ _ _ nCol_E_B_C Col_E_B_D Col_E_B_B neq_D_B) as nCol_D_B_C.
	pose proof (lemma_NCorder _ _ _ nCol_D_B_C) as (nCol_B_D_C & nCol_B_C_D & nCol_C_D_B & nCol_D_C_B & nCol_C_B_D). (* wanted nCol_B_D_C *)

	pose proof (by_def_Triangle _ _ _ nCol_A_B_E) as Triangle_ABE.
	pose proof (by_def_Triangle _ _ _ nCol_B_A_E) as Triangle_BAE.
	pose proof (by_def_Triangle _ _ _ nCol_C_E_D) as Triangle_CED.
	pose proof (by_def_Triangle _ _ _ nCol_E_C_D) as Triangle_ECD.

	pose proof (proposition_20 _ _ _ Triangle_ABE) as TogetherGreater_BA_AE_BE.
	pose proof (proposition_20 _ _ _ Triangle_ECD) as TogetherGreater_CE_ED_CD.

	pose proof (lemma_21helper _ _ _ _ TogetherGreater_BA_AE_BE BetS_A_E_C) as TT_B_A_A_C_B_E_E_C.
	pose proof (lemma_21helper _ _ _ _ TogetherGreater_CE_ED_CD BetS_E_D_B) as TT_C_E_E_B_C_D_D_B.
	pose proof (lemma_TTorder _ _ _ _ _ _ _ _ TT_C_E_E_B_C_D_D_B) as TT_E_B_C_E_C_D_D_B.
	pose proof (lemma_TTflip _ _ _ _ _ _ _ _ TT_E_B_C_E_C_D_D_B) as TT_B_E_E_C_C_D_D_B.
	pose proof (lemma_TTtransitive _ _ _ _ _ _ _ _ _ _ _ _ TT_B_A_A_C_B_E_E_C TT_B_E_E_C_C_D_D_B) as TT_B_A_A_C_C_D_D_B.
	pose proof (lemma_TTflip2 _ _ _ _ _ _ _ _ TT_B_A_A_C_C_D_D_B) as TT_B_A_A_C_B_D_D_C.

	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_D_C) as CongA_BDC_CDB.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_D_E_C) as CongA_DEC_CED.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_C_E_B) as CongA_CEB_BEC.
	pose proof (lemma_ABCequalsCBA _ _ _ nCol_B_A_E) as CongA_BAE_EAB.

	pose proof (lemma_s_onray_assert_ABB _ _ neq_A_B) as OnRay_AB_B.
	pose proof (lemma_s_onray_assert_ABB _ _ neq_E_C) as OnRay_EC_C.
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_A_E_C neq_A_E) as OnRay_AE_C.
	pose proof (lemma_s_onray_assert_bets_ABE _ _ _ BetS_E_D_B neq_E_D) as OnRay_ED_B.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_AE_C) as OnRay_AC_E.

	pose proof (lemma_equalanglesreflexive _ _ _ nCol_B_A_C) as CongA_BAC_BAC.
	pose proof (lemma_equalanglesreflexive _ _ _ nCol_C_E_D) as CongA_CED_CED.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_BAC_BAC OnRay_AB_B OnRay_AC_E) as CongA_BAC_BAE.
	pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ CongA_CED_CED OnRay_EC_C OnRay_ED_B) as CongA_CED_CEB.

	pose proof (proposition_16 _ _ _ _ Triangle_CED BetS_E_D_B) as (_ & LtA_DEC_CDB).
	pose proof (proposition_16 _ _ _ _ Triangle_BAE BetS_A_E_C) as (_ & LtA_EAB_BEC).

	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_EAB_BEC CongA_BAE_EAB) as LtA_BAE_BEC.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_BAE_BEC CongA_CEB_BEC) as LtA_BAE_CEB.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_BAE_CEB CongA_CED_CEB) as LtA_BAE_CED.
	pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ LtA_BAE_CED CongA_BAC_BAE) as LtA_BAC_CED.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_BAC_CED CongA_DEC_CED) as LtA_BAC_DEC.
	pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_BAC_DEC LtA_DEC_CDB) as LtA_BAC_CDB.
	pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_BAC_CDB CongA_BDC_CDB) as LtA_BAC_BDC.

	split.
	exact TT_B_A_A_C_B_D_D_C.
	exact LtA_BAC_BDC.
Qed.

End Euclid.
