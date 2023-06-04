Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_interior5 :
	forall A B C D a b c d,
	BetS A B C ->
	BetS a b c ->
	Cong A B a b->
	Cong B C b c->
	Cong A D a d->
	Cong C D c d->
	Cong B D b d.
Proof.
	intros A B C D a b c d.
	intros BetS_A_B_C.
	intros BetS_a_b_c.
	intros Cong_AB_ab.
	intros Cong_BC_bc.
	intros Cong_AD_ad.
	intros Cong_CD_cd.

	pose proof (lemma_betweennotequal _ _ _ BetS_A_B_C) as (neq_B_C & _ & neq_A_C).
	assert (~ eq C A) as neq_C_A.
	{
		intros eq_C_A.

		pose proof (lemma_equalitysymmetric _ _ eq_C_A) as eq_A_C.

		contradict eq_A_C.
		exact neq_A_C.
	}
	pose proof (lemma_extension _ _ _ _ neq_C_A neq_B_C) as (M & BetS_C_A_M & Cong_AM_BC).
	pose proof (cn_congruencereverse M A) as Cong_MA_AM.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_MA_AM Cong_AM_BC) as Cong_MA_BC.

	pose proof (lemma_betweennotequal _ _ _ BetS_a_b_c) as (neq_b_c & _ & neq_a_c).
	assert (~ eq c a) as neq_c_a.
	{
		intros eq_c_a.

		pose proof (lemma_equalitysymmetric _ _ eq_c_a) as eq_a_c.

		contradict eq_a_c.
		exact neq_a_c.
	}
	pose proof (lemma_extension _ _ _ _ neq_c_a neq_b_c) as (m & BetS_c_a_m & Cong_am_bc).
	pose proof (cn_congruencereverse m a) as Cong_ma_am.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_ma_am Cong_am_bc) as Cong_ma_bc.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_ma_bc) as Cong_bc_ma.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_BC_bc Cong_bc_ma) as Cong_BC_ma.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_MA_BC Cong_BC_ma) as Cong_MA_ma.
	pose proof (
		cn_sumofparts _ _ _ _ _ _ Cong_AB_ab Cong_BC_bc BetS_A_B_C BetS_a_b_c
	) as Cong_AC_ac.
	pose proof (lemma_doublereverse _ _ _ _ Cong_AC_ac) as (_ & Cong_CA_ca).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_MA_ma) as (Cong_AM_am & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_CD_cd) as (Cong_DC_dc & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_AD_ad) as (Cong_DA_da & _).

	pose proof (
		axiom_5_line
		C A M D
		c a m d

		Cong_AM_am
		Cong_CD_cd
		Cong_AD_ad
		BetS_C_A_M
		BetS_c_a_m
		Cong_CA_ca
	) as Cong_DM_dm.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_DM_dm) as (Cong_MD_md & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_B_C) as BetS_C_B_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_a_b_c) as BetS_c_b_a.
	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_c_b_a BetS_c_a_m) as BetS_b_a_m.
	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_C_B_A BetS_C_A_M) as BetS_B_A_M.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_b_a_m) as BetS_m_a_b.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_M) as BetS_M_A_B.

	pose proof (
		axiom_5_line
		M A B D
		m a b d

		Cong_AB_ab
		Cong_MD_md
		Cong_AD_ad
		BetS_M_A_B
		BetS_m_a_b
		Cong_MA_ma
	) as Cong_DB_db.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_DB_db) as (Cong_BD_bd & _).

	exact Cong_BD_bd.
Qed.

End Euclid.
