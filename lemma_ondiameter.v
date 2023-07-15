Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_equalitysymmetric.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_s_incirc_centre.
Require Import ProofCheckingEuclid.lemma_s_incirc_within_radius.
Require Coq.Logic.Classical_Prop.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_ondiameter :
	forall D F K M N P Q,
	CI K F P Q ->
	Cong F D P Q ->
	Cong F M P Q ->
	BetS D F M ->
	BetS D N M ->
	InCirc N K.
Proof.
	intros D F K M N P Q.
	intros CI_K_F_P_Q.
	intros Cong_FD_PQ.
	intros Cong_FM_PQ.
	intros BetS_D_F_M.
	intros BetS_D_N_M.

	pose proof (cn_congruencereflexive F N) as Cong_FN_FN.

	pose proof (lemma_betweennotequal _ _ _ BetS_D_F_M) as (_ & neq_D_F & _).
	pose proof (lemma_inequalitysymmetric _ _ neq_D_F) as neq_F_D.

	assert (~ ~ (BetS D N F \/ BetS F N M \/ eq F N)) as n_n_BetS_D_N_F_or_BetS_F_N_M_or_eq_F_N.
	{
		intro n_BetS_D_N_F_or_BetS_F_N_M_or_eq_F_N.

		apply Classical_Prop.not_or_and in n_BetS_D_N_F_or_BetS_F_N_M_or_eq_F_N.
		destruct n_BetS_D_N_F_or_BetS_F_N_M_or_eq_F_N as (n_BetS_D_N_F & n_BetS_F_N_M_or_eq_F_N).
		apply Classical_Prop.not_or_and in n_BetS_F_N_M_or_eq_F_N.
		destruct n_BetS_F_N_M_or_eq_F_N as (n_BetS_F_N_M & neq_F_N).

		assert (~ BetS D F N) as n_BetS_D_F_N.
		{
			intro BetS_D_F_N.

			pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_D_F_N BetS_D_N_M) as BetS_F_N_M.

			contradict BetS_F_N_M.
			exact n_BetS_F_N_M.
		}

		pose proof (axiom_connectivity _ _ _ _ BetS_D_F_M BetS_D_N_M n_BetS_D_F_N n_BetS_D_N_F) as eq_F_N.

		contradict eq_F_N.
		exact neq_F_N.
	}
	assert (BetS_D_N_F_or_BetS_F_N_M_or_eq_F_N := n_n_BetS_D_N_F_or_BetS_F_N_M_or_eq_F_N).
	apply Classical_Prop.NNPP in BetS_D_N_F_or_BetS_F_N_M_or_eq_F_N.


	(* assert by cases *)
	assert (InCirc N K) as InCirc_N_K.
	destruct BetS_D_N_F_or_BetS_F_N_M_or_eq_F_N as [BetS_D_N_F | [ BetS_F_N_M | eq_F_N]].
	{
		(* case BetS_D_N_F *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_N_F) as BetS_F_N_D.
		pose proof (lemma_s_incirc_within_radius _ _ _ _ _ _ _ CI_K_F_P_Q BetS_F_N_D Cong_FD_PQ Cong_FN_FN) as InCirc_N_K.

		exact InCirc_N_K.
	}
	{
		(* case BetS_F_N_M *)
		pose proof (lemma_s_incirc_within_radius _ _ _ _ _ _ _ CI_K_F_P_Q BetS_F_N_M Cong_FM_PQ Cong_FN_FN) as InCirc_N_K.

		exact InCirc_N_K.
	}
	{
		(* case eq_F_N *)
		pose proof (lemma_equalitysymmetric _ _ eq_F_N) as eq_N_F.
		assert (CI K N P Q) as CI_K_N_P_Q by (rewrite eq_N_F; exact CI_K_F_P_Q).

		pose proof (lemma_s_incirc_centre _ _ _ _ CI_K_N_P_Q) as InCirc_N_K.

		exact InCirc_N_K.
	}
	exact InCirc_N_K.
Qed.

End Euclid.
