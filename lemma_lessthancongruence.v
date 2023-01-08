Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_betweennesspreserved.
Require Import ProofCheckingEuclid.lemma_betweennotequal.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_lessthancongruence :
	forall A B C D E F,
	Lt A B C D ->
	Cong C D E F ->
	Lt A B E F.
Proof.

	intros A B C D E F.
	intros Lt_AB_CD.
	intros Cong_CD_EF.

	unfold Lt in Lt_AB_CD.
	destruct Lt_AB_CD as (G & BetS_C_G_D & Cong_CG_AB).

	pose proof (lemma_betweennotequal _ _ _ BetS_C_G_D) as (neq_G_D & neq_C_G & neq_C_D).
	pose proof (axiom_nocollapse _ _ _ _ neq_C_D Cong_CD_EF) as neq_E_F.
	pose proof (lemma_inequalitysymmetric _ _ neq_E_F) as neq_F_E.

	pose proof (lemma_extension _ _ _ _ neq_F_E neq_F_E) as (P & BetS_F_E_P & Cong_EP_FE).
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_F_E_P) as BetS_P_E_F.
	pose proof (lemma_betweennotequal _ _ _ BetS_P_E_F) as (_ & neq_P_E & neq_P_F).
	pose proof (axiom_nocollapse _ _ _ _ neq_C_G Cong_CG_AB) as neq_A_B.

	pose proof (lemma_extension _ _ _ _ neq_P_E neq_A_B) as (H & BetS_P_E_H & Cong_EH_AB).

	pose proof (lemma_inequalitysymmetric _ _ neq_C_D) as neq_D_C.
	pose proof (lemma_inequalitysymmetric _ _ neq_P_E) as neq_E_P.
	pose proof (lemma_extension _ _ _ _ neq_D_C neq_E_P) as (Q & BetS_D_C_Q & Cong_CQ_EP).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_CQ_EP) as (Cong_QC_PE & _ & _).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_C_Q) as BetS_Q_C_D.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_Q_C_D BetS_C_G_D) as BetS_Q_C_G.


	pose proof (
		cn_sumofparts
		Q C D
		P E F
		Cong_QC_PE Cong_CD_EF
		BetS_Q_C_D BetS_P_E_F
	) as Cong_QD_PF.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_QD_PF) as (Cong_DQ_FP & _).
	pose proof (lemma_congruenceflip _ _ _ _ Cong_CD_EF) as (Cong_DC_FE & _).
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_EH_AB) as Cong_AB_EH.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_CG_AB Cong_AB_EH) as Cong_CG_EH.

	(* △QCD , △PEF are degenerate and SSS congruent. *)
	(* △DCG , △FEH are degenerate and SAS congruent. *)
	(* ∠QCD is supplement to ∠DCG and ∠PEF is supplement to ∠FEH . *)
	(* △DCG ≅ △FEH implies that GD ≅ HF . *)
	pose proof (
		axiom_5_line

		Q C G D
		P E H F

		Cong_QC_PE
		Cong_CD_EF
		Cong_DQ_FP

		BetS_Q_C_G
		BetS_P_E_H

		Cong_DC_FE
		Cong_CG_EH
	) as Cong_GD_HF.

	pose proof (
		lemma_betweennesspreserved

		C G D
		E H F

		Cong_CG_EH
		Cong_CD_EF
		Cong_GD_HF

		BetS_C_G_D
	) as BetS_E_H_F.

	unfold Lt.
	exists H.
	split.
	exact BetS_E_H_F.
	exact Cong_EH_AB.
Qed.

End Euclid.
