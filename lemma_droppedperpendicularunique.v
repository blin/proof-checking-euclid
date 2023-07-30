Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Midpoint.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_collinear.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_reverse.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_altitudebisectsbase.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_midpointunique.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ABD.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_BCD_ACD.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_droppedperpendicularunique :
	forall A J M P,
	RightTriangle A M P ->
	RightTriangle A J P ->
	Col A M J ->
	eq M J.
Proof.
	intros A J M P.
	intros RightTriangle_AMP.
	intros RightTriangle_AJP.
	intros Col_A_M_J.

	pose proof (by_prop_Col_order _ _ _ Col_A_M_J) as (_ & Col_M_J_A & _ & _ & Col_J_M_A).

	assert (~ neq M J) as eq_M_J.
	{
		intros neq_M_J.

		pose proof (by_prop_neq_symmetric _ _ neq_M_J) as neq_J_M.

		pose proof (lemma_extension _ _ _ _ neq_M_J neq_M_J) as (E & BetS_M_J_E & _).

		pose proof (by_prop_BetS_notequal _ _ _ BetS_M_J_E) as (_ & _ & neq_M_E).
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_M_J_E) as BetS_E_J_M.

		pose proof (lemma_extension _ _ _ _ neq_J_M neq_M_E) as (F & BetS_J_M_F & Cong_MF_ME).

		pose proof (lemma_orderofpoints_ABC_BCD_ABD _ _ _ _ BetS_E_J_M BetS_J_M_F) as BetS_E_J_F.
		pose proof (lemma_orderofpoints_ABC_BCD_ACD _ _ _ _ BetS_E_J_M BetS_J_M_F) as BetS_E_M_F.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_J_F) as BetS_F_J_E.
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_M_F) as BetS_F_M_E.
		pose proof (by_prop_BetS_notequal _ _ _ BetS_E_J_F) as (neq_J_F & _ & _).
		pose proof (by_prop_BetS_notequal _ _ _ BetS_J_M_F) as (neq_M_F & _ & _).
		pose proof (by_prop_neq_symmetric _ _ neq_J_F) as neq_F_J.
		pose proof (by_prop_neq_symmetric _ _ neq_M_F) as neq_F_M.

		pose proof (by_prop_Cong_flip _ _ _ _ Cong_MF_ME) as (_ & Cong_FM_ME & _ ).

		pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_J_M_F) as Col_J_M_F.
		pose proof (by_prop_Col_order _ _ _ Col_J_M_F) as (Col_M_J_F & _ & _ & _ & _).

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_M_J_F Col_M_J_A neq_M_J) as Col_J_F_A.
		pose proof (by_prop_Col_order _ _ _ Col_J_F_A) as (_ & _ & Col_A_J_F & _ & _).

		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_AJP Col_A_J_F neq_F_J) as RightTriangle_FJP.

		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_J_M_F Col_J_M_A neq_J_M) as Col_M_F_A.
		pose proof (by_prop_Col_order _ _ _ Col_M_F_A) as (_ & _ & Col_A_M_F & _ & _).

		pose proof (by_prop_RightTriangle_collinear _ _ _ _ RightTriangle_AMP Col_A_M_F neq_F_M) as RightTriangle_FMP.
		pose proof (by_prop_RightTriangle_reverse _ _ _ _ RightTriangle_FMP BetS_F_M_E Cong_FM_ME) as Cong_FP_EP.
		pose proof (lemma_altitudebisectsbase _ _ _ _ BetS_F_J_E Cong_FP_EP RightTriangle_FJP) as Midpoint_F_J_E.
		pose proof (by_def_Midpoint _ _ _ BetS_F_M_E Cong_FM_ME) as Midpoint_F_M_E.
		pose proof (lemma_midpointunique _ _ _ _ Midpoint_F_J_E Midpoint_F_M_E) as eq_J_M.

		contradict eq_J_M.
		exact neq_J_M.
	}
	apply Classical_Prop.NNPP in eq_M_J.

	exact eq_M_J.
Qed.

End Euclid.
