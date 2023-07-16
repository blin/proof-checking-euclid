Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_congruenceflip.
Require Import ProofCheckingEuclid.lemma_congruencesymmetric.
Require Import ProofCheckingEuclid.lemma_congruencetransitive.
Require Import ProofCheckingEuclid.lemma_doublereverse.
Require Import ProofCheckingEuclid.lemma_equalanglessymmetric.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_inequalitysymmetric.
Require Import ProofCheckingEuclid.lemma_onray_ABC_ACB.
Require Import ProofCheckingEuclid.lemma_onray_strict.
Require Import ProofCheckingEuclid.lemma_right_triangle_leg_change.
Require Import ProofCheckingEuclid.lemma_right_triangle_symmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equaltorightisright :
	forall A B C a b c,
	RightTriangle A B C ->
	CongA a b c A B C ->
	RightTriangle a b c.
Proof.
	intros A B C a b c.
	intros RightTriangle_ABC.
	intros CongA_abc_ABC.

	pose proof (lemma_equalanglessymmetric _ _ _ _ _ _ CongA_abc_ABC) as CongA_ABC_abc.

	destruct CongA_ABC_abc as (E & F & e & f & OnRay_BA_E & OnRay_BC_F & OnRay_ba_e & OnRay_bc_f & Cong_BE_be & Cong_BF_bf & Cong_EF_ef & _).

	pose proof (lemma_onray_strict _ _ _ OnRay_BA_E) as neq_B_E.

	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_ba_e) as OnRay_be_a.
	pose proof (lemma_onray_ABC_ACB _ _ _ OnRay_bc_f) as OnRay_bf_c.
	pose proof (lemma_onray_strict _ _ _ OnRay_bc_f) as neq_b_f.

	pose proof (lemma_doublereverse _ _ _ _ Cong_BE_be) as (Cong_eb_EB & _).
	pose proof (axiom_nocollapse _ _ _ _ neq_B_E Cong_BE_be) as neq_b_e.
	pose proof (lemma_inequalitysymmetric _ _ neq_b_e) as neq_e_b.

	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_BF_bf) as Cong_bf_BF.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_EF_ef) as Cong_ef_EF.

	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_ABC OnRay_BC_F) as RightTriangle_ABF.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_ABF) as RightTriangle_FBA.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_FBA OnRay_BA_E) as RightTriangle_FBE.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_FBE) as RightTriangle_EBF.

	destruct RightTriangle_EBF as (W & BetS_E_B_W & Cong_EB_WB & Cong_EF_WF & _).

	pose proof (lemma_congruenceflip _ _ _ _ Cong_EB_WB) as (_ & _ & Cong_EB_BW).

	pose proof (lemma_extension _ _ _ _ neq_e_b neq_e_b) as (w & BetS_e_b_w & Cong_bw_eb).

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_bw_eb Cong_eb_EB) as Cong_bw_EB.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_bw_EB Cong_EB_BW) as Cong_bw_BW.
	pose proof (lemma_congruencesymmetric _ _ _ _ Cong_bw_BW) as Cong_BW_bw.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_eb_EB Cong_EB_BW) as Cong_eb_BW.
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_eb_BW Cong_BW_bw) as Cong_eb_bw.
	pose proof (lemma_congruenceflip _ _ _ _ Cong_eb_bw) as (_ & _ & Cong_eb_wb).
	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_ef_EF Cong_EF_WF) as Cong_ef_WF.

	pose proof (axiom_5_line _ _ _ _ _ _ _ _ Cong_bw_BW Cong_ef_EF Cong_bf_BF BetS_e_b_w BetS_E_B_W Cong_eb_EB) as Cong_fw_FW.
	pose proof (lemma_doublereverse _ _ _ _ Cong_fw_FW) as (Cong_WF_wf & _).

	pose proof (lemma_congruencetransitive _ _ _ _ _ _ Cong_ef_WF Cong_WF_wf) as Cong_ef_wf.

	pose proof (by_def_RightTriangle _ _ _ _ BetS_e_b_w Cong_eb_wb Cong_ef_wf neq_b_f) as RightTriangle_ebf.

	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_ebf OnRay_bf_c) as RightTriangle_ebc.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_ebc) as RightTriangle_cbe.
	pose proof (lemma_right_triangle_leg_change _ _ _ _ RightTriangle_cbe OnRay_be_a) as RightTriangle_cba.
	pose proof (lemma_right_triangle_symmetric _ _ _ RightTriangle_cba) as RightTriangle_abc.

	exact RightTriangle_abc.
Qed.

End Euclid.
