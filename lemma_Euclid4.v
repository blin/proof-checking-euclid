Require Import ProofCheckingEuclid.by_def_CongA.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_RightTriangle.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_CongA_symmetric.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_Cong_doublereverse.
Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.by_prop_Cong_transitive.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_NC.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_leg_change.
Require Import ProofCheckingEuclid.by_prop_RightTriangle_symmetric.
Require Import ProofCheckingEuclid.by_prop_TogetherGreater_flip.
Require Import ProofCheckingEuclid.by_prop_TogetherGreater_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_layoff.
Require Import ProofCheckingEuclid.lemma_layoffunique.
Require Import ProofCheckingEuclid.lemma_right_triangle_same_base_cong_side_cong_hypotenuse.
Require Import ProofCheckingEuclid.proposition_20.
Require Import ProofCheckingEuclid.proposition_22.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_Euclid4 :
	forall A B C a b c,
	RightTriangle A B C ->
	RightTriangle a b c ->
	CongA A B C a b c.
Proof.
	intros A B C a b c.
	intros RightTriangle_ABC.
	intros RightTriangle_abc.

	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq A A) as eq_A_A by (reflexivity).
	pose proof (cn_congruencereverse B A) as Cong_BA_AB.
	pose proof (cn_congruencereflexive B A) as Cong_BA_BA.

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_ABC) as nCol_A_B_C.
	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_abc) as nCol_a_b_c.

	assert (RightTriangle_ABC2 := RightTriangle_ABC).
	destruct RightTriangle_ABC2 as (D & BetS_A_B_D & Cong_AB_DB & _ & neq_B_C).

	assert (RightTriangle_abc2 := RightTriangle_abc).
	destruct RightTriangle_abc2 as (d & BetS_a_b_d & _ & _ & neq_b_c).

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_B_D) as (_ & neq_A_B & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_a_b_d) as (_ & neq_a_b & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_B) as neq_B_A.
	pose proof (by_prop_neq_symmetric _ _ neq_a_b) as neq_b_a.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_A) as OnRay_BA_A.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_C) as OnRay_BC_C.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AB_DB) as (_ & _ & Cong_AB_BD).

	pose proof (lemma_layoff _ _ _ _ neq_b_a neq_B_A) as (p & OnRay_ba_p & Cong_bp_BA).
	pose proof (lemma_layoff _ _ _ _ neq_b_c neq_B_C) as (q & OnRay_bc_q & Cong_bq_BC).

	assert (eq q q) as eq_q_q by (reflexivity).
	assert (eq p p) as eq_p_p by (reflexivity).
	pose proof (cn_congruencereverse q b) as Cong_qb_bq.
	pose proof (cn_congruencereflexive b p) as Cong_bp_bp.
	pose proof (cn_congruencereflexive b q) as Cong_bq_bq.
	pose proof (cn_congruencereflexive p q) as Cong_pq_pq.

	pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_abc OnRay_bc_q) as RightTriangle_abq.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_abq) as RightTriangle_qba.
	pose proof (by_prop_RightTriangle_leg_change _ _ _ _ RightTriangle_qba OnRay_ba_p) as RightTriangle_qbp.
	pose proof (by_prop_RightTriangle_symmetric _ _ _ RightTriangle_qbp) as RightTriangle_pbq.

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_pbq) as nCol_p_b_q.
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_p_b_q) as n_Col_p_b_q.
	pose proof (by_prop_nCol_order _ _ _ nCol_p_b_q) as (nCol_b_p_q & nCol_b_q_p & nCol_q_p_b & nCol_p_q_b & nCol_q_b_p).
	pose proof (by_prop_nCol_distinct _ _ _ nCol_p_b_q) as (neq_p_b & _ & neq_p_q & neq_b_p & neq_q_b & neq_q_p).

	destruct RightTriangle_pbq as (r & BetS_p_b_r & Cong_pb_rb & Cong_pq_rq & neq_b_q).

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_b_q) as OnRay_bq_q.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_b_p) as OnRay_bp_p.

	pose proof (by_def_Triangle _ _ _ nCol_p_b_q) as Triangle_pbq.
	pose proof (by_def_Triangle _ _ _ nCol_b_q_p) as Triangle_bqp.
	pose proof (by_def_Triangle _ _ _ nCol_q_p_b) as Triangle_qpb.

	pose proof (proposition_20 _ _ _ Triangle_pbq) as TogetherGreater_bp_pq_bq.
	pose proof (proposition_20 _ _ _ Triangle_bqp) as TogetherGreater_qb_bp_qp.
	pose proof (proposition_20 _ _ _ Triangle_qpb) as TogetherGreater_pq_qb_pb.

	pose proof (by_prop_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_qb_bp_qp) as (TogetherGreater_bq_bp_qp & _).
	pose proof (by_prop_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_bq_bp_qp) as (_ & TogetherGreater_bq_bp_pq).
	pose proof (by_prop_TogetherGreater_symmetric _ _ _ _ _ _ TogetherGreater_pq_qb_pb) as TogetherGreater_qb_pq_pb.
	pose proof (by_prop_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_qb_pq_pb) as (TogetherGreater_bq_pq_pb & _).
	pose proof (by_prop_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_bq_pq_pb) as (_ & TogetherGreater_bq_pq_bp).
	pose proof (by_prop_TogetherGreater_flip _ _ _ _ _ _ TogetherGreater_bp_pq_bq) as (_ & TogetherGreater_bp_pq_qb).

	pose proof (proposition_22 _ _ _ _ _ _ _ _ TogetherGreater_bq_bp_pq TogetherGreater_bq_pq_bp TogetherGreater_bp_pq_bq neq_B_A) as (E & F & Cong_BE_bp & Cong_BF_bq & Cong_EF_pq & OnRay_BA_E & _).

	assert (eq F F) as eq_F_F by (reflexivity).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_BF_bq) as Cong_bq_BF.
	pose proof (axiom_nocollapse _ _ _ _ neq_b_q Cong_bq_BF) as neq_B_F.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_B_F) as OnRay_BF_F.

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BE_bp Cong_bp_BA) as Cong_BE_BA.
	pose proof (lemma_layoffunique _ _ _ _ OnRay_BA_E OnRay_BA_A Cong_BE_BA) as eq_E_A.
	assert (Cong B A b p) as Cong_BA_bp by (rewrite <- eq_E_A; exact Cong_BE_bp).
	assert (Cong A F p q) as Cong_AF_pq by (rewrite <- eq_E_A; exact Cong_EF_pq).

	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_pb_rb) as Cong_rb_pb.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_AF_pq) as Cong_pq_AF.
	pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_bq_BC) as Cong_BC_bq.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_rb_pb) as (_ & Cong_br_pb & _).
	pose proof (by_prop_Cong_doublereverse _ _ _ _ Cong_BA_bp) as (Cong_pb_AB & _).
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_br_pb Cong_pb_AB) as Cong_br_AB.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AF_pq Cong_pq_rq) as Cong_AF_rq.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AF_rq) as (_ & _ & Cong_AF_qr).
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_BC_bq Cong_bq_BF) as Cong_BC_BF.
	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_br_AB Cong_AB_BD) as Cong_br_BD.

	(* △pbq and △ABF are SSS congruent. *)
	(* △qbr and △FBD are SAS congruent. *)
	(* ∠pbq is supplement to ∠qbr and ∠ABF is supplement to ∠FBD . *)
	(* △qbr ≅ △FBD implies that rq ≅ DF . *)
	pose proof (
		axiom_5_line
		p b r q
		A B D F

		Cong_br_BD
		Cong_pq_AF
		Cong_bq_BF
		BetS_p_b_r
		BetS_A_B_D
		Cong_pb_AB
	) as Cong_qr_FD.

	pose proof (by_prop_Cong_transitive _ _ _ _ _ _ Cong_AF_qr Cong_qr_FD) as Cong_AF_FD.
	pose proof (by_prop_Cong_flip _ _ _ _ Cong_AF_FD) as (_ & _ & Cong_AF_DF).

	pose proof (by_def_RightTriangle _ _ _ _ BetS_A_B_D Cong_AB_DB Cong_AF_DF neq_B_F) as RightTriangle_ABF.

	pose proof (by_prop_RightTriangle_NC _ _ _ RightTriangle_ABF) as nCol_A_B_F.

	pose proof (lemma_right_triangle_same_base_cong_side_cong_hypotenuse _ _ _ _ RightTriangle_ABC RightTriangle_ABF Cong_BC_BF) as Cong_AC_AF.

	pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_BA_A OnRay_BC_C OnRay_BA_A OnRay_BF_F Cong_BA_BA Cong_BC_BF Cong_AC_AF nCol_A_B_C) as CongA_ABC_ABF.
	pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_BA_E OnRay_BF_F OnRay_bp_p OnRay_bq_q Cong_BE_bp Cong_BF_bq Cong_EF_pq nCol_A_B_F) as CongA_ABF_pbq.
	pose proof (by_def_CongA _ _ _ _ _ _ _ _ _ _ OnRay_ba_p OnRay_bc_q OnRay_bp_p OnRay_bq_q Cong_bp_bp Cong_bq_bq Cong_pq_pq nCol_a_b_c) as CongA_abc_pbq.

	pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_abc_pbq) as CongA_pbq_abc.

	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_ABF CongA_ABF_pbq) as CongA_ABC_pbq.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_pbq CongA_pbq_abc) as CongA_ABC_abc.

	exact CongA_ABC_abc.
Qed.

End Euclid.
