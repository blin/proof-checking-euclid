Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_B.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_Parallelogram.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_flip.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_Par_NC.
Require Import ProofCheckingEuclid.by_prop_Par_collinear.
Require Import ProofCheckingEuclid.by_prop_Par_flip.
Require Import ProofCheckingEuclid.by_prop_Par_symmetric.
Require Import ProofCheckingEuclid.by_prop_Par_to_TarskiPar.
Require Import ProofCheckingEuclid.by_prop_SameSide_flip.
Require Import ProofCheckingEuclid.by_prop_SameSide_symmetric.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_orderofpoints_ABC_ACD_BCD.
Require Import ProofCheckingEuclid.lemma_sameside_onray_EFAC_BFG_EGAC.
Require Import ProofCheckingEuclid.lemma_samesidecollinear.
Require Import ProofCheckingEuclid.lemma_samesidetransitive.
Require Import ProofCheckingEuclid.lemma_supplements_SumTwoRT.
Require Import ProofCheckingEuclid.proposition_28D.
Require Import ProofCheckingEuclid.proposition_29C.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_43B :
	forall A B C D E F G H K,
	Parallelogram A B C D ->
	BetS A H D ->
	BetS A E B ->
	BetS D F C ->
	BetS B G C ->
	Parallelogram E A H K ->
	Parallelogram G K F C ->
	Parallelogram E K G B.
Proof.
	intros A B C D E F G H K.
	intros Parallelogram_A_B_C_D.
	intros BetS_A_H_D.
	intros BetS_A_E_B.
	intros BetS_D_F_C.
	intros BetS_B_G_C.
	intros Parallelogram_E_A_H_K.
	intros Parallelogram_G_K_F_C.

	assert (eq B B) as eq_B_B by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	pose proof (by_def_Col_from_eq_A_B B B E eq_B_B) as Col_B_B_E.
	pose proof (by_def_Col_from_eq_B_C B C C eq_C_C) as Col_B_C_C.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_H_D) as (_ & neq_A_H & _).

	pose proof (by_def_OnRay_from_BetS_A_B_E A H D BetS_A_H_D neq_A_H) as OnRay_A_H_D.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_A_H_D) as OnRay_A_D_H.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_B) as BetS_B_E_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_B) as (neq_E_B & neq_A_E & neq_A_B).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_E_A) as (neq_E_A & neq_B_E & neq_B_A).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_B) as Col_A_E_B.
	pose proof (by_prop_Col_order _ _ _ Col_A_E_B) as (Col_E_A_B & Col_E_B_A & Col_B_A_E & Col_A_B_E & Col_B_E_A).
	
	pose proof (by_def_OnRay_from_BetS_A_B_E A E B BetS_A_E_B neq_A_E) as OnRay_A_E_B.
	pose proof (by_def_OnRay_from_BetS_A_B_E B E A BetS_B_E_A neq_B_E) as OnRay_B_E_A.
	pose proof (by_def_OnRay_from_neq_A_B B A neq_B_A) as OnRay_B_A_A.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_B_E_A) as OnRay_B_A_E.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_D_F_C) as BetS_C_F_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_D) as (_ & neq_C_F & _).

	pose proof (by_def_OnRay_from_BetS_A_B_E C F D BetS_C_F_D neq_C_F) as OnRay_C_F_D.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_C_F_D) as OnRay_C_D_F.
	
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_G_C) as BetS_C_G_B.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_G_C) as (neq_G_C & neq_B_G & neq_B_C).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_G_B) as (neq_G_B & neq_C_G & neq_C_B).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_G_C) as Col_B_G_C.
	pose proof (by_prop_Col_order _ _ _ Col_B_G_C) as (Col_G_B_C & Col_G_C_B & Col_C_B_G & Col_B_C_G & Col_C_G_B).

	pose proof (by_def_OnRay_from_BetS_A_B_E B G C BetS_B_G_C neq_B_G) as OnRay_B_G_C.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_B_G_C) as OnRay_B_C_G.
	
	assert (Parallelogram_A_B_C_D_2 := Parallelogram_A_B_C_D).
	destruct Parallelogram_A_B_C_D_2 as (Par_A_B_C_D & Par_A_D_B_C).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_B_C_D) as Par_C_D_A_B.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_A_D_B_C) as Par_B_C_A_D.
	pose proof (by_prop_Par_flip _ _ _ _ Par_C_D_A_B) as (_ & Par_C_D_B_A & _).
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_D_B_C) as (_ & _ & nCol_D_B_C & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_D_B_C) as (_ & _ & _ & nCol_D_C_B & _).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_D_C_B) as CongA_D_C_B_D_C_B.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_A_B_C_D) as TarskiPar_A_B_C_D.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_B_C_A_D) as TarskiPar_B_C_A_D.

	assert (TarskiPar_A_B_C_D_2 := TarskiPar_A_B_C_D).
	destruct TarskiPar_A_B_C_D_2 as (_ & neq_C_D & n_Meet_A_B_C_D & SameSide_C_D_A_B).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_C_D_A_B) as (SameSide_D_C_A_B & _ & _).
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_C_D_A_B) as SameSide_C_D_B_A.

	assert (TarskiPar_B_C_A_D_2 := TarskiPar_B_C_A_D).
	destruct TarskiPar_B_C_A_D_2 as (_ & neq_A_D & n_Meet_B_C_A_D & SameSide_A_D_B_C).

	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_A_D_B_C) as SameSide_A_D_C_B.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_D_C_B) as (SameSide_D_A_C_B & _ & _).
	
	assert (Parallelogram_E_A_H_K_2 := Parallelogram_E_A_H_K).
	destruct Parallelogram_E_A_H_K_2 as (Par_E_A_H_K & Par_E_K_A_H).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_E_K_A_H) as Par_A_H_E_K.
	pose proof (by_prop_Par_NC _ _ _ _ Par_A_H_E_K) as (nCol_A_H_E & _ & _ & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_H_E) as (_ & _ & nCol_E_A_H & _ & _).
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_E_A_H) as CongA_E_A_H_E_A_H.
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_E_A_H_K) as TarskiPar_E_A_H_K.

	assert (TarskiPar_E_A_H_K_2 := TarskiPar_E_A_H_K).
	destruct TarskiPar_E_A_H_K_2 as (_ & neq_H_K & n_Meet_E_A_H_K & SameSide_H_K_E_A).

	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_H_K_E_A) as (_ & SameSide_H_K_A_E & _).
	
	assert (Parallelogram_G_K_F_C_2 := Parallelogram_G_K_F_C).
	destruct Parallelogram_G_K_F_C_2 as (Par_G_K_F_C & Par_G_C_K_F).

	pose proof (by_prop_Par_symmetric _ _ _ _ Par_G_K_F_C) as Par_F_C_G_K.
	pose proof (by_prop_Par_flip _ _ _ _ Par_F_C_G_K) as (Par_C_F_G_K & _ & _).
	pose proof (by_prop_Par_to_TarskiPar _ _ _ _ Par_G_C_K_F) as TarskiPar_G_C_K_F.

	assert (TarskiPar_G_C_K_F_2 := TarskiPar_G_C_K_F).
	destruct TarskiPar_G_C_K_F_2 as (_ & neq_K_F & n_Meet_G_C_K_F & SameSide_K_F_G_C).

	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_K_F_G_C) as SameSide_K_F_C_G.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_K_F_C_G) as (SameSide_F_K_C_G & _ & _).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_E_A_H_E_A_H OnRay_A_E_B OnRay_A_H_D) as CongA_E_A_H_B_A_D.
	pose proof (by_prop_CongA_flip _ _ _ _ _ _ CongA_E_A_H_B_A_D) as CongA_H_A_E_D_A_B.
	
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_C_D_B_A Col_B_A_E neq_B_E) as SameSide_C_D_B_E.
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_C_D_B_E Col_B_A_E OnRay_A_D_H) as SameSide_C_H_B_E.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_H_K_E_A Col_E_A_B neq_E_B) as SameSide_H_K_E_B.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_H_K_E_B) as SameSide_H_K_B_E.
	pose proof (lemma_samesidetransitive _ _ _ _ _ SameSide_C_H_B_E SameSide_H_K_B_E) as SameSide_C_K_B_E.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_C_K_B_E) as (SameSide_K_C_B_E & _ & _).
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_K_C_B_E Col_B_B_E OnRay_B_C_G) as SameSide_K_G_B_E.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_K_G_B_E) as SameSide_K_G_E_B.
	
	pose proof (lemma_sameside_onray_EFAC_BFG_EGAC _ _ _ _ _ _ SameSide_A_D_B_C Col_B_C_C OnRay_C_D_F) as SameSide_A_F_B_C.
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_K_F_C_G Col_C_G_B neq_C_B) as SameSide_K_F_C_B.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_K_F_C_B) as SameSide_K_F_B_C.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_K_F_B_C) as (SameSide_F_K_B_C & _ & _).
	pose proof (lemma_samesidetransitive _ _ _ _ _ SameSide_A_F_B_C SameSide_F_K_B_C) as SameSide_A_K_B_C.
	pose proof (by_prop_SameSide_symmetric _ _ _ _ SameSide_A_K_B_C) as (SameSide_K_A_B_C & _ & _).
	pose proof (lemma_samesidecollinear _ _ _ _ _ SameSide_K_A_B_C Col_B_C_G neq_B_G) as SameSide_K_A_B_G.
	pose proof (by_prop_SameSide_flip _ _ _ _ SameSide_K_A_B_G) as SameSide_K_A_G_B.
	
	pose proof (lemma_extension B A B A neq_B_A neq_B_A) as (e & BetS_B_A_e & Cong_A_e_B_A).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_A_e) as BetS_e_A_B.
	pose proof (lemma_orderofpoints_ABC_ACD_BCD _ _ _ _ BetS_B_E_A BetS_B_A_e) as BetS_E_A_e.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_E_A_e) as BetS_e_A_E.

	pose proof (proposition_29C _ _ _ _ _ Par_A_D_B_C SameSide_D_C_A_B BetS_e_A_B) as (_ & SumTwoRT_D_A_B_A_B_C).
	pose proof (proposition_29C _ _ _ _ _ Par_A_H_E_K SameSide_H_K_A_E BetS_e_A_E) as (_ & SumTwoRT_H_A_E_A_E_K).
	
	epose proof (
		lemma_supplements_SumTwoRT
		H A E A B C D A B A E K
		SumTwoRT_H_A_E_A_E_K
		CongA_H_A_E_D_A_B
		SumTwoRT_D_A_B_A_B_C
	) as (CongA_A_E_K_A_B_C & CongA_A_B_C_A_E_K).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_A_E_K_A_B_C OnRay_B_A_E OnRay_B_C_G) as CongA_A_E_K_E_B_G.

	pose proof (proposition_28D _ _ _ _ _ BetS_A_E_B CongA_A_E_K_E_B_G SameSide_K_G_E_B) as Par_E_K_B_G.
	pose proof (by_prop_Par_flip _ _ _ _ Par_E_K_B_G) as (_ & Par_E_K_G_B & _).

	pose proof (lemma_extension B C B C neq_B_C neq_B_C) as (c & BetS_B_C_c & Cong_C_c_B_C).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_C_c) as BetS_c_C_B.
	pose proof (axiom_orderofpoints_ABD_BCD_ABC _ _ _ _ BetS_c_C_B BetS_C_G_B) as BetS_c_C_G.

	pose proof (by_def_OnRay_from_BetS_A_B_E C G B BetS_C_G_B neq_C_G) as OnRay_C_G_B.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_C_G_B) as OnRay_C_B_G.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_D_C_B_D_C_B OnRay_C_D_F OnRay_C_B_G) as CongA_D_C_B_F_C_G.

	pose proof (proposition_29C _ _ _ _ _ Par_C_D_B_A SameSide_D_A_C_B BetS_c_C_B) as (_ & SumTwoRT_D_C_B_C_B_A).
	pose proof (proposition_29C _ _ _ _ _ Par_C_F_G_K SameSide_F_K_C_G BetS_c_C_G) as (_ & SumTwoRT_F_C_G_C_G_K).

	epose proof (
		lemma_supplements_SumTwoRT
		D C B C G K F C G C B A
		SumTwoRT_D_C_B_C_B_A
		CongA_D_C_B_F_C_G
		SumTwoRT_F_C_G_C_G_K
	) as (CongA_C_B_A_C_G_K & CongA_C_G_K_C_B_A).

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_C_G_K_C_B_A OnRay_B_C_G OnRay_B_A_A) as CongA_C_G_K_G_B_A.

	pose proof (proposition_28D _ _ _ _ _ BetS_C_G_B CongA_C_G_K_G_B_A SameSide_K_A_G_B) as Par_G_K_B_A.
	pose proof (by_prop_Par_flip _ _ _ _ Par_G_K_B_A) as (_ & Par_G_K_A_B & _).
	pose proof (by_prop_Par_collinear _ _ _ _ _ Par_G_K_A_B Col_A_B_E neq_E_B) as Par_G_K_E_B.
	pose proof (by_prop_Par_symmetric _ _ _ _ Par_G_K_E_B) as Par_E_B_G_K.
	pose proof (by_prop_Par_flip _ _ _ _ Par_E_B_G_K) as (_ & Par_E_B_K_G & _).

	pose proof (by_def_Parallelogram _ _ _ _ Par_E_K_G_B Par_E_B_K_G) as Parallelogram_E_K_G_B.

	exact Parallelogram_E_K_G_B.
Qed.

End Euclid.
