Require Import ProofCheckingEuclid.by_prop_Parallelogram_flip.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.proposition_34.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_43 :
	forall A B C D E F G H K,
	Parallelogram A B C D ->
	BetS A H D ->
	BetS A E B ->
	BetS D F C ->
	BetS B G C ->
	BetS A K C ->
	Parallelogram E A H K ->
	Parallelogram G K F C ->
	EqAreaQuad K G B E D F K H.
Proof.
	intros A B C D E F G H K.
	intros Parallelogram_A_B_C_D.
	intros BetS_A_H_D.
	intros BetS_A_E_B.
	intros BetS_D_F_C.
	intros BetS_B_G_C.
	intros BetS_A_K_C.
	intros Parallelogram_E_A_H_K.
	intros Parallelogram_G_K_F_C.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_E_B) as BetS_B_E_A.
	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_H_D) as BetS_D_H_A.

	pose proof (by_prop_Parallelogram_flip _ _ _ _ Parallelogram_A_B_C_D) as Parallelogram_B_A_D_C.
	pose proof (proposition_34 _ _ _ _ Parallelogram_B_A_D_C) as (_ & _ & _ & _ & CongTriangles_ABC_CDA).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_ABC_CDA) as EqAreaTri_A_B_C_C_D_A.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_B_C_C_D_A) as (_ & _ & _ & _ & EqAreaTri_A_B_C_A_C_D).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_B_C_A_C_D) as EqAreaTri_A_C_D_A_B_C.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_C_D_A_B_C) as (_ & EqAreaTri_A_C_D_A_C_B & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_C_D_A_C_B) as EqAreaTri_A_C_B_A_C_D.

	pose proof (proposition_34 _ _ _ _ Parallelogram_E_A_H_K) as (_ & _ & _ & _ & CongTriangles_AEK_KHA).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_AEK_KHA) as EqAreaTri_A_E_K_K_H_A.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_A_E_K_K_H_A) as (EqAreaTri_A_E_K_H_A_K & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_A_E_K_H_A_K) as EqAreaTri_H_A_K_A_E_K.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_H_A_K_A_E_K) as (_ & _ & EqAreaTri_H_A_K_E_A_K & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_H_A_K_E_A_K) as EqAreaTri_E_A_K_H_A_K.

	pose proof (proposition_34 _ _ _ _ Parallelogram_G_K_F_C) as (_ & _ & _ & _ & CongTriangles_KGC_CFK).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_KGC_CFK) as EqAreaTri_K_G_C_C_F_K.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_K_G_C_C_F_K) as (_ & _ & _ & _ & EqAreaTri_K_G_C_K_C_F).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_K_G_C_K_C_F) as EqAreaTri_K_C_F_K_G_C.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_K_C_F_K_G_C) as (_ & EqAreaTri_K_C_F_K_C_G & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_K_C_F_K_C_G) as EqAreaTri_K_C_G_K_C_F.

	pose proof (axiom_cutoff1 _ _ _ _ _ _ _ _ _ _ BetS_A_K_C BetS_A_K_C BetS_B_G_C BetS_D_F_C EqAreaTri_K_C_G_K_C_F EqAreaTri_A_C_B_A_C_D) as EqAreaQuad_A_K_G_B_A_K_F_D.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_A_K_G_B_A_K_F_D) as (_ & _ & EqAreaQuad_A_K_G_B_F_D_A_K & _ & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_A_K_G_B_F_D_A_K) as EqAreaQuad_F_D_A_K_A_K_G_B.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_F_D_A_K_A_K_G_B) as (_ & _ & EqAreaQuad_F_D_A_K_G_B_A_K & _ & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_F_D_A_K_G_B_A_K) as EqAreaQuad_G_B_A_K_F_D_A_K.

	pose proof (axiom_cutoff2 _ _ _ _ _ _ _ _ _ _ BetS_B_E_A BetS_D_H_A EqAreaTri_E_A_K_H_A_K EqAreaQuad_G_B_A_K_F_D_A_K) as EqAreaQuad_G_B_E_K_F_D_H_K.

	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_G_B_E_K_F_D_H_K) as (_ & _ & _ & EqAreaQuad_G_B_E_K_D_F_K_H & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_G_B_E_K_D_F_K_H) as EqAreaQuad_D_F_K_H_G_B_E_K.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_D_F_K_H_G_B_E_K) as (_ & _ & _ & _ & EqAreaQuad_D_F_K_H_K_G_B_E & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_D_F_K_H_K_G_B_E) as EqAreaQuad_K_G_B_E_D_F_K_H.

	exact EqAreaQuad_K_G_B_E_D_F_K_H.
Qed.

End Euclid.
