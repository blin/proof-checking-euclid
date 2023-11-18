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
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_ABC_CDA) as EqAreaTri_ABC_CDA.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_ABC_CDA) as (_ & _ & _ & _ & EqAreaTri_ABC_ACD).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_ABC_ACD) as EqAreaTri_ACD_ABC.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_ACD_ABC) as (_ & EqAreaTri_ACD_ACB & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_ACD_ACB) as EqAreaTri_ACB_ACD.

	pose proof (proposition_34 _ _ _ _ Parallelogram_E_A_H_K) as (_ & _ & _ & _ & CongTriangles_AEK_KHA).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_AEK_KHA) as EqAreaTri_AEK_KHA.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_AEK_KHA) as (EqAreaTri_AEK_HAK & _ & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_AEK_HAK) as EqAreaTri_HAK_AEK.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_HAK_AEK) as (_ & _ & EqAreaTri_HAK_EAK & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_HAK_EAK) as EqAreaTri_EAK_HAK.

	pose proof (proposition_34 _ _ _ _ Parallelogram_G_K_F_C) as (_ & _ & _ & _ & CongTriangles_KGC_CFK).
	pose proof (axiom_congruentequal _ _ _ _ _ _ CongTriangles_KGC_CFK) as EqAreaTri_KGC_CFK.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_KGC_CFK) as (_ & _ & _ & _ & EqAreaTri_KGC_KCF).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_KGC_KCF) as EqAreaTri_KCF_KGC.
	pose proof (axiom_EqAreaTri_permutation _ _ _ _ _ _ EqAreaTri_KCF_KGC) as (_ & EqAreaTri_KCF_KCG & _ & _ & _).
	pose proof (axiom_EqAreaTri_symmetric _ _ _ _ _ _ EqAreaTri_KCF_KCG) as EqAreaTri_KCG_KCF.

	pose proof (axiom_cutoff1 _ _ _ _ _ _ _ _ _ _ BetS_A_K_C BetS_A_K_C BetS_B_G_C BetS_D_F_C EqAreaTri_KCG_KCF EqAreaTri_ACB_ACD) as EqAreaQuad_AKGB_AKFD.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_AKGB_AKFD) as (_ & _ & EqAreaQuad_AKGB_FDAK & _ & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_AKGB_FDAK) as EqAreaQuad_FDAK_AKGB.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_FDAK_AKGB) as (_ & _ & EqAreaQuad_FDAK_GBAK & _ & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_FDAK_GBAK) as EqAreaQuad_GBAK_FDAK.

	pose proof (axiom_cutoff2 _ _ _ _ _ _ _ _ _ _ BetS_B_E_A BetS_D_H_A EqAreaTri_EAK_HAK EqAreaQuad_GBAK_FDAK) as EqAreaQuad_GBEK_FDHK.

	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_GBEK_FDHK) as (_ & _ & _ & EqAreaQuad_GBEK_DFKH & _ & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_GBEK_DFKH) as EqAreaQuad_DFKH_GBEK.
	pose proof (axiom_EqAreaQuad_permutation _ _ _ _ _ _ _ _ EqAreaQuad_DFKH_GBEK) as (_ & _ & _ & _ & EqAreaQuad_DFKH_KGBE & _ & _).
	pose proof (axiom_EqAreaQuad_symmetric _ _ _ _ _ _ _ _ EqAreaQuad_DFKH_KGBE) as EqAreaQuad_KGBE_DFKH.

	exact EqAreaQuad_KGBE_DFKH.
Qed.

End Euclid.
