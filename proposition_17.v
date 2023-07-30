Require Import ProofCheckingEuclid.by_def_AngleSum.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_A_C.
Require Import ProofCheckingEuclid.by_def_Col_from_eq_B_C.
Require Import ProofCheckingEuclid.by_def_OnRay_from_BetS_A_B_E.
Require Import ProofCheckingEuclid.by_def_OnRay_from_neq_A_B.
Require Import ProofCheckingEuclid.by_def_Triangle.
Require Import ProofCheckingEuclid.by_def_nCol_from_Triangle.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_CongA_ABCequalsCBA.
Require Import ProofCheckingEuclid.by_prop_CongA_helper.
Require Import ProofCheckingEuclid.by_prop_CongA_reflexive.
Require Import ProofCheckingEuclid.by_prop_CongA_transitive.
Require Import ProofCheckingEuclid.by_prop_LtA_respects_congruence_smaller.
Require Import ProofCheckingEuclid.by_prop_OnRay_ABC_ACB.
Require Import ProofCheckingEuclid.by_prop_OnRay_impliescollinear.
Require Import ProofCheckingEuclid.by_prop_OnRay_neq_A_B.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.by_prop_nCol_helper.
Require Import ProofCheckingEuclid.by_prop_nCol_order.
Require Import ProofCheckingEuclid.by_prop_neq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_crossbar.
Require Import ProofCheckingEuclid.lemma_extension.
Require Import ProofCheckingEuclid.lemma_s_ncol_n_col.
Require Import ProofCheckingEuclid.proposition_16.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_17 :
	forall A B C,
	Triangle A B C ->
	exists X Y Z, AngleSum A B C B C A X Y Z.
Proof.
	intros A B C.
	intros Triangle_ABC.

	assert (eq A A) as eq_A_A by (reflexivity).
	assert (eq C C) as eq_C_C by (reflexivity).
	assert (eq B B) as eq_B_B by (reflexivity).

	pose proof (by_def_Col_from_eq_A_C B C B eq_B_B) as Col_B_C_B.
	pose proof (by_def_Col_from_eq_A_C C A C eq_C_C) as Col_C_A_C.
	pose proof (by_def_Col_from_eq_B_C A C C eq_C_C) as Col_A_C_C.
	pose proof (by_def_Col_from_eq_B_C B C C eq_C_C) as Col_B_C_C.

	pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_ABC) as nCol_A_B_C.
	pose proof (lemma_s_ncol_n_col _ _ _ nCol_A_B_C) as n_Col_A_B_C.
	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_C) as (_ & neq_B_C & _ & _ & neq_C_B & _).
	pose proof (by_prop_nCol_order _ _ _ nCol_A_B_C) as (_ & nCol_B_C_A & _ & nCol_A_C_B & _).
	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_B_C) as CongA_ABC_CBA.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_B) as OnRay_CB_B.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_B_C_A) as CongA_BCA_BCA.

	pose proof (postulate_Euclid2 _ _ neq_B_C) as (D & BetS_B_C_D).

	pose proof (by_def_Col_from_eq_A_C C D C eq_C_C) as Col_C_D_C.
	pose proof (by_def_Col_from_eq_B_C D A A eq_A_A) as Col_D_A_A.

	pose proof (by_prop_BetS_notequal _ _ _ BetS_B_C_D) as (neq_C_D & _ & neq_B_D).
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_B_C_D) as Col_B_C_D.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_C_A Col_B_C_B Col_B_C_D neq_B_D) as nCol_B_D_A.
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_B_C_A Col_B_C_C Col_B_C_D neq_C_D) as nCol_C_D_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_B_D_A) as (_ & _ & _ & _ & nCol_A_D_B).
	pose proof (by_prop_nCol_order _ _ _ nCol_C_D_A) as (_ & nCol_D_A_C & _ & _ & _).

	pose proof (proposition_16 _ _ _ _ Triangle_ABC BetS_B_C_D) as (_ & LtA_CBA_ACD).

	pose proof (by_prop_LtA_respects_congruence_smaller _ _ _ _ _ _ _ _ _ LtA_CBA_ACD CongA_ABC_CBA) as LtA_ABC_ACD.
	destruct LtA_ABC_ACD as (a & e & d & BetS_a_e_d & OnRay_CA_a & OnRay_CD_d & CongA_ABC_ACe).

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_CA_a) as OnRay_Ca_A.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_CD_d) as OnRay_Cd_D.
	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_CA_a) as Col_C_A_a.
	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_CD_d) as Col_C_D_d.

	pose proof (by_prop_OnRay_neq_A_B _ _ _ OnRay_Ca_A) as neq_C_a.
	pose proof (by_prop_OnRay_neq_A_B _ _ _ OnRay_Cd_D) as neq_C_d.
	pose proof (by_prop_neq_symmetric _ _ neq_C_a) as neq_a_C.

	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_D_A Col_C_D_C Col_C_D_d neq_C_d) as nCol_C_d_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_d_A) as (_ & _ & _ & nCol_C_A_d & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_A_d Col_C_A_C Col_C_A_a neq_C_a) as nCol_C_a_d.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_a_d) as (nCol_a_C_d & _ & _ & _ & _).
	pose proof (by_prop_Col_order _ _ _ Col_C_A_a) as (Col_A_C_a & _ & _ & _ & _).
	pose proof (by_def_Triangle _ _ _ nCol_a_C_d) as Triangle_aCd.

	pose proof (lemma_crossbar _ _ _ _ _ _ Triangle_aCd BetS_a_e_d OnRay_Ca_A OnRay_Cd_D) as (E & OnRay_Ce_E & BetS_A_E_D).

	pose proof (by_def_Col_from_eq_A_C C E C eq_C_C) as Col_C_E_C.

	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_Ce_E) as OnRay_CE_e.
	pose proof (by_prop_OnRay_neq_A_B _ _ _ OnRay_Ce_E) as neq_C_e.
	pose proof (by_prop_OnRay_neq_A_B _ _ _ OnRay_CE_e) as neq_C_E.

	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_e) as OnRay_Ce_e.
	pose proof (by_def_OnRay_from_neq_A_B _ _ neq_C_E) as OnRay_CE_E.
	pose proof (by_prop_OnRay_impliescollinear _ _ _ OnRay_CE_e) as Col_C_E_e.

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_E_D) as Col_A_E_D.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_E_D) as (_ & neq_A_E & _).
	pose proof (by_prop_neq_symmetric _ _ neq_A_E) as neq_E_A.

	pose proof (by_prop_Col_order _ _ _ Col_A_E_D) as (_ & _ & Col_D_A_E & _ & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_D_A_C Col_D_A_E Col_D_A_A neq_E_A) as nCol_E_A_C.
	pose proof (by_prop_nCol_order _ _ _ nCol_E_A_C) as (_ & nCol_A_C_E & nCol_C_E_A & nCol_E_C_A & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_C_E_A Col_C_E_C Col_C_E_e neq_C_e) as nCol_C_e_A.
	pose proof (by_prop_nCol_order _ _ _ nCol_C_e_A) as (_ & _ & nCol_A_C_e & _ & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_C_e Col_A_C_a Col_A_C_C neq_a_C) as nCol_a_C_e.

	pose proof (by_prop_CongA_reflexive _ _ _ nCol_a_C_e) as CongA_aCe_aCe.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_A_C_e) as CongA_ACe_ACe.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_aCe_aCe OnRay_Ca_A OnRay_Ce_E) as CongA_aCe_ACE.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ACe_ACe OnRay_CA_a OnRay_Ce_e) as CongA_ACe_aCe.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_ACe CongA_ACe_aCe) as CongA_ABC_aCe.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_aCe CongA_aCe_ACE) as CongA_ABC_ACE.

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_A_C_E) as CongA_ACE_ECA.
	pose proof (by_prop_CongA_reflexive _ _ _ nCol_E_C_A) as CongA_ECA_ECA.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_ACE CongA_ACE_ECA) as CongA_ABC_ECA.

	pose proof (postulate_Pasch_inner _ _ _ _ _ BetS_A_E_D BetS_B_C_D nCol_A_D_B) as (F & BetS_A_F_C & BetS_B_F_E).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_A_F_C) as BetS_C_F_A.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_A_F_C) as (neq_F_C & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_C_F_A) as (_ & neq_C_F & _).
	pose proof (by_def_OnRay_from_BetS_A_B_E _ _ _ BetS_C_F_A neq_C_F) as OnRay_CF_A.
	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_A_F_C) as Col_A_F_C.
	pose proof (by_prop_OnRay_ABC_ACB _ _ _ OnRay_CF_A) as OnRay_CA_F.

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_B_F_E) as BetS_E_F_B.

	pose proof (by_prop_Col_order _ _ _ Col_A_F_C) as (_ & _ & _ & Col_A_C_F & _).
	pose proof (by_prop_nCol_helper _ _ _ _ _ nCol_A_C_B Col_A_C_F Col_A_C_C neq_F_C) as nCol_F_C_B.
	pose proof (by_prop_nCol_order _ _ _ nCol_F_C_B) as (_ & _ & _ & _ & nCol_B_C_F).

	pose proof (by_prop_CongA_ABCequalsCBA _ _ _ nCol_B_C_F) as CongA_BCF_FCB.

	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_ECA_ECA OnRay_CE_E OnRay_CA_F) as CongA_ECA_ECF.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_ABC_ECA CongA_ECA_ECF) as CongA_ABC_ECF.
	pose proof (by_prop_CongA_helper _ _ _ _ _ _ _ _ CongA_BCA_BCA OnRay_CB_B OnRay_CA_F) as CongA_BCA_BCF.
	pose proof (by_prop_CongA_transitive _ _ _ _ _ _ _ _ _ CongA_BCA_BCF CongA_BCF_FCB) as CongA_BCA_FCB.

	pose proof (by_def_AngleSum _ _ _ _ _ _ _ _ _ _ CongA_ABC_ECF CongA_BCA_FCB BetS_E_F_B) as AngleSum_ABC_BCA_ECB.

	exists E, C, B.
	exact AngleSum_ABC_BCA_ECB.
Qed.

End Euclid.
