Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_5_line :
	forall A B C D a b c d,
	Cong A B a b ->
	Cong B C b c ->
	Cong C A c a ->
	BetS A B D ->
	BetS a b d ->
	Cong B D b d ->
	Cong D C d c.
Proof.
	intros A B C D a b c d.
	intros Cong_AB_ab.
	intros Cong_BC_bc.
	intros Cong_CA_ca.
	intros BetS_A_B_D.
	intros BetS_a_b_d.
	intros Cong_BD_bd.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_CA_ca) as (Cong_AC_ac & _).

	pose proof (axiom_5_line _ _ _ _ _ _ _ _ Cong_BD_bd Cong_AC_ac Cong_BC_bc BetS_A_B_D BetS_a_b_d Cong_AB_ab) as Cong_CD_cd.

	pose proof (by_prop_Cong_flip _ _ _ _ Cong_CD_cd) as (Cong_DC_dc & _).

	exact Cong_DC_dc.
Qed.

End Euclid.
