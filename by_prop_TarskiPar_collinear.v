Require Import ProofCheckingEuclid.by_prop_TarskiPar_collinear_ABcd_Ccd_ABCd.
Require Import ProofCheckingEuclid.by_prop_TarskiPar_collinear_ABcd_cCd_ABCd.
Require Import ProofCheckingEuclid.by_prop_TarskiPar_flip.
Require Import ProofCheckingEuclid.by_prop_eq_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_TarskiPar_collinear :
	forall A B C c d,
	TarskiPar A B c d ->
	Col c d C ->
	neq C d ->
	TarskiPar A B C d.
Proof.
	intros A B C c d.
	intros TarskiPar_AB_cd.
	intros Col_c_d_C.
	intros neq_C_d.


	assert (TarskiPar_AB_cd_2 := TarskiPar_AB_cd).
	destruct TarskiPar_AB_cd_2 as (neq_A_B & neq_c_d & n_Meet_A_B_c_d & SameSide_c_d_AB).

	pose proof (by_prop_TarskiPar_flip _ _ _ _ TarskiPar_AB_cd) as (_ & TarskiPar_AB_dc & _).

	(* assert by cases *)
	assert (TarskiPar A B C d) as TarskiPar_AB_Cd.
	destruct Col_c_d_C as [eq_c_d | [eq_c_C | [eq_d_C | [BetS_d_c_C | [BetS_c_d_C | BetS_c_C_d]]]]].
	{
		(* case eq_c_d *)

		contradict eq_c_d.
		exact neq_c_d.
	}
	{
		(* case eq_c_C *)
		assert (TarskiPar A B C d) as TarskiPar_AB_Cd by (rewrite <- eq_c_C; exact TarskiPar_AB_cd).

		exact TarskiPar_AB_Cd.
	}
	{
		(* case eq_d_C *)
		pose proof (by_prop_eq_symmetric _ _ eq_d_C) as eq_C_d.
		contradict eq_C_d.
		exact neq_C_d.
	}
	{
		(* case BetS_d_c_C *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_d_c_C) as BetS_C_c_d.
		pose proof (by_prop_TarskiPar_collinear_ABcd_Ccd_ABCd _ _ _ _ _ TarskiPar_AB_cd BetS_C_c_d) as TarskiPar_AB_Cd.

		exact TarskiPar_AB_Cd.
	}
	{
		(* case BetS_c_d_C *)
		pose proof (axiom_betweennesssymmetry _ _ _ BetS_c_d_C) as BetS_C_d_c.

		pose proof (by_prop_TarskiPar_collinear_ABcd_Ccd_ABCd _ _ _ _ _ TarskiPar_AB_dc BetS_C_d_c) as TarskiPar_AB_Cc.
		pose proof (by_prop_TarskiPar_flip _ _ _ _ TarskiPar_AB_Cc) as (_ & TarskiPar_AB_cC & _).
		pose proof (by_prop_TarskiPar_collinear_ABcd_cCd_ABCd _ _ _ _ _ TarskiPar_AB_cC BetS_c_d_C) as TarskiPar_AB_dC.
		pose proof (by_prop_TarskiPar_flip _ _ _ _ TarskiPar_AB_dC) as (_ & TarskiPar_AB_Cd & _).

		exact TarskiPar_AB_Cd.
	}
	{
		(* case BetS_c_C_d *)
		pose proof (by_prop_TarskiPar_collinear_ABcd_cCd_ABCd _ _ _ _ _ TarskiPar_AB_cd BetS_c_C_d) as TarskiPar_AB_Cd.

		exact TarskiPar_AB_Cd.
	}

	exact TarskiPar_AB_Cd.
Qed.

End Euclid.
