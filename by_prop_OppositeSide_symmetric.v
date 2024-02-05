Require Coq.Logic.Classical_Prop.
Require Import ProofCheckingEuclid.by_def_Col_from_BetS_A_B_C.
Require Import ProofCheckingEuclid.by_def_OppositeSide.
Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_BetS_notequal.
Require Import ProofCheckingEuclid.by_prop_Col_ABC_ABD_BCD.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.by_prop_nCol_distinct.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma by_prop_OppositeSide_symmetric :
	forall A B P Q,
	OppositeSide P A B Q ->
	OppositeSide Q A B P.
Proof.
	intros A B P Q.
	intros OppositeSide_P_AB_Q.

	destruct OppositeSide_P_AB_Q as (R & BetS_P_R_Q & Col_A_B_R & nCol_A_B_P).

	pose proof (axiom_betweennesssymmetry _ _ _ BetS_P_R_Q) as BetS_Q_R_P.
	pose proof (by_prop_BetS_notequal _ _ _ BetS_P_R_Q) as (neq_R_Q & _ & _).
	pose proof (by_prop_BetS_notequal _ _ _ BetS_Q_R_P) as (_ & neq_Q_R & neq_Q_P).

	pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_P_R_Q) as Col_P_R_Q.

	pose proof (by_prop_Col_order _ _ _ Col_P_R_Q) as (_ & _ & _ & _ & Col_Q_R_P).
	pose proof (by_prop_Col_order _ _ _ Col_A_B_R) as (_ & _ & _ & _ & Col_R_B_A).

	pose proof (by_prop_nCol_distinct _ _ _ nCol_A_B_P) as (neq_A_B & _ & _ & _ & _ & _).
	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_P) as n_Col_A_B_P.

	assert (~ Col A B Q) as n_Col_A_B_Q.
	{
		intros Col_A_B_Q.

		pose proof (by_prop_Col_order _ _ _ Col_A_B_Q) as (_ & Col_B_Q_A & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_A_B_Q Col_A_B_R neq_A_B) as Col_B_Q_R.
		pose proof (by_prop_Col_order _ _ _ Col_B_Q_R) as (_ & Col_Q_R_B & _ & _ & _).
		pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_Q_R_B Col_Q_R_P neq_Q_R) as Col_R_B_P.

		assert (Col A P B) as Col_A_P_B.
		assert (eq R B \/ neq R B) as [eq_R_B|neq_R_B] by (apply Classical_Prop.classic).
		{
			(* case eq_R_B *)
			assert (Col P B Q) as Col_P_B_Q by (rewrite <- eq_R_B; exact Col_P_R_Q).
			pose proof (by_prop_Col_order _ _ _ Col_P_B_Q) as (_ & Col_B_Q_P & Col_Q_P_B  & _ & _).

			assert (neq B Q) as neq_B_Q by (rewrite <- eq_R_B; exact neq_R_Q).
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_B_Q_P Col_B_Q_A neq_B_Q) as Col_Q_P_A.

			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_Q_P_A Col_Q_P_B neq_Q_P) as Col_P_A_B.
			pose proof (by_prop_Col_order _ _ _ Col_P_A_B) as (Col_A_P_B & _ & _ & _ & _).

			exact Col_A_P_B.
		}
		{
			(* case neq_R_B *)
			pose proof (by_prop_Col_ABC_ABD_BCD _ _ _ _ Col_R_B_P Col_R_B_A neq_R_B) as Col_B_P_A.
			pose proof (by_prop_Col_order _ _ _ Col_B_P_A) as (_ & _ & _ & _ & Col_A_P_B).
			exact Col_A_P_B.
		}
		pose proof (by_prop_Col_order _ _ _ Col_A_P_B) as (_ & _ & _ & Col_A_B_P & _).

		contradict Col_A_B_P.
		exact n_Col_A_B_P.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_A_B_Q) as nCol_A_B_Q.

	pose proof (by_def_OppositeSide _ _ _ _ _ BetS_Q_R_P Col_A_B_R nCol_A_B_Q) as OppositeSide_Q_AB_P.

	exact OppositeSide_Q_AB_P.
Qed.

End Euclid.
