Require Import ProofCheckingEuclid.by_def_nCol_from_n_Col.
Require Import ProofCheckingEuclid.by_def_n_Col_from_nCol.
Require Import ProofCheckingEuclid.by_prop_Col_order.
Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma by_prop_nCol_order :
	forall A B C,
	nCol A B C ->
	nCol B A C /\ nCol B C A /\ nCol C A B /\ nCol A C B /\ nCol C B A.
Proof.
	intros A B C.
	intros nCol_A_B_C.

	pose proof (by_def_n_Col_from_nCol _ _ _ nCol_A_B_C) as n_Col_A_B_C.

	assert (~ Col B A C) as n_Col_B_A_C.
	{
		intros Col_B_A_C.
		pose proof (by_prop_Col_order _ _ _ Col_B_A_C) as (Col_A_B_C & _).
		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_A_C) as nCol_B_A_C.

	assert (~ Col B C A) as n_Col_B_C_A.
	{
		intros Col_B_C_A.
		pose proof (by_prop_Col_order _ _ _ Col_B_C_A) as (_ & _ & Col_A_B_C & _).
		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_B_C_A) as nCol_B_C_A.

	assert (~ Col C A B) as n_Col_C_A_B.
	{
		intros Col_C_A_B.
		pose proof (by_prop_Col_order _ _ _ Col_C_A_B) as (_ & Col_A_B_C & _ ).
		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_C_A_B) as nCol_C_A_B.

	assert (~ Col A C B) as n_Col_A_C_B.
	{
		intros Col_A_C_B.
		pose proof (by_prop_Col_order _ _ _ Col_A_C_B) as (_ & _ & _ & Col_A_B_C & _).
		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_A_C_B) as nCol_A_C_B.

	assert (~ Col C B A) as n_Col_C_B_A.
	{
		intros Col_C_B_A.
		pose proof (by_prop_Col_order _ _ _ Col_C_B_A) as (_ & _ & _ & _ & Col_A_B_C).
		contradict Col_A_B_C.
		exact n_Col_A_B_C.
	}
	pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_C_B_A) as nCol_C_B_A.

	split.
	exact nCol_B_A_C.
	split.
	exact nCol_B_C_A.
	split.
	exact nCol_C_A_B.
	split.
	exact nCol_A_C_B.
	exact nCol_C_B_A.
Qed.

End Euclid.
