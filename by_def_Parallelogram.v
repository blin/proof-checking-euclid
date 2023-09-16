Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

(* Definition Parallelogram A B C D := Par A B C D /\ Par A D B C. *)
Lemma by_def_Parallelogram :
	forall A B C D,
	Par A B C D ->
	Par A D B C ->
	Parallelogram A B C D.
Proof.
	intros A B C D.
	intros Par_AB_CD.
	intros Par_AD_BC.

	unfold Parallelogram.
	split.
	exact Par_AB_CD.
	exact Par_AD_BC.
Qed.

End Euclid.
