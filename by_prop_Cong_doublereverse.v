Require Import ProofCheckingEuclid.by_prop_Cong_flip.
Require Import ProofCheckingEuclid.by_prop_Cong_symmetric.
Require Import ProofCheckingEuclid.euclidean_axioms.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma by_prop_Cong_doublereverse :
	forall A B C D,
	Cong A B C D ->
	Cong D C B A /\ Cong B A D C.
Proof.
	intros A B C D.
	intros Cong_AB_CD.
	apply by_prop_Cong_flip in Cong_AB_CD as (Cong_BA_DC & Cong_BA_CD & Cong_AB_DC).
	apply by_prop_Cong_symmetric in Cong_BA_DC as Cong_DC_BA.
	split.
	exact Cong_DC_BA.
	exact Cong_BA_DC.
Qed.

End Euclid.
