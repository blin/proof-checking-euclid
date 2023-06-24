Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_s_par :
	forall A B C D U V u v X,
	neq A B ->
	neq C D ->
	Col A B U ->
	Col A B V ->
	neq U V ->
	Col C D u ->
	Col C D v ->
	neq u v ->
	~ Meet A B C D ->
	BetS U X v ->
	BetS u X V ->
	Par A B C D.
Proof.
	intros A B C D U V u v X.
	intros neq_A_B.
	intros neq_C_D.
	intros Col_A_B_U.
	intros Col_A_B_V.
	intros neq_U_V.
	intros Col_C_D_u.
	intros Col_C_D_v.
	intros neq_u_v.
	intros n_Meet_A_B_C_D.
	intros BetS_U_X_v.
	intros BetS_u_X_V.


	unfold Par.
	exists U,V,u,v,X.
	split.
	exact neq_A_B.
	split.
	exact neq_C_D.
	split.
	exact Col_A_B_U.
	split.
	exact Col_A_B_V.
	split.
	exact neq_U_V.
	split.
	exact Col_C_D_u.
	split.
	exact Col_C_D_v.
	split.
	exact neq_u_v.
	split.
	exact n_Meet_A_B_C_D.
	split.
	exact BetS_U_X_v.
	exact BetS_u_X_V.
Qed.

End Euclid.

