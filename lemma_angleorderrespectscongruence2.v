Require Import ProofCheckingEuclid.euclidean_axioms.
Require Import ProofCheckingEuclid.euclidean_defs.
Require Import ProofCheckingEuclid.lemma_equalanglestransitive.
Require Import ProofCheckingEuclid.lemma_s_lta.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleorderrespectscongruence2 : 
   forall A B C D E F a b c,
   LtA A B C D E F ->
   CongA a b c A B C ->
   LtA a b c D E F.
Proof.
   intros A B C D E F a b c.
   intros LtA_ABC_DEF.
   intros CongA_abc_ABC.

   destruct LtA_ABC_DEF as (P & Q & R & BetS_P_Q_R & OnRay_ED_P & OnRay_EF_R & CongA_ABC_DEQ).
   pose proof (lemma_equalanglestransitive a b c _ _ _ D E Q CongA_abc_ABC CongA_ABC_DEQ) as CongA_abc_DEQ.

   pose proof (lemma_s_lta a b c D E F P Q R BetS_P_Q_R OnRay_ED_P OnRay_EF_R CongA_abc_DEQ) as LtA_abc_DEF.

   exact LtA_abc_DEF.
Qed.

End Euclid.
