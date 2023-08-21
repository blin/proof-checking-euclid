# Proof Checking Euclid

This repository is an attempt to understand

```
Beeson, Michael, et al. ‘Proof-Checking Euclid’. Annals of Mathematics and Artificial Intelligence, vol. 85, no. 2–4, Apr. 2019, pp. 213–57. DOI.org (Crossref), https://doi.org/10.1007/s10472-018-9606-x.
```

and https://github.com/GeoCoq/GeoCoq specifically.

Most of the code here is a direct translation but
`auto` tactic and the like are not used.
The goal is to be able to follow how the proof unfolds.

## Reading order

Each lemma has a tree of dependencies,
and so the dependencies need to be introduced in a particular order.

001. [euclidean_axioms](./euclidean_axioms.v)
001. [euclidean_defs](./euclidean_defs.v)
001. [by_prop_Cong_symmetric](./by_prop_Cong_symmetric.v)
001. [by_prop_Cong_transitive](./by_prop_Cong_transitive.v)
001. [by_prop_Cong_flip](./by_prop_Cong_flip.v)
001. [by_def_InCirc_center](./by_def_InCirc_center.v)
001. [by_prop_eq_symmetric](./by_prop_eq_symmetric.v)
001. [by_prop_neq_symmetric](./by_prop_neq_symmetric.v)
001. [lemma_localextension](./lemma_localextension.v)
     ([img](./lemma_localextension.svg))
001. [by_def_OnCirc](./by_def_OnCirc.v)
001. [by_def_OutCirc](./by_def_OutCirc.v)
001. [lemma_orderofpoints_ABC_ACD_BCD](./lemma_orderofpoints_ABC_ACD_BCD.v)
001. [by_prop_BetS_notequal](./by_prop_BetS_notequal.v)
001. [lemma_extensionunique](./lemma_extensionunique.v)
001. [lemma_orderofpoints_ABC_BCD_ACD](./lemma_orderofpoints_ABC_BCD_ACD.v)
001. [lemma_orderofpoints_ABC_BCD_ABD](./lemma_orderofpoints_ABC_BCD_ABD.v)
001. [lemma_partnotequalwhole](./lemma_partnotequalwhole.v)
001. [proposition_01](./proposition_01.v)
     ([img](./proposition_01.svg))
001. [by_prop_nCol_distinct](./by_prop_nCol_distinct.v)
001. [by_prop_Cong_doublereverse](./by_prop_Cong_doublereverse.v)
001. [lemma_differenceofparts](./lemma_differenceofparts.v)
001. [by_def_InCirc_within_radius](./by_def_InCirc_within_radius.v)
001. [proposition_02](./proposition_02.v)
     ([img](./proposition_02.svg))
001. [lemma_betweennesspreserved](./lemma_betweennesspreserved.v)
001. [lemma_extension](./lemma_extension.v)
001. [by_prop_Lt_congruence](./by_prop_Lt_congruence.v)
     ([img](./by_prop_Lt_congruence.svg))
     * The illustration includes triangles implied by `axiom_5_line`, where
       point D is "moving onto the line". See section "6.6 Degenerate cases".
001. [proposition_03](./proposition_03.v)
     * For illsutration see `by_prop_Lt_congruence`.
      `proposition_03` is
       a direct application of that lemma and so their illustrations are
       equivalent.
001. [lemma_orderofpoints_ABD_BCD_ACD](./lemma_orderofpoints_ABD_BCD_ACD.v)
001. [lemma_orderofpoints_ABC_ACD_ABD](./lemma_orderofpoints_ABC_ACD_ABD.v)
001. [lemma_outerconnectivity](./lemma_outerconnectivity.v)
001. [by_def_Col_from_n_nCol](./by_def_Col_from_n_nCol.v)
001. [by_prop_Col_ABC_ABD_BCD](./by_prop_Col_ABC_ABD_BCD.v)
001. [lemma_collinearitypreserved](./lemma_collinearitypreserved.v)
001. [by_prop_Col_ABC_BCA](./by_prop_Col_ABC_BCA.v)
001. [by_prop_Col_ABC_BAC](./by_prop_Col_ABC_BAC.v)
001. [by_prop_Col_order](./by_prop_Col_order.v)
001. [by_prop_OnRay_impliescollinear](./by_prop_OnRay_impliescollinear.v)
001. [by_prop_OnRay_neq_A_B](./by_prop_OnRay_neq_A_B.v)
001. [by_prop_OnRay_neq_A_C](./by_prop_OnRay_neq_A_C.v)
001. [by_def_nCol_from_n_Col](./by_def_nCol_from_n_Col.v)
001. [by_def_n_Col_from_nCol](./by_def_n_Col_from_nCol.v)
001. [by_prop_CongA_NC](./by_prop_CongA_NC.v)
001. [lemma_interior5](./lemma_interior5.v)
001. [by_def_Lt](./by_def_Lt.v)
001. [by_prop_OnRay_betweenness](./by_prop_OnRay_betweenness.v)
001. [by_prop_OnRay_orderofpoints_any](./by_prop_OnRay_orderofpoints_any.v)
001. [lemma_layoffunique](./lemma_layoffunique.v)
001. [by_def_OnRay](./by_def_OnRay.v)
001. [by_prop_OnRay_assert](./by_prop_OnRay_assert.v)
001. [by_def_OnRay_from_neq_A_B](./by_def_OnRay_from_neq_A_B.v)
001. [by_def_OnRay_from_BetS_A_B_E](./by_def_OnRay_from_BetS_A_B_E.v)
001. [by_def_OnRay_from_BetS_A_E_B](./by_def_OnRay_from_BetS_A_E_B.v)
001. [lemma_s_conga_sss](./lemma_s_conga_sss.v)
001. [by_prop_nCol_order](./by_prop_nCol_order.v)
001. [by_prop_OnRay_ABC_ACB](./by_prop_OnRay_ABC_ACB.v)
001. [lemma_s_onray_congruence_betweenness](./lemma_s_onray_congruence_betweenness.v)
001. [lemma_s_triangle_vertex_to_ray_congruent](./lemma_s_triangle_vertex_to_ray_congruent.v)
001. [proposition_04](./proposition_04.v)
001. [by_def_CongA](./by_def_CongA.v)
001. [by_prop_CongA_ABCequalsCBA](./by_prop_CongA_ABCequalsCBA.v)
001. [proposition_05](./proposition_05.v)
001. [by_def_Cut](./by_def_Cut.v)
001. [lemma_s_intersecting_triangles_ncol_ADE](./lemma_s_intersecting_triangles_ncol_ADE.v)
001. [lemma_s_intersecting_triangles_ncol_BDE](./lemma_s_intersecting_triangles_ncol_BDE.v)
001. [lemma_twolines](./lemma_twolines.v)
001. [lemma_s_intersecting_triangles_cong_AF_BF](./lemma_s_intersecting_triangles_cong_AF_BF.v)
001. [lemma_s_ncol_ABD_col_ABC_ncol_ACD](./lemma_s_ncol_ABD_col_ABC_ncol_ACD.v)
001. [proposition_10](./proposition_10.v)
     * Fig 1: constructing point F using Pasch's Inner postulate
       ([img](./proposition_10_pasch_F.svg))
     * Fig 2: constructing point M using Pasch's Inner postulate
       ([img](./proposition_10_pasch_M.svg))
001. [by_def_RightTriangle](./by_def_RightTriangle.v)
001. [by_def_Perp_at](./by_def_Perp_at.v)
001. [proposition_12](./proposition_12.v)
     ([img](./proposition_12.svg))
001. [by_prop_Col_ABC_ABD_ABE_CDE](./by_prop_Col_ABC_ABD_ABE_CDE.v)
001. [lemma_oppositeside_betweenness_PABC_RPQ_QABC](./lemma_oppositeside_betweenness_PABC_RPQ_QABC.v)
001. [lemma_oppositeside_betweenness_PABC_RQP_QABC](./lemma_oppositeside_betweenness_PABC_RQP_QABC.v)
001. [by_def_OppositeSide](./by_def_OppositeSide.v)
001. [lemma_twolines2](./lemma_twolines2.v)
001. [lemma_planeseparation](./lemma_planeseparation.v)
001. [by_prop_CongA_symmetric](./by_prop_CongA_symmetric.v)
001. [by_prop_CongA_distinct](./by_prop_CongA_distinct.v)
001. [by_prop_OnRay_shared_initial_point](./by_prop_OnRay_shared_initial_point.v)
001. [by_prop_CongA_helper](./by_prop_CongA_helper.v)
001. [lemma_layoff](./lemma_layoff.v)
001. [by_prop_CongA_transitive](./by_prop_CongA_transitive.v)
001. [by_prop_Lt_transitive](./by_prop_Lt_transitive.v)
001. [lemma_midpointunique](./lemma_midpointunique.v)
001. [lemma_s_congruence_null_segment](./lemma_s_congruence_null_segment.v)
001. [by_prop_RightTriangle_NC](./by_prop_RightTriangle_NC.v)
001. [lemma_supplements_conga](./lemma_supplements_conga.v)
001. [by_prop_RightTriangle_symmetric](./by_prop_RightTriangle_symmetric.v)
001. [by_prop_RightTriangle_leg_change](./by_prop_RightTriangle_leg_change.v)
001. [by_prop_RightTriangle_collinear](./by_prop_RightTriangle_collinear.v)
001. [lemma_altitudebisectsbase](./lemma_altitudebisectsbase.v)
001. [by_prop_RightTriangle_reverse](./by_prop_RightTriangle_reverse.v)
001. [lemma_droppedperpendicularunique](./lemma_droppedperpendicularunique.v)
001. [lemma_fiveline](./lemma_fiveline.v)
001. [by_def_SameSide](./by_def_SameSide.v)
001. [by_prop_SameSide_symmetric](./by_prop_SameSide_symmetric.v)
001. [proposition_07](./proposition_07.v)
001. [by_prop_Lt_trichotomous](./by_prop_Lt_trichotomous.v)
001. [by_def_LtA](./by_def_LtA.v)
001. [by_prop_LtA_respects_congruence_smaller](./by_prop_LtA_respects_congruence_smaller.v)
001. [by_prop_LtA_respects_congruence](./by_prop_LtA_respects_congruence.v)
001. [lemma_crossbar](./lemma_crossbar.v)
001. [by_prop_CongA_reflexive](./by_prop_CongA_reflexive.v)
001. [by_prop_LtA_transitive](./by_prop_LtA_transitive.v)
001. [lemma_sameside_onray](./lemma_sameside_onray.v)
001. [lemma_angletrichotomy](./lemma_angletrichotomy.v)
001. [proposition_06a](./proposition_06a.v)
001. [proposition_06](./proposition_06.v)
001. [proposition_08](./proposition_08.v)
001. [by_def_InAngle](./by_def_InAngle.v)
001. [proposition_09](./proposition_09.v)
     ([img](./proposition_09.svg))
001. [proposition_11](./proposition_11.v)
001. [by_prop_nCol_helper](./by_prop_nCol_helper.v)
001. [lemma_s_sumsupp](./lemma_s_sumsupp.v)
001. [proposition_13](./proposition_13.v)
001. [by_prop_OppositeSide_symmetric](./by_prop_OppositeSide_symmetric.v)
001. [proposition_14](./proposition_14.v)
001. [proposition_15](./proposition_15.v)
001. [by_def_Col_from_BetS_A_B_C](./by_def_Col_from_BetS_A_B_C.v)
001. [by_def_nCol_from_Triangle](./by_def_nCol_from_Triangle.v)
001. [proposition_16](./proposition_16.v)
     * Fig 1: proving ∠BAC < ∠ACD
       ([img](./proposition_16_LtA_BAC_ACD.svg))
     * Fig 1: proving ∠CBA < ∠ACD
       ([img](./proposition_16_LtA_CBA_ACD.svg))
001. [by_def_AngleSum](./by_def_AngleSum.v)
001. [by_def_Col_from_eq_A_C](./by_def_Col_from_eq_A_C.v)
001. [by_def_Col_from_eq_B_C](./by_def_Col_from_eq_B_C.v)
001. [by_def_Triangle](./by_def_Triangle.v)
001. [proposition_17](./proposition_17.v)
001. [by_def_isosceles](./by_def_isosceles.v)
001. [proposition_18](./proposition_18.v)
001. [proposition_19](./proposition_19.v)
001. [by_def_TogetherGreater](./by_def_TogetherGreater.v)
001. [proposition_20](./proposition_20.v)
001. [by_prop_Lt_congruence_smaller](./by_prop_Lt_congruence_smaller.v)
001. [by_def_Col_from_BetS_A_C_B](./by_def_Col_from_BetS_A_C_B.v)
001. [by_def_Col_from_BetS_B_A_C](./by_def_Col_from_BetS_B_A_C.v)
001. [by_def_Col_from_eq_A_B](./by_def_Col_from_eq_A_B.v)
001. [by_prop_Lt_asymmetric](./by_prop_Lt_asymmetric.v)
001. [by_prop_Lt_additive](./by_prop_Lt_additive.v)
001. [by_prop_Lt_between](./by_prop_Lt_between.v)
001. [by_def_TT](./by_def_TT.v)
001. [lemma_21helper](./lemma_21helper.v)
001. [by_prop_TogetherGreater_flip](./by_prop_TogetherGreater_flip.v)
001. [by_prop_TogetherGreater_symmetric](./by_prop_TogetherGreater_symmetric.v)
001. [by_prop_TT_flip](./by_prop_TT_flip.v)
001. [by_prop_TT_flip2](./by_prop_TT_flip2.v)
001. [by_prop_TT_order](./by_prop_TT_order.v)
001. [by_prop_TT_transitive](./by_prop_TT_transitive.v)
001. [proposition_21](./proposition_21.v)
001. [by_prop_Lt_notequal](./by_prop_Lt_notequal.v)
001. [lemma_ondiameter](./lemma_ondiameter.v)
001. [lemma_subtractequals](./lemma_subtractequals.v)
001. [lemma_together](./lemma_together.v)
001. [proposition_22](./proposition_22.v)
001. [proposition_23](./proposition_23.v)
001. [by_prop_CongA_flip](./by_prop_CongA_flip.v)
001. [proposition_24](./proposition_24.v)
001. [proposition_15a](./proposition_15a.v)
001. [lemma_pointreflectionisometry](./lemma_pointreflectionisometry.v)
001. [lemma_linereflectionisometry](./lemma_linereflectionisometry.v)
001. [lemma_right_triangle_same_base_cong_side_cong_hypotenuse](./lemma_right_triangle_same_base_cong_side_cong_hypotenuse.v)
001. [lemma_Euclid4](./lemma_Euclid4.v)
001. [lemma_sameside_onray_EFAC_BFG_EGAC](./lemma_sameside_onray_EFAC_BFG_EGAC.v)
001. [lemma_oppositeside_onray_PABC_RQP_QABC](./lemma_oppositeside_onray_PABC_RQP_QABC.v)
001. [by_prop_RightTriangle_CBA_n_ACB](./by_prop_RightTriangle_CBA_n_ACB.v)
001. [by_prop_SameSide_reflexive](./by_prop_SameSide_reflexive.v)
001. [lemma_notperp](./lemma_notperp.v)
001. [proposition_11B](./proposition_11B.v)
001. [proposition_23B](./proposition_23B.v)
001. [proposition_23C](./proposition_23C.v)
001. [lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF](./lemma_angletrichotomy_n_CongA_ABC_DEF_n_LtA_DEF_ABC_LtA_ABC_DEF.v)
001. [proposition_25](./proposition_25.v)
001. [proposition_26A](./proposition_26A.v)
001. [by_def_Meet](./by_def_Meet.v)
001. [lemma_collinearbetween](./lemma_collinearbetween.v)
001. [lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB](./lemma_s_col_ABC_col_ABD_ncol_ACD_eq_AB.v)
001. [by_def_Par](./by_def_Par.v)
001. [lemma_27helper_BetS_A_E_G](./lemma_27helper_BetS_A_E_G.v)
001. [lemma_27helper_OnRay_EA_G](./lemma_27helper_OnRay_EA_G.v)
001. [proposition_27](./proposition_27.v)
001. [proposition_28A](./proposition_28A.v)
001. [by_prop_Par_flip](./by_prop_Par_flip.v)
001. [proposition_31](./proposition_31.v)
001. [lemma_crossbar_LtA](./lemma_crossbar_LtA.v)
001. [by_prop_Supp_symmetric](./by_prop_Supp_symmetric.v)
001. [lemma_supplementinequality](./lemma_supplementinequality.v)
001. [proposition_29](./proposition_29.v)
001. [by_prop_Par_collinear](./by_prop_Par_collinear.v)
001. [by_prop_Par_NC](./by_prop_Par_NC.v)
001. [by_def_TarskiPar](./by_def_TarskiPar.v)
001. [by_prop_TarskiPar_collinear_ABcd_Ccd_ABCd](./by_prop_TarskiPar_collinear_ABcd_Ccd_ABCd.v)
001. [by_prop_TarskiPar_collinear_ABcd_cCd_ABCd](./by_prop_TarskiPar_collinear_ABcd_cCd_ABCd.v)
001. [by_prop_TarskiPar_flip](./by_prop_TarskiPar_flip.v)
001. [by_prop_TarskiPar_collinear](./by_prop_TarskiPar_collinear.v)
001. [by_prop_Par_to_TarskiPar](./by_prop_Par_to_TarskiPar.v)
001. [by_prop_Par_symmetric](./by_prop_Par_symmetric.v)
001. [by_def_Cross](./by_def_Cross.v)
001. [lemma_crisscross](./lemma_crisscross.v)
001. [lemma_30helper](./lemma_30helper.v)
001. [lemma_crossimpliesopposite](./lemma_crossimpliesopposite.v)
001. [proposition_30A](./proposition_30A.v)
001. [proposition_30](./proposition_30.v)
001. [by_def_AngleSum](./by_def_AngleSum.v)
001. [proposition_31short](./proposition_31short.v)
001. [proposition_32](./proposition_32.v)
001. [proposition_27B](./proposition_27B.v)
001. [proposition_29B](./proposition_29B.v)
001. [proposition_33](./proposition_33.v)

The following were done ahead of their time to prove something unrelated:

001. [by_prop_RightTriangle_equaltoright](./by_prop_RightTriangle_equaltoright.v)
001. [by_prop_OppositeSide_flip](./by_prop_OppositeSide_flip.v)
001. [by_prop_RightTriangle_supplement](./by_prop_RightTriangle_supplement.v)
001. [proposition_28B](./proposition_28B.v)
001. [proposition_28C](./proposition_28C.v)
001. [lemma_twoperpsparallel](./lemma_twoperpsparallel.v)
001. [lemma_samenotopposite](./lemma_samenotopposite.v)
001. [proposition_33B](./proposition_33B.v)
001. [by_def_Square](./by_def_Square.v)
001. [lemma_road_to_reality_2_7](./lemma_road_to_reality_2_7.v)

## Differences from GeoCoq

* `cn_equalityreverse` is renamed to `cn_congruencereverse`.
  I think the original name is due to how this common notion was applied in the
  `.prf` files: `EEABBA cn:equalityreverse` . I found this hard to follow given
  that the rest of the congruence common notions start with `congruence`.
* `lemma_3_6a` and the like are renamed to `lemma_orderofpoints_ABC_ACD_BCD`
  and the like. Section "8 Book Zero and filling in book I" mentions
  "several important and often-used lemmas \[that\] are about the
  order of four points on a line,
  when two betweenness relations are known between them", which seems to match
  `lemma_3_6a` and the like. I found `orderofpoints` to be a more appropriate
  name for those lemmas.
* `axiom_innertransitivity` is renamed to `axiom_orderofpoints_ABD_BCD_ABC`
  to match the renaming of `lemma_3_6a` into `lemma_orderofpoints_ABC_ACD_BCD`.
* `Out` is renamed to `OnRay`, which I found easier to reason about.
* `lemma_ray*` were renamed to `lemma_onray*` to match the change
  from `Out` to `OnRay`.
* `lemma_onray[12345]` instead of having numeric suffixes have evocative
  if not descriptive suffixes,
  `by_prop_OnRay_orderofpoints_any` instead of `lemma_ray1`.
* `lemma_collinear[124]` instead of having a numeric suffixes have evocative
  if not descriptive suffixes,
  `by_prop_Col_ABC_BAC` instead of `lemma_collinear1`.
* You can find the full list of renames in [sed_renames.txt](./sed_renames.txt).
* Many lemmas are introduced
  to make it easier to use some of the definitions and
  to make sense of what is going on. Newly introduced lemmas start with
  `lemma_s` , with `s` for `supporting`.


## How images were generated

1. Diagrams were built by hand in
   [GeoGebra](https://en.wikipedia.org/wiki/GeoGebra) .
1. Downloaded as SVG.
1. Clipped with
   [Inkscape](https://en.wikipedia.org/wiki/Inkscape) .
1. Cleaned up with [format_geogebra_svg.sh](./format_geogebra_svg.sh) .

GeoGebra is used as a way of enforcing straightedge-and-compass construction.
