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
001. [lemma_congruencesymmetric](./lemma_congruencesymmetric.v)
001. [lemma_congruencetransitive](./lemma_congruencetransitive.v)
001. [lemma_congruenceflip](./lemma_congruenceflip.v)
001. [lemma_s_incirc_centre](./lemma_s_incirc_centre.v)
001. [lemma_equalitysymmetric](./lemma_equalitysymmetric.v)
001. [lemma_inequalitysymmetric](./lemma_inequalitysymmetric.v)
001. [lemma_localextension](./lemma_localextension.v)
     ([img](./lemma_localextension.svg))
001. [lemma_s_oncirc_radius](./lemma_s_oncirc_radius.v)
001. [lemma_s_outcirc_beyond_perimeter](./lemma_s_outcirc_beyond_perimeter.v)
001. [lemma_orderofpoints_ABC_ACD_BCD](./lemma_orderofpoints_ABC_ACD_BCD.v)
001. [lemma_betweennotequal](./lemma_betweennotequal.v)
001. [lemma_extensionunique](./lemma_extensionunique.v)
001. [lemma_orderofpoints_ABC_BCD_ACD](./lemma_orderofpoints_ABC_BCD_ACD.v)
001. [lemma_orderofpoints_ABC_BCD_ABD](./lemma_orderofpoints_ABC_BCD_ABD.v)
001. [lemma_partnotequalwhole](./lemma_partnotequalwhole.v)
001. [proposition_01](./proposition_01.v)
     ([img](./proposition_01.svg))
001. [lemma_NCdistinct](./lemma_NCdistinct.v)
001. [lemma_doublereverse](./lemma_doublereverse.v)
001. [lemma_differenceofparts](./lemma_differenceofparts.v)
001. [lemma_s_incirc_within_radius](./lemma_s_incirc_within_radius.v)
001. [proposition_02](./proposition_02.v)
     ([img](./proposition_02.svg))
001. [lemma_betweennesspreserved](./lemma_betweennesspreserved.v)
001. [lemma_extension](./lemma_extension.v)
001. [lemma_lessthancongruence](./lemma_lessthancongruence.v)
     ([img](./lemma_lessthancongruence.svg))
     * The illustration includes triangles implied by `axiom_5_line`, where
       point D is "moving onto the line". See section "6.6 Degenerate cases".
001. [proposition_03](./proposition_03.v)
     * For illsutration see `lemma_lessthancongruence`.
      `proposition_03` is
       a direct application of that lemma and so their illustrations are
       equivalent.
001. [euclidean_tactics](./euclidean_tactics.v)
001. [lemma_orderofpoints_ABD_BCD_ACD](./lemma_orderofpoints_ABD_BCD_ACD.v)
001. [lemma_orderofpoints_ABC_ACD_ABD](./lemma_orderofpoints_ABC_ACD_ABD.v)
001. [lemma_outerconnectivity](./lemma_outerconnectivity.v)
001. [lemma_s_n_ncol_col](./lemma_s_n_ncol_col.v)
001. [lemma_collinear_ABC_ABD_BCD](./lemma_collinear_ABC_ABD_BCD.v)
001. [lemma_collinearitypreserved](./lemma_collinearitypreserved.v)
001. [lemma_collinear_ABC_BCA](./lemma_collinear_ABC_BCA.v)
001. [lemma_collinear_ABC_BAC](./lemma_collinear_ABC_BAC.v)
001. [lemma_collinearorder](./lemma_collinearorder.v)
001. [lemma_onray_impliescollinear](./lemma_onray_impliescollinear.v)
001. [lemma_onray_neq_A_B](./lemma_onray_neq_A_B.v)
001. [lemma_onray_strict](./lemma_onray_strict.v)
001. [lemma_s_n_col_ncol](./lemma_s_n_col_ncol.v)
001. [lemma_s_ncol_n_col](./lemma_s_ncol_n_col.v)
001. [lemma_equalanglesNC](./lemma_equalanglesNC.v)
001. [lemma_interior5](./lemma_interior5.v)
001. [lemma_s_lt](./lemma_s_lt.v)
001. [lemma_onray_betweenness](./lemma_onray_betweenness.v)
001. [lemma_onray_orderofpoints_any](./lemma_onray_orderofpoints_any.v)
001. [lemma_layoffunique](./lemma_layoffunique.v)
001. [lemma_s_onray](./lemma_s_onray.v)
001. [lemma_onray_assert](./lemma_onray_assert.v)
001. [lemma_s_onray_assert_ABB](./lemma_s_onray_assert_ABB.v)
001. [lemma_s_onray_assert_bets_ABE](./lemma_s_onray_assert_bets_ABE.v)
001. [lemma_s_onray_assert_bets_AEB](./lemma_s_onray_assert_bets_AEB.v)
001. [lemma_s_conga_sss](./lemma_s_conga_sss.v)
001. [lemma_NCorder](./lemma_NCorder.v)
001. [lemma_onray_ABC_ACB](./lemma_onray_ABC_ACB.v)
001. [lemma_s_onray_congruence_betweenness](./lemma_s_onray_congruence_betweenness.v)
001. [lemma_s_triangle_vertex_to_ray_congruent](./lemma_s_triangle_vertex_to_ray_congruent.v)
001. [proposition_04](./proposition_04.v)
001. [lemma_s_conga](./lemma_s_conga.v)
001. [lemma_ABCequalsCBA](./lemma_ABCequalsCBA.v)
001. [proposition_05](./proposition_05.v)
001. [lemma_s_cut](./lemma_s_cut.v)
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
001. [lemma_s_right_triangle](./lemma_s_right_triangle.v)
001. [lemma_s_perp_at](./lemma_s_perp_at.v)
001. [proposition_12](./proposition_12.v)
     ([img](./proposition_12.svg))
001. [lemma_collinear_ABC_ABD_ABE_CDE](./lemma_collinear_ABC_ABD_ABE_CDE.v)
001. [lemma_otherside_betweenness_PABC_RPQ_QABC](./lemma_otherside_betweenness_PABC_RPQ_QABC.v)
001. [lemma_otherside_betweenness_PABC_RQP_QABC](./lemma_otherside_betweenness_PABC_RQP_QABC.v)
001. [lemma_s_os](./lemma_s_os.v)
001. [lemma_twolines2](./lemma_twolines2.v)
001. [lemma_planeseparation](./lemma_planeseparation.v)
001. [lemma_equalanglessymmetric](./lemma_equalanglessymmetric.v)
001. [lemma_angledistinct](./lemma_angledistinct.v)
001. [lemma_onray_shared_initial_point](./lemma_onray_shared_initial_point.v)
001. [lemma_equalangleshelper](./lemma_equalangleshelper.v)
001. [lemma_layoff](./lemma_layoff.v)
001. [lemma_equalanglestransitive](./lemma_equalanglestransitive.v)
001. [lemma_lessthantransitive](./lemma_lessthantransitive.v)
001. [lemma_midpointunique](./lemma_midpointunique.v)
001. [lemma_s_congruence_null_segment](./lemma_s_congruence_null_segment.v)
001. [lemma_right_triangle_NC](./lemma_right_triangle_NC.v)
001. [lemma_supplements_conga](./lemma_supplements_conga.v)
001. [lemma_right_triangle_symmetric](./lemma_right_triangle_symmetric.v)
001. [lemma_right_triangle_leg_change](./lemma_right_triangle_leg_change.v)
001. [lemma_collinearright](./lemma_collinearright.v)
001. [lemma_altitudebisectsbase](./lemma_altitudebisectsbase.v)
001. [lemma_rightreverse](./lemma_rightreverse.v)
001. [lemma_droppedperpendicularunique](./lemma_droppedperpendicularunique.v)
001. [lemma_fiveline](./lemma_fiveline.v)
001. [lemma_s_ss](./lemma_s_ss.v)
001. [lemma_samesidesymmetric](./lemma_samesidesymmetric.v)
001. [proposition_07](./proposition_07.v)
001. [lemma_trichotomy_equal](./lemma_trichotomy_equal.v)
001. [lemma_s_lta](./lemma_s_lta.v)
001. [lemma_angleorderrespectscongruence_smaller](./lemma_angleorderrespectscongruence_smaller.v)
001. [lemma_angleorderrespectscongruence](./lemma_angleorderrespectscongruence.v)
001. [lemma_crossbar](./lemma_crossbar.v)
001. [lemma_equalanglesreflexive](./lemma_equalanglesreflexive.v)
001. [lemma_angleordertransitive](./lemma_angleordertransitive.v)
001. [lemma_sameside_onray](./lemma_sameside_onray.v)
001. [lemma_angletrichotomy](./lemma_angletrichotomy.v)
001. [proposition_06a](./proposition_06a.v)
001. [proposition_06](./proposition_06.v)
001. [proposition_08](./proposition_08.v)
001. [lemma_s_inangle](./lemma_s_inangle.v)
001. [proposition_09](./proposition_09.v)
     ([img](./proposition_09.svg))
001. [proposition_11](./proposition_11.v)
001. [lemma_NChelper](./lemma_NChelper.v)
001. [lemma_s_sumsupp](./lemma_s_sumsupp.v)
001. [proposition_13](./proposition_13.v)
001. [lemma_oppositesidesymmetric](./lemma_oppositesidesymmetric.v)
001. [proposition_14](./proposition_14.v)
001. [proposition_15](./proposition_15.v)
001. [lemma_s_col_BetS_A_B_C](./lemma_s_col_BetS_A_B_C.v)
001. [lemma_s_ncol_triangle](./lemma_s_ncol_triangle.v)
001. [proposition_16](./proposition_16.v)
     * Fig 1: proving ∠BAC < ∠ACD
       ([img](./proposition_16_LtA_BAC_ACD.svg))
     * Fig 1: proving ∠CBA < ∠ACD
       ([img](./proposition_16_LtA_CBA_ACD.svg))
001. [lemma_s_AngleSum](./lemma_s_AngleSum.v)
001. [lemma_s_col_eq_A_C](./lemma_s_col_eq_A_C.v)
001. [lemma_s_col_eq_B_C](./lemma_s_col_eq_B_C.v)
001. [lemma_s_triangle](./lemma_s_triangle.v)
001. [proposition_17](./proposition_17.v)

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
  `lemma_onray_orderofpoints_any` instead of `lemma_ray1`.
* `lemma_collinear[124]` instead of having a numeric suffixes have evocative
  if not descriptive suffixes,
  `lemma_collinear_ABC_BAC` instead of `lemma_collinear1`.
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
