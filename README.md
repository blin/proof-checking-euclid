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
001. [lemma_incirc_centre](./lemma_incirc_centre.v)
001. [lemma_localextension](./lemma_localextension.v)
     ([img](./lemma_localextension.svg))
001. [lemma_equalitysymmetric](./lemma_equalitysymmetric.v)
001. [lemma_inequalitysymmetric](./lemma_inequalitysymmetric.v)
001. [lemma_congruencesymmetric](./lemma_congruencesymmetric.v)
001. [lemma_congruencetransitive](./lemma_congruencetransitive.v)
001. [lemma_congruenceflip](./lemma_congruenceflip.v)
001. [lemma_orderofpoints_ABC_ACD_BCD](./lemma_orderofpoints_ABC_ACD_BCD.v)
001. [lemma_betweennotequal](./lemma_betweennotequal.v)
001. [lemma_extensionunique](./lemma_extensionunique.v)
001. [lemma_orderofpoints_ABC_BCD_ACD](./lemma_orderofpoints_ABC_BCD_ACD.v)
001. [lemma_orderofpoints_ABC_BCD_ABD](./lemma_orderofpoints_ABC_BCD_ABD.v)
001. [lemma_partnotequalwhole](./lemma_partnotequalwhole.v)
001. [lemma_oncirc_radius](./lemma_oncirc_radius.v)
001. [lemma_outcirc_beyond_perimeter](./lemma_outcirc_beyond_perimeter.v)
001. [proposition_01](./proposition_01.v)
     ([img](./proposition_01.svg))
     * Dependency tree up to this point has
       * 14 definitions
       * 3 common notions
       * 6 axioms
       * 4 postulates
       * 15 lemmas
001. [lemma_NCdistinct](./lemma_NCdistinct.v)
001. [lemma_doublereverse](./lemma_doublereverse.v)
001. [lemma_differenceofparts](./lemma_differenceofparts.v)
001. [lemma_incirc_within_radius](./lemma_incirc_within_radius.v)
001. [proposition_02](./proposition_02.v)
     ([img](./proposition_02.svg))
     * Dependency tree up to this point has
       * 14 definitions
       * 4 common notions
       * 6 axioms
       * 4 postulates
       * 19 lemmas
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
     * Dependency tree up to this point has
       * 15 definitions
       * 4 common notions
       * 6 axioms
       * 4 postulates
       * 22 lemmas
001. [lemma_orderofpoints_ABD_BCD_ACD](./lemma_orderofpoints_ABD_BCD_ACD.v)
001. [lemma_orderofpoints_ABC_ACD_ABD](./lemma_orderofpoints_ABC_ACD_ABD.v)
001. [lemma_outerconnectivity](./lemma_outerconnectivity.v)
001. [euclidean_tactics](./euclidean_tactics.v)
001. [lemma_collinear_ABC_ABD_BCD](./lemma_collinear_ABC_ABD_BCD.v)
001. [lemma_collinear_ABC_BCA](./lemma_collinear_ABC_BCA.v)
001. [lemma_collinear_ABC_BAC](./lemma_collinear_ABC_BAC.v)
001. [lemma_collinearorder](./lemma_collinearorder.v)
001. [lemma_collinearitypreserved](./lemma_collinearitypreserved.v)
001. [lemma_onray_impliescollinear](./lemma_onray_impliescollinear.v)
001. [lemma_onray_neq_A_B](./lemma_onray_neq_A_B.v)
001. [lemma_onray_strict](./lemma_onray_strict.v)
001. [lemma_supporting_n_ncol_col](./lemma_supporting_n_ncol_col.v)
001. [lemma_supporting_n_col_ncol](./lemma_supporting_n_col_ncol.v)
001. [lemma_supporting_ncol_n_col](./lemma_supporting_ncol_n_col.v)
001. [lemma_equalanglesNC](./lemma_equalanglesNC.v)

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
* Following lemmas are introduced
  to make it easier to use some of the definitions:
  * lemma_incirc_centre
  * lemma_incirc_within_radius
  * lemma_oncirc_radius
  * lemma_outcirc_beyond_perimeter


## How images were generated

1. Diagrams were built by hand in
   [GeoGebra](https://en.wikipedia.org/wiki/GeoGebra) .
1. Downloaded as SVG.
1. Clipped with
   [Inkscape](https://en.wikipedia.org/wiki/Inkscape) .
1. Cleaned up with [format_geogebra_svg.sh](./format_geogebra_svg.sh) .

GeoGebra is used as a way of enforcing straightedge-and-compass construction.
