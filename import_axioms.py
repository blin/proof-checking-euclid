from import_rpl import (
    Lemma,
    PropSimple,
    PropExists,
    PropInversion,
    PropConjunction,
)

# TODO: extract from euclidean_axioms.v
axioms = {
    "axiom_nocollapse": Lemma(
        name="axiom_nocollapse",
        points=["A", "B", "C", "D"],
        given=[
            PropSimple(head="neq", points=["A", "B"]),
            PropSimple(head="Cong", points=["A", "B", "C", "D"]),
        ],
        conclusion=PropSimple(head="neq", points=["C", "D"]),
        asserts=[],
    ),
    "axiom_5_line": Lemma(
        name="axiom_5_line",
        points=["A", "B", "C", "D", "a", "b", "c", "d"],
        given=[
            PropSimple(head="Cong", points=["B", "C", "b", "c"]),
            PropSimple(head="Cong", points=["A", "D", "a", "d"]),
            PropSimple(head="Cong", points=["B", "D", "b", "d"]),
            PropSimple(head="BetS", points=["A", "B", "C"]),
            PropSimple(head="BetS", points=["a", "b", "c"]),
            PropSimple(head="Cong", points=["A", "B", "a", "b"]),
        ],
        conclusion=PropSimple(head="Cong", points=["D", "C", "d", "c"]),
        asserts=[],
    ),
    "axiom_connectivity": Lemma(
        name="axiom_connectivity",
        points=["A", "B", "C", "D"],
        given=[
            PropSimple(head="BetS", points=["A", "B", "D"]),
            PropSimple(head="BetS", points=["A", "C", "D"]),
            PropInversion(p=PropSimple(head="BetS", points=["A", "B", "C"])),
            PropInversion(p=PropSimple(head="BetS", points=["A", "C", "B"])),
        ],
        conclusion=PropSimple(head="eq", points=["B", "C"]),
        asserts=[],
    ),
    "axiom_orderofpoints_ABD_BCD_ABC": Lemma(
        name="axiom_orderofpoints_ABD_BCD_ABC",
        points=["A", "B", "C", "D"],
        given=[
            PropSimple(head="BetS", points=["A", "B", "D"]),
            PropSimple(head="BetS", points=["B", "C", "D"]),
        ],
        conclusion=PropSimple(head="BetS", points=["A", "B", "C"]),
        asserts=[],
    ),
    "axiom_circle_center_radius": Lemma(
        name="axiom_circle_center_radius",
        points=["A", "B", "C", "J", "P"],
        given=[
            PropSimple(head="CI", points=["J", "A", "B", "C"]),
            PropSimple(head="OnCirc", points=["P", "J"]),
        ],
        conclusion=PropSimple(head="Cong", points=["A", "P", "B", "C"]),
        asserts=[],
    ),
    "cn_sumofparts": Lemma(
        name="cn_sumofparts",
        points=["A", "B", "C", "a", "b", "c"],
        given=[
            PropSimple(head="Cong", points=["A", "B", "a", "b"]),
            PropSimple(head="Cong", points=["B", "C", "b", "c"]),
            PropSimple(head="BetS", points=["A", "B", "C"]),
            PropSimple(head="BetS", points=["a", "b", "c"]),
        ],
        conclusion=PropSimple(head="Cong", points=["A", "C", "a", "c"]),
        asserts=[],
    ),
    "cn_congruencetransitive": Lemma(
        name="cn_congruencetransitive",
        points=["A", "B", "C", "D", "E", "F"],
        given=[
            PropSimple(head="Cong", points=["A", "B", "C", "D"]),
            PropSimple(head="Cong", points=["A", "B", "E", "F"]),
        ],
        conclusion=PropSimple(head="Cong", points=["C", "D", "E", "F"]),
        asserts=[],
    ),
    "postulate_Euclid3": Lemma(
        name="postulate_Euclid3",
        points=["A", "B"],
        given=[
            PropSimple(head="neq", points=["A", "B"]),
        ],
        conclusion=PropExists(points=["X"], p=PropSimple(head="CI", points=["X", "A", "A", "B"])),
        asserts=[],
    ),
    "postulate_Pasch_inner": Lemma(
        name="postulate_Pasch_inner",
        points=["A", "B", "C", "P", "Q"],
        given=[
            PropSimple(head="BetS", points=["A", "P", "C"]),
            PropSimple(head="BetS", points=["B", "Q", "C"]),
            PropInversion(p=PropSimple(head="Col", points=["A", "C", "B"])),
        ],
        conclusion=PropExists(
            points=["X"],
            p=PropConjunction(
                left=PropSimple(head="BetS", points=["A", "X", "Q"]),
                right=PropSimple(head="BetS", points=["B", "X", "P"]),
            ),
        ),
        asserts=[],
    ),
    "postulate_Pasch_outer": Lemma(
        name="postulate_Pasch_outer",
        points=["A", "B", "C", "P", "Q"],
        given=[
            PropSimple(head="BetS", points=["A", "P", "C"]),
            PropSimple(head="BetS", points=["B", "C", "Q"]),
            PropInversion(p=PropSimple(head="Col", points=["B", "Q", "A"])),
        ],
        conclusion=PropExists(
            points=["X"],
            p=PropConjunction(
                left=PropSimple(head="BetS", points=["A", "X", "Q"]),
                right=PropSimple(head="BetS", points=["B", "P", "X"]),
            ),
        ),
        asserts=[],
    ),
    "postulate_Euclid5": Lemma(
        name="postulate_Euclid5",
        points=["a", "p", "q", "r", "s", "t"],
        given=[
            PropSimple(head="BetS", points=["r", "t", "s"]),
            PropSimple(head="BetS", points=["p", "t", "q"]),
            PropSimple(head="BetS", points=["r", "a", "q"]),
            PropSimple(head="Cong", points=["p", "t", "q", "t"]),
            PropSimple(head="Cong", points=["t", "r", "t", "s"]),
            PropInversion(p=PropSimple(head="Col", points=["p", "q", "s"])),
        ],
        conclusion=PropExists(
            points=["X"],
            p=PropConjunction(
                left=PropSimple(head="BetS", points=["p", "a", "X"]),
                right=PropSimple(head="BetS", points=["s", "q", "X"]),
            ),
        ),
        asserts=[],
    ),
}

# TODO: extract from euclidean_defs.v
supporting_lemmas_for_defs: dict[str, Lemma] = {
    "lemma_s_oncirc_radius": Lemma(
        name="lemma_s_oncirc_radius",
        points=["B", "J", "U", "X", "Y"],
        given=[
            PropSimple(head="CI", points=["J", "U", "X", "Y"]),
            PropSimple(head="Cong", points=["U", "B", "X", "Y"]),
        ],
        conclusion=PropSimple(head="OnCirc", points=["B", "J"]),
        asserts=[],
    ),
    "lemma_s_outcirc_beyond_perimeter": Lemma(
        name="lemma_s_outcirc_beyond_perimeter",
        points=["P", "J", "U", "V", "W", "X"],
        given=[
            PropSimple(head="CI", points=["J", "U", "V", "W"]),
            PropSimple(head="BetS", points=["U", "X", "P"]),
            PropSimple(head="Cong", points=["U", "X", "V", "W"]),
        ],
        conclusion=PropSimple(head="OutCirc", points=["P", "J"]),
        asserts=[],
    ),
    "lemma_s_onray": Lemma(
        name="lemma_s_onray",
        points=["A", "B", "C", "X"],
        given=[
            PropSimple(head="BetS", points=["X", "A", "B"]),
            PropSimple(head="BetS", points=["X", "A", "C"]),
        ],
        conclusion=PropSimple(head="OnRay", points=["A", "B", "C"]),
        asserts=[],
    ),
    "lemma_s_os": Lemma(
        name="lemma_s_os",
        points=["P", "A", "B", "Q", "X"],
        given=[
            PropSimple(head="BetS", points=["P", "X", "Q"]),
            PropSimple(head="Col", points=["A", "B", "X"]),
            PropInversion(p=PropSimple(head="Col", points=["A", "B", "P"])),
        ],
        conclusion=PropSimple(head="OS", points=["P", "A", "B", "Q"]),
        asserts=[],
    ),
    "lemma_s_ss": Lemma(
        name="lemma_s_ss",
        points=["P", "Q", "A", "B", "X", "U", "V"],
        given=[
            PropSimple(head="Col", points=["A", "B", "U"]),
            PropSimple(head="Col", points=["A", "B", "V"]),
            PropSimple(head="BetS", points=["P", "U", "X"]),
            PropSimple(head="BetS", points=["Q", "V", "X"]),
            PropInversion(p=PropSimple(head="Col", points=["A", "B", "P"])),
            PropInversion(p=PropSimple(head="Col", points=["A", "B", "Q"])),
        ],
        conclusion=PropSimple(head="SS", points=["P", "Q", "A", "B"]),
        asserts=[],
    ),
    "lemma_s_lt": Lemma(
        name="lemma_s_lt",
        points=["A", "B", "C", "D", "X"],
        given=[
            PropSimple(head="BetS", points=["C", "X", "D"]),
            PropSimple(head="Cong", points=["C", "X", "A", "B"]),
        ],
        conclusion=PropSimple(head="Lt", points=["A", "B", "C", "D"]),
        asserts=[],
    ),
    "lemma_s_midpoint": Lemma(
        name="lemma_s_midpoint",
        points=["A", "B", "C"],
        given=[
            PropSimple(head="BetS", points=["A", "B", "C"]),
            PropSimple(head="Cong", points=["A", "B", "B", "C"]),
        ],
        conclusion=PropSimple(head="Midpoint", points=["A", "B", "C"]),
        asserts=[],
    ),
    "lemma_s_right_triangle": Lemma(
        name="lemma_s_right_triangle",
        points=["A", "B", "C", "X"],
        given=[
            PropSimple(head="BetS", points=["A", "B", "X"]),
            PropSimple(head="Cong", points=["A", "B", "X", "B"]),
            PropSimple(head="Cong", points=["A", "C", "X", "C"]),
            PropSimple(head="neq", points=["B", "C"]),
        ],
        conclusion=PropSimple(head="RightTriangle", points=["A", "B", "C"]),
        asserts=[],
    ),
    "lemma_s_lta": Lemma(
        name="lemma_s_lta",
        points=["A", "B", "C", "D", "E", "F", "U", "X", "V"],
        given=[
            PropSimple(head="BetS", points=["U", "X", "V"]),
            PropSimple(head="OnRay", points=["E", "D", "U"]),
            PropSimple(head="OnRay", points=["E", "F", "V"]),
            PropSimple(head="CongA", points=["A", "B", "C", "D", "E", "X"]),
        ],
        conclusion=PropSimple(head="LtA", points=["A", "B", "C", "D", "E", "F"]),
        asserts=[],
    ),
    "lemma_s_supp": Lemma(
        name="lemma_s_supp",
        points=["A", "B", "C", "D", "F"],
        given=[
            PropSimple(head="OnRay", points=["B", "C", "D"]),
            PropSimple(head="BetS", points=["A", "B", "F"]),
        ],
        conclusion=PropSimple(head="Supp", points=["A", "B", "C", "D", "F"]),
        asserts=[],
    ),
    "lemma_s_conga": Lemma(
        name="lemma_s_conga",
        points=["A", "B", "C", "a", "b", "c", "U", "V", "u", "v"],
        given=[
            PropSimple(head="OnRay", points=["B", "A", "U"]),
            PropSimple(head="OnRay", points=["B", "C", "V"]),
            PropSimple(head="OnRay", points=["b", "a", "u"]),
            PropSimple(head="OnRay", points=["b", "c", "v"]),
            PropSimple(head="Cong", points=["B", "U", "b", "u"]),
            PropSimple(head="Cong", points=["B", "V", "b", "v"]),
            PropSimple(head="Cong", points=["U", "V", "u", "v"]),
            PropInversion(p=PropSimple(head="Col", points=["A", "B", "C"])),
        ],
        conclusion=PropSimple(head="CongA", points=["A", "B", "C", "a", "b", "c"]),
        asserts=[],
    ),
    "lemma_s_meet": Lemma(
        name="lemma_s_meet",
        points=["A", "B", "C", "D", "X"],
        given=[
            PropSimple(head="neq", points=["A", "B"]),
            PropSimple(head="neq", points=["C", "D"]),
            PropSimple(head="Col", points=["A", "B", "X"]),
            PropSimple(head="Col", points=["C", "D", "X"]),
        ],
        conclusion=PropSimple(head="Meet", points=["A", "B", "C", "D"]),
        asserts=[],
    ),
    "lemma_s_par": Lemma(
        name="lemma_s_par",
        points=["A", "B", "C", "D", "U", "V", "u", "v", "X"],
        given=[
            PropSimple(head="neq", points=["A", "B"]),
            PropSimple(head="neq", points=["C", "D"]),
            PropSimple(head="Col", points=["A", "B", "U"]),
            PropSimple(head="Col", points=["A", "B", "V"]),
            PropSimple(head="neq", points=["U", "V"]),
            PropSimple(head="Col", points=["C", "D", "u"]),
            PropSimple(head="Col", points=["C", "D", "v"]),
            PropSimple(head="neq", points=["u", "v"]),
            PropInversion(p=PropSimple(head="Meet", points=["A", "B", "C", "D"])),
            PropSimple(head="BetS", points=["U", "X", "v"]),
            PropSimple(head="BetS", points=["u", "X", "V"]),
        ],
        conclusion=PropSimple(head="Par", points=["A", "B", "C", "D"]),
        asserts=[],
    ),
    "lemma_s_sumtwort": Lemma(
        name="lemma_s_sumtwort",
        points=["A", "B", "C", "D", "E", "F", "X", "Y", "Z", "U", "V"],
        given=[
            PropSimple(head="Supp", points=["X", "Y", "U", "V", "Z"]),
            PropSimple(head="CongA", points=["A", "B", "C", "X", "Y", "U"]),
            PropSimple(head="CongA", points=["D", "E", "F", "V", "Y", "Z"]),
        ],
        conclusion=PropSimple(head="SumTwoRT", points=["A", "B", "C", "D", "E", "F"]),
        asserts=[],
    ),
    "lemma_s_tarski_par": Lemma(
        name="lemma_s_tarski_par",
        points=["A", "B", "C", "D"],
        given=[
            PropSimple(head="neq", points=["A", "B"]),
            PropSimple(head="neq", points=["C", "D"]),
            PropInversion(p=PropSimple(head="Meet", points=["A", "B", "C", "D"])),
            PropSimple(head="SS", points=["C", "D", "A", "B"]),
        ],
        conclusion=PropSimple(head="TarskiPar", points=["A", "B", "C", "D"]),
        asserts=[],
    ),
    "lemma_s_cross": Lemma(
        name="lemma_s_cross",
        points=["A", "B", "C", "D", "X"],
        given=[
            PropSimple(head="BetS", points=["A", "X", "B"]),
            PropSimple(head="BetS", points=["C", "X", "D"]),
        ],
        conclusion=PropSimple(head="Cross", points=["A", "B", "C", "D"]),
        asserts=[],
    ),
}

defs_to_supporting_lemmas_for_defs = {
    "CongA": "lemma_s_conga",
    "Cross": "lemma_s_cross",
    "Lt": "lemma_s_lt",
    "LtA": "lemma_s_lta",
    "Meet": "lemma_s_meet",
    "Midpoint": "lemma_s_midpoint",
    "OS": "lemma_s_os",
    "OnCirc": "lemma_s_oncirc_radius",
    "OnRay": "lemma_s_onray",
    "OutCirc": "lemma_s_outcirc_beyond_perimeter",
    "Par": "lemma_s_par",
    "RightTriangle": "lemma_s_right_triangle",
    "SS": "lemma_s_ss",
    "SumTwoRT": "lemma_s_sumtwort",
    "Supp": "lemma_s_supp",
    "TarskiPar": "lemma_s_tarski_par",
}

assert {l.name for l in supporting_lemmas_for_defs.values()} <= set(
    defs_to_supporting_lemmas_for_defs.values()
)
