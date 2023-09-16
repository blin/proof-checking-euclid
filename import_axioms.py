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
    "by_def_OnCirc": Lemma(
        name="by_def_OnCirc",
        points=["B", "J", "U", "X", "Y"],
        given=[
            PropSimple(head="CI", points=["J", "U", "X", "Y"]),
            PropSimple(head="Cong", points=["U", "B", "X", "Y"]),
        ],
        conclusion=PropSimple(head="OnCirc", points=["B", "J"]),
        asserts=[],
    ),
    "by_def_OutCirc": Lemma(
        name="by_def_OutCirc",
        points=["P", "J", "U", "V", "W", "X"],
        given=[
            PropSimple(head="CI", points=["J", "U", "V", "W"]),
            PropSimple(head="BetS", points=["U", "X", "P"]),
            PropSimple(head="Cong", points=["U", "X", "V", "W"]),
        ],
        conclusion=PropSimple(head="OutCirc", points=["P", "J"]),
        asserts=[],
    ),
    "by_def_OnRay": Lemma(
        name="by_def_OnRay",
        points=["A", "B", "C", "X"],
        given=[
            PropSimple(head="BetS", points=["X", "A", "B"]),
            PropSimple(head="BetS", points=["X", "A", "C"]),
        ],
        conclusion=PropSimple(head="OnRay", points=["A", "B", "C"]),
        asserts=[],
    ),
    "by_def_OppositeSide": Lemma(
        name="by_def_OppositeSide",
        points=["P", "A", "B", "Q", "X"],
        given=[
            PropSimple(head="BetS", points=["P", "X", "Q"]),
            PropSimple(head="Col", points=["A", "B", "X"]),
            PropInversion(p=PropSimple(head="Col", points=["A", "B", "P"])),
        ],
        conclusion=PropSimple(head="OppositeSide", points=["P", "A", "B", "Q"]),
        asserts=[],
    ),
    "by_def_SameSide": Lemma(
        name="by_def_SameSide",
        points=["P", "Q", "A", "B", "X", "U", "V"],
        given=[
            PropSimple(head="Col", points=["A", "B", "U"]),
            PropSimple(head="Col", points=["A", "B", "V"]),
            PropSimple(head="BetS", points=["P", "U", "X"]),
            PropSimple(head="BetS", points=["Q", "V", "X"]),
            PropInversion(p=PropSimple(head="Col", points=["A", "B", "P"])),
            PropInversion(p=PropSimple(head="Col", points=["A", "B", "Q"])),
        ],
        conclusion=PropSimple(head="SameSide", points=["P", "Q", "A", "B"]),
        asserts=[],
    ),
    "by_def_Lt": Lemma(
        name="by_def_Lt",
        points=["A", "B", "C", "D", "X"],
        given=[
            PropSimple(head="BetS", points=["C", "X", "D"]),
            PropSimple(head="Cong", points=["C", "X", "A", "B"]),
        ],
        conclusion=PropSimple(head="Lt", points=["A", "B", "C", "D"]),
        asserts=[],
    ),
    "by_def_Midpoint": Lemma(
        name="by_def_Midpoint",
        points=["A", "B", "C"],
        given=[
            PropSimple(head="BetS", points=["A", "B", "C"]),
            PropSimple(head="Cong", points=["A", "B", "B", "C"]),
        ],
        conclusion=PropSimple(head="Midpoint", points=["A", "B", "C"]),
        asserts=[],
    ),
    "by_def_RightTriangle": Lemma(
        name="by_def_RightTriangle",
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
    "by_def_LtA": Lemma(
        name="by_def_LtA",
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
    "by_def_Supp": Lemma(
        name="by_def_Supp",
        points=["A", "B", "C", "D", "F"],
        given=[
            PropSimple(head="OnRay", points=["B", "C", "D"]),
            PropSimple(head="BetS", points=["A", "B", "F"]),
        ],
        conclusion=PropSimple(head="Supp", points=["A", "B", "C", "D", "F"]),
        asserts=[],
    ),
    "by_def_CongA": Lemma(
        name="by_def_CongA",
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
    "by_def_Meet": Lemma(
        name="by_def_Meet",
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
    "by_def_Par": Lemma(
        name="by_def_Par",
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
    "by_def_SumTwoRT": Lemma(
        name="by_def_SumTwoRT",
        points=["A", "B", "C", "D", "E", "F", "X", "Y", "Z", "U", "V"],
        given=[
            PropSimple(head="Supp", points=["X", "Y", "U", "V", "Z"]),
            PropSimple(head="CongA", points=["A", "B", "C", "X", "Y", "U"]),
            PropSimple(head="CongA", points=["D", "E", "F", "V", "Y", "Z"]),
        ],
        conclusion=PropSimple(head="SumTwoRT", points=["A", "B", "C", "D", "E", "F"]),
        asserts=[],
    ),
    "by_def_TarskiPar": Lemma(
        name="by_def_TarskiPar",
        points=["A", "B", "C", "D"],
        given=[
            PropSimple(head="neq", points=["A", "B"]),
            PropSimple(head="neq", points=["C", "D"]),
            PropInversion(p=PropSimple(head="Meet", points=["A", "B", "C", "D"])),
            PropSimple(head="SameSide", points=["C", "D", "A", "B"]),
        ],
        conclusion=PropSimple(head="TarskiPar", points=["A", "B", "C", "D"]),
        asserts=[],
    ),
    "by_def_Cross": Lemma(
        name="by_def_Cross",
        points=["A", "B", "C", "D", "X"],
        given=[
            PropSimple(head="BetS", points=["A", "X", "B"]),
            PropSimple(head="BetS", points=["C", "X", "D"]),
        ],
        conclusion=PropSimple(head="Cross", points=["A", "B", "C", "D"]),
        asserts=[],
    ),
    "by_def_AngleSum": Lemma(
        name="by_def_AngleSum",
        points=['A', 'B', 'C', 'D', 'E', 'F', 'P', 'Q', 'R', 'X'],
        given=[
            PropSimple(head="CongA", points=["A", "B", "C", "P", "Q", "X"]),
            PropSimple(head="CongA", points=["D", "E", "F", "X", "Q", "R"]),
            PropSimple(head="BetS", points=["P", "X", "R"]),
        ],
        conclusion=PropSimple(head="AngleSum", points=["A", "B", "C", "D", "E", "F", "P", "Q", "R"]),
        asserts=[],
    ),
    "by_def_CongTriangles": Lemma(
        name="by_def_CongTriangles",
        points=['A', 'B', 'C', 'a', 'b', 'c'],
        given=[
            PropSimple(head="Cong", points=["A", "B", "a", "b"]),
            PropSimple(head="Cong", points=["B", "C", "b", "c"]),
            PropSimple(head="Cong", points=["A", "C", "a", "c"]),
        ],
        conclusion=PropSimple(head="CongTriangles", points=["A", "B", "C", "a", "b", "c"]),
        asserts=[],
    ),
    "by_def_Parallelogram": Lemma(
        name="by_def_Parallelogram",
        points=['A', 'B', 'C', 'D'],
        given=[
            PropSimple(head="Par", points=["A", "B", "C", "D"]),
            PropSimple(head="Par", points=["A", "D", "B", "C"]),
        ],
        conclusion=PropSimple(head="Parallelogram", points=["A", "B", "C", "D"]),
        asserts=[],
    ),
}

defs_to_supporting_lemmas_for_defs = {
    "AngleSum": "by_def_AngleSum",
    "CongA": "by_def_CongA",
    "CongTriangles": "by_def_CongTriangles",
    "Cross": "by_def_Cross",
    "Lt": "by_def_Lt",
    "LtA": "by_def_LtA",
    "Meet": "by_def_Meet",
    "Midpoint": "by_def_Midpoint",
    "OnCirc": "by_def_OnCirc",
    "OnRay": "by_def_OnRay",
    "OppositeSide": "by_def_OppositeSide",
    "OutCirc": "by_def_OutCirc",
    "Parallelogram": "by_def_Parallelogram",
    "Par": "by_def_Par",
    "RightTriangle": "by_def_RightTriangle",
    "SameSide": "by_def_SameSide",
    "SumTwoRT": "by_def_SumTwoRT",
    "Supp": "by_def_Supp",
    "TarskiPar": "by_def_TarskiPar",
}

assert {l.name for l in supporting_lemmas_for_defs.values()} <= set(
    defs_to_supporting_lemmas_for_defs.values()
)
