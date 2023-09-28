#!/usr/bin/env python3

import sys


# fmt: off
axiom_betweennesssymmetry = "pose proof (axiom_betweennesssymmetry _ _ _ BetS_p01_p02_p03) as BetS_p03_p02_p01."
by_prop_BetS_notequal = "pose proof (by_prop_BetS_notequal _ _ _ BetS_p01_p02_p03) as (neq_p02_p03 & neq_p01_p02 & neq_p01_p03)."
by_def_Col_from_BetS_A_B_C = "pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_p01_p02_p03) as Col_p01_p02_p03."

by_prop_Col_order = "pose proof (by_prop_Col_order _ _ _ Col_p01_p02_p03) as (Col_p02_p01_p03 & Col_p02_p03_p01 & Col_p03_p01_p02 & Col_p01_p03_p02 & Col_p03_p02_p01)."
destruct_Col = """\
assert (Col_p01_p02_p03_2 := Col_p01_p02_p03).
destruct Col_p01_p02_p03_2 as [eq_p01_p02 | [eq_p01_p03 | [eq_p02_p03 | [BetS_p02_p01_p03 | [BetS_p01_p02_p03 | BetS_p01_p03_p02]]]]].
{
	(* case eq_p01_p02 *)
	admit.
}
{
	(* case eq_p01_p03 *)
	admit.
}
{
	(* case eq_p02_p03 *)
	admit.
}
{
	(* case BetS_p02_p01_p03 *)
	admit.
}
{
	(* case BetS_p01_p02_p03 *)
	admit.
}
{
	(* case BetS_p01_p03_p02 *)
	admit.
}
"""

by_def_nCol_from_n_Col = "pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_p01_p02_p03) as nCol_p01_p02_p03."
by_def_n_Col_from_nCol = "pose proof (by_def_n_Col_from_nCol _ _ _ nCol_p01_p02_p03) as n_Col_p01_p02_p03."
by_prop_nCol_distinct = "pose proof (by_prop_nCol_distinct _ _ _ nCol_p01_p02_p03) as (neq_p01_p02 & neq_p02_p03 & neq_p01_p03 & neq_p02_p01 & neq_p03_p02 & neq_p03_p01)."
by_prop_nCol_order = "pose proof (by_prop_nCol_order _ _ _ nCol_p01_p02_p03) as (nCol_p02_p01_p03 & nCol_p02_p03_p01 & nCol_p03_p01_p02 & nCol_p01_p03_p02 & nCol_p03_p02_p01)."

by_prop_CongA_symmetric = "pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_p01_p02_p03_p04_p05_p06) as CongA_p04_p05_p06_p01_p02_p03."
by_prop_CongA_distinct = "pose proof (by_prop_CongA_distinct _ _ _ _ _ _ CongA_p01_p02_p03_p04_p05_p06) as (neq_p01_p02 & neq_p02_p03 & neq_p01_p03 & neq_p04_p05 & neq_p05_p06 & neq_p04_p06)."
by_prop_CongA_NC = "pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_p01_p02_p03_p04_p05_p06) as nCol_p04_p05_p06."
by_prop_CongA_flip_left = "pose proof (by_prop_CongA_flip_left _ _ _ _ _ _ CongA_p01_p02_p03_p04_p05_p06) as CongA_p03_p02_p01_p04_p05_p06."
by_prop_CongA_flip_right = "pose proof (by_prop_CongA_flip_right _ _ _ _ _ _ CongA_p01_p02_p03_p04_p05_p06) as CongA_p01_p02_p03_p06_p05_p04."

destruct_OppositeSide = """\
assert (OppositeSide_p01_p02_p03_p04_2 := OppositeSide_p01_p02_p03_p04).
destruct OppositeSide_p01_p02_p03_p04_2 as (p05 & BetS_p01_p05_p04 & Col_p02_p03_p05 & nCol_p02_p03_p01).
"""

eq_reflexivity = "assert (eq p01 p01) as eq_p01_p01 by (reflexivity)."
by_def_Col_from_eq_B_C = "pose proof (by_def_Col_from_eq_B_C sp p01 p01 eq_p01_p01) as Col_sp_p01_p01."
by_prop_Col_A_B_B_order = "pose proof (by_prop_Col_order _ _ _ Col_sp_p01_p01) as (Col_p01_sp_p01 & Col_p01_p01_sp & _ & _ & _)."

eq_neq_classic = "assert (eq p01 p02 \/ neq p01 p02) as [eq_p01_p02|neq_p01_p02] by (apply Classical_Prop.classic)."

destruct_OnRay = """
pose proof (by_prop_OnRay_orderofpoints_any _ _ _ OnRay_p01_p02_p03) as [BetS_p01_p03_p02 | [eq_p02_p03 | BetS_p01_p02_p03]].
{
    (* case BetS_p01_p03_p02 *)
    admit.
}
{
    (* case eq_p02_p03 *)
    admit.
}
{
    (* case BetS_p01_p02_p03 *)
    admit.
}
"""

by_prop_Cong_flip = "pose proof (by_prop_Cong_flip _ _ _ _ Cong_p01_p02_p03_p04) as (Cong_p02_p01_p04_p03 & Cong_p02_p01_p03_p04 & Cong_p01_p02_p04_p03)."
by_prop_Cong_symmetric = "pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_p01_p02_p03_p04) as Cong_p03_p04_p01_p02." 

by_prop_Par_flip = "pose proof (by_prop_Par_flip _ _ _ _ Par_p01_p02_p03_p04) as (Par_p02_p01_p03_p04 & Par_p01_p02_p04_p03 & Par_p02_p01_p04_p03)."
by_prop_Par_symmetric = "pose proof (by_prop_Par_symmetric _ _ _ _ Par_p01_p02_p03_p04) as Par_p03_p04_p01_p02." 
by_prop_Par_NC = "pose proof (by_prop_Par_NC _ _ _ _ Par_p01_p02_p03_p04) as (nCol_p01_p02_p03 & nCol_p01_p03_p04 & nCol_p02_p03_p04 & nCol_p01_p02_p04)."

by_prop_neq_symmetric = "pose proof (by_prop_neq_symmetric _ _ neq_p01_p02) as neq_p02_p01."
by_def_OnRay_from_neq_A_B  = "pose proof (by_def_OnRay_from_neq_A_B _ _ neq_p01_p02) as OnRay_p01_p02_p02."


destruct_Par = """
assert (Par_p01_p02_p03_p04_2 := Par_p01_p02_p03_p04).
destruct Par_p01_p02_p03_p04_2 as (p05 & p06 & p07 & p08 & p09 & neq_p01_p02 & neq_p03_p04 & Col_p01_p02_p05 & Col_p01_p02_p06 & neq_p05_p06 & Col_p03_p04_p07 & Col_p03_p04_p08 & neq_p07_p08 & n_Meet_p01_p02_p03_p04 & BetS_p05_p09_p08 & BetS_p07_p09_p06).\
"""

destruct_Par_not_Meet = """
assert (Par_p01_p02_p03_p04_2 := Par_p01_p02_p03_p04).
destruct Par_p01_p02_p03_p04_2 as (_ & _ & _ & _ & _ & neq_p01_p02 & neq_p03_p04 & _ & _ & _ & _ & _ & _ & n_Meet_p01_p02_p03_p04 & _ & _).
"""

destruct_Cross = """
assert (Cross_p01_p02_p03_p04_2 := Cross_p01_p02_p03_p04).
destruct Cross_p01_p02_p03_p04_2 as (p05 & BetS_p01_p05_p02 & BetS_p03_p05_p04).
"""

destruct_SumTwoRT = """
assert (SumTwoRT_p01_p02_p03_p04_p05_p06_2 := SumTwoRT_p01_p02_p03_p04_p05_p06).
destruct SumTwoRT_p01_p02_p03_p04_p05_p06_2 as (p07 & p08 & p09 & p10 & p11 & Supp_p07_p08_p10_p11_p09 & CongA_p01_p02_p03_p07_p08_p10 & CongA_p04_p05_p06_p11_p08_p09).
"""

destruct_Midpoint = """\
assert (Midpoint_p01_p02_p03_2 := Midpoint_p01_p02_p03).
destruct Midpoint_p01_p02_p03_2 as (BetS_p01_p02_p03 & Cong_p01_p02_p02_p03).
"""

destruct_Parallelogram = """\
assert (Parallelogram_p01_p02_p03_p04_2 := Parallelogram_p01_p02_p03_p04).
destruct Parallelogram_p01_p02_p03_p04_2 as (Par_p01_p02_p03_p04 & Par_p01_p04_p02_p03).
"""

proposition_34 = "pose proof (proposition_34 _ _ _ _ Parallelogram_p01_p02_p03_p04) as (Cong_p01_p04_p02_p03 & Cong_p01_p02_p04_p03 & CongA_p02_p01_p04_p04_p03_p02 & CongA_p01_p04_p03_p03_p02_p01 & CongTriangles_p02_p01_p04_p04_p03_p02)."

destruct_TarskiPar = """
assert (TarskiPar_p01_p02_p03_p04_2 := TarskiPar_p01_p02_p03_p04).
destruct TarskiPar_p01_p02_p03_p04_2 as (neq_p01_p02 & neq_p03_p04 & n_Meet_p01_p02_p03_p04 & SameSide_p03_p04_p01_p02).
"""

by_prop_Supp_symmetric = "pose proof (by_prop_Supp_symmetric _ _ Supp_p01_p02_p03_p04_p05) as Supp_p05_p02_p04_p03_p01."

by_def_nCol_from_Triangle = "pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_p01_p02_p03) as nCol_p01_p02_p03."
# fmt: on


def replace_points(f: str, points: list[str]) -> str:
    var_names = [f"p{i:02}" for i in range(1,20)]
    for old, new in zip(var_names, points):
        f = f.replace(old, new)
    return f


def main():
    h = sys.argv[1]

    t, *points = h.split("_")

    match t:
        case "BetS":
            print(replace_points(axiom_betweennesssymmetry, points))
            print(replace_points(by_prop_BetS_notequal, points))
            print(replace_points(by_prop_BetS_notequal, reversed(points)))
            print(replace_points(by_def_Col_from_BetS_A_B_C, points))
            print(replace_points(by_prop_Col_order, points))
        case "Col":
            print(replace_points(by_prop_Col_order, points))
            print(replace_points(destruct_Col, points))
        case "nCol":
            print(replace_points(by_prop_nCol_order, points))
            print(replace_points(by_prop_nCol_distinct, points))
            print(replace_points(by_def_n_Col_from_nCol, points))
            print(replace_points(by_def_nCol_from_n_Col, points))
        case "CongA":
            points_symmetric = points[3:] + points[0:3]
            print(replace_points(by_prop_CongA_symmetric, points))
            print(replace_points(by_prop_CongA_flip_left, points))
            print(replace_points(by_prop_CongA_flip_left, points_symmetric))
            print(replace_points(by_prop_CongA_flip_right, points))
            print(replace_points(by_prop_CongA_flip_right, points_symmetric))
            print(replace_points(by_prop_CongA_NC, points))
            print(replace_points(by_prop_CongA_NC, points_symmetric))
            print(replace_points(by_prop_nCol_order, points[0:3]))
            print(replace_points(by_prop_nCol_order, points[3:]))
        case "OppositeSide":
            print(replace_points(destruct_OppositeSide, points))
        case "OnRay":
            print(replace_points(destruct_OnRay, points))
        case "Cong":
            print(replace_points(by_prop_Cong_flip, points))
            print(replace_points(by_prop_Cong_symmetric, points))
            print(replace_points(by_prop_Cong_flip, points[2:] + points[:2]))
        case "Par":
            print(replace_points(by_prop_Par_flip, points))
            print(replace_points(by_prop_Par_symmetric, points))
            print(replace_points(by_prop_Par_flip, points[2:] + points[:2]))
            print(replace_points(by_prop_Par_NC, points))
            print(replace_points(destruct_Par_not_Meet, points))
            print(replace_points(by_prop_neq_symmetric, points[0:2]))
            print(replace_points(by_prop_neq_symmetric, points[2:4]))
            print(replace_points(destruct_Par, points))
        case "eq":
            print(replace_points(eq_reflexivity, points))
            print(replace_points(by_def_Col_from_eq_B_C, points))
            print(replace_points(by_prop_Col_A_B_B_order, points))
            print(replace_points(eq_neq_classic, points))
        case "neq":
            print(replace_points(by_def_OnRay_from_neq_A_B , points))
        case "Cross":
            print(replace_points(destruct_Cross , points))
        case "SumTwoRT":
            print(replace_points(destruct_SumTwoRT , points))
        case "Supp":
            print(replace_points(by_prop_Supp_symmetric, points))
        case "Midpoint":
            print(replace_points(destruct_Midpoint, points))
        case "Parallelogram":
            print(replace_points(destruct_Parallelogram, points))
            print(replace_points(proposition_34, points))
        case "TarskiPar":
            print(replace_points(destruct_TarskiPar, points))
        case "Triangle":
            print(replace_points(by_def_nCol_from_Triangle, points))
        case _:
            raise ValueError(f"Unsupported hypothesis type: {t}")


if __name__ == "__main__":
    main()
