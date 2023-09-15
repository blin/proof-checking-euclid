#!/usr/bin/env python3

import sys


# fmt: off
axiom_betweennesssymmetry = "pose proof (axiom_betweennesssymmetry _ _ _ BetS_p1_p2_p3) as BetS_p3_p2_p1."
by_prop_BetS_notequal = "pose proof (by_prop_BetS_notequal _ _ _ BetS_p1_p2_p3) as (neq_p2_p3 & neq_p1_p2 & neq_p1_p3)."
by_def_Col_from_BetS_A_B_C = "pose proof (by_def_Col_from_BetS_A_B_C _ _ _ BetS_p1_p2_p3) as Col_p1_p2_p3."

by_prop_Col_order = "pose proof (by_prop_Col_order _ _ _ Col_p1_p2_p3) as (Col_p2_p1_p3 & Col_p2_p3_p1 & Col_p3_p1_p2 & Col_p1_p3_p2 & Col_p3_p2_p1)."
destruct_Col = """\
assert (Col_p1_p2_p3_2 := Col_p1_p2_p3).
destruct Col_p1_p2_p3_2 as [eq_p1_p2 | [eq_p1_p3 | [eq_p2_p3 | [BetS_p2_p1_p3 | [BetS_p1_p2_p3 | BetS_p1_p3_p2]]]]].
{
	(* case eq_p1_p2 *)
	admit.
}
{
	(* case eq_p1_p3 *)
	admit.
}
{
	(* case eq_p2_p3 *)
	admit.
}
{
	(* case BetS_p2_p1_p3 *)
	admit.
}
{
	(* case BetS_p1_p2_p3 *)
	admit.
}
{
	(* case BetS_p1_p3_p2 *)
	admit.
}
"""

by_def_nCol_from_n_Col = "pose proof (by_def_nCol_from_n_Col _ _ _ n_Col_p1_p2_p3) as nCol_p1_p2_p3."
by_def_n_Col_from_nCol = "pose proof (by_def_n_Col_from_nCol _ _ _ nCol_p1_p2_p3) as n_Col_p1_p2_p3."
by_prop_nCol_distinct = "pose proof (by_prop_nCol_distinct _ _ _ nCol_p1_p2_p3) as (neq_p1_p2 & neq_p2_p3 & neq_p1_p3 & neq_p2_p1 & neq_p3_p2 & neq_p3_p1)."
by_prop_nCol_order = "pose proof (by_prop_nCol_order _ _ _ nCol_p1_p2_p3) as (nCol_p2_p1_p3 & nCol_p2_p3_p1 & nCol_p3_p1_p2 & nCol_p1_p3_p2 & nCol_p3_p2_p1)."

by_prop_CongA_symmetric = "pose proof (by_prop_CongA_symmetric _ _ _ _ _ _ CongA_p1_p2_p3_p4_p5_p6) as CongA_p4_p5_p6_p1_p2_p3."
by_prop_CongA_distinct = "pose proof (by_prop_CongA_distinct _ _ _ _ _ _ CongA_p1_p2_p3_p4_p5_p6) as (neq_p1_p2 & neq_p2_p3 & neq_p1_p3 & neq_p4_p5 & neq_p5_p6 & neq_p4_p6)."
by_prop_CongA_NC = "pose proof (by_prop_CongA_NC _ _ _ _ _ _ CongA_p1_p2_p3_p4_p5_p6) as nCol_p4_p5_p6."

destruct_OppositeSide = """\
assert (OppositeSide_p1_p2_p3_p4_2 := OppositeSide_p1_p2_p3_p4).
destruct OppositeSide_p1_p2_p3_p4_2 as (p5 & BetS_p1_p5_p4 & Col_p2_p3_p5 & nCol_p2_p3_p1).
"""

eq_reflexivity = "assert (eq p1 p1) as eq_p1_p1 by (reflexivity)."
by_def_Col_from_eq_B_C = "pose proof (by_def_Col_from_eq_B_C sp p1 p1 eq_p1_p1) as Col_sp_p1_p1."
by_prop_Col_A_B_B_order = "pose proof (by_prop_Col_order _ _ _ Col_sp_p1_p1) as (Col_p1_sp_p1 & Col_p1_p1_sp & _ & _ & _)."

destruct_OnRay = """
pose proof (by_prop_OnRay_orderofpoints_any _ _ _ OnRay_p1_p2_p3) as [BetS_p1_p3_p2 | [eq_p2_p3 | BetS_p1_p2_p3]].
{
    (* case BetS_p1_p3_p2 *)
    admit.
}
{
    (* case eq_p2_p3 *)
    admit.
}
{
    (* case BetS_p1_p2_p3 *)
    admit.
}
"""

by_prop_Cong_flip = "pose proof (by_prop_Cong_flip _ _ _ _ Cong_p1_p2_p3_p4) as (Cong_p2_p1_p4_p3 & Cong_p2_p1_p3_p4 & Cong_p1_p2_p4_p3)."
by_prop_Cong_symmetric = "pose proof (by_prop_Cong_symmetric _ _ _ _ Cong_p1_p2_p3_p4) as Cong_p3_p4_p1_p2." 

by_prop_Par_flip = "pose proof (by_prop_Par_flip _ _ _ _ Par_p1_p2_p3_p4) as (Par_p2_p1_p3_p4 & Par_p1_p2_p4_p3 & Par_p2_p1_p4_p3)."
by_prop_Par_symmetric = "pose proof (by_prop_Par_symmetric _ _ _ _ Par_p1_p2_p3_p4) as Par_p3_p4_p1_p2." 
by_prop_Par_NC = "pose proof (by_prop_Par_NC _ _ _ _ Par_p1_p2_p3_p4) as (nCol_p1_p2_p3 & nCol_p1_p3_p4 & nCol_p2_p3_p4 & nCol_p1_p2_p4)."

by_prop_neq_symmetric = "pose proof (by_prop_neq_symmetric _ _ neq_p1_p2) as neq_p2_p1."
by_def_OnRay_from_neq_A_B  = "pose proof (by_def_OnRay_from_neq_A_B _ _ neq_p1_p2) as OnRay_p1_p2_p2."


destruct_Par = """
assert (Par_p1_p2_p3_p4_2 := Par_p1_p2_p3_p4).
destruct Par_p1_p2_p3_p4_2 as (p5 & p6 & p7 & p8 & p9 & neq_p1_p2 & neq_p3_p4 & Col_p1_p2_p5 & Col_p1_p2_p6 & neq_p5_p6 & Col_p3_p4_p7 & Col_p3_p4_p8 & neq_p7_p8 & n_Meet_p1_p2_p3_p4 & BetS_p5_p9_p8 & BetS_p7_p9_p6).\
"""
# fmt: on


def replace_points(f: str, points: list[str]) -> str:
    for old, new in zip(["p1", "p2", "p3", "p4", "p5", "p6"], points):
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
            print(replace_points(by_prop_CongA_symmetric, points))
            print(replace_points(by_prop_CongA_NC, points))
            print(replace_points(by_prop_CongA_NC, points[3:] + points[0:3]))
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
            print(replace_points(destruct_Par, points))
            print(replace_points(by_prop_neq_symmetric, points[0:2]))
            print(replace_points(by_prop_neq_symmetric, points[2:4]))
        case "eq":
            print(replace_points(eq_reflexivity, points))
            print(replace_points(by_def_Col_from_eq_B_C, points))
            print(replace_points(by_prop_Col_A_B_B_order, points))
        case "neq":
            print(replace_points(by_def_OnRay_from_neq_A_B , points))
        case _:
            raise ValueError(f"Unsupported hypothesis type: {t}")


if __name__ == "__main__":
    main()
