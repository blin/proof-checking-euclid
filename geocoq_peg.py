import itertools
from typing import Any, TextIO
from dataclasses import dataclass
import io

cols = []


class Expression:
    def to_str(self) -> str:
        raise NotImplementedError

    def to_var(self) -> str:
        raise NotImplementedError


class PrefixedStringIO:
    def __init__(self, w: io.StringIO, p: str):
        self.w = w
        self.p = p

    def write(self, s: str) -> None:
        self.w.write(self.p)
        self.w.write(s)

    def getvalue(self) -> str:
        return self.w.getvalue()


@dataclass
class Hypothesis(Expression):
    head: str
    points: list[str]

    def to_str(self) -> str:
        return f"{self.head} {' '.join(self.points)}"

    def to_var(self) -> str:
        return f"{self.head}_{'_'.join(self.points)}"


@dataclass
class Inversion(Expression):
    h: Hypothesis

    def to_str(self) -> str:
        return f"~ {self.h.to_str()}"

    def to_var(self) -> str:
        return f"n_{self.h.to_var()}"


@dataclass
class Disjunction(Expression):
    hs: list[Hypothesis]

    def to_str(self) -> str:
        return " \\/ ".join([h.to_str() for h in self.hs])

    def to_var(self) -> str:
        return " | ".join([h.to_var() for h in self.hs])


@dataclass
class Conjunction(Expression):
    hs: list[Hypothesis]

    def to_str(self) -> str:
        return " /\\ ".join([h.to_str() for h in self.hs])

    def to_var(self) -> str:
        return " & ".join([h.to_var() for h in self.hs])


def proposition_03(e: Conjunction, stack: list[list[Any]], w: TextIO) -> None:
    BetS_E_X_F, Cong_E_X_C_D = e.hs
    E, X, F = BetS_E_X_F.points
    E, X, C, D = Cong_E_X_C_D.points

    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_lt = [h for h in hhs if h.head == "Lt"]
    hhs_cong = [h for h in hhs if h.head == "Cong"]
    for hh_lt in hhs_lt:
        lt_C, lt_D, A, B = hh_lt.points
        if [lt_C, lt_D] != [C, D]:
            continue
        for hh_cong in hhs_cong:
            cong_E, cong_F, cong_A, cong_B = hh_cong.points
            if [cong_E, cong_F, cong_A, cong_B] != [E, F, A, B]:
                continue
            w.write(
                f"pose proof (proposition_03 {A} {B} {C} {D} {E} {F} Lt_{C}_{D}_{A}_{B} Cong_{E}_{F}_{A}_{B}) as ({X} & {e.to_var()}).\n"
            )
            break


def proposition_04(e: Conjunction, stack: list[list[Any]], w: TextIO) -> None:
    Cong_B_C_b_c, CongA_A_B_C_a_b_c, CongA_A_C_B_a_c_b = e.hs
    B, C, b, c = Cong_B_C_b_c.points
    A, B, C, a, b, c = CongA_A_B_C_a_b_c.points
    A, C, B, a, c, b = CongA_A_C_B_a_c_b.points
    w.write(
        f"pose proof (proposition_04 {A} {B} {C} {a} {b} {c} Cong_{A}_{B}_{a}_{b} Cong_{A}_{C}_{a}_{c} CongA_{B}_{A}_{C}_{b}_{a}_{c}) as ({e.to_var()}).\n"
    )


def proposition_10(e: Conjunction, stack: list[list[Any]], w: TextIO) -> None:
    BetS_A_X_B, Cong_X_A_X_B = e.hs
    A, X, B = BetS_A_X_B.points
    X, A, X, B = Cong_X_A_X_B.points
    w.write(f"pose proof (proposition_10 {A} {B} neq_{A}_{B}) as ({X} & {e.to_var()}).\n")


def proposition_15(e: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    w.write("\n")
    A, E, C, D, E, B = e.points
    w.write(
        f"pose proof (proposition_15 {A} {B} {C} {D} {E} BetS_{A}_{E}_{B} BetS_{C}_{E}_{D} nCol_{A}_{E}_{C}) as ({e.to_var()} & _).\n"
    )
    C, E, B, A, E, D = e.points
    w.write(
        f"pose proof (proposition_15 {A} {B} {C} {D} {E} BetS_{A}_{E}_{B} BetS_{C}_{E}_{D} nCol_{A}_{E}_{C}) as (_ & {e.to_var()}).\n"
    )
    w.write("\n")


def proposition_16(e: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    w.write("\n")
    B, A, C, A, C, D = e.points
    w.write(
        f"pose proof (proposition_16 {A} {B} {C} {D} Triangle_{A}_{B}_{C} BetS_{B}_{C}_{D}) as ({e.to_var()} & _).\n"
    )
    C, B, A, A, C, D = e.points
    w.write(
        f"pose proof (proposition_16 {A} {B} {C} {D} Triangle_{A}_{B}_{C} BetS_{B}_{C}_{D}) as (_ & {e.to_var()}).\n"
    )
    w.write("\n")


def lemma_NChelper(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    P, Q, C = e.points

    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_ncol = [h for h in hhs if h.head == "nCol"]
    hhs_col = [h for h in hhs if h.head == "Col"]

    for hh in hhs_ncol:
        ncol_A, ncol_B, ncol_C = hh.points
        if ncol_C != C:
            continue

        col_ABP = None
        for hhc in hhs_col:
            col_A, col_B, col_P = hhc.points
            if [col_A, col_B, col_P] != [ncol_A, ncol_B, P]:
                continue
            col_ABP = hhc
            break
        if col_ABP is None:
            continue

        col_ABQ = None
        for hhc in hhs_col:
            col_A, col_B, col_Q = hhc.points
            if [col_A, col_B, col_Q] != [ncol_A, ncol_B, Q]:
                continue
            col_ABQ = hhc
            break
        if col_ABQ is None:
            continue

        A, B = ncol_A, ncol_B
        w.write(
            f"pose proof (lemma_NChelper _ _ _ _ _ nCol_{A}_{B}_{C} Col_{A}_{B}_{P} Col_{A}_{B}_{Q} neq_{P}_{Q}) as nCol_{P}_{Q}_{C}.\n"
        )
        break


def lemma_crossbar(e: Conjunction, stack: list[list[Any]], w: TextIO) -> None:
    # Triangle A B C -> BetS A E C -> OnRay B A U -> OnRay B C V -> exists X, OnRay B E X /\ BetS U X V.
    OnRay_B_E_X, BetS_U_X_V = e.hs
    B, E, X = OnRay_B_E_X.points
    U, X, V = BetS_U_X_V.points

    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_triangle = [h for h in hhs if h.head == "Triangle"]
    for hh_triangle in hhs_triangle:
        A, triangle_B, C = hh_triangle.points
        if triangle_B != B:
            continue
        w.write(
            f"pose proof (lemma_crossbar _ _ _ _ _ _ {hh_triangle.to_var()} BetS_{A}_{E}_{C} OnRay_{B}_{A}_{U} OnRay_{B}_{C}_{V}) as ({X} & {e.to_var()}).\n"
        )


def LtA(e: Expression, stack: list[list[Any]], w: TextIO) -> None:
    if isinstance(e, Hypothesis):
        # Definition LtA A B C D E F := exists U X V, BetS U X V /\ OnRay E D U /\ OnRay E F V /\ CongA A B C D E X.
        A, B, C, D, E, F = e.points

        hhs = itertools.chain(*stack)
        hhs = [h for h in hhs if isinstance(h, Hypothesis)]
        hhs_onray = [h for h in hhs if h.head == "OnRay"]
        hhs_conga = [h for h in hhs if h.head == "CongA"]
        hhs_bets = [h for h in hhs if h.head == "BetS"]

        for hh_onray in hhs_onray:
            onray_E, onray_D, U = hh_onray.points
            if [onray_E, onray_D] != [E, D]:
                continue
            for hh_onray2 in hhs_onray:
                onray2_E, onray2_F, V = hh_onray2.points
                if [onray2_E, onray2_F] != [E, F]:
                    continue
                for hh_conga in hhs_conga:
                    conga_A, conga_B, conga_C, conga_D, conga_E, X = hh_conga.points
                    if [conga_A, conga_B, conga_C, conga_D, conga_E] != [A, B, C, D, E]:
                        continue
                    for hh_bets in hhs_bets:
                        bets_U, bets_X, bets_V = hh_bets.points
                        if [bets_U, bets_X, bets_V] != [U, X, V]:
                            continue

                        w.write(
                            f"pose proof (lemma_s_lta _ _ _ _ _ _ _ _ _ BetS_{U}_{X}_{V} OnRay_{E}_{D}_{U} OnRay_{E}_{F}_{V} CongA_{A}_{B}_{C}_{D}_{E}_{X}) as {e.to_var()}.\n"
                        )
                        return
    if not isinstance(e, Conjunction):
        return
    BetS_U_X_V, OnRay_E_D_U, OnRay_E_F_V, CongA_A_B_C_D_E_X = e.hs
    U, X, V = BetS_U_X_V.points
    E, D, U = OnRay_E_D_U.points
    E, F, V = OnRay_E_F_V.points
    A, B, C, D, E, X = CongA_A_B_C_D_E_X.points
    w.write(f"destruct LtA_{A}_{B}_{C}_{D}_{E}_{F} as ({U} & {X} & {V} & {e.to_var()}).\n")


def isosceles(e: Expression, stack: list[list[Any]], w: TextIO) -> None:
    # Definition isosceles A B C := Triangle A B C /\ Cong A B A C.
    A, B, C = e.points
    w.write(
        f"pose proof (lemma_s_isosceles _ _ _ Triangle_{A}_{B}_{C} Cong_{A}_{B}_{A}_{C}) as {e.to_var()}.\n"
    )
