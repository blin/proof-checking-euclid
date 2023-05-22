import itertools
from typing import Any, Optional, TextIO
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor, Node
from dataclasses import dataclass
import io

cols = []


class Expression:
    def to_str(self) -> str:
        raise NotImplementedError

    def to_var(self) -> str:
        raise NotImplementedError


@dataclass
class UnneededStatement:
    text: str


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


class Assertion:
    by: str

    def to_str(self, indent: int, stack: list[list[Any]]) -> str:
        raise NotImplementedError

    def modify_stack_post(self, stack: list[list[Any]]):
        raise NotImplementedError


@dataclass
class ConcludeAssertion(Assertion):
    e: Expression
    by: str
    conclude_type: str

    def to_str(self, indent: int, stack: list[list[Any]]) -> str:
        return "\t" * indent + f"pose proof ({self.by}) as {self.e.to_var()}.\n"

    def modify_stack_post(self, stack: list[list[Any]]):
        frame = stack[-1]
        frame.append(self.e)


@dataclass
class ContradictAssertion(Assertion):
    e: Expression
    by: str
    assertions: Assertion

    def to_str(self, indent: int, stack: list[list[Any]]) -> str:
        w = io.StringIO()
        w.write("\n")
        w.write("\t" * indent)
        if isinstance(self.e, Inversion):
            var_name = f"n{self.e.to_var()}" if self.e.h.head in ["eq"] else f"n_{self.e.to_var()}"
        elif isinstance(self.e, Hypothesis):
            var_name = f"n{self.e.to_var()}" if self.e.head in ["eq"] else f"n_{self.e.to_var()}"
        else:
            raise ValueError(f"expected to contradict Hypothesis or Inversion, got: {self.e}")
        w.write(f"assert (~ {self.e.to_str()}) as {var_name}.\n")
        stack.append(list())
        w.write("\t" * indent)
        w.write("{\n")
        indent += 1
        w.write("\t" * indent)
        w.write(f"intro {self.e.to_var()}.\n")
        stack[-1].append(self.e)
        w.write("\n")
        for a in self.assertions:
            if a.by in globals():
                globals()[a.by](a.e, stack, PrefixedStringIO(w, "\t" * indent))
            else:
                w.write(a.to_str(indent=indent, stack=stack))
            a.modify_stack_post(stack)
        # TODO: contradict last statement
        last_s = self.assertions[-1].e
        w.write("\n")
        w.write("\t" * indent)
        w.write(f"contradict {last_s.to_var()}.\n")
        w.write("\t" * indent)
        w.write(f"exact n_{last_s.to_var()}.\n")
        indent -= 1
        w.write("\t" * indent)
        w.write("}\n")
        stack.pop()
        if isinstance(self.e, Inversion):
            if self.e.h.head in ["Col"]:
                w.write("\t" * indent)
                w.write(f"pose proof (lemma_s_n_col_ncol _ _ _ n_{self.e.to_var()}) as n{self.e.to_var()}.\n")
                stack[-1].append(Hypothesis(head="nCol", points=self.e.h.points))
        elif isinstance(self.e, Hypothesis):
            if self.e.head in ["Col"]:
                w.write("\t" * indent)
                w.write(f"pose proof (lemma_s_n_col_ncol _ _ _ n_{self.e.to_var()}) as n{self.e.to_var()}.\n")
                stack[-1].append(Hypothesis(head="nCol", points=self.e.points))
        else:
            raise ValueError(f"expected to contradict Hypothesis or Inversion, got: {self.e}")
        return w.getvalue()

    def modify_stack_post(self, stack: list[list[Any]]):
        pass


@dataclass
class ByCasesAssertion(Assertion):
    by: str

    def to_str(self, indent: int, stack: list[list[Any]]) -> str:
        # TODO: try proposition_04
        return "\t" * indent + "proof by cases.\n"


@dataclass
class DestructAssertion(Assertion):
    e: Expression
    points: list[str]
    by: str
    splitter_points: list[str]
    conclude_type: str

    def to_str(self, indent: int, stack: list[list[Any]]) -> str:
        ps = " & ".join(self.points)
        return "\t" * indent + f"pose proof ({self.by}) as ({ps} & {self.e.to_var()}).\n"

    def modify_stack_post(self, stack: list[list[Any]]):
        if not isinstance(self.e, Conjunction):
            raise ValueError("Expected a conjunction in destruct, got: {self.e}")
        frame = stack[-1]
        frame.extend(self.e.hs)


@dataclass
class Coq:
    lemma_name: str
    lemma_points: list[str]
    given_hypothesises: list[Expression]
    lemma_conclusion: Optional[Expression]
    lemma_conclusion_points: list[str]
    assertions: list[Assertion]
    requirements: set[str]


class CoqVisitor(NodeVisitor):
    def __init__(self):
        self.coq = Coq(
            lemma_name="",
            lemma_points=list(),
            given_hypothesises=list(),
            lemma_conclusion=None,
            lemma_conclusion_points=None,
            assertions=list(),
            requirements=set(),
        )

    def visit_lemma(self, node: Node, vc: list[Node]):
        lemma_intro = vc[0]
        self.coq.lemma_name = lemma_intro[2]

        lemma_statements = [s[0] for s in vc[1] if not isinstance(s[0], UnneededStatement)]
        # TODO: raise if not assertion
        self.coq.assertions = lemma_statements

    def visit_assert_contradiction(self, node: Node, vc: list[Node]):
        h = vc[1]
        assertions = [s[0] for s in vc[8]]
        return ContradictAssertion(e=h, by="contradiction", assertions=assertions)

    def visit_assert_by_cases(self, node: Node, vc: list[Node]):
        # TODO
        return ByCasesAssertion(by="cases")

    def visit_unneeded_statement(self, n: Node, _: list[Any]):
        return UnneededStatement(text=n.text)

    def visit_statement_assert(self, n: Node, vc: list[Any]):
        e = vc[3]
        conclude_type = vc[6]
        by = vc[8]
        self.coq.requirements.add(by)
        return ConcludeAssertion(e=e, by=by, conclude_type=conclude_type)

    def visit_conclude_type(self, n: Node, _: list[Any]):
        return n.text

    def visit_lemma_preamble_points(self, _: Node, vc: list[Any]):
        points = vc[2]
        self.coq.lemma_points = points

    def visit_lemma_preamble_given(self, _: Node, vc: list[Any]):
        h = vc[0]
        self.coq.given_hypothesises.append(h)

    def visit_lemma_preamble_conclusion(self, n: Node, vc: list[Any]):
        pp = vc[0]
        if isinstance(pp, list) and len(pp) == 1:
            p = pp[0][1]
            self.coq.lemma_conclusion_points = p
        h = vc[1]
        self.coq.lemma_conclusion = h

    def visit_disjunction(self, n: Node, vc: list[Any]):
        if isinstance(vc[0], Hypothesis):
            return vc[0]
        if isinstance(vc[0], Inversion):
            return vc[0]
        if isinstance(vc[0], Conjunction):
            return vc[0]

        vc2 = vc[0]
        h0 = vc2[0]
        h_rest = vc2[1]
        hhs = [h0]
        for h in h_rest:
            _, _, hh = h
            hhs.append(hh)
        return Disjunction(hs=hhs)

    def visit_conjunction(self, n: Node, vc: list[Any]):
        if isinstance(vc[0], Hypothesis):
            return vc[0]
        if isinstance(vc[0], Inversion):
            return vc[0]

        vc2 = vc[0]
        h0 = vc2[0]
        h_rest = vc2[1]
        hhs = [h0]
        for h in h_rest:
            _, _, hh = h
            hhs.append(hh)
        return Conjunction(hs=hhs)

    def visit_inversion(self, node: Node, vc: list[Any]):
        if isinstance(vc[0], Hypothesis):
            return vc[0]
        return Inversion(h=vc[0][2])

    def visit_hypothesis(self, node: Node, vc: list[Any]):
        return Hypothesis(head=vc[0], points=vc[1])

    def visit_qualified_id(self, _: Node, vc: list[Any]):
        path = [c for _, c in vc]
        return path

    def visit_destruct_assert(self, _: Node, vc: list[Any]):
        (
            _,
            points,
            _,
            _,
            _,
            expression,
            _,
            _,
            conclude_type,
            _,
            by,
            _,
            splitter_points,
            _,
        ) = vc
        self.coq.requirements.add(by)
        return DestructAssertion(
            e=expression,
            points=points,
            by=by,
            splitter_points=splitter_points,
            conclude_type=conclude_type,
        )

    def visit_destruct_splitter(self, _: Node, vc: list[Any]):
        _, points, _ = vc
        return points

    def visit_destruct_point(self, node: Node, vc: list[Any]):
        _, p, mp, _ = vc
        if isinstance(mp, list):
            return [p, *mp[0]]
        return [p]

    def visit_point(self, node: Node, _: list[Any]):
        n = node.children[0].text
        return n

    def visit_id(self, node: Node, _: list[Any]):
        n = node.children[0].text
        return n

    def generic_visit(self, node, vc):
        """The generic visit method."""
        return vc or node


# TODO: pose proof (postulate_Pasch_inner) as (H & BetS_D_H_E & BetS_F_H_C).
def axiom_betweennesssymmetry(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    A, B, C = h.points
    w.write(f"pose proof (axiom_betweennesssymmetry _ _ _ BetS_{C}_{B}_{A}) as BetS_{A}_{B}_{C}.\n")


def cn_congruencereflexive(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    A, B, _, _ = h.points
    w.write(f"pose proof (cn_congruencereflexive {A} {B}) as Cong_{A}_{B}_{A}_{B}.\n")


def cn_congruencetransitive(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    C, D, E, F = h.points
    w.write(f"pose proof (cn_congruencetransitive X Y {C} {D} {E} {F} Cong_X_Y_{C}_{D} Cong_X_Y_{E}_{F}) as Cong_{C}_{D}_{E}_{F}.\n")


def cn_equalityreflexive(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    A, A = h.points
    w.write(f"assert (eq {A} {A}) as eq_{A}_{A} by (reflexivity).\n")


def cn_equalitysub(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    if len(h.points) != 3:
        raise NotImplementedError("equalitysub with not 3 points is not yet done")
    A, B, C = h.points
    w.write("\n")
    w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite eq_{A}_X; exact {h.head}_X_{B}_{C}).\n")
    w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite eq_{B}_X; exact {h.head}_{A}_X_{C}).\n")
    w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite eq_{C}_X; exact {h.head}_{A}_{B}_X).\n")
    w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite <- eq_X_{A}; exact {h.head}_X_{B}_{C}).\n")
    w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite <- eq_X_{B}; exact {h.head}_{A}_X_{C}).\n")
    w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite <- eq_X_{C}; exact {h.head}_{A}_{B}_X).\n")
    w.write("\n")


def cn_congruencereverse(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    A, B, _, _ = h.points
    w.write(f"pose proof (cn_congruencereverse {A} {B}) as Cong_{A}_{B}_{B}_{A}.\n")


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


def proposition_05(e: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    A, B, C, A, C, B = e.points
    w.write(f"pose proof (proposition_05 _ _ _ isosceles_{A}_{B}_{C}) as {e.to_var()}.\n")


def proposition_10(e: Conjunction, stack: list[list[Any]], w: TextIO) -> None:
    BetS_A_X_B, Cong_X_A_X_B = e.hs
    A, X, B = BetS_A_X_B.points
    X, A, X, B = Cong_X_A_X_B.points
    w.write(f"pose proof (proposition_10 {A} {B} neq_{A}_{B}) as ({X} & {e.to_var()}).\n")


def proposition_15(e: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    w.write("\n")
    A, E, C, D, E, B = e.points
    w.write(f"pose proof (proposition_15 {A} {B} {C} {D} {E} BetS_{A}_{E}_{B} BetS_{C}_{E}_{D} nCol_{A}_{E}_{C}) as ({e.to_var()} & _).\n")
    C, E, B, A, E, D = e.points
    w.write(f"pose proof (proposition_15 {A} {B} {C} {D} {E} BetS_{A}_{E}_{B} BetS_{C}_{E}_{D} nCol_{A}_{E}_{C}) as (_ & {e.to_var()}).\n")
    w.write("\n")


def proposition_16(e: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    w.write("\n")
    B, A, C, A, C, D = e.points
    w.write(f"pose proof (proposition_16 {A} {B} {C} {D} Triangle_{A}_{B}_{C} BetS_{B}_{C}_{D}) as ({e.to_var()} & _).\n")
    C, B, A, A, C, D = e.points
    w.write(f"pose proof (proposition_16 {A} {B} {C} {D} Triangle_{A}_{B}_{C} BetS_{B}_{C}_{D}) as (_ & {e.to_var()}).\n")
    w.write("\n")


def lemma_ABCequalsCBA(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, B, C, C, B, A = e.points
    w.write(f"pose proof (lemma_ABCequalsCBA {A} {B} {C} nCol_{A}_{B}_{C}) as {e.to_var()}.\n")


def lemma_NCdistinct(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs = [h for h in hhs if h.head == "nCol"]

    for hh in hhs:
        if not (set(e.points) <= set(hh.points)):
            continue
        X, Y, Z = hh.points
        w.write(
            f"pose proof (lemma_NCdistinct _ _ _ nCol_{X}_{Y}_{Z}) as (neq_{X}_{Y} & neq_{Y}_{Z} & neq_{X}_{Z} & neq_{Y}_{X} & neq_{Z}_{Y} & neq_{Z}_{X}).\n"
        )
        break


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


def lemma_NCorder(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs = [h for h in hhs if h.head == "nCol"]

    for hh in hhs:
        if set(e.points) != set(hh.points):
            continue
        X, Y, Z = hh.points
        w.write(
            f"pose proof (lemma_NCorder _ _ _ nCol_{X}_{Y}_{Z}) as (nCol_{Y}_{X}_{Z} & nCol_{Y}_{Z}_{X} & nCol_{Z}_{X}_{Y} & nCol_{X}_{Z}_{Y} & nCol_{Z}_{Y}_{X}).\n"
        )
        break


def lemma_angledistinct(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    A, B = h.points

    w.write("\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_{A}_{B}_Z_x_y_z) as (neq_{A}_{B} & _ & _ & _ & _ & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_X_{A}_{B}_x_y_z) as (_ & neq_{A}_{B} & _ & _ & _ & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_{A}_Y_{B}_x_y_z) as (_ & _ & neq_{A}_{B} & _ & _ & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_X_Y_Z_{A}_{B}_z) as (_ & _ & _ & neq_{A}_{B} & _ & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_X_Y_Z_x_{A}_{B}) as (_ & _ & _ & _ & neq_{A}_{B} & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_X_Y_Z_{A}_y_{B}) as (_ & _ & _ & _ & _ & neq_{A}_{B}).\n")
    w.write("\n")


def lemma_angleorderrespectscongruence(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, B, C, a, b, c = e.points

    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_lta = [h for h in hhs if h.head == "LtA"]
    hhs_conga = [h for h in hhs if h.head == "CongA"]

    for hh_lta in hhs_lta:
        lta_A, lta_B, lta_C, D, E, F = hh_lta.points
        if [lta_A, lta_B, lta_C] != [A, B, C]:
            continue
        for hh_conga in hhs_conga:
            conga_a, conga_b, conga_c, conga_D, conga_E, conga_F = hh_conga.points
            if [conga_a, conga_b, conga_c, conga_D, conga_E, conga_F] != [a, b, c, D, E, F]:
                continue

            w.write(
                f"pose proof (lemma_angleorderrespectscongruence _ _ _ _ _ _ _ _ _ LtA_{A}_{B}_{C}_{D}_{E}_{F} CongA_{a}_{b}_{c}_{D}_{E}_{F}) as {e.to_var()}.\n"
            )
            break


def lemma_angleorderrespectscongruence_smaller(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_lta = [h for h in hhs if h.head == "LtA"]
    hhs_conga = [h for h in hhs if h.head == "CongA"]

    a, b, c, D, E, F = e.points
    for hh_lta in hhs_lta:
        X, Y, Z, lta_D, lta_E, lta_F = hh_lta.points
        if [lta_D, lta_E, lta_F] != [D, E, F]:
            continue
        for hh_conga in hhs_conga:
            conga_a, conga_b, conga_c, conga_X, conga_Y, conga_Z = hh_conga.points
            if [conga_a, conga_b, conga_c, conga_X, conga_Y, conga_Z] != [a, b, c, X, Y, Z]:
                continue

            w.write(
                f"pose proof (lemma_angleorderrespectscongruence_smaller _ _ _ _ _ _ _ _ _ {hh_lta.to_var()} {hh_conga.to_var()}) as {e.to_var()}.\n"
            )
            break


def lemma_angleordertransitive(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, B, C, P, Q, R = e.points

    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_lta = [h for h in hhs if h.head == "LtA"]

    for hh_lta in hhs_lta:
        lta_A, lta_B, lta_C, D, E, F = hh_lta.points
        if [lta_A, lta_B, lta_C] != [A, B, C]:
            continue
        for hh_lta2 in hhs_lta:
            lta2_D, lta2_E, lta2_F, lta2_P, lta2_Q, lta2_R = hh_lta2.points
            if [lta2_D, lta2_E, lta2_F, lta2_P, lta2_Q, lta2_R] != [D, E, F, P, Q, R]:
                continue

            w.write(
                f"pose proof (lemma_angleordertransitive _ _ _ _ _ _ _ _ _ LtA_{A}_{B}_{C}_{D}_{E}_{F} LtA_{D}_{E}_{F}_{P}_{Q}_{R}) as {e.to_var()}.\n"
            )
            break


def lemma_betweennotequal(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs = [h for h in hhs if h.head == "BetS"]

    A, B = e.points
    for hh in hhs:
        if not (set(e.points) <= set(hh.points)):
            continue
        X, Y, Z = hh.points
        if [A, B] == [Y, Z]:
            w.write(f"pose proof (lemma_betweennotequal _ _ _ BetS_{X}_{Y}_{Z}) as (neq_{Y}_{Z} & _ & _).\n")
            break
        elif [A, B] == [X, Y]:
            w.write(f"pose proof (lemma_betweennotequal _ _ _ BetS_{X}_{Y}_{Z}) as (_ & neq_{X}_{Y} & _).\n")
            break
        elif [A, B] == [X, Z]:
            w.write(f"pose proof (lemma_betweennotequal _ _ _ BetS_{X}_{Y}_{Z}) as (_ & _ & neq_{X}_{Z}).\n")
            break


def lemma_collinear_ABC_ABD_BCD(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    B, C, D = e.points

    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_col = [h for h in hhs if h.head == "Col"]
    for hh_col in hhs_col:
        A, col_B, col_C = hh_col.points
        if [col_B, col_C] != [B, C]:
            continue
        for hh_col2 in hhs_col:
            col2_A, col2_B, col2_D = hh_col2.points
            if [col2_A, col2_B, col2_D] != [A, B, D]:
                continue

            w.write(f"pose proof (lemma_collinear_ABC_ABD_BCD _ _ _ _ Col_{A}_{B}_{C} Col_{A}_{B}_{D} neq_{A}_{B}) as {e.to_var()}.\n")


def lemma_collinearorder(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs = [h for h in hhs if h.head == "Col"]

    for col in hhs:
        if set(e.points) != set(col.points):
            continue
        X, Y, Z = col.points
        w.write(
            f"pose proof (lemma_collinearorder _ _ _ Col_{X}_{Y}_{Z}) as (Col_{Y}_{X}_{Z} & Col_{Y}_{Z}_{X} & Col_{Z}_{X}_{Y} & Col_{X}_{Z}_{Y} & Col_{Z}_{Y}_{X}).\n"
        )
        break


def lemma_congruenceflip(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    w.write("\n")
    B, A, D, C = e.points
    w.write(f"pose proof (lemma_congruenceflip {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as ({e.to_var()} & _ & _).\n")
    B, A, C, D = e.points
    w.write(f"pose proof (lemma_congruenceflip {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as (_ & {e.to_var()} & _).\n")
    A, B, D, C = e.points
    w.write(f"pose proof (lemma_congruenceflip {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as (_ & _ & {e.to_var()}).\n")
    w.write("\n")


def lemma_congruencesymmetric(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    C, D, A, B = h.points
    w.write(f"pose proof (lemma_congruencesymmetric {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as Cong_{C}_{D}_{A}_{B}.\n")


def lemma_congruencetransitive(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    A, B, E, F = h.points
    w.write(f"pose proof (lemma_congruencetransitive {A} {B} X Y {E} {F} Cong_{A}_{B}_X_Y Cong_X_Y_{E}_{F}) as Cong_{A}_{B}_{E}_{F}.\n")


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


def lemma_doublereverse(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    w.write("\n")
    D, C, B, A = e.points
    w.write(f"pose proof (lemma_doublereverse {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as ({e.to_var()} & _).\n")
    B, A, D, C = e.points
    w.write(f"pose proof (lemma_doublereverse {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as (_ & {e.to_var()}).\n")
    w.write("\n")


def lemma_equalanglesNC(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    a, b, c = e.points
    w.write(f"pose proof (lemma_equalanglesNC X Y Z {a} {b} {c} CongA_X_Y_Z_{a}_{b}_{c}) as {e.to_var()}.\n")


def lemma_equalangleshelper(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, B, C, p, b, q = e.points

    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_conga = [h for h in hhs if h.head == "CongA"]

    for hh_conga in hhs_conga:
        conga_A, conga_B, conga_C, a, conga_b, c = hh_conga.points
        if [conga_A, conga_B, conga_C, conga_b] != [A, B, C, b]:
            continue
        w.write(
            f"pose proof (lemma_equalangleshelper _ _ _ _ _ _ _ _ {hh_conga.to_var()} OnRay_{b}_{a}_{p} OnRay_{b}_{c}_{q}) as {e.to_var()}.\n"
        )


def lemma_equalanglesreflexive(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, B, C, A, B, C = e.points
    w.write(f"pose proof (lemma_equalanglesreflexive {A} {B} {C} nCol_{A}_{B}_{C}) as {e.to_var()}.\n")


def lemma_equalanglessymmetric(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    a, b, c, A, B, C = e.points
    w.write(f"pose proof (lemma_equalanglessymmetric {A} {B} {C} {a} {b} {c} CongA_{A}_{B}_{C}_{a}_{b}_{c}) as {e.to_var()}.\n")


# TODO: next pose proof (postulate_Pasch_inner) as (F & BetS_A_F_C & BetS_B_F_E).
def lemma_equalanglestransitive(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, B, C, P, Q, R = e.points

    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_conga = [h for h in hhs if h.head == "CongA"]
    for hh_conga in hhs_conga:
        conga_A, conga_B, conga_C, D, E, F = hh_conga.points
        if [conga_A, conga_B, conga_C] != [A, B, C]:
            continue
        for hh_conga2 in hhs_conga:
            conga2_D, conga2_E, conga2_F, conga2_P, conga2_Q, conga2_R = hh_conga2.points
            if [conga2_D, conga2_E, conga2_F, conga2_P, conga2_Q, conga2_R] != [D, E, F, P, Q, R]:
                continue

            w.write(
                f"pose proof (lemma_equalanglestransitive _ _ _ _ _ _ _ _ _ {hh_conga.to_var()} {hh_conga2.to_var()}) as {e.to_var()}.\n"
            )


def lemma_extension(e: Conjunction, stack: list[list[Any]], w: TextIO) -> None:
    BetS_A_B_X, Cong_B_X_P_Q = e.hs
    A, B, X = BetS_A_B_X.points
    B, X, P, Q = Cong_B_X_P_Q.points
    w.write(f"pose proof (lemma_extension {A} {B} {P} {Q} neq_{A}_{B} neq_{P}_{Q}) as ({X} & {e.to_var()}).\n")


def lemma_inequalitysymmetric(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    B, A = h.points
    w.write(f"pose proof (lemma_inequalitysymmetric {A} {B} neq_{A}_{B}) as neq_{B}_{A}.\n")


def lemma_onray_neq_A_B(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, B = e.points

    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs = [h for h in hhs if h.head == "OnRay"]
    for hh in hhs:
        X, Y, _ = hh.points
        if [X, Y] == [A, B]:
            w.write(f"pose proof (lemma_onray_neq_A_B _ _ _ {hh.to_var()}) as {e.to_var()}.\n")
            break


def lemma_onray_ABC_ACB(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, C, B = e.points
    w.write(f"pose proof (lemma_onray_ABC_ACB {A} {B} {C} OnRay_{A}_{B}_{C}) as {e.to_var()}.\n")


def lemma_onray_assert(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, B, E = e.points
    if B == E:
        w.write(f"pose proof (lemma_s_onray_assert_ABB {A} {B} neq_{A}_{B}) as {e.to_var()}.\n")
    else:
        w.write(f"pose proof (lemma_s_onray_assert_bets_ABE {A} {B} {E} BetS_{A}_{B}_{E} neq_{A}_{B}) as {e.to_var()}.\n")
        w.write(f"pose proof (lemma_s_onray_assert_bets_AEB {A} {B} {E} BetS_{A}_{E}_{B} neq_{A}_{B}) as {e.to_var()}.\n")


def lemma_onray_impliescollinear(e: Hypothesis, stack: list[list[Any]], w: TextIO):
    A, B, C = e.points
    w.write(f"pose proof (lemma_onray_impliescollinear _ _ _ OnRay_{A}_{B}_{C}) as {e.to_var()}.\n")


def Triangle(h: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    A, B, C = h.points
    if h.head == "nCol":
        w.write(f"pose proof (lemma_s_ncol_triangle {A} {B} {C} Triangle_{A}_{B}_{C}) as nCol_{A}_{B}_{C}.\n")
        w.write(f"pose proof (lemma_s_ncol_n_col {A} {B} {C} nCol_{A}_{B}_{C}) as n_Col_{A}_{B}_{C}.\n")
    elif h.head == "Triangle":
        w.write(f"pose proof (lemma_s_triangle {A} {B} {C} nCol_{A}_{B}_{C}) as Triangle_{A}_{B}_{C}.\n")
    else:
        raise ValueError(f"Expected assertion by Triangle to be either nCol or Triangle, got: {h.head}")


def Col(e: Hypothesis, stack: list[list[Any]], w: TextIO) -> None:
    hhs = itertools.chain(*stack)
    hhs = [h for h in hhs if isinstance(h, Hypothesis)]
    hhs_eq = [h for h in hhs if h.head == "eq"]
    hhs_bets = [h for h in hhs if h.head == "BetS"]

    A, B, C = e.points
    for hh in hhs_eq:
        if not (set(hh.points) <= set(e.points)):
            continue
        X, Y = hh.points
        if [X, Y] == [A, B]:
            w.write(f"pose proof (lemma_s_col_eq_A_B {A} {B} {C} eq_{A}_{B}) as Col_{A}_{B}_{C}.\n")
            break
        elif [X, Y] == [A, C]:
            w.write(f"pose proof (lemma_s_col_eq_A_C {A} {B} {C} eq_{A}_{C}) as Col_{A}_{B}_{C}.\n")
            break
        elif [X, Y] == [B, C]:
            w.write(f"pose proof (lemma_s_col_eq_B_C {A} {B} {C} eq_{B}_{C}) as Col_{A}_{B}_{C}.\n")
            break
    for hh in hhs_bets:
        if set(e.points) != set(hh.points):
            continue
        X, Y, Z = hh.points
        if [X, Y, Z] == [B, A, C]:
            w.write(f"pose proof (lemma_s_col_BetS_B_A_C {A} {B} {C} BetS_{B}_{A}_{C}) as Col_{A}_{B}_{C}.\n")
            break
        elif [X, Y, Z] == [A, B, C]:
            w.write(f"pose proof (lemma_s_col_BetS_A_B_C {A} {B} {C} BetS_{A}_{B}_{C}) as Col_{A}_{B}_{C}.\n")
            break
        elif [X, Y, Z] == [A, C, B]:
            w.write(f"pose proof (lemma_s_col_BetS_A_C_B {A} {B} {C} BetS_{A}_{C}_{B}) as Col_{A}_{B}_{C}.\n")
            break


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
    w.write(f"pose proof (lemma_s_isosceles _ _ _ Triangle_{A}_{B}_{C} Cong_{A}_{B}_{A}_{C}) as {e.to_var()}.\n")


def print_coq_top(c: Coq, w: TextIO) -> None:
    rs = c.requirements
    rs |= {
        "euclidean_axioms",
        "euclidean_defs",
        "euclidean_tactics",
        "lemma_s_col_BetS_A_B_C",
        "lemma_s_col_BetS_A_C_B",
        "lemma_s_col_BetS_B_A_C",
        "lemma_s_col_eq_A_B",
        "lemma_s_col_eq_A_C",
        "lemma_s_col_eq_B_C",
        "lemma_s_n_col_ncol",
        "lemma_s_ncol_n_col",
        "lemma_s_ncol_triangle",
        "lemma_s_onray_assert_ABB",
        "lemma_s_onray_assert_bets_ABE",
        "lemma_s_onray_assert_bets_AEB",
        "lemma_s_triangle",
        "lemma_NCorder",
        "lemma_NCdistinct",
        "lemma_s_lta",
        "lemma_s_isosceles",
    }
    for r in sorted(rs):
        if any([r.startswith(p) for p in ["cn_", "axiom_", "postulate_"]]):
            continue
        if not any([r.startswith(p) for p in ["lemma_", "proposition_", "euclidean_"]]):
            continue
        w.write(f"Require Import ProofCheckingEuclid.{r}.\n")
    w.write("\n")

    w.write("Section Euclid.\n\n")
    w.write("Context `{Ax:euclidean_neutral_ruler_compass}.\n\n")
    w.write(f"Lemma {c.lemma_name} :\n")
    w.write(f"\tforall {' '.join(c.lemma_points)},\n")
    for gh in c.given_hypothesises:
        w.write(f"\t{gh.to_str()} ->\n")
    if c.lemma_conclusion is None:
        raise ValueError("expected lemma to have conclusion")
    if c.lemma_conclusion_points:
        w.write(f"\texists {' '.join(c.lemma_conclusion_points)}, {c.lemma_conclusion.to_str()}.\n")
    else:
        w.write(f"\t{c.lemma_conclusion.to_str()}.\n")
    w.write("Proof.\n")

    w.write(f"\tintros {' '.join(c.lemma_points)}.\n")
    for gh in c.given_hypothesises:
        w.write(f"\tintros {gh.to_var()}.\n")
    w.write(f"\n")


def print_coq(c: Coq, w: io.StringIO) -> None:
    print_coq_top(c, w)

    asserted_stack = [[]]
    asserted_stack[-1].extend(c.given_hypothesises)
    indent = 1
    for a in c.assertions:
        if a.by in globals():
            # TODO: Out interacts poorly with jupyter
            if a.by == "Out":
                continue
            globals()[a.by](a.e, asserted_stack, PrefixedStringIO(w, "\t" * indent))
        else:
            w.write(a.to_str(indent=indent, stack=asserted_stack))
        a.modify_stack_post(asserted_stack)

    w.write("Qed.\n\n")
    w.write("End Euclid.\n")


tree = Grammar(open("geocoq.peg").read()).parse(open("/tmp/test.v").read())

v = CoqVisitor()
t = v.visit(tree)


s = io.StringIO()
print_coq(v.coq, s)
print(s.getvalue())
