from typing import Any, Optional, TextIO
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor, Node
from dataclasses import dataclass
import io


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

    def to_str(self, indent: int) -> str:
        raise NotImplementedError


@dataclass
class ConcludeAssertion(Assertion):
    e: Hypothesis
    by: str
    conclude_type: str

    def to_str(self, indent: int) -> str:
        return "\t" * indent + f"pose proof ({self.by}) as {self.e.to_var()}.\n"


@dataclass
class ContradictAssertion(Assertion):
    e: Hypothesis
    by: str
    assertions: Assertion

    def to_str(self, indent: int) -> str:
        w = io.StringIO()
        w.write("\n")
        w.write("\t" * indent)
        w.write(f"assert (~ {self.e.to_str()}) as n_{self.e.to_var()}.\n")
        w.write("\t" * indent)
        w.write("{\n")
        indent += 1
        w.write("\t" * indent)
        w.write(f"intro {self.e.to_var()}.\n")
        w.write("\n")
        for a in self.assertions:
            if a.by in globals():
                globals()[a.by](a.e, PrefixedStringIO(w, "\t" * indent))
            else:
                w.write(a.to_str(indent=indent))
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
        return w.getvalue()


@dataclass
class ByCasesAssertion(Assertion):
    by: str

    def to_str(self, indent: int) -> str:
        # TODO: try proposition_04
        return "\t" * indent + "proof by cases.\n"


@dataclass
class DestructAssertion(Assertion):
    e: Expression
    points: list[str]
    by: str
    splitter_points: list[str]
    conclude_type: str

    def to_str(self, indent: int) -> str:
        ps = " & ".join(self.points)
        return "\t" * indent + f"pose proof ({self.by}) as ({ps} & {self.e.to_var()}).\n"


@dataclass
class Coq:
    lemma_name: str
    lemma_points: list[str]
    given_hypothesises: list[Expression]
    lemma_conclusion: Optional[Expression]
    lemma_conclusion_point: Optional[str]
    assertions: list[Assertion]
    requirements: set[str]


class CoqVisitor(NodeVisitor):
    def __init__(self):
        self.coq = Coq(
            lemma_name="",
            lemma_points=list(),
            given_hypothesises=list(),
            lemma_conclusion=None,
            lemma_conclusion_point=None,
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
        h = vc[3]
        conclude_type = vc[6]
        by = vc[8]
        self.coq.requirements.add(by)
        return ConcludeAssertion(e=h, by=by, conclude_type=conclude_type)

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
            self.coq.lemma_conclusion_point = p
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


def cn_congruencereflexive(h: Hypothesis, w: TextIO) -> None:
    A, B, _, _ = h.points
    w.write(f"pose proof (cn_congruencereflexive {A} {B}) as Cong_{A}_{B}_{A}_{B}.\n")


def cn_congruencetransitive(h: Hypothesis, w: TextIO) -> None:
    C, D, E, F = h.points
    w.write(f"pose proof (cn_congruencetransitive X Y {C} {D} {E} {F} Cong_X_Y_{C}_{D} Cong_X_Y_{E}_{F}) as Cong_{C}_{D}_{E}_{F}.\n")


def cn_equalitysub(h: Hypothesis, w: TextIO) -> None:
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


def lemma_congruencesymmetric(h: Hypothesis, w: TextIO) -> None:
    C, D, A, B = h.points
    w.write(f"pose proof (lemma_congruencesymmetric {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as Cong_{C}_{D}_{A}_{B}.\n")


def cn_congruencereverse(h: Hypothesis, w: TextIO) -> None:
    A, B, _, _ = h.points
    w.write(f"pose proof (cn_congruencereverse {A} {B}) as Cong_{A}_{B}_{B}_{A}.\n")


def proposition_03(e: Conjunction, w: TextIO) -> None:
    BetS_E_X_F, Cong_E_X_C_D = e.hs
    E, X, F = BetS_E_X_F.points
    E, X, C, D = Cong_E_X_C_D.points
    A, B = "X", "Y"
    w.write(f"pose proof (proposition_03 {A} {B} {C} {D} {E} {F} Lt_{C}_{D}_{A}_{B} Cong_{E}_{F}_{A}_{B}) as ({X} & {e.to_var()}).\n")


def proposition_10(e: Conjunction, w: TextIO) -> None:
    BetS_A_X_B, Cong_X_A_X_B = e.hs
    A, X, B = BetS_A_X_B.points
    X, A, X, B = Cong_X_A_X_B.points
    w.write(f"pose proof (proposition_10 {A} {B} neq_{A}_{B}) as ({X} & {e.to_var()}).\n")


def proposition_15(e: Hypothesis, w: TextIO) -> None:
    A, E, C, D, E, B = e.points
    w.write(f"pose proof (proposition_15 {A} {B} {C} {D} {E} BetS_{A}_{E}_{B} BetS_{C}_{E}_{D} nCol_{A}_{E}_{C}) as ({e.to_var()} & _).\n")
    C, E, B, A, E, D = e.points
    w.write(f"pose proof (proposition_15 {A} {B} {C} {D} {E} BetS_{A}_{E}_{B} BetS_{C}_{E}_{D} nCol_{A}_{E}_{C}) as (_ & {e.to_var()}).\n")


def lemma_ABCequalsCBA(e: Hypothesis, w: TextIO):
    A, B, C, C, B, A = e.points
    w.write(f"pose proof (lemma_ABCequalsCBA {A} {B} {C} nCol_{A}_{B}_{C}) as {e.to_var()}.\n")


def lemma_angledistinct(h: Hypothesis, w: TextIO) -> None:
    A, B = h.points

    w.write("\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_{A}_{B}_Z_x_y_z) as (neq_{A}_{B} & _ & _ & _ & _ & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_X_{A}_{B}_x_y_z) as (_ & neq_{A}_{B} & _ & _ & _ & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_{A}_Y_{B}_x_y_z) as (_ & _ & neq_{A}_{B} & _ & _ & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_X_Y_Z_{A}_{B}_z) as (_ & _ & _ & neq_{A}_{B} & _ & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_X_Y_Z_x_{A}_{B}) as (_ & _ & _ & _ & neq_{A}_{B} & _).\n")
    w.write(f"pose proof (lemma_angledistinct _ _ _ _ _ _ CongA_X_Y_Z_{A}_y_{B}) as (_ & _ & _ & _ & _ & neq_{A}_{B}).\n")
    w.write("\n")


def lemma_betweennotequal(e: Hypothesis, w: TextIO):
    A, B = e.points
    w.write("\n")
    w.write(f"pose proof (lemma_betweennotequal _ _ _ BetS_X_{A}_{B}) as (neq_{A}_{B} & _ & _).\n")
    w.write(f"pose proof (lemma_betweennotequal _ _ _ BetS_{A}_{B}_Z) as (_ & neq_{A}_{B} & _).\n")
    w.write(f"pose proof (lemma_betweennotequal _ _ _ BetS_{A}_Y_{B}) as (_ & _ & neq_{A}_{B}).\n")
    w.write("\n")


def lemma_congruencetransitive(h: Hypothesis, w: TextIO) -> None:
    A, B, E, F = h.points
    w.write(f"pose proof (lemma_congruencetransitive {A} {B} X Y {E} {F} Cong_{A}_{B}_X_Y Cong_X_Y_{E}_{F}) as Cong_{A}_{B}_{E}_{F}.\n")


def lemma_extension(e: Conjunction, w: TextIO) -> None:
    BetS_A_B_X, Cong_B_X_P_Q = e.hs
    A, B, X = BetS_A_B_X.points
    B, X, P, Q = Cong_B_X_P_Q.points
    w.write(f"pose proof (lemma_extension {A} {B} {P} {Q} neq_{A}_{B} neq_{P}_{Q}) as ({X} & {e.to_var()}).\n")


def lemma_inequalitysymmetric(h: Hypothesis, w: TextIO) -> None:
    B, A = h.points
    w.write(f"pose proof (lemma_inequalitysymmetric {A} {B} neq_{A}_{B}) as neq_{B}_{A}.\n")


def lemma_angleorderrespectscongruence(e: Hypothesis, w: TextIO):
    A, B, C, a, b, c = e.points
    w.write(f"pose proof (lemma_angleorderrespectscongruence {A} {B} {C}) as {e.to_var()}.\n")


def lemma_angleorderrespectscongruence_smaller(e: Hypothesis, w: TextIO):
    a, b, c, D, E, F = e.points
    w.write(f"pose proof (lemma_angleorderrespectscongruence_smaller {a} {b} {c}) as {e.to_var()}.\n")


def lemma_collinear_ABC_ABD_BCD(e: Hypothesis, w: TextIO):
    B, C, D = e.points
    w.write(f"pose proof (lemma_collinear_ABC_ABD_BCD X {B} {C} {D} Col_X_{B}_{C} Col_X_{B}_{D} neq_X_{B}) as {e.to_var()}.\n")


def lemma_collinearorder(e: Hypothesis, w: TextIO):
    A, B, C = e.points
    w.write("\n")
    w.write(f"pose proof (lemma_collinearorder _ _ _ Col_{B}_{A}_{C}) as (Col_{A}_{B}_{C} & _ & _ & _ & _).\n")
    w.write(f"pose proof (lemma_collinearorder _ _ _ Col_{C}_{A}_{B}) as (_ & Col_{A}_{B}_{C} & _ & _ & _).\n")
    w.write(f"pose proof (lemma_collinearorder _ _ _ Col_{B}_{C}_{A}) as (_ & _ & Col_{A}_{B}_{C} & _ & _).\n")
    w.write(f"pose proof (lemma_collinearorder _ _ _ Col_{A}_{C}_{B}) as (_ & _ & _ & Col_{A}_{B}_{C} & _).\n")
    w.write(f"pose proof (lemma_collinearorder _ _ _ Col_{C}_{B}_{A}) as (_ & _ & _ & _ & Col_{A}_{B}_{C}).\n")
    w.write("\n")


def lemma_congruenceflip(e: Hypothesis, w: TextIO):
    # TODO: expansion
    A, B, C, D = e.points
    w.write(f"pose proof (lemma_congruenceflip {A} {B} {C}) as {e.to_var()}.\n")


def lemma_doublereverse(e: Hypothesis, w: TextIO):
    # TODO: expansion
    A, B, C, D = e.points
    w.write(f"pose proof (lemma_doublereverse {A} {B} {C}) as {e.to_var()}.\n")


def lemma_equalanglesNC(e: Hypothesis, w: TextIO):
    a, b, c = e.points
    w.write(f"pose proof (lemma_equalanglesNC {a} {b} {c}) as {e.to_var()}.\n")


def lemma_equalangleshelper(e: Hypothesis, w: TextIO):
    A, B, C, p, b, q = e.points
    w.write(f"pose proof (lemma_equalangleshelper {A} {B} {C}) as {e.to_var()}.\n")


def lemma_equalanglesreflexive(e: Hypothesis, w: TextIO):
    A, B, C, A, B, C = e.points
    w.write(f"pose proof (lemma_equalanglesreflexive {A} {B} {C}) as {e.to_var()}.\n")


def lemma_equalanglessymmetric(e: Hypothesis, w: TextIO):
    a, b, c, A, B, C = e.points
    w.write(f"pose proof (lemma_equalanglessymmetric {A} {B} {C}) as {e.to_var()}.\n")


# TODO: next
# pose proof (lemma_equalanglestransitive A E B) as CongA_A_E_B_C_E_F.
# pose proof (lemma_doublereverse B E F) as Cong_B_E_F_E.
# pose proof (lemma_congruenceflip E B E) as Cong_E_B_E_F.
def lemma_equalanglestransitive(e: Hypothesis, w: TextIO):
    A, B, C, P, Q, R = e.points
    w.write(f"pose proof (lemma_equalanglestransitive {A} {B} {C}) as {e.to_var()}.\n")


def lemma_onray_ABC_ACB(e: Hypothesis, w: TextIO):
    A, C, B = e.points
    w.write(f"pose proof (lemma_onray_ABC_ACB {A} {B} {C}) as {e.to_var()}.\n")


def lemma_onray_assert(e: Hypothesis, w: TextIO):
    A, B, E = e.points
    w.write(f"pose proof (lemma_onray_assert {A} {B} {E}) as {e.to_var()}.\n")


def Triangle(h: Hypothesis, w: TextIO) -> None:
    A, B, C = h.points
    if h.head == "nCol":
        w.write(f"pose proof (lemma_s_ncol_triangle {A} {B} {C} Triangle_{A}_{B}_{C}) as nCol_{A}_{B}_{C}.\n")
        w.write(f"pose proof (lemma_s_ncol_n_col {A} {B} {C} nCol_{A}_{B}_{C}) as n_Col_{A}_{B}_{C}.\n")
    elif h.head == "Triangle":
        w.write(f"pose proof (lemma_s_triangle {A} {B} {C} nCol_{A}_{B}_{C}) as Triangle_{A}_{B}_{C}.\n")
    else:
        raise ValueError(f"Expected assertion by Triangle to be either nCol or Triangle, got: {h.head}")


def Col(h: Hypothesis, w: TextIO) -> None:
    A, B, C = h.points
    if h.head != "Col":
        raise ValueError(f"Expected assertion by Triangle to be either nCol or Triangle, got: {h.head}")
    w.write("\n")
    w.write(f"pose proof (lemma_s_col_eq_A_B {A} {B} {C} eq_{A}_{B}) as Col_{A}_{B}_{C}.\n")
    w.write(f"pose proof (lemma_s_col_eq_A_C {A} {B} {C} eq_{A}_{C}) as Col_{A}_{B}_{C}.\n")
    w.write(f"pose proof (lemma_s_col_eq_B_C {A} {B} {C} eq_{B}_{C}) as Col_{A}_{B}_{C}.\n")
    w.write(f"pose proof (lemma_s_col_BetS_B_A_C {A} {B} {C} BetS_{B}_{A}_{C}) as Col_{A}_{B}_{C}.\n")
    w.write(f"pose proof (lemma_s_col_BetS_A_B_C {A} {B} {C} BetS_{A}_{B}_{C}) as Col_{A}_{B}_{C}.\n")
    w.write(f"pose proof (lemma_s_col_BetS_A_C_B {A} {B} {C} BetS_{A}_{C}_{B}) as Col_{A}_{B}_{C}.\n")
    w.write("\n")


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
        "lemma_s_ncol_n_col",
        "lemma_s_ncol_triangle",
        "lemma_s_triangle",
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
    if c.lemma_conclusion_point:
        w.write(f"\texists {c.lemma_conclusion_point}, {c.lemma_conclusion.to_str()}.\n")
    else:
        w.write(f"\t{c.lemma_conclusion.to_str()}.\n")
    w.write("Proof.\n")

    w.write(f"\tintros {' '.join(c.lemma_points)}.\n")
    for gh in c.given_hypothesises:
        w.write(f"\tintros {gh.to_var()}.\n")
    w.write(f"\n")


def print_coq(c: Coq, w: io.StringIO) -> None:
    print_coq_top(c, w)

    indent = 1
    for a in c.assertions:
        if a.by in globals():
            # TODO: Out interacts poorly with jupyter
            if a.by == "Out":
                continue
            globals()[a.by](a.e, PrefixedStringIO(w, "\t" * indent))
        else:
            w.write(a.to_str(indent=indent))

    w.write("Qed.\n\n")
    w.write("End Euclid.\n")


tree = Grammar(open("geocoq.peg").read()).parse(open("/tmp/test.v").read())

v = CoqVisitor()
t = v.visit(tree)


s = io.StringIO()
print_coq(v.coq, s)
print(s.getvalue())
