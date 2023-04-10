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
                w.write("\t" * indent)
                globals()[a.by](a.e, w)
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
        return (
            "\t" * indent + f"pose proof ({self.by}) as ({ps} & {self.e.to_var()}).\n"
        )


@dataclass
class Coq:
    lemma_name: str
    lemma_points: list[str]
    given_hypothesises: list[Expression]
    lemma_conclusion: Optional[Expression]
    lemma_conclusion_point: Optional[str]
    assertions: list[Assertion]


class CoqVisitor(NodeVisitor):
    def __init__(self):
        self.coq = Coq(
            lemma_name="",
            lemma_points=list(),
            given_hypothesises=list(),
            lemma_conclusion=None,
            lemma_conclusion_point=None,
            assertions=list(),
        )

    def visit_lemma(self, node: Node, vc: list[Node]):
        lemma_intro = vc[0]
        self.coq.lemma_name = lemma_intro[2]

        lemma_statements = [
            s[0] for s in vc[1] if not isinstance(s[0], UnneededStatement)
        ]
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


tree = Grammar(open("geocoq.peg").read()).parse(open("/tmp/test.v").read())

v = CoqVisitor()
t = v.visit(tree)


def print_coq_top(c: Coq, w: TextIO) -> None:
    w.write("Section Euclid.\n\n")
    w.write("Context `{Ax:euclidean_neutral}.\n\n")
    w.write(f"Lemma {c.lemma_name} :\n")
    w.write(f"\tforall {' '.join(c.lemma_points)},\n")
    for gh in c.given_hypothesises:
        w.write(f"\t{gh.to_str()} ->\n")
    if c.lemma_conclusion is None:
        raise ValueError("expected lemma to have conclusion")
    if c.lemma_conclusion_point:
        w.write(
            f"\texists {c.lemma_conclusion_point}, {c.lemma_conclusion.to_str()}.\n"
        )
    else:
        w.write(f"\t{c.lemma_conclusion.to_str()}.\n")
    w.write("Proof.\n")

    w.write(f"\tintros {' '.join(c.lemma_points)}\n")
    for gh in c.given_hypothesises:
        w.write(f"\tintros {gh.to_var()}.\n")
    w.write(f"\n")


def cn_congruencereflexive(h: Hypothesis, w: TextIO) -> None:
    A, B, _, _ = h.points
    w.write(f"pose proof (cn_congruencereflexive {A} {B}) as Cong_{A}_{B}_{A}_{B}.\n")


def cn_congruencetransitive(h: Hypothesis, w: TextIO) -> None:
    C, D, E, F = h.points
    w.write(
        f"pose proof (cn_congruencetransitive X Y {C} {D} {E} {F} Cong_X_Y_{C}_{D} Cong_X_Y_{E}_{F}) as Cong_{C}_{D}_{E}_{F}.\n"
    )


def lemma_congruencesymmetric(h: Hypothesis, w: TextIO) -> None:
    C, D, A, B = h.points
    w.write(
        f"pose proof (lemma_congruencesymmetric {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as Cong_{C}_{D}_{A}_{B}.\n"
    )


def cn_equalityreverse(h: Hypothesis, w: TextIO) -> None:
    A, B, _, _ = h.points
    w.write(f"pose proof (cn_congruencereverse {A} {B}) as Cong_{A}_{B}_{B}_{A}.\n")


def lemma_congruencetransitive(h: Hypothesis, w: TextIO) -> None:
    A, B, E, F = h.points
    w.write(
        f"pose proof (lemma_congruencetransitive {A} {B} X Y {E} {F} Cong_{A}_{B}_X_Y Cong_X_Y_{E}_{F}) as Cong_{A}_{B}_{E}_{F}.\n"
    )


def print_coq(c: Coq, w: TextIO) -> None:
    print_coq_top(c, w)

    indent = 1
    for a in c.assertions:
        if a.by in globals():
            # TODO: Out interacts poorly with jupyter
            if a.by == "Out":
                continue
            w.write("\t" * indent)
            globals()[a.by](a.e, w)
        else:
            w.write(a.to_str(indent=indent))

    w.write("Qed.\n\n")
    w.write("End Euclid.\n")


s = io.StringIO()
print_coq(v.coq, s)
print(s.getvalue())
