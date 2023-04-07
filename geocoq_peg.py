from typing import Any, Optional, TextIO
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor, Node
from dataclasses import dataclass
import io


@dataclass
class Hypothesis:
    head: str
    points: list[str]

    def to_str(self) -> str:
        return f"{self.head} {' '.join(self.points)}"


def h_str(h: Hypothesis):
    return f"{h.head} {' '.join(h.points)}"


def h_var(h: Hypothesis):
    return f"{h.head}_{'_'.join(h.points)}"


@dataclass
class Conjunction:
    hs: list[Hypothesis]

    def to_str(self) -> str:
        return " /\\ ".join([h.to_str() for h in self.hs])


@dataclass
class Assertion:
    h: Hypothesis
    by: str


@dataclass
class Coq:
    lemma_name: str
    lemma_points: list[str]
    given_hypothesises: list[Hypothesis]
    lemma_conclusion: Optional[Hypothesis]
    assertions: list[Assertion]


class CoqVisitor(NodeVisitor):
    def __init__(self):
        self.coq = Coq(
            lemma_name="",
            lemma_points=list(),
            given_hypothesises=list(),
            lemma_conclusion=None,
            assertions=list(),
        )

    def visit_lemma(self, node: Node, vc: list[Node]):
        self.coq.lemma_name = vc[2]

    def visit_statement_assert(self, _: Node, vc: list[Any]):
        h = vc[3]
        by = vc[6]
        self.coq.assertions.append(Assertion(h=h, by=by))

    def visit_lemma_preamble_points(self, _: Node, vc: list[Any]):
        points = vc[2]
        self.coq.lemma_points = points

    def visit_lemma_preamble_given(self, _: Node, vc: list[Any]):
        h = vc[0]
        self.coq.given_hypothesises.append(h)

    def visit_lemma_preamble_conclusion(self, _: Node, vc: list[Any]):
        h = vc[0]
        print(f"conclusion is: {h}")
        self.coq.lemma_conclusion = h

    def visit_conjunction(self, n: Node, vc: list[Any]):
        if isinstance(vc[0], Hypothesis):
            return vc[0]

        vc2 = vc[0]
        h0 = vc2[0]
        h_rest = vc2[1]
        hhs = [h0]
        for h in h_rest:
            _, _, hh = h
            hhs.append(hh)
        return Conjunction(hs=hhs)

    def visit_hypothesis(self, node: Node, vc: list[Any]):
        return Hypothesis(head=vc[0], points=vc[1])

    def visit_qualified_id(self, _: Node, vc: list[Any]):
        path = [c for _, c in vc]
        return path

    def visit_point(self, node: Node, _: list[Any]):
        n = node.children[0].text
        return n

    def visit_id(self, node: Node, _: list[Any]):
        n = node.children[0].text
        return n

    def generic_visit(self, node, vc):
        """The generic visit method."""
        return vc or node


tree = Grammar(open("geocoq.peg").read()).parse(
    open(
        "/home/blin/src/github.com/GeoCoq/GeoCoq/Elements/OriginalProofs/lemma_congruenceflip.v"
    ).read()
)

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
    w.write(f"\t{c.lemma_conclusion.to_str()}.\n")
    w.write("Proof.\n")

    w.write(f"\tintros {' '.join(c.lemma_points)}\n")
    for gh in c.given_hypothesises:
        w.write(f"\tintros {h_var(gh)}.\n")
    w.write(f"\n")


def cn_congruencereflexive(h: Hypothesis, w: TextIO) -> None:
    assert h.points[0] == h.points[2]
    assert h.points[1] == h.points[3]
    w.write(
        f"\tpose proof (cn_congruencereflexive {h.points[0]} {h.points[1]}) as {h_var(h)}.\n"
    )


def cn_congruencetransitive(h: Hypothesis, w: TextIO) -> None:
    C, D, E, F = h.points
    w.write(
        f"\tpose proof (cn_congruencetransitive X Y {C} {D} {E} {F} Cong_X_Y_{C}_{D} Cong_X_Y_{E}_{F}) as Cong_{C}_{D}_{E}_{F}.\n"
    )


def lemma_congruencesymmetric(h: Hypothesis, w: TextIO) -> None:
    C, D, A, B = h.points
    w.write(
        f"\tpose proof (lemma_congruencesymmetric {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as Cong_{C}_{D}_{A}_{B}.\n"
    )


def cn_equalityreverse(h: Hypothesis, w: TextIO) -> None:
    A, B, _, _ = h.points
    w.write(f"\tpose proof (cn_congruencereverse {A} {B}) as Cong_{A}_{B}_{B}_{A}.\n")


def lemma_congruencetransitive(h: Hypothesis, w: TextIO) -> None:
    A, B, E, F = h.points
    w.write(
        f"\tpose proof (lemma_congruencetransitive {A} {B} X Y {E} {F} Cong_{A}_{B}_X_Y Cong_X_Y_{E}_{F}) as Cong_{A}_{B}_{E}_{F}.\n"
    )


def print_coq(c: Coq, w: TextIO) -> None:
    print_coq_top(c, w)

    for a in c.assertions:
        if a.by in globals():
            globals()[a.by](a.h, w)
        else:
            w.write(f"\tpose proof ({a.by}) as {h_var(a.h)}.\n")

    w.write("Qed.\n\n")
    w.write("End Euclid.\n")


s = io.StringIO()
print_coq(v.coq, s)
print(s.getvalue())
