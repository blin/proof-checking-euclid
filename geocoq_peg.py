from typing import Any, Optional
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor, Node
from dataclasses import dataclass, asdict
import json

tree = Grammar(open("geocoq.peg").read()).parse(
    open(
        "/home/blin/src/github.com/GeoCoq/GeoCoq/Elements/OriginalProofs/lemma_congruencesymmetric.v"
    ).read()
)


@dataclass
class Hypothesis:
    head: str
    points: list[str]


@dataclass
class Assertion:
    hypothesis: Hypothesis
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
        self.coq.assertions.append(Assertion(hypothesis=h, by=by))

    def visit_lemma_preamble_points(self, _: Node, vc: list[Any]):
        points = vc[2]
        self.coq.lemma_points = points

    def visit_lemma_preamble_given(self, _: Node, vc: list[Any]):
        h = vc[0]
        self.coq.given_hypothesises.append(h)

    def visit_lemma_preamble_conclusion(self, _: Node, vc: list[Any]):
        h = vc[0]
        self.coq.lemma_conclusion = h

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


v = CoqVisitor()
t = v.visit(tree)
json.dumps(asdict(v.coq))
