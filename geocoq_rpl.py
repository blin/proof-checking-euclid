import json
from typing import Any, Union, get_args
from typing_extensions import NotRequired, TypedDict
from pprint import pprint
from dataclasses import dataclass


class Node(TypedDict):
    type: str
    s: int
    e: int
    data: str
    subs: NotRequired[list["Node"]]


@dataclass
class PropSimple:
    head: str
    points: list[str]


@dataclass
class PropInversion:
    p: "Prop"


@dataclass
class PropConjunction:
    left: "Prop"
    right: "Prop"


@dataclass
class PropDisjunction:
    left: "Prop"
    right: "Prop"


Prop = Union[PropSimple, PropInversion, PropConjunction, PropDisjunction]


@dataclass
class LtacUnneeded:
    data: str


@dataclass
class LtacConclude:
    t: str
    n: str


@dataclass
class LtacAssert:
    prop: Prop


@dataclass
class LtacAssertBy:
    prop: Prop
    by: LtacConclude


@dataclass
class LtacAssertContradiction:
    prop: PropInversion
    by: list["Assert"]


Assert = Union[LtacAssertBy, LtacAssertContradiction]


@dataclass
class Command:
    data: str


@dataclass
class Require:
    qid: list[str]


@dataclass
class Lemma:
    name: str
    points: list[str]
    given: list[Prop]
    conclusion: Prop
    asserts: list[Assert]


@dataclass
class Section:
    lemmas: list[Lemma]


@dataclass
class Top:
    requires: list[Require]
    lemmas: list[Lemma]


class NodeVisitor:
    def visit(self, node: Node):
        t = node["type"].replace(".", "_")

        method = getattr(self, f"visit_{t}", self.generic_visit)

        subs = node["subs"] if "subs" in node else list()

        return method(node, [self.visit(n) for n in subs])

    def generic_visit(self, node: Node, vc: list[Any]):
        if vc:
            return (node["type"], vc)
        return node

    def visit_id(self, node: Node, vc: list[Any]):
        return node["data"]

    def visit_qualified_id(self, node: Node, vc: list[Any]):
        return vc

    def visit_point(self, node: Node, vc: list[Any]):
        return node["data"].rstrip()

    def visit_points(self, node: Node, vc: list[Any]):
        return vc

    def visit_prop(self, node: Node, vc: list[Any]):
        if len(vc) != 1:
            raise ValueError(f"prop all with braces: {node}")
        return vc[0]

    def visit_prop_all(self, node: Node, vc: list[Any]):
        return vc[0]

    def visit_prop_simple(self, node: Node, vc: list[Any]):
        return PropSimple(head=vc[0], points=vc[1])

    def visit_prop_inversion(self, node: Node, vc: list[Any]):
        return PropInversion(p=vc[0])

    def visit_ltac_expr(self, node: Node, vc: list[Any]):
        if len(vc) != 2:
            raise ValueError(f"ltac_expr with braces: {node}")
        return vc[1]

    def visit_ltac_expr_ltac_expr4(self, node: Node, vc: list[Any]):
        head = vc[0]
        if len(vc) != 1:
            assert isinstance(head, get_args(Assert)), f"ltac_expr4 head is not an assert: {head}"
            assert all([isinstance(e, LtacUnneeded) for e in vc[1:]]), f"ltac_expr4 with needed statements: {vc[1:]}"
        return vc[0]

    def visit_ltac_expr_ltac_expr1(self, node: Node, vc: list[Any]):
        tactic_name = vc[0]
        if tactic_name == "assert":
            assert len(vc) in [4, 2], f"assert different form: {node}"
            prop = vc[1]
            assert isinstance(prop, get_args(Prop)), f"assert with unknown prop: {prop}"
            if len(vc) == 2:
                return LtacAssert(prop=prop)
            by = vc[3]
            assert isinstance(by, LtacConclude), f"assert with unknown by: {by}"
            return LtacAssertBy(prop=prop, by=by)
        if tactic_name in {"conclude", "conclude_def", "forward_using"}:
            assert len(vc) == 2, f"unexpected conclude form: {node}"
            return LtacConclude(t=tactic_name, n=vc[1])
        return LtacUnneeded(data=node["data"])

    def visit_ltac_expr_tactic_name(self, node: Node, vc: list[Any]):
        return node["data"]

    def visit_ltac_expr_tactic_arg(self, node: Node, vc: list[Any]):
        return vc[0]

    def visit_ltac_expr_ltac_intro(self, node: Node, vc: list[Any]):
        return None

    def visit_command(self, node: Node, vc: list[Any]):
        return Command(data=node["data"])

    def visit_sentence(self, node: Node, vc: list[Any]):
        return vc[0]

    def visit_lemma_compound(self, node: Node, vc: list[Any]):
        return vc[0]

    def visit_lemma_compound_assert_contradiction(self, node: Node, vc: list[Any]):
        top_assert = vc[0]
        assert isinstance(top_assert, LtacAssert)
        assert isinstance(top_assert.prop, PropInversion)

        asserts = [e for e in vc[1:] if isinstance(e, get_args(Assert))]

        return LtacAssertContradiction(prop=top_assert.prop, by=asserts)

    def visit_require(self, node: Node, vc: list[Any]):
        return Require(qid=vc[0])

    def visit_section(self, node: Node, vc: list[Any]):
        lemmas = vc[2:-1]
        assert all(isinstance(l, Lemma) for l in lemmas)
        return Section(lemmas=lemmas)

    def visit_lemma_preamble_given(self, node: Node, vc: list[Any]):
        return vc[0]

    def visit_lemma_preamble_conclusion(self, node: Node, vc: list[Any]):
        return vc[0]

    def visit_lemma_preamble_points(self, node: Node, vc: list[Any]):
        return vc[0]

    def visit_lemma_intro(self, node: Node, vc: list[Any]):
        name = vc[0]
        preamble = vc[1][1]
        points = preamble[0]
        given = preamble[1:-1]
        conclusion = preamble[-1]
        assert all(isinstance(p, get_args(Prop)) for p in given)
        assert isinstance(conclusion, get_args(Prop)), f"intro conclusion is not a prop: {conclusion}"

        return (name, points, given, conclusion)

    def visit_lemma(self, node: Node, vc: list[Any]):
        name, points, given, conclusion = vc[0]
        asserts = [e for e in vc[1:-1] if isinstance(e, get_args(Assert))]
        return Lemma(name=name, points=points, given=given, conclusion=conclusion, asserts=asserts)

    def visit_top(self, node: Node, vc: list[Any]):
        requires = [e for e in vc if isinstance(e, Require)]
        sections = [e for e in vc if isinstance(e, Section)]
        assert len(sections) == 1
        return Top(requires=requires, lemmas=sections[0].lemmas)

    def visit_prop_conjunction(self, node: Node, vc: list[Any]):
        return PropConjunction(left=vc[0], right=vc[1])

    def visit_prop_disjunction(self, node: Node, vc: list[Any]):
        return PropDisjunction(left=vc[0], right=vc[1])

    def visit_exists_prop(self, node: Node, vc: list[Any]):
        return PropConjunction(left=vc[0], right=vc[1])


def process_parse_tree(parse_tree: Node) -> Top:
    return NodeVisitor().visit(parse_tree["subs"][0])


bad_path = "proposition_23"
bad_path2 = f"build/{bad_path}_parse_tree.json"
pprint(process_parse_tree(json.load(open(bad_path2))))
