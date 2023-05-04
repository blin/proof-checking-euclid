import json
from typing import Any, Union
from typing_extensions import NotRequired, TypedDict
from pprint import pprint
from dataclasses import dataclass

parse_tree = json.load(open("/tmp/proposition_19_parse_tree.json"))


class Node(TypedDict):
    type: str
    s: int
    e: int
    data: str
    subs: NotRequired[list["Node"]]


@dataclass
class PropSimpile:
    head: str
    points: list[str]


@dataclass
class PropInversion:
    p: "Prop"


Prop = Union[PropSimpile, PropInversion]


@dataclass
class LemmaStatementUnneeded:
    data: str


class NodeVisitor:
    def visit(self, node: Node):
        t = node["type"].replace(".", "_")

        method = getattr(self, f"visit_{t}", self.generic_visit)

        subs = node["subs"] if "subs" in node else list()

        return method(node, [self.visit(n) for n in subs])

    def generic_visit(self, node: Node, vc: list[Any]):
        print(node["type"])
        if vc:
            return (node["type"], vc)
        return node

    def visit_id(self, node: Node, vc: list[Any]):
        return node["data"]

    def visit_qualified_id(self, node: Node, vc: list[Any]):
        return vc

    def visit_point(self, node: Node, vc: list[Any]):
        return node["data"]

    def visit_prop(self, node: Node, vc: list[Any]):
        if len(vc) != 1:
            raise ValueError(f"prop all with braces: {node}")
        return vc[0]

    def visit_prop_all(self, node: Node, vc: list[Any]):
        return vc[0]

    def visit_prop_simple(self, node: Node, vc: list[Any]):
        return PropSimpile(head=vc[0], points=vc[1:])

    def visit_prop_inversion(self, node: Node, vc: list[Any]):
        return PropInversion(p=vc[0])

    def visit_lemma_statement(self, node: Node, vc: list[Any]):
        print("lemma_statement node:", node)
        print("lemma_statement vc:", vc)
        return vc

    def visit_lemma_statement_unneeded(self, node: Node, vc: list[Any]):
        return LemmaStatementUnneeded(data=node["data"])


a = NodeVisitor().visit(parse_tree["subs"][0])
