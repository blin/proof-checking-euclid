import glob
import io
import itertools
import json
from pprint import pprint
from typing import TextIO, Union

from geocoq_rpl import (
    Assert,
    Lemma,
    LtacAssertBy,
    LtacAssertByCases,
    LtacAssertContradiction,
    Prop,
    PropSimple,
    PropInversion,
    PropConjunction,
    PropDisjunction,
    Top,
    process_parse_tree,
)


def process_all():
    parse_tree_paths = sorted(glob.glob("build/*_parse_tree.json"))

    ls: dict[str, Lemma] = dict()
    for p in parse_tree_paths:
        print(p)
        t = process_parse_tree(json.load(open(p)))
        for l in t.lemmas:
            ls[l.name] = l
    return ls


lemmas_by_name = process_all()


def extract_requirements_assert(a: Assert) -> set[str]:
    requirements = set()
    # TODO: use match
    if isinstance(a, LtacAssertBy):
        requirements.add(a.by.n)
    elif isinstance(a, LtacAssertContradiction):
        for aa in a.by:
            requirements.update(extract_requirements_assert(aa))
    elif isinstance(a, LtacAssertByCases):
        for case in a.cases:
            for aa in case.asserts:
                requirements.update(extract_requirements_assert(aa))

    return requirements


def extract_requirements_lemma(l: Lemma) -> set[str]:
    return set().union(*[extract_requirements_assert(a) for a in l.asserts])


def extract_requirements_top(t: Top) -> set[str]:
    return set().union(*[extract_requirements_lemma(l) for l in t.lemmas])


def print_requirements(w: TextIO, t: Top) -> None:
    rs = extract_requirements_top(top)
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


def print_top(w: TextIO, t: Top) -> None:
    print_requirements(w, top)
    w.write("Section Euclid.\n\n")
    w.write("Context `{Ax:euclidean_neutral_ruler_compass}.\n\n")


class LemmaContext:
    def __init__(self):
        self.scopes: list[list[Prop]] = list()

    def push_scope(self) -> None:
        self.scopes.append([])

    def pop_scope(self) -> None:
        self.scopes.pop()

    def add_prop(self, p: Prop) -> None:
        self.scopes[-1].append(p)

    def get_props(self) -> list[Prop]:
        return list(itertools.chain(*self.scopes))


class LemmaPrinter:
    def __init__(self, l: Lemma, w: TextIO, lemmas_by_name: dict[str, Lemma]):
        self.l = l
        self.indent = 1
        self.w = w
        self.lemmas_by_name = lemmas_by_name
        self.context = LemmaContext()

    def process_indent(self) -> None:
        self.w.write("\t" * self.indent)

    def process_preamble(self) -> None:
        self.w.write(f"Lemma {self.l.name} :\n")
        self.w.write(f"\tforall {' '.join(self.l.points)},\n")
        for p in self.l.given:
            self.w.write(f"\t{p.to_str()} ->\n")
        self.w.write(f"\t{p.to_str()}.\n")

        self.w.write("Proof.\n")

        self.w.write(f"\tintros {' '.join(self.l.points)}.\n")

        self.context.push_scope()
        for p in self.l.given:
            self.w.write(f"\tintros {p.to_var()}.\n")
            self.context.add_prop(p)
        self.w.write("\n")

    def assert_by(self, a: LtacAssertBy) -> None:
        self.process_indent()
        if a.by.t in {
            "conclude_def",
            "forward_using",
        }:
            # forward_using is used for conjunctions?
            # TODO: Triangle
            self.w.write(f"pose proof ({a.by.n}) as {a.prop.to_var()}.\n")
            self.context.add_prop(a.prop)
            return

        assert a.by.t in {
            "conclude",
        }
        proof_lemma = self.lemmas_by_name[a.by.n]
        proof_points = " ".join(["_"] * len(proof_lemma.points))
        proof_props = " ".join([p.to_var() for p in proof_lemma.given])
        proof = f"{proof_lemma.name} {proof_points} {proof_props}"
        match a.prop:
            case PropSimple():
                prove_simple(a.prop, proof_lemma, self.context.get_props())
            case PropInversion():
                prove_inversion(a.prop, proof_lemma, self.context.get_props())
            case other:
                raise ValueError(f"did not expect conclude for {other}")
        self.w.write(f"pose proof ({proof}) as {a.prop.to_var()}.\n")

        self.context.add_prop(a.prop)

    def assert_contradiction(self, a: LtacAssertContradiction) -> None:
        self.context.push_scope()

        # TODO: move assertion into the type
        prop = a.prop
        by = a.by
        assert isinstance(prop, PropInversion)
        self.w.write("\n")
        self.process_indent()
        self.w.write(f"assert ({prop.to_str()}) as {prop.to_var()}.\n")
        self.process_indent()
        self.w.write("{\n")
        self.indent += 1
        self.process_indent()
        self.w.write(f"intro {prop.p.to_var()}.")
        self.context.add_prop(prop.p)
        self.w.write("\n")
        for aa in by:
            self.process_assert(aa)

        self.indent -= 1
        self.process_indent()
        self.w.write("}\n")
        self.w.write("\n")

        self.context.pop_scope()
        self.context.add_prop(a.prop)

    def process_assert(self, a: Assert) -> None:
        match a:
            case LtacAssertBy():
                self.assert_by(a)
            case LtacAssertContradiction():
                self.assert_contradiction(a)

    def process(self) -> None:
        self.process_preamble()

        for a in l.asserts:
            self.process_assert(a)

        self.w.write("Qed.\n")


def prove_simple(p: PropSimple, by: Lemma, context: list[Prop]) -> list[Prop]:
    print(f"trying to prove simple {p} using {by.name}")
    pprint(context)


def prove_inversion(p: PropInversion, by: Lemma, context: list[Prop]) -> list[Prop]:
    print(f"trying to prove inverseion {p} using {by.name}")
    pprint(context)


bad_path = "proposition_19"
bad_path2 = f"build/{bad_path}_parse_tree.json"
top = process_parse_tree(json.load(open(bad_path2)))

s = io.StringIO()
print_top(s, top)
for l in top.lemmas:
    LemmaPrinter(l=l, w=s, lemmas_by_name=lemmas_by_name).process()
s.write("End Euclid.\n")
# print(s.getvalue())
