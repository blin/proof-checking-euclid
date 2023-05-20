import io
import itertools
import json
from pprint import pprint
from typing import TextIO, Tuple, Union

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
    parse_all_lemmas,
    process_parse_tree,
)

from pyswip import Functor, Variable, Query, call, Prolog, PL_term_type
from pyswip.easy import getList, Functor, getString


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
        # TODO: hacky :(
        if p in self.get_props():
            return
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
        self.w.write(f"\t{self.l.conclusion.to_str()}.\n")

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
        match a.by.n:
            case "cn_equalityreflexive":
                # TODO reflixivity
                self.context.add_prop(a.prop)
                return
            case "axiom_betweennesssymmetry":
                self.context.add_prop(a.prop)
                return
            case "cn_congruencereflexive":
                self.context.add_prop(a.prop)
                return
        proof_lemma = self.lemmas_by_name[a.by.n]
        proof_points = " ".join(["_"] * len(proof_lemma.points))
        proof_props = " ".join([p.to_var() for p in proof_lemma.given])
        proof = f"{proof_lemma.name} {proof_points} {proof_props}"
        match a.prop:
            case PropSimple():
                proof = prove_simple(a.prop, proof_lemma, self.context.get_props())
                self.context.add_prop(a.prop)
            case PropInversion():
                prove_inversion(a.prop, proof_lemma, self.context.get_props())
                self.context.add_prop(a.prop)
            case PropConjunction():
                # lemma_extension
                # TODO: need to recurse, maybe recurse in add_prop?
                self.context.add_prop(a.prop.left)
                self.context.add_prop(a.prop.right)
        self.w.write(f"pose proof ({proof}) as {a.prop.to_var()}.\n")

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
        match a.prop.p.head:
            case "eq":
                self.context.add_prop(PropSimple(head="neq", points=a.prop.p.points))
            case "Col":
                self.context.add_prop(PropSimple(head="nCol", points=a.prop.p.points))
            case _:
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


def prove_inversion(p: PropInversion, by: Lemma, context: list[Prop]) -> list[Prop]:
    pass
    # print(f"trying to prove inverseion {p} using {by.name}")
    # pprint(context)


def prolog_prop(p: Prop) -> str:
    match p:
        case PropSimple():
            ps = ",".join([f'"{pt}"' for pt in p.points])
            return f'prop("{p.head}",[{ps}])'
        case PropInversion():
            ps = ",".join([f'"{pt}"' for pt in p.p.points])
            return f'prop("n_{p.p.head}",[{ps}])'
        case PropConjunction():
            raise ValueError(f"what: {p}")


def prove_simple(p: PropSimple, by: Lemma, context: list[Prop]) -> list[Prop]:
    prolog = Prolog()
    prolog.consult("/tmp/lemmas.pl")

    with open("/tmp/context.pl", "w") as cf:
        for cp in context:
            cf.write(prolog_prop(cp))
            cf.write(".\n")
    prolog.consult("/tmp/context.pl")

    pq_given = ",".join([f"G{i+1}" for i in range(len(by.given))])
    pq_args = f"{pq_given},{prolog_prop(p)}"
    q = f"{by.name}({pq_args})"

    answers = list(prolog.query(q, normalize=False))
    if len(answers) != 1:
        if by.name == "lemma_onray_assert":
            # TODO: :(
            return "lemma_onray_assert ???"
        pprint(q)
        pprint(answers)
        pprint(context)
    assert len(answers) == 1
    answer = answers[0]
    answer_vars: list[Tuple[str, PropSimple]] = list()
    for f in answer:
        assert isinstance(f, Functor)
        assert f.name.get_value() == "="
        var_name = f.args[0].get_value()
        prop = f.args[1]

        assert isinstance(prop, Functor)
        assert prop.name.get_value() == "prop"

        prop_name = prop.args[0].decode("utf-8")
        points_raw = prop.args[1]
        assert isinstance(points_raw, list)
        points = [p.decode("utf-8") for p in points_raw]
        answer_vars.append((var_name, PropSimple(head=prop_name, points=points)))
    pp = " ".join(["_" for i in range(len(by.points))])
    gg = " ".join([e[1].to_var() for e in answer_vars])
    return f"{by.name} {pp} {gg}"


bad_path = "proposition_20"
bad_path2 = f"build/{bad_path}_parse_tree.json"
top = process_parse_tree(json.load(open(bad_path2)))

lemmas_by_name = parse_all_lemmas()


# lemma_angleorderrespectscongruence(G1,G2,C1) :-
# G1 = prop(G1H,G1P),
# prop(G1H,G1P),
# G1H = "LtA",
# G1P = [P1,P2,P3,P4,P5,P6],
# G2 = prop(G2H,G2P),
# prop(G2H,G2P),
# G2H = "CongA",
# G2P = [P7,P8,P9,P4,P5,P6],
# C1 = prop(C1H,C1P),
# C1H = "LtA",
# C1P = [P1,P2,P3,P7,P8,P9].
def prolog_lemma_rule(p: Prop, idp: str, p_to_i: dict[str, int]) -> str:
    r = io.StringIO()
    conclusion = idp[0] == "C"
    r.write(f"{idp} = prop({idp}H,{idp}P),\n")
    if not conclusion:
        r.write(f"prop({idp}H,{idp}P),\n")

    points = []
    match p:
        case PropSimple():
            r.write(f'{idp}H = "{p.head}",\n')
            points = p.points

        case PropInversion():
            r.write(f'{idp}H = "n_{p.p.head}",\n')
            points = p.p.points
    i = max(itertools.chain([0], p_to_i.values())) + 1
    for p in points:
        if p in p_to_i:
            continue
        p_to_i[p] = i
        i += 1
    ps = [f"P{p_to_i[p]}" for p in points]
    pss = ",".join(ps)
    r.write(f"{idp}P = [{pss}]")
    r.write("." if conclusion else ",")
    r.write("\n")

    return r.getvalue()


req_names = extract_requirements_top(top) - {
    "Triangle",
    "isosceles",
    "Col",
    "CongA",
    "LtA",
    "TG",
    "cn_congruencereflexive",
    "cn_equalityreflexive",
    "axiom_betweennesssymmetry",
}
req_names

rr = open("/tmp/lemmas.pl", "w")
for req_name in sorted(req_names):
    req = lemmas_by_name[req_name]
    r = io.StringIO()
    q = ",".join([f"G{i+1}" for i in range(len(req.given))] + ["C1"])
    r.write(f"{req_name}({q}) :-\n")
    p_to_i = dict()
    for i, p in enumerate(req.given):
        r.write(prolog_lemma_rule(p, f"G{i+1}", p_to_i))
    r.write(prolog_lemma_rule(req.conclusion, f"C1", p_to_i))
    rr.write(r.getvalue())
    rr.write("\n")
rr.close()
# TODO: prolog for conjunctions
# lemma_NCorder(G1,C1) :-
# lemma_angledistinct(G1,C1) :-

lemmas_by_name["lemma_angleorderrespectscongruence"].conclusion

s = io.StringIO()
print_top(s, top)
for l in top.lemmas:
    LemmaPrinter(l=l, w=s, lemmas_by_name=lemmas_by_name).process()
s.write("End Euclid.\n")
print(s.getvalue())
