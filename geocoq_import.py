import io
import itertools
import json
from pprint import pprint
import sys
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
    rs = extract_requirements_top(t)
    rs |= {
        "euclidean_axioms",
        "euclidean_defs",
        "euclidean_tactics",
        "lemma_NCdistinct",
        "lemma_NCorder",
        "lemma_s_col_BetS_A_B_C",
        "lemma_s_col_BetS_A_C_B",
        "lemma_s_col_BetS_B_A_C",
        "lemma_s_col_eq_A_B",
        "lemma_s_col_eq_A_C",
        "lemma_s_col_eq_B_C",
        "lemma_s_isosceles",
        "lemma_s_lt",
        "lemma_s_lta",
        "lemma_s_n_col_ncol",
        "lemma_s_ncol_n_col",
        "lemma_s_ncol_triangle",
        "lemma_s_onray_assert_ABB",
        "lemma_s_onray_assert_bets_ABE",
        "lemma_s_onray_assert_bets_AEB",
        "lemma_s_triangle",
    }
    for r in sorted(rs):
        if any([r.startswith(p) for p in ["cn_", "axiom_", "postulate_"]]):
            continue
        if not any([r.startswith(p) for p in ["lemma_", "proposition_", "euclidean_"]]):
            continue
        w.write(f"Require Import ProofCheckingEuclid.{r}.\n")
    w.write("\n")


def print_top(w: TextIO, t: Top) -> None:
    print_requirements(w, t)
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
        match p:
            case PropConjunction(left, right) | PropDisjunction(left, right):
                self.add_prop(left)
                self.add_prop(right)
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

    def assert_by_conclude_def_Col(self, a: LtacAssertBy) -> None:
        e = a.prop
        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]
        hhs_eq = [h for h in hhs if h.head == "eq"]
        hhs_bets = [h for h in hhs if h.head == "BetS"]

        A, B, C = e.points
        for hh in hhs_eq:
            if not (set(hh.points) <= set(e.points)):
                continue
            X, Y = hh.points
            if [X, Y] == [A, B]:
                self.w.write(f"pose proof (lemma_s_col_eq_A_B {A} {B} {C} eq_{A}_{B}) as Col_{A}_{B}_{C}.\n")
                break
            elif [X, Y] == [A, C]:
                self.w.write(f"pose proof (lemma_s_col_eq_A_C {A} {B} {C} eq_{A}_{C}) as Col_{A}_{B}_{C}.\n")
                break
            elif [X, Y] == [B, C]:
                self.w.write(f"pose proof (lemma_s_col_eq_B_C {A} {B} {C} eq_{B}_{C}) as Col_{A}_{B}_{C}.\n")
                break
        for hh in hhs_bets:
            if set(e.points) != set(hh.points):
                continue
            X, Y, Z = hh.points
            if [X, Y, Z] == [B, A, C]:
                self.w.write(f"pose proof (lemma_s_col_BetS_B_A_C {A} {B} {C} BetS_{B}_{A}_{C}) as Col_{A}_{B}_{C}.\n")
                break
            elif [X, Y, Z] == [A, B, C]:
                self.w.write(f"pose proof (lemma_s_col_BetS_A_B_C {A} {B} {C} BetS_{A}_{B}_{C}) as Col_{A}_{B}_{C}.\n")
                break
            elif [X, Y, Z] == [A, C, B]:
                self.w.write(f"pose proof (lemma_s_col_BetS_A_C_B {A} {B} {C} BetS_{A}_{C}_{B}) as Col_{A}_{B}_{C}.\n")
                break

    def assert_by_conclude_def_destruct(self, a: LtacAssertBy) -> None:
        e = a.prop
        assert isinstance(e, PropConjunction)
        self.w.write(f"destruct {a.by.n} as (X & {a.prop.to_var()}).\n")

    def assert_by_conclude_def_Lt(self, a: LtacAssertBy) -> None:
        assert isinstance(a.prop, PropSimple)
        A, B, C, D = a.prop.points
        X = "X"
        self.w.write(f"pose proof (lemma_s_lt _ _ _ _ _ BetS_{C}_{X}_{D} Cong_{C}_{X}_{A}_{B}) as {a.prop.to_var()}.\n")

    def assert_by_conclude_def(self, a: LtacAssertBy) -> None:
        if isinstance(a.prop, PropConjunction):
            self.assert_by_conclude_def_destruct(a)
            return

        match a.by.n:
            case "Triangle":
                A, B, C = a.prop.points
                match a.prop.head:
                    case "nCol":
                        self.w.write(f"pose proof (lemma_s_ncol_triangle _ _ _ Triangle_{A}_{B}_{C}) as nCol_{A}_{B}_{C}.\n")
                    case "Triangle":
                        self.w.write(f"pose proof (lemma_s_triangle _ _ _ nCol_{A}_{B}_{C}) as Triangle_{A}_{B}_{C}.\n")
            case "Col":
                self.assert_by_conclude_def_Col(a)
            case "Lt":
                self.assert_by_conclude_def_Lt(a)
            case _:
                self.w.write(f"pose proof ({a.by.n}) as {a.prop.to_var()}. (* conclude_def *)\n")

    def assert_by_forward_using_lemma_betweennotequal(self, a: LtacAssertBy) -> None:
        e = a.prop
        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]
        hhs = [h for h in hhs if h.head == "BetS"]

        A, B = e.points
        for hh in hhs:
            if not (set(e.points) <= set(hh.points)):
                continue
            X, Y, Z = hh.points
            if [A, B] == [Y, Z]:
                self.w.write(f"pose proof (lemma_betweennotequal _ _ _ BetS_{X}_{Y}_{Z}) as (neq_{Y}_{Z} & _ & _).\n")
                break
            elif [A, B] == [X, Y]:
                self.w.write(f"pose proof (lemma_betweennotequal _ _ _ BetS_{X}_{Y}_{Z}) as (_ & neq_{X}_{Y} & _).\n")
                break
            elif [A, B] == [X, Z]:
                self.w.write(f"pose proof (lemma_betweennotequal _ _ _ BetS_{X}_{Y}_{Z}) as (_ & _ & neq_{X}_{Z}).\n")
                break

    def assert_by_forward_using_lemma_collinearorder(self, a: LtacAssertBy) -> None:
        e = a.prop
        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]
        hhs = [h for h in hhs if h.head == "Col"]

        for col in hhs:
            if set(e.points) != set(col.points):
                continue
            X, Y, Z = col.points
            self.w.write(
                f"pose proof (lemma_collinearorder _ _ _ Col_{X}_{Y}_{Z}) as (Col_{Y}_{X}_{Z} & Col_{Y}_{Z}_{X} & Col_{Z}_{X}_{Y} & Col_{X}_{Z}_{Y} & Col_{Z}_{Y}_{X}).\n"
            )
            break

    def assert_by_forward_using_lemma_congruenceflip(self, a: LtacAssertBy):
        e = a.prop
        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]

        self.w.write("\n")
        B, A, D, C = e.points
        self.w.write(f"pose proof (lemma_congruenceflip {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as ({e.to_var()} & _ & _).\n")
        B, A, C, D = e.points
        self.w.write(f"pose proof (lemma_congruenceflip {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as (_ & {e.to_var()} & _).\n")
        A, B, D, C = e.points
        self.w.write(f"pose proof (lemma_congruenceflip {A} {B} {C} {D} Cong_{A}_{B}_{C}_{D}) as (_ & _ & {e.to_var()}).\n")
        self.w.write("\n")

    def assert_by_forward_using(self, a: LtacAssertBy) -> None:
        # forward_using is used for conjunctions?
        match a.by.n:
            case "lemma_betweennotequal":
                self.assert_by_forward_using_lemma_betweennotequal(a)
            case "lemma_collinearorder":
                self.assert_by_forward_using_lemma_collinearorder(a)
            case "lemma_congruenceflip":
                self.assert_by_forward_using_lemma_congruenceflip(a)
            case _:
                self.w.write(f"pose proof ({a.by.n}) as {a.prop.to_var()}. (* forward_using *)\n")

    def assert_by_lemma_onray_assert(self, a: LtacAssertBy) -> None:
        e = a.prop
        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]

        A, B, E = e.points
        if B == E:
            self.w.write(f"pose proof (lemma_s_onray_assert_ABB {A} {B} neq_{A}_{B}) as {e.to_var()}.\n")
        else:
            self.w.write(f"pose proof (lemma_s_onray_assert_bets_ABE {A} {B} {E} BetS_{A}_{B}_{E} neq_{A}_{B}) as {e.to_var()}.\n")
            self.w.write(f"pose proof (lemma_s_onray_assert_bets_AEB {A} {B} {E} BetS_{A}_{E}_{B} neq_{A}_{B}) as {e.to_var()}.\n")

    def assert_by_cn_equalitysub(self, a: LtacAssertBy) -> None:
        h = a.prop

        match len(h.points):
            case 3:
                A, B, C = h.points
                self.w.write("\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite eq_{A}_X; exact {h.head}_X_{B}_{C}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite eq_{B}_X; exact {h.head}_{A}_X_{C}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite eq_{C}_X; exact {h.head}_{A}_{B}_X).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite <- eq_X_{A}; exact {h.head}_X_{B}_{C}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite <- eq_X_{B}; exact {h.head}_{A}_X_{C}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite <- eq_X_{C}; exact {h.head}_{A}_{B}_X).\n")
                self.w.write("\n")
            case 4:
                A, B, C, D = h.points
                self.w.write("\n")
                # fmt: off
                self.w.write(f"assert ({h.head} {A} {B} {C} {D}) as {h.head}_{A}_{B}_{C}_{D} by (rewrite eq_{A}_X; exact {h.head}_X_{B}_{C}_{D}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C} {D}) as {h.head}_{A}_{B}_{C}_{D} by (rewrite eq_{B}_X; exact {h.head}_{A}_X_{C}_{D}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C} {D}) as {h.head}_{A}_{B}_{C}_{D} by (rewrite eq_{C}_X; exact {h.head}_{A}_{B}_X_{D}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C} {D}) as {h.head}_{A}_{B}_{C}_{D} by (rewrite eq_{D}_X; exact {h.head}_{A}_{B}_{C}_X).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C} {D}) as {h.head}_{A}_{B}_{C}_{D} by (rewrite <- eq_X_{A}; exact {h.head}_X_{B}_{C}_{D}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C} {D}) as {h.head}_{A}_{B}_{C}_{D} by (rewrite <- eq_X_{B}; exact {h.head}_{A}_X_{C}_{D}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C} {D}) as {h.head}_{A}_{B}_{C}_{D} by (rewrite <- eq_X_{C}; exact {h.head}_{A}_{B}_X_{D}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C} {D}) as {h.head}_{A}_{B}_{C}_{D} by (rewrite <- eq_X_{D}; exact {h.head}_{A}_{B}_{C}_X).\n")
                # fmt: on
                self.w.write("\n")
            case _:
                raise NotImplementedError("equalitysub with not 3,4 points is not yet done")

    def assert_by(self, a: LtacAssertBy) -> None:
        self.process_indent()
        if a.by.t == "conclude_def":
            # TODO: Triangle
            self.assert_by_conclude_def(a)
            self.context.add_prop(a.prop)
            return
        if a.by.t == "forward_using":
            self.assert_by_forward_using(a)
            self.context.add_prop(a.prop)
            return

        assert a.by.t == "conclude"

        match a.by.n:
            case "cn_equalityreflexive":
                self.w.write(f"assert ({a.prop.to_str()}) as {a.prop.to_var()} by (reflexivity).\n")
                self.context.add_prop(a.prop)
                return
            case "axiom_betweennesssymmetry":
                A, B, C = a.prop.points
                self.w.write(f"pose proof (axiom_betweennesssymmetry _ _ _ BetS_{C}_{B}_{A}) as {a.prop.to_var()}.\n")
                self.context.add_prop(a.prop)
                return
            case "axiom_betweennessidentity":
                proof = a.by.n + "???"
                self.w.write(f"pose proof ({proof}) as {a.prop.to_var()}.\n")
                self.context.add_prop(a.prop)
                return
            case "axiom_nocollapse":
                proof = a.by.n + "???"
                self.w.write(f"pose proof ({proof}) as {a.prop.to_var()}.\n")
                self.context.add_prop(a.prop)
                return
            case "cn_congruencereflexive":
                A, B, A, B = a.prop.points
                self.w.write(f"pose proof (cn_congruencereflexive {A} {B}) as {a.prop.to_var()}.\n")
                self.context.add_prop(a.prop)
                return
            case "cn_congruencereverse":
                A, B, B, A = a.prop.points
                self.w.write(f"pose proof (cn_congruencereverse {A} {B}) as {a.prop.to_var()}.\n")
                self.context.add_prop(a.prop)
                return
            case "cn_sumofparts":
                proof = a.by.n + "???"
                self.w.write(f"pose proof ({proof}) as {a.prop.to_var()}.\n")
                self.context.add_prop(a.prop)
                return
            case "cn_equalitysub":
                self.assert_by_cn_equalitysub(a)
                self.context.add_prop(a.prop)
                return
            case "lemma_onray_assert":
                self.assert_by_lemma_onray_assert(a)
                self.context.add_prop(a.prop)
                return
            case "proposition_16":
                # somehow this is not forward_using
                proof = a.by.n + "???"
                self.w.write(f"pose proof ({proof}) as {a.prop.to_var()}.\n")
                self.context.add_prop(a.prop)
                return
        proof_lemma = self.lemmas_by_name[a.by.n]
        proof_points = " ".join(["_"] * len(proof_lemma.points))
        proof_props = " ".join([p.to_var() for p in proof_lemma.given])
        proof = f"{proof_lemma.name} {proof_points} {proof_props} (* not real *)"
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
                self.context.add_prop(a.prop)
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

        last_a = by[-1]
        self.process_indent()
        self.w.write(f"contradict {last_a.prop.to_var()}.\n")
        self.process_indent()
        self.w.write(f"exact n_{last_a.prop.to_var()}.\n")

        self.indent -= 1
        self.process_indent()
        self.w.write("}\n")
        self.w.write("\n")

        self.context.pop_scope()
        if isinstance(a.prop.p, PropInversion):
            self.process_indent()
            self.w.write(f"assert ({a.prop.p.p.to_var()} := {a.prop.to_var()}).\n")
            self.process_indent()
            self.w.write(f"apply Classical_Prop.NNPP in {a.prop.p.p.to_var()}.\n")
            self.context.add_prop(PropSimple(head=a.prop.p.p.head, points=a.prop.p.p.points))
            return
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

        for a in self.l.asserts:
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
    if len(answers) < 1:
        pprint(q)
        pprint(answers)
        pprint(context)
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


def import_lemma_by_name(lemma_name: str):
    lemma_path = f"build/{lemma_name}_parse_tree.json"
    top = process_parse_tree(json.load(open(lemma_path)))

    lemmas_by_name = parse_all_lemmas()

    req_names = extract_requirements_top(top) - {
        "Col",
        "CongA",
        "Lt",
        "LtA",
        "OnRay",
        "TT",
        "TogetherGreater",
        "Triangle",
        "axiom_betweennessidentity",
        "axiom_betweennesssymmetry",
        "axiom_nocollapse",
        "cn_congruencereflexive",
        "cn_congruencereverse",
        "cn_equalityreflexive",
        "cn_equalitysub",
        "cn_sumofparts",
        "isosceles",
    }

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

    s = io.StringIO()
    print_top(s, top)
    for l in top.lemmas:
        LemmaPrinter(l=l, w=s, lemmas_by_name=lemmas_by_name).process()
    s.write("\nEnd Euclid.\n")
    print(s.getvalue())


if __name__ == "__main__":
    import_lemma_by_name(sys.argv[1])
