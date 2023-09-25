"""
This file and its dependencies are made out of hacks, repetitive if else trees,
incomprehensible variable names, copy paste with minimal changes and otherwise 
bad code.

Many things are still handled poorly, most prominently destructs, disjunctions
and proof by cases.

Still, it enabled me to convert thousands of lines of original proofs
in a single sitting, so I'm proud of what this code accomplished, if not of how.
"""
import io
import itertools
import json
import sys
from typing import TextIO

from import_rpl import (
    Assert,
    Lemma,
    LtacAssertBy,
    LtacAssertByCases,
    LtacAssertConclude,
    LtacAssertContradiction,
    LtacConclude,
    Prop,
    PropSimple,
    PropExists,
    PropInversion,
    PropConjunction,
    PropDisjunction,
    Top,
    collect_conjunction_nodes,
    collect_disjunction_nodes,
    parse_all_lemmas,
    process_parse_tree,
)
from import_prolog import (
    prolog_context,
    prolog_lemmas,
    prove_conclude_conjunction,
    prove_conclude_exists,
    prove_simple,
    prove_forward_using,
)
from import_axioms import axioms, defs_to_supporting_lemmas_for_defs, supporting_lemmas_for_defs


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
    rs = set().union(*[extract_requirements_assert(a) for a in l.asserts])
    for d, s in defs_to_supporting_lemmas_for_defs.items():
        if d in rs:
            rs.add(s)
    return rs


def extract_requirements_top(t: Top) -> set[str]:
    rs = set().union(*[extract_requirements_lemma(l) for l in t.lemmas])
    return rs


def print_requirements(w: TextIO, t: Top) -> None:
    rs = extract_requirements_top(t)
    if "Triangle" in rs:
        rs |= {"by_def_nCol_from_Triangle", "by_def_Triangle"}
    if "OnRay" in rs:
        rs |= {
            "by_def_OnRay_from_neq_A_B",
            "by_def_OnRay_from_BetS_A_B_E",
            "by_def_OnRay_from_BetS_A_E_B",
        }
    if "Col" in rs:
        rs |= {
            "by_def_Col_from_BetS_A_B_C",
            "by_def_Col_from_BetS_A_C_B",
            "by_def_Col_from_BetS_B_A_C",
            "by_def_Col_from_eq_A_B",
            "by_def_Col_from_eq_A_C",
            "by_def_Col_from_eq_B_C",
        }
    if "nCol" in rs:
        rs |= {
            "by_prop_nCol_distinct",
            "by_prop_nCol_order",
            "by_def_nCol_from_n_Col",
            "by_def_n_Col_from_nCol",
        }
    if "isosceles" in rs:
        rs |= { "by_def_isosceles" }
    if "CI" in rs:
        rs |= { "by_def_OnCirc" }
    rs |= {
        "euclidean_axioms",
        "euclidean_defs",
    }
    for r in sorted(rs):
        if any([r.startswith(p) for p in ["cn_", "axiom_", "postulate_"]]):
            continue
        if not any([r.startswith(p) for p in ["lemma_", "proposition_", "euclidean_", "by_"]]):
            continue
        w.write(f"Require Import ProofCheckingEuclid.{r}.\n")
    w.write("\n")


def print_top(w: TextIO, t: Top) -> None:
    print_requirements(w, t)
    w.write("Section Euclid.\n\n")
    w.write("Context `{Ax:euclidean_neutral_ruler_compass}.\n\n")


lemmas_can_be_forward_using = [
    "lemma_crossimpliesopposite",
    "lemma_legsmallerhypotenuse",
    "lemma_righttogether",
    "by_prop_RightTriangle_supplement",
    "lemma_together",
    "lemma_togethera",
    "proposition_04",
    "proposition_14",
    "proposition_15",
    "proposition_16",
    "proposition_26A",
    "proposition_29",
    "proposition_29C",
    "proposition_33",
    "proposition_33B",
    "proposition_34",
]


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
            case PropExists():
                self.add_prop(p.p)
                return
            case PropSimple() | PropInversion():
                pass
            case _:
                raise ValueError(f"unexpected {p} added to context")
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
        self.prolog_lemmas_path = "/tmp/lemmas.pl"
        self.prolog_context_path = "/tmp/context.pl"

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
        self.process_indent()
        for hh in hhs_eq:
            if not (set(hh.points) <= set(e.points)):
                continue
            X, Y = hh.points
            if [X, Y] == [A, B]:
                self.w.write(
                    f"pose proof (by_def_Col_from_eq_A_B {A} {B} {C} eq_{A}_{B}) as Col_{A}_{B}_{C}.\n"
                )
                break
            elif [X, Y] == [A, C]:
                self.w.write(
                    f"pose proof (by_def_Col_from_eq_A_C {A} {B} {C} eq_{A}_{C}) as Col_{A}_{B}_{C}.\n"
                )
                break
            elif [X, Y] == [B, C]:
                self.w.write(
                    f"pose proof (by_def_Col_from_eq_B_C {A} {B} {C} eq_{B}_{C}) as Col_{A}_{B}_{C}.\n"
                )
                break
        for hh in hhs_bets:
            if set(e.points) != set(hh.points):
                continue
            X, Y, Z = hh.points
            if [X, Y, Z] == [B, A, C]:
                self.w.write(
                    f"pose proof (by_def_Col_from_BetS_B_A_C {A} {B} {C} BetS_{B}_{A}_{C}) as Col_{A}_{B}_{C}.\n"
                )
                break
            elif [X, Y, Z] == [A, B, C]:
                self.w.write(
                    f"pose proof (by_def_Col_from_BetS_A_B_C {A} {B} {C} BetS_{A}_{B}_{C}) as Col_{A}_{B}_{C}.\n"
                )
                break
            elif [X, Y, Z] == [A, C, B]:
                self.w.write(
                    f"pose proof (by_def_Col_from_BetS_A_C_B {A} {B} {C} BetS_{A}_{C}_{B}) as Col_{A}_{B}_{C}.\n"
                )
                break

    def assert_by_conclude_def_destruct(self, a: LtacAssertBy) -> None:
        e = a.prop
        assert isinstance(e, PropExists) or isinstance(e, PropConjunction)
        # TODO: cover the PropConjunction case

        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]
        hhs = [h for h in hhs if h.head == a.by.n]
        self.w.write("\n")
        for hh in hhs:
            self.process_indent()
            self.w.write(f"destruct {hh.to_var()} as {a.prop.to_var()}.\n")

    def assert_by_conclude_def(self, a: LtacAssertBy) -> None:
        match a.prop:
            case PropExists() | PropConjunction():
                self.assert_by_conclude_def_destruct(a)
                return
            case PropDisjunction():
                self.process_indent()
                self.w.write(f"destruct Col_X_Y_Z as {a.prop.to_var()}.\n")
                return

        match a.prop:
            case PropSimple():
                if a.prop.head != a.by.n:
                    self.process_indent()
                    self.w.write(f"destruct X as {a.prop.to_var()}. (* def destruct *)\n")
                    return
            case PropInversion():
                self.process_indent()
                self.w.write(f"destruct X as {a.prop.to_var()}. (* def destruct *)\n")
                return

        if a.by.n in defs_to_supporting_lemmas_for_defs:
            self.assert_by(
                LtacAssertBy(
                    a.prop,
                    by=LtacConclude(t="conclude", n=defs_to_supporting_lemmas_for_defs[a.by.n]),
                )
            )
            return

        match a.by.n:
            case "Triangle":
                A, B, C = a.prop.points
                match a.prop.head:
                    case "nCol":
                        self.process_indent()
                        self.w.write(
                            f"pose proof (by_def_nCol_from_Triangle _ _ _ Triangle_{A}_{B}_{C}) as nCol_{A}_{B}_{C}.\n"
                        )
                    case "Triangle":
                        self.process_indent()
                        self.w.write(
                            f"pose proof (by_def_Triangle _ _ _ nCol_{A}_{B}_{C}) as Triangle_{A}_{B}_{C}.\n"
                        )
            case "Col":
                self.assert_by_conclude_def_Col(a)
            case "InCirc":
                P, J = a.prop.points
                U, V, W, X, Y = "U", "V", "W", "X", "Y"
                self.w.write(
                    f"pose proof (by_def_InCirc_center _ _ _ _ CI_{J}_{P}_{V}_{W}) as {a.prop.to_var()}.\n"
                )
                self.process_indent()
                self.w.write(
                    f"pose proof (by_def_InCirc_within_radius _ _ _ _ _ _ _ CI_{J}_{U}_{V}_{W} BetS_{U}_{Y}_{X} Cong_{U}_{X}_{V}_{W} Cong_{U}_{P}_{U}_{Y}) as {a.prop.to_var()}.\n"
                )
            case _:
                self.process_indent()
                self.w.write(f"pose proof ({a.by.n}) as {a.prop.to_var()}. (* conclude_def *)\n")

    def assert_by_forward_using(self, a: LtacAssertBy) -> None:
        by = self.lemmas_by_name[a.by.n]
        assert isinstance(by.conclusion, PropConjunction), a
        conclusions = collect_conjunction_nodes(by.conclusion)

        prolog_context(self.context.get_props(), self.prolog_context_path)
        proof, ci = prove_forward_using(
            a.prop, by, self.prolog_lemmas_path, self.prolog_context_path
        )
        ass = ["_" for i in range(len(conclusions))]
        ass[ci] = a.prop.to_var()
        asss = " & ".join(ass)

        self.process_indent()
        self.w.write(f"pose proof ({proof}) as ({asss}).\n")

    def assert_by_by_prop_OnRay_assert(self, a: LtacAssertBy) -> None:
        e = a.prop
        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]

        A, B, E = e.points
        if B == E:
            self.w.write(
                f"pose proof (by_def_OnRay_from_neq_A_B {A} {B} neq_{A}_{B}) as {e.to_var()}.\n"
            )
        else:
            # fmt: off
            self.w.write("\n")
            self.process_indent()
            self.w.write(f"pose proof (by_def_OnRay_from_BetS_A_B_E {A} {B} {E} BetS_{A}_{B}_{E} neq_{A}_{B}) as {e.to_var()}.\n")
            self.process_indent()
            self.w.write(f"pose proof (by_def_OnRay_from_BetS_A_E_B {A} {B} {E} BetS_{A}_{E}_{B} neq_{A}_{B}) as {e.to_var()}.\n")
            self.w.write("\n")
            # fmt: on

    def assert_by_lemma_extension(self, a: LtacAssertBy) -> None:
        e = a.prop
        assert isinstance(e, PropExists)
        e = e.p

        BetS_A_B_X, Cong_B_X_P_Q = collect_conjunction_nodes(e)
        A, B, X = BetS_A_B_X.points
        B, X, P, Q = Cong_B_X_P_Q.points
        self.w.write(
            f"pose proof (lemma_extension {A} {B} {P} {Q} neq_{A}_{B} neq_{P}_{Q}) as ({X} & {e.to_var()}).\n"
        )

    def assert_by_cn_equalitysub(self, a: LtacAssertBy) -> None:
        e = a.prop
        if not isinstance(e, PropSimple):
            self.w.write(f"assert ({e.to_str()}) as {e.to_var()} by (rewrite ???; exact ???).\n")
            return

        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]
        hhs_eq = [h for h in hhs if h.head == "eq"]
        hhs_same = [h for h in hhs if h.head == e.head]

        src_points_joined = "".join(e.points)
        for h in hhs_same:
            dst_points_joined = "".join(h.points)
            for h_eq in hhs_eq:
                A, B = h_eq.points
                replaced_A_B = src_points_joined.replace(A, B)
                replaced_B_A = src_points_joined.replace(B, A)
                # fmt: off
                if replaced_A_B == dst_points_joined:
                    self.w.write(f"assert ({e.to_str()}) as {e.to_var()} by (rewrite {h_eq.to_var()}; exact {h.to_var()}).\n")
                    return
                elif replaced_B_A == dst_points_joined:
                    self.w.write(f"assert ({e.to_str()}) as {e.to_var()} by (rewrite <- {h_eq.to_var()}; exact {h.to_var()}).\n")
                    return
                # fmt: on
        # fmt: off
        self.w.write(f"assert ({e.to_str()}) as {e.to_var()} by (setoid_rewrite).\n")
        # fmt: on

    def assert_by(self, a: LtacAssertBy) -> None:
        if a.by.t == "conclude_def":
            self.assert_by_conclude_def(a)
            self.context.add_prop(a.prop)
            return
        if a.by.t == "forward_using":
            self.assert_by_forward_using(a)
            self.context.add_prop(a.prop)
            return

        if a.by.n in lemmas_can_be_forward_using and isinstance(a.prop, PropSimple):
            self.assert_by_forward_using(a)
            self.context.add_prop(a.prop)
            return

        # Special case for proposition_27
        if a.by.t in ["unfold", "auto", "eapply"]:
            self.process_indent()
            self.w.write(f"pose proof (???) as {a.prop.to_var()}.\n")
            self.context.add_prop(a.prop)
            return

        assert a.by.t == "conclude", a

        self.process_indent()
        match a.by.n:
            case "cn_equalityreflexive":
                self.w.write(f"assert ({a.prop.to_str()}) as {a.prop.to_var()} by (reflexivity).\n")
                self.context.add_prop(a.prop)
                return
            case "axiom_betweennesssymmetry":
                A, B, C = a.prop.points
                self.w.write(
                    f"pose proof (axiom_betweennesssymmetry _ _ _ BetS_{C}_{B}_{A}) as {a.prop.to_var()}.\n"
                )
                self.context.add_prop(a.prop)
                return
            case "axiom_betweennessidentity":
                A, B, A = a.prop.p.points
                self.w.write(
                    f"pose proof (axiom_betweennessidentity {A} {B}) as {a.prop.to_var()}.\n"
                )
                self.context.add_prop(a.prop)
                return
            case "postulate_circle_circle":
                proof = a.by.n + "???"
                self.w.write(f"pose proof ({proof}) as {a.prop.to_var()}.\n")
                self.context.add_prop(a.prop)
                return
            case "axiom_paste3" | "axiom_halvesofequals":
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
            case "cn_equalitysub":
                self.assert_by_cn_equalitysub(a)
                self.context.add_prop(a.prop)
                return
            case "by_prop_OnRay_assert":
                self.assert_by_by_prop_OnRay_assert(a)
                self.context.add_prop(a.prop)
                return
            case "lemma_extension":
                self.assert_by_lemma_extension(a)
                self.context.add_prop(a.prop)
                return
            case "by_prop_OnRay_orderofpoints_any" | "cn_equalitytransitive":
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
            case PropSimple() | PropInversion():
                prolog_context(self.context.get_props(), self.prolog_context_path)
                proof = prove_simple(
                    a.prop, proof_lemma, self.prolog_lemmas_path, self.prolog_context_path
                )
                self.context.add_prop(a.prop)
            case PropConjunction():
                prolog_context(self.context.get_props(), self.prolog_context_path)
                proof = prove_conclude_conjunction(
                    a.prop, proof_lemma, self.prolog_lemmas_path, self.prolog_context_path
                )
                self.context.add_prop(a.prop)
            case PropExists():
                match a.prop.p:
                    case PropSimple():
                        prolog_context(self.context.get_props(), self.prolog_context_path)
                        proof = prove_simple(
                            a.prop.p, proof_lemma, self.prolog_lemmas_path, self.prolog_context_path
                        )
                    case PropConjunction():
                        prolog_context(self.context.get_props(), self.prolog_context_path)
                        proof = prove_conclude_exists(
                            a.prop, proof_lemma, self.prolog_lemmas_path, self.prolog_context_path
                        )

                self.context.add_prop(a.prop.p)
            case _:
                raise ValueError(f"unexpected {a.prop} in {a}")
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

        # TODO: weird case in proposition_22
        if by:
            last_a = by[-1]
            self.process_indent()
            self.w.write(f"contradict {last_a.prop.to_var()}.\n")
            self.process_indent()
            self.w.write(f"exact n_{last_a.prop.to_var()}.\n")
        else:
            self.process_indent()
            self.w.write(f"NOTHING TO CONTRADICT????\n")

        self.indent -= 1
        self.process_indent()
        self.w.write("}\n")

        self.context.pop_scope()

        if isinstance(a.prop.p, PropInversion):
            self.process_indent()
            self.w.write(f"assert ({a.prop.p.p.to_var()} := {a.prop.to_var()}).\n")
            self.process_indent()
            self.w.write(f"apply Classical_Prop.NNPP in {a.prop.p.p.to_var()}.\n")
            self.context.add_prop(a.prop.p.p)
            self.w.write("\n")
            return

        match a.prop.p.head:
            case "eq":
                new_p = PropSimple(head="neq", points=a.prop.p.points)

                self.process_indent()
                self.w.write(f"assert ({new_p.to_var()} := {a.prop.to_var()}).\n")
                self.w.write("\n")

                self.context.add_prop(new_p)
            case "neq":
                new_p = PropSimple(head="eq", points=a.prop.p.points)

                self.process_indent()
                self.w.write(f"assert ({new_p.to_var()} := {a.prop.to_var()}).\n")
                self.process_indent()
                self.w.write(f"apply Classical_Prop.NNPP in {new_p.to_var()}.\n")
                self.w.write("\n")

                self.context.add_prop(new_p)
            case "Col":
                new_prop = PropSimple(head="nCol", points=a.prop.p.points)
                self.context.add_prop(new_prop)
                self.process_indent()
                self.w.write(
                    f"pose proof (by_def_nCol_from_n_Col _ _ _ {prop.to_var()}) as {new_prop.to_var()}.\n"
                )
            case _:
                self.context.add_prop(a.prop)
        self.w.write("\n")

    def assert_by_cases(self, a: LtacAssertByCases) -> None:
        prop = a.prop

        self.w.write("\n")
        self.process_indent()
        self.w.write("(* assert by cases *)\n")
        self.process_indent()
        self.w.write(f"assert ({prop.to_str()}) as {prop.to_var()}.\n")
        self.process_indent()
        self.w.write(f"destruct X as {a.on.to_var()}.\n")

        disjunction_props = collect_disjunction_nodes(a.on)

        assert len(disjunction_props) == len(a.cases)
        for i, case in enumerate(a.cases):
            disjunction_prop = disjunction_props[i]
            self.context.push_scope()
            self.context.add_prop(disjunction_prop)

            self.process_indent()
            self.w.write("{\n")
            self.indent += 1

            self.process_indent()
            self.w.write(f"(* case {disjunction_prop.to_var()} *)\n")
            for aa in case.asserts:
                self.process_assert(aa)

            self.w.write("\n")
            self.process_indent()
            self.w.write(f"exact {prop.to_var()}.\n")

            self.indent -= 1
            self.process_indent()
            self.w.write("}\n")
            self.context.pop_scope()
        self.context.add_prop(a.prop)

    def assert_conclude(self, a: LtacAssertConclude) -> None:
        prop = a.prop

        self.w.write("\n")
        self.process_indent()
        self.w.write(f"assert ({prop.to_str()}) as {prop.to_var()}. (* assert_conclude *)\n")
        self.context.add_prop(prop)

    def process_assert(self, a: Assert) -> None:
        match a:
            case LtacAssertBy():
                self.assert_by(a)
            case LtacAssertContradiction():
                self.assert_contradiction(a)
            case LtacAssertByCases():
                self.assert_by_cases(a)
            case LtacAssertConclude():
                self.assert_conclude(a)
            case _:
                raise ValueError(f"Unexpected assert type: {a}")

    def prepare_prolog(self) -> None:
        prolog_lemmas(
            extract_requirements_lemma(self.l), self.lemmas_by_name, self.prolog_lemmas_path
        )

    def process(self) -> None:
        self.prepare_prolog()
        self.process_preamble()

        for a in self.l.asserts:
            self.process_assert(a)
            
        match self.l.conclusion:
            case PropSimple() | PropInversion():
                self.w.write("\n")
                self.process_indent()
                self.w.write(f"exact {self.l.conclusion.to_var()}.")
            case _:
                self.w.write("\n")
                self.process_indent()
                self.w.write(f"(* exact {self.l.conclusion.to_var()}. *)")

        self.w.write("\n")
        self.w.write("Qed.\n")


def import_lemma_by_name(lemma_name: str):
    lemma_path = f"build/{lemma_name}_parse_tree.json"
    top = process_parse_tree(json.load(open(lemma_path)))

    lemmas_by_name = parse_all_lemmas() | axioms | supporting_lemmas_for_defs

    s = io.StringIO()
    print_top(s, top)
    for l in top.lemmas:
        LemmaPrinter(l=l, w=s, lemmas_by_name=lemmas_by_name).process()
    s.write("\nEnd Euclid.\n")
    print(s.getvalue())


if __name__ == "__main__":
    import_lemma_by_name(sys.argv[1])
