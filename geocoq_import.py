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
from geocoq_prolog import (
    prolog_context,
    prolog_lemmas,
    prove_simple,
    prove_forward_using,
)


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
    if "OnCirc" in rs:
        rs.add("lemma_s_oncirc_radius")
    if "OutCirc" in rs:
        rs.add("lemma_s_outcirc_beyond_perimeter")
    if "OnRay" in rs:
        rs.add("lemma_s_onray")
    return rs


def extract_requirements_top(t: Top) -> set[str]:
    rs = set().union(*[extract_requirements_lemma(l) for l in t.lemmas])
    return rs


def print_requirements(w: TextIO, t: Top) -> None:
    rs = extract_requirements_top(t)
    rs |= {
        "euclidean_axioms",
        "euclidean_defs",
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
        "lemma_s_oncirc_radius",
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
        for hh in hhs_eq:
            if not (set(hh.points) <= set(e.points)):
                continue
            X, Y = hh.points
            if [X, Y] == [A, B]:
                self.w.write(
                    f"pose proof (lemma_s_col_eq_A_B {A} {B} {C} eq_{A}_{B}) as Col_{A}_{B}_{C}.\n"
                )
                break
            elif [X, Y] == [A, C]:
                self.w.write(
                    f"pose proof (lemma_s_col_eq_A_C {A} {B} {C} eq_{A}_{C}) as Col_{A}_{B}_{C}.\n"
                )
                break
            elif [X, Y] == [B, C]:
                self.w.write(
                    f"pose proof (lemma_s_col_eq_B_C {A} {B} {C} eq_{B}_{C}) as Col_{A}_{B}_{C}.\n"
                )
                break
        for hh in hhs_bets:
            if set(e.points) != set(hh.points):
                continue
            X, Y, Z = hh.points
            if [X, Y, Z] == [B, A, C]:
                self.w.write(
                    f"pose proof (lemma_s_col_BetS_B_A_C {A} {B} {C} BetS_{B}_{A}_{C}) as Col_{A}_{B}_{C}.\n"
                )
                break
            elif [X, Y, Z] == [A, B, C]:
                self.w.write(
                    f"pose proof (lemma_s_col_BetS_A_B_C {A} {B} {C} BetS_{A}_{B}_{C}) as Col_{A}_{B}_{C}.\n"
                )
                break
            elif [X, Y, Z] == [A, C, B]:
                self.w.write(
                    f"pose proof (lemma_s_col_BetS_A_C_B {A} {B} {C} BetS_{A}_{C}_{B}) as Col_{A}_{B}_{C}.\n"
                )
                break

    def assert_by_conclude_def_destruct(self, a: LtacAssertBy) -> None:
        e = a.prop
        assert isinstance(e, PropExists)
        # TODO: cover the PropConjunction case

        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]
        hhs = [h for h in hhs if h.head == a.by.n]
        self.w.write("\n")
        for hh in hhs:
            self.process_indent()
            self.w.write(f"destruct {hh.to_var()} as {a.prop.to_var()}.\n")

    def assert_by_conclude_def_Lt(self, a: LtacAssertBy) -> None:
        assert isinstance(a.prop, PropSimple)
        A, B, C, D = a.prop.points
        X = "X"
        self.w.write(
            f"pose proof (lemma_s_lt _ _ _ _ _ BetS_{C}_{X}_{D} Cong_{C}_{X}_{A}_{B}) as {a.prop.to_var()}.\n"
        )

    def assert_by_conclude_def(self, a: LtacAssertBy) -> None:
        match a.prop:
            case PropExists() | PropConjunction():
                self.assert_by_conclude_def_destruct(a)
                return
            case PropDisjunction():
                self.w.write(f"destruct Col_X_Y_Z as {a.prop.to_var()}")
                return

        match a.by.n:
            case "Triangle":
                A, B, C = a.prop.points
                match a.prop.head:
                    case "nCol":
                        self.w.write(
                            f"pose proof (lemma_s_ncol_triangle _ _ _ Triangle_{A}_{B}_{C}) as nCol_{A}_{B}_{C}.\n"
                        )
                    case "Triangle":
                        self.w.write(
                            f"pose proof (lemma_s_triangle _ _ _ nCol_{A}_{B}_{C}) as Triangle_{A}_{B}_{C}.\n"
                        )
            case "Col":
                self.assert_by_conclude_def_Col(a)
            case "Lt":
                self.assert_by_conclude_def_Lt(a)
            case "InCirc":
                P, J = a.prop.points
                U, V, W, X, Y = "U", "V", "W", "X", "Y"
                self.w.write(
                    f"pose proof (lemma_s_incirc_centre _ _ _ _ CI_{J}_{P}_{V}_{W}) as {a.prop.to_var()}.\n"
                )
                self.process_indent()
                self.w.write(
                    f"pose proof (lemma_s_incirc_within_radius _ _ _ _ _ _ _ CI_{J}_{U}_{V}_{W} BetS_{U}_{Y}_{X} Cong_{U}_{X}_{V}_{W} Cong_{U}_{P}_{U}_{Y}) as {a.prop.to_var()}.\n"
                )
            case "OnCirc":
                self.assert_by(
                    LtacAssertBy(a.prop, by=LtacConclude(t="conclude", n="lemma_s_oncirc_radius"))
                )
            case "OutCirc":
                self.assert_by(
                    LtacAssertBy(
                        a.prop, by=LtacConclude(t="conclude", n="lemma_s_outcirc_beyond_perimeter")
                    )
                )
            case "OnRay":
                self.assert_by(
                    LtacAssertBy(a.prop, by=LtacConclude(t="conclude", n="lemma_s_onray"))
                )
            case _:
                self.w.write(f"pose proof ({a.by.n}) as {a.prop.to_var()}. (* conclude_def *)\n")

    def assert_by_forward_using(self, a: LtacAssertBy) -> None:
        by = self.lemmas_by_name[a.by.n]
        assert isinstance(by.conclusion, PropConjunction)
        conclusions = collect_conjunction_nodes(by.conclusion)

        prolog_context(self.context.get_props(), self.prolog_context_path)
        proof, ci = prove_forward_using(
            a.prop, by, self.prolog_lemmas_path, self.prolog_context_path
        )
        ass = ["_" for i in range(len(conclusions))]
        ass[ci] = a.prop.to_var()
        asss = " & ".join(ass)
        self.w.write(f"pose proof ({proof}) as ({asss}).\n")

    def assert_by_lemma_onray_assert(self, a: LtacAssertBy) -> None:
        e = a.prop
        hhs = self.context.get_props()
        hhs = [h for h in hhs if isinstance(h, PropSimple)]

        A, B, E = e.points
        if B == E:
            self.w.write(
                f"pose proof (lemma_s_onray_assert_ABB {A} {B} neq_{A}_{B}) as {e.to_var()}.\n"
            )
        else:
            self.w.write(
                f"pose proof (lemma_s_onray_assert_bets_ABE {A} {B} {E} BetS_{A}_{B}_{E} neq_{A}_{B}) as {e.to_var()}.\n"
            )
            self.w.write(
                f"pose proof (lemma_s_onray_assert_bets_AEB {A} {B} {E} BetS_{A}_{E}_{B} neq_{A}_{B}) as {e.to_var()}.\n"
            )

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
        h = a.prop

        match len(h.points):
            case 3:
                A, B, C = h.points
                self.w.write("\n")
                # fmt: off
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite eq_{A}_X; exact {h.head}_X_{B}_{C}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite eq_{B}_X; exact {h.head}_{A}_X_{C}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite eq_{C}_X; exact {h.head}_{A}_{B}_X).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite <- eq_X_{A}; exact {h.head}_X_{B}_{C}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite <- eq_X_{B}; exact {h.head}_{A}_X_{C}).\n")
                self.w.write(f"assert ({h.head} {A} {B} {C}) as {h.head}_{A}_{B}_{C} by (rewrite <- eq_X_{C}; exact {h.head}_{A}_{B}_X).\n")
                # fmt: on
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
                self.w.write(
                    f"pose proof (axiom_betweennesssymmetry _ _ _ BetS_{C}_{B}_{A}) as {a.prop.to_var()}.\n"
                )
                self.context.add_prop(a.prop)
                return
            case "axiom_betweennessidentity" | "postulate_circle_circle":
                proof = a.by.n + "???"
                self.w.write(f"pose proof ({proof}) as {a.prop.to_var()}.\n")
                self.context.add_prop(a.prop)
                return
            case "lemma_together":
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
            case "lemma_onray_assert":
                self.assert_by_lemma_onray_assert(a)
                self.context.add_prop(a.prop)
                return
            case "lemma_extension":
                self.assert_by_lemma_extension(a)
                self.context.add_prop(a.prop)
                return
            case "proposition_16":
                self.assert_by_forward_using(a)
                self.context.add_prop(a.prop)
                return
            case "lemma_crossbar" | "lemma_onray_orderofpoints_any":
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
                prolog_context(self.context.get_props(), self.prolog_context_path)
                proof = prove_simple(
                    a.prop, proof_lemma, self.prolog_lemmas_path, self.prolog_context_path
                )
                self.context.add_prop(a.prop)
            case PropConjunction() | PropInversion():
                self.context.add_prop(a.prop)
            case PropExists():
                match a.prop.p:
                    case PropSimple():
                        prolog_context(self.context.get_props(), self.prolog_context_path)
                        proof = prove_simple(
                            a.prop.p, proof_lemma, self.prolog_lemmas_path, self.prolog_context_path
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
                self.context.add_prop(PropSimple(head="neq", points=a.prop.p.points))
            case "Col":
                new_prop = PropSimple(head="nCol", points=a.prop.p.points)
                self.context.add_prop(new_prop)
                self.process_indent()
                self.w.write(
                    f"pose proof (lemma_s_n_col_ncol _ _ _ {prop.to_var()}) as {new_prop.to_var()}.\n"
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

    def process_assert(self, a: Assert) -> None:
        match a:
            case LtacAssertBy():
                self.assert_by(a)
            case LtacAssertContradiction():
                self.assert_contradiction(a)
            case LtacAssertByCases():
                self.assert_by_cases(a)

    def prepare_prolog(self) -> None:
        prolog_lemmas(
            extract_requirements_lemma(self.l), self.lemmas_by_name, self.prolog_lemmas_path
        )

    def process(self) -> None:
        self.prepare_prolog()
        self.process_preamble()

        for a in self.l.asserts:
            self.process_assert(a)

        self.w.write("Qed.\n")


axioms = {
    "axiom_nocollapse": Lemma(
        name="axiom_nocollapse",
        points=["A", "B", "C", "D"],
        given=[
            PropSimple(head="neq", points=["A", "B"]),
            PropSimple(head="Cong", points=["A", "B", "C", "D"]),
        ],
        conclusion=PropSimple(head="neq", points=["C", "D"]),
        asserts=[],
    ),
    "cn_sumofparts": Lemma(
        name="cn_sumofparts",
        points=["A", "B", "C", "a", "b", "c"],
        given=[
            PropSimple(head="Cong", points=["A", "B", "a", "b"]),
            PropSimple(head="Cong", points=["B", "C", "b", "c"]),
            PropSimple(head="BetS", points=["A", "B", "C"]),
            PropSimple(head="BetS", points=["a", "b", "c"]),
        ],
        conclusion=PropSimple(head="Cong", points=["A", "C", "a", "c"]),
        asserts=[],
    ),
    "cn_congruencetransitive": Lemma(
        name="cn_congruencetransitive",
        points=["A", "B", "C", "D", "E", "F"],
        given=[
            PropSimple(head="Cong", points=["A", "B", "C", "D"]),
            PropSimple(head="Cong", points=["A", "B", "E", "F"]),
        ],
        conclusion=PropSimple(head="Cong", points=["C", "D", "E", "F"]),
        asserts=[],
    ),
    "axiom_connectivity": Lemma(
        name="axiom_connectivity",
        points=["A", "B", "C", "D"],
        given=[
            PropSimple(head="BetS", points=["A", "B", "D"]),
            PropSimple(head="BetS", points=["A", "C", "D"]),
            PropInversion(p=PropSimple(head="BetS", points=["A", "B", "C"])),
            PropInversion(p=PropSimple(head="BetS", points=["A", "C", "B"])),
        ],
        conclusion=PropSimple(head="eq", points=["B", "C"]),
        asserts=[],
    ),
    "postulate_Euclid3": Lemma(
        name="postulate_Euclid3",
        points=["A", "B"],
        given=[
            PropSimple(head="neq", points=["A", "B"]),
        ],
        conclusion=PropExists(points=["X"], p=PropSimple(head="CI", points=["X", "A", "A", "B"])),
        asserts=[],
    ),
    "lemma_s_oncirc_radius": Lemma(
        name="lemma_s_oncirc_radius",
        points=["B", "J", "U", "X", "Y"],
        given=[
            PropSimple(head="CI", points=["J", "U", "X", "Y"]),
            PropSimple(head="Cong", points=["U", "B", "X", "Y"]),
        ],
        conclusion=PropSimple(head="OnCirc", points=["B", "J"]),
        asserts=[],
    ),
    "lemma_s_outcirc_beyond_perimeter": Lemma(
        name="lemma_s_outcirc_beyond_perimeter",
        points=["P", "J", "U", "V", "W", "X"],
        given=[
            PropSimple(head="CI", points=["J", "U", "V", "W"]),
            PropSimple(head="BetS", points=["U", "X", "P"]),
            PropSimple(head="Cong", points=["U", "X", "V", "W"]),
        ],
        conclusion=PropSimple(head="OutCirc", points=["P", "J"]),
        asserts=[],
    ),
    "lemma_s_onray": Lemma(
        name="lemma_s_onray",
        points=["A", "B", "C", "X"],
        given=[
            PropSimple(head="BetS", points=["X", "A", "B"]),
            PropSimple(head="BetS", points=["X", "A", "C"]),
        ],
        conclusion=PropSimple(head="OnRay", points=["A", "B", "C"]),
        asserts=[],
    ),
    "axiom_orderofpoints_ABD_BCD_ABC": Lemma(
        name="axiom_orderofpoints_ABD_BCD_ABC",
        points=["A", "B", "C", "D"],
        given=[
            PropSimple(head="BetS", points=["A", "B", "D"]),
            PropSimple(head="BetS", points=["B", "C", "D"]),
        ],
        conclusion=PropSimple(head="BetS", points=["A", "B", "C"]),
        asserts=[],
    ),
    "axiom_circle_center_radius": Lemma(
        name="axiom_circle_center_radius",
        points=["A", "B", "C", "J", "P"],
        given=[
            PropSimple(head="CI", points=["J", "A", "B", "C"]),
            PropSimple(head="OnCirc", points=["P", "J"]),
        ],
        conclusion=PropSimple(head="Cong", points=["A", "P", "B", "C"]),
        asserts=[],
    ),
}


def import_lemma_by_name(lemma_name: str):
    lemma_path = f"build/{lemma_name}_parse_tree.json"
    top = process_parse_tree(json.load(open(lemma_path)))

    lemmas_by_name = parse_all_lemmas() | axioms

    s = io.StringIO()
    print_top(s, top)
    for l in top.lemmas:
        LemmaPrinter(l=l, w=s, lemmas_by_name=lemmas_by_name).process()
    s.write("\nEnd Euclid.\n")
    print(s.getvalue())


if __name__ == "__main__":
    import_lemma_by_name(sys.argv[1])
