import io
import itertools
import json
from pprint import pprint
import sys
from typing import TextIO, Tuple, Union

from pyswip import Functor, Variable, Query, call, Prolog, PL_term_type
from pyswip.easy import getList, Functor, getString

from geocoq_rpl import (
    Lemma,
    Prop,
    PropSimple,
    PropExists,
    PropInversion,
    PropConjunction,
    PropDisjunction,
    collect_conjunction_nodes,
    parse_all_lemmas,
    process_parse_tree,
)


def prolog_prop(p: Prop) -> str:
    match p:
        case PropSimple():
            ps = ",".join([f'"{pt}"' for pt in p.points])
            return f'prop("{p.head}",[{ps}])'
        case PropInversion():
            ps = ",".join([f'"{pt}"' for pt in p.p.points])
            return f'prop("n_{p.p.head}",[{ps}])'
        case _:
            raise ValueError(f"what: {p}")


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

        case PropExists():
            p = p.p
            r.write(f'{idp}H = "{p.head}",\n')
            points = p.points
        case _:
            raise ValueError(f"prolog_lemma_rule: {p}")
    i = max(itertools.chain([0], p_to_i.values())) + 1
    for p in points:
        if p in p_to_i:
            continue
        p_to_i[p] = i
        i += 1
    ps = [f"P{p_to_i[p]}" for p in points]
    pss = ",".join(ps)
    r.write(f"{idp}P = [{pss}]")

    return r.getvalue()


def prolog_rule_for_lemma(req: Lemma) -> str:
    r = io.StringIO()

    req_name = req.name
    match req.conclusion:
        case PropSimple() | PropInversion():
            conclusions = [req.conclusion]
        case PropExists(points=_, p=PropSimple()):
            conclusions = [req.conclusion.p]
        case PropConjunction():
            conclusions = collect_conjunction_nodes(req.conclusion)
        case _:
            raise ValueError(f"prolog_rule_for_lemma: {req}")
    gids = [f"G{i+1}" for i in range(len(req.given))]
    cids = [f"C{i+1}" for i in range(len(conclusions))]
    q = ",".join(gids + cids)
    r.write(f"{req_name}({q}) :-\n")

    p_to_i = dict()
    for i, p in enumerate(req.given):
        r.write(prolog_lemma_rule(p, f"G{i+1}", p_to_i))
        r.write(",\n")

    match req.conclusion:
        case PropSimple() | PropInversion():
            r.write(prolog_lemma_rule(req.conclusion, f"C1", p_to_i))
            r.write(".\n")
        case PropExists(points=_, p=PropSimple()):
            r.write(prolog_lemma_rule(req.conclusion.p, f"C1", p_to_i))
            r.write(".\n")
        case PropConjunction():
            r.write(",\n".join([prolog_lemma_rule(p, f"C{i+1}", p_to_i) for i, p in enumerate(conclusions)]))
            r.write(".\n")
        case _:
            raise ValueError(f"prolog_rule_for_lemma: {req}")

    return r.getvalue()


def prolog_lemmas(req_names: list[str], lemmas_by_name: dict[str, Lemma], prolog_lemmas_path: str) -> None:
    req_names = req_names - {
        "Col",
        "CongA",
        "InCirc",
        "Lt",
        "LtA",
        "OnCirc",
        "OnRay",
        "OutCirc",
        "TT",
        "TogetherGreater",
        "Triangle",
        "axiom_betweennessidentity",
        "axiom_betweennesssymmetry",
        "cn_congruencereflexive",
        "cn_congruencereverse",
        "cn_equalityreflexive",
        "cn_equalitysub",
        "isosceles",
        "lemma_extension",
        "lemma_layoff",
        "lemma_onray_assert",
        "postulate_circle_circle",
        "proposition_22",
        "proposition_22",
    }

    rr = open(prolog_lemmas_path, "w")
    for req_name in sorted(req_names):
        req = lemmas_by_name[req_name]
        rr.write(prolog_rule_for_lemma(req))
        rr.write("\n")
    rr.close()


def prolog_context(context: list[Prop], prolog_context_path: str) -> None:
    with open(prolog_context_path, "w") as cf:
        for cp in context:
            if isinstance(cp, PropInversion) and isinstance(cp.p, PropDisjunction):
                cp_d = cp.p
                cf.write(prolog_prop(PropInversion(p=cp_d.left)))
                cf.write(".\n")
                if isinstance(cp_d.right, PropDisjunction):
                    cf.write(prolog_prop(PropInversion(p=cp_d.right.left)))
                    cf.write(".\n")
                    cf.write(prolog_prop(PropInversion(p=cp_d.right.right)))
                    cf.write(".\n")
                else:
                    cf.write(prolog_prop(PropInversion(p=cp_d.right)))
                    cf.write(".\n")
            else:
                cf.write(prolog_prop(cp))
                cf.write(".\n")


def functor_to_var_prop(f: Functor) -> Tuple[str, PropSimple]:
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
    return (var_name, PropSimple(head=prop_name, points=points))


def prove_simple(p: PropSimple, by: Lemma, prolog_lemmas_path: str, prolog_context_path: str) -> str:
    prolog = Prolog()
    prolog.consult(prolog_lemmas_path)
    prolog.consult(prolog_context_path)

    pq_given = ",".join([f"G{i+1}" for i in range(len(by.given))])
    pq_args = f"{pq_given},{prolog_prop(p)}"
    q = f"{by.name}({pq_args})"

    answers = list(prolog.query(q, normalize=False))
    if len(answers) < 1:
        pprint(q)
        pprint(answers)
        pprint(open(prolog_context_path).read())
        raise ValueError("no answers!")
    answer = answers[0]
    answer_vars: list[Tuple[str, PropSimple]] = list()
    for f in answer:
        var_name, prop = functor_to_var_prop(f)
        answer_vars.append((var_name, prop))
    pp = " ".join(["_" for i in range(len(by.points))])
    gg = " ".join([e[1].to_var() for e in answer_vars])
    return f"{by.name} {pp} {gg}"


def prove_forward_using(p: PropSimple, by: Lemma, prolog_lemmas_path: str, prolog_context_path: str) -> Tuple[str, int]:
    prolog = Prolog()
    prolog.consult(prolog_lemmas_path)
    prolog.consult(prolog_context_path)

    given = by.given
    assert isinstance(by.conclusion, PropConjunction)
    conclusions = collect_conjunction_nodes(by.conclusion)
    gids = [f"G{i+1}" for i in range(len(given))]

    for ci in range(len(conclusions)):
        cids = [f"C{i+1}" for i in range(len(conclusions))]
        cids[ci] = prolog_prop(p)
        pq_given = ",".join(gids)
        pg_conclusion = ",".join(cids)
        pq_args = f"{pq_given},{pg_conclusion}"
        q = f"{by.name}({pq_args})"

        answers = list(prolog.query(q, normalize=False))
        if len(answers) < 1:
            continue
        answer = answers[0]
        answer_vars: list[Tuple[str, PropSimple]] = list()
        for f in answer:
            var_name, prop = functor_to_var_prop(f)
            answer_vars.append((var_name, prop))
        pp = " ".join(["_" for i in range(len(by.points))])
        gg = " ".join([e[1].to_var() for e in answer_vars if e[0].startswith("G")])
        return (f"{by.name} {pp} {gg}", ci)
    pprint(q)
    pprint(open(prolog_context_path).read())
    raise ValueError("no answers in forward_using!")


lemma_name = "lemma_TogetherGreater_flip"
lemmas_by_name = parse_all_lemmas()

# pprint(lemmas_by_name[lemma_name])
# print(prolog_rule_for_lemma(lemmas_by_name[lemma_name]))
