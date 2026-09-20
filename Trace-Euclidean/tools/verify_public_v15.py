"""Rerun the v15 rational certificates against the published extracted inputs."""

from __future__ import annotations

import json
import re
from fractions import Fraction as Q
from math import factorial
from pathlib import Path

import mpmath as mp
import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "inputs" / "manuscript_inputs_v15.json"
OUTPUT = ROOT / "results" / "python_v15_summary.json"
mp.mp.dps = 90
checks: dict[str, bool] = {}


def check(name: str, condition: bool) -> None:
    checks[name] = bool(condition)
    if not condition:
        raise AssertionError(name)


def atan_bounds(q: int, terms: int = 100) -> tuple[Q, Q]:
    lower = sum((Q((-1) ** j, (2 * j + 1) * q ** (2 * j + 1))
                 for j in range(terms)), Q(0))
    return lower, lower + Q(1, (2 * terms + 1) * q ** (2 * terms + 1))


def snap(lower: Q, upper: Q, digits: int = 100) -> tuple[Q, Q]:
    scale = 10 ** digits
    return (Q(lower.numerator * scale // lower.denominator, scale),
            Q(-((-upper.numerator * scale) // upper.denominator), scale))


def exp_bounds(x: Q, terms: int = 210) -> tuple[Q, Q]:
    term = total = Q(1)
    for j in range(1, terms + 1):
        term *= x / j
        total += term
    return snap(total, total + term * x / (terms + 1) / (1 - x / (terms + 2)))


p5, p5_upper = atan_bounds(5)
p239, p239_upper = atan_bounds(239)
PI_LO, PI_HI = snap(16 * p5 - 4 * p239_upper, 16 * p5_upper - 4 * p239)
E_LO, E_HI = exp_bounds(Q(1))
EXP_LO, EXP_HI = exp_bounds(Q(10667, 1000))
_, EXP_CORR_HI = exp_bounds(Q(10667, 15000))
MIN_DISCRIMINANTS = (1, 5, 49, 725, 14641, 300125, 20134393,
                     282300416, 9685993193)


def volume_interval(n: int, d: int) -> tuple[Q, Q]:
    dimension = n * d
    k = dimension // 2
    if dimension % 2:
        coefficient = Q(d ** dimension * 16 ** (k + 1) * factorial(k + 1) ** 2,
                        factorial(2 * k + 2) ** 2)
        power = dimension - 1
    else:
        coefficient = Q(d ** dimension, factorial(k) ** 2)
        power = dimension
    if d <= 9:
        coefficient /= MIN_DISCRIMINANTS[d - 1] ** n
    elif d == 10:
        coefficient /= Q(14) ** dimension
    elif d == 11:
        coefficient /= Q(14083, 1000) ** dimension
    else:
        coefficient /= Q(36347, 1000) ** dimension
    lower, upper = coefficient * PI_LO ** power, coefficient * PI_HI ** power
    if d >= 12:
        lower *= EXP_LO ** n
        upper *= EXP_HI ** n
    return lower, upper


def mpq(q: Q) -> mp.mpf:
    return mp.mpf(q.numerator) / q.denominator


def fundamental_discriminant(m: int) -> int:
    return m if m % 4 == 1 else 4 * m


def rho(a: int, b: int, c: int) -> Q:
    return Q(a * c * (a + c - 2 * b), 4 * (a * c - b * b))


def main() -> int:
    data = json.loads(INPUT.read_text(encoding="utf-8"))
    paper = data["manuscript"]
    check("v15_source_digest_format", paper["version"] == "v15" and
          re.fullmatch(r"[0-9a-f]{64}", paper["sha256"]) is not None)
    check("required_label_coverage", all(
        label in data["labels"] for label in (
            "thm:finiteness-classic", "thm:finiteness-integral",
            "thm:rank-one-classification", "prop:trace-euclidean-quadratic")))
    check("rank_cutoff", 4 * PI_HI * E_HI < 35)
    check("degree_cutoff", Q(36347, 1000) / EXP_CORR_HI > 2 * PI_HI * E_HI)

    intervals = {(n, d): volume_interval(n, d)
                 for n in range(1, 35) for d in range(1, 15)}
    pairs: dict[str, list[tuple[int, int]]] = {}
    for kind in ("classic", "integral"):
        retained: list[tuple[int, int]] = []
        for d in range(1, 15):
            for n in range(1, 35):
                lower, upper = intervals[n, d]
                threshold = Q(1) if kind == "classic" or n == 1 else Q(1, 2 ** (n * d))
                check(f"resolved_{kind}_{n}_{d}", lower >= threshold or upper < threshold)
                if lower >= threshold:
                    retained.append((n, d))
        pairs[kind] = retained
        rows = data["table_rows"][kind]
        check(f"{kind}_table_pairs", [(r["n"], r["d"]) for r in rows] == retained)
        check(f"{kind}_table_count", len(rows) == data["table_pair_counts"][kind])
        for row in rows:
            n, d = row["n"], row["d"]
            lower, upper = intervals[n, d]
            check(f"{kind}_volume_bound_{n}_{d}", Q(row["volume_upper_display"]) >= upper)
            value = mp.log((mpq(lower) + mpq(upper)) / 2) / n
            if kind == "integral":
                value += d * mp.log(2)
            check(f"{kind}_h_rounding_{n}_{d}",
                  abs(value - mpq(Q(row["h_display"]))) < mp.mpf("0.0000005"))
        rank_bounds = [max((n for n, degree in retained if degree == d), default=0)
                       for d in range(1, 15)]
        degree_bounds = [max((d for rank, d in retained if rank == n), default=0)
                         for n in range(1, 35)]
        check(f"{kind}_rank_bounds", rank_bounds == data["rank_bounds_by_degree"][kind])
        check(f"{kind}_degree_bounds", degree_bounds == data["degree_bounds_by_rank"][kind])

    triples = [(a, b, c) for a in range(2, 8) for b in range(a // 2 + 1)
               for c in range(a, 8) if rho(a, b, c) < 2]
    check("twenty_two_reduced_gram_triples", len(triples) == 22 and
          [list(t) for t in triples] == data["reduced_gram_triples"])
    candidates = [(m, a, b, c, (a * c - b * b) // fundamental_discriminant(m))
                  for m in range(2, 22)
                  if all(exponent == 1 for exponent in sp.factorint(m).values())
                  for a, b, c in triples
                  if (a * c - b * b) % fundamental_discriminant(m) == 0
                  and (m % 4 == 1 or a % 2 == b % 2 == c % 2 == 0)]
    check("nine_field_gram_candidates", len(candidates) == 9 and
          [list(t) for t in candidates] == data["field_gram_candidates"])

    surviving = []
    for m, a, b, c, norm in candidates:
        delta = fundamental_discriminant(m)
        solutions = [(t, k) for t in range(-a, a + 1) for k in range(1, a + 1)
                     if (a - delta * t) % 2 == 0 and a * a - delta * t * t == 4 * norm * k * k]
        if solutions:
            surviving.append((m, a, b, c, norm))
        if m != 3:
            check(f"index_one_{m}_{a}_{b}_{c}", all(k == 1 for _, k in solutions))
    check("six_surviving_gram_candidates", len(surviving) == 6)
    representative_rows = [(r["m"], *r["gram"],
                            (r["gram"][0] * r["gram"][2] - r["gram"][1] ** 2)
                            // fundamental_discriminant(r["m"]))
                           for r in data["representatives"]]
    check("six_representatives_match_survivors", sorted(representative_rows) == sorted(surviving))
    for i, rep in enumerate(data["representatives"], 1):
        a, b, c = rep["gram"]
        check(f"representative_radius_{i}", rho(a, b, c) == Q(rep["radius"]) < 2)

    output = {
        "source_sha256": paper["sha256"],
        "checks": len(checks),
        "pass": sum(checks.values()),
        "fail": len(checks) - sum(checks.values()),
        "classic_pairs": len(pairs["classic"]),
        "integral_pairs": len(pairs["integral"]),
        "gram_triples": len(triples),
        "field_candidates": len(candidates),
        "surviving_candidates": len(surviving),
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
