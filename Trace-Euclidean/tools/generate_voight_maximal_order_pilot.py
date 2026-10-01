#!/usr/bin/env python3
"""Generate a Lean maximal-order certificate for one archived Voight row.

The pilot exercises the full certificate path on the first nonsquarefree row
with nontrivial power-order index (degree 5, archived row 85).  All discovery
computations use exact rational or finite-field arithmetic; Lean rechecks the
emitted identities.
"""

from __future__ import annotations

import json
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path
from typing import Iterable

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results" / "voight-nonsquarefree-basis-matrices.json"
OUTPUT = ROOT / "lean" / "TraceEuclidean" / "VoightMaximalOrderPilot.lean"
TARGET_DEGREE = 5
TARGET_ROW = 85
X = sp.symbols("x")


def trim(values: Iterable[int]) -> list[int]:
    out = list(values)
    while out and out[-1] == 0:
        out.pop()
    return out


def as_fraction(pair: list[int]) -> Fraction:
    return Fraction(pair[0], pair[1])


def identity(n: int, *, fraction: bool = True) -> list[list[Fraction | int]]:
    cast = Fraction if fraction else int
    return [[cast(i == j) for j in range(n)] for i in range(n)]


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def matrix_inverse(matrix: list[list[Fraction]]) -> list[list[Fraction]]:
    n = len(matrix)
    work = [row[:] + identity(n)[i] for i, row in enumerate(matrix)]
    for column in range(n):
        pivot = next(i for i in range(column, n) if work[i][column])
        work[column], work[pivot] = work[pivot], work[column]
        scale = work[column][column]
        work[column] = [value / scale for value in work[column]]
        for row in range(n):
            if row == column or not work[row][column]:
                continue
            scale = work[row][column]
            work[row] = [a - scale * b for a, b in zip(work[row], work[column])]
    return [row[n:] for row in work]


def matrix_mul(left, right):
    return [
        [sum(left[i][k] * right[k][j] for k in range(len(right)))
         for j in range(len(right[0]))]
        for i in range(len(left))
    ]


def matrix_vec(matrix, vector):
    return [sum(a * b for a, b in zip(row, vector)) for row in matrix]


def field_mul(left: list[Fraction], right: list[Fraction], defining: list[int]) -> list[Fraction]:
    n = len(defining) - 1
    result = [Fraction(0) for _ in range(2 * n - 1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    for degree in range(2 * n - 2, n - 1, -1):
        leading = result[degree]
        if leading:
            for i in range(n):
                result[degree - n + i] -= leading * defining[i]
    return result[:n]


def field_pow(value: list[Fraction], exponent: int, defining: list[int]) -> list[Fraction]:
    result = [Fraction(1)] + [Fraction(0)] * (len(value) - 1)
    base = value
    while exponent:
        if exponent & 1:
            result = field_mul(result, base, defining)
        base = field_mul(base, base, defining)
        exponent //= 2
    return result


def rref_mod(matrix: list[list[int]], prime: int, augment=None):
    left_columns = len(matrix[0])
    work = [[value % prime for value in row] for row in matrix]
    if augment is not None:
        work = [
            row + [value % prime for value in extra]
            for row, extra in zip(work, augment)
        ]
    row = 0
    pivots: list[int] = []
    for column in range(left_columns):
        pivot = next(
            (i for i in range(row, len(work)) if work[i][column] % prime),
            None,
        )
        if pivot is None:
            continue
        work[row], work[pivot] = work[pivot], work[row]
        inverse_pivot = pow(work[row][column], -1, prime)
        work[row] = [(inverse_pivot * value) % prime for value in work[row]]
        for i in range(len(work)):
            if i == row or not work[i][column]:
                continue
            scale = work[i][column]
            work[i] = [
                (a - scale * b) % prime for a, b in zip(work[i], work[row])
            ]
        pivots.append(column)
        row += 1
        if row == len(work):
            break
    return work, pivots


def nullspace_mod(matrix: list[list[int]], prime: int):
    reduced, pivots = rref_mod(matrix, prime)
    free = [j for j in range(len(matrix[0])) if j not in pivots]
    basis = []
    for free_column in free:
        vector = [0] * len(matrix[0])
        vector[free_column] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = -reduced[i][free_column] % prime
        basis.append(vector)
    return basis, free, pivots


def solve_mod(matrix: list[list[int]], vector: list[int], prime: int) -> list[int]:
    reduced, pivots = rref_mod(matrix, prime, [[x] for x in vector])
    if any(all(value % prime == 0 for value in row[:len(matrix[0])]) and row[-1]
           for row in reduced):
        raise ArithmeticError("inconsistent modular system")
    solution = [0] * len(matrix[0])
    for i, pivot in enumerate(pivots):
        solution[pivot] = reduced[i][-1]
    check = [
        sum(matrix[i][j] * solution[j] for j in range(len(solution))) % prime
        for i in range(len(matrix))
    ]
    if check != [x % prime for x in vector]:
        raise ArithmeticError("modular solve verification failed")
    return solution


def fraction_mod(value: Fraction, prime: int) -> int:
    """Reduce a rational number whose denominator is a p-adic unit mod p."""
    denominator = value.denominator % prime
    if denominator == 0:
        raise ArithmeticError("rational coefficient has p-divisible denominator")
    return (value.numerator % prime) * pow(denominator, -1, prime) % prime


def poly(coefficients: list[int], modulus=None) -> sp.Poly:
    domain = sp.ZZ if modulus is None else sp.GF(modulus)
    return sp.Poly(sum(value * X**i for i, value in enumerate(coefficients)), X, domain=domain)


def poly_coefficients(value: sp.Poly, modulus=None) -> list[int]:
    if value.is_zero:
        return []
    out = [int(value.nth(i)) for i in range(value.degree() + 1)]
    if modulus is not None:
        out = [entry % modulus for entry in out]
    return trim(out)


def lift_mod_poly(value: sp.Poly, prime: int) -> sp.Poly:
    return poly(poly_coefficients(value, prime))


def dedekind_local_certificate(defining: list[int], prime: int):
    f_int = poly(defining)
    f_mod = poly(defining, prime)
    factors = sp.factor_list(f_mod)[1]
    radical = sp.Poly(1, X, modulus=prime)
    exponent = 0
    for factor, multiplicity in factors:
        radical *= factor
        exponent = max(exponent, multiplicity)
    h = f_mod.exquo(radical)
    k = (radical**exponent).exquo(f_mod)
    aprime, bprime, squarefree_gcd = sp.gcdex(radical, radical.diff())
    if squarefree_gcd.degree() != 0:
        raise ArithmeticError("radical squarefreeness certificate failed")
    unit = int(squarefree_gcd.nth(0)) % prime
    inverse_unit = pow(unit, -1, prime)
    aprime *= inverse_unit
    bprime *= inverse_unit

    radical_lift = lift_mod_poly(radical, prime)
    h_lift = lift_mod_poly(h, prime)
    numerator = radical_lift * h_lift - f_int
    quotient, remainder = sp.div(numerator, sp.Poly(prime, X, domain=sp.ZZ))
    if not remainder.is_zero:
        raise ArithmeticError("Dedekind correction is not integral")

    at, bt, first_gcd = sp.gcdex(sp.Poly(quotient, X, modulus=prime), radical)
    at2, c, final_gcd = sp.gcdex(first_gcd, h)
    if final_gcd.degree() != 0:
        return None
    unit = int(final_gcd.nth(0)) % prime
    inverse_unit = pow(unit, -1, prime)
    at2 *= inverse_unit
    c *= inverse_unit
    a = at2 * at
    b = at2 * bt
    return {
        "prime": prime,
        "n": exponent,
        "a_prime": poly_coefficients(aprime, prime),
        "b_prime": poly_coefficients(bprime, prime),
        "k": poly_coefficients(k, prime),
        "f": poly_coefficients(quotient),
        "g": poly_coefficients(radical, prime),
        "h": poly_coefficients(h, prime),
        "a": poly_coefficients(a, prime),
        "b": poly_coefficients(b, prime),
        "c": poly_coefficients(c, prime),
    }


def dedekind_global_certificate(defining: list[int]):
    defining_poly = poly(defining)
    a_rat, b_rat, result = sp.gcdex(defining_poly, defining_poly.diff())
    if result != 1:
        a_rat = a_rat.exquo_ground(result.nth(0))
        b_rat = b_rat.exquo_ground(result.nth(0))
    denominators = [
        int(coefficient.q)
        for value in (a_rat, b_rat)
        for coefficient in value.all_coeffs()
    ]
    integer = 1
    for denominator in denominators:
        integer = lcm(integer, denominator)
    a_int = sp.Poly(a_rat * integer, X, domain=sp.ZZ)
    b_int = sp.Poly(b_rat * integer, X, domain=sp.ZZ)
    if a_int * defining_poly + b_int * defining_poly.diff() != integer:
        raise ArithmeticError("global Bezout identity failed")
    if integer < 0:
        integer = -integer
        a_int = -a_int
        b_int = -b_int
    factorization = sp.factorint(integer)
    locals_ = []
    good = []
    bad = []
    for prime in factorization:
        certificate = dedekind_local_certificate(defining, prime)
        if certificate is None:
            bad.append(prime)
        else:
            good.append(prime)
            locals_.append(certificate)
    return {
        "integer": integer,
        "primes": list(factorization),
        "exponents": list(factorization.values()),
        "a": poly_coefficients(a_int),
        "b": poly_coefficients(b_int),
        "good": good,
        "bad": bad,
        "locals": locals_,
    }


def build_order(record: dict):
    n = record["degree"]
    basis = [[as_fraction(value) for value in row] for row in record["matrix"]]
    basis_inverse = matrix_inverse(basis)
    basis_columns = transpose(basis)
    denominator = 1
    for row in basis:
        for value in row:
            denominator = lcm(denominator, value.denominator)
    numerator_columns = [
        [int(denominator * value) for value in column]
        for column in basis_columns
    ]
    if numerator_columns[0] != [denominator] + [0] * (n - 1):
        raise ArithmeticError("the first integral-basis vector is not one")
    for i in range(n):
        for j in range(i):
            if numerator_columns[j][i] != 0:
                raise ArithmeticError("basis numerator matrix is not upper triangular")

    table = []
    for left in basis_columns:
        table_row = []
        for right in basis_columns:
            coordinates = matrix_vec(
                basis_inverse,
                field_mul(left, right, record["coefficients"]),
            )
            if any(value.denominator != 1 for value in coordinates):
                raise ArithmeticError("candidate basis is not multiplicatively closed")
            table_row.append([int(value) for value in coordinates])
        table.append(table_row)

    defining_poly = poly(record["coefficients"])
    correction = []
    for i in range(n):
        correction_row = []
        left = poly(numerator_columns[i])
        for j in range(n):
            right = poly(numerator_columns[j])
            target = sp.Poly(0, X, domain=sp.ZZ)
            for k in range(n):
                target += poly(numerator_columns[k]) * (denominator * table[i][j][k])
            quotient, remainder = sp.div(target - left * right, defining_poly)
            if not remainder.is_zero:
                raise ArithmeticError("times-table correction is not divisible by T")
            correction_row.append(poly_coefficients(quotient))
        correction.append(correction_row)

    alpha = [Fraction(0), Fraction(1)] + [Fraction(0)] * (n - 2)
    alpha_coordinates = matrix_vec(basis_inverse, alpha)
    if any(value.denominator != 1 for value in alpha_coordinates):
        raise ArithmeticError("alpha is not in the candidate order")
    alpha_coordinates = [int(value) for value in alpha_coordinates]
    alpha_numerator = sp.Poly(0, X, domain=sp.ZZ)
    for coefficient, vector in zip(alpha_coordinates, numerator_columns):
        alpha_numerator += coefficient * poly(vector)
    root_quotient, root_remainder = sp.div(
        sp.Poly(denominator * X, X, domain=sp.ZZ) - alpha_numerator,
        defining_poly,
    )
    if not root_remainder.is_zero:
        raise ArithmeticError("root membership certificate failed")

    return {
        "basis": basis,
        "basis_inverse": basis_inverse,
        "basis_columns": basis_columns,
        "denominator": denominator,
        "numerator_columns": numerator_columns,
        "table": table,
        "correction": correction,
        "alpha_coordinates": alpha_coordinates,
        "root_quotient": poly_coefficients(root_quotient),
    }


def maximality_certificate(record: dict, order: dict, prime: int):
    n = record["degree"]
    basis = order["basis"]
    basis_inverse = order["basis_inverse"]
    basis_columns = order["basis_columns"]
    exponent = 0
    while prime**exponent < n:
        exponent += 1
    frobenius_power = prime**exponent
    powered = [
        field_pow(value, frobenius_power, record["coefficients"])
        for value in basis_columns
    ]
    coefficients_q = matrix_mul(basis_inverse, transpose(powered))
    if any(value.denominator != 1 for row in coefficients_q for value in row):
        raise ArithmeticError("Frobenius coordinates are not integral")
    coefficients = [[int(value) % prime for value in row] for row in coefficients_q]

    kernel, kernel_pivots, image_source_pivots = nullspace_mod(coefficients, prime)
    transpose_reduced, image_pivots = rref_mod(transpose(coefficients), prime)
    rank = len(image_pivots)
    image_rows = transpose_reduced[:rank]
    image = transpose(image_rows)
    preimages = [solve_mod(coefficients, column, prime) for column in transpose(image)]
    if len(kernel) + rank != n:
        raise ArithmeticError("rank-nullity failed")

    result = {
        "prime": prime,
        "m": len(kernel),
        "n": rank,
        "t": exponent,
        "v": kernel,
        "v_ind": kernel_pivots,
        "w": preimages,
        "w_frob": transpose(image),
        "w_ind": image_pivots,
    }
    if not kernel:
        return result

    radical_columns = kernel + [[prime * x for x in vector] for vector in preimages]
    radical_matrix = transpose(radical_columns)
    radical_power_matrix = matrix_mul(basis, radical_matrix)
    radical_inverse = matrix_inverse(radical_power_matrix)

    endomorphisms = []
    for basis_element in basis_columns:
        product_columns = [
            field_mul(basis_element, vector, record["coefficients"])
            for vector in transpose(radical_power_matrix)
        ]
        endomorphism = matrix_mul(radical_inverse, transpose(product_columns))
        endomorphisms.append(endomorphism)

    flattened = [
        [fraction_mod(value, prime) for row in endomorphism for value in row]
        for endomorphism in endomorphisms
    ]
    reduced_augmented, endomorphism_pivots = rref_mod(
        flattened, prime, identity(n, fraction=False)
    )
    if len(endomorphism_pivots) != n:
        raise ArithmeticError("multiplication endomorphisms are not independent")
    transformation = [row[n*n:] for row in reduced_augmented[:n]]

    exact_endomorphisms = []
    scaled_generators = []
    for generator in transformation:
        element = matrix_vec(basis, [Fraction(x) for x in generator])
        product_columns = [
            field_mul(element, vector, record["coefficients"])
            for vector in transpose(radical_power_matrix)
        ]
        endomorphism = matrix_mul(radical_inverse, transpose(product_columns))
        scale = 1
        for row in endomorphism:
            for value in row:
                scale = lcm(scale, value.denominator)
        if scale % prime == 0:
            raise ArithmeticError("endomorphism denominator is divisible by p")
        scaled_generators.append([scale * value for value in generator])
        exact = [[scale * value for value in row] for row in endomorphism]
        if any(value.denominator != 1 for row in exact for value in row):
            raise ArithmeticError("failed to clear endomorphism denominators")
        exact_endomorphisms.append([[int(value) for value in row] for row in exact])

    a = []
    c = []
    d = []
    e = []
    m = len(kernel)
    for endomorphism in exact_endomorphisms:
        a.append([
            [endomorphism[row][column] for row in range(m)]
            for column in range(m)
        ])
        c.append([
            [endomorphism[row][column] for row in range(m, n)]
            for column in range(m)
        ])
        d.append([
            [endomorphism[row][column] for row in range(m)]
            for column in range(m, n)
        ])
        e.append([
            [endomorphism[row][column] for row in range(m, n)]
            for column in range(m, n)
        ])

    result.update({
        "g": [[int(value) for value in row] for row in scaled_generators],
        "a": a,
        "c": c,
        "d": d,
        "e": e,
        "endomorphism_pivots": endomorphism_pivots,
    })
    return result


def lean_list(value) -> str:
    if isinstance(value, list):
        return "[" + ", ".join(lean_list(item) for item in value) + "]"
    return str(value)


def lean_vector(value) -> str:
    if not isinstance(value, list):
        return str(value)
    return "![" + ", ".join(lean_vector(item) if isinstance(item, list) else str(item)
                              for item in value) + "]"


def lean_vector_to_lists(value, function_depth: int) -> str:
    """Emit nested Lean functions whose values at the leaves are Lists.

    Lean's `![...]` syntax denotes a function on `Fin n`, whereas ordinary
    `[...]` syntax denotes a `List`.  Several certificate fields have types
    such as `Fin n → Fin n → List ℤ`, so blindly emitting vectors at every
    nesting level changes the leaf type.
    """
    if function_depth == 0:
        return lean_list(value)
    if not isinstance(value, list):
        raise TypeError("expected one list dimension for each function argument")
    return "![" + ", ".join(
        lean_vector_to_lists(item, function_depth - 1) for item in value
    ) + "]"


def sum_index(index: int, m: int) -> str:
    return f"Sum.inl {index}" if index < m else f"Sum.inr {index - m}"


def emit_maximality(
    degree: int, order: dict, prime: int, maximality: dict,
) -> list[str]:
    """Emit one local p-maximality certificate."""
    m = maximality["m"]
    rank = maximality["n"]
    table_mod = [
        [[entry % prime for entry in value] for value in row]
        for row in order["table"]
    ]
    if m == 0:
        return [
            f"noncomputable def M{prime} : "
            f"MaximalOrderCertificateOfUnramifiedLists {prime} O Om hm where",
            f"  n := {rank}",
            f"  t := {maximality['t']}",
            "  hpos := by decide",
            "  TT := timesTableO",
            "  B' := B'",
            "  T := Table",
            "  heq := timesTableO_eq_Table",
            f"  TMod := {lean_vector_to_lists(table_mod, 2)}",
            "  hTMod := by decide",
            "  hle := by decide",
            f"  w := {lean_vector(maximality['w'])}",
            f"  wFrob := {lean_vector(maximality['w_frob'])}",
            f"  w_ind := {lean_vector(maximality['w_ind'])}",
            "  hindw := by decide",
            "  hwFrobComp := by decide",
            "",
        ]

    indices = []
    for pivot in maximality["endomorphism_pivots"]:
        output = pivot // degree
        input_ = pivot % degree
        indices.append(
            f"({sum_index(input_, m)}, {sum_index(output, m)})"
        )
    return [
        f"noncomputable def M{prime} : MaximalOrderCertificateLists "
        f"{prime} O Om hm where",
        f"  m := {m}",
        f"  n := {rank}",
        f"  t := {maximality['t']}",
        "  hpos := by decide",
        "  TT := timesTableO",
        "  B' := B'",
        "  T := Table",
        "  heq := timesTableO_eq_Table",
        f"  TMod := {lean_vector_to_lists(table_mod, 2)}",
        "  hTMod := by decide",
        "  hle := by decide",
        f"  b1 := {lean_vector(maximality['v'])}",
        f"  b2 := {lean_vector(maximality['w'])}",
        f"  v := {lean_vector(maximality['v'])}",
        f"  w := {lean_vector(maximality['w'])}",
        f"  wFrob := {lean_vector(maximality['w_frob'])}",
        f"  v_ind := {lean_vector(maximality['v_ind'])}",
        f"  w_ind := {lean_vector(maximality['w_ind'])}",
        "  hmod1 := by decide",
        "  hmod2 := by decide",
        "  hindv := by decide",
        "  hindw := by decide",
        "  hvFrobKer := by decide",
        "  hwFrobComp := by decide",
        f"  g := {lean_vector(maximality['g'])}",
        f"  a := {lean_vector(maximality['a'])}",
        f"  c := {lean_vector(maximality['c'])}",
        f"  d := {lean_vector(maximality['d'])}",
        f"  e := {lean_vector(maximality['e'])}",
        "  ab_ind := ![" + ", ".join(indices) + "]",
        "  hindab := by decide",
        "  hmul1 := by decide",
        "  hmul2 := by decide",
        "",
    ]


DEGREE_WORD = {
    5: "Five",
    6: "Six",
    7: "Seven",
    8: "Eight",
    9: "Nine",
    10: "Ten",
}


def emit(
    record: dict,
    order: dict,
    dedekind: dict,
    maximalities: dict[int, dict],
    namespace: str | None = None,
) -> str:
    n = record["degree"]
    bad = dedekind["bad"]
    if bad != list(maximalities):
        raise ArithmeticError(
            f"maximality certificates {list(maximalities)} do not cover {bad}"
        )
    if namespace is None:
        namespace = (
            f"VoightMaximalOrderD{n}R{record['row_number']}"
        )
    degree_word = DEGREE_WORD[n]
    lines = [
        "import TraceEuclidean.VoightAllIrreducible",
        "import TraceEuclidean.VoightIntegralBasisCertificate",
        "import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertifyAdjoinRootCore",
        "import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.MaximalAPI",
        "import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertificateDedekind",
        "import Mathlib.Tactic",
        "",
        "set_option linter.all false",
        "set_option maxHeartbeats 5000000",
        "",
        "namespace TraceEuclidean",
        f"namespace {namespace}",
        "",
        "open Polynomial Module BigOperators Classical Matrix",
        "",
        "noncomputable section",
        "",
        f"def row : VoightPolynomialRow := ⟨{record['field_discriminant']}, "
        f"{lean_list(record['coefficients'])}, {record['index']}⟩",
        f"local notation \"l\" => {lean_list(record['coefficients'])}",
        "noncomputable def T : ℤ[X] := row.polynomial",
        "lemma T_ofList : ofList l = T := by rfl",
        f"lemma row_mem : row ∈ voightPolynomialRows{degree_word} := by native_decide",
        "lemma T_irreducible : Irreducible T :=",
        f"  voightPolynomialRows{degree_word}_irreducible row row_mem",
        "lemma T_monic : Monic T := by",
        "  rw [← T_ofList]",
        "  exact monic_ofList l rfl",
        "",
        "abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)",
        "instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where",
        "  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1",
        "    T_irreducible",
        "instance KField : Field K := AdjoinRoot.instField",
        "instance : Algebra ℤ K := Ring.toIntAlgebra K",
        "instance : IsScalarTower ℤ ℚ K :=",
        "  IsScalarTower.of_algebraMap_eq' (by ext; simp)",
        "noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=",
        "  AdjoinRoot.isAdjoinRoot _",
        "local notation \"θ\" => Adj.root",
        "",
        f"def basisDenominator : ℤ := {order['denominator']}",
        f"def basisNumerator : Fin {n} → Fin {n} → ℤ := "
        f"{lean_vector(order['numerator_columns'])}",
        "",
        f"noncomputable def BQ : SubalgebraBuilderLists {n} ℤ ℚ K T l where",
        "  d := basisDenominator",
        "  hlen := rfl",
        "  htr := rfl",
        "  hofL := T_ofList.symm",
        "  hm := rfl",
        "  B := basisNumerator",
        f"  a := {lean_vector(order['table'])}",
        f"  s := {lean_vector_to_lists(order['correction'], 2)}",
        "  h := Adj",
        "  honed := by decide",
        "  hd := by norm_num [basisDenominator]",
        "  hcc := by decide",
        "  hin := by decide",
        "  hsymma := by decide",
        "  hc_le := by decide",
        "",
        f"lemma T_degree : T.natDegree = {n} := (SubalgebraBuilderOfList T l BQ).hdeg",
        "",
        "noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K",
        "noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ",
        "def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)",
        "noncomputable def B' : Basis (Fin " + str(n) + ") ℤ Om :=",
        "  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic",
        "    (Irreducible.prime T_irreducible)) (finCongr T_degree)",
        "instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'",
        "instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'",
        "",
        f"noncomputable def timesTableO : TimesTable (Fin {n}) ℤ O :=",
        "  timesTableOfSubalgebraBuilderLists T l BQ",
        f"lemma timesTableO_basis_apply (i : Fin {n}) :",
        "    ((timesTableO.basis i).val : K) =",
        "      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *",
        "        map (algebraMap ℤ ℚ)",
        "          (ofList (List.ofFn (basisNumerator i)))) := by",
        "  exact basisOfBuilderLists_apply T l BQ i",
        f"def Table : Fin {n} → Fin {n} → List ℤ := "
        f"{lean_vector_to_lists(order['table'], 2)}",
        "lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by",
        "  decide",
        "lemma hroot_mem : θ ∈ O := by",
        f"  exact root_in_subalgebra_lists T l BQ {lean_vector(order['alpha_coordinates'])} "
        f"{lean_list(order['root_quotient'])} (by decide)",
        "",
    ]
    for prime in dedekind["primes"]:
        lines.append(
            f"instance hp{prime} : Fact (Nat.Prime {prime}) := fact_iff.2 (by norm_num)"
        )
    lines.append("")
    for certificate in dedekind["locals"]:
        prime = certificate["prime"]
        lines += [
            f"def CD{prime} : CertificateDedekindCriterionLists l {prime} where",
            f"  n := {certificate['n']}",
            f"  a' := {lean_list(certificate['a_prime'])}",
            f"  b' := {lean_list(certificate['b_prime'])}",
            f"  k := {lean_list(certificate['k'])}",
            f"  f := {lean_list(certificate['f'])}",
            f"  g := {lean_list(certificate['g'])}",
            f"  h := {lean_list(certificate['h'])}",
            f"  a := {lean_list(certificate['a'])}",
            f"  b := {lean_list(certificate['b'])}",
            f"  c := {lean_list(certificate['c'])}",
            "  hdvdpow := rfl",
            "  hcop := rfl",
            "  hf := by rfl",
            "  habc := by rfl",
            "",
        ]
    lines += [
        f"noncomputable def D : CertificateDedekindAlmostAllLists T l {lean_list(bad)} where",
        f"  n := {len(dedekind['primes'])}",
        f"  p := {lean_vector(dedekind['primes'])}",
        f"  exp := {lean_vector(dedekind['exponents'])}",
        f"  pdgood := {lean_list(dedekind['good'])}",
        "  hsub := by decide",
        "  hp := by",
        "    intro i",
        "    fin_cases i",
    ]
    for prime in dedekind["primes"]:
        lines.append(f"    exact hp{prime}.out")
    lines += [
        f"  a := {lean_list(dedekind['a'])}",
        f"  b := {lean_list(dedekind['b'])}",
        "  hab := by decide",
        "  hd := by",
        "    intro q hq",
        "    fin_cases hq",
    ]
    for prime in dedekind["good"]:
        lines.append(
            f"    exact satisfiesDedekindCriterion_of_certificate_lists T l {prime} T_ofList CD{prime}"
        )
    lines.append("")

    for prime in bad:
        lines += emit_maximality(n, order, prime, maximalities[prime])

    theorem_name = "candidate_order_eq_integralClosure"
    lines += [
        f"theorem {theorem_name} : O = integralClosure ℤ K := by",
        "  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_",
        "  intro q hq",
        f"  by_cases hbad : q ∈ {lean_list(bad)}",
        "  · fin_cases hbad",
    ]
    for prime in bad:
        if maximalities[prime]["m"] == 0:
            cert_theorem = (
                "pMaximal_of_MaximalOrderCertificateOfUnramifiedLists"
            )
        else:
            cert_theorem = "pMaximal_of_MaximalOrderCertificateLists"
        lines.append(
            f"    exact @{cert_theorem} K {prime} _ "
            "IsAddTorsionFree.to_noZeroSMulDivisors_int _ "
            f"O Om hm _ _ M{prime}"
        )
    lines += [
        "  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq",
        "    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int",
        "      Adj T_monic hm ?_ hroot_mem",
        f"      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList {lean_list(bad)} D q hq hbad)",
        "    rw [T_degree, rank_subalgebra_eq_card_basis Om B']",
        "",
        f"noncomputable def bOm : Basis (Fin {n}) ℤ "
        "(NumberField.RingOfIntegers K) :=",
        "  timesTableO.basis.map",
        "    (Subalgebra.equivOfEq O Om "
        "candidate_order_eq_integralClosure).toLinearEquiv",
        "",
        "lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=",
        "  NumberField.discr_eq_discr K bOm",
        "",
        "noncomputable def pb : PowerBasis ℚ K :=",
        "  AdjoinRoot.powerBasis hirr.out.ne_zero",
        "",
        f"lemma pb_dim : pb.dim = {n} := by",
        f"  change (map (algebraMap ℤ ℚ) T).natDegree = {n}",
        "  calc",
        "    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=",
        "      T_monic.natDegree_map (algebraMap ℤ ℚ)",
        f"    _ = {n} := T_degree",
        "",
        f"noncomputable def bQ : Basis (Fin {n}) ℚ K :=",
        "  pb.basis.reindex (finCongr pb_dim)",
        "",
        "lemma pb_gen : pb.gen = Adj.root := by",
        "  unfold pb",
        "  rw [AdjoinRoot.powerBasis_gen]",
        "  exact (AdjoinRoot.isAdjoinRoot_root_eq_root",
        "    (map (algebraMap ℤ ℚ) T)).symm",
        "",
        f"def P : Matrix (Fin {n}) (Fin {n}) ℚ :=",
        "  fun i j => (basisNumerator j i : ℚ) / "
        "(basisDenominator : ℚ)",
        "",
        f"lemma bQ_apply (i : Fin {n}) :",
        "    bQ i = Adj.root ^ (i : ℕ) := by",
        "  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by",
        "    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]",
        "  rw [pb.basis_eq_pow, pb_gen]",
        "  congr 1",
        "",
        "lemma bOm_cast_eq_vecMul :",
        "    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =",
        "      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by",
        "  funext j",
        "  change (timesTableO.basis j).val = _",
        "  rw [timesTableO_basis_apply]",
        "  rw [ofList_eq_sum']",
        "  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,",
        "    Polynomial.map_pow, Polynomial.map_X]",
        "  rw [_root_.map_mul, _root_.map_sum]",
        "  rw [← IsAdjoinRoot.algebraMap_apply Adj]",
        "  have hdist :",
        "      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *",
        f"          (∑ x : Fin {n},",
        "            Adj.map (C ((algebraMap ℤ ℚ) "
        "(basisNumerator j x)) * X ^ (x : ℕ))) =",
        f"        ∑ x : Fin {n},",
        "          (algebraMap ℚ K) ((algebraMap ℤ ℚ) "
        "basisDenominator)⁻¹ *",
        "            Adj.map (C ((algebraMap ℤ ℚ) "
        "(basisNumerator j x)) * X ^ (x : ℕ)) := by",
        "    exact Finset.mul_sum Finset.univ _ _",
        "  rw [hdist]",
        "  rw [Matrix.vecMul_apply_eq_sum]",
        "  apply Finset.sum_congr rfl",
        "  intro i hi",
        "  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,",
        "    _root_.map_pow, IsAdjoinRoot.map_X Adj]",
        "  rw [bQ_apply]",
        "  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]",
        "",
        "lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by",
        "  calc",
        "    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by",
        "      simpa [bQ] using",
        "        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)",
        "    _ = (minpoly ℚ pb.gen).discr :=",
        "      powerBasis_discr_eq_minpoly_discr pb",
        "    _ = (map (algebraMap ℤ ℚ) T).discr := by",
        "      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=",
        "        T_monic.map (algebraMap ℤ ℚ)",
        "      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by",
        "        rw [pb_gen]",
        "        calc",
        "          minpoly ℚ Adj.root =",
        "              map (algebraMap ℤ ℚ) T *",
        "                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=",
        "            AdjoinRoot.minpoly_root hirr.out.ne_zero",
        "          _ = map (algebraMap ℤ ℚ) T := by",
        "            rw [hqmonic.leadingCoeff]",
        "            simp]",
        "    _ = (T.discr : ℚ) := by",
        "      exact (intCast_discr_eq_discr_map T T_monic",
        "        (T_degree ▸ by norm_num)).symm",
        "",
        "lemma P_det_index_sq :",
        "    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by",
        "  have htriangular : P.BlockTriangular id := by",
        "    have hcheck :",
        f"        (List.ofFn fun i : Fin {n} =>",
        f"          (List.ofFn fun j : Fin {n} =>",
        "            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =",
        "          true := by native_decide",
        "    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,",
        "      decide_eq_true_eq] at hcheck",
        "    intro i j hji",
        "    exact hcheck i j hji",
        "  rw [Matrix.det_of_upperTriangular htriangular]",
        "  native_decide",
        "",
        "theorem field_discriminant_eq_recorded :",
        "    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by",
        "  apply Rat.intCast_injective",
        "  have hbOmCast :",
        "      ((NumberField.discr K : ℤ) : ℚ) =",
        "        Algebra.discr ℚ",
        "          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by",
        "    rw [← bOm_discr]",
        "    exact discr_ringOfIntegers_cast K bOm",
        "  have hrecorded :",
        "      T.discr = (row.index : ℤ) ^ 2 *",
        "        (row.fieldDiscriminant : ℤ) := by",
        "    simpa [T] using",
        f"      (voightPolynomialDiscriminantInput {n} row row_mem)",
        "  have hrecordedQ :",
        "      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *",
        "        (row.fieldDiscriminant : ℚ) := by",
        "    exact_mod_cast hrecorded",
        "  calc",
        "    ((NumberField.discr K : ℤ) : ℚ) =",
        "        Algebra.discr ℚ",
        "          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=",
        "      hbOmCast",
        "    _ = Algebra.discr ℚ",
        "        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by",
        "      rw [bOm_cast_eq_vecMul]",
        "    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=",
        "      Algebra.discr_of_matrix_vecMul bQ P",
        "    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]",
        "    _ = P.det ^ 2 *",
        "        ((row.index : ℚ) ^ 2 *",
        "          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]",
        "    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *",
        "        (row.fieldDiscriminant : ℚ) := by ring",
        "    _ = (row.fieldDiscriminant : ℚ) := by",
        "      rw [P_det_index_sq, one_mul]",
        "",
        "end",
        "",
        f"end {namespace}",
        "end TraceEuclidean",
        "",
    ]
    return "\n".join(lines)


def main() -> None:
    payload = json.loads(SOURCE.read_text(encoding="utf-8"))
    record = next(
        item for item in payload["records"]
        if item["degree"] == TARGET_DEGREE and item["row_number"] == TARGET_ROW
    )
    order = build_order(record)
    dedekind = dedekind_global_certificate(record["coefficients"])
    maximalities = {
        prime: maximality_certificate(record, order, prime)
        for prime in dedekind["bad"]
    }
    text = emit(
        record,
        order,
        dedekind,
        maximalities,
        namespace="VoightMaximalOrderPilot",
    )
    OUTPUT.write_text(text, encoding="utf-8")
    print(
        "VOIGHT MAXIMAL-ORDER PILOT: generated",
        f"degree={TARGET_DEGREE}",
        f"row={TARGET_ROW}",
        f"bad={dedekind['bad']}",
        "local_dimensions=" + str({
            prime: (certificate["m"], certificate["n"])
            for prime, certificate in maximalities.items()
        }),
        f"output={OUTPUT}",
    )


if __name__ == "__main__":
    main()
