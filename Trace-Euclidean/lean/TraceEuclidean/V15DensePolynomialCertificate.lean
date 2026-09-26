import Mathlib

/-!
# Computable dense-polynomial certificates

`Polynomial` deliberately uses noncomputable algebra instances in mathlib.
This module provides a small list-backed polynomial language whose operations
can be replayed by `native_decide`, together with a semantic map to mathlib
polynomials and proofs that the replayed operations have their usual meaning.
-/

namespace TraceEuclidean

open Polynomial

namespace V15DensePolynomial

/-- Coefficientwise addition, retaining harmless trailing zeroes. -/
def add {R : Type*} [Add R] : List R → List R → List R
  | [], right => right
  | left, [] => left
  | leftHead :: leftTail, rightHead :: rightTail =>
      (leftHead + rightHead) :: add leftTail rightTail

/-- Coefficientwise negation. -/
def neg {R : Type*} [Neg R] (values : List R) : List R :=
  values.map (-·)

/-- Coefficientwise subtraction. -/
def sub {R : Type*} [Add R] [Neg R] (left right : List R) : List R :=
  add left (right.map (-·))

/-- Multiply every coefficient by a scalar. -/
def scale {R : Type*} [Mul R] (scalar : R) (values : List R) : List R :=
  values.map (scalar * ·)

/-- Schoolbook multiplication in ascending coefficient order. -/
def mul {R : Type*} [Semiring R] : List R → List R → List R
  | [], _ => []
  | leftHead :: leftTail, right =>
      add (scale leftHead right) (0 :: mul leftTail right)

/-- Natural powers in the dense language. -/
def pow {R : Type*} [Semiring R] (values : List R) : ℕ → List R
  | 0 => [1]
  | exponent + 1 => mul (pow values exponent) values

/-- Product of a list of dense polynomials. -/
def prod {R : Type*} [Semiring R] : List (List R) → List R
  | [] => [1]
  | values :: rest => mul values (prod rest)

/-- Extensional equality of two coefficient lists, ignoring trailing zeroes. -/
def equal {R : Type*} [Zero R] [DecidableEq R]
    (left right : List R) : Bool :=
  (List.range (max left.length right.length)).all fun exponent =>
    decide (left.getD exponent 0 = right.getD exponent 0)

/-- Interpret an ascending coefficient list as a mathlib polynomial. -/
noncomputable def toPolynomial {R : Type*} [Semiring R] : List R → R[X]
  | [] => 0
  | head :: tail => C head + X * toPolynomial tail

@[simp]
theorem toPolynomial_nil {R : Type*} [Semiring R] :
    toPolynomial ([] : List R) = 0 := rfl

@[simp]
theorem toPolynomial_cons {R : Type*} [Semiring R]
    (head : R) (tail : List R) :
    toPolynomial (head :: tail) = C head + X * toPolynomial tail := rfl

@[simp]
theorem coeff_toPolynomial {R : Type*} [Semiring R]
    (values : List R) (exponent : ℕ) :
    (toPolynomial values).coeff exponent = values.getD exponent 0 := by
  induction values generalizing exponent with
  | nil => simp
  | cons head tail induction =>
      cases exponent with
      | zero => simp
      | succ exponent => simp [induction, coeff_X_mul]

@[simp]
theorem toPolynomial_add {R : Type*} [CommSemiring R]
    (left right : List R) :
    toPolynomial (add left right) =
      toPolynomial left + toPolynomial right := by
  induction left generalizing right with
  | nil => simp [add]
  | cons leftHead leftTail induction =>
      cases right with
      | nil => simp [add]
      | cons rightHead rightTail =>
          simp [add, induction]
          ring_nf

@[simp]
theorem toPolynomial_neg {R : Type*} [CommRing R]
    (values : List R) :
    toPolynomial (neg values) = -toPolynomial values := by
  induction values with
  | nil => simp [neg]
  | cons head tail induction =>
      change toPolynomial ((-head) :: neg tail) =
        -(C head + X * toPolynomial tail)
      rw [toPolynomial_cons, induction]
      simp
      ring

@[simp]
theorem toPolynomial_sub {R : Type*} [CommRing R]
    (left right : List R) :
    toPolynomial (sub left right) =
      toPolynomial left - toPolynomial right := by
  change toPolynomial (add left (neg right)) = _
  rw [toPolynomial_add, toPolynomial_neg]
  rfl

@[simp]
theorem toPolynomial_scale {R : Type*} [CommSemiring R]
    (scalar : R) (values : List R) :
    toPolynomial (scale scalar values) =
      C scalar * toPolynomial values := by
  induction values with
  | nil => simp [scale]
  | cons head tail induction =>
      change toPolynomial ((scalar * head) :: scale scalar tail) =
        C scalar * (C head + X * toPolynomial tail)
      rw [toPolynomial_cons, induction]
      simp
      ring

@[simp]
theorem toPolynomial_mul {R : Type*} [CommSemiring R]
    (left right : List R) :
    toPolynomial (mul left right) =
      toPolynomial left * toPolynomial right := by
  induction left with
  | nil => simp [mul]
  | cons head tail induction =>
      simp [mul, induction]
      ring_nf

@[simp]
theorem toPolynomial_pow {R : Type*} [CommSemiring R]
    (values : List R) (exponent : ℕ) :
    toPolynomial (pow values exponent) =
      toPolynomial values ^ exponent := by
  induction exponent with
  | zero => simp [pow]
  | succ exponent induction =>
      simp [pow, induction, pow_succ]

@[simp]
theorem toPolynomial_prod {R : Type*} [CommSemiring R]
    (values : List (List R)) :
    toPolynomial (prod values) =
      (values.map toPolynomial).prod := by
  induction values with
  | nil => simp [prod]
  | cons head tail induction =>
      simp [prod, induction]

/-- A successful dense equality check proves equality of the interpreted
mathlib polynomials. -/
theorem toPolynomial_eq_of_equal {R : Type*}
    [CommSemiring R] [DecidableEq R]
    {left right : List R} (h : equal left right = true) :
    toPolynomial left = toPolynomial right := by
  apply Polynomial.ext
  intro exponent
  simp only [coeff_toPolynomial]
  by_cases hexponent : exponent < max left.length right.length
  · have hentry :=
      (List.all_eq_true.mp h) exponent (List.mem_range.mpr hexponent)
    exact of_decide_eq_true hentry
  · have hbound : max left.length right.length ≤ exponent :=
      Nat.le_of_not_gt hexponent
    have hleft : left.length ≤ exponent :=
      (Nat.le_max_left _ _).trans hbound
    have hright : right.length ≤ exponent :=
      (Nat.le_max_right _ _).trans hbound
    rw [List.getD_eq_default left 0 hleft,
      List.getD_eq_default right 0 hright]

end V15DensePolynomial

end TraceEuclidean
