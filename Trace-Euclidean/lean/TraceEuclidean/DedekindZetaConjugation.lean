import TraceEuclidean.DedekindZetaZeros
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Conjugation symmetry of a regularized Dedekind zeta function

The ideal-count coefficients of the Dedekind zeta Dirichlet series are
nonnegative integers. Complex conjugation therefore commutes with the series
on its defining half-plane. The analytic identity theorem propagates that
symmetry to any entire continuation of `(s - 1) * ζ_K(s)`.
-/

namespace TraceEuclidean

noncomputable section

open Complex
open scoped ComplexConjugate NumberField

/-- A Dirichlet series with natural-number coefficients has conjugation
symmetry, including at arguments where its `tsum` takes the fallback value. -/
theorem LSeries_conj_natCoeff (a : ℕ → ℕ) (s : ℂ) :
    LSeries (fun n ↦ (a n : ℂ)) (conj s) =
      conj (LSeries (fun n ↦ (a n : ℂ)) s) := by
  simp only [LSeries, conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      map_div₀, conj_natCast]
    have hpow : (n : ℂ) ^ conj s = conj ((n : ℂ) ^ s) := by
      simpa using (conj_cpow (n : ℂ) (conj s)
        (by rw [natCast_arg]; positivity))
    rw [hpow]

/-- The defining ideal-norm series itself commutes with conjugation. -/
theorem dedekindZeta_conj (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    NumberField.dedekindZeta K (conj s) =
      conj (NumberField.dedekindZeta K s) :=
  LSeries_conj_natCoeff
    (fun n ↦ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) s

variable {K : Type*} [Field K] [NumberField K]

/-- Conjugating an entire regularization at both the input and output
produces another entire regularization of the same right-half-plane series. -/
def DedekindZetaRegularization.conjugate
    (Z : DedekindZetaRegularization K) : DedekindZetaRegularization K where
  value := fun s ↦ conj (Z.value (conj s))
  analytic := by
    apply DifferentiableOn.analyticOnNhd (s := Set.univ) _ isOpen_univ
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    exact differentiableAt_conj_conj_iff.mpr
      (Z.analytic (conj s) (Set.mem_univ _)).differentiableAt
  agrees_right := by
    intro s hs
    have hs' : 1 < (conj s).re := by simpa using hs
    rw [Z.agrees_right (conj s) hs', map_mul, map_sub, map_one,
      dedekindZeta_conj, conj_conj, conj_conj]

/-- Every entire regularization of `(s - 1) ζ_K(s)` automatically has
conjugation symmetry. This removes the separate symmetry input from the
paired-zero reduction. -/
theorem DedekindZetaRegularization.conj_symm
    (Z : DedekindZetaRegularization K) (s : ℂ) :
    Z.value (conj s) = conj (Z.value s) := by
  have h := Z.value_unique Z.conjugate
  have hs := congrFun h (conj s)
  simpa [DedekindZetaRegularization.conjugate] using hs

/-- Repeated derivatives commute with conjugation at both ends. -/
theorem iteratedDeriv_conj_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n (fun s ↦ conj (f (conj s))) =
      fun s ↦ conj (iteratedDeriv n f (conj s)) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      simpa [Function.comp_def] using (deriv_conj_conj (f := iteratedDeriv n f))

/-- Complex conjugation preserves the analytic order, hence the
multiplicity, of every zero of a regularized Dedekind zeta function. -/
theorem DedekindZetaRegularization.order_conj
    (Z : DedekindZetaRegularization K) (s : ℂ) :
    analyticOrderAt Z.value (conj s) = analyticOrderAt Z.value s := by
  let n := analyticOrderNatAt Z.value (conj s)
  have hfinite := Z.order_ne_top (conj s)
  have hsrc : analyticOrderAt Z.value (conj s) = (n : ℕ∞) := by
    exact (Nat.cast_analyticOrderNatAt hfinite).symm
  have han := Z.analytic (conj s) (Set.mem_univ _)
  have hder := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mp hsrc
  have hconj : analyticOrderAt Z.conjugate.value s = (n : ℕ∞) := by
    have hconjAn := Z.conjugate.analytic s (Set.mem_univ _)
    apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hconjAn).mpr
    constructor
    · intro k hk
      change iteratedDeriv k (fun z ↦ conj (Z.value (conj z))) s = 0
      rw [iteratedDeriv_conj_conj]
      simp [hder.1 k hk]
    · change iteratedDeriv n (fun z ↦ conj (Z.value (conj z))) s ≠ 0
      rw [iteratedDeriv_conj_conj]
      simpa using hder.2
  rw [← Z.value_unique Z.conjugate] at hconj
  exact hsrc.trans hconj.symm

theorem DedekindZetaRegularization.orderNat_conj
    (Z : DedekindZetaRegularization K) (s : ℂ) :
    analyticOrderNatAt Z.value (conj s) = analyticOrderNatAt Z.value s := by
  simp only [analyticOrderNatAt, Z.order_conj s]

/-- Conjugation acts on zero occurrences themselves, preserving the slot
within each zero's multiplicity fibre. -/
def DedekindZetaZeroOccurrence.conjugate
    {Z : DedekindZetaRegularization K}
    (o : DedekindZetaZeroOccurrence Z) : DedekindZetaZeroOccurrence Z :=
  ⟨⟨conj o.value, by simpa using o.in_strip⟩,
    Fin.cast (Z.orderNat_conj o.value).symm o.2⟩

@[simp]
theorem DedekindZetaZeroOccurrence.value_conjugate
    {Z : DedekindZetaRegularization K}
    (o : DedekindZetaZeroOccurrence Z) :
    o.conjugate.value = conj o.value := rfl

theorem DedekindZetaZeroOccurrence.conjugate_involutive
    {Z : DedekindZetaRegularization K} :
    Function.Involutive
      (DedekindZetaZeroOccurrence.conjugate (Z := Z)) := by
  intro o
  cases o with
  | mk s i =>
    cases s with
    | mk z hz =>
      simp only [DedekindZetaZeroOccurrence.conjugate,
        DedekindZetaZeroOccurrence.value]
      apply Sigma.ext
      · apply Subtype.ext
        simp
      · apply (Fin.heq_ext_iff (by simp)).2
        rfl

/-- Conjugation is an equivalence of the multiplicity-aware strip-zero
occurrences of any entire regularization. -/
def DedekindZetaZeroOccurrence.conjugateEquiv
    {Z : DedekindZetaRegularization K} :
    DedekindZetaZeroOccurrence Z ≃ DedekindZetaZeroOccurrence Z where
  toFun := DedekindZetaZeroOccurrence.conjugate
  invFun := DedekindZetaZeroOccurrence.conjugate
  left_inv := DedekindZetaZeroOccurrence.conjugate_involutive
  right_inv := DedekindZetaZeroOccurrence.conjugate_involutive

/-- The conjugation involution preserves every finite-height occurrence
set, including zeros on its boundary. -/
theorem DedekindZetaZeroOccurrence.conjugate_mem_boundedSet_iff
    {Z : DedekindZetaRegularization K}
    (o : DedekindZetaZeroOccurrence Z) (T : ℝ) :
    o.conjugate ∈ DedekindZetaZeroOccurrence.boundedSet Z T ↔
      o ∈ DedekindZetaZeroOccurrence.boundedSet Z T := by
  simp [DedekindZetaZeroOccurrence.boundedSet,
    DedekindZetaZeroOccurrence.value_conjugate]

/-- The field-normalized paired-zero series now needs no separate
conjugation premise. The continuation, ordered representative enumeration,
and quantitative HSW count remain explicit inputs. -/
theorem DedekindZetaZeroOccurrence.paired_sum_summable_of_field_HSW_auto
    (Z : DedekindZetaRegularization K)
    (representative : ℕ → DedekindZetaZeroOccurrence Z)
    (hInjective : Function.Injective representative)
    (hOrdered : ∀ i j : ℕ, i ≤ j →
      |(representative i).value.im| ≤ |(representative j).value.im|)
    (hNumeric : DedekindZetaZeroOccurrence.HSWFieldInput Z) :
    (∀ i, Z.value (conj (representative i).value) = 0) ∧
      Summable (fun i ↦
        odlyzkoPhi (representative i).value +
          odlyzkoPhi (conj (representative i).value)) := by
  exact DedekindZetaZeroOccurrence.paired_sum_summable_of_field_HSW
    Z representative hInjective Z.conj_symm hOrdered hNumeric

end
end TraceEuclidean
