import TraceEuclidean.V15DegreeTwoDiscriminant
import TraceEuclidean.V15PrimitiveBasis
import TraceEuclidean.V15IdealDeterminant
import Mathlib.NumberTheory.NumberField.Norm

/-!
# Small quadratic field discriminants

This module derives the elementary integral-basis arithmetic needed to remove
the abstract quadratic-radicand input from the imprimitive quartic reduction.
-/

namespace TraceEuclidean

noncomputable section

open Matrix Module Finset
open scoped NumberField nonZeroDivisors

/-- In a quadratic number field, `1` is a primitive vector of the ring of
integers. -/
theorem v15_ringOfIntegers_one_isPrimitive_dim_two
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) :
    V15IsPrimitiveVector (1 : 𝓞 K) := by
  intro a x hax
  have hnorm : a ^ 2 * Algebra.norm ℤ x = 1 := by
    calc
      a ^ 2 * Algebra.norm ℤ x =
          Algebra.norm ℤ (algebraMap ℤ (𝓞 K) a) * Algebra.norm ℤ x := by
        rw [Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hdegree]
      _ = Algebra.norm ℤ (algebraMap ℤ (𝓞 K) a * x) := by
        rw [map_mul]
      _ = Algebra.norm ℤ (a • x) := by rw [Algebra.smul_def]
      _ = 1 := by rw [hax, map_one]
  have hpow : IsUnit (a ^ 2) :=
    isUnit_iff_dvd_one.mpr ⟨Algebra.norm ℤ x, hnorm.symm⟩
  exact (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow

/-- A quadratic ring of integers has an integral basis beginning with `1`. -/
theorem v15_exists_ringOfIntegers_basis_one_dim_two
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) :
    ∃ bz : Basis (Fin 2) ℤ (𝓞 K), bz 0 = 1 := by
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_basis
        (NumberField.RingOfIntegers.basis K)]
      exact (NumberField.RingOfIntegers.rank K).trans hdegree)
  let b : Basis (Fin 2) ℤ (𝓞 K) :=
    (NumberField.RingOfIntegers.basis K).reindex e
  exact v15_exists_fin_two_basis_zero_eq_of_primitive b 1
    (v15_ringOfIntegers_one_isPrimitive_dim_two K hdegree)

/-- The trace of the second vector of an integral basis beginning with `1` is
the second coordinate of its square. -/
theorem v15_quadratic_integral_basis_trace_second
    (K : Type*) [Field K] [NumberField K]
    (b : Basis (Fin 2) ℤ (𝓞 K)) (hb0 : b 0 = 1) :
    Algebra.trace ℚ K (b 1 : K) =
      (b.repr (b 1 * b 1) 1 : ℚ) := by
  let bQ := b.localizationLocalization ℚ ℤ⁰ K
  rw [Algebra.trace_eq_matrix_trace bQ]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, bQ, hb0, ← map_mul]

/-- If `1,w` is an integral basis and
`w^2 = A + B*w`, then the field discriminant is `B^2 + 4*A`. -/
theorem v15_quadratic_integral_basis_discriminant_formula
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2)
    (b : Basis (Fin 2) ℤ (𝓞 K)) (hb0 : b 0 = 1) :
    NumberField.discr K =
      (b.repr (b 1 * b 1) 1) ^ 2 +
        4 * b.repr (b 1 * b 1) 0 := by
  let w : 𝓞 K := b 1
  let A : ℤ := b.repr (w * w) 0
  let B : ℤ := b.repr (w * w) 1
  let bQ := b.localizationLocalization ℚ ℤ⁰ K
  have htracew : Algebra.trace ℚ K (w : K) = (B : ℚ) := by
    simpa [w, B] using v15_quadratic_integral_basis_trace_second K b hb0
  have hsum := b.sum_repr (w * w)
  have hsumK := congrArg (fun z : 𝓞 K ↦ (z : K)) hsum
  have hrelation :
      (w : K) * w = (A : ℚ) + (B : ℚ) * (w : K) := by
    simpa [Fin.sum_univ_two, w, A, B, hb0, add_comm] using hsumK.symm
  have htraceA : Algebra.trace ℚ K ((A : ℚ) : K) = (2 : ℚ) * A := by
    rw [show ((A : ℚ) : K) = algebraMap ℚ K (A : ℚ) by rfl,
      Algebra.trace_algebraMap, hdegree]
    ring
  have htraceBw :
      Algebra.trace ℚ K (((B : ℚ) : K) * (w : K)) =
        (B : ℚ) * Algebra.trace ℚ K (w : K) := by
    rw [show (((B : ℚ) : K) * (w : K)) =
      (B : ℚ) • (w : K) by rw [Algebra.smul_def]; rfl]
    exact map_smul (Algebra.trace ℚ K) (B : ℚ) (w : K)
  have htracewsq :
      Algebra.trace ℚ K ((w : K) * w) =
        (2 : ℚ) * A + B ^ 2 := by
    rw [hrelation, map_add, htraceA, htraceBw, htracew]
    ring
  have htraceOne : Algebra.trace ℚ K (1 : K) = 2 := by
    rw [show (1 : K) = algebraMap ℚ K 1 by simp,
      Algebra.trace_algebraMap, hdegree]
    norm_num
  have hfield := v15_discr_of_integral_basis (F := K) b
  rw [Algebra.discr_def, Matrix.det_fin_two] at hfield
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply] at hfield
  have hformulaQ :
      (NumberField.discr K : ℚ) = (B : ℚ) ^ 2 + 4 * A := by
    rw [hfield]
    simp [hb0, w, htracew, htracewsq, htraceOne]
    ring
  exact_mod_cast hformulaQ

/-- The discriminant of a quadratic number field is congruent to zero or one
modulo four.  This is derived from an integral basis beginning with `1`, so no
classification of quadratic fields is used. -/
theorem v15_quadratic_discriminant_emod_four
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) :
    NumberField.discr K % 4 = 0 ∨ NumberField.discr K % 4 = 1 := by
  obtain ⟨b, hb0⟩ := v15_exists_ringOfIntegers_basis_one_dim_two K hdegree
  let A : ℤ := b.repr (b 1 * b 1) 0
  let B : ℤ := b.repr (b 1 * b 1) 1
  have hdisc : NumberField.discr K = B ^ 2 + 4 * A := by
    simpa [A, B] using
      v15_quadratic_integral_basis_discriminant_formula K hdegree b hb0
  rcases Int.even_or_odd B with ⟨c, hc⟩ | ⟨c, hc⟩
  · left
    rw [hdisc, hc]
    have hfactor : (c + c) ^ 2 + 4 * A = 4 * (c ^ 2 + A) := by ring
    rw [hfactor]
    simp
  · right
    rw [hdisc, hc]
    have hfactor :
        (2 * c + 1) ^ 2 + 4 * A = 4 * (c ^ 2 + c + A) + 1 := by
      ring
    rw [hfactor]
    simp

/-- No quadratic number field has discriminant `20`.  If an integral basis
`1,w` had this discriminant, then after completing the square the element
`alpha = w-c` would satisfy `alpha^2=5`.  The integral element
`(1+alpha)/2` would then have a half-integral second basis coordinate. -/
theorem v15_quadratic_discriminant_ne_twenty
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) :
    NumberField.discr K ≠ 20 := by
  intro htwenty
  obtain ⟨b, hb0⟩ := v15_exists_ringOfIntegers_basis_one_dim_two K hdegree
  let w : 𝓞 K := b 1
  let A : ℤ := b.repr (w * w) 0
  let B : ℤ := b.repr (w * w) 1
  have hdisc : NumberField.discr K = B ^ 2 + 4 * A := by
    simpa [w, A, B] using
      v15_quadratic_integral_basis_discriminant_formula K hdegree b hb0
  have hsum := b.sum_repr (w * w)
  have hsumK := congrArg (fun z : 𝓞 K ↦ (z : K)) hsum
  have hrelation :
      (w : K) * w = (A : K) + (B : K) * (w : K) := by
    simpa [Fin.sum_univ_two, w, A, B, hb0, add_comm] using hsumK.symm
  rcases Int.even_or_odd B with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hAc : A + c ^ 2 = 5 := by
      rw [hdisc, hc] at htwenty
      nlinarith
    let alpha : K := (w : K) - (c : K)
    have halpha : alpha ^ 2 = (5 : K) := by
      calc
        alpha ^ 2 = (w : K) ^ 2 - 2 * (c : K) * (w : K) + (c : K) ^ 2 := by
          simp only [alpha]
          ring
        _ = (A : K) + (c : K) ^ 2 := by
          rw [pow_two (w : K), hrelation, hc]
          push_cast
          ring
        _ = 5 := by exact_mod_cast hAc
    let beta : K := (1 + alpha) / 2
    have hbetaInt : IsIntegral ℤ beta := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C 1, ?_, ?_⟩
      · monicity
        norm_num
      · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        have hidentity : beta ^ 2 - beta - 1 = (alpha ^ 2 - 5) / 4 := by
          simp only [beta]
          field_simp
          ring
        rw [map_one, hidentity, halpha]
        norm_num
    let betaO : 𝓞 K := ⟨beta, hbetaInt⟩
    have htwo :
        (2 : ℤ) • betaO = b 0 + b 1 - c • b 0 := by
      apply NumberField.RingOfIntegers.ext
      simp [betaO, beta, alpha, hb0]
      field_simp
      simp only [map_ofNat]
      ring
    have hcoord := congrArg (fun z : 𝓞 K ↦ b.repr z 1) htwo
    have hleft : b.repr ((2 : ℤ) • betaO) 1 =
        (2 : ℤ) * b.repr betaO 1 := by
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hright : b.repr (b 0 + b 1 - c • b 0) 1 = 1 := by
      simp only [map_sub, map_add, map_smul, Finsupp.sub_apply,
        Finsupp.add_apply, Finsupp.smul_apply]
      simp
    have hcoord' : (2 : ℤ) * b.repr betaO 1 = 1 := by
      rw [hleft, hright] at hcoord
      exact hcoord
    omega
  · rw [hdisc, hc] at htwenty
    have hfactor :
        (2 * c + 1) ^ 2 + 4 * A = 4 * (c ^ 2 + c + A) + 1 := by
      ring
    rw [hfactor] at htwenty
    omega

/-- A totally real quadratic field whose discriminant is at most `26` has one
of the seven discriminants used by the imprimitive quartic sieve. -/
theorem v15_totallyReal_quadratic_discriminant_rows
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 2)
    (hupper : (NumberField.discr K).natAbs ≤ 26) :
    (NumberField.discr K).natAbs = 5 ∨
      (NumberField.discr K).natAbs = 8 ∨
      (NumberField.discr K).natAbs = 12 ∨
      (NumberField.discr K).natAbs = 13 ∨
      (NumberField.discr K).natAbs = 17 ∨
      (NumberField.discr K).natAbs = 21 ∨
      (NumberField.discr K).natAbs = 24 := by
  letI : NumberField.IsTotallyReal K := hreal
  let D : ℤ := NumberField.discr K
  let d : ℕ := D.natAbs
  have hsign : D.sign = 1 := by
    simp only [D]
    rw [NumberField.sign_discr,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
    norm_num
  have hpos : 0 < D := Int.sign_eq_one_iff_pos.mp hsign
  have hdint : (d : ℤ) = D := by
    rw [show (d : ℤ) = |D| by exact Int.natCast_natAbs D,
      abs_of_pos hpos]
  have hfiveR := v15_degree_two_discriminant_ge_five K hreal hdegree
  have hfiveZ : (5 : ℤ) ≤ |D| := by
    exact_mod_cast hfiveR
  have hfive : 5 ≤ d := by
    have hfive' : (5 : ℤ) ≤ (d : ℤ) := by
      rw [hdint]
      simpa [abs_of_pos hpos] using hfiveZ
    exact_mod_cast hfive'
  have hupperd : d ≤ 26 := by
    simpa only [d, D] using hupper
  have hmod : (d : ℤ) % 4 = 0 ∨ (d : ℤ) % 4 = 1 := by
    rw [hdint]
    exact v15_quadratic_discriminant_emod_four K hdegree
  have hnotSquare : ¬ IsSquare (D : ℚ) := by
    simpa only [D] using v15_field_discr_not_isSquare_of_finrank_two K hdegree
  have hdneNine : d ≠ 9 := by
    intro hd
    apply hnotSquare
    refine ⟨3, ?_⟩
    rw [← hdint, hd]
    norm_num
  have hdneSixteen : d ≠ 16 := by
    intro hd
    apply hnotSquare
    refine ⟨4, ?_⟩
    rw [← hdint, hd]
    norm_num
  have hdneTwenty : d ≠ 20 := by
    intro hd
    apply v15_quadratic_discriminant_ne_twenty K hdegree
    have hD : D = 20 := by
      rw [← hdint, hd]
      norm_num
    simpa only [D] using hD
  have hdneTwentyFive : d ≠ 25 := by
    intro hd
    apply hnotSquare
    refine ⟨5, ?_⟩
    rw [← hdint, hd]
    norm_num
  change d = 5 ∨ d = 8 ∨ d = 12 ∨ d = 13 ∨ d = 17 ∨ d = 21 ∨ d = 24
  interval_cases d
  all_goals norm_num at hmod
  all_goals simp_all

end

end TraceEuclidean
