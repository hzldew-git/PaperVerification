import NormEuclidean.LogScaleTraceHaar
import NormEuclidean.ChapterX.MinkowskiSmallVector
import NormEuclidean.PositivePairingBounds

/-!
# Archimedean normalization of varying positive diagonal forms

Each coordinate is scaled by the square root of the absolute value of its
coefficient at the actual infinite place. The square of the real determinant
is the absolute field norm of the product of the coefficients.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.PositiveDiagonalScaling

open Module NumberField NumberField.InfinitePlace MixedEmbedding
open NumberFieldLatticeModule MeasureTheory PseudoBasisEmbedding
open scoped NumberField Classical

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def parameter (a : K) (w : InfinitePlace K) : ℝ := Real.log (w a) / 2

def equiv (a : Fin n → K) : Space K n ≃ₗ[ℝ] Space K n :=
  LinearEquiv.piCongrRight fun i ↦
    (ArchimedeanLogScale.scale K (parameter (a i))).toLinearEquiv

theorem det_square (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    LinearMap.det (equiv a).toLinearMap ^ 2 =
      (fieldAbsNorm K (∏ i, a i) : ℝ) := by
  have hsingle (b : K) (hb : b ≠ 0) :
      LinearMap.det (ArchimedeanLogScale.scale K (parameter b)).toLinearMap ^ 2 =
        (fieldAbsNorm K b : ℝ) := by
    rw [LogScaleTraceHaar.determinant]
    have hj : LogScaleTraceHaar.logJacobian K (parameter b) =
        ∑ w, (mult w : ℝ) * parameter b w := by
      rw [sum_eq_sum_add_sum]
      simp only [mult_isReal, mult_isComplex, Nat.cast_one, Nat.cast_ofNat, one_mul,
        LogScaleTraceHaar.logJacobian, Finset.mul_sum]
    rw [hj, ← Real.exp_nat_mul]
    have he : (2 : ℝ) * (∑ w, (mult w : ℝ) * parameter b w) =
        ∑ w, (mult w : ℝ) * Real.log (w b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      simp only [parameter]
      ring
    rw [Nat.cast_ofNat, he, Real.exp_sum]
    simp_rw [Real.exp_nat_mul, Real.exp_log (pos_iff.mpr hb)]
    rw [prod_eq_abs_norm]
    simp only [fieldAbsNorm, Rat.cast_abs]
  change LinearMap.det (LinearMap.pi fun i ↦
    (ArchimedeanLogScale.scale K (parameter (a i))).toLinearMap.comp
      (LinearMap.proj i)) ^ 2 = _
  rw [LinearMap.det_pi, ← Finset.prod_pow]
  simp_rw [hsingle _ (ha _)]
  simp only [fieldAbsNorm, map_prod, Finset.abs_prod, Rat.cast_prod, Rat.cast_abs]

omit [NumberField K] in
theorem place_square (a : K) (ha : a ≠ 0) (w : InfinitePlace K)
    (x : NumberField.mixedEmbedding.mixedSpace K) :
    NumberField.mixedEmbedding.normAtPlace w
        (ArchimedeanLogScale.scale K (parameter a) x) ^ 2 =
      w a * NumberField.mixedEmbedding.normAtPlace w x ^ 2 := by
  rw [ArchimedeanLogScale.normAtPlace_scale, mul_pow]
  have he : Real.exp (parameter a w) ^ 2 = w a := by
    rw [← Real.exp_nat_mul]
    simp only [parameter, Nat.cast_ofNat]
    rw [show (2 : ℝ) * (Real.log (w a) / 2) = Real.log (w a) by ring]
    exact Real.exp_log (pos_iff.mpr ha)
  rw [he]

local instance (n : ℕ) : BorelSpace (Space K n) := inferInstance

local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (𝓞 K))

local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (𝓞 K))

/-- Scaling the actual embedded pseudobasis removes the Gram determinant from
the square-covolume formula. This includes nonprincipal coefficient ideals. -/
theorem scaled_covolume_square (a : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (B : LinearMap.BilinForm K (Fin n → K))
    (hdet : (B.toMatrix (Pi.basisFun K (Fin n))).det = ∏ i, a i)
    {L : Submodule (𝓞 K) (Fin n → K)} (pb : PseudoBasis n L)
    (hL : L.IsLattice K) :
    (normalizedMeasure n).real
        (ZSpan.fundamentalDomain ((mixedBasis pb hL).map (equiv a))) ^ 2 =
      (FractionalIdeal.absNorm (IntegralVolume.volumeIdeal B n L hL.fg) : ℝ) := by
  let b := mixedBasis pb hL
  have hb : b.det (b.map (equiv a)) = LinearMap.det (equiv a).toLinearMap := by
    change b.det ((equiv a).toLinearMap ∘ b) = _
    rw [Basis.det_comp, Basis.det_self, mul_one]
  rw [ZSpan.measureReal_fundamentalDomain _ _ b, hb, mul_pow, sq_abs,
    det_square a ha, mul_comm]
  rw [← hdet]
  exact measureReal_squared_mul_gramNorm B pb hL

/-- A bound chosen before the coefficients or lattice controls a nonzero
vector after the positive diagonal normalization. -/
theorem exists_uniform_scaled_vector (n : ℕ) (hn : 0 < n) (C : ℚ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (a : Fin n → K), (∀ i, a i ≠ 0) →
      ∀ (B : LinearMap.BilinForm K (Fin n → K)),
      (B.toMatrix (Pi.basisFun K (Fin n))).det = ∏ i, a i →
      ∀ (L : Submodule (𝓞 K) (Fin n → K)) (hL : L.IsLattice K),
      FractionalIdeal.absNorm (IntegralVolume.volumeIdeal B n L hL.fg) ≤ C →
      ∃ x ∈ L, x ≠ 0 ∧ ‖equiv a (inclusion n x)‖ ≤ R := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : FiniteDimensional ℝ (Space K n) := (standardBasis n).finiteDimensional_of_finite
  obtain ⟨R, hR, hsmall⟩ := MinkowskiBound.exists_uniform_norm_bound
    (ι := Index K n) (normalizedMeasure (K := K) n)
    (ENNReal.ofReal (Real.sqrt (C : ℝ))) (by finiteness)
  refine ⟨R, hR, ?_⟩
  intro a ha B hdet L hL hvol
  obtain ⟨pb⟩ := exists_pseudoBasis n L hL
  let b := (mixedBasis pb hL).map (equiv a)
  let μ := normalizedMeasure (K := K) n
  have hfinite : μ (ZSpan.fundamentalDomain b) ≠ ⊤ := by
    rw [ZSpan.measure_fundamentalDomain _ _ (standardBasis n),
      measure_standard_fundamentalDomain, mul_one]
    exact ENNReal.ofReal_ne_top
  have hsq : μ.real (ZSpan.fundamentalDomain b) ^ 2 ≤ (C : ℝ) := by
    rw [scaled_covolume_square a ha B hdet pb hL]
    exact_mod_cast hvol
  have hbound : μ (ZSpan.fundamentalDomain b) ≤ ENNReal.ofReal (Real.sqrt (C : ℝ)) := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le hsq)
  obtain ⟨z, hz, hz0, hzs⟩ := hsmall b hbound
  have hspan : Submodule.span ℤ (Set.range b) =
      (embedded n L).map ((equiv a).toLinearMap.restrictScalars ℤ) := by
    change Submodule.span ℤ (Set.range ((equiv a) ∘ mixedBasis pb hL)) = _
    rw [Set.range_comp]
    change Submodule.span ℤ (((equiv a).toLinearMap.restrictScalars ℤ) ''
      Set.range (mixedBasis pb hL)) = _
    rw [Submodule.span_image, span_mixedBasis pb hL]
  rw [hspan] at hz
  obtain ⟨y, ⟨x, hx, hxy⟩, hyz⟩ := hz
  have he : equiv a (inclusion n x) = z := by rw [← hyz, ← hxy]; rfl
  refine ⟨x, hx, ?_, ?_⟩
  · intro hx0
    apply hz0
    rw [← he, hx0, map_zero, map_zero]
  · rw [he]
    exact hzs

end NormEuclidean.PositiveDiagonalScaling
