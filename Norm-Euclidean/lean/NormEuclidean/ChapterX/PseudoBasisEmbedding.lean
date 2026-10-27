import NormEuclidean.ChapterX.MixedEmbedding
import NormEuclidean.ChapterX.PseudoBasisVolume
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Actual embedded pseudobases and normalized fundamental-domain measures

The integer basis of a possibly nonfree integer-ring lattice and its rational
basis have the same actual vectors. Their mixed images span the embedded lattice
over the integers. Haar measure is normalized by the fixed integral mixed basis;
this normalization is independent of the varying lattice and of the quadratic form.
-/

noncomputable section

namespace NormEuclidean.PseudoBasisEmbedding

open Module NumberField NumberFieldLatticeModule MixedEmbedding MeasureTheory
open scoped NumberField Classical nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

local instance (n : ℕ) : BorelSpace (Space K n) := inferInstance

local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (𝓞 K))

local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (𝓞 K))

/-- The actual mixed image of the integer module, with its induced integer action. -/
def embedded (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) :
    Submodule ℤ (Space K n) :=
  (L.restrictScalars ℤ).map ((inclusion n).restrictScalars ℤ)

/-- The actual integer basis transported from the coefficient fractional ideals. -/
def integerBasis {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)} (pb : PseudoBasis n L) :
    Basis (Index K n) ℤ L :=
  ((coordinateBasis n pb.ideals pb.ideals_ne).map (pb.equiv.restrictScalars ℤ)).reindex
    (Equiv.prodComm (Fin n) (Module.Free.ChooseBasisIndex ℤ (𝓞 K)))

/-- The rational basis obtained by extending the same pseudobasis map. -/
def rationalBasis {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) :
    Basis (Index K n) ℚ (Fin n → K) :=
  (coordinateFieldBasis n pb.ideals pb.ideals_ne).map
    ((pb.ambientEquiv hL).restrictScalars ℚ)

theorem rationalBasis_apply {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) (ai : Index K n) :
    rationalBasis pb hL ai = (integerBasis pb ai : Fin n → K) := by
  rw [rationalBasis, Basis.map_apply, integerBasis, Basis.reindex_apply, Basis.map_apply]
  change pb.ambientEquiv hL (coordinateFieldBasis n pb.ideals pb.ideals_ne ai) = _
  rw [coordinateFieldBasis_apply, fractionalIdealCommonFieldBasis_apply,
    ← coordinateBasis_apply_val n pb.ideals pb.ideals_ne (ai.2, ai.1)]
  exact pb.ambientEquiv_apply_mem hL _

/-- The actual real basis consisting of mixed images of the integer basis. -/
def mixedBasis {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) : Basis (Index K n) ℝ (Space K n) :=
  realBasis n (rationalBasis pb hL)

@[simp]
theorem mixedBasis_apply {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) (ai : Index K n) :
    mixedBasis pb hL ai = inclusion n (integerBasis pb ai : Fin n → K) := by
  rw [mixedBasis, realBasis_apply, rationalBasis_apply]

/-- The integer span of the actual mixed basis is precisely the embedded lattice. -/
theorem span_mixedBasis {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) :
    Submodule.span ℤ (Set.range (mixedBasis pb hL)) = embedded n L := by
  let j : L →ₗ[ℤ] Space K n :=
    ((inclusion n).restrictScalars ℤ).comp (L.subtype.restrictScalars ℤ)
  have hfamily : (mixedBasis pb hL : Index K n → Space K n) =
      j ∘ integerBasis pb := funext (mixedBasis_apply pb hL)
  rw [hfamily, Set.range_comp, Submodule.span_image, (integerBasis pb).span_eq]
  rw [Submodule.map_top]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The rational determinant of the actual pseudobasis equals the product of
coefficient norms times the norm of the ambient field determinant. -/
theorem abs_det_rationalBasis {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) :
    |(standardCoordinateFieldBasis (K := K) n).det (rationalBasis pb hL)| =
      fieldAbsNorm K (LinearMap.det (pb.ambientEquiv hL).toLinearMap) *
        ∏ i, FractionalIdeal.absNorm (pb.ideals i) := by
  have hfamily : (rationalBasis pb hL : Index K n → (Fin n → K)) =
      ((pb.ambientEquiv hL).toLinearMap.restrictScalars ℚ) ∘
        coordinateFieldBasis n pb.ideals pb.ideals_ne := rfl
  rw [hfamily, Basis.det_comp, abs_mul, LinearMap.det_restrictScalars,
    abs_det_standardCoordinateFieldBasis_coordinateFieldBasis]
  rfl

/-- Fixed Haar normalization, giving the integral mixed basis fundamental domain measure one. -/
def normalizedMeasure (n : ℕ) : Measure (Space K n) := (standardBasis (K := K) n).addHaar

instance (n : ℕ) : Measure.IsAddHaarMeasure (normalizedMeasure (K := K) n) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (standardBasis (K := K) n).addHaar)

theorem measure_standard_fundamentalDomain (n : ℕ) :
    normalizedMeasure n (ZSpan.fundamentalDomain (standardBasis (K := K) n)) = 1 := by
  rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _)]
  exact (standardBasis (K := K) n).addHaar_self

/-- Exact measure of the actual embedded lattice fundamental domain, in the fixed Haar
normalization. The coefficient ideals need not be principal. -/
theorem measure_fundamentalDomain {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) :
    normalizedMeasure n (ZSpan.fundamentalDomain (mixedBasis pb hL)) =
      ENNReal.ofReal ((fieldAbsNorm K (LinearMap.det (pb.ambientEquiv hL).toLinearMap) *
        ∏ i, FractionalIdeal.absNorm (pb.ideals i) : ℚ) : ℝ) := by
  rw [ZSpan.measure_fundamentalDomain _ _ (standardBasis (K := K) n),
    measure_standard_fundamentalDomain, mul_one, mixedBasis, det_realBasis]
  congr 1
  rw [← Rat.cast_abs, abs_det_rationalBasis]

/-- The field Gram determinant changes by the square of the actual ambient determinant. -/
theorem gram_det {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (B : LinearMap.BilinForm K (Fin n → K)) (pb : PseudoBasis n L)
    (hL : L.IsLattice K) :
    (IntegralVolume.pairingMatrix B (PseudoBasisVolume.fieldBasis pb hL)
      (PseudoBasisVolume.fieldBasis pb hL)).det =
        (LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) B).det *
          LinearMap.det (pb.ambientEquiv hL).toLinearMap ^ 2 := by
  let b := Pi.basisFun K (Fin n)
  let f := (pb.ambientEquiv hL).toLinearMap
  have hGram : IntegralVolume.pairingMatrix B (PseudoBasisVolume.fieldBasis pb hL)
      (PseudoBasisVolume.fieldBasis pb hL) = LinearMap.BilinForm.toMatrix b (B.comp f f) := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [hGram, LinearMap.BilinForm.toMatrix_comp b b B f f, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, ← LinearMap.det_toMatrix b f]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Intrinsic volume norm equals fixed Gram norm times the square of normalized covolume.
This is derived from actual determinants and coefficient ideals, for every full module. -/
theorem absNorm_volumeIdeal {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (B : LinearMap.BilinForm K (Fin n → K)) (pb : PseudoBasis n L)
    (hL : L.IsLattice K) :
    FractionalIdeal.absNorm (IntegralVolume.volumeIdeal B n L hL.fg) =
      fieldAbsNorm K (LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) B).det *
        (fieldAbsNorm K (LinearMap.det (pb.ambientEquiv hL).toLinearMap) *
          ∏ i, FractionalIdeal.absNorm (pb.ideals i)) ^ 2 := by
  rw [PseudoBasisVolume.absNorm_volumeIdeal_formula B pb hL, gram_det,
    fieldAbsNorm_mul, pow_two, fieldAbsNorm_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Exact comparison with the real measure of the actual fundamental domain.
The fixed Haar normalization is stated explicitly and does not depend on the lattice. -/
theorem measureReal_squared_mul_gramNorm {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (B : LinearMap.BilinForm K (Fin n → K)) (pb : PseudoBasis n L)
    (hL : L.IsLattice K) :
    (normalizedMeasure n).real (ZSpan.fundamentalDomain (mixedBasis pb hL)) ^ 2 *
      (fieldAbsNorm K (LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) B).det : ℝ) =
        (FractionalIdeal.absNorm (IntegralVolume.volumeIdeal B n L hL.fg) : ℝ) := by
  have hnonneg : 0 ≤ fieldAbsNorm K (LinearMap.det (pb.ambientEquiv hL).toLinearMap) *
      ∏ i, FractionalIdeal.absNorm (pb.ideals i) := by
    exact mul_nonneg (fieldAbsNorm_nonneg K _) (Finset.prod_nonneg fun i _ ↦
      FractionalIdeal.absNorm_nonneg _)
  rw [Measure.real, measure_fundamentalDomain,
    ENNReal.toReal_ofReal (by exact_mod_cast hnonneg), absNorm_volumeIdeal B pb hL]
  push_cast
  ring

end NormEuclidean.PseudoBasisEmbedding
