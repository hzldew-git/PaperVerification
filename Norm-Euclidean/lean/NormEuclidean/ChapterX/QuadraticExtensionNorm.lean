/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Dyadic.HilbertSymbol
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Norm.Defs
import NormEuclidean.ChapterX.AdmissibleNormCore

/-!
# The actual quadratic-extension norm behind `IsQuadraticNorm`

For a nonsquare unit `theta`, `QuadraticAlgebra K theta 0` is a field and,
when `K` is a number field, is a number field. The norm form used by the
formal Hilbert-symbol and Hasse-norm layers is exactly its determinant norm.
Consequently the existing global quadratic-norm subgroup is the range of
the actual norm map on extension units. This is a base-field bridge; full
idèle norm and finite-place transport remain separate constructions.
-/

namespace NormEuclidean.QuadraticExtensionNorm

open Bong.Dyadic

universe u

variable {K : Type u} [Field K]

/-- The quadratic norm equation is the norm equation in the quadratic
algebra, before any irreducibility hypothesis is imposed. -/
theorem quadraticNorm_iff_quadraticAlgebra_norm
    (theta alpha : Kˣ) :
    IsQuadraticNorm K theta alpha ↔
      ∃ z : QuadraticAlgebra K (theta : K) 0,
        QuadraticAlgebra.norm z = (alpha : K) := by
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨⟨x, y⟩, ?_⟩
    calc
      QuadraticAlgebra.norm (⟨x, y⟩ : QuadraticAlgebra K (theta : K) 0) =
          x ^ 2 - (theta : K) * y ^ 2 := by
            simp [QuadraticAlgebra.norm_def]
            ring
      _ = (alpha : K) := h
  · rintro ⟨z, h⟩
    refine ⟨z.re, z.im, ?_⟩
    calc
      _ = QuadraticAlgebra.norm z := by simp [QuadraticAlgebra.norm_def]; ring
      _ = (alpha : K) := h

/-- A nonsquare parameter makes `X² - theta` irreducible in the concrete
condition used by mathlib's quadratic-algebra field instance. -/
theorem nonsquare_quadraticAlgebra_field_fact
    (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    ∀ r : K, r ^ 2 ≠ (theta : K) + 0 * r := by
  intro r hr
  have hr2 : r ^ 2 = (theta : K) := by simpa using hr
  have hr0 : r ≠ 0 := by
    intro hz
    simpa [hz] using hr2.symm
  apply htheta
  refine ⟨Units.mk0 r hr0, ?_⟩
  apply Units.ext
  change (theta : K) = r * r
  simpa [pow_two] using hr2.symm

/-- The concrete field structure on `K[√theta]` for nonsquare `theta`.
The definition is reducible so the inherited algebra structure is the
same one used by the quadratic-algebra norm theorem. -/
@[reducible] noncomputable def quadraticExtensionField
    (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    Field (QuadraticAlgebra K (theta : K) 0) := by
  letI : Fact (∀ r : K, r ^ 2 ≠ (theta : K) + 0 * r) :=
    ⟨nonsquare_quadraticAlgebra_field_fact theta htheta⟩
  infer_instance

/-- The determinant algebra norm is exactly the quadratic-algebra norm.
The calculation uses the explicit basis `1, √theta` and multiplication
matrix `[[x, theta*y], [y, x]]`. -/
theorem algebra_norm_eq_quadraticAlgebra_norm (theta : Kˣ)
    (z : QuadraticAlgebra K (theta : K) 0) :
    Algebra.norm K z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis (theta : K) 0)]
  have hmatrix :
      Algebra.leftMulMatrix (QuadraticAlgebra.basis (theta : K) 0) z =
        !![z.re, (theta : K) * z.im; z.im, z.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis,
        QuadraticAlgebra.linearEquivTuple, QuadraticAlgebra.equivProd]
  rw [hmatrix, Matrix.det_fin_two]
  simp [QuadraticAlgebra.norm_def]

/-- The paper's quadratic norm relation is literally the determinant norm
equation of the concrete quadratic algebra. -/
theorem quadraticNorm_iff_algebra_norm (theta alpha : Kˣ) :
    IsQuadraticNorm K theta alpha ↔
      ∃ z : QuadraticAlgebra K (theta : K) 0,
        Algebra.norm K z = (alpha : K) := by
  simpa only [algebra_norm_eq_quadraticAlgebra_norm] using
    (quadraticNorm_iff_quadraticAlgebra_norm theta alpha)

/-- The algebra-norm equation remains exact when the nonsquare parameter
makes the quadratic algebra an actual field extension. -/
theorem nonsquare_quadraticNorm_iff_fieldNorm
    (theta alpha : Kˣ) (htheta : ¬ IsSquare theta) :
    (letI := quadraticExtensionField theta htheta
     IsQuadraticNorm K theta alpha ↔
       ∃ z : QuadraticAlgebra K (theta : K) 0,
         Algebra.norm K z = (alpha : K)) := by
  exact quadraticNorm_iff_algebra_norm theta alpha

/-- A nonzero represented norm has a nonzero extension element, hence an
extension unit in the nonsquare field. -/
theorem nonsquare_quadraticNorm_iff_extension_unit_norm
    (theta alpha : Kˣ) (htheta : ¬ IsSquare theta) :
    (letI := quadraticExtensionField theta htheta
     IsQuadraticNorm K theta alpha ↔
       ∃ z : (QuadraticAlgebra K (theta : K) 0)ˣ,
         Algebra.norm K (z : QuadraticAlgebra K (theta : K) 0) =
           (alpha : K)) := by
  letI := quadraticExtensionField theta htheta
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (quadraticNorm_iff_algebra_norm theta alpha).mp h
    have hz0 : z ≠ 0 := by
      intro hz0
      have ha : (alpha : K) = 0 := by
        calc
          (alpha : K) = Algebra.norm K z := hz.symm
          _ = QuadraticAlgebra.norm z := algebra_norm_eq_quadraticAlgebra_norm theta z
          _ = 0 := by simp [hz0]
      exact (Units.ne_zero alpha) ha
    refine ⟨Units.mk0 z hz0, ?_⟩
    simpa using hz
  · rintro ⟨z, hz⟩
    exact (quadraticNorm_iff_algebra_norm theta alpha).mpr ⟨z, hz⟩

/-- The multiplicative norm on units of the concrete quadratic algebra. -/
noncomputable def quadraticAlgebraNormUnits (theta : Kˣ) :
    (QuadraticAlgebra K (theta : K) 0)ˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- Membership in the previously defined global quadratic-norm subgroup
is membership in the range of the actual extension unit norm. -/
theorem mem_quadraticNormGroup_iff_norm_units_range
    (theta alpha : Kˣ) (htheta : ¬ IsSquare theta) :
    (letI := quadraticExtensionField theta htheta
     alpha ∈ quadraticNormGroup K theta ↔
       alpha ∈ (quadraticAlgebraNormUnits theta).range) := by
  letI := quadraticExtensionField theta htheta
  rw [mem_quadraticNormGroup, MonoidHom.mem_range]
  constructor
  · intro h
    obtain ⟨z, hz⟩ :=
      (nonsquare_quadraticNorm_iff_extension_unit_norm theta alpha htheta).mp h
    refine ⟨z, ?_⟩
    apply Units.ext
    simpa [quadraticAlgebraNormUnits] using hz
  · rintro ⟨z, hz⟩
    apply (nonsquare_quadraticNorm_iff_extension_unit_norm theta alpha htheta).mpr
    refine ⟨z, ?_⟩
    have hv := congrArg Units.val hz
    simpa [quadraticAlgebraNormUnits] using hv

/-- The formal global quadratic-norm subgroup is the actual range of the
norm homomorphism from extension units. -/
theorem quadraticNormGroup_eq_norm_units_range
    (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    (letI := quadraticExtensionField theta htheta
     quadraticNormGroup K theta = (quadraticAlgebraNormUnits theta).range) := by
  letI := quadraticExtensionField theta htheta
  ext alpha
  exact mem_quadraticNormGroup_iff_norm_units_range theta alpha htheta

/-- A nonzero quadratic norm has a unit preimage in the quadratic algebra.
Mathlib's `isUnit_iff_norm_isUnit` covers both fields and split algebras. -/
theorem quadraticNorm_iff_quadraticAlgebra_unit_norm
    (theta alpha : Kˣ) :
    IsQuadraticNorm K theta alpha ↔
      ∃ z : (QuadraticAlgebra K (theta : K) 0)ˣ,
        Algebra.norm K (z : QuadraticAlgebra K (theta : K) 0) =
          (alpha : K) := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (quadraticNorm_iff_algebra_norm theta alpha).mp h
    have hunitNorm : IsUnit (QuadraticAlgebra.norm z) := by
      rw [← algebra_norm_eq_quadraticAlgebra_norm theta z, hz]
      exact Units.isUnit alpha
    have hunitZ : IsUnit z :=
      (QuadraticAlgebra.isUnit_iff_norm_isUnit).mpr hunitNorm
    obtain ⟨u, hu⟩ := hunitZ
    exact ⟨u, by simpa [hu] using hz⟩
  · rintro ⟨z, hz⟩
    exact (quadraticNorm_iff_algebra_norm theta alpha).mpr ⟨z, hz⟩

/-- The norm subgroup is the image of the quadratic-algebra unit norm
for every nonzero parameter, without a nonsquare condition. -/
theorem quadraticNormGroup_eq_norm_units_range_all (theta : Kˣ) :
    quadraticNormGroup K theta = (quadraticAlgebraNormUnits theta).range := by
  ext alpha
  rw [mem_quadraticNormGroup, MonoidHom.mem_range]
  constructor
  · intro h
    obtain ⟨z, hz⟩ :=
      (quadraticNorm_iff_quadraticAlgebra_unit_norm theta alpha).mp h
    refine ⟨z, ?_⟩
    apply Units.ext
    simpa [quadraticAlgebraNormUnits] using hz
  · rintro ⟨z, hz⟩
    apply (quadraticNorm_iff_quadraticAlgebra_unit_norm theta alpha).mpr
    refine ⟨z, ?_⟩
    have hv := congrArg Units.val hz
    simpa [quadraticAlgebraNormUnits] using hv

/-- Pointwise form of the norm-image equality, for use at completions. -/
theorem quadraticNorm_iff_mem_algebraNormUnits_range
    (theta alpha : Kˣ) :
    IsQuadraticNorm K theta alpha ↔
      alpha ∈ (quadraticAlgebraNormUnits theta).range := by
  rw [← mem_quadraticNormGroup]
  rw [quadraticNormGroup_eq_norm_units_range_all]

variable [NumberField K]

/-- A nonsquare parameter over a number field produces an actual quadratic
number field. The field instance is explicit to avoid silently treating
the split quadratic algebra as a field. -/
theorem quadraticExtensionNumberField
    (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    @NumberField (QuadraticAlgebra K (theta : K) 0)
      (quadraticExtensionField theta htheta) := by
  letI := quadraticExtensionField theta htheta
  exact NumberField.of_module_finite K (QuadraticAlgebra K (theta : K) 0)

/-- The actual full idèle norm of `K[√theta]/K` for a nonsquare parameter.
The field structure is constructed, and no Hasse or norm-index input is required. -/
noncomputable def quadraticExtensionIdeleNorm (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ExtensionIdeleNorm.NumberFieldIdele (QuadraticAlgebra K (theta : K) 0) →*
      ExtensionIdeleNorm.NumberFieldIdele K := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact ExtensionIdeleNorm.extensionIdeleNorm

end NormEuclidean.QuadraticExtensionNorm
