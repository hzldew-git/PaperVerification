import NormEuclidean.ChapterX.PseudoBasisEmbedding
import NormEuclidean.ChapterX.MinkowskiBound
import NormEuclidean.ChapterX.VolumeNormBound
import Mathlib.Analysis.Real.Sqrt

/-!
# Actual uniform small vectors over a general number field

The intrinsic volume norm bounds the actual fundamental-domain measure in
the fixed integral-basis Haar normalization. Minkowski then supplies a
nonzero vector in the original module, with all coordinate conjugates bounded.
No small-vector or covolume comparison premise is supplied by the caller.
-/

noncomputable section

namespace NormEuclidean.MinkowskiSmallVector

open Module NumberField NumberFieldLatticeModule MixedEmbedding PseudoBasisEmbedding
open MeasureTheory
open scoped NumberField Classical nonZeroDivisors ENNReal

variable {K : Type*} [Field K] [NumberField K]

local instance (n : ℕ) : BorelSpace (Space K n) := inferInstance

local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (𝓞 K))

local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (𝓞 K))

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Actual bounded intrinsic volumes give actual uniformly small nonzero vectors.
This allows nonprincipal coefficient ideals, indefinite forms and complex places. -/
theorem exists_uniform_coordinate_bound (n : ℕ) (hn : 0 < n)
    (B : LinearMap.BilinForm K (Fin n → K)) (hB : B.Nondegenerate) (C : ℚ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (L : Submodule (𝓞 K) (Fin n → K)) (hL : L.IsLattice K),
      FractionalIdeal.absNorm (IntegralVolume.volumeIdeal B n L hL.fg) ≤ C →
        ∃ x ∈ L, x ≠ 0 ∧ ∀ (φ : K →+* ℂ) (i : Fin n), ‖φ (x i)‖ ≤ R := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : FiniteDimensional ℝ (Space K n) := (standardBasis n).finiteDimensional_of_finite
  let d := fieldAbsNorm K (LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) B).det
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast fieldAbsNorm_pos K
      ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Pi.basisFun K (Fin n))).mp hB)
  let D := ENNReal.ofReal (Real.sqrt ((C : ℝ) / (d : ℝ)))
  obtain ⟨R, hR, hsmall⟩ := MinkowskiBound.exists_uniform_norm_bound
    (ι := Index K n) (normalizedMeasure (K := K) n) D (by finiteness)
  refine ⟨R, hR, ?_⟩
  intro L hL hvol
  obtain ⟨pb⟩ := exists_pseudoBasis n L hL
  let b := mixedBasis pb hL
  let μ := normalizedMeasure (K := K) n
  have hfinite : μ (ZSpan.fundamentalDomain b) ≠ ⊤ := by
    rw [measure_fundamentalDomain pb hL]
    exact ENNReal.ofReal_ne_top
  have hsq : μ.real (ZSpan.fundamentalDomain b) ^ 2 * (d : ℝ) ≤ (C : ℝ) := by
    rw [measureReal_squared_mul_gramNorm B pb hL]
    exact_mod_cast hvol
  have hbound : μ (ZSpan.fundamentalDomain b) ≤ D := by
    calc
      μ (ZSpan.fundamentalDomain b) =
          ENNReal.ofReal (μ.real (ZSpan.fundamentalDomain b)) :=
        (ENNReal.ofReal_toReal hfinite).symm
      _ ≤ D := ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le ((le_div_iff₀ hd).mpr hsq))
  obtain ⟨z, hz, hz0, hzsmall⟩ := hsmall b hbound
  rw [span_mixedBasis pb hL] at hz
  obtain ⟨x, hx, hxz⟩ := hz
  change inclusion n x = z at hxz
  have hxsmall : ‖inclusion n x‖ ≤ R := by rw [hxz]; exact hzsmall
  refine ⟨x, hx, ?_, ?_⟩
  · intro hx0
    apply hz0
    rw [← hxz, hx0]
    exact (inclusion n).map_zero
  · intro φ i
    exact (conjugate_coordinate_norm_le n x φ i).trans hxsmall

section Ambient

variable {V : Type*} [AddCommGroup V] [Module K V]

set_option backward.isDefEq.respectTransparency false in
/-- In any fixed field basis, every integral-scale lattice above a nonzero
volume ideal contains a uniformly small nonzero vector. No anisotropy is needed. -/
theorem exists_uniform_small_vector (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (n : ℕ) (b : Basis (Fin n) K V) (hn : 0 < n)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ L : Lattice (integerSubring K) Q,
      L.scaleIdeal ≤ 1 → c ≤ L.volumeIdeal →
        ∃ x ∈ L.carrier, x ≠ 0 ∧
          ∀ (φ : K →+* ℂ) (i : Fin n), ‖φ (b.repr x i)‖ ≤ R := by
  let e := b.equivFun
  let B := halfPolar Q
  let C := B.comp e.symm.toLinearMap e.symm.toLinearMap
  have hB : B.Nondegenerate := (SpinorBridge.quadraticSpace Q hQ).nondegenerate
  have hC : C.Nondegenerate := hB.congr e
  obtain ⟨D, _, hD⟩ := VolumeNormBound.exists_norm_bound Q c hc
  obtain ⟨R, hR, hsmall⟩ := exists_uniform_coordinate_bound n hn C hC D
  refine ⟨R, hR, ?_⟩
  intro L hs hvol
  let Lc := L.carrier.map (e.toLinearMap.restrictScalars (integerSubring K))
  have hLc : Lc.IsLattice K := by
    constructor
    · exact L.finite.map _
    · change Submodule.span K (e.toLinearMap '' (L.carrier : Set V)) = ⊤
      rw [Submodule.span_image, L.full, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr e.surjective
  have hdim : Module.finrank K V = n := by simpa using Module.finrank_eq_card_basis b
  have hvolume : IntegralVolume.volumeIdeal C n Lc hLc.fg = L.volumeIdeal := by
    apply FractionalIdeal.coeToSubmodule_injective
    change MixedVolume.submodule (integerSubring K) C n Lc =
      MixedVolume.submodule (integerSubring K) B (Module.finrank K V) L.carrier
    rw [hdim]
    apply MixedVolume.map_isometry (integerSubring K) B C n L.carrier e.toLinearMap
    intro x y
    change B (e.symm (e x)) (e.symm (e y)) = B x y
    rw [e.symm_apply_apply, e.symm_apply_apply]
  obtain ⟨z, hz, hz0, hzsmall⟩ := hsmall Lc hLc (by rw [hvolume]; exact hD L hs hvol)
  obtain ⟨x, hx, hxz⟩ := hz
  change e x = z at hxz
  refine ⟨x, hx, ?_, ?_⟩
  · intro hx0
    apply hz0
    rw [← hxz, hx0]
    exact e.map_zero
  · intro φ i
    change ‖φ (e x i)‖ ≤ R
    rw [hxz]
    exact hzsmall φ i

end Ambient

end NormEuclidean.MinkowskiSmallVector
