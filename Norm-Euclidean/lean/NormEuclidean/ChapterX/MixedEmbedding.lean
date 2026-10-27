import NormEuclidean.ChapterX.PseudoBasisDeterminant
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Actual real embeddings of coordinate modules

The coordinatewise mixed embedding sends `K^n` to its real mixed space.
Every rational basis extends to an actual real basis, by comparison with
the number-field integral basis. No total reality or positivity is assumed.
-/

noncomputable section

namespace NormEuclidean.MixedEmbedding

open Module NumberField NumberFieldLatticeModule
open scoped NumberField Classical

variable {K : Type*} [Field K] [NumberField K]

abbrev Index (K : Type*) [Field K] [NumberField K] (n : ℕ) :=
  Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin n

abbrev Space (K : Type*) [Field K] (n : ℕ) :=
  Fin n → NumberField.mixedEmbedding.mixedSpace K

/-- The actual coordinatewise mixed embedding as a rational linear map. -/
def inclusion (n : ℕ) : (Fin n → K) →ₗ[ℚ] Space K n :=
  LinearMap.pi fun i ↦ (NumberField.mixedEmbedding K).toRatAlgHom.toLinearMap.comp
    (LinearMap.proj i)

@[simp]
theorem inclusion_apply (n : ℕ) (x : Fin n → K) (i : Fin n) :
    inclusion n x i = NumberField.mixedEmbedding K (x i) := rfl

theorem inclusion_injective (n : ℕ) : Function.Injective (inclusion (K := K) n) := by
  intro x y h
  funext i
  exact NumberField.mixedEmbedding_injective K (congrFun h i)

/-- The product of the number-field integral mixed bases, with rational-basis ordering. -/
def standardBasis (n : ℕ) : Basis (Index K n) ℝ (Space K n) :=
  (Pi.basis fun _ : Fin n ↦ NumberField.mixedEmbedding.latticeBasis K).reindex
    ((Equiv.sigmaEquivProd (Fin n) (Module.Free.ChooseBasisIndex ℤ (𝓞 K))).trans
      (Equiv.prodComm (Fin n) (Module.Free.ChooseBasisIndex ℤ (𝓞 K))))

@[simp]
theorem standardBasis_apply (n : ℕ) (ai : Index K n) :
    standardBasis (K := K) n ai =
      Pi.single ai.2 (NumberField.mixedEmbedding K (NumberField.integralBasis K ai.1)) := by
  classical
  rcases ai with ⟨a, i⟩
  simp [standardBasis]

/-- Actual mixed-basis coordinates are the real casts of rational integral-basis coordinates. -/
theorem standardBasis_repr_inclusion (n : ℕ) (x : Fin n → K) (ai : Index K n) :
    (standardBasis (K := K) n).repr (inclusion n x) ai =
      ((standardCoordinateFieldBasis (K := K) n).repr x ai : ℝ) := by
  rcases ai with ⟨a, i⟩
  rw [standardCoordinateFieldBasis_repr]
  unfold standardBasis
  rw [Basis.repr_reindex_apply]
  change (NumberField.mixedEmbedding.latticeBasis K).repr
    (NumberField.mixedEmbedding K (x i)) a = _
  exact NumberField.mixedEmbedding.latticeBasis_repr_apply K (x i) a

/-- The mixed determinant of an actual rational family is its real-cast determinant. -/
theorem det_inclusion (n : ℕ) (b : Index K n → (Fin n → K)) :
    (standardBasis (K := K) n).det (fun i ↦ inclusion n (b i)) =
      (((standardCoordinateFieldBasis (K := K) n).det b) : ℝ) := by
  classical
  rw [Basis.det_apply, Basis.det_apply]
  change _ = algebraMap ℚ ℝ ((standardCoordinateFieldBasis (K := K) n).toMatrix b).det
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact standardBasis_repr_inclusion n (b j) i

/-- A rational basis becomes a genuine real basis under the actual mixed embedding. -/
def realBasis (n : ℕ) (b : Basis (Index K n) ℚ (Fin n → K)) :
    Basis (Index K n) ℝ (Space K n) := by
  classical
  have hunit : IsUnit ((standardBasis (K := K) n).det (fun i ↦ inclusion n (b i))) := by
    rw [det_inclusion, isUnit_iff_ne_zero, Rat.cast_ne_zero]
    exact ((standardCoordinateFieldBasis (K := K) n).isUnit_det b).ne_zero
  have hb := (standardBasis (K := K) n).is_basis_iff_det.mpr hunit
  exact Basis.mk hb.1 (by rw [hb.2])

@[simp]
theorem realBasis_apply (n : ℕ) (b : Basis (Index K n) ℚ (Fin n → K)) (i : Index K n) :
    realBasis n b i = inclusion n (b i) := by
  simp only [realBasis, Basis.coe_mk]

theorem det_realBasis (n : ℕ) (b : Basis (Index K n) ℚ (Fin n → K)) :
    (standardBasis (K := K) n).det (realBasis n b) =
      (((standardCoordinateFieldBasis (K := K) n).det b) : ℝ) := by
  have h : (realBasis n b : Index K n → Space K n) = fun i ↦ inclusion n (b i) :=
    funext (realBasis_apply n b)
  rw [h]
  exact det_inclusion n b

/-- Every complex conjugate is bounded by the actual mixed-space norm. -/
theorem conjugate_norm_le (x : K) (φ : K →+* ℂ) :
    ‖φ x‖ ≤ ‖NumberField.mixedEmbedding K x‖ := by
  let w := NumberField.InfinitePlace.mk φ
  have h := Finset.le_sup' (s := Finset.univ)
    (f := fun v ↦ NumberField.mixedEmbedding.normAtPlace v
      (NumberField.mixedEmbedding K x)) (Finset.mem_univ w)
  rw [← NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace] at h
  simpa only [NumberField.mixedEmbedding.normAtPlace_apply, NumberField.InfinitePlace.apply,
    w] using h

/-- A norm bound on the coordinatewise mixed embedding bounds all field conjugates. -/
theorem conjugate_coordinate_norm_le (n : ℕ) (x : Fin n → K) (φ : K →+* ℂ) (i : Fin n) :
    ‖φ (x i)‖ ≤ ‖inclusion n x‖ :=
  (conjugate_norm_le (x i) φ).trans (norm_le_pi_norm (inclusion n x) i)

end NormEuclidean.MixedEmbedding
