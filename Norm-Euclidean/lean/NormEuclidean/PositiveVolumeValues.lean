import NormEuclidean.PositiveDiagonalScaling
import NormEuclidean.IntegralDiagonalFrame

/-!
# Uniform finite represented values for varying anisotropic spaces

The finite set is chosen from the field, rank and intrinsic volume bound
before the quadratic space. Integral lattices need not be free. This is the
small-value input for finiteness of the ambient binary spaces.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.PositiveVolumeValues

open Module NumberField NumberField.InfinitePlace MixedEmbedding
open NumberFieldLatticeModule PositiveDiagonalScaling
open scoped NumberField Classical nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (𝓞 K))
local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (𝓞 K))

theorem value_bound {n : ℕ} (a x : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (R : ℝ) (hx : ‖equiv a (inclusion n x)‖ ≤ R)
    (φ : K →+* ℂ) : ‖φ (∑ i, a i * x i ^ 2)‖ ≤ n * R ^ 2 := by
  let w := InfinitePlace.mk φ
  have hterm (i : Fin n) : ‖φ (a i * x i ^ 2)‖ ≤ R ^ 2 := by
    let z := ArchimedeanLogScale.scale K (parameter (a i)) (mixedEmbedding K (x i))
    have hz : mixedEmbedding.normAtPlace w z ≤ R := by
      have hp := Finset.le_sup' (s := Finset.univ)
        (f := fun v ↦ mixedEmbedding.normAtPlace v z) (Finset.mem_univ w)
      rw [← mixedEmbedding.norm_eq_sup'_normAtPlace] at hp
      exact hp.trans ((norm_le_pi_norm (equiv a (inclusion n x)) i).trans hx)
    have hn := mixedEmbedding.normAtPlace_nonneg w z
    have hs : mixedEmbedding.normAtPlace w z ^ 2 = ‖φ (a i * x i ^ 2)‖ := by
      rw [place_square (a i) (ha i), mixedEmbedding.normAtPlace_apply]
      simp only [w, InfinitePlace.apply, map_mul, map_pow, norm_mul, norm_pow]
    rw [← hs]
    exact pow_le_pow_left₀ hn hz 2
  rw [map_sum]
  calc
    ‖∑ i, φ (a i * x i ^ 2)‖ ≤ ∑ i, ‖φ (a i * x i ^ 2)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, R ^ 2 := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = n * R ^ 2 := by simp

section Ambient

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem diagonal_gram (Q : QuadraticForm K V)
    (L : Lattice (integerSubring K) Q)
    (f : IntegralDiagonalFrame L (Fin (finrank K V))) :
    ((halfPolar Q).comp f.basis.equivFun.symm.toLinearMap
      f.basis.equivFun.symm.toLinearMap).toMatrix
        (Pi.basisFun K (Fin (finrank K V))) =
      Matrix.diagonal (fun i ↦ (f.coeff i : K)) := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply]
  simp only [LinearMap.BilinForm.comp_apply, Pi.basisFun_apply]
  change halfPolar Q (f.basis.equivFun.symm (Pi.single i 1))
    (f.basis.equivFun.symm (Pi.single j 1)) = _
  rw [halfPolar_apply]
  simp only [QuadraticMap.polar, ← map_add, f.diagonal]
  by_cases hij : i = j
  · subst j
    simp [Pi.single_apply, ite_pow, mul_ite]
    ring_nf
    simp [ite_pow, mul_ite, ite_mul]
    ring
  · simp [Pi.single_apply, hij, add_sq, mul_add, Finset.sum_add_distrib,
      mul_ite, Ne.symm hij]

end Ambient

universe v

/-- The finite values are uniform over all ambient spaces of the fixed rank.
No Euclidean approximation, class number, integral basis or space finiteness
assumption is used. -/
theorem exists_finite_values (n : ℕ) (hn : 0 < n) (C : ℚ) :
    ∃ Φ : Set K, Φ.Finite ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic → finrank K V = n →
        FractionalIdeal.absNorm L.volumeIdeal ≤ C →
        ∃ x ∈ L.carrier, Q x ≠ 0 ∧ Q x ∈ Φ := by
  obtain ⟨R, _, hsmall⟩ := exists_uniform_scaled_vector (K := K) n hn C
  let Φ : Set K := {a | IsIntegral ℤ a ∧ ∀ φ : K →+* ℂ, ‖φ a‖ ≤ n * R ^ 2}
  refine ⟨Φ, NumberField.Embeddings.finite_of_norm_le K ℂ (n * R ^ 2), ?_⟩
  intro V _ _ Q L hA hdim hvol
  subst n
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  let f := L.integralDiagonalFrame
  let e := f.basis.equivFun
  let B := (halfPolar Q).comp e.symm.toLinearMap e.symm.toLinearMap
  let a := fun i ↦ (f.coeff i : K)
  have ha (i) : a i ≠ 0 := by
    rw [show a i = Q (f.basis i) from f.coeff_eq i]
    exact fun h ↦ f.basis.ne_zero i (hA _ h)
  have hdet : (B.toMatrix (Pi.basisFun K (Fin (finrank K V)))).det = ∏ i, a i := by
    rw [diagonal_gram Q L f, Matrix.det_diagonal]
  let Lc := L.carrier.map (e.toLinearMap.restrictScalars (integerSubring K))
  have hLc : Lc.IsLattice K := by
    constructor
    · exact L.finite.map _
    · change Submodule.span K (e.toLinearMap '' (L.carrier : Set V)) = ⊤
      rw [Submodule.span_image, L.full, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr e.surjective
  have hvolume : IntegralVolume.volumeIdeal B (finrank K V) Lc hLc.fg = L.volumeIdeal := by
    apply FractionalIdeal.coeToSubmodule_injective
    change MixedVolume.submodule (integerSubring K) B (finrank K V) Lc =
      MixedVolume.submodule (integerSubring K) (halfPolar Q) (finrank K V) L.carrier
    apply MixedVolume.map_isometry (integerSubring K) (halfPolar Q) B
      (finrank K V) L.carrier e.toLinearMap
    intro x y
    change halfPolar Q (e.symm (e x)) (e.symm (e y)) = halfPolar Q x y
    rw [e.symm_apply_apply, e.symm_apply_apply]
  obtain ⟨x, hx, hx0, hxs⟩ := hsmall a ha B hdet Lc hLc (by rwa [hvolume])
  obtain ⟨y, hy, hyx⟩ := hx
  change e y = x at hyx
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    rw [← hyx, h, map_zero]
  refine ⟨y, hy, fun h ↦ hy0 (hA _ h), L.integral _ hy, ?_⟩
  intro φ
  have he : Q y = ∑ i, a i * x i ^ 2 := by
    rw [← hyx]
    exact f.diagonal_repr y
  rw [he]
  exact value_bound a x ha R hxs φ

end NormEuclidean.PositiveVolumeValues
