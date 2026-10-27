import NormEuclidean.ChapterX.MixedVolume
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-!
# Determinant content of coordinate modules

For a module cut out coordinatewise by coefficient modules, the span of its
coordinate determinants is the product of those coefficient modules. Mixed
pairing determinants then give the Gram determinant times the square of this
content. The coefficient modules need not be principal or nonzero.
-/

noncomputable section

namespace NormEuclidean.DeterminantContent

open IntegralVolume
open scoped Pointwise

variable {K : Type*} [Field K]

/-- Coordinatewise membership in the chosen coefficient modules. -/
def coordinateModule (R : Subring K) (n : ℕ) (I : Fin n → Submodule R K) :
    Submodule R (Fin n → K) := Submodule.pi Set.univ I

/-- The actual span of the coordinate determinants of vector families. -/
def submodule (R : Subring K) (n : ℕ) (L : Submodule R (Fin n → K)) : Submodule R K :=
  Submodule.span R (Set.range fun x : Fin n → L ↦
    (show Matrix (Fin n) (Fin n) K from fun i ↦ (x i : Fin n → K)).det)

/-- Products of coefficient modules are spanned by actual products of their elements. -/
theorem product_eq_span (R : Subring K) (n : ℕ) (I : Fin n → Submodule R K) :
    (∏ i, I i) = Submodule.span R (∏ i, (I i : Set K)) := by
  simpa only [Submodule.span_eq] using
    Submodule.prod_span (R := R) Finset.univ (fun i ↦ (I i : Set K))

/-- Every coordinate determinant belongs to the product of the coefficient modules. -/
theorem det_mem_product (R : Subring K) (n : ℕ) (I : Fin n → Submodule R K)
    (x : Matrix (Fin n) (Fin n) K) (hx : ∀ i j, x i j ∈ I j) : x.det ∈ ∏ i, I i := by
  classical
  rw [product_eq_span, Matrix.det_apply']
  apply Submodule.sum_mem
  intro σ _
  have hprod : (∏ i, x (σ i) i) ∈ Submodule.span R (∏ i, (I i : Set K)) :=
    Submodule.subset_span (Set.mem_fintype_prod _ _ |>.mpr
      ⟨fun i ↦ x (σ i) i, fun i ↦ hx (σ i) i, rfl⟩)
  have h := (Submodule.span R (∏ i, (I i : Set K))).smul_mem
    (((Equiv.Perm.sign σ : ℤ) : R)) hprod
  simpa only [Subring.smul_def, Subring.coe_intCast, smul_eq_mul] using h

/-- The determinant content of the actual coordinate module is its coefficient product. -/
theorem coordinate_content (R : Subring K) (n : ℕ) (I : Fin n → Submodule R K) :
    submodule R n (coordinateModule R n I) = ∏ i, I i := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact det_mem_product R n I _ fun i j ↦
      Submodule.mem_pi.mp (x i).2 j (Set.mem_univ j)
  · rw [product_eq_span]
    apply Submodule.span_le.mpr
    intro a ha
    obtain ⟨z, hz, rfl⟩ := (Set.mem_fintype_prod _ _).mp ha
    let x : Fin n → coordinateModule R n I := fun i ↦ ⟨Matrix.diagonal z i, by
      rw [coordinateModule, Submodule.mem_pi]
      intro j _
      by_cases hij : i = j
      · subst j
        rw [Matrix.diagonal_apply_eq]
        exact hz i
      · simpa only [Matrix.diagonal_apply_ne _ hij] using (I j).zero_mem⟩
    rw [← Matrix.det_diagonal (d := z)]
    exact Submodule.subset_span ⟨x, rfl⟩

/-- A mixed pairing matrix is the coordinate matrix times Gram times transpose. -/
theorem pairingMatrix_coordinates (n : ℕ) (B : LinearMap.BilinForm K (Fin n → K))
    (x y : Matrix (Fin n) (Fin n) K) :
    pairingMatrix B x y = x * LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) B *
      y.transpose := by
  apply Matrix.ext
  intro i j
  change B (x i) (y j) = _
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec (Pi.basisFun K (Fin n)) B]
  simp only [dotProduct, Matrix.mulVec, Pi.basisFun_repr, Matrix.mul_apply,
    Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The actual determinant factorization in coordinates. -/
theorem det_pairingMatrix_coordinates (n : ℕ)
    (B : LinearMap.BilinForm K (Fin n → K)) (x y : Matrix (Fin n) (Fin n) K) :
    (pairingMatrix B x y).det =
      (LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) B).det * (x.det * y.det) := by
  rw [pairingMatrix_coordinates, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Mixed volume is the Gram determinant times the square of determinant content. -/
theorem mixed_volume (R : Subring K) (n : ℕ)
    (B : LinearMap.BilinForm K (Fin n → K)) (L : Submodule R (Fin n → K)) :
    MixedVolume.submodule R B n L =
      (LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) B).det •
        (submodule R n L * submodule R n L) := by
  classical
  let d := (LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) B).det
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    dsimp only
    rw [det_pairingMatrix_coordinates]
    have hx : (show Matrix (Fin n) (Fin n) K from fun i ↦ (p.1 i : Fin n → K)).det ∈
        submodule R n L := Submodule.subset_span ⟨p.1, rfl⟩
    have hy : (show Matrix (Fin n) (Fin n) K from fun i ↦ (p.2 i : Fin n → K)).det ∈
        submodule R n L := Submodule.subset_span ⟨p.2, rfl⟩
    exact (Submodule.mem_smul_pointwise_iff_exists _ d _).mpr
      ⟨_, Submodule.mul_mem_mul hx hy, rfl⟩
  · rw [submodule, Submodule.span_mul_span, Submodule.smul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    change d * _ ∈ _
    rw [← det_pairingMatrix_coordinates]
    exact MixedVolume.det_mem R B n L _ _ (fun i ↦ (x i).2) (fun j ↦ (y j).2)

/-- The nonfree coordinate volume formula, including zero degree and degenerate forms. -/
theorem coordinate_volume (R : Subring K) (n : ℕ)
    (B : LinearMap.BilinForm K (Fin n → K)) (I : Fin n → Submodule R K) :
    MixedVolume.submodule R B n (coordinateModule R n I) =
      (LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) B).det • (∏ i, I i) ^ 2 := by
  rw [mixed_volume, coordinate_content, pow_two]

end NormEuclidean.DeterminantContent
