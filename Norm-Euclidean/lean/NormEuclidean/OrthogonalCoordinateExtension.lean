import NormEuclidean.ChapterX.ProjectedComplement
import NormEuclidean.CoordinateFormFiniteness
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Extending complementary coordinates by an orthogonal line

The construction uses a field basis of the complement, not a free integral
basis of the lattice. Its polar matrix is a literal block matrix.
-/

noncomputable section

namespace NormEuclidean.OrthogonalCoordinateExtension

open Module ProjectedComplement CoordinateFormFiniteness

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

def block {n : ℕ} (a : K) (M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Fin.cons (Fin.cons (2 * a) 0) (fun i ↦ Fin.cons 0 (M i))

/-- A nonzero-value vector and any basis of its orthogonal complement give
an actual ambient basis, with no integral freeness assumption. -/
def basis (Q : QuadraticForm K V) (y : V) (hy : Q y ≠ 0) {n : ℕ}
    (b : Basis (Fin n) K (complement Q y)) : Basis (Fin (n + 1)) K V :=
  b.mkFinCons y (fun c x hx h ↦ by
    have hx0 : halfPolar Q y x = 0 := hx y (Submodule.subset_span (by simp))
    have he := congrArg (halfPolar Q y) h
    simp only [map_add, map_smul, smul_eq_mul, halfPolar_self, hx0, add_zero,
      map_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hy) (fun z ↦ by
    refine ⟨-(halfPolar Q y z / Q y), ?_⟩
    rw [complement, LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
    change halfPolar Q y (z + -(halfPolar Q y z / Q y) • y) = 0
    simp only [map_add, map_smul, smul_eq_mul, halfPolar_self]
    field_simp
    ring)

theorem basis_coe (Q : QuadraticForm K V) (y : V) (hy : Q y ≠ 0) {n : ℕ}
    (b : Basis (Fin n) K (complement Q y)) :
    (basis Q y hy b : Fin (n + 1) → V) = Fin.cons y (fun i ↦ (b i : V)) :=
  Basis.coe_mkFinCons _ _ _ _

/-- The only new polar coefficient is twice the represented value; the
cross coefficients vanish and the complementary block is unchanged. -/
theorem polarMatrix_basis (Q : QuadraticForm K V) (y : V) (hy : Q y ≠ 0) {n : ℕ}
    (b : Basis (Fin n) K (complement Q y)) :
    polarMatrix (n + 1) (Q.basisRepr (basis Q y hy b)) =
      block (Q y) (polarMatrix n ((Q.comp (complement Q y).subtype).basisRepr b)) := by
  rw [polarMatrix_basisRepr, polarMatrix_basisRepr]
  have hzero (i : Fin n) : Q.polarBilin y (b i : V) = 0 := by
    have h := (b i).property y (Submodule.subset_span (by simp))
    change (2 : K)⁻¹ * Q.polarBilin y (b i : V) = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num))
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases
  · simp [basis_coe, block]
  · simp [basis_coe, block, hzero]
  · simp only [basis_coe, block, Fin.cons_succ, Fin.cons_zero]
    exact (QuadraticMap.polar_comm Q _ _).trans (hzero _)
  · simp only [basis_coe, block, Fin.cons_succ, QuadraticMap.polarBilin_comp]
    rfl

end NormEuclidean.OrthogonalCoordinateExtension
