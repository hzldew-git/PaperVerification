import NormEuclidean.ChapterX.IntegralMatrix
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The maximum-entry valuation in O'Meara 101:4(i)

For a nonzero-dimensional matrix with determinant of valuation one, the
maximum-entry valuation is one exactly when every entry is integral.
This supplies the numerical version of the integral-model criterion at the
actual finite completions. The nonempty basis hypothesis is essential.
-/

noncomputable section

namespace NormEuclidean.IntegralMatrix

variable {F Γ₀ ι : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
  [Fintype ι] [DecidableEq ι]

/-- The nonarchimedean maximum-entry matrix valuation. -/
def matrixValue (w : Valuation F Γ₀) (A : Matrix ι ι F) : Γ₀ :=
  Finset.univ.sup (fun p : ι × ι ↦ w (A p.1 p.2))

omit [DecidableEq ι] in
theorem matrixValue_le_iff (w : Valuation F Γ₀) (A : Matrix ι ι F) (c : Γ₀) :
    matrixValue w A ≤ c ↔ ∀ i j, w (A i j) ≤ c := by
  simp only [matrixValue, Finset.sup_le_iff, Finset.mem_univ, forall_const, Prod.forall]

omit [DecidableEq ι] in
theorem entryValue_le_matrixValue (w : Valuation F Γ₀) (A : Matrix ι ι F) (i j : ι) :
    w (A i j) ≤ matrixValue w A :=
  Finset.le_sup (f := fun p : ι × ι ↦ w (A p.1 p.2)) (Finset.mem_univ (i, j))

/-- In positive dimension, entries strictly smaller than one force the
determinant to have valuation strictly smaller than one. -/
theorem detValue_lt_one_of_entries_lt_one [Nonempty ι]
    (w : Valuation F Γ₀) (A : Matrix ι ι F) (hA : ∀ i j, w (A i j) < 1) :
    w A.det < 1 := by
  rw [Matrix.det_apply']
  apply w.map_sum_lt one_ne_zero
  intro σ _
  have hs : w ((Equiv.Perm.sign σ : ℤ) : F) = 1 := by
    rcases Int.isUnit_eq_one_or (Equiv.Perm.sign σ).isUnit with h | h <;>
      rw [h] <;> simp
  rw [w.map_mul, hs, one_mul, map_prod]
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ w (A (σ j) j)) (Finset.mem_univ i)]
  have he : ∏ j ∈ Finset.univ.erase i, w (A (σ j) j) ≤ 1 :=
    Finset.prod_le_one' (fun j _ ↦ (hA (σ j) j).le)
  exact (mul_le_mul_right he _).trans_lt (by simpa using hA (σ i) i)

/-- A determinant of valuation one supplies the missing lower bound for
the maximum-entry valuation. -/
theorem one_le_matrixValue_of_detValue_one [Nonempty ι]
    (w : Valuation F Γ₀) (A : Matrix ι ι F) (hdet : w A.det = 1) :
    1 ≤ matrixValue w A := by
  by_contra h
  have hA : ∀ i j, w (A i j) < 1 := fun i j ↦
    (entryValue_le_matrixValue w A i j).trans_lt (lt_of_not_ge h)
  have hd := detValue_lt_one_of_entries_lt_one w A hA
  rw [hdet] at hd
  exact lt_irrefl _ hd

theorem matrixValue_eq_one_iff [Nonempty ι]
    (w : Valuation F Γ₀) (A : Matrix ι ι F) (hdet : w A.det = 1) :
    matrixValue w A = 1 ↔ ∀ i j, w (A i j) ≤ 1 := by
  constructor
  · intro h
    exact (matrixValue_le_iff w A 1).mp h.le
  · intro h
    exact le_antisymm ((matrixValue_le_iff w A 1).mpr h)
      (one_le_matrixValue_of_detValue_one w A hdet)

omit [DecidableEq ι] in
theorem matrixValue_eq_zero_of_isEmpty [IsEmpty ι]
    (w : Valuation F Γ₀) (A : Matrix ι ι F) : matrixValue w A = 0 := by
  simp [matrixValue, bot_eq_zero]

section Completions

open CompletedIntegralLattice ProperSpinor AdelicOrthogonal IsDedekindDomain

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R) [Invertible (2 : K)] [Nonempty ι]

/-- O'Meara 101:4(i), with equality to one in the actual discrete value
group, for the proper completed orthogonal group. -/
theorem mem_completedModel_iff_matrixValue_eq_one (P : QuadraticForm K V)
    (b : Module.Basis ι K V) (g : properGroup (form R v P)) :
    g ∈ properStabilizerWithin (form R v P) (carrier R v (model R b)) ↔
      matrixValue Valued.v
        (LinearMap.toMatrixAlgEquiv (b.baseChange (LocalField R v)) g.1.1.toLinearMap) = 1 := by
  rw [mem_completedModel_iff_valuation_le_one R v P b g]
  exact (matrixValue_eq_one_iff Valued.v _ (by
    rw [proper_matrix_det, Valuation.map_one])).symm

variable [CharZero K] [FiniteDimensional K V]

/-- The numerical criterion includes improper transformations of any
regular completed quadratic space in characteristic zero. -/
theorem mem_completedModel_ambient_iff_matrixValue_eq_one (P : QuadraticForm K V)
    (hP : P.polarBilin.Nondegenerate) (b : Module.Basis ι K V)
    (g : ambientGroup (form R v P)) :
    g ∈ integralStabilizer (form R v P) (carrier R v (model R b)) ↔
      matrixValue Valued.v
        (LinearMap.toMatrixAlgEquiv (b.baseChange (LocalField R v)) g.1.toLinearMap) = 1 := by
  rw [mem_completedModel_ambient_iff_integralEntries R v P hP b g]
  change (∀ i j, Valued.v
    (LinearMap.toMatrixAlgEquiv (b.baseChange (LocalField R v)) g.1.toLinearMap i j) ≤ 1) ↔ _
  apply (matrixValue_eq_one_iff Valued.v _ _).symm
  rcases ambient_matrix_det_sign (form R v P)
    (form_polarBilin_nondegenerate R v P hP) (b.baseChange (LocalField R v)) g with h | h <;>
    rw [h] <;> simp

end Completions

end NormEuclidean.IntegralMatrix
