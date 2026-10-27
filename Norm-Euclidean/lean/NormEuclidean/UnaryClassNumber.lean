import NormEuclidean.GlobalLatticeRecovery
import NormEuclidean.QuadraticBaseChangeNondegenerate
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Ordinary class number one in dimension one

Every local isometry of a regular line preserves each integral submodule.
Equality at every actual finite completion therefore recovers the global
lattice. Neither freeness nor a norm-Euclidean hypothesis is required.
-/

namespace NormEuclidean.UnaryClassNumber

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]

/-- A regular quadratic form on a line is anisotropic. -/
theorem anisotropic (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank F E = 1) : Q.Anisotropic := by
  intro x hx
  by_contra hxn
  apply hxn
  apply hQ.1 x
  intro y
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hxn y
  simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hx]

/-- Equal quadratic values on a regular line differ by at most a sign. -/
theorem eq_or_eq_neg_of_value_eq (Q : QuadraticForm F E)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank F E = 1)
    (x y : E) (hxy : Q y = Q x) : y = x ∨ y = -x := by
  have hA := anisotropic Q hQ hdim
  by_cases hx : x = 0
  · subst x
    exact Or.inl (hA y (by simpa using hxy))
  · obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hx y
    have hQx : Q x ≠ 0 := fun h ↦ hx (hA x h)
    have hc : c ^ 2 = 1 := by
      apply mul_right_cancel₀ hQx
      simpa only [Q.map_smul, smul_eq_mul, one_mul, pow_two] using hxy
    rcases sq_eq_one_iff.mp hc with hc | hc
    · exact Or.inl (by simp [hc])
    · exact Or.inr (by simp [hc])

/-- An integral isometry of two submodules on a regular line forces their equality. -/
theorem carrier_eq_of_isometry (Q : QuadraticForm F E)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank F E = 1)
    {R : Subring F} {A B : Submodule R E} (e : LatticeIsometry Q Q A B) : A = B := by
  ext x
  have hs : e.toLinearEquiv x ∈ B ↔ x ∈ B := by
    rcases eq_or_eq_neg_of_value_eq Q hQ hdim x (e.toLinearEquiv x) (e.q_eq x) with h | h
    · rw [h]
    · rw [h, Submodule.neg_mem_iff]
  exact (e.mem_iff x).symm.trans hs

open CompletedIntegralLattice

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- The ordinary genus of a regular rank-one lattice has only its original carrier. -/
theorem carrier_eq_of_sameGenus (L M : Lattice (integerSubring K) Q)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 1)
    (hgen : SameGenus Q L M) : L.carrier = M.carrier := by
  letI := L.finiteDimensional
  apply AdelicApproximation.completedCarriersRecoverGlobalLattices Q L M
  intro p
  obtain ⟨e⟩ := hgen.1 p
  apply carrier_eq_of_isometry (form (integerSubring K) p Q)
    (form_polarBilin_nondegenerate (integerSubring K) p Q hQ) _ e
  simp only [Space, Module.finrank_tensorProduct, Module.finrank_self, one_mul, hdim]

/-- Every regular rank-one integral lattice over a number field has ordinary class number one. -/
theorem classNumberOne (L : Lattice (integerSubring K) Q)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 1) :
    HasLatticeClassNumberOne Q L := by
  rw [hasLatticeClassNumberOne_iff]
  intro M hgen
  have h := carrier_eq_of_sameGenus L M hQ hdim hgen
  exact ⟨{ toLinearEquiv := LinearEquiv.refl K V
           q_eq := fun _ ↦ rfl
           mem_iff := fun x ↦ by change x ∈ M.carrier ↔ x ∈ L.carrier; rw [h] }⟩

end NormEuclidean.UnaryClassNumber
