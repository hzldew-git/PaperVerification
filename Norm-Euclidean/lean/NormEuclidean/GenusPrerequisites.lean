import NormEuclidean.AllPlaceUniversality
import NormEuclidean.UnconditionalClassNumber
import NormEuclidean.QuadraticBaseChangeNondegenerate

/-!
# Proved arithmetic and local inputs for the remaining genus theorem

This bundle derives the field-class-number parity, rank bound and genuine
all-place universality needed in the manuscript's final argument. It does
not assert genus/proper-class equality, stable isometry, or `h(L)=1`.
-/
namespace NormEuclidean
open scoped NumberField
variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- Three genuine prerequisites, with no assumed arithmetic classification theorem. -/
theorem hyperbolic_genus_prerequisites
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    Odd (NumberField.classNumber K) ∧
      4 ≤ Module.finrank K (Hyperbolic K V) ∧
      AllPlaceUniversal (Hyperbolic.form Q) L.hyperbolic := by
  refine ⟨?_, ?_, hyperbolic_allPlaceUniversal Q L⟩
  · rw [classNumber_eq_one_of_rank_ge_three L hdim hA hE]
    exact odd_one
  · letI := L.finiteDimensional
    have hr : Module.finrank K (Hyperbolic K V) = Module.finrank K V + 2 := by
      simp [Hyperbolic, Module.finrank_prod]
    omega

omit [NumberField K] in
/-- Archimedean base change also preserves nondegeneracy; the inverse of two
is in the completed field, never an integral valuation ring. -/
theorem archimedean_form_polarBilin_nondegenerate [FiniteDimensional K V]
    (v : NumberField.InfinitePlace K) (hQ : Q.polarBilin.Nondegenerate) :
    (ArchimedeanComparison.form v Q).polarBilin.Nondegenerate := by
  letI : Invertible (2 : v.Completion) :=
    (Invertible.map (algebraMap K v.Completion) 2).copy 2 (map_ofNat _ _).symm
  exact quadraticForm_baseChange_polarBilin_nondegenerate Q hQ

/-- The hyperbolic extension and every one of its actual completions are
nondegenerate, derived from the original anisotropy. -/
theorem hyperbolic_allPlace_nondegenerate
    (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic) :
    (Hyperbolic.form Q).polarBilin.Nondegenerate ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (integerSubring K),
        (CompletedIntegralLattice.form (integerSubring K) v
          (Hyperbolic.form Q)).polarBilin.Nondegenerate) ∧
      ∀ v : NumberField.InfinitePlace K,
        (ArchimedeanComparison.form v (Hyperbolic.form Q)).polarBilin.Nondegenerate := by
  letI := L.finiteDimensional
  have hQ := Hyperbolic.form_polarBilin_nondegenerate Q
    (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA)
  exact ⟨hQ, fun v => CompletedIntegralLattice.form_polarBilin_nondegenerate _ v _ hQ,
    fun v => archimedean_form_polarBilin_nondegenerate v hQ⟩

end NormEuclidean
