import NormEuclidean.ChapterX.HasseArithmetic
import NormEuclidean.ChapterX.AllPlaceValueReduction

/-!
# Hasse--Minkowski for general regular quadratic forms over number fields

Diagonal models remove any restriction equating the universes of the
base field and the vector space. Scalar extension is compared on the
entire actual tensor space. The scalar case of 66:3 is then unconditional.
-/

noncomputable section

namespace NormEuclidean.HasseMinkowski

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation
open Bong.HeADCV5.Global.NumberFieldLattice
open scoped NumberField TensorProduct

universe u v w
variable {K : Type u} [Field K] [NumberField K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [NumberField K] [FiniteDimensional K V] [FiniteDimensional K W] in
/-- Isotropy transports across any genuine quadratic-space isometry. -/
theorem isometry_isotropy {q : Bong.QuadraticSpace K V} {r : Bong.QuadraticSpace K W}
    (e : Bong.QuadraticSpace.Isometry q r) (h : ∃ x, x ≠ 0 ∧ q.quadratic x = 0) :
    ∃ y, y ≠ 0 ∧ r.quadratic y = 0 := by
  obtain ⟨x, hx, hqx⟩ := h
  exact ⟨e.toLinearEquiv x, by simpa using e.toLinearEquiv.injective.ne hx,
    (e.map_quadratic x).trans hqx⟩

/-- The all-rank isotropy theorem on an arbitrary finite-dimensional vector space. -/
theorem space_isotropic (q : Bong.QuadraticSpace K V)
    (hf : ∀ p : HeightOneSpectrum (𝓞 K), ∃ x, x ≠ 0 ∧
      (q.scalarExtension (E := p.adicCompletion K)).quadratic x = 0)
    (hi : ∀ p : NumberField.InfinitePlace K, ∃ x, x ≠ 0 ∧
      (q.scalarExtension (E := p.Completion)).quadratic x = 0) :
    ∃ x, x ≠ 0 ∧ q.quadratic x = 0 := by
  let e := q.fieldDiagonalizationIsometry
  have h := HasseArithmetic.allPlaceIsotropy q.fieldDiagonalModel
    (fun p ↦ isometry_isotropy (e.scalarExtension (E := p.adicCompletion K)) (hf p))
    (fun p ↦ isometry_isotropy (e.scalarExtension (E := p.Completion)) (hi p))
  exact isometry_isotropy e.symm h

variable [Invertible (2 : K)]

/-- O'Meara 66:1 for general regular quadratic forms and all actual completions. -/
theorem isotropic_of_all_places (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hf : ∀ p : HeightOneSpectrum (integerSubring K),
      ¬ (form (integerSubring K) p Q).Anisotropic)
    (hi : ∀ p : NumberField.InfinitePlace K, ¬ (Q.baseChange p.Completion).Anisotropic) :
    ¬ Q.Anisotropic := by
  let q := SpinorBridge.quadraticSpace Q hQ
  apply (HasseArithmetic.not_anisotropic_iff Q).mpr
  have h := space_isotropic q
    (fun p ↦ by
      obtain ⟨x, hx, hval⟩ := (HasseArithmetic.not_anisotropic_iff _).mp (hf p)
      exact ⟨x, hx, (HasseFormComparison.quadraticSpace_scalarExtension_value Q hQ x).trans hval⟩)
    (fun p ↦ by
      obtain ⟨x, hx, hval⟩ := (HasseArithmetic.not_anisotropic_iff _).mp (hi p)
      exact ⟨x, hx, (HasseFormComparison.quadraticSpace_scalarExtension_value Q hQ x).trans hval⟩)
  simpa only [q, SpinorBridge.quadraticSpace_quadratic] using h

/-- Global isotropy supplies the nonzero vectors at every actual completion. -/
theorem isotropic_iff_all_places (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) :
    ¬ Q.Anisotropic ↔
      (∀ p : HeightOneSpectrum (integerSubring K),
        ¬ (form (integerSubring K) p Q).Anisotropic) ∧
      (∀ p : NumberField.InfinitePlace K, ¬ (Q.baseChange p.Completion).Anisotropic) := by
  constructor
  · intro h
    obtain ⟨x, hx, hval⟩ := (HasseArithmetic.not_anisotropic_iff Q).mp h
    constructor
    · intro p
      apply (HasseArithmetic.not_anisotropic_iff _).mpr
      refine ⟨inclusion (integerSubring K) p x, ?_, ?_⟩
      · intro heq
        exact hx ((Module.FaithfullyFlat.one_tmul_eq_zero_iff K V x).mp heq)
      · rw [form_inclusion, hval, map_zero]
    · intro p
      apply (HasseArithmetic.not_anisotropic_iff _).mpr
      refine ⟨(1 : p.Completion) ⊗ₜ[K] x, ?_, ?_⟩
      · intro heq
        exact hx ((Module.FaithfullyFlat.one_tmul_eq_zero_iff K V x).mp heq)
      · simp only [QuadraticForm.baseChange_tmul, hval, zero_smul]
  · exact fun h ↦ isotropic_of_all_places Q hQ h.1 h.2

/-- O'Meara 66:3 for a scalar value, with no isotropy-transfer premise. -/
theorem represents_value (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (a : K)
    (hf : ∀ p : HeightOneSpectrum (integerSubring K),
      ∃ x, form (integerSubring K) p Q x = algebraMap K (LocalField _ p) a)
    (hi : ∀ p : NumberField.InfinitePlace K,
      ∃ x, Q.baseChange p.Completion x = algebraMap K p.Completion a) :
    ∃ x : V, Q x = a :=
  AllPlaceValueReduction.represents_of_local_representations_and_isotropy_transfer Q hQ a
    (fun hreg hfinite hinfinite ↦ isotropic_of_all_places _ hreg hfinite hinfinite) hf hi

/-- Exact scalar representation comparison, including the zero target. -/
theorem represents_value_iff (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (a : K) : (∃ x : V, Q x = a) ↔
      (∀ p : HeightOneSpectrum (integerSubring K),
        ∃ x, form (integerSubring K) p Q x = algebraMap K (LocalField _ p) a) ∧
      (∀ p : NumberField.InfinitePlace K,
        ∃ x, Q.baseChange p.Completion x = algebraMap K p.Completion a) :=
  ⟨AllPlaceValueReduction.local_representations_of_representation Q a,
    fun h ↦ represents_value Q hQ a h.1 h.2⟩

end NormEuclidean.HasseMinkowski
