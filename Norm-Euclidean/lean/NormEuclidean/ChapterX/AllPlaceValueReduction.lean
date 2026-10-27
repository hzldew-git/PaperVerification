import NormEuclidean.ChapterX.NegativeLineBaseChange
import NormEuclidean.ChapterX.MixedScalarWeakApproximation

/-!
# The scalar representation case of 66:3 from the 66:1 isotropy input

Every place is the actual finite adic or infinite completion used by the
project. All comparison maps and the zero-target case are proved here.
The displayed isotropy-transfer premise is precisely the remaining
Hasse--Minkowski arithmetic input; it is not asserted as a theorem.
-/

noncomputable section

namespace NormEuclidean.AllPlaceValueReduction

open IsDedekindDomain CompletedIntegralLattice QuadraticValueRepresentation
open scoped TensorProduct

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Scalar representation over all actual completions follows from the
isotropy-transfer theorem for the single regular negative-line form.
This implication does not prove or assume a local-to-global value theorem. -/
theorem represents_of_local_representations_and_isotropy_transfer
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (a : K)
    (hHasse : (negativeLine Q a).polarBilin.Nondegenerate →
      (∀ v : HeightOneSpectrum (integerSubring K),
        ¬ (form (integerSubring K) v (negativeLine Q a)).Anisotropic) →
      (∀ w : NumberField.InfinitePlace K,
        ¬ ((negativeLine Q a).baseChange w.Completion).Anisotropic) →
      ¬ (negativeLine Q a).Anisotropic)
    (hfinite : ∀ v : HeightOneSpectrum (integerSubring K),
      ∃ x, form (integerSubring K) v Q x =
        algebraMap K (LocalField (integerSubring K) v) a)
    (hinfinite : ∀ w : NumberField.InfinitePlace K,
      ∃ x, Q.baseChange w.Completion x = algebraMap K w.Completion a) :
    ∃ x : V, Q x = a := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  apply (represents_iff_negativeLine_isotropic Q hQ a).mpr
  apply hHasse (negativeLine_regular Q hQ a ha)
  · intro v
    letI : Invertible (2 : LocalField (integerSubring K) v) :=
      invertibleOfNonzero (by norm_num)
    exact (NegativeLineBaseChange.represents_iff_completed_negativeLine_isotropic
      (F := LocalField (integerSubring K) v) Q hQ a).mp (hfinite v)
  · intro w
    letI : Invertible (2 : w.Completion) := invertibleOfNonzero (by norm_num)
    exact (NegativeLineBaseChange.represents_iff_completed_negativeLine_isotropic
      (F := w.Completion) Q hQ a).mp (hinfinite w)

/-- Global representation gives the actual finite and infinite witnesses
by inclusion. No completion comparison or representation premise is needed. -/
theorem local_representations_of_representation (Q : QuadraticForm K V) (a : K)
    (h : ∃ x : V, Q x = a) :
    (∀ v : HeightOneSpectrum (integerSubring K),
      ∃ x, form (integerSubring K) v Q x =
        algebraMap K (LocalField (integerSubring K) v) a) ∧
    (∀ w : NumberField.InfinitePlace K,
      ∃ x, Q.baseChange w.Completion x = algebraMap K w.Completion a) := by
  obtain ⟨x, hx⟩ := h
  constructor
  · intro v
    exact ⟨inclusion (integerSubring K) v x, by rw [form_inclusion, hx]⟩
  · intro w
    refine ⟨(1 : w.Completion) ⊗ₜ[K] x, ?_⟩
    simp only [QuadraticForm.baseChange_tmul, hx, Algebra.smul_def, mul_one, one_mul]

end NormEuclidean.AllPlaceValueReduction
