import NormEuclidean.CompletedCoefficientComparison

/-!
# Actual p-adic traces and trace characters over a rational prime

The canonical tensor trace decomposition is compared with the actual
Q_p coefficient algebras of the original completions. The sum of their
constructed local trace characters is the rational primary character
of the literal global trace. This is a fixed-rational-prime identity,
not yet the full global adelic character product.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedTraceDecomposition

open NumberField IsDedekindDomain Bong.NumberFieldCompletion
open CompletedTensorProduct CompletedTensorIntegers CompletedCoefficientComparison
open scoped NumberField NormEuclidean.CompletedTensorProduct

variable (F : Type*) [Field F] [NumberField F]

attribute [local instance] coefficientAlgebra baseIntegerAlgebra factorIntegerAlgebra
  factorIntegerTower CompletedPadicBase.padicAlgebra

theorem padicCast_cancel {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (h : p = r) (x : ℚ_[r]) : padicCast h (padicCast h.symm x) = x := by
  subst r
  rfl

theorem character_cast {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (h : p = r) (x : ℚ_[p]) :
    PadicTraceCharacter.character r (padicCast h x) = PadicTraceCharacter.character p x := by
  subst r
  rfl

/-- The actual trace of one factor transported to the common rational p-adic field. -/
theorem trace_factor (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q)
    (x : (prime F q w).adicCompletion F) :
    fieldEquiv q (Algebra.trace (Base q) ((prime F q w).adicCompletion F) x) =
      padicCast (CompletedRationalPrime.factor_rationalPrime q w)
        (Algebra.trace ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]
          ((prime F q w).adicCompletion F) x) := by
  rw [← CompletedCoefficientComparison.trace_eq F q w x]
  simp only [actualFieldEquiv, RingEquiv.trans_apply, padicCast_cancel]

/-- The global trace is the sum of literal original Q_p local traces over the rational prime. -/
theorem global_trace (q : HeightOneSpectrum (𝓞 ℚ)) (x : F) :
    algebraMap ℚ ℚ_[CompletedRationalPrime.prime q] (Algebra.trace ℚ F x) =
      ∑ w : Place F q, padicCast (CompletedRationalPrime.factor_rationalPrime q w)
        (Algebra.trace ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]
          ((prime F q w).adicCompletion F)
          (algebraMap F ((prime F q w).adicCompletion F) x)) := by
  have hr : (fieldEquiv q).toRingHom.comp (algebraMap ℚ (Base q)) =
      algebraMap ℚ ℚ_[CompletedRationalPrime.prime q] := Subsingleton.elim _ _
  calc
    _ = fieldEquiv q (algebraMap ℚ (Base q) (Algebra.trace ℚ F x)) :=
      (congrArg (fun f : ℚ →+* ℚ_[CompletedRationalPrime.prime q] ↦
        f (Algebra.trace ℚ F x)) hr).symm
    _ = ∑ w : Place F q, fieldEquiv q
        (Algebra.trace (Base q) ((prime F q w).adicCompletion F)
          (algebraMap F ((prime F q w).adicCompletion F) x)) := by
      rw [CompletedTensorProduct.global_trace_eq_sum, map_sum]
    _ = _ := Finset.sum_congr rfl fun w _ ↦ trace_factor F q w _

/-- At one rational prime, the actual local trace characters sum to the global primary trace. -/
theorem trace_character_sum (q : HeightOneSpectrum (𝓞 ℚ)) (x : F) :
    RationalPrimaryCharacter.character (CompletedRationalPrime.prime q)
        (Algebra.trace ℚ F x) =
      ∑ w : Place F q, LocalTraceAnnihilator.traceCharacter
        (CompletedPadicBase.rationalPrime (prime F q w)) ((prime F q w).adicCompletion F)
        (algebraMap F ((prime F q w).adicCompletion F) x) := by
  have h := congrArg (PadicTraceCharacter.character (CompletedRationalPrime.prime q))
    (global_trace F q x)
  rw [map_sum] at h
  change PadicTraceCharacter.character (CompletedRationalPrime.prime q)
    ((Algebra.trace ℚ F x : ℚ) : ℚ_[CompletedRationalPrime.prime q]) = _ at h
  rw [PadicTraceCharacter.character_rat] at h
  refine h.trans (Finset.sum_congr rfl fun w _ ↦ ?_)
  exact character_cast (CompletedRationalPrime.factor_rationalPrime q w) _

end NormEuclidean.CompletedTraceDecomposition
