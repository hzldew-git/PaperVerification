import NormEuclidean.CompletedRationalPrime
import NormEuclidean.CompletedTensorIntegers
import NormEuclidean.CompletedPadicIntegers

/-!
# Canonical completed coefficients and the original actual p-adic coefficients

The rational-place prime is identified with the actual residue
characteristic. Continuous coefficient homomorphisms agree on dense
rationals, hence everywhere. The actual trace and integral coefficient
range are then compared, not supplied as compatibility assumptions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedCoefficientComparison

open NumberField IsDedekindDomain Bong.NumberFieldCompletion
open CompletedTensorProduct CompletedTensorIntegers
open scoped NumberField NormEuclidean.CompletedTensorProduct

variable (F : Type*) [Field F] [NumberField F]

attribute [local instance] coefficientAlgebra baseIntegerAlgebra factorIntegerAlgebra
  factorIntegerTower CompletedPadicBase.padicAlgebra

local instance rationalAdicAlgebra (q : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (q.adicCompletion ℚ) :=
  HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ q

instance rationalPrimeFact (q : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (CompletedRationalPrime.prime q : ℕ).Prime := ⟨(CompletedRationalPrime.prime q).2⟩

/-- Equality of primes gives the literal p-adic field identification. -/
def padicCast {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (h : p = r) : ℚ_[p] ≃+* ℚ_[r] := by
  subst r
  exact RingEquiv.refl _

theorem padicCast_continuous {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (h : p = r) :
    Continuous (padicCast h) := by
  subst r
  exact continuous_id

def integerCast {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (h : p = r) : ℤ_[p] ≃+* ℤ_[r] := by
  subst r
  exact RingEquiv.refl _

theorem cast_integer {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (h : p = r) (z : ℤ_[p]) :
    padicCast h (z : ℚ_[p]) = (integerCast h z : ℚ_[r]) := by
  subst r
  rfl

/-- The actual rational-place completion is the p-adic field of its original prime. -/
def fieldEquiv (q : HeightOneSpectrum (𝓞 ℚ)) :
    Base q ≃+* ℚ_[(CompletedRationalPrime.prime q : ℕ)] :=
  (baseEquiv q).trans (Rat.HeightOneSpectrum.adicCompletion.padicEquiv q).toRingEquiv

theorem fieldEquiv_continuous (q : HeightOneSpectrum (𝓞 ℚ)) : Continuous (fieldEquiv q) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv q).continuous.comp
    (relativeFinitePlaceCompletionRingHom_isometry q).continuous

def integralEquiv (q : HeightOneSpectrum (𝓞 ℚ)) :
    integerRing q ≃+* ℤ_[(CompletedRationalPrime.prime q : ℕ)] :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv q).toRingEquiv

theorem field_integer (q : HeightOneSpectrum (𝓞 ℚ)) (r : integerRing q) :
    fieldEquiv q (algebraMap (integerRing q) (Base q) r) =
      (integralEquiv q r : ℚ_[(CompletedRationalPrime.prime q : ℕ)]) := by
  change (Rat.HeightOneSpectrum.adicCompletion.padicEquiv q)
    (baseEquiv q ((baseEquiv q).symm (r : q.adicCompletion ℚ))) = _
  rw [RingEquiv.apply_symm_apply]
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.coe_padicIntEquiv_apply q r).symm

/-- The base field is compared with the p-adic field already constructed for this actual factor. -/
def actualFieldEquiv (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    Base q ≃+* ℚ_[CompletedPadicBase.rationalPrime (prime F q w)] :=
  (fieldEquiv q).trans (padicCast (CompletedRationalPrime.factor_rationalPrime q w).symm)

theorem actualFieldEquiv_continuous (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    Continuous (actualFieldEquiv F q w) :=
  (padicCast_continuous _).comp (fieldEquiv_continuous q)

def actualIntegralEquiv (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    integerRing q ≃+* ℤ_[CompletedPadicBase.rationalPrime (prime F q w)] :=
  (integralEquiv q).trans (integerCast (CompletedRationalPrime.factor_rationalPrime q w).symm)

theorem actual_field_integer (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q)
    (r : integerRing q) :
    actualFieldEquiv F q w (algebraMap (integerRing q) (Base q) r) =
      (actualIntegralEquiv F q w r : ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]) := by
  change padicCast _ (fieldEquiv q (algebraMap (integerRing q) (Base q) r)) = _
  rw [field_integer, cast_integer]
  rfl

theorem rational_dense (q : HeightOneSpectrum (𝓞 ℚ)) : DenseRange (algebraMap ℚ (Base q)) := by
  have hc := (AddMonoidHomClass.isometry_of_norm (baseEquiv q).symm
    (baseEquiv_symm_norm q)).continuous
  have hd := (baseEquiv q).symm.surjective.denseRange.comp (q.denseRange_algebraMap ℚ) hc
  have he : (baseEquiv q).symm.toRingHom.comp (algebraMap ℚ (q.adicCompletion ℚ)) =
      algebraMap ℚ (Base q) := Subsingleton.elim _ _
  change DenseRange ((baseEquiv q).symm.toRingHom.comp
    (algebraMap ℚ (q.adicCompletion ℚ))) at hd
  rwa [he] at hd

/-- The two actual coefficient maps agree by continuity and rational density. -/
theorem coefficient_eq (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) (a : Base q) :
    algebraMap (Base q) ((prime F q w).adicCompletion F) a =
      algebraMap ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]
        ((prime F q w).adicCompletion F) (actualFieldEquiv F q w a) := by
  have he := (rational_dense q).equalizer (coefficient_continuous F q w)
    ((CompletedPadicBase.algebraMap_continuous (prime F q w)).comp
      (actualFieldEquiv_continuous F q w)) ?_
  · exact congrFun he a
  · have hr : (algebraMap (Base q) ((prime F q w).adicCompletion F)).comp
        (algebraMap ℚ (Base q)) =
      ((algebraMap ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]
        ((prime F q w).adicCompletion F)).comp (actualFieldEquiv F q w).toRingHom).comp
          (algebraMap ℚ (Base q)) := Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* ((prime F q w).adicCompletion F) ↦ (f : ℚ → _)) hr

/-- The literal determinant traces agree under the proved actual coefficient comparison. -/
theorem trace_eq (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q)
    (x : (prime F q w).adicCompletion F) :
    actualFieldEquiv F q w (Algebra.trace (Base q) ((prime F q w).adicCompletion F) x) =
      Algebra.trace ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]
        ((prime F q w).adicCompletion F) x := by
  have hc : (algebraMap ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]
      ((prime F q w).adicCompletion F)).comp (actualFieldEquiv F q w).toRingHom =
        (RingEquiv.refl ((prime F q w).adicCompletion F)).toRingHom.comp
          (algebraMap (Base q) ((prime F q w).adicCompletion F)) := by
    apply RingHom.ext
    intro a
    exact (coefficient_eq F q w a).symm
  have h := Algebra.trace_eq_of_equiv_equiv (actualFieldEquiv F q w)
    (RingEquiv.refl ((prime F q w).adicCompletion F)) hc x
  exact (congrArg (actualFieldEquiv F q w) h).trans (by rw [RingEquiv.apply_symm_apply]; rfl)

/-- The two literal integral coefficient ranges correspond under the actual field equivalence. -/
theorem integer_range_iff (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) (a : Base q) :
    actualFieldEquiv F q w a ∈
        (algebraMap ℤ_[CompletedPadicBase.rationalPrime (prime F q w)]
          ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]).range ↔
      a ∈ (algebraMap (integerRing q) (Base q)).range := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(actualIntegralEquiv F q w).symm z, (actualFieldEquiv F q w).injective ?_⟩
    rw [actual_field_integer, RingEquiv.apply_symm_apply]
    exact hz
  · rintro ⟨r, rfl⟩
    exact ⟨actualIntegralEquiv F q w r, (actual_field_integer F q w r).symm⟩

/-- Integral completed trace is precisely integral actual p-adic trace. -/
theorem trace_integral_iff (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q)
    (x : (prime F q w).adicCompletion F) :
    Algebra.trace (Base q) ((prime F q w).adicCompletion F) x ∈
        (algebraMap (integerRing q) (Base q)).range ↔
      Algebra.trace ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]
          ((prime F q w).adicCompletion F) x ∈
        (algebraMap ℤ_[CompletedPadicBase.rationalPrime (prime F q w)]
          ℚ_[CompletedPadicBase.rationalPrime (prime F q w)]).range := by
  rw [← trace_eq F q w x, integer_range_iff]

end NormEuclidean.CompletedCoefficientComparison
