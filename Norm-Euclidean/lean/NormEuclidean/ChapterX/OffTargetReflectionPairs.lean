import NormEuclidean.ChapterX.ReflectionVectorNeighborhoods
import NormEuclidean.ChapterX.QuadraticValueNormalization

/-!
# Integral reflection pairs at good off-target primes

Only the actual completed carrier at the specified prime is used.
Global norm integrality of the module, global unit values and membership
of the reflecting vectors at the controlled primes are unnecessary.
-/

noncomputable section

namespace NormEuclidean.OffTargetReflectionPairs

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation LocalPrimitivePairing
  ProperSpinor SpinorBaseChange AdelicOrthogonal AdelicApproximation ReflectionApproximation

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local instance finiteCharZero (p : HeightOneSpectrum (integerSubring K)) :
    CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _

local instance finiteInvertibleTwo (p : HeightOneSpectrum (integerSubring K)) :
    Invertible (2 : LocalField (integerSubring K) p) := invertibleOfNonzero (by norm_num)

/-- The actual global reflection pair localizes to the pair in the included vectors. -/
theorem localize_pair_eq (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0)
    (p : HeightOneSpectrum (integerSubring K)) :
    localizeProper Q (doubleReflection Q hQ x hx y hy) p =
      doubleReflection (form (integerSubring K) p Q)
        (form_polarBilin_nondegenerate (integerSubring K) p Q hQ)
        (inclusion (integerSubring K) p x) (form_inclusion_ne_zero _ p Q x hx)
        (inclusion (integerSubring K) p y) (form_inclusion_ne_zero _ p Q y hy) := by
  apply Subtype.ext
  apply Subtype.ext
  exact equiv_doubleReflection Q (integerSubring K) hQ x hx y hy p

/-- Equal global values give the actual local Wall kernel at every finite prime. -/
theorem localize_pair_spinorNorm (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0) (hxy : Q x = Q y)
    (p : HeightOneSpectrum (integerSubring K)) :
    properAmbientSpinorNormHom (form (integerSubring K) p Q)
      (form_polarBilin_nondegenerate (integerSubring K) p Q hQ)
      (localizeProper Q (doubleReflection Q hQ x hx y hy) p) = 1 := by
  rw [localize_pair_eq]
  apply doubleReflection_spinorNorm_eq_one_of_value_eq
  rw [form_inclusion, form_inclusion, hxy]

set_option backward.isDefEq.respectTransparency false in
/-- Self-duality and a local unit value make the pair integral at this actual prime. -/
theorem localize_pair_mem_stabilizer (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Submodule (integerSubring K) V)
    (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0) (hxy : Q x = Q y)
    (p : HeightOneSpectrum (integerSubring K))
    (hself : SelfDual (LocalRing (integerSubring K) p) (halfPolar (form _ p Q))
      (carrier (integerSubring K) p L))
    (hxL : inclusion (integerSubring K) p x ∈ carrier (integerSubring K) p L)
    (hyL : inclusion (integerSubring K) p y ∈ carrier (integerSubring K) p L)
    (hunit : p.valuation K (Q x) = 1) :
    localizeProper Q (doubleReflection Q hQ x hx y hy) p ∈
      properStabilizerWithin (form (integerSubring K) p Q) (carrier _ p L) := by
  let P := form (integerSubring K) p Q
  have hdiag (z : Space (V := V) (integerSubring K) p) : halfPolar P z z = P z := by
    simp [halfPolar_apply, P.polar_self, nsmul_eq_mul]
  have hint (z) (hz : z ∈ carrier (integerSubring K) p L) :
      P z ∈ LocalRing (integerSubring K) p := by
    have h := (hself z).mp hz z hz
    rwa [hdiag] at h
  have hinv : (P (inclusion (integerSubring K) p x))⁻¹ ∈ LocalRing (integerSubring K) p := by
    rw [form_inclusion, ← map_inv₀]
    exact (QuadraticValueNormalization.local_unit_membership _ p hunit).2
  have hinvy : (P (inclusion (integerSubring K) p y))⁻¹ ∈ LocalRing (integerSubring K) p := by
    rw [form_inclusion, ← hxy]
    simpa only [P, form_inclusion] using hinv
  rw [localize_pair_eq]
  exact doubleReflection_mem_properStabilizerWithin P
    (form_polarBilin_nondegenerate (integerSubring K) p Q hQ)
    (LocalRing (integerSubring K) p) (carrier _ p L) hint
    (inclusion _ p x) (form_inclusion_ne_zero _ p Q x hx) hxL hinv
    (inclusion _ p y) (form_inclusion_ne_zero _ p Q y hy) hyL hinvy

end NormEuclidean.OffTargetReflectionPairs
