import NormEuclidean.PadicTraceCharacter
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The constructed local trace character has the actual inverse different as annihilator

The base character was constructed with its exact integral kernel.
Composing it with the actual determinant trace therefore identifies the
annihilator of an actual integral closure with its codifferent. The
statement concerns finite extensions of Q_p and actual algebraic integer
rings, rather than an assumed trace-character conductor comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.LocalTraceAnnihilator

open scoped nonZeroDivisors Classical

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra ℚ_[p] L]

/-- The actual p-adic trace character, with the constructed base character. -/
def traceCharacter : L →+ RationalPrimaryCharacter.Circle :=
  (PadicTraceCharacter.character p).comp (Algebra.trace ℚ_[p] L).toAddMonoidHom

/-- The trace character vanishes exactly when the actual trace is p-adically integral. -/
theorem trace_kernel (x : L) :
    traceCharacter p L x = 0 ↔ ‖Algebra.trace ℚ_[p] L x‖ ≤ 1 :=
  PadicTraceCharacter.kernel_iff p _

/-- The original integral subring is exactly the actual unit norm ball. -/
theorem integral_range (x : ℚ_[p]) :
    x ∈ (algebraMap ℤ_[p] ℚ_[p]).range ↔ ‖x‖ ≤ 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

variable (B : Type*) [CommRing B] [IsDedekindDomain B]
  [Algebra ℤ_[p] B] [Algebra B L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [IsScalarTower ℤ_[p] B L]
  [IsFractionRing B L] [FiniteDimensional ℚ_[p] L]
  [Algebra.IsSeparable ℚ_[p] L] [IsIntegralClosure B ℤ_[p] L]

include L in
/-- The actual fraction-field embeddings prove torsion freeness of the integral ring. -/
theorem integralTorsionFree : Module.IsTorsionFree ℤ_[p] B := by
  letI : Module.IsTorsionFree ℤ_[p] L := Module.IsTorsionFree.trans ℚ_[p]
  exact Function.Injective.moduleIsTorsionFree (algebraMap B L) (IsFractionRing.injective B L)
    (fun a b ↦ (IsScalarTower.toAlgHom ℤ_[p] B L).toLinearMap.map_smul a b)

/-- The actual inverse relative different in the original finite extension. -/
def codifferent : FractionalIdeal B⁰ L :=
  letI := integralTorsionFree p L B
  (differentIdeal ℤ_[p] B : FractionalIdeal B⁰ L)⁻¹

/-- The literal codifferent is the actual trace-dual fractional ideal. -/
theorem codifferent_eq_dual :
    codifferent p L B = FractionalIdeal.dual ℤ_[p] ℚ_[p] (1 : FractionalIdeal B⁰ L) := by
  letI := integralTorsionFree p L B
  rw [codifferent, coeIdeal_differentIdeal ℤ_[p] ℚ_[p] L B, inv_inv]

/-- The annihilator of the actual integral ring is precisely its actual codifferent. -/
theorem integral_annihilator (x : L) :
    (∀ a : B, traceCharacter p L (x * algebraMap B L a) = 0) ↔
      x ∈ codifferent p L B := by
  rw [codifferent_eq_dual,
    FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal B⁰ L) ≠ 0)]
  simp only [Algebra.traceForm_apply, FractionalIdeal.mem_one_iff]
  constructor
  · rintro h a ⟨b, rfl⟩
    exact (integral_range p _).mpr ((trace_kernel p L _).mp (h b))
  · intro h a
    apply (trace_kernel p L _).mpr
    exact (integral_range p _).mp (h _ ⟨a, rfl⟩)

/-- Every integral product is annihilated by a member of the actual codifferent. -/
theorem on_codifferent (x : L) (hx : x ∈ codifferent p L B) (a : B) :
    traceCharacter p L (x * algebraMap B L a) = 0 :=
  (integral_annihilator p L B x).mpr hx a

end NormEuclidean.LocalTraceAnnihilator
