import NormEuclidean.LocalTraceAnnihilator
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Genuine unit-modulus complex trace characters

The constructed rational-circle characters are embedded injectively
into the usual complex unit circle. Their computed kernels and trace
annihilators are unchanged. These are actual complex-valued characters,
so they can be used directly in Haar and Fourier integrals.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.ComplexTraceCharacter

open scoped Classical

/-- The actual inclusion of the rational circle into the real unit-period circle. -/
def realClass : RationalPrimaryCharacter.Circle →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ)) (AddSubgroup.zmultiples (1 : ℝ))
    (Rat.castHom ℝ).toAddMonoidHom (by
      rintro q ⟨n, rfl⟩
      exact ⟨n, by simp⟩)

/-- The inclusion has its literal value on each original rational class. -/
theorem realClass_rat (q : ℚ) : realClass (q : RationalPrimaryCharacter.Circle) =
    ((q : ℝ) : AddCircle (1 : ℝ)) := rfl

/-- The rational-to-real circle inclusion loses no character kernel information. -/
theorem realClass_kernel (q : RationalPrimaryCharacter.Circle) : realClass q = 0 ↔ q = 0 := by
  induction q using QuotientAddGroup.induction_on with
  | H q =>
    rw [realClass_rat]
    simp only [AddCircle.coe_eq_zero_iff, zsmul_eq_mul, mul_one]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by exact_mod_cast hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by exact_mod_cast hn⟩

/-- The literal exponential phase of an actual rational circle class. -/
def phase : AddChar RationalPrimaryCharacter.Circle ℂ where
  toFun q := (AddCircle.toCircle (realClass q) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp only [map_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The phase is faithful on the rational circle. -/
theorem phase_kernel (q : RationalPrimaryCharacter.Circle) : phase q = 1 ↔ q = 0 := by
  constructor
  · intro h
    change (AddCircle.toCircle (realClass q) : ℂ) = 1 at h
    have he : AddCircle.toCircle (realClass q) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      apply Subtype.ext
      simpa only [AddCircle.toCircle_zero, Circle.coe_one] using h
    exact (realClass_kernel q).mp ((AddCircle.injective_toCircle one_ne_zero) he)
  · rintro rfl
    exact phase.map_zero_eq_one

/-- The original phase has complex norm one at every actual input. -/
theorem phase_norm (q : RationalPrimaryCharacter.Circle) : ‖phase q‖ = 1 :=
  Circle.norm_coe _

variable (p : ℕ) [Fact p.Prime]

/-- The constructed complex-valued p-adic character. -/
def base : AddChar ℚ_[p] ℂ := phase.compAddMonoidHom (PadicTraceCharacter.character p)

/-- The actual complex character has exactly the proved integral kernel. -/
theorem base_kernel (x : ℚ_[p]) : base p x = 1 ↔ ‖x‖ ≤ 1 := by
  rw [base, AddChar.compAddMonoidHom_apply, phase_kernel, PadicTraceCharacter.kernel_iff]

/-- Unit modulus is a theorem about the constructed complex character. -/
theorem base_norm (x : ℚ_[p]) : ‖base p x‖ = 1 := phase_norm _

/-- The actual complex character is locally constant. -/
theorem base_locallyConstant : IsLocallyConstant (base p) :=
  (PadicTraceCharacter.locallyConstant p).comp phase

/-- Continuity follows from the proved local constancy. -/
theorem base_continuous : Continuous (base p) := (base_locallyConstant p).continuous

/-- The base complex character is nontrivial at the actual inverse prime. -/
theorem base_nontrivial : base p (p : ℚ_[p])⁻¹ ≠ 1 := by
  rw [ne_eq, base, AddChar.compAddMonoidHom_apply, phase_kernel]
  exact PadicTraceCharacter.nontrivial p

variable (L : Type*) [Field L] [Algebra ℚ_[p] L]

/-- The actual determinant-trace complex character of a finite p-adic extension. -/
def trace : AddChar L ℂ := phase.compAddMonoidHom (LocalTraceAnnihilator.traceCharacter p L)

/-- The complex trace character has the exact same literal trace-integrality kernel. -/
theorem trace_kernel (x : L) : trace p L x = 1 ↔ ‖Algebra.trace ℚ_[p] L x‖ ≤ 1 := by
  rw [trace, AddChar.compAddMonoidHom_apply, phase_kernel, LocalTraceAnnihilator.trace_kernel]

/-- The actual extension trace character also has unit complex modulus. -/
theorem trace_norm (x : L) : ‖trace p L x‖ = 1 := phase_norm _

/-- The actual trace character is continuous on each finite normed p-adic field extension. -/
theorem trace_continuous (M : Type*) [NormedField M] [NormedAlgebra ℚ_[p] M]
    [FiniteDimensional ℚ_[p] M] : Continuous (trace p M) := by
  change Continuous (fun x : M ↦ base p (Algebra.trace ℚ_[p] M x))
  exact (base_continuous p).comp (Algebra.trace ℚ_[p] M).continuous_of_finiteDimensional

end NormEuclidean.ComplexTraceCharacter
