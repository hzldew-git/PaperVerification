import NormEuclidean.ArchimedeanIdealDual

/-!
# The actual character annihilator of an ideal lattice

The Fourier phase is the fixed negative trace phase. Triviality on an
original ideal is equivalent to membership in the actual trace-dual
ideal lattice, for arbitrary mixed-space frequencies.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.IdealTraceCharacters

open NumberField NumberField.mixedEmbedding MixedTracePairing
open scoped NumberField Classical nonZeroDivisors

/-- The original real Fourier phase has exactly the integer lattice as kernel. -/
theorem fourierChar_eq_one (t : ℝ) :
    (Real.fourierChar t : ℂ) = 1 ↔ t ∈ (1 : Submodule ℤ ℝ) := by
  rw [← ArchimedeanTraceFourier.phase_eq]
  constructor
  · intro h
    have hc : AddCircle.toCircle (t : AddCircle (1 : ℝ)) =
        AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      apply Subtype.ext
      simpa only [AdelicTraceCharacter.realPhase, AddChar.coe_mk, AddCircle.toCircle_zero,
        OneMemClass.coe_one] using h
    have hz := AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hc
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    exact Submodule.mem_one.mpr ⟨n, by simpa using hn⟩
  · intro ht
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp ht
    have hz : (t : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simpa using hn⟩
    rw [hz, AddChar.map_zero_eq_one]

variable (F : Type*) [Field F] [NumberField F]

/-- The actual negative trace Fourier frequency on the complete mixed space. -/
def frequency (z : mixedSpace F) : AddChar (mixedSpace F) ℂ where
  toFun x := (Real.fourierChar (-(form F z x)) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [map_add, neg_add, Real.fourierChar.map_add_eq_mul, Circle.coe_mul]

theorem frequency_apply (z x : mixedSpace F) :
    frequency F z x = (Real.fourierChar (-(form F z x)) : ℂ) := rfl

/-- Character modulus is one for every actual mixed-space frequency and argument. -/
theorem norm_frequency (z x : mixedSpace F) : ‖frequency F z x‖ = 1 :=
  Circle.norm_coe _

/-- Each original frequency is continuous in the original mixed topology. -/
theorem continuous_frequency (z : mixedSpace F) : Continuous (frequency F z) := by
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (LinearMap.continuous_of_finiteDimensional (form F z)).neg)

/-- Frequency triviality is the literal integral mixed trace-pairing condition. -/
theorem frequency_eq_one (z x : mixedSpace F) :
    frequency F z x = 1 ↔ form F z x ∈ (1 : Submodule ℤ ℝ) := by
  rw [frequency_apply, fourierChar_eq_one, Submodule.neg_mem_iff]

/-- The actual character annihilator is the full actual trace-dual ideal lattice. -/
theorem annihilator (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (z : mixedSpace F) :
    (∀ x ∈ (I : Set F), frequency F z (mixedEmbedding F x) = 1) ↔
      z ∈ idealLattice F (ArchimedeanIdealDual.dual F I) := by
  simp_rw [frequency_eq_one]
  exact (ArchimedeanIdealDual.mem_dual_lattice F I z).symm

/-- Every actual period has phase one at a trace-dual frequency. -/
theorem frequency_lattice (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (z : idealLattice F (ArchimedeanIdealDual.dual F I)) (x : idealLattice F I) :
    frequency F z x = 1 := by
  rw [frequency_eq_one]
  have hz : (z : mixedSpace F) ∈ (form F).dualSubmodule (idealLattice F I) := by
    rw [ArchimedeanIdealDual.dual_lattice]
    exact z.2
  exact hz x x.2

/-- Translation of the argument by an actual period does not change a dual character. -/
theorem frequency_add_lattice (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (z : idealLattice F (ArchimedeanIdealDual.dual F I)) (x : mixedSpace F)
    (a : idealLattice F I) : frequency F z (x + (a : mixedSpace F)) = frequency F z x := by
  rw [AddChar.map_add_eq_mul, frequency_lattice F I z a, mul_one]

/-- The mixed character is the unchanged global infinite trace character. -/
theorem frequency_coordinates (a b : InfiniteAdeleRing F) :
    frequency F (InfiniteTraceHaar.coordinates F b) (InfiniteTraceHaar.coordinates F a) =
      AdelicTraceCharacter.infiniteCharacter (a * b) := by
  rw [frequency_apply, (symmetric F).eq, ← MixedTracePairing.character]

end NormEuclidean.IdealTraceCharacters
