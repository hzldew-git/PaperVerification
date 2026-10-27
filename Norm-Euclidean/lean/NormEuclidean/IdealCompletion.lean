import NormEuclidean.ChapterX.VolumeLocalization
import Mathlib.RingTheory.FractionalIdeal.Extended

/-!
# Fractional ideals in the actual finite completions

Extension of fractional ideals is identified with the actual completed scalar
span. The completed DVR makes the ideal principal, and extension preserves its
inverse. Both reciprocal generators are obtained without a global PID assumption.
-/

noncomputable section

namespace NormEuclidean.IdealCompletion

open IsDedekindDomain CompletedIntegralLattice
open scoped nonZeroDivisors

variable {K : Type*} [Field K]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

local instance : IsFractionRing (LocalRing R v) (LocalField R v) :=
  inferInstanceAs (IsFractionRing (v.adicCompletionIntegers K) (LocalField R v))

local instance : IsPrincipalIdealRing (LocalRing R v) :=
  inferInstanceAs (IsPrincipalIdealRing (v.adicCompletionIntegers K))

/-- The original integer inclusion into the actual completed valuation ring. -/
def integerMap : R →+* LocalRing R v where
  toFun r := ⟨algebraMap K (LocalField R v) (r : K), algebraMap_mem R v r.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Every original nonzero integer stays nonzero in the completed integer ring. -/
theorem maps_nonzero : R⁰ ≤ Submonoid.comap (integerMap R v) (LocalRing R v)⁰ := by
  intro r hr
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have hfield := congrArg (fun a : LocalRing R v ↦ (a : LocalField R v)) h
  have hrK : (r : K) = 0 := (map_eq_zero (algebraMap K (LocalField R v))).mp hfield
  exact nonZeroDivisors.ne_zero hr (Subtype.ext hrK)

/-- Localization of this integer inclusion is the original field inclusion. -/
theorem fieldMap_eq :
    IsLocalization.map (S := K) (LocalField R v) (integerMap R v) (maps_nonzero R v) =
      algebraMap K (LocalField R v) := by
  apply IsLocalization.ringHom_ext R⁰
  ext r
  rw [RingHom.comp_apply, IsLocalization.map_eq]
  rfl

/-- Actual extension of fractional ideals to the completed DVR. -/
def map : FractionalIdeal R⁰ K →+* FractionalIdeal (LocalRing R v)⁰ (LocalField R v) :=
  FractionalIdeal.extendedHom' (M := R⁰) (N := (LocalRing R v)⁰)
    (f := integerMap R v) (LocalField R v) (maps_nonzero R v)

/-- The extended ideal is literally the completed scalar span of the original module. -/
theorem coe_map (I : FractionalIdeal R⁰ K) :
    (map R v I : Submodule (LocalRing R v) (LocalField R v)) =
      VolumeLocalization.scalarSpan R v (I : Submodule R K) := by
  change (FractionalIdeal.extended (LocalField R v) (maps_nonzero R v) I :
    Submodule (LocalRing R v) (LocalField R v)) = _
  rw [FractionalIdeal.coe_extended_eq_span, fieldMap_eq]
  rfl

/-- Nonzero ideals remain nonzero under completion. -/
theorem map_ne_zero (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) : map R v I ≠ 0 := by
  have h := congrArg (map R v) (mul_inv_cancel₀ hI)
  rw [map_mul, map_one] at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- A single reciprocal pair generates the completed ideal and its inverse. -/
theorem exists_reciprocal_generator (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ a : LocalField R v, a ≠ 0 ∧
      VolumeLocalization.scalarSpan R v (I : Submodule R K) =
        Submodule.span (LocalRing R v) {a} ∧
      VolumeLocalization.scalarSpan R v ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) =
        Submodule.span (LocalRing R v) {a⁻¹} := by
  obtain ⟨a, ha⟩ := (FractionalIdeal.isPrincipal_iff (map R v I)).mp inferInstance
  have ha0 : a ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mp
    (ha ▸ map_ne_zero R v I hI)
  refine ⟨a, ha0, ?_, ?_⟩
  · rw [← coe_map, ha, FractionalIdeal.coe_spanSingleton]
  · have hinv : map R v I⁻¹ = FractionalIdeal.spanSingleton (LocalRing R v)⁰ a⁻¹ := by
      rw [map_inv₀, ha, FractionalIdeal.spanSingleton_inv]
    rw [← coe_map, hinv, FractionalIdeal.coe_spanSingleton]

end NormEuclidean.IdealCompletion
