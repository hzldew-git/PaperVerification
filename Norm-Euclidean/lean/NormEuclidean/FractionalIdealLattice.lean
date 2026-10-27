import NormEuclidean.LatticeOperations
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Fractional ideals as full rank-one modules and their content

These lemmas use actual fractional ideals, including nonprincipal ones.
They supply the common module facts for ideal unary and hyperbolic lattices.
-/

namespace NormEuclidean.FractionalIdealLattice

open scoped nonZeroDivisors

variable {K : Type*} [Field K] {R : Subring K} [IsFractionRing R K]

omit [IsFractionRing R K] in
/-- Membership in the unit fractional ideal is literal membership in the base subring. -/
theorem mem_one_iff (x : K) : x ∈ (1 : FractionalIdeal R⁰ K) ↔ x ∈ R := by
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ r.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

omit [IsFractionRing R K] in
/-- Every nonzero fractional ideal contains a nonzero ambient scalar. -/
theorem exists_nonzero (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ x ∈ I, x ≠ (0 : K) := by
  apply (I : Submodule R K).ne_bot_iff.mp
  intro h
  apply hI
  apply FractionalIdeal.coeToSubmodule_injective
  simpa only [FractionalIdeal.coe_zero] using h

omit [IsFractionRing R K] in
/-- Nonzero fractional ideals span the entire one-dimensional ambient field. -/
theorem full (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    Submodule.span K (I : Set K) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := exists_nonzero I hI
  apply top_unique
  intro y _
  have h := (Submodule.span K (I : Set K)).smul_mem (y / x) (Submodule.subset_span hx)
  simpa only [smul_eq_mul, div_mul_cancel₀ _ hx0] using h

omit [IsFractionRing R K] in
/-- Fractional ideals over a Noetherian domain are finitely generated modules. -/
theorem fg [IsNoetherianRing R] (I : FractionalIdeal R⁰ K) :
    (I : Submodule R K).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl I

/-- The coefficient ideal of the ambient scalar one is the original fractional ideal. -/
theorem coefficient_one [IsNoetherianRing R] (I : FractionalIdeal R⁰ K) :
    GeneralContent.coefficientIdeal (I : Submodule R K) (fg I) 1 one_ne_zero = I := by
  apply FractionalIdeal.coeToSubmodule_injective
  ext a
  change a • (1 : K) ∈ (I : Submodule R K) ↔ a ∈ I
  simp only [smul_eq_mul, mul_one, FractionalIdeal.mem_coe]

/-- The intrinsic content of one in an ideal module is the inverse ideal. -/
theorem content_one [IsNoetherianRing R] (I : FractionalIdeal R⁰ K) :
    GeneralContent.contentIdeal (I : Submodule R K) (fg I) 1 = I⁻¹ := by
  rw [GeneralContent.contentIdeal_of_ne_zero _ _ _ one_ne_zero, coefficient_one]

/-- The full scalar content formula, with no principal-ideal assumption. -/
theorem content_scalar [IsDedekindDomain R] (I : FractionalIdeal R⁰ K) (a : K) :
    GeneralContent.contentIdeal (I : Submodule R K) (fg I) a =
      FractionalIdeal.spanSingleton R⁰ a * I⁻¹ := by
  have h := GeneralContent.contentIdeal_smul (I : Submodule R K) (fg I) a (1 : K)
  simpa only [smul_eq_mul, mul_one, content_one] using h

/-- Principal ideal membership in normalized scalar coordinates. -/
theorem mem_spanSingleton_iff (a : K) (ha : a ≠ 0) (x : K) :
    x ∈ FractionalIdeal.spanSingleton R⁰ a ↔ a⁻¹ * x ∈ R := by
  rw [FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨r, rfl⟩
    change a⁻¹ * ((r : K) * a) ∈ R
    simpa only [mul_left_comm, inv_mul_cancel₀ ha, mul_one] using r.property
  · intro hx
    refine ⟨⟨a⁻¹ * x, hx⟩, ?_⟩
    change (a⁻¹ * x) * a = x
    rw [mul_right_comm, inv_mul_cancel₀ ha, one_mul]

/-- The module rank of a nonzero fractional ideal is one, without freeness. -/
theorem finrank (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    Module.finrank R (I : Submodule R K) = 1 := by
  letI := ScalarExtension.localizedSubtype (I : Submodule R K) (full I hI)
  calc
    Module.finrank R (I : Submodule R K) = Module.finrank R K :=
      (IsLocalizedModule.finrank_eq R⁰ (I : Submodule R K).subtype le_rfl).symm
    _ = Module.finrank K K :=
      congrArg Cardinal.toNat (IsLocalization.rank_eq (N := K) K R⁰ le_rfl).symm
    _ = 1 := Module.finrank_self K

/-- A nonzero fractional ideal is free precisely when it is principal.
Thus the ideal models retain exactly the possible obstruction to an integral basis. -/
theorem free_iff_isPrincipal (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    Module.Free R (I : Submodule R K) ↔ (I : Submodule R K).IsPrincipal := by
  constructor
  · intro hfree
    letI := hfree
    obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one (finrank I hI)
    exact Module.isPrincipal_submodule_iff.mp (e.isPrincipal_iff.mp inferInstance)
  · intro hprincipal
    obtain ⟨a, ha⟩ := (FractionalIdeal.isPrincipal_iff I).mp hprincipal
    have ha0 : a ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mp (ha ▸ hI)
    have hsub : Submodule.span R {a} = (I : Submodule R K) := by
      rw [ha, FractionalIdeal.coe_spanSingleton]
    exact Module.Free.of_equiv ((LinearEquiv.toSpanNonzeroSingleton R K a ha0).trans
      (LinearEquiv.ofEq _ _ hsub))

end NormEuclidean.FractionalIdealLattice
