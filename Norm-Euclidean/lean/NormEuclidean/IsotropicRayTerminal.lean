import NormEuclidean.NumberField
import NormEuclidean.CompletedHyperbolic
import NormEuclidean.ValuationRayContent

/-!
# Norm descent on arbitrary global isotropic rays

Clearing a denominator extends the proved integral descent to every
nonzero isotropic vector. The terminal scalar determines its content in
every actual finite completion.
-/

noncomputable section

namespace NormEuclidean.IsotropicRayTerminal

open IsDedekindDomain CompletedIntegralLattice
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- No integrality assumption is needed on the initial isotropic vector. -/
theorem exists_terminal (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (z : Hyperbolic K V)
    (hz : z ≠ 0) (hiso : Hyperbolic.q Q z = 0) :
    ∃ g : Hyperbolic.Aut (Q := Q) L.carrier, ∃ c : Kˣ,
      g z = (c : K) • Hyperbolic.e := by
  obtain ⟨d, hd, hdz⟩ := ScalarExtension.exists_denominator L.hyperbolic.carrier
    L.hyperbolic.full z
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have hdz0 : (d : K) • z ≠ 0 := smul_ne_zero hdK hz
  have hdQ : Hyperbolic.q Q ((d : K) • z) = 0 := by
    change Hyperbolic.form Q ((d : K) • z) = 0
    rw [QuadraticMap.map_smul]
    change ((d : K) * (d : K)) * Hyperbolic.q Q z = 0
    rw [hiso, mul_zero]
  obtain ⟨g, c, _, hc, hgc, _⟩ := numberField_norm_descent Q L hA hE hdz hdz0 hdQ
  refine ⟨g, Units.mk0 (c / (d : K)) (div_ne_zero hc hdK), ?_⟩
  have heq := congrArg (fun x : Hyperbolic K V ↦ (d : K)⁻¹ • x) hgc
  simpa only [Hyperbolic.Aut.map_smul, smul_smul, inv_mul_cancel₀ hdK, one_smul,
    div_eq_mul_inv, mul_comm, Units.val_mk0] using heq

/-- The completed primitive hyperbolic vector has scalar content one. -/
theorem hyperbolic_e_content (L : Submodule (integerSubring K) V)
    (p : HeightOneSpectrum (integerSubring K)) (a : (LocalField (integerSubring K) p)ˣ) :
    ValuationRayContent.HasContent
      (carrier (integerSubring K) p (Hyperbolic.submodule L))
      ((a : LocalField (integerSubring K) p) •
        inclusion (integerSubring K) p (Hyperbolic.e : Hyperbolic K V)) a := by
  intro b
  change b • ((a : LocalField (integerSubring K) p) • inclusion _ p Hyperbolic.e) ∈
    carrier (integerSubring K) p (Hyperbolic.submodule L) ↔ Valued.v (b * (a : _)) ≤ 1
  rw [← hyperbolicEquiv_carrier]
  simp [map_smul, hyperbolicEquiv_inclusion, Hyperbolic.e, Hyperbolic.Mem,
    Hyperbolic.submodule, smul_smul, smul_eq_mul]
  change ((0 : Space (V := V) (integerSubring K) p) ∈ carrier _ p L ∧
    b * (a : _) ∈ LocalRing (integerSubring K) p ∧
      (0 : LocalField (integerSubring K) p) ∈ LocalRing (integerSubring K) p) ↔ _
  simp only [Submodule.zero_mem, Subring.zero_mem, true_and, and_true]
  change Valued.v (b * a.val) ≤ 1 ↔ Valued.v b * Valued.v a.val ≤ 1
  rw [map_mul]

/-- The same global terminal generator works at every actual finite completion. -/
theorem exists_completed_contents (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (z : Hyperbolic K V)
    (hz : z ≠ 0) (hiso : Hyperbolic.q Q z = 0) :
    ∃ c : Kˣ, ∀ p : HeightOneSpectrum (integerSubring K),
      ValuationRayContent.HasContent
        (carrier (integerSubring K) p L.hyperbolic.carrier)
        (inclusion (integerSubring K) p z)
        (Units.map (algebraMap K (LocalField (integerSubring K) p)).toMonoidHom c) := by
  obtain ⟨g, c, hgc⟩ := exists_terminal L hA hE z hz hiso
  refine ⟨c, fun p ↦ ?_⟩
  apply (ValuationRayContent.equiv_iff (equiv (integerSubring K) p g.toLinearEquiv)
    (equiv_carrier _ p _ _ g.toLinearEquiv g.mem_iff) _ _).mp
  rw [equiv_inclusion]
  change ValuationRayContent.HasContent _ (inclusion _ p (g z)) _
  rw [hgc]
  have heq : inclusion (integerSubring K) p ((c : K) • Hyperbolic.e) =
      algebraMap K (LocalField (integerSubring K) p) (c : K) •
        inclusion (integerSubring K) p (Hyperbolic.e : Hyperbolic K V) := by
    rw [(inclusion (integerSubring K) p).map_smul,
      ← IsScalarTower.algebraMap_smul (R := K) (A := LocalField (integerSubring K) p)]
  rw [heq]
  exact hyperbolic_e_content L.carrier p
    (Units.map (algebraMap K (LocalField (integerSubring K) p)).toMonoidHom c)

end NormEuclidean.IsotropicRayTerminal
