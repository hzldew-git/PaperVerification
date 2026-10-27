import NormEuclidean.ChapterX.GenusFiniteness
import NormEuclidean.LocalRescaling

/-!
# Number-field 104:1 for lattices with fractional quadratic values

An actual common denominator for the half-polar pairing scales the form so
the same source carrier is norm-integral. Applying the proved 104:1 to that
form and cancelling its nonzero scalar gives the literal original value on
every finite full source module. The denominator need not avoid target primes;
the actual multiplier still does. No class-finiteness or value-integrality
premise is supplied.
-/

noncomputable section

namespace NormEuclidean.FractionalValueMultiplier

open CompletedIntegralLattice IsDedekindDomain

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]

omit [Invertible (2 : K)] in
/-- A finite module has a nonzero integral scalar making all actual
quadratic values integral after scaling the form. No fullness is required. -/
theorem exists_integral_form_scalar (Q : QuadraticForm K V)
    (L : Submodule (integerSubring K) V) (hfg : L.FG) :
    ∃ d : integerSubring K, d ≠ 0 ∧ ∀ x ∈ L, ((d : K) • Q) x ∈ integerSubring K := by
  obtain ⟨d, hd, hdual⟩ := exists_lattice_denominator L ((halfPolar Q).dualSubmodule L) hfg
    (IntegralBiduality.dual_full (halfPolar Q) L hfg)
  refine ⟨d, hd, ?_⟩
  intro x hx
  have h := hdual x hx x hx
  rw [LinearMap.BilinForm.smul_left, halfPolar_self] at h
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp h
  change (d : K) * Q x ∈ integerSubring K
  rw [← hr]
  exact r.property

/-- The literal full-integer-ring 104:1 multiplier for every finite full
module, including fractional quadratic values. The original form, carrier
and divisible value are returned without any integrality or finiteness input. -/
theorem exists_divided_value_multiplier (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Submodule (integerSubring K) V)
    (hfg : L.FG) (hfull : Submodule.span K (L : Set V) = ⊤)
    (hdim : 3 ≤ Module.finrank K V) (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ a : K, (∃ b : integerSubring K, a = (γ : K) * (b : K)) →
        (∃ x : V, Q x = a) →
        (∀ v : HeightOneSpectrum (integerSubring K),
          ∃ z ∈ carrier (integerSubring K) v L,
            form (integerSubring K) v Q z =
              algebraMap K (LocalField (integerSubring K) v) a) →
        ∃ x ∈ L, Q x = a := by
  obtain ⟨d, hd, hdint⟩ := exists_integral_form_scalar Q L hfg
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  let M : Lattice (integerSubring K) ((d : K) • Q) :=
    { carrier := L, finite := hfg, full := hfull, integral := hdint }
  obtain ⟨γ, hγ, hγT, hrep⟩ := GenusFiniteness.exists_integral_divided_value_multiplier
    ((d : K) • Q) (GenusVolumeFiniteness.polarBilin_smul_nondegenerate Q hQ d hdK) M hdim T
  refine ⟨γ, hγ, hγT, ?_⟩
  intro a hdiv hglobal hlocal
  have hdiv' : ∃ b : integerSubring K, (d : K) * a = (γ : K) * (b : K) := by
    obtain ⟨b, hb⟩ := hdiv
    refine ⟨d * b, ?_⟩
    rw [hb, Subring.coe_mul]
    ring
  have hglobal' : ∃ x : V, ((d : K) • Q) x = (d : K) * a := by
    obtain ⟨x, hx⟩ := hglobal
    exact ⟨x, by change (d : K) * Q x = _; rw [hx]⟩
  have hlocal' : ∀ v : HeightOneSpectrum (integerSubring K),
      ∃ z ∈ carrier (integerSubring K) v M.carrier,
        form (integerSubring K) v ((d : K) • Q) z =
          algebraMap K (LocalField (integerSubring K) v) ((d : K) * a) := by
    intro v
    obtain ⟨z, hz, hQz⟩ := hlocal v
    refine ⟨z, hz, ?_⟩
    rw [form_rescale, QuadraticMap.smul_apply, smul_eq_mul, hQz, map_mul]
  obtain ⟨x, hx, hQx⟩ := hrep _ hdiv' hglobal' hlocal'
  exact ⟨x, hx, mul_left_cancel₀ hdK hQx⟩

end NormEuclidean.FractionalValueMultiplier
