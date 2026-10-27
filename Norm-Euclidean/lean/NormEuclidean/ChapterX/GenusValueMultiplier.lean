import NormEuclidean.ChapterX.GenusNormalization
import NormEuclidean.ChapterX.UnitDenominator
import NormEuclidean.ChapterX.ProperClassFiniteness
import NormEuclidean.LocalIntegrality

/-!
# The finite-representative transfer in O'Meara 104:1

Finite actual genus classes, proved proper normalization, and the proved unit
denominator construct a common multiplier for all values represented by the
genus. The hyperbolic specialization derives local proper comparisons.
Finiteness from 103:4 and the representation/patching step 102:5 remain separate.
-/

noncomputable section

namespace NormEuclidean.GenusValueMultiplier

open GenusNormalization UnitDenominator ProperClassFiniteness CompletedIntegralLattice
open IsDedekindDomain

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

omit [NumberField K] [Invertible (2 : K)] [FiniteDimensional K V] in
/-- The standard integral hyperbolic enlargement represents every value
represented by any norm-integral lattice on the same enlarged space. -/
theorem hyperbolic_represents_value_of_integral_lattice {R : Subring K}
    (L : Lattice R Q) (M : Lattice R (Hyperbolic.form Q)) (b : K)
    (hrep : ∃ x ∈ M.carrier, Hyperbolic.form Q x = b) :
    ∃ z ∈ L.hyperbolic.carrier, Hyperbolic.form Q z = b := by
  obtain ⟨x, hx, hQx⟩ := hrep
  have hb : b ∈ R := hQx ▸ M.integral x hx
  refine ⟨(0, 1, b), ?_, ?_⟩
  · exact ⟨L.carrier.zero_mem, R.one_mem, hb⟩
  · simp [Hyperbolic.form_apply, Hyperbolic.q]

omit [Invertible (2 : K)] [FiniteDimensional K V] in
/-- The hyperbolic represented-value multiplier can be chosen as one,
without regularity, local comparison, or class-finiteness premises. This
does not approximate specified vectors or prove strong approximation. -/
theorem hyperbolic_exists_genus_value_multiplier_unconditional
    (L : Lattice (integerSubring K) Q) (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ = 1 ∧ γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ M : Lattice (integerSubring K) (Hyperbolic.form Q), ∀ b : K,
        (∃ x ∈ M.carrier, Hyperbolic.form Q x = b) →
          ∃ z ∈ L.hyperbolic.carrier, Hyperbolic.form Q z = (γ : K) * b := by
  refine ⟨1, rfl, one_ne_zero, ?_, ?_⟩
  · intro v _
    have heq : (⟨algebraMap K (LocalField (integerSubring K) v)
        ((1 : integerSubring K) : K), algebraMap_mem (integerSubring K) v
        (1 : integerSubring K).property⟩ : LocalRing (integerSubring K) v) = 1 := by
      apply Subtype.ext
      simp
    rw [heq]
    exact isUnit_one
  · intro M b hrep
    simpa only [Subring.coe_one, one_mul] using
      hyperbolic_represents_value_of_integral_lattice Q L M b hrep

omit [FiniteDimensional K V] in
/-- For the standard hyperbolic enlargement, actual integral local
representation at every finite place gives an actual global integral vector.
Regularity, global representability, and class finiteness are not premises. -/
theorem hyperbolic_represents_of_all_finite (L : Lattice (integerSubring K) Q) (a : K)
    (hlocal : ∀ v : HeightOneSpectrum (integerSubring K),
      ∃ z ∈ carrier (integerSubring K) v L.hyperbolic.carrier,
        form (integerSubring K) v (Hyperbolic.form Q) z =
          algebraMap K (LocalField (integerSubring K) v) a) :
    ∃ z ∈ L.hyperbolic.carrier, Hyperbolic.form Q z = a := by
  have ha : a ∈ integerSubring K := by
    apply mem_of_forall_finite_integral (integerSubring K)
    intro v
    obtain ⟨z, hz, hQz⟩ := hlocal v
    exact hQz ▸ carrier_integral (integerSubring K) v (Hyperbolic.form Q)
      L.hyperbolic.carrier L.hyperbolic.integral z hz
  refine ⟨(0, 1, a), ⟨L.carrier.zero_mem, (integerSubring K).one_mem, ha⟩, ?_⟩
  simp [Hyperbolic.form_apply, Hyperbolic.q]

omit [FiniteDimensional K V] in
/-- Exact integral local-global representation for the standard hyperbolic
enlargement, including its actual dyadic completed carriers. This contains
no approximation to prescribed vectors. -/
theorem hyperbolic_represents_iff_all_finite (L : Lattice (integerSubring K) Q) (a : K) :
    (∃ z ∈ L.hyperbolic.carrier, Hyperbolic.form Q z = a) ↔
      ∀ v : HeightOneSpectrum (integerSubring K),
        ∃ z ∈ carrier (integerSubring K) v L.hyperbolic.carrier,
          form (integerSubring K) v (Hyperbolic.form Q) z =
            algebraMap K (LocalField (integerSubring K) v) a := by
  constructor
  · rintro ⟨z, hz, hQz⟩ v
    refine ⟨inclusion (integerSubring K) v z,
      inclusion_mem (integerSubring K) v L.hyperbolic.carrier hz, ?_⟩
    rw [form_inclusion, hQz]
  · exact hyperbolic_represents_of_all_finite Q L a

/-- Construct the finite normalized family and transfer every represented
genus value, rather than assuming a normalized-family witness. The finite
class premise and local proper comparison condition remain explicit. -/
theorem exists_genus_value_multiplier (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Lattice (integerSubring K) Q)
    (hfinite : Finite (GenusClassSet Q L))
    (hproper : ∀ M : Lattice (integerSubring K) Q,
      SameGenus Q L M → SameProperGenus Q L M)
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ (M : Lattice (integerSubring K) Q), SameGenus Q L M →
        ∀ b : K, (∃ x ∈ M.carrier, Q x = b) → ∃ z ∈ L.carrier, Q z = (γ : K) * b := by
  letI := hfinite
  let R : GenusClassSet Q L → Lattice (integerSubring K) Q := fun c ↦ c.out.1
  choose N hN hlocal using fun c : GenusClassSet Q L ↦
    exists_normalized_lattice Q hQ hpos L (R c) (hproper (R c) c.out.2) T
  obtain ⟨γ, hγ0, hγunit, hγ⟩ :=
    exists_unit_square_multiplier (integerSubring K) Q L N T hlocal
  refine ⟨γ, hγ0, hγunit, ?_⟩
  intro M hM b hrep
  let c : GenusClassSet Q L := Quotient.mk (genusClassSetoid Q L) ⟨M, hM⟩
  have hMR : GloballyIsometric Q M (R c) := by
    have h : Quotient.mk (genusClassSetoid Q L) (⟨M, hM⟩ : GenusMember Q L) =
        Quotient.mk (genusClassSetoid Q L) c.out := (Quotient.out_eq c).symm
    exact Quotient.exact h
  obtain ⟨e⟩ := hMR
  obtain ⟨f, _⟩ := hN c
  obtain ⟨x, hx, hQx⟩ := hrep
  let ef := e.compose f
  apply hγ c b
  exact ⟨ef.toLinearEquiv x, (ef.mem_iff x).2 hx, (ef.q_eq x).trans hQx⟩

/-- Proper class finiteness suffices for the same actual represented-value
transfer, through the already proved forgetful quotient. -/
theorem exists_genus_value_multiplier_of_finite_proper_classes
    (hQ : Q.polarBilin.Nondegenerate) (hpos : 0 < Module.finrank K V)
    (L : Lattice (integerSubring K) Q) (hfinite : Finite (ProperGenusClassSet Q L))
    (hproper : ∀ M : Lattice (integerSubring K) Q,
      SameGenus Q L M → SameProperGenus Q L M)
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ (M : Lattice (integerSubring K) Q), SameGenus Q L M →
        ∀ b : K, (∃ x ∈ M.carrier, Q x = b) → ∃ z ∈ L.carrier, Q z = (γ : K) * b :=
  exists_genus_value_multiplier Q hQ hpos L
    ((finite_proper_classes_iff_finite_classes Q hQ L).mp hfinite) hproper T

omit [FiniteDimensional K V] in
/-- For the hyperbolic base, local proper comparisons and positive dimension
are derived. Only actual genus finiteness remains as the external input. -/
theorem hyperbolic_exists_genus_value_multiplier (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q)
    (hfinite : Finite (GenusClassSet (Hyperbolic.form Q) L.hyperbolic))
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ M : Lattice (integerSubring K) (Hyperbolic.form Q),
        SameGenus (Hyperbolic.form Q) L.hyperbolic M → ∀ b : K,
          (∃ x ∈ M.carrier, Hyperbolic.form Q x = b) →
            ∃ z ∈ L.hyperbolic.carrier, Hyperbolic.form Q z = (γ : K) * b := by
  letI := L.finiteDimensional
  have hr : Module.finrank K (Hyperbolic K V) = Module.finrank K V + 2 := by
    simp [Hyperbolic, Module.finrank_prod]
  have hpos : 0 < Module.finrank K (Hyperbolic K V) := by rw [hr]; omega
  exact exists_genus_value_multiplier (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ) hpos L.hyperbolic hfinite
    (fun M hM ↦ (hyperbolic_sameGenus_iff_sameProperGenus Q hQ L M).mp hM) T

end NormEuclidean.GenusValueMultiplier
