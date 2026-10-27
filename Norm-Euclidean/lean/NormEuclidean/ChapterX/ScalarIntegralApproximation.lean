import NormEuclidean.ChapterX.FiniteWeakApproximation
import NormEuclidean.ChapterX.UnitDenominator
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Integral scalar approximation at actual finite places

Chinese remainders give simultaneous approximation of local integral scalars
by one global integer. Its integrality at every other finite place is automatic.
This is the finite integral part of O'Meara 33:11, not its archimedean or
excluded-place growth assertion.
-/

noncomputable section

namespace NormEuclidean.ScalarIntegralApproximation

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CompletedIntegralLattice
  Filter Topology WithZeroMulInt WithZero
open scoped WithZero WithZeroTopology

variable {K : Type*} [Field K]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

theorem valuation_algebraMap (v : HeightOneSpectrum R) (a : K) :
    Valued.v (algebraMap K (LocalField R v) a) = v.valuation K a := by
  change Valued.v (a : v.adicCompletion K) = _
  exact valuedAdicCompletion_eq_valuation' v a

/-- Valuation balls around any actual completed scalar are neighborhoods. -/
theorem valuation_ball_mem_nhds (v : HeightOneSpectrum R) (x : LocalField R v)
    (γ : (ℤᵐ⁰)ˣ) :
    {y : LocalField R v | Valued.v (y - x) < γ} ∈ 𝓝 x := by
  have hc : Continuous (Valued.v : LocalField R v → ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v)
  apply (isOpen_Iio.preimage (hc.comp (continuous_id.sub continuous_const))).mem_nhds
  change Valued.v (x - x) < (γ : ℤᵐ⁰)
  simp only [sub_self, map_zero]
  exact Units.zero_lt γ

/-- An actual local integer has a global integral approximation to any
nonzero valuation precision. No density of the integer ring is assumed. -/
theorem exists_integer_valuation_close (v : HeightOneSpectrum R) (x : LocalRing R v)
    (γ : (ℤᵐ⁰)ˣ) :
    ∃ a : R, Valued.v (algebraMap K (LocalField R v) (a : K) - x) < γ := by
  have hx : (LocalRing R v : Set (LocalField R v)) ∈ 𝓝 (x : LocalField R v) :=
    (OrthogonalTopology.isOpen_localRing R v).mem_nhds x.property
  obtain ⟨b, hb, hbint⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := K) v).mem_nhds
    (inter_mem (valuation_ball_mem_nhds R v x γ) hx)
  have hbval : v.valuation K b ≤ 1 := by
    change Valued.v (algebraMap K (LocalField R v) b) ≤ 1 at hbint
    rwa [valuation_algebraMap] at hbint
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hbval γ
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap K (LocalField R v) (a : K) -
      algebraMap K (LocalField R v) b) < γ := by
    rw [← map_sub, valuation_algebraMap]
    exact ha
  have hsum := Valued.v.map_add
    (algebraMap K (LocalField R v) (a : K) - algebraMap K (LocalField R v) b)
    (algebraMap K (LocalField R v) b - x)
  rw [sub_add_sub_cancel] at hsum
  exact hsum.trans_lt (max_lt ha' hb)

/-- Chinese remainders supply an integral scalar with arbitrary independent
valuation precisions at a finite set of actual local integer targets. -/
theorem exists_simultaneous_integer (T : Finset (HeightOneSpectrum R))
    (x : (v : T) → LocalRing R v.1) (γ : T → (ℤᵐ⁰)ˣ) :
    ∃ a : R, ∀ v : T,
      Valued.v (algebraMap K (LocalField R v.1) (a : K) - x v) < γ v := by
  classical
  choose b hb using fun v : T ↦ exists_integer_valuation_close R v.1 (x v) (γ v)
  choose n hn using fun v : T ↦ exists_exp_neg_natCast_lt (Units.ne_zero (γ v))
  let e : HeightOneSpectrum R → ℕ := fun v ↦ if h : v ∈ T then n ⟨v, h⟩ else 0
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (fun v : HeightOneSpectrum R ↦ v.asIdeal) e
    (fun v _ ↦ v.irreducible.prime)
    (fun v _ w _ hvw ↦ HeightOneSpectrum.ext_iff.not.mp hvw) b
  refine ⟨a, ?_⟩
  intro v
  have hmem := ha v.1 v.2
  have hv : v.1.intValuation (a - b v) ≤ exp (-(n v : ℤ)) := by
    apply (v.1.intValuation_le_pow_iff_mem (a - b v) (n v)).mpr
    simpa only [e, dif_pos v.2] using hmem
  have hab : Valued.v (algebraMap K (LocalField R v.1) (a : K) -
      algebraMap K (LocalField R v.1) (b v : K)) < γ v := by
    rw [← map_sub, valuation_algebraMap]
    change v.1.valuation K (algebraMap R K (a - b v)) < (γ v : ℤᵐ⁰)
    rw [valuation_of_algebraMap]
    exact hv.trans_lt (hn v)
  have hsum := Valued.v.map_add
    (algebraMap K (LocalField R v.1) (a : K) -
      algebraMap K (LocalField R v.1) (b v : K))
    (algebraMap K (LocalField R v.1) (b v : K) - x v)
  rw [sub_add_sub_cancel] at hsum
  exact hsum.trans_lt (max_lt hab (hb v))

/-- Integral scalar approximation stated with the actual completion topology.
The targets are local integers; no control at infinite places is asserted. -/
theorem exists_simultaneous_integer_nhds (T : Finset (HeightOneSpectrum R))
    (x : (v : T) → LocalRing R v.1) (W : (v : T) → Set (LocalField R v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v : LocalField R v.1)) :
    ∃ a : R, (∀ v : T, algebraMap K (LocalField R v.1) (a : K) ∈ W v) ∧
      ∀ v : HeightOneSpectrum R,
        algebraMap K (LocalField R v) (a : K) ∈ LocalRing R v := by
  classical
  choose δ hδ using fun v : T ↦ Valued.mem_nhds.mp (hW v)
  let γ : T → (ℤᵐ⁰)ˣ := fun v ↦
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass (Valued.v : Valuation (LocalField R v.1) ℤᵐ⁰)))) (δ v)
  obtain ⟨a, ha⟩ := exists_simultaneous_integer R T x γ
  refine ⟨a, ?_, fun v ↦ algebraMap_mem R v a.property⟩
  intro v
  apply hδ v
  exact (Valuation.restrict_lt_iff_lt_embedding
    (Valued.v : Valuation (LocalField R v.1) ℤᵐ⁰)).mpr (ha v)

/-- The global integer ring maps into the actual completed integer ring. -/
def integerMap (v : HeightOneSpectrum R) : R →+* LocalRing R v :=
  ((algebraMap K (LocalField R v)).comp R.subtype).codRestrict (LocalRing R v)
    (fun a ↦ algebraMap_mem R v a.property)

@[simp] theorem integerMap_coe (v : HeightOneSpectrum R) (a : R) :
    (integerMap R v a : LocalField R v) = algebraMap K (LocalField R v) (a : K) := rfl

/-- Local unit membership detects avoidance of the corresponding prime. -/
theorem not_mem_of_isUnit_integerMap (v : HeightOneSpectrum R) (a : R)
    (ha : IsUnit (integerMap R v a)) : a ∉ v.asIdeal := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at ha
  change Valued.v (algebraMap K (LocalField R v) (a : K)) = 1 at ha
  rw [valuation_algebraMap] at ha
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mp ha

/-- An arithmetic progression of nonzero modulus avoiding the target primes
can approximate every local integral target. The congruence and integrality
at all finite places are conclusions, not supplied approximation laws. -/
theorem exists_integer_congruence_nhds (T : Finset (HeightOneSpectrum R))
    (m b : R) (hm : ∀ v ∈ T, m ∉ v.asIdeal)
    (x : (v : T) → LocalRing R v.1) (W : (v : T) → Set (LocalField R v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v : LocalField R v.1)) :
    ∃ a : R, (∃ z : R, a - b = m * z) ∧
      (∀ v : T, algebraMap K (LocalField R v.1) (a : K) ∈ W v) ∧
      ∀ v : HeightOneSpectrum R,
        algebraMap K (LocalField R v) (a : K) ∈ LocalRing R v := by
  classical
  have hu (v : T) : IsUnit (integerMap R v.1 m) :=
    isUnit_algebraMap_localRing R v.1 (hm v.1 v.2)
  let u : (v : T) → (LocalRing R v.1)ˣ := fun v ↦ (hu v).unit
  let y : (v : T) → LocalRing R v.1 := fun v ↦
    (↑((u v)⁻¹) : LocalRing R v.1) * (x v - integerMap R v.1 b)
  have hxy (v : T) : integerMap R v.1 m * y v + integerMap R v.1 b = x v := by
    rw [← (hu v).unit_spec]
    change (u v : LocalRing R v.1) *
      ((↑((u v)⁻¹) : LocalRing R v.1) * (x v - integerMap R v.1 b)) +
        integerMap R v.1 b = x v
    rw [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]
  let f (v : T) (z : LocalField R v.1) :=
    algebraMap K (LocalField R v.1) (m : K) * z +
      algebraMap K (LocalField R v.1) (b : K)
  have hfy (v : T) : f v (y v) = x v := by
    exact congrArg (fun z : LocalRing R v.1 ↦ (z : LocalField R v.1)) (hxy v)
  have hw (v : T) : f v ⁻¹' W v ∈ 𝓝 (y v : LocalField R v.1) := by
    have hc : Continuous (f v) :=
      (continuous_const.mul continuous_id).add continuous_const
    apply hc.continuousAt.preimage_mem_nhds
    simpa only [hfy] using hW v
  obtain ⟨z, hz, _⟩ := exists_simultaneous_integer_nhds R T y
    (fun v ↦ f v ⁻¹' W v) hw
  refine ⟨m * z + b, ⟨z, by ring⟩, ?_, fun v ↦ algebraMap_mem R v (m * z + b).property⟩
  intro v
  have hv := hz v
  change f v (algebraMap K (LocalField R v.1) (z : K)) ∈ W v at hv
  change algebraMap K (LocalField R v.1) ((m : K) * (z : K) + (b : K)) ∈ W v
  simpa only [f, map_add, map_mul] using hv

end NormEuclidean.ScalarIntegralApproximation
