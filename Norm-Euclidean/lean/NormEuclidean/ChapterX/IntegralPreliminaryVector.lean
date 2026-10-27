import NormEuclidean.ChapterX.ScalarIntegralApproximation
import NormEuclidean.ChapterX.FixedValueWeakApproximation

/-!
# The actual integral preliminary vector in O'Meara 104:3, step 2

Completed integrality at the finitely many targets yields a common denominator
which is a unit there. Integral scalar approximation then makes this denominator
arbitrarily close to one while multiplying the vector into the original global
module. This preserves the target value up to the square of that scalar.
-/

noncomputable section

namespace NormEuclidean.IntegralPreliminaryVector

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation Filter Topology
open scoped NormEuclidean.OrthogonalTopology WithZero

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- Local integrality of one vector at the targets gives a denominator which
is a unit at every target. It uses actual completed carriers and no integral basis. -/
theorem exists_unit_denominator (L : Submodule R V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (y : V)
    (T : Finset (HeightOneSpectrum R))
    (hy : ∀ v ∈ T, inclusion R v y ∈ carrier R v L) :
    ∃ d : R, d ≠ 0 ∧ (∀ v ∈ T, d ∉ v.asIdeal) ∧ (d : K) • y ∈ L := by
  let M := L ⊔ Submodule.span R {y}
  have hMfg : M.FG := hfg.sup (Submodule.fg_span_singleton y)
  have heq (v : HeightOneSpectrum R) (hv : v ∈ T) : carrier R v M = carrier R v L := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, hl, z, hz, hsum⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a, hax⟩ := Submodule.mem_span_singleton.mp hz
      rw [← hsum, ← hax, inclusion_add, inclusion_smul]
      exact (carrier R v L).add_mem (inclusion_mem R v L hl)
        ((carrier R v L).smul_mem _ (hy v hv))
    · exact Submodule.span_mono (Set.image_mono (fun _ hx ↦ (show L ≤ M from le_sup_left) hx))
  obtain ⟨d, hd0, hdT, hd⟩ := UnitDenominator.exists_unit_common_lattice_denominator
    R L hfull (fun _ : Unit ↦ M) (fun _ ↦ hMfg) T (fun _ v hv ↦ heq v hv)
  exact ⟨d, hd0, hdT, hd () y ((show Submodule.span R {y} ≤ M from le_sup_right)
    (Submodule.subset_span (Set.mem_singleton y)))⟩

/-- The preliminary vector can be put in the global module by a nonzero
integral scalar arbitrarily close to one at each target. This closes the scalar
denominator step of 104:3, including an empty set of targets. -/
theorem exists_integral_scalar_near_one (L : Submodule R V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (y : V)
    (T : Finset (HeightOneSpectrum R))
    (hy : ∀ v ∈ T, inclusion R v y ∈ carrier R v L)
    (W : (v : T) → Set (LocalField R v.1)) (hW : ∀ v, W v ∈ 𝓝 (1 : LocalField R v.1)) :
    ∃ l : R, l ≠ 0 ∧ (l : K) • y ∈ L ∧
      (∀ v : T, IsUnit (integerMap R v.1 l)) ∧
      ∀ v : T, algebraMap K (LocalField R v.1) (l : K) ∈ W v := by
  classical
  obtain ⟨d, hd0, hdT, hdy⟩ := exists_unit_denominator R L hfg hfull y T hy
  by_cases hT : T.Nonempty
  · let U (v : T) : Set (LocalField R v.1) := {a | Valued.v a = 1}
    have hU (v : T) : U v ∈ 𝓝 (1 : LocalField R v.1) := by
      simpa only [U, map_one] using
        (Valued.locally_const (by simp : Valued.v (1 : LocalField R v.1) ≠ 0))
    obtain ⟨l, ⟨z, hz⟩, hl, _⟩ := exists_integer_congruence_nhds R T d 0 hdT
      (fun _ ↦ 1) (fun v ↦ W v ∩ U v) (fun v ↦ inter_mem (hW v) (hU v))
    have hunit (v : T) : IsUnit (integerMap R v.1 l) := by
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact (hl v).2
    have hl0 : l ≠ 0 := by
      obtain ⟨v, hv⟩ := hT
      intro hzero
      have h := not_mem_of_isUnit_integerMap R v l (hunit ⟨v, hv⟩)
      exact h (hzero ▸ v.asIdeal.zero_mem)
    refine ⟨l, hl0, ?_, hunit, fun v ↦ (hl v).1⟩
    have hleq : l = d * z := by simpa only [sub_zero] using hz
    rw [hleq, Subring.coe_mul, mul_smul, smul_comm]
    exact L.smul_mem z hdy
  · refine ⟨d, hd0, hdy, ?_, ?_⟩ <;> intro v <;> exact (hT ⟨v.1, v.2⟩).elim

section NumberField

variable [NumberField K] [Invertible (2 : K)] [FiniteDimensional K V]

/-- O'Meara 104:3, step 2, with actual finite-completion topologies: a globally
represented nonzero value has a globally integral preliminary vector, with
value multiplied by an integral unit scalar squared. Both scalar and vector
approximation at the targets are proved, not supplied as existence hypotheses. -/
theorem exists_integral_preliminary_vector (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 2 ≤ Module.finrank K V)
    (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (a : K) (ha : a ≠ 0)
    (hrep : ∃ y : V, Q y = a) (T : Finset (HeightOneSpectrum (integerSubring K)))
    (z : (v : T) → Space (V := V) (integerSubring K) v.1)
    (hz : ∀ v, form (integerSubring K) v.1 Q (z v) =
      algebraMap K (LocalField (integerSubring K) v.1) a)
    (hzL : ∀ v, z v ∈ carrier (integerSubring K) v.1 L)
    (W : (v : T) → Set (Space (V := V) (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝 (z v))
    (B : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hB : ∀ v, B v ∈ 𝓝 (1 : LocalField (integerSubring K) v.1)) :
    ∃ (l : integerSubring K) (y : V), l ≠ 0 ∧ y ∈ L ∧ Q y = (l : K) ^ 2 * a ∧
      (∀ v : T, IsUnit (integerMap (integerSubring K) v.1 l)) ∧
      (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) (l : K) ∈ B v) ∧
      ∀ v : T, inclusion (integerSubring K) v.1 y ∈ W v := by
  classical
  choose U hUW hU hzU using fun v : T ↦ mem_nhds_iff.mp (hW v)
  have hcar (v : T) : IsOpen
      (carrier (integerSubring K) v.1 L : Set (Space (V := V) (integerSubring K) v.1)) :=
    OrthogonalTopology.isOpen_of_full _ (OrthogonalTopology.isOpen_localRing _ _)
      _ (carrier_full _ _ _ hfull)
  have hnb (v : T) : U v ∩ carrier (integerSubring K) v.1 L ∈ 𝓝 (z v) :=
    inter_mem ((hU v).mem_nhds (hzU v)) ((hcar v).mem_nhds (hzL v))
  obtain ⟨x, hx, hxT⟩ := FixedValueWeakApproximation.exists_global_fixed_value_weak_approximation
    Q hQ hdim a ha hrep T z hz (fun v ↦ U v ∩ carrier (integerSubring K) v.1 L) hnb
  let C (v : T) : Set (LocalField (integerSubring K) v.1) :=
    (fun t ↦ t • inclusion (integerSubring K) v.1 x) ⁻¹' U v ∩ B v
  have hC (v : T) : C v ∈ 𝓝 (1 : LocalField (integerSubring K) v.1) := by
    apply inter_mem _ (hB v)
    have hc : Continuous (fun t : LocalField (integerSubring K) v.1 ↦
        t • inclusion (integerSubring K) v.1 x) :=
      IsModuleTopology.continuous_of_linearMap
        ((LinearMap.id : LocalField (integerSubring K) v.1 →ₗ[
          LocalField (integerSubring K) v.1] LocalField (integerSubring K) v.1).smulRight
            (inclusion (integerSubring K) v.1 x))
    apply hc.continuousAt.preimage_mem_nhds
    simpa only [one_smul] using (hU v).mem_nhds (hxT v).1
  obtain ⟨l, hl0, hlx, hlunit, hlT⟩ := exists_integral_scalar_near_one (integerSubring K)
    L hfg hfull x T (fun v hv ↦ (hxT ⟨v, hv⟩).2) C hC
  refine ⟨l, (l : K) • x, hl0, hlx, ?_, hlunit, fun v ↦ (hlT v).2, ?_⟩
  · rw [Q.map_smul, hx, smul_eq_mul]
    ring
  · intro v
    apply hUW v
    rw [(inclusion (integerSubring K) v.1).map_smul, ← IsScalarTower.algebraMap_smul
      (R := K) (A := LocalField (integerSubring K) v.1)]
    exact (hlT v).1

end NumberField

end NormEuclidean.IntegralPreliminaryVector
