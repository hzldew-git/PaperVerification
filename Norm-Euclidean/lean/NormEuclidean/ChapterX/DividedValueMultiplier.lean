import NormEuclidean.ChapterX.GenusRepresentationTransfer

/-!
# Dividing represented values by the square multiplier in O'Meara 104:1

The common denominator is retained as an actual scalar `mu`, with multiplier
`mu^2`. Division preserves global ambient representation and integral local
representation where `mu` is a unit. Class finiteness and local integral
universality outside a finite set remain explicit until separately proved.
-/

noncomputable section

namespace NormEuclidean.DividedValueMultiplier

open IsDedekindDomain CompletedIntegralLattice GenusNormalization UnitDenominator Filter

section Values

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]

/-- Dividing an ambient representing vector divides its quadratic value by
the square of the scalar. There is no integral-vector conclusion here. -/
theorem represents_div_square (Q : QuadraticForm F E) (a c : F)
    (h : ∃ x : E, Q x = a) : ∃ y : E, Q y = a / c ^ 2 := by
  obtain ⟨x, hx⟩ := h
  refine ⟨c⁻¹ • x, ?_⟩
  rw [Q.map_smul, hx, smul_eq_mul, div_eq_mul_inv, ← inv_pow]
  ring

/-- A unit of an actual subring has its field reciprocal in that subring. -/
theorem inverse_mem_of_isUnit (S : Subring F) (a : S) (ha : IsUnit a) :
    (a : F)⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := ha
  have haF : (a : F) ≠ 0 := by
    rw [← hu]
    exact (Units.map S.subtype.toMonoidHom u).ne_zero
  have hprod : ((u⁻¹ : Sˣ) : F) * (a : F) = 1 := by
    rw [← hu]
    exact congrArg Subtype.val (Units.inv_mul u)
  have heq : ((u⁻¹ : Sˣ) : F) = (a : F)⁻¹ :=
    calc
      ((u⁻¹ : Sˣ) : F) = ((u⁻¹ : Sˣ) : F) * ((a : F) * (a : F)⁻¹) := by
        rw [mul_inv_cancel₀ haF, mul_one]
      _ = (a : F)⁻¹ := by rw [← mul_assoc, hprod, one_mul]
  exact heq ▸ ((u⁻¹ : Sˣ) : S).property

end Values

section Places

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

set_option maxHeartbeats 800000 in
/-- Avoiding a prime makes the reciprocal integral at its actual completion. -/
theorem local_inverse_mem (v : HeightOneSpectrum R) (c : R) (hc : c ∉ v.asIdeal) :
    (algebraMap K (LocalField R v) (c : K))⁻¹ ∈ LocalRing R v := by
  let a : LocalRing R v :=
    ⟨algebraMap K (LocalField R v) (c : K), algebraMap_mem R v c.property⟩
  have ha : IsUnit a := isUnit_algebraMap_localRing R v hc
  exact inverse_mem_of_isUnit (F := LocalField R v) (LocalRing R v) a ha

variable [Invertible (2 : K)]

/-- A local integral representation can be divided by a scalar which is a
unit at that prime. This uses the actual completed carrier, including dyadic ones. -/
theorem local_represents_div_square (Q : QuadraticForm K V) (L : Submodule R V)
    (v : HeightOneSpectrum R) (a : K) (c : R) (hc : c ∉ v.asIdeal)
    (h : ∃ z ∈ carrier R v L, form R v Q z = algebraMap K (LocalField R v) a) :
    ∃ y ∈ carrier R v L,
      form R v Q y = algebraMap K (LocalField R v) (a / (c : K) ^ 2) := by
  obtain ⟨z, hz, hQz⟩ := h
  let ci : LocalRing R v :=
    ⟨(algebraMap K (LocalField R v) (c : K))⁻¹, local_inverse_mem R v c hc⟩
  refine ⟨ci • z, (carrier R v L).smul_mem ci hz, ?_⟩
  change form R v Q ((ci : LocalField R v) • z) = _
  rw [(form R v Q).map_smul, hQz, map_div₀, map_pow]
  change (algebraMap K (LocalField R v) (c : K))⁻¹ *
      (algebraMap K (LocalField R v) (c : K))⁻¹ * algebraMap K (LocalField R v) a = _
  rw [div_eq_mul_inv, ← inv_pow]
  ring

end Places

section NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- Retain an actual square-root scalar for the genus multiplier. Both the
common scalar and its local unit conditions are derived from finite classes. -/
theorem exists_genus_scaling_factor (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Lattice (integerSubring K) Q)
    (hfinite : Finite (GenusClassSet Q L))
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ c : integerSubring K, c ≠ 0 ∧ (∀ v ∈ T, c ∉ v.asIdeal) ∧
      ∀ M : Lattice (integerSubring K) Q, SameGenus Q L M →
        ∀ b : K, (∃ x ∈ M.carrier, Q x = b) →
          ∃ z ∈ L.carrier, Q z = (c : K) ^ 2 * b := by
  letI := hfinite
  let A : GenusClassSet Q L → Lattice (integerSubring K) Q := fun k ↦ k.out.1
  choose N hN hlocal using fun k : GenusClassSet Q L ↦
    exists_normalized_lattice Q hQ hpos L (A k)
      (LocalIntegralReflection.sameProperGenus_of_sameGenus Q hQ L (A k) k.out.2) T
  obtain ⟨c, hc0, hcv, hc⟩ := exists_unit_common_lattice_denominator (integerSubring K)
    L.carrier L.full (fun k ↦ (N k).carrier) (fun k ↦ (N k).finite) T hlocal
  refine ⟨c, hc0, hcv, ?_⟩
  intro M hM b hrep
  let k : GenusClassSet Q L := Quotient.mk (genusClassSetoid Q L) ⟨M, hM⟩
  have hMA : GloballyIsometric Q M (A k) := by
    have heq : Quotient.mk (genusClassSetoid Q L) (⟨M, hM⟩ : GenusMember Q L) =
        Quotient.mk (genusClassSetoid Q L) k.out := (Quotient.out_eq k).symm
    exact Quotient.exact heq
  obtain ⟨e⟩ := hMA
  obtain ⟨f, _⟩ := hN k
  obtain ⟨x, hx, hQx⟩ := hrep
  let y := (e.compose f).toLinearEquiv x
  have hy : y ∈ (N k).carrier := ((e.compose f).mem_iff x).mpr hx
  refine ⟨(c : K) • y, hc k y hy, ?_⟩
  rw [Q.map_smul, (e.compose f).q_eq, hQx]
  simp only [smul_eq_mul, pow_two]

/-- The divided-value conclusion of 104:1 follows from actual class
finiteness and integral local universality outside the finite set. The two
arithmetic inputs remain explicit; neither is replaced by a conclusion-bearing law. -/
theorem exists_divided_value_multiplier (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Lattice (integerSubring K) Q)
    (hfinite : Finite (GenusClassSet Q L))
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (huniv : ∀ v ∉ T, ∀ b : LocalField (integerSubring K) v,
      b ∈ LocalRing (integerSubring K) v →
        ∃ z ∈ carrier (integerSubring K) v L.carrier, form (integerSubring K) v Q z = b) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ a : K, (∃ b : integerSubring K, a = (γ : K) * (b : K)) →
        (∃ x : V, Q x = a) →
        (∀ v ∈ T, ∃ z ∈ carrier (integerSubring K) v L.carrier,
          form (integerSubring K) v Q z = algebraMap K (LocalField (integerSubring K) v) a) →
        ∃ x ∈ L.carrier, Q x = a := by
  obtain ⟨c, hc0, hcv, hc⟩ := exists_genus_scaling_factor Q hQ hpos L hfinite T
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  refine ⟨c ^ 2, pow_ne_zero _ hc0, ?_, ?_⟩
  · intro v hv
    apply isUnit_algebraMap_localRing (integerSubring K) v
    exact v.asIdeal.primeCompl.pow_mem (hcv v hv) 2
  · intro a ha hglobal hlocal
    obtain ⟨b, hab⟩ := ha
    have hab' : a / (c : K) ^ 2 = (b : K) := by
      rw [hab, Subring.coe_pow]
      exact mul_div_cancel_left₀ (b : K) (pow_ne_zero _ hcK)
    have hglobalb : ∃ x : V, Q x = (b : K) := by
      simpa only [hab'] using represents_div_square Q a (c : K) hglobal
    have hlocalb : ∀ v : HeightOneSpectrum (integerSubring K),
        ∃ z ∈ carrier (integerSubring K) v L.carrier,
          form (integerSubring K) v Q z =
            algebraMap K (LocalField (integerSubring K) v) (b : K) := by
      intro v
      by_cases hv : v ∈ T
      · simpa only [hab'] using local_represents_div_square (integerSubring K) Q L.carrier
          v a c (hcv v hv) (hlocal v hv)
      · exact huniv v hv (algebraMap K (LocalField (integerSubring K) v) (b : K))
          (algebraMap_mem (integerSubring K) v b.property)
    obtain ⟨P, hP, hrep⟩ := GenusPatching.exists_genus_lattice_representing Q hQ L (b : K)
      hglobalb hlocalb
    obtain ⟨x, hx, hQx⟩ := hc P hP (b : K) hrep
    exact ⟨x, hx, hQx.trans (by simpa only [Subring.coe_pow] using hab.symm)⟩

/-- Enlarge the prescribed finite set internally to cover the exceptions to
local integral universality. This has the source conclusion of 104:1, with
actual class finiteness and eventual local universality still explicit. -/
theorem exists_divided_value_multiplier_of_eventual_universality
    (hQ : Q.polarBilin.Nondegenerate) (hpos : 0 < Module.finrank K V)
    (L : Lattice (integerSubring K) Q) (hfinite : Finite (GenusClassSet Q L))
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (huniv : ∀ᶠ v : HeightOneSpectrum (integerSubring K) in cofinite,
      ∀ b : LocalField (integerSubring K) v, b ∈ LocalRing (integerSubring K) v →
        ∃ z ∈ carrier (integerSubring K) v L.carrier, form (integerSubring K) v Q z = b) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ a : K, (∃ b : integerSubring K, a = (γ : K) * (b : K)) →
        (∃ x : V, Q x = a) →
        (∀ v : HeightOneSpectrum (integerSubring K),
          ∃ z ∈ carrier (integerSubring K) v L.carrier,
            form (integerSubring K) v Q z =
              algebraMap K (LocalField (integerSubring K) v) a) →
        ∃ x ∈ L.carrier, Q x = a := by
  classical
  let bad := {v : HeightOneSpectrum (integerSubring K) |
    ¬ ∀ b : LocalField (integerSubring K) v, b ∈ LocalRing (integerSubring K) v →
      ∃ z ∈ carrier (integerSubring K) v L.carrier, form (integerSubring K) v Q z = b}
  have hbad : bad.Finite := by simpa only [eventually_cofinite] using huniv
  let S := T ∪ hbad.toFinset
  have hS : ∀ v ∉ S, ∀ b : LocalField (integerSubring K) v,
      b ∈ LocalRing (integerSubring K) v →
        ∃ z ∈ carrier (integerSubring K) v L.carrier, form (integerSubring K) v Q z = b := by
    intro v hv
    by_contra hnot
    exact hv (Finset.mem_union_right T (hbad.mem_toFinset.mpr hnot))
  obtain ⟨γ, hγ0, hγunit, hγ⟩ := exists_divided_value_multiplier Q hQ hpos L hfinite S hS
  refine ⟨γ, hγ0, fun v hv ↦ hγunit v (Finset.mem_union_left _ hv), ?_⟩
  intro a ha hglobal hlocal
  exact hγ a ha hglobal (fun v _ ↦ hlocal v)

end NumberField

end NormEuclidean.DividedValueMultiplier
