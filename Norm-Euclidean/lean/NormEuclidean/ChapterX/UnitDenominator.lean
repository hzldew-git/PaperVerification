import NormEuclidean.AdelicOrthogonal
import NormEuclidean.CompletionDescent
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Operations

/-!
# Common denominators which are units at prescribed places

This is the denominator input used in O'Meara 104:1, from 21:2(a).
For a finite family of finite modules whose actual completions agree with
a full target at prescribed places, one nonzero integral scalar carries
the entire family into the target and avoids every prescribed prime.
The finite normalized genus representatives themselves are not supplied here.
-/

noncomputable section

namespace NormEuclidean.UnitDenominator

open IsDedekindDomain CompletedIntegralLattice

section Modules

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite collection of denominators in a multiplicative set has one
common denominator in that same set. -/
theorem exists_common_denominator_in (S : Submonoid R) (L : Submodule R M) (t : Finset M)
    (h : ∀ x ∈ t, ∃ a : S, (a : R) • x ∈ L) :
    ∃ a : S, ∀ x ∈ t, (a : R) • x ∈ L := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | @insert x t hx ih =>
    obtain ⟨a, ha⟩ := h x (Finset.mem_insert_self x t)
    obtain ⟨b, hb⟩ := ih (fun y hy ↦ h y (Finset.mem_insert_of_mem hy))
    refine ⟨a * b, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa only [Submonoid.coe_mul, mul_comm (a : R) (b : R), mul_smul]
        using L.smul_mem (b : R) ha
    · simpa only [Submonoid.coe_mul, mul_smul] using L.smul_mem (a : R) (hb y hy)

end Modules

section Places

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

omit [IsDedekindDomain R] [IsFractionRing R K] in
/-- Prime avoidance gives a nonzero element of an ideal avoiding every
prescribed finite prime. The zero ideal is included in the avoided family. -/
theorem exists_nonzero_avoiding_primes (I : Ideal R) (hI0 : I ≠ ⊥)
    (T : Finset (HeightOneSpectrum R)) (hI : ∀ v ∈ T, ¬ I ≤ v.asIdeal) :
    ∃ a ∈ I, a ≠ 0 ∧ ∀ v ∈ T, a ∉ v.asIdeal := by
  classical
  let s : Finset (Option (HeightOneSpectrum R)) := insert none (T.image some)
  let f : Option (HeightOneSpectrum R) → Ideal R
    | none => ⊥
    | some v => v.asIdeal
  have hp : ∀ i ∈ s, i ≠ none → i ≠ none → (f i).IsPrime := by
    intro i _ hi _
    cases i with
    | none => exact (hi rfl).elim
    | some v => exact v.isPrime
  have hnot : ¬ (I : Set R) ⊆ ⋃ i ∈ (s : Set (Option (HeightOneSpectrum R))), f i := by
    intro h
    obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime none none hp).mp h
    cases i with
    | none => exact hI0 (le_bot_iff.mp hle)
    | some v =>
        have hv : v ∈ T := by simpa only [s, Finset.mem_coe, Finset.mem_insert,
          Option.some_ne_none, false_or, Finset.mem_image, Option.some_inj,
          exists_eq_right] using hi
        exact hI v hv hle
  obtain ⟨a, haI, ha⟩ := Set.not_subset.mp hnot
  refine ⟨a, haI, ?_, ?_⟩
  · intro hzero
    apply ha
    exact Set.mem_iUnion.mpr ⟨none, Set.mem_iUnion.mpr
      ⟨by simp [s], by simp [f, hzero]⟩⟩
  · intro v hv hav
    apply ha
    exact Set.mem_iUnion.mpr ⟨some v, Set.mem_iUnion.mpr
      ⟨by simp [s, hv], hav⟩⟩

/-- Localization containment at one place permits a denominator outside
that prime for the entire finitely generated source module. -/
theorem exists_denominator_away_of_localized_le (v : HeightOneSpectrum R)
    (L M : Submodule R V) (hM : M.FG)
    (hlocal : M.localized' (v.valuation K).valuationSubring v.asIdeal.primeCompl LinearMap.id ≤
      L.localized' (v.valuation K).valuationSubring v.asIdeal.primeCompl LinearMap.id) :
    ∃ a : R, a ∉ v.asIdeal ∧ ∀ x ∈ M, a • x ∈ L := by
  classical
  obtain ⟨t, ht⟩ := hM
  have hex : ∀ x ∈ t, ∃ a : v.asIdeal.primeCompl, (a : R) • x ∈ L := by
    intro x hx
    have hxM : x ∈ M := by rw [← ht]; exact Submodule.subset_span hx
    have hxlocal : x ∈ L.localized' (v.valuation K).valuationSubring
        v.asIdeal.primeCompl LinearMap.id := hlocal ⟨x, hxM, 1, by simp⟩
    obtain ⟨y, hy, a, hax⟩ := hxlocal
    have hyx : y = (a : R) • x := by
      simpa only [LinearMap.id_apply, Submonoid.smul_def]
        using IsLocalizedModule.mk'_eq_iff.mp hax
    exact ⟨a, hyx ▸ hy⟩
  obtain ⟨a, ha⟩ := exists_common_denominator_in v.asIdeal.primeCompl L t hex
  refine ⟨a, a.2, ?_⟩
  intro x hx
  rw [← ht] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact ha x hx
  | zero => simpa only [smul_zero] using L.zero_mem
  | add x y _ _ hx hy => simpa only [smul_add] using L.add_mem hx hy
  | smul b x _ hx => simpa only [smul_comm (a : R) b x] using L.smul_mem b hx

/-- O'Meara 21:2(a), in the actual finite-completion language needed by
104:1. Both the common denominator and its local unit conditions are derived. -/
theorem exists_unit_common_lattice_denominator {ι : Type*} [Finite ι]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤)
    (M : ι → Submodule R V) (hM : ∀ i, (M i).FG)
    (T : Finset (HeightOneSpectrum R))
    (hlocal : ∀ i v, v ∈ T → carrier R v (M i) = carrier R v L) :
    ∃ a : R, a ≠ 0 ∧ (∀ v ∈ T, a ∉ v.asIdeal) ∧
      ∀ i, ∀ x ∈ M i, (a : K) • x ∈ L := by
  let N := ⨆ i, M i
  have hN : N.FG := Submodule.fg_iSup M hM
  let I := L.colon (N : Set V)
  obtain ⟨b, hb0, hb⟩ := exists_lattice_denominator N L hN hL
  have hbI : b ∈ I := Submodule.mem_colon.mpr hb
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hbI
    exact hb0 hbI
  have havoid : ∀ v ∈ T, ¬ I ≤ v.asIdeal := by
    intro v hv hle
    have hl : N.localized' (v.valuation K).valuationSubring v.asIdeal.primeCompl LinearMap.id ≤
        L.localized' (v.valuation K).valuationSubring v.asIdeal.primeCompl LinearMap.id := by
      rw [Submodule.localized'_iSup]
      exact iSup_le fun i ↦
        (CompletionDescent.localized_eq_of_completed_carrier_eq R v (hlocal i v hv)).le
    obtain ⟨a, ha, hax⟩ := exists_denominator_away_of_localized_le R v L N hN hl
    exact ha (hle (Submodule.mem_colon.mpr hax))
  obtain ⟨a, haI, ha0, hav⟩ := exists_nonzero_avoiding_primes R I hI0 T havoid
  refine ⟨a, ha0, hav, ?_⟩
  intro i x hx
  exact Submodule.mem_colon.mp haI x ((le_iSup M i) hx)

/-- The square multiplier used by 104:1 transfers every represented value
of the finite normalized family to a represented value of the target.
Its nonvanishing and its units at the prescribed actual completions are proved. -/
theorem exists_unit_square_multiplier {ι : Type*} [Finite ι]
    (Q : QuadraticForm K V) (L : Lattice R Q) (M : ι → Lattice R Q)
    (T : Finset (HeightOneSpectrum R))
    (hlocal : ∀ i v, v ∈ T → carrier R v (M i).carrier = carrier R v L.carrier) :
    ∃ γ : R, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField R v) (γ : K),
        algebraMap_mem R v γ.property⟩ : LocalRing R v)) ∧
      ∀ i b, (∃ x ∈ (M i).carrier, Q x = b) →
        ∃ z ∈ L.carrier, Q z = (γ : K) * b := by
  obtain ⟨μ, hμ0, hμv, hμ⟩ := exists_unit_common_lattice_denominator R L.carrier L.full
    (fun i ↦ (M i).carrier) (fun i ↦ (M i).finite) T hlocal
  refine ⟨μ ^ 2, pow_ne_zero _ hμ0, ?_, ?_⟩
  · intro v hv
    apply isUnit_algebraMap_localRing R v
    change μ ^ 2 ∈ v.asIdeal.primeCompl
    exact v.asIdeal.primeCompl.pow_mem (hμv v hv) 2
  · intro i b hb
    obtain ⟨x, hx, hQx⟩ := hb
    refine ⟨(μ : K) • x, hμ i x hx, ?_⟩
    rw [Q.map_smul, hQx]
    simp only [smul_eq_mul, Subring.coe_mul, pow_two]

end Places

end NormEuclidean.UnitDenominator
