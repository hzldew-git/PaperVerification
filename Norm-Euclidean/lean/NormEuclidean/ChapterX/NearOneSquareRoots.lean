import NormEuclidean.ChapterX.LocalUnitSquares

/-!
# Square roots with actual neighborhood control

The derivative-one Hensel root of X^2+X-delta is in the maximal ideal.
Its valuation equals that of delta, since one plus the root is a unit.
Thus squares near one have a unit square root in any prescribed neighborhood
of one, including at dyadic finite places.
-/

noncomputable section

namespace NormEuclidean.NearOneSquareRoots

open Polynomial IsDedekindDomain CompletedIntegralLattice Filter Topology
open scoped WithZero

/-- The auxiliary root is lifted in the maximal ideal, rather than choosing
an uncontrolled square root after passing to the fraction field. -/
theorem exists_auxiliary_root {S : Type*} [CommRing S] [IsLocalRing S]
    [HenselianRing S (IsLocalRing.maximalIdeal S)] (δ : S)
    (hδ : δ ∈ IsLocalRing.maximalIdeal S) :
    ∃ z : S, z ^ 2 + z = δ ∧ z ∈ IsLocalRing.maximalIdeal S := by
  let f : S[X] := X ^ 2 + X - C δ
  have hf : f.Monic := by
    dsimp only [f]
    rw [add_sub_assoc]
    exact monic_X_pow_add (by rw [degree_X_sub_C]; norm_num)
  have hf0 : f.eval 0 ∈ IsLocalRing.maximalIdeal S := by
    simpa [f] using (IsLocalRing.maximalIdeal S).neg_mem hδ
  have hf' : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (f.derivative.eval 0)) := by
    have hder : f.derivative.eval 0 = (1 : S) := by simp [f]
    rw [hder, map_one]
    exact isUnit_one
  obtain ⟨z, hz, hzI⟩ := HenselianRing.is_henselian f hf 0 hf0 hf'
  refine ⟨z, ?_, by simpa only [sub_zero] using hzI⟩
  exact sub_eq_zero.mp (by simpa [f, Polynomial.IsRoot] using hz)

variable {K : Type*} [Field K] [NumberField K]

set_option backward.isDefEq.respectTransparency false in
/-- Unit square roots can be selected in an arbitrary actual neighborhood
of one. No inverse of two in the completed integer ring is assumed. -/
theorem exists_square_roots_in_neighborhood
    (v : HeightOneSpectrum (integerSubring K))
    (C : Set (LocalField (integerSubring K) v)) (hC : C ∈ 𝓝 1) :
    ∃ B : Set (LocalField (integerSubring K) v), B ∈ 𝓝 1 ∧
      ∀ t ∈ B, ∃ u : (LocalRing (integerSubring K) v)ˣ,
        ((u : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ^ 2 = t ∧
        ((u : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ∈ C := by
  let F := LocalField (integerSubring K) v
  let S := LocalRing (integerSubring K) v
  letI := CompletionHensel.henselian_completed_integers v
  have hpre : (fun z : F ↦ 1 + 2 * z) ⁻¹' C ∈ 𝓝 (0 : F) := by
    have hcont : Continuous (fun z : F ↦ 1 + 2 * z) := by fun_prop
    apply hcont.continuousAt.preimage_mem_nhds
    change C ∈ 𝓝 (1 + 2 * (0 : F))
    simpa only [mul_zero, add_zero] using hC
  obtain ⟨γ₀, hγ₀⟩ := Valued.mem_nhds_zero.mp hpre
  let γ : (ℤᵐ⁰)ˣ := Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
    (f := (.ofClass (Valued.v : Valuation F ℤᵐ⁰)))) γ₀
  have hγ (z : F) (hz : Valued.v z < γ) : 1 + 2 * z ∈ C :=
    hγ₀ ((Valuation.restrict_lt_iff_lt_embedding
      (Valued.v : Valuation F ℤᵐ⁰)).mpr hz)
  let η := min γ 1
  let B : Set F := {t | Valued.v ((t - 1) / 4) < η}
  have hB : B ∈ 𝓝 (1 : F) := by
    have hball := ScalarIntegralApproximation.valuation_ball_mem_nhds
      (integerSubring K) v (0 : F) η
    have hcont : Continuous (fun t : F ↦ (t - 1) / 4) :=
      (continuous_id.sub continuous_const).div_const 4
    change (fun t : F ↦ (t - 1) / 4) ⁻¹' {z : F | Valued.v z < η} ∈ 𝓝 1
    apply hcont.continuousAt.preimage_mem_nhds
    change {z : F | Valued.v z < η} ∈ 𝓝 ((1 - 1) / (4 : F))
    simpa only [sub_self, sub_zero, zero_div] using hball
  refine ⟨B, hB, ?_⟩
  intro t ht
  have hδlt : Valued.v ((t - 1) / 4) < (1 : ℤᵐ⁰) :=
    ht.trans_le (by exact_mod_cast min_le_right γ 1)
  let δ : S := ⟨(t - 1) / 4, hδlt.le⟩
  have hδI : δ ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have heq := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu
    exact hδlt.ne heq
  obtain ⟨z, hz, hzI⟩ := exists_auxiliary_root δ hδI
  have hzlt : Valued.v (z : F) < (1 : ℤᵐ⁰) := by
    apply lt_of_le_of_ne z.property
    intro heq
    have hu : IsUnit z :=
      (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr heq
    exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hzI
  have hzδ : Valued.v (z : F) = Valued.v (δ : F) := by
    have hfactor : (z : F) * ((z : F) + 1) = (δ : F) := by
      have h := congrArg (fun x : S ↦ (x : F)) hz
      change (z : F) ^ 2 + (z : F) = (δ : F) at h
      linear_combination h
    rw [← hfactor, map_mul, add_comm (z : F) 1,
      (Valued.v : Valuation F ℤᵐ⁰).map_one_add_of_lt hzlt, mul_one]
  have hu : IsUnit (1 + 2 * z) := IsLocalRing.notMem_maximalIdeal.mp (by
    intro h
    have hone : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      simpa only [add_sub_cancel_right] using
        (IsLocalRing.maximalIdeal S).sub_mem h
          ((IsLocalRing.maximalIdeal S).mul_mem_left 2 hzI)
    exact (inferInstance : (IsLocalRing.maximalIdeal S).IsMaximal).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one))
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [hu.unit_spec]
    change (1 + 2 * (z : F)) ^ 2 = t
    have h := congrArg (fun x : S ↦ (x : F)) hz
    change (z : F) ^ 2 + (z : F) = (t - 1) / 4 at h
    linear_combination 4 * h
  · rw [hu.unit_spec]
    apply hγ
    rw [hzδ]
    exact ht.trans_le (by exact_mod_cast min_le_left γ 1)

end NormEuclidean.NearOneSquareRoots
