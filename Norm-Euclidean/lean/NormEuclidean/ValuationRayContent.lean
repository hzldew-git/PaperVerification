import NormEuclidean.ChapterX.CompletedTopology

/-!
# Scalar content of a local vector and its open neighborhoods

The scalar-membership predicate records a generator of the local content
ideal without choosing a basis of the integral lattice.
-/

noncomputable section

namespace NormEuclidean.ValuationRayContent

open Filter Topology
open scoped WithZero

variable {F W : Type*} [Field F] [Valued F ℤᵐ⁰] [AddCommGroup W] [Module F W]

local notation "v" => (Valued.v : Valuation F ℤᵐ⁰)

/-- Scalar membership is measured by one nonzero local scalar. -/
def HasContent (N : Set W) (x : W) (a : Fˣ) : Prop :=
  ∀ b : F, b • x ∈ N ↔ v (b * (a : F)) ≤ 1

/-- The valuation of a content generator is intrinsic. -/
theorem valuation_eq {N : Set W} {x : W} {a c : Fˣ}
    (ha : HasContent N x a) (hc : HasContent N x c) :
    Valued.v (a : F) = Valued.v (c : F) := by
  have hax : (a : F)⁻¹ • x ∈ N := (ha _).mpr (by simp)
  have hcx : (c : F)⁻¹ • x ∈ N := (hc _).mpr (by simp)
  have hac := (hc _).mp hax
  have hca := (ha _).mp hcx
  rw [mul_comm, ← div_eq_mul_inv, map_div₀] at hac hca
  have hcpos : (0 : ℤᵐ⁰) < v (c : F) :=
    bot_lt_iff_ne_bot.mpr ((Valuation.ne_zero_iff v).mpr c.ne_zero)
  have hapos : (0 : ℤᵐ⁰) < v (a : F) :=
    bot_lt_iff_ne_bot.mpr ((Valuation.ne_zero_iff v).mpr a.ne_zero)
  exact le_antisymm
    ((div_le_one₀ hcpos).mp hca) ((div_le_one₀ hapos).mp hac)

/-- Lattice-preserving equivalences preserve scalar content. -/
theorem equiv_iff {N : Set W}
    (g : W ≃ₗ[F] W) (hg : ∀ x, g x ∈ N ↔ x ∈ N) (x : W) (a : Fˣ) :
    HasContent N (g x) a ↔ HasContent N x a := by
  simp only [HasContent, ← g.map_smul, hg]

variable [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul F W]

/-- A primitive vector with an integral coordinate has an open neighborhood
of scalar multiples with the same local content valuation. -/
theorem eventually_hasContent (N : Set W)
    (hN : IsOpen (N : Set W)) (phi : W →ₗ[F] F) (hphi : Continuous phi)
    (hsmul : ∀ r : F, v r ≤ 1 → ∀ x ∈ N, r • x ∈ N)
    (hphiN : ∀ x ∈ N, Valued.v (phi x) ≤ 1) (e : W) (he : e ∈ N)
    (hphie : phi e = 1) (a : Fˣ) :
    ∀ᶠ x in 𝓝 ((a : F) • e), HasContent N x a := by
  have hmem : ∀ᶠ x in 𝓝 ((a : F) • e), (a : F)⁻¹ • x ∈ N := by
    apply (hN.preimage (continuous_const_smul _)).mem_nhds
    change (a : F)⁻¹ • ((a : F) • e) ∈ N
    rw [smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul]
    exact he
  have hcoord : ∀ᶠ x in 𝓝 ((a : F) • e), Valued.v (phi x) = Valued.v (a : F) := by
    have ht : Tendsto phi (𝓝 ((a : F) • e)) (𝓝 (a : F)) := by
      simpa only [map_smul, hphie, smul_eq_mul, mul_one] using hphi.tendsto ((a : F) • e)
    exact ht.eventually (Valued.locally_const (by simpa using a.ne_zero))
  filter_upwards [hmem, hcoord] with x hx hv
  intro b
  constructor
  · intro hbx
    have h := hphiN _ hbx
    simpa only [map_smul, smul_eq_mul, map_mul, hv] using h
  · intro hb
    have h := hsmul (b * (a : F)) hb _ hx
    simpa only [smul_smul, mul_assoc, mul_inv_cancel₀ a.ne_zero, mul_one] using h

end NormEuclidean.ValuationRayContent
