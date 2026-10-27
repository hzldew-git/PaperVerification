import NormEuclidean.ChapterX.ScalarNeighborhoods
import NormEuclidean.ChapterX.LocalLatticePatching
import NormEuclidean.ChapterX.ScalarSUnitContraction

/-!
# Small completed submodules for O'Meara 104:3

Coordinate valuation balls are actual submodules over the completed integer
ring and form neighborhoods of zero in the finite-dimensional module topology.
Finite generation then makes one sufficiently small global scalar shrink an
entire completed carrier, rather than only its chosen global generators.
-/

noncomputable section

namespace NormEuclidean.SmallCompletedModules

open IsDedekindDomain CompletedIntegralLattice Filter Topology
open scoped WithZero NormEuclidean.OrthogonalTopology

section Local

variable {K E ι : Type*} [Field K] [AddCommGroup E] [Finite ι]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R) [Module (LocalField R v) E]

/-- Coordinate valuation balls are modules over the actual local integer ring. -/
def valuationBox (b : Module.Basis ι (LocalField R v) E) (γ : ι → (ℤᵐ⁰)ˣ) :
    Submodule (LocalRing R v) E where
  carrier := {x | ∀ i, Valued.v (b.equivFun x i) < γ i}
  zero_mem' := by
    intro i
    simp only [map_zero, Pi.zero_apply, map_zero]
    exact Units.zero_lt (γ i)
  add_mem' := by
    intro x y hx hy i
    simp only [map_add, Pi.add_apply]
    exact (Valued.v.map_add _ _).trans_lt (max_lt (hx i) (hy i))
  smul_mem' := by
    intro a x hx i
    have h : b.equivFun (a • x) i = (a : LocalField R v) * b.equivFun x i := by
      rw [Subring.smul_def, map_smul]
      rfl
    rw [h, map_mul]
    exact (mul_le_of_le_one_left bot_le a.property).trans_lt (hx i)

variable [TopologicalSpace E] [IsModuleTopology (LocalField R v) E]

set_option backward.isDefEq.respectTransparency false in
/-- Every actual zero neighborhood contains a completed-integer submodule
which is itself a zero neighborhood. No local compactness input is needed. -/
theorem exists_submodule_neighborhood (b : Module.Basis ι (LocalField R v) E)
    (U : Set E) (hU : U ∈ 𝓝 (0 : E)) :
    ∃ B : Submodule (LocalRing R v) E, (B : Set E) ∈ 𝓝 (0 : E) ∧ (B : Set E) ⊆ U := by
  classical
  have hp : b.equivFun.symm ⁻¹' U ∈ 𝓝 (0 : ι → LocalField R v) := by
    apply (OrthogonalTopology.basisHomeomorph b).symm.continuous.continuousAt.preimage_mem_nhds
    change U ∈ 𝓝 (b.equivFun.symm 0)
    simpa only [map_zero] using hU
  rw [nhds_pi] at hp
  obtain ⟨I, _, t, ht, hsub⟩ := Filter.mem_pi.mp hp
  choose δ hδ using fun i ↦ Valued.mem_nhds.mp (ht i)
  let γ (i : ι) : (ℤᵐ⁰)ˣ := Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
    (f := (.ofClass (Valued.v : Valuation (LocalField R v) ℤᵐ⁰)))) (δ i)
  refine ⟨valuationBox R v b γ, ?_, ?_⟩
  · apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun x : E ↦ b.equivFun x i) :=
      (continuous_apply i).comp (OrthogonalTopology.basisHomeomorph b).continuous
    have hball := ScalarIntegralApproximation.valuation_ball_mem_nhds R v 0 (γ i)
    have h : (fun x : E ↦ b.equivFun x i) ⁻¹'
        {y : LocalField R v | Valued.v (y - 0) < γ i} ∈ 𝓝 (0 : E) :=
      hc.continuousAt.preimage_mem_nhds (by simpa only [map_zero, Pi.zero_apply] using hball)
    change {x : E | Valued.v (b.equivFun x i) < γ i} ∈ 𝓝 (0 : E)
    simpa only [sub_zero, Set.preimage_setOf_eq] using h
  · intro x hx
    have hcoord : b.equivFun x ∈ I.pi t := by
      intro i _
      apply hδ i
      apply (Valuation.restrict_lt_iff_lt_embedding
        (Valued.v : Valuation (LocalField R v) ℤᵐ⁰)).mpr
      change Valued.v (b.equivFun x i - 0) < (γ i : ℤᵐ⁰)
      rw [sub_zero]
      exact hx i
    have h := hsub hcoord
    simpa only [Set.mem_preimage, LinearEquiv.symm_apply_apply] using h

end Local

section Global

variable {K V : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Scaling as the image of an actual field-linear map. -/
def scaled (N : Submodule (integerSubring K) V) (d : integerSubring K) :
    Submodule (integerSubring K) V :=
  N.map (((d : K) • (LinearMap.id : V →ₗ[K] V)).restrictScalars (integerSubring K))

/-- One valuation precision controls every vector of an entire completed finite
module. The proof uses a submodule neighborhood, so arbitrary local integral
linear combinations are controlled rather than just the global generators. -/
theorem exists_precision (N : Submodule (integerSubring K) V) (hN : N.FG)
    (v : HeightOneSpectrum (integerSubring K))
    (U : Set (Space (V := V) (integerSubring K) v)) (hU : U ∈ 𝓝 0) :
    ∃ γ : (ℤᵐ⁰)ˣ, ∀ d : integerSubring K, v.intValuation d < γ →
      (carrier (integerSubring K) v (scaled N d) : Set _) ⊆ U := by
  classical
  let b := (Module.finBasis K V).baseChange (LocalField (integerSubring K) v)
  obtain ⟨B, hB, hBU⟩ := exists_submodule_neighborhood (integerSubring K) v b U hU
  obtain ⟨s, hs⟩ := hN
  have hgen (x : s) : ∃ γ : (ℤᵐ⁰)ˣ, ∀ d : integerSubring K,
      v.intValuation d < γ → inclusion (integerSubring K) v ((d : K) • (x : V)) ∈ B := by
    let f (a : LocalField (integerSubring K) v) := a • inclusion (integerSubring K) v (x : V)
    have hf : Continuous f := by
      change Continuous (fun a : LocalField (integerSubring K) v ↦
        a • inclusion (integerSubring K) v (x : V))
      exact (continuous_id : Continuous (fun a : LocalField (integerSubring K) v ↦ a)).smul
        (continuous_const : Continuous (fun _ : LocalField (integerSubring K) v ↦
          inclusion (integerSubring K) v (x : V)))
    have hpre : f ⁻¹' (B : Set _) ∈ 𝓝 (algebraMap K (LocalField (integerSubring K) v)
        ((0 : integerSubring K) : K)) := by
      apply hf.continuousAt.preimage_mem_nhds
      simpa only [f, Subring.coe_zero, map_zero, zero_smul] using hB
    obtain ⟨γ, hγ⟩ := ScalarNeighborhoods.finite_precision v 0 _ hpre
    refine ⟨γ, fun d hd ↦ ?_⟩
    have h := hγ d (by simpa only [sub_zero] using hd)
    change algebraMap K (LocalField (integerSubring K) v) (d : K) •
      inclusion (integerSubring K) v (x : V) ∈ B at h
    rw [map_smul, ← IsScalarTower.algebraMap_smul
      (R := K) (A := LocalField (integerSubring K) v)]
    exact h
  choose γ hγ using hgen
  obtain ⟨γ₀, hγ₀⟩ := Finite.exists_ge γ
  refine ⟨γ₀, ?_⟩
  intro d hd
  have hspan (x : V) (hx : x ∈ N) :
      inclusion (integerSubring K) v ((d : K) • x) ∈ B := by
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hγ ⟨x, hx⟩ d (hd.trans_le (hγ₀ ⟨x, hx⟩))
    | zero => simpa only [smul_zero, map_zero] using B.zero_mem
    | add x y _ _ hx hy =>
        rw [smul_add, map_add]
        exact B.add_mem hx hy
    | smul a x _ hx =>
        change inclusion (integerSubring K) v ((d : K) • ((a : K) • x)) ∈ B
        rw [smul_comm (d : K) (a : K)]
        change inclusion (integerSubring K) v (a • ((d : K) • x)) ∈ B
        rw [inclusion_smul]
        exact B.smul_mem _ hx
  have hCB : carrier (integerSubring K) v (scaled N d) ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact hspan y hy
  exact fun x hx ↦ hBU (hCB hx)

/-- A finite full global module has an actual finite full submodule which is
arbitrarily small at all prescribed finite places and has exactly the original
completed carrier everywhere else. Empty targets and dyadic places are allowed. -/
theorem exists_small_module (N : Submodule (integerSubring K) V) (hNfg : N.FG)
    (hN : Submodule.span K (N : Set V) = ⊤)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (U : (v : T) → Set (Space (V := V) (integerSubring K) v.1))
    (hU : ∀ v, U v ∈ 𝓝 0) :
    ∃ M : Submodule (integerSubring K) V, M.FG ∧ Submodule.span K (M : Set V) = ⊤ ∧
      M ≤ N ∧ (∀ v : T, (carrier (integerSubring K) v.1 M : Set _) ⊆ U v) ∧
      ∀ v : HeightOneSpectrum (integerSubring K), v ∉ T →
        carrier (integerSubring K) v M = carrier (integerSubring K) v N := by
  classical
  choose γ hγ using fun v : T ↦ exists_precision N hNfg v.1 (U v) (hU v)
  obtain ⟨d, hd0, hdT, hdout⟩ := ScalarSUnitContraction.exists_finite_contraction T γ
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  let f := (d : K) • (LinearMap.id : V →ₗ[K] V)
  have hf : Function.Surjective f := by
    intro x
    refine ⟨(d : K)⁻¹ • x, ?_⟩
    change (d : K) • ((d : K)⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hdK, one_smul]
  have hfull : Submodule.span K (scaled N d : Set V) = ⊤ := by
    rw [scaled, Submodule.map_coe]
    change Submodule.span K (f '' (N : Set V)) = ⊤
    rw [Submodule.span_image, hN, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf
  have hle : scaled N d ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact N.smul_mem d hx
  refine ⟨scaled N d, hNfg.map _, hfull, hle, fun v ↦ hγ v d (hdT v), ?_⟩
  intro v hv
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono hle)
  · apply carrier_le_of_scaled_le_of_not_mem
      (integerSubring K) v N (scaled N d) d
    · intro x hx
      exact ⟨x, hx, rfl⟩
    · exact hdout v hv

end Global

end NormEuclidean.SmallCompletedModules
