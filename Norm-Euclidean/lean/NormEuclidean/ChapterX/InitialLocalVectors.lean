import NormEuclidean.ChapterX.NearOneSquareRoots
import NormEuclidean.ChapterX.ScalarSUnitContraction
import NormEuclidean.ChapterX.ScalarNeighborhoods

/-!
# Initial exceptional-place vectors when the denominator is a local unit

A nonzero represented vector is contracted by an actual nonzero global
integer. A controlled unit square root then solves the residual equation
with beta arbitrarily close to the reciprocal of the local denominator.
This constructs the initial vectors at target places, including dyadic ones.
Places where the denominator is not a unit require a separate argument.
-/

noncomputable section

namespace NormEuclidean.InitialLocalVectors

open IsDedekindDomain CompletedIntegralLattice Filter Topology
open scoped WithZero

variable {K : Type*} [Field K] [NumberField K]

section Local

variable {E : Type*} [AddCommGroup E]
variable (v : HeightOneSpectrum (integerSubring K))
  [Module (LocalField (integerSubring K) v) E]

set_option backward.isDefEq.respectTransparency false in
/-- Every neighborhood of zero contains a nonzero value represented in the
same local integral module, by an explicit contraction of the given vector. -/
theorem exists_small_nonzero_value
    (Q : QuadraticForm (LocalField (integerSubring K) v) E)
    (N : Submodule (LocalRing (integerSubring K) v) E)
    (x : E) (hx : x ∈ N) (hx0 : Q x ≠ 0)
    (B : Set (LocalField (integerSubring K) v)) (hB : B ∈ 𝓝 0) :
    ∃ y ∈ N, Q y ≠ 0 ∧ Q y ∈ B := by
  let F := LocalField (integerSubring K) v
  let S := LocalRing (integerSubring K) v
  let f (d : F) := d ^ 2 * Q x
  have hf : Continuous f :=
    ((continuous_id : Continuous (fun d : F ↦ d)).pow 2).mul continuous_const
  have hpre : f ⁻¹' B ∈ 𝓝 (algebraMap K F ((0 : integerSubring K) : K)) := by
    rw [Subring.coe_zero, map_zero]
    apply hf.continuousAt.preimage_mem_nhds
    change B ∈ 𝓝 ((0 : F) ^ 2 * Q x)
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul] using hB
  obtain ⟨γ, hγ⟩ := ScalarNeighborhoods.finite_precision v 0 _ hpre
  obtain ⟨d, hd0, hd, _⟩ := ScalarSUnitContraction.exists_finite_contraction
    {v} (fun _ ↦ γ)
  have hdin : v.intValuation (d - 0) < γ := by
    simpa only [sub_zero] using hd ⟨v, by simp⟩
  let ds : S := ⟨algebraMap K F (d : K), algebraMap_mem (integerSubring K) v d.property⟩
  have hds : (ds : F) ≠ 0 := by
    apply (map_ne_zero (algebraMap K F)).mpr
    exact_mod_cast hd0
  have hvalue : Q (ds • x) = (ds : F) ^ 2 * Q x := by
    change Q ((ds : F) • x) = _
    rw [Q.map_smul]
    simp only [smul_eq_mul, pow_two]
  refine ⟨ds • x, N.smul_mem ds hx, ?_, ?_⟩
  · rw [hvalue]
    exact mul_ne_zero (pow_ne_zero 2 hds) hx0
  · rw [hvalue]
    exact hγ d hdin

/-- A local unit denominator and a nonzero local represented vector suffice
to construct an initial residual vector. Beta lies in the requested open
part of the neighborhood, so that the neighborhood is also a neighborhood
of beta, as required by the finite scalar selection theorem. -/
theorem exists_initial_vector
    (Q : QuadraticForm (LocalField (integerSubring K) v) E)
    (N : Submodule (LocalRing (integerSubring K) v) E)
    (x : E) (hx : x ∈ N) (hx0 : Q x ≠ 0)
    (a : LocalField (integerSubring K) v) (ha : a ≠ 0)
    (c : (LocalRing (integerSubring K) v)ˣ)
    (C : Set (LocalField (integerSubring K) v))
    (hC : C ∈ 𝓝 (((c : LocalRing (integerSubring K) v) :
      LocalField (integerSubring K) v)⁻¹)) :
    ∃ β : (LocalRing (integerSubring K) v)ˣ,
      ((β : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ∈ C ∧
      C ∈ 𝓝 ((β : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ∧
      ∃ y ∈ N, Q y ≠ 0 ∧ Q y = a *
        (1 - ((c : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ^ 2 *
          ((β : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ^ 2) := by
  let F := LocalField (integerSubring K) v
  let S := LocalRing (integerSubring K) v
  let cf : F := (c : S)
  have hc : cf ≠ 0 := (c.isUnit.map S.subtype).ne_zero
  let D : Set F := (fun u : F ↦ u / cf) ⁻¹' interior C
  have hD : D ∈ 𝓝 (1 : F) := by
    apply (continuous_id.div_const cf).continuousAt.preimage_mem_nhds
    change interior C ∈ 𝓝 ((1 : F) / cf)
    simpa only [one_div] using interior_mem_nhds.mpr hC
  obtain ⟨U, hU, hroot⟩ := NearOneSquareRoots.exists_square_roots_in_neighborhood v D hD
  let f (t : F) := 1 - t / a
  have hf : Continuous f := by fun_prop
  have hpre : f ⁻¹' U ∈ 𝓝 (0 : F) := by
    apply hf.continuousAt.preimage_mem_nhds
    change U ∈ 𝓝 (1 - (0 : F) / a)
    simpa only [zero_div, sub_zero] using hU
  obtain ⟨y, hy, hy0, hyU⟩ := exists_small_nonzero_value v Q N x hx hx0 _ hpre
  obtain ⟨u, hu, huD⟩ := hroot (f (Q y)) hyU
  let β := c⁻¹ * u
  have hmul : (c : S) * (β : S) = (u : S) := by simp [β, ← mul_assoc]
  have hmulF : cf * ((β : S) : F) = ((u : S) : F) :=
    congrArg (fun z : S ↦ (z : F)) hmul
  have hβ : ((β : S) : F) = ((u : S) : F) / cf := by
    apply (eq_div_iff hc).mpr
    rw [mul_comm]
    exact hmulF
  have hβint : ((β : S) : F) ∈ interior C := by
    rw [hβ]
    exact huD
  refine ⟨β, interior_subset hβint,
    mem_of_superset (isOpen_interior.mem_nhds hβint) interior_subset, y, hy, hy0, ?_⟩
  change Q y = a * (1 - cf ^ 2 * ((β : S) : F) ^ 2)
  rw [← mul_pow, hmulF, hu]
  dsimp only [f]
  field_simp
  ring

end Local

section Completed

variable {V : Type*} [AddCommGroup V] [Module K V] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
/-- A regular positive-dimensional full global module has an actual
nonzero-value vector. No integral quadratic values or free basis are assumed. -/
theorem exists_nonzero_value (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (N : Submodule (integerSubring K) V)
    (hN : Submodule.span K (N : Set V) = ⊤) : ∃ x ∈ N, Q x ≠ 0 := by
  letI : FiniteDimensional K V := Module.finite_of_finrank_pos hpos
  have hex : ∃ x : V, Q x ≠ 0 := by
    by_contra! hzero
    obtain ⟨e, he⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    apply he
    apply hQ.1 e
    intro y
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hzero]
  obtain ⟨x, hx⟩ := hex
  obtain ⟨d, hd0, hd⟩ := ScalarExtension.exists_denominator N hN x
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  refine ⟨(d : K) • x, hd, ?_⟩
  rw [Q.map_smul, smul_eq_mul]
  exact mul_ne_zero (mul_ne_zero hdK hdK) hx

/-- At every finite place where the denominator is a unit, the initial
completed residual vector is constructed from regularity and fullness. -/
theorem exists_initial_completed_vector (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hpos : 0 < Module.finrank K V)
    (N : Submodule (integerSubring K) V) (hN : Submodule.span K (N : Set V) = ⊤)
    (v : HeightOneSpectrum (integerSubring K))
    (a : LocalField (integerSubring K) v) (ha : a ≠ 0)
    (c : (LocalRing (integerSubring K) v)ˣ)
    (C : Set (LocalField (integerSubring K) v))
    (hC : C ∈ 𝓝 (((c : LocalRing (integerSubring K) v) :
      LocalField (integerSubring K) v)⁻¹)) :
    ∃ β : (LocalRing (integerSubring K) v)ˣ,
      ((β : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ∈ C ∧
      C ∈ 𝓝 ((β : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ∧
      ∃ y ∈ carrier (integerSubring K) v N,
        form (integerSubring K) v Q y ≠ 0 ∧ form (integerSubring K) v Q y = a *
          (1 - ((c : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ^ 2 *
            ((β : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ^ 2) := by
  obtain ⟨x, hx, hx0⟩ := exists_nonzero_value Q hQ hpos N hN
  have hxv : form (integerSubring K) v Q (inclusion (integerSubring K) v x) ≠ 0 := by
    rw [form_inclusion]
    exact (map_ne_zero (algebraMap K (LocalField (integerSubring K) v))).mpr hx0
  exact exists_initial_vector v _ _ _ (inclusion_mem (integerSubring K) v N hx) hxv
    a ha c C hC

end Completed

end NormEuclidean.InitialLocalVectors
