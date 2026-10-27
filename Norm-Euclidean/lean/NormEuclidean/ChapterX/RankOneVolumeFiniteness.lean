import NormEuclidean.ChapterX.VolumeIdeal
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# The rank-one base of 103:4

On a fixed regular line, a lower volume ideal and norm integrality put the
actual lattices into one finite module interval. Finiteness here is of the
actual carriers, which is stronger than finiteness of their isometry classes.
-/

noncomputable section

namespace NormEuclidean.RankOneVolumeFiniteness

open Module IntegralVolume
open scoped nonZeroDivisors Pointwise

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Reconstruction in a one-vector field basis. -/
theorem reconstruct (b : Basis (Fin 1) K V) (x : V) :
    x = (b.repr x 0) • b 0 := by
  simpa only [Fin.sum_univ_one] using (b.sum_repr x).symm

/-- A fixed integral nonzero basis value clears every coefficient of a
norm-integral lattice on the line. Square integrality is proved, not assumed. -/
theorem integral_value_times_coefficient (Q : QuadraticForm K V)
    (b : Basis (Fin 1) K V) (hβ : Q (b 0) ∈ integerSubring K)
    (L : Lattice (integerSubring K) Q) (x : V) (hx : x ∈ L.carrier) :
    Q (b 0) * b.repr x 0 ∈ integerSubring K := by
  let a := b.repr x 0
  let β := Q (b 0)
  have hQ : Q x = a ^ 2 * β := by
    calc
      Q x = Q (a • b 0) := congrArg Q (reconstruct b x)
      _ = a ^ 2 * β := by simp only [Q.map_smul, smul_eq_mul, pow_two]; rfl
  have hpow : (β * a) ^ 2 = β * Q x := by rw [hQ]; ring
  have hint : IsIntegral ℤ ((β * a) ^ 2) := by
    rw [hpow]
    exact ((mem_integerSubring K _).mp hβ).mul
      ((mem_integerSubring K _).mp (L.integral x hx))
  exact (mem_integerSubring K _).mpr (hint.of_pow (by decide : 0 < 2))

/-- Every volume element sends the fixed integral basis vector into the
source lattice. This holds for actual intrinsic mixed determinant generators. -/
theorem volume_scalar_mem (Q : QuadraticForm K V) (b : Basis (Fin 1) K V)
    (hβ : Q (b 0) ∈ integerSubring K) (L : Lattice (integerSubring K) Q)
    (t : K) (ht : t ∈ volumeSubmodule (halfPolar Q) 1 L.carrier) :
    t • b 0 ∈ L.carrier := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨p, rfl⟩ := ht
    change (pairingMatrix (halfPolar Q) (fun i ↦ (p.1 i : V))
      (fun j ↦ (p.2 j : V))).det • b 0 ∈ L.carrier
    rw [Matrix.det_unique]
    let x : V := p.1 0
    let z : V := p.2 0
    let a := b.repr x 0
    let β := Q (b 0)
    have ha := integral_value_times_coefficient Q b hβ L x (p.1 0).2
    have hx : x = a • b 0 := reconstruct b x
    have hz : z = (b.repr z 0) • b 0 := reconstruct b z
    have heq : halfPolar Q x z • b 0 = (β * a) • z := by
      rw [hx, hz, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
        halfPolar_self, smul_smul]
      congr 1
      ring
    change halfPolar Q x z • b 0 ∈ L.carrier
    rw [heq]
    exact L.carrier.smul_mem (⟨β * a, ha⟩ : integerSubring K) (p.2 0).2
  | zero => simp
  | add a b _ _ ha hb => simpa only [add_smul] using L.carrier.add_mem ha hb
  | smul r a _ ha =>
    simpa only [Subring.smul_def, smul_eq_mul, smul_smul] using L.carrier.smul_mem r ha

/-- A positive-rank regular lattice contains an actual vector of nonzero value. -/
theorem exists_nonzero_integral_value (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hpos : 0 < Module.finrank K V)
    (L : Lattice (integerSubring K) Q) : ∃ x ∈ L.carrier, Q x ≠ 0 := by
  let q := SpinorBridge.quadraticSpace Q hQ
  obtain ⟨u, hu⟩ := q.exists_isAnisotropic_of_finrank_pos hpos
  have huQ : Q u ≠ 0 := by
    simpa only [Bong.QuadraticSpace.IsAnisotropic, q,
      SpinorBridge.quadraticSpace_quadratic] using hu
  obtain ⟨d, hd0, hd⟩ := ScalarExtension.exists_denominator L.carrier L.full u
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  refine ⟨(d : K) • u, hd, ?_⟩
  rw [Q.map_smul, smul_eq_mul]
  exact mul_ne_zero (mul_ne_zero hdK hdK) huQ

/-- A regular rank-one reference lattice gives a fixed finite interval
containing all norm-integral lattices above the prescribed nonzero volume. -/
theorem finite_rank_one_lattices_from_reference (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 1)
    (L₀ : Lattice (integerSubring K) Q) (c : FractionalIdeal (integerSubring K)⁰ K)
    (hc : c ≠ 0) :
    {L : Lattice (integerSubring K) Q | c ≤ L.volumeIdeal}.Finite := by
  classical
  let b := (Module.finBasis K V).reindex (finCongr hdim)
  obtain ⟨d, hd0, hd⟩ := exists_common_denominator L₀.carrier L₀.full
    (Finset.univ.image b)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  let b' := b.unitsSMul (fun _ ↦ Units.mk0 (d : K) hdK)
  have hb' : b' 0 ∈ L₀.carrier := by
    simpa only [b', Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0] using
      hd (b 0) (Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩)
  let β := Q (b' 0)
  have hβ : β ∈ integerSubring K := L₀.integral _ hb'
  have hβ0 : β ≠ 0 := by
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b').mp
      (SpinorBridge.quadraticSpace Q hQ).nondegenerate
    change (LinearMap.BilinForm.toMatrix b' (halfPolar Q)).det ≠ 0 at h
    simpa only [Matrix.det_unique, Fin.default_eq_zero,
      LinearMap.BilinForm.toMatrix_apply, halfPolar_self] using h
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hc)
  let A := Submodule.span (integerSubring K) {δ • b' 0}
  let U := Submodule.span (integerSubring K) {β⁻¹ • b' 0}
  have hA : Submodule.span K (A : Set V) = ⊤ := by
    apply top_unique
    intro x _
    have hmem : δ • b' 0 ∈ Submodule.span K (A : Set V) :=
      Submodule.subset_span (Submodule.subset_span (Set.mem_singleton _))
    have h := (Submodule.span K (A : Set V)).smul_mem (b'.repr x 0 * δ⁻¹) hmem
    simpa only [smul_smul, mul_assoc, inv_mul_cancel₀ hδ0, mul_one,
      ← reconstruct b' x] using h
  letI : Ring.HasFiniteQuotients (integerSubring K) :=
    inferInstanceAs (Ring.HasFiniteQuotients (NumberField.RingOfIntegers K))
  have hinterval := LatticeInterval.finite_interval_of_full (integerSubring K) A U hA
    (Submodule.fg_span (Set.finite_singleton _))
  apply Set.Finite.of_injOn (f := fun L : Lattice (integerSubring K) Q ↦ L.carrier)
    (t := {M : Submodule (integerSubring K) V | A ≤ M ∧ M ≤ U})
  · intro L hL
    constructor
    · apply Submodule.span_le.mpr
      rintro _ rfl
      have hδL : δ ∈ volumeSubmodule (halfPolar Q) (Module.finrank K V) L.carrier := hL hδ
      rw [hdim] at hδL
      exact volume_scalar_mem Q b' hβ L δ hδL
    · intro x hx
      have hi := integral_value_times_coefficient Q b' hβ L x hx
      apply Submodule.mem_span_singleton.mpr
      refine ⟨(⟨β * b'.repr x 0, hi⟩ : integerSubring K), ?_⟩
      change (β * b'.repr x 0) • (β⁻¹ • b' 0) = x
      rw [smul_smul, mul_comm β (b'.repr x 0), mul_assoc, mul_inv_cancel₀ hβ0, mul_one]
      exact (reconstruct b' x).symm
  · intro L _ M _ h
    cases L
    cases M
    cases h
    rfl
  · exact hinterval

/-- The rank-one base of bounded-volume class finiteness is unconditional:
if the family is nonempty a reference is chosen from it; otherwise it is empty. -/
theorem finite_rank_one_lattices (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 1)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    {L : Lattice (integerSubring K) Q | c ≤ L.volumeIdeal}.Finite := by
  by_cases h : ({L : Lattice (integerSubring K) Q | c ≤ L.volumeIdeal} : Set _).Nonempty
  · obtain ⟨L₀, _⟩ := h
    exact finite_rank_one_lattices_from_reference Q hQ hdim L₀ c hc
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact Set.finite_empty

end NormEuclidean.RankOneVolumeFiniteness
