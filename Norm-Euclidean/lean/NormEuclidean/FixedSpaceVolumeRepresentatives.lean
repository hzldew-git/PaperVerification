import NormEuclidean.ChapterX.VolumeClassFiniteness
import NormEuclidean.IntegralFrameIntervals

/-!
# Fixed-space representatives for norm-integral lattices

The fixed-space theorem is applied after doubling, where the half-polar scale
is integral. Representatives are selected from the original family and the
doubling scalar is cancelled, so integrality of a halved arbitrary lattice
is never assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.FixedSpaceVolumeRepresentatives

open Module VolumeClassFiniteness
open scoped NumberField Classical nonZeroDivisors

variable {K V W : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem map_volume {Q : QuadraticForm K V} {P : QuadraticForm K W}
    (L : Lattice (integerSubring K) Q) (e : Q.IsometryEquiv P) :
    (IntegralFrameIntervals.map L e).volumeIdeal = L.volumeIdeal := by
  apply FractionalIdeal.coeToSubmodule_injective
  change MixedVolume.submodule (integerSubring K) (halfPolar P) (finrank K W)
      (L.carrier.map (e.toLinearEquiv.toLinearMap.restrictScalars (integerSubring K))) =
    MixedVolume.submodule (integerSubring K) (halfPolar Q) (finrank K V) L.carrier
  rw [e.toLinearEquiv.finrank_eq]
  apply MixedVolume.map_isometry
  intro x y
  change halfPolar P (e x) (e y) = halfPolar Q x y
  simp only [halfPolar_apply, QuadraticMap.polar]
  have hadd : e (x + y) = e x + e y := e.toLinearEquiv.map_add x y
  rw [← hadd, e.map_app, e.map_app, e.map_app]

variable [FiniteDimensional K V]

/-- Every original norm-integral lattice is covered by one of finitely many
original norm-integral representatives. Integral half-polar scale is not an
extra hypothesis on the original family. -/
theorem exists_finite_representatives (Q : QuadraticForm K V) (hA : Q.Anisotropic)
    (S : Set (FractionalIdeal (integerSubring K)⁰ K)) (hS : S.Finite) :
    ∃ A : Set (Lattice (integerSubring K) Q), A.Finite ∧
      (∀ N ∈ A, N.volumeIdeal ∈ S) ∧
      ∀ L : Lattice (integerSubring K) Q, L.volumeIdeal ∈ S →
        ∃ N ∈ A, GloballyIsometric Q L N := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  have hQ := quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA
  let P := (2 : K) • Q
  have hPA : P.Anisotropic := by
    intro x hx
    apply hA x
    have he : (2 : K) * Q x = 0 := hx
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  have hP := quadraticForm_polarBilin_nondegenerate_of_anisotropic P hPA
  let f := FractionalIdeal.spanSingleton (integerSubring K)⁰ ((2 : K) ^ finrank K V)
  have hf : f ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr
    (pow_ne_zero _ (by norm_num))
  let S' := {I ∈ S | I ≠ 0}
  have hS' : S'.Finite := hS.subset fun _ h ↦ h.1
  let T (I : FractionalIdeal (integerSubring K)⁰ K) :=
    ordinaryClass P '' {M : Lattice (integerSubring K) P |
      M.scaleIdeal ≤ 1 ∧ f * I ≤ M.volumeIdeal}
  have hT (I) (hI : I ∈ S') : (T I).Finite :=
    finite_bounded_ordinary_classes P hP (f * I) (mul_ne_zero hf hI.2)
  let g (L : Lattice (integerSubring K) Q) := ordinaryClass P (L.rescale 2)
  let C := g '' {L : Lattice (integerSubring K) Q | L.volumeIdeal ∈ S}
  have hC : C.Finite := by
    apply (hS'.biUnion hT).subset
    rintro _ ⟨L, hL, rfl⟩
    refine Set.mem_iUnion_of_mem L.volumeIdeal
      (Set.mem_iUnion_of_mem ⟨hL, L.volumeIdeal_ne_zero hQ⟩ ?_)
    refine ⟨L.rescale 2, ⟨L.doubled_scaleIdeal_le_one, ?_⟩, rfl⟩
    rw [L.volumeIdeal_rescale]
    rfl
  letI : Finite C := hC
  let rep (c : C) : Lattice (integerSubring K) Q := Classical.choose c.property
  have hrep (c : C) : (rep c).volumeIdeal ∈ S ∧ g (rep c) = c.val :=
    Classical.choose_spec c.property
  refine ⟨Set.range rep, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact (hrep c).1
  · intro L hL
    let c : C := ⟨g L, ⟨L, hL, rfl⟩⟩
    have he : g L = g (rep c) := (hrep c).2.symm
    have hi : GloballyIsometric P (L.rescale 2) ((rep c).rescale 2) := Quotient.exact he
    obtain ⟨e⟩ := hi
    exact ⟨rep c, Set.mem_range_self c, ⟨LatticeIsometry.of_rescale 2 (by norm_num) e⟩⟩

end NormEuclidean.FixedSpaceVolumeRepresentatives
