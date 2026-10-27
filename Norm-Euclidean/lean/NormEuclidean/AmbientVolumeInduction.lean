import NormEuclidean.PositiveVolumeValues
import NormEuclidean.OrthogonalCoordinateExtension
import NormEuclidean.ChapterX.ProjectedVolume
import NormEuclidean.ChapterX.VolumeFiniteness

/-!
# Finite ambient spaces in every fixed rank from finite volume ideals

Induction uses uniform small represented values, the actual projected lattice,
and its proved volume-ideal inclusion. Doubling removes integral half-polar
scale from the final theorem. The integral module may be nonfree.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.AmbientVolumeInduction

open Module IntegralVolume ProjectedComplement ProjectedVolume CoordinateFormFiniteness
open scoped Classical nonZeroDivisors

universe v
variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (NumberField.RingOfIntegers K))
local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers K))

/-- Finite ambient forms for integral-scale lattices, with the set chosen
before the varying quadratic space. This is the induction statement. -/
theorem exists_finite_forms_integral_scale (n : ℕ)
    (S : Set (FractionalIdeal (integerSubring K)⁰ K)) (hS : S.Finite) :
    ∃ F : Set (QuadraticForm K (Fin n → K)), F.Finite ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic → finrank K V = n →
        L.scaleIdeal ≤ 1 → L.volumeIdeal ∈ S →
        ∃ b : Basis (Fin n) K V, Q.basisRepr b ∈ F := by
  classical
  induction n generalizing S with
  | zero =>
    refine ⟨{0}, Set.finite_singleton _, ?_⟩
    intro V _ _ Q L _ hr _ _
    letI := L.finiteDimensional
    refine ⟨Module.finBasisOfFinrankEq K V hr, ?_⟩
    apply Set.mem_singleton_iff.mpr
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  | succ n ih =>
    obtain ⟨C, hC⟩ := (hS.image FractionalIdeal.absNorm).bddAbove
    obtain ⟨Φ, hΦ, hvalue⟩ :=
      PositiveVolumeValues.exists_finite_values (K := K) (n + 1) (by omega) C
    let Φ' : Set K := {a ∈ Φ | a ≠ 0}
    let S' := {I ∈ S | I ≠ 0}
    have hΦ' : Φ'.Finite := hΦ.subset fun _ h ↦ h.1
    have hS' : S'.Finite := hS.subset fun _ h ↦ h.1
    let T (a : K) (I : FractionalIdeal (integerSubring K)⁰ K) :=
      {J : FractionalIdeal (integerSubring K)⁰ K |
        FractionalIdeal.spanSingleton (integerSubring K)⁰ (a ^ (2 * (n + 1))) * I ≤ J ∧
          J ≤ 1}
    have hT (a) (ha : a ∈ Φ') (I) (hI : I ∈ S') : (T a I).Finite :=
      finite_integral_ideals_containing _
        (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
          (pow_ne_zero _ ha.2)) hI.2)
    let U := ⋃ a ∈ Φ', ⋃ I ∈ S', T a I
    have hU : U.Finite := hΦ'.biUnion fun a ha ↦ hS'.biUnion (hT a ha)
    obtain ⟨F, hF, hforms⟩ := ih U hU
    let B := ⋃ a ∈ Φ', (fun P ↦ OrthogonalCoordinateExtension.block a (polarMatrix n P)) '' F
    have hB : B.Finite := hΦ'.biUnion fun a _ ↦ hF.image _
    refine ⟨polarMatrix (n + 1) ⁻¹' B,
      hB.preimage (polarMatrix_injective (n + 1)).injOn, ?_⟩
    intro V _ _ Q L hA hr hs hvol
    letI := L.finiteDimensional
    letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
    have hQ := quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA
    obtain ⟨y, hy, hy0, hyΦ⟩ := hvalue V Q L hA hr (hC ⟨_, hvol, rfl⟩)
    let P := Q.comp (complement Q y).subtype
    let N := projectedLattice Q L y hy hs hy0
    have hPA : P.Anisotropic := fun x hx ↦ Subtype.ext (hA (x : V) hx)
    have hdim : finrank K (complement Q y) = n := by
      have h := complement_finrank Q y hy0
      omega
    have hNV : N.volumeIdeal ∈ U := by
      refine Set.mem_iUnion_of_mem (Q y) (Set.mem_iUnion_of_mem ⟨hyΦ, hy0⟩
        (Set.mem_iUnion_of_mem L.volumeIdeal
          (Set.mem_iUnion_of_mem ⟨hvol, L.volumeIdeal_ne_zero hQ⟩ ?_)))
      refine ⟨?_, N.volumeIdeal_le_one (projected_scale_integral Q L y hy hs hy0)⟩
      simpa only [hr] using scaled_volumeIdeal_le_projected Q L y hy hs hy0
    obtain ⟨b, hb⟩ := hforms (complement Q y) P N hPA hdim
      (projected_scale_integral Q L y hy hs hy0) hNV
    refine ⟨OrthogonalCoordinateExtension.basis Q y hy0 b, ?_⟩
    change polarMatrix (n + 1) _ ∈ B
    rw [OrthogonalCoordinateExtension.polarMatrix_basis]
    exact Set.mem_iUnion_of_mem (Q y)
      (Set.mem_iUnion_of_mem ⟨hyΦ, hy0⟩ ⟨P.basisRepr b, hb, rfl⟩)

/-- In every fixed rank, norm-integral anisotropic lattices with volume in
a finite set have only finitely many ambient quadratic spaces. No class
bound, Euclidean approximation, or integral-scale hypothesis is used. -/
theorem exists_finite_forms (n : ℕ)
    (S : Set (FractionalIdeal (integerSubring K)⁰ K)) (hS : S.Finite) :
    ∃ F : Set (QuadraticForm K (Fin n → K)), F.Finite ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic → finrank K V = n →
        L.volumeIdeal ∈ S → ∃ b : Basis (Fin n) K V, Q.basisRepr b ∈ F := by
  let f := FractionalIdeal.spanSingleton (integerSubring K)⁰ ((2 : K) ^ n)
  obtain ⟨F, hF, hforms⟩ := exists_finite_forms_integral_scale n
    ((fun I ↦ f * I) '' S) (hS.image _)
  refine ⟨((fun P ↦ (2 : K)⁻¹ • P) '' F), hF.image _, ?_⟩
  intro V _ _ Q L hA hr hvol
  have hA2 : ((2 : K) • Q).Anisotropic := by
    intro x hx
    exact hA x ((mul_eq_zero.mp hx).resolve_left (by norm_num))
  have hv : (L.rescale 2).volumeIdeal ∈ (fun I ↦ f * I) '' S := by
    refine ⟨L.volumeIdeal, hvol, ?_⟩
    rw [L.volumeIdeal_rescale, hr]
    rfl
  obtain ⟨b, hb⟩ := hforms V ((2 : K) • Q) (L.rescale 2) hA2 hr
    L.doubled_scaleIdeal_le_one hv
  refine ⟨b, ((2 : K) • Q).basisRepr b, hb, ?_⟩
  ext x
  simp [QuadraticMap.basisRepr_apply, smul_eq_mul]

end NormEuclidean.AmbientVolumeInduction
