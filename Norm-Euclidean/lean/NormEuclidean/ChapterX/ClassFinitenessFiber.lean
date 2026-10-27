import NormEuclidean.ChapterX.ProjectedComplement
import NormEuclidean.ChapterX.ModuleGenusPatching

/-!
# Finite class fibers in the 103:4 induction

Fix a represented nonzero value and one class of projected complements.
Actual orthogonal lifts normalize the split submodule. The original lattices
then lie in a common finite module interval after global isometry.
The bounded-value and bounded-volume induction inputs remain separate.
-/

noncomputable section

namespace NormEuclidean.ClassFinitenessFiber

open Module ProjectedComplement ProperSpinor AdelicApproximation
open Bong.QuadraticSpace

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- A complement isometry extends to an actual ambient isometry fixing the
represented vector. The orthogonal decomposition and extension are constructed. -/
theorem exists_ambient_lift_fixing_vector (hQ : Q.polarBilin.Nondegenerate)
    (y : V) (hy0 : Q y ≠ 0)
    (e : (Q.comp (complement Q y).subtype).IsometryEquiv
      (Q.comp (complement Q y).subtype)) :
    ∃ g : ambientGroup Q, g.1 y = y ∧
      ∀ u : complement Q y, g.1 (u : V) = (e u : V) := by
  let q := SpinorBridge.quadraticSpace Q hQ
  let S := K ∙ y
  have hyy : q.bilin y y ≠ 0 := by
    change q.quadratic y ≠ 0
    simpa only [q, SpinorBridge.quadraticSpace_quadratic] using hy0
  have hcompl := LinearMap.BilinForm.isCompl_span_singleton_orthogonal hyy
  have hS : (q.bilin.restrict S).Nondegenerate :=
    q.bilin.nondegenerate_restrict_of_disjoint_orthogonal q.isSymm.isRefl hcompl.disjoint
  let d := WittExtension.decompositionIsometry q S hS
  have htail (u v : complement Q y) :
      halfPolar (Q.comp (complement Q y).subtype) (e u) (e v) =
        halfPolar (Q.comp (complement Q y).subtype) u v := by
    simp only [halfPolar_apply, QuadraticMap.polar]
    rw [← map_add e, e.map_app, e.map_app, e.map_app]
  let tail : Isometry (WittExtension.complementarySpace q S hS)
      (WittExtension.complementarySpace q S hS) :=
    { toLinearEquiv := e.toLinearEquiv
      map_bilin := by
        intro u v
        change halfPolar (Q.comp (complement Q y).subtype) (e u) (e v) =
          halfPolar (Q.comp (complement Q y).subtype) u v
        exact htail u v }
  let h := (d.symm.trans
    ((Isometry.refl (WittExtension.restrictedSpace q S hS)).fieldOrthogonalSum tail)).trans d
  let g : ambientGroup Q := ⟨h.toLinearEquiv, fun x ↦ by
    simpa only [q, SpinorBridge.quadraticSpace_quadratic] using h.map_quadratic x⟩
  have hc := q.bilin.isCompl_orthogonal_of_restrict_nondegenerate q.isSymm.isRefl hS
  have hline (x : S) : g.1 (x : V) = (x : V) := by
    change (Submodule.prodEquivOfIsCompl S (q.bilin.orthogonal S) hc)
      (((Submodule.prodEquivOfIsCompl S (q.bilin.orthogonal S) hc).symm x).1,
        tail.toLinearEquiv
          ((Submodule.prodEquivOfIsCompl S (q.bilin.orthogonal S) hc).symm x).2) = x.1
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp only [map_zero, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, add_zero]
  refine ⟨g, hline ⟨y, Submodule.subset_span (Set.mem_singleton y)⟩, ?_⟩
  intro u
  change (Submodule.prodEquivOfIsCompl S (q.bilin.orthogonal S) hc)
    (((Submodule.prodEquivOfIsCompl S (q.bilin.orthogonal S) hc).symm u).1,
      e.toLinearEquiv
        ((Submodule.prodEquivOfIsCompl S (q.bilin.orthogonal S) hc).symm u).2) = (e u : V)
  rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
  simp only [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, zero_add]
  rfl

/-- A lifted complement comparison identifies the two actual split submodules. -/
theorem map_splitCarrier_eq (L₀ L : Lattice (integerSubring K) Q) (y : V)
    (hy₀ : y ∈ L₀.carrier) (hs₀ : L₀.scaleIdeal ≤ 1)
    (hy : y ∈ L.carrier) (hs : L.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0)
    (e : LatticeIsometry (Q.comp (complement Q y).subtype)
      (Q.comp (complement Q y).subtype)
      (projectedLattice Q L y hy hs hy0).carrier
      (projectedLattice Q L₀ y hy₀ hs₀ hy0).carrier)
    (g : ambientGroup Q) (hgy : g.1 y = y)
    (hgu : ∀ u : complement Q y, g.1 (u : V) = (e.toLinearEquiv u : V)) :
    (splitCarrier Q L y).map (g.1.toLinearMap.restrictScalars (integerSubring K)) =
      splitCarrier Q L₀ y := by
  have hspan : (Submodule.span (integerSubring K) {y}).map
      (g.1.toLinearMap.restrictScalars (integerSubring K)) =
      Submodule.span (integerSubring K) {y} := by
    rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span (integerSubring K) {g.1 y} = _
    rw [hgy]
  have hemap : (projectedCarrier Q L y).map
      (e.toLinearEquiv.toLinearMap.restrictScalars (integerSubring K)) =
      projectedCarrier Q L₀ y := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (e.mem_iff v).mpr hv
    · intro hu
      refine ⟨e.toLinearEquiv.symm u, ?_, e.toLinearEquiv.apply_symm_apply u⟩
      apply (e.mem_iff _).mp
      rw [LinearEquiv.apply_symm_apply]
      change u ∈ projectedCarrier Q L₀ y
      exact hu
  have hcomp : (g.1.toLinearMap.restrictScalars (integerSubring K)).comp
      ((complement Q y).subtype.restrictScalars (integerSubring K)) =
      ((complement Q y).subtype.restrictScalars (integerSubring K)).comp
        (e.toLinearEquiv.toLinearMap.restrictScalars (integerSubring K)) := by
    ext u
    exact hgu u
  rw [splitCarrier, Submodule.map_sup, hspan, ← Submodule.map_comp, hcomp,
    Submodule.map_comp, hemap]
  rfl

/-- Each projected-complement class fiber has finitely many ordinary global
classes. This is the finite-interval conclusion in the induction for 103:4. -/
theorem exists_finite_representatives_of_projected_class
    (hQ : Q.polarBilin.Nondegenerate) (L₀ : Lattice (integerSubring K) Q)
    (y : V) (hy₀ : y ∈ L₀.carrier) (hs₀ : L₀.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0) :
    ∃ A : Set (Lattice (integerSubring K) Q), A.Finite ∧
      ∀ (L : Lattice (integerSubring K) Q) (hy : y ∈ L.carrier) (hs : L.scaleIdeal ≤ 1),
        GloballyIsometric (Q.comp (complement Q y).subtype)
          (projectedLattice Q L y hy hs hy0) (projectedLattice Q L₀ y hy₀ hs₀ hy0) →
          ∃ N ∈ A, GloballyIsometric Q L N := by
  let N₀ := splitLattice Q L₀ y hy₀ hs₀ hy0
  let f : V →ₗ[integerSubring K] V :=
    (LinearMap.lsmul K V (Q y)⁻¹).restrictScalars (integerSubring K)
  let U := N₀.carrier.map f
  let A := {N : Lattice (integerSubring K) Q | N₀.carrier ≤ N.carrier ∧ N.carrier ≤ U}
  letI : Ring.HasFiniteQuotients (integerSubring K) :=
    inferInstanceAs (Ring.HasFiniteQuotients (NumberField.RingOfIntegers K))
  have hinterval : {P : Submodule (integerSubring K) V | N₀.carrier ≤ P ∧ P ≤ U}.Finite :=
    LatticeInterval.finite_interval_of_full (integerSubring K) N₀.carrier U N₀.full
      (N₀.finite.map f)
  have hA : A.Finite := by
    apply Set.Finite.of_injOn (f := fun N : Lattice (integerSubring K) Q ↦ N.carrier)
      (t := {P : Submodule (integerSubring K) V | N₀.carrier ≤ P ∧ P ≤ U})
    · intro N hN
      exact hN
    · intro N _ M _ h
      cases N
      cases M
      cases h
      rfl
    · exact hinterval
  refine ⟨A, hA, ?_⟩
  intro L hy hs hiso
  obtain ⟨e⟩ := hiso
  let eQ : (Q.comp (complement Q y).subtype).IsometryEquiv
      (Q.comp (complement Q y).subtype) :=
    { toLinearEquiv := e.toLinearEquiv
      map_app' := e.q_eq }
  obtain ⟨g, hgy, hgu⟩ := exists_ambient_lift_fixing_vector Q hQ y hy0 eQ
  have hmap := map_splitCarrier_eq Q L₀ L y hy₀ hs₀ hy hs hy0 e g hgy hgu
  let N := transportLattice Q g L
  have hlower : N₀.carrier ≤ N.carrier := by
    change splitCarrier Q L₀ y ≤ L.carrier.map _
    rw [← hmap]
    exact Submodule.map_mono (splitCarrier_le Q L y hy hs)
  have hscaled (x : V) (hx : x ∈ N.carrier) : Q y • x ∈ N₀.carrier := by
    obtain ⟨z, hz, rfl⟩ := hx
    change Q y • (g.1 z) ∈ N₀.carrier
    have hmem : g.1 (Q y • z) ∈ N₀.carrier := by
      change g.1 (Q y • z) ∈ splitCarrier Q L₀ y
      rw [← hmap]
      exact ⟨Q y • z, value_smul_mem_splitCarrier Q L y hy hs z hz, rfl⟩
    simpa only [map_smul] using hmem
  have hupper : N.carrier ≤ U := by
    intro x hx
    refine ⟨Q y • x, hscaled x hx, ?_⟩
    change (Q y)⁻¹ • (Q y • x) = x
    rw [smul_smul, inv_mul_cancel₀ hy0, one_smul]
  refine ⟨N, ⟨hlower, hupper⟩, ?_⟩
  exact ⟨{ toLinearEquiv := g.1
           q_eq := g.2
           mem_iff := mem_transportLattice Q g L }⟩

end NormEuclidean.ClassFinitenessFiber
