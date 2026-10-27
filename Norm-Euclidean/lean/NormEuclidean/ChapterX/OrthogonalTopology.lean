import NormEuclidean.ProperSpinor
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Instances.Matrix

/-!
# Local orthogonal topology for O'Meara Chapter X

The endomorphism algebra has its finite-dimensional module topology. Linear
automorphisms inherit the unit-group topology through the actual equivalence
with invertible endomorphisms. The existing ambient and proper orthogonal
groups therefore retain their algebraic definitions and acquire subgroup
topologies. Instances are scoped to this file's namespace.
-/

noncomputable section

namespace NormEuclidean.OrthogonalTopology

open Filter Topology ProperSpinor

variable {F E : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [AddCommGroup E] [Module F E] [Module.Finite F E]

scoped instance endTopology : TopologicalSpace (Module.End F E) :=
  moduleTopology F (Module.End F E)

open scoped NormEuclidean.OrthogonalTopology

scoped instance endTopologicalRing : IsTopologicalRing (Module.End F E) :=
  IsModuleTopology.isTopologicalRing F (Module.End F E)

scoped instance matrixModuleTopology {ι κ : Type*} [Finite ι] [Finite κ] :
    IsModuleTopology F (Matrix ι κ F) := by
  change IsModuleTopology F (ι → κ → F)
  infer_instance

scoped instance automorphismTopology : TopologicalSpace (E ≃ₗ[F] E) :=
  TopologicalSpace.induced LinearMap.GeneralLinearGroup.ofLinearEquiv inferInstance

omit [IsTopologicalRing F] [Module.Finite F E] in
theorem continuous_automorphismUnits :
    Continuous (LinearMap.GeneralLinearGroup.ofLinearEquiv :
      (E ≃ₗ[F] E) → (Module.End F E)ˣ) := continuous_induced_dom

scoped instance automorphismTopologicalGroup : IsTopologicalGroup (E ≃ₗ[F] E) :=
  topologicalGroup_induced
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F E).symm.toMonoidHom

omit [IsTopologicalRing F] [Module.Finite F E] in
theorem continuous_automorphismLinearMap :
    Continuous (fun g : E ≃ₗ[F] E ↦ g.toLinearMap) :=
  Units.continuous_val.comp continuous_automorphismUnits

variable [TopologicalSpace E] [IsModuleTopology F E]

def evaluationLinear (x : E) : Module.End F E →ₗ[F] E where
  toFun g := g x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalRing F] [Module.Finite F E] in
theorem continuous_automorphism_apply (x : E) :
    Continuous (fun g : E ≃ₗ[F] E ↦ g x) := by
  letI := IsModuleTopology.topologicalAddGroup F E
  exact (IsModuleTopology.continuous_of_linearMap (evaluationLinear x)).comp
    continuous_automorphismLinearMap

omit [IsTopologicalRing F] [Module.Finite F E] in
theorem continuous_ambient_apply (Q : QuadraticForm F E) (x : E) :
    Continuous (fun g : ambientGroup Q ↦ g.1 x) :=
  (continuous_automorphism_apply x).comp continuous_subtype_val

omit [IsTopologicalRing F] [Module.Finite F E] in
theorem continuous_proper_apply (Q : QuadraticForm F E) (x : E) :
    Continuous (fun g : properGroup Q ↦ g.1.1 x) :=
  (continuous_ambient_apply Q x).comp continuous_subtype_val

/-- Coordinates in any finite basis give the usual product topology. -/
def basisHomeomorph {ι : Type*} [Finite ι] (b : Module.Basis ι F E) : E ≃ₜ (ι → F) := by
  letI := IsModuleTopology.topologicalAddGroup F E
  exact {
    toEquiv := b.equivFun.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }

/-- Endomorphism coordinates agree with the finite matrix product topology. -/
def endMatrixHomeomorph {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F E) : Module.End F E ≃ₜ Matrix ι ι F := {
  toEquiv := (LinearMap.toMatrixAlgEquiv b).toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    (LinearMap.toMatrixAlgEquiv b).toLinearEquiv.toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    (LinearMap.toMatrixAlgEquiv b).symm.toLinearEquiv.toLinearMap }

omit [TopologicalSpace E] [IsModuleTopology F E] in
/-- Over a topological field, the unit-group topology on automorphisms is
already determined by the forward endomorphism coordinates. -/
theorem continuous_automorphism_iff_linearMap [ContinuousInv₀ F]
    {X : Type*} [TopologicalSpace X] (f : X → E ≃ₗ[F] E) :
    Continuous f ↔ Continuous (fun x ↦ (f x).toLinearMap) := by
  classical
  constructor
  · exact fun h ↦ continuous_automorphismLinearMap.comp h
  · intro hf
    let b := Module.Free.chooseBasis F E
    let e := LinearMap.toMatrixAlgEquiv b
    have hm : Continuous (fun x ↦ e (f x).toLinearMap) :=
      (endMatrixHomeomorph b).continuous.comp hf
    have hi : Continuous (fun x ↦ (e (f x).toLinearMap)⁻¹) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      have hu : IsUnit (e (f x).toLinearMap) :=
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (f x)).isUnit.map e.toRingHom
      have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
      apply (continuousAt_matrix_inv _ ?_).comp hm.continuousAt
      have hr : (Ring.inverse : F → F) = Inv.inv := funext Ring.inverse_eq_inv
      rw [hr]
      exact continuousAt_inv₀ hd.ne_zero
    have heq (x : X) : e (f x).symm.toLinearMap = (e (f x).toLinearMap)⁻¹ := by
      let u := Units.map e.toMonoidHom (LinearMap.GeneralLinearGroup.ofLinearEquiv (f x))
      exact Matrix.coe_units_inv u
    have hinv : Continuous (fun x ↦ (f x).symm.toLinearMap) := by
      have h := (endMatrixHomeomorph b).symm.continuous.comp hi
      change Continuous (fun x ↦ e.symm ((e (f x).toLinearMap)⁻¹)) at h
      simpa only [← heq, AlgEquiv.symm_apply_apply] using h
    apply continuous_induced_rng.mpr
    exact Units.continuous_iff.mpr ⟨hf, hinv⟩

omit [TopologicalSpace E] [IsModuleTopology F E] in
/-- The automorphism topology is exactly the topology induced by its forward
matrix coordinates, rather than a stronger condition on two independent maps. -/
theorem isInducing_automorphismLinearMap [ContinuousInv₀ F] :
    Topology.IsInducing (fun g : E ≃ₗ[F] E ↦ g.toLinearMap) := by
  refine ⟨le_antisymm (continuous_iff_le_induced.mp continuous_automorphismLinearMap) ?_⟩
  let T := TopologicalSpace.induced (fun g : E ≃ₗ[F] E ↦ g.toLinearMap) endTopology
  have h : @Continuous (E ≃ₗ[F] E) (E ≃ₗ[F] E) T automorphismTopology id := by
    letI : TopologicalSpace (E ≃ₗ[F] E) := T
    exact (continuous_automorphism_iff_linearMap (fun g : E ≃ₗ[F] E ↦ g)).mpr
      continuous_induced_dom
  simpa only [induced_id] using continuous_iff_le_induced.mp h

omit [TopologicalSpace E] [IsModuleTopology F E] in
theorem isInducing_ambientLinearMap [ContinuousInv₀ F] (Q : QuadraticForm F E) :
    Topology.IsInducing (fun g : ambientGroup Q ↦ g.1.toLinearMap) :=
  isInducing_automorphismLinearMap.comp Topology.IsInducing.subtypeVal

omit [TopologicalSpace E] [IsModuleTopology F E] in
theorem isInducing_properLinearMap [ContinuousInv₀ F] (Q : QuadraticForm F E) :
    Topology.IsInducing (fun g : properGroup Q ↦ g.1.1.toLinearMap) :=
  (isInducing_ambientLinearMap Q).comp Topology.IsInducing.subtypeVal

/-- Continuity of an endomorphism-valued family can be tested on a finite basis. -/
theorem continuous_end_iff_apply {X : Type*} [TopologicalSpace X]
    (f : X → Module.End F E) :
    Continuous f ↔ ∀ x : E, Continuous (fun t ↦ f t x) := by
  letI := IsModuleTopology.topologicalAddGroup F E
  constructor
  · intro hf x
    exact (IsModuleTopology.continuous_of_linearMap (evaluationLinear x)).comp hf
  · intro hf
    let b := Module.Free.chooseBasis F E
    have hc := (IsModuleTopology.continuous_of_linearMap (b.constr F).toLinearMap).comp
      (continuous_pi fun i ↦ hf (b i))
    simpa only [Function.comp_def, LinearEquiv.coe_coe, Module.Basis.constr_self] using hc

/-- An open coefficient subring makes every full submodule open in the
finite-dimensional ambient module topology. Finite generation is not needed here. -/
theorem isOpen_of_full (R : Subring F) (hR : IsOpen (R : Set F))
    (L : Submodule R E) (hL : Submodule.span F (L : Set E) = ⊤) :
    IsOpen (L : Set E) := by
  classical
  letI := IsModuleTopology.topologicalAddGroup F E
  let hspan : (⊤ : Submodule F E) ≤ Submodule.span F (L : Set E) := by rw [hL]
  let b := Module.Basis.ofSpan hspan
  let ι := (linearIndepOn_empty F id).extend (Set.empty_subset (L : Set E))
  letI := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite _
  let U : Set (ι → F) := {a | ∀ i, a i ∈ R}
  have hU : IsOpen U := by
    have h := isOpen_set_pi (Set.finite_univ : (Set.univ : Set ι).Finite)
      (fun _ _ ↦ hR)
    simpa [U, Set.pi] using h
  have he : IsOpenMap b.equivFun.symm :=
    IsModuleTopology.isOpenMap_of_surjective b.equivFun.symm.surjective
  have hzero : (0 : E) ∈ b.equivFun.symm '' U :=
    ⟨0, fun _ ↦ R.zero_mem, map_zero _⟩
  apply AddSubgroup.isOpen_of_mem_nhds L.toAddSubgroup
  apply Filter.mem_of_superset ((he _ hU).mem_nhds hzero)
  rintro _ ⟨a, ha, rfl⟩
  rw [Module.Basis.equivFun_symm_apply]
  apply L.sum_mem
  intro i _
  exact L.smul_mem (⟨a i, ha i⟩ : R) (Module.Basis.ofSpan_subset hspan ⟨i, rfl⟩)

/-- The quadratic form is continuous in the finite-dimensional module topology. -/
theorem continuous_quadratic [Invertible (2 : F)] (Q : QuadraticForm F E) :
    Continuous Q := by
  letI := IsModuleTopology.topologicalAddGroup F E
  have h := (IsModuleTopology.continuous_bilinear_of_finite_left
    (QuadraticMap.associatedHom F Q)).comp (continuous_id.prodMk continuous_id)
  simpa only [Function.comp_def, id_eq, QuadraticMap.associated_eq_self_apply] using h

/-- O'Meara 101:2: the reflecting vectors form an open subset. -/
theorem isOpen_reflectingVectors [Invertible (2 : F)] (Q : QuadraticForm F E)
    [T1Space F] : IsOpen {x : E | Q x ≠ 0} :=
  (isOpen_ne (x := (0 : F))).preimage (continuous_quadratic Q)

/-- O'Meara 101:2 for the actual ambient linear reflection. -/
theorem continuous_reflection [Invertible (2 : F)] [ContinuousInv₀ F]
    (Q : QuadraticForm F E) :
    Continuous (fun x : {x : E // Q x ≠ 0} ↦
      IntegralReflection.linearEquiv Q x.1 x.2) := by
  letI := IsModuleTopology.topologicalAddGroup F E
  have hlin : Continuous (fun x : {x : E // Q x ≠ 0} ↦
      (IntegralReflection.linearEquiv Q x.1 x.2).toLinearMap) := by
    apply (continuous_end_iff_apply _).mpr
    intro y
    change Continuous (fun x : {x : E // Q x ≠ 0} ↦
      y - ((Q x.1)⁻¹ * Q.polarBilin x.1 y) • x.1)
    have hq : Continuous (fun x : {x : E // Q x ≠ 0} ↦ Q x.1) :=
      (continuous_quadratic Q).comp continuous_subtype_val
    have hp : Continuous (fun x : {x : E // Q x ≠ 0} ↦ Q.polarBilin x.1 y) :=
      (IsModuleTopology.continuous_of_linearMap (Q.polarBilin.flip y)).comp
      continuous_subtype_val
    exact (continuous_const : Continuous (fun _ : {x : E // Q x ≠ 0} ↦ y)).sub
      ((hq.inv₀ (fun x ↦ x.2)).mul hp |>.smul continuous_subtype_val)
  apply continuous_induced_rng.mpr
  apply Units.continuous_iff.mpr
  constructor
  · exact hlin
  · change Continuous (fun x : {x : E // Q x ≠ 0} ↦
      (IntegralReflection.linearEquiv Q x.1 x.2).symm.toLinearMap)
    simpa only [IntegralReflection.linearEquiv, Module.reflection_symm] using hlin

omit [TopologicalSpace F] [IsTopologicalRing F] [Module.Finite F E]
  [TopologicalSpace E] [IsModuleTopology F E] in
private theorem mapsTo_of_generators {R : Subring F} (L : Submodule R E)
    (s : Finset E) (hs : Submodule.span R (s : Set E) = L) (g : E ≃ₗ[F] E)
    (hg : ∀ x ∈ s, g x ∈ L) : ∀ x ∈ L, g x ∈ L := by
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hg x hx
  | zero => simpa only [map_zero] using L.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using L.add_mem hx hy
  | smul a x _ hx =>
      simpa only [Subring.smul_def, map_smul] using L.smul_mem a hx

/-- O'Meara 101:4(ii): a finitely generated open lattice has an open integral
orthogonal stabilizer. Both directions are checked on actual generators. -/
theorem isOpen_integralStabilizer (Q : QuadraticForm F E) {R : Subring F}
    (L : Submodule R E) (hfg : L.FG) (hopen : IsOpen (L : Set E)) :
    IsOpen (integralStabilizer Q L : Set (ambientGroup Q)) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  have hgen (x : E) (hx : x ∈ s) : x ∈ L := by
    rw [← hs]
    exact Submodule.subset_span hx
  have hiff (g : ambientGroup Q) :
      g ∈ integralStabilizer Q L ↔
        ∀ x ∈ s, g.1 x ∈ L ∧ (g⁻¹).1 x ∈ L := by
    constructor
    · intro hg x hx
      refine ⟨(hg x).mpr (hgen x hx), ?_⟩
      exact (hg (g.1.symm x)).mp (by
        simpa only [LinearEquiv.apply_symm_apply] using (hgen x hx))
    · intro hg x
      have hf := mapsTo_of_generators L s hs g.1 (fun x hx ↦ (hg x hx).1)
      have hi := mapsTo_of_generators L s hs (g⁻¹).1 (fun x hx ↦ (hg x hx).2)
      exact ⟨fun hx ↦ by simpa only [Subgroup.coe_inv, LinearEquiv.coe_inv,
        LinearEquiv.symm_apply_apply] using hi (g.1 x) hx, hf x⟩
  have hset : (integralStabilizer Q L : Set (ambientGroup Q)) =
      ⋂ x ∈ (s : Set E), {g : ambientGroup Q | g.1 x ∈ L ∧ (g⁻¹).1 x ∈ L} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_coe]
    exact hiff g
  rw [hset]
  apply s.finite_toSet.isOpen_biInter
  intro x _
  exact (hopen.preimage (continuous_ambient_apply Q x)).inter
    (hopen.preimage ((continuous_ambient_apply Q x).comp continuous_inv))

end NormEuclidean.OrthogonalTopology
