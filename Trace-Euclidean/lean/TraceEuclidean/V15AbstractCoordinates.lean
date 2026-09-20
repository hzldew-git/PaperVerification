import TraceEuclidean.GlobalLatticeClass
import TraceEuclidean.V15RankOneIdealBridge
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
Coordinate transport for a lattice on an arbitrary finite-dimensional space
over an already coded totally real number field.  A choice of field basis is
used only to obtain the canonical `Fin n → F` ambient space.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

/-- Every number field has a code inside the fixed algebraic closure; this
records the field-level part of the varying-field representation. -/
theorem v15_number_field_has_code (F : Type*) [Field F] [NumberField F] :
    ∃ C : CodedNumberField, Nonempty (F ≃ₐ[ℚ] C.1) := by
  let f : F →ₐ[ℚ] UniversalNumberFieldAmbient := IsAlgClosed.lift
  haveI : FiniteDimensional ℚ f.fieldRange := f.toLinearMap.finiteDimensional_range
  exact ⟨⟨f.fieldRange, inferInstance⟩, ⟨f.equivFieldRange⟩⟩

/-- The field code of a totally real number field is totally real.  The
isomorphism also identifies integer rings and preserves the rational trace. -/
theorem v15_totally_real_field_code
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F] :
    ∃ C : CodedNumberField, ∃ e : F ≃ₐ[ℚ] C.1,
      NumberField.IsTotallyReal C.1 ∧
      (∀ a : 𝓞 F,
        ((NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv a : 𝓞 C.1) : C.1) =
          e (a : F)) ∧
      (∀ x : F, Algebra.trace ℚ C.1 (e x) = Algebra.trace ℚ F x) := by
  obtain ⟨C, ⟨e⟩⟩ := v15_number_field_has_code F
  refine ⟨C, e, NumberField.IsTotallyReal.ofRingEquiv e.toRingEquiv, ?_, ?_⟩
  · intro a
    exact NumberField.RingOfIntegers.mapRingEquiv_apply e.toRingEquiv a
  · intro x
    exact Algebra.trace_eq_of_algEquiv e x

namespace NumberFieldLattice

variable (C : CodedNumberField) [NumberField.IsTotallyReal C.1]
variable {V : Type*} [AddCommGroup V] [Module C.1 V]
variable [Module (𝓞 C.1) V] [IsScalarTower (𝓞 C.1) C.1 V]
variable [FiniteDimensional C.1 V]

/-- The linear coordinate map given by a chosen field basis. -/
def v15CoordinateEquiv (_M : NumberFieldLattice (F := C.1) (V := V)) :
    V ≃ₗ[C.1] (Fin (Module.finrank C.1 V) → C.1) :=
  (Module.finBasis C.1 V).equivFun

/-- The image of the original integer lattice under the coordinate map. -/
def v15CoordinateLattice (M : NumberFieldLattice (F := C.1) (V := V)) :
    Submodule (𝓞 C.1) (Fin (Module.finrank C.1 V) → C.1) :=
  M.L.map ((M.v15CoordinateEquiv C).toLinearMap.restrictScalars (𝓞 C.1))

/-- The quadratic form expressed in the same coordinates. -/
def v15CoordinateForm (M : NumberFieldLattice (F := C.1) (V := V)) :
    QuadraticForm C.1 (Fin (Module.finrank C.1 V) → C.1) :=
  M.Q.comp (M.v15CoordinateEquiv C).symm.toLinearMap

/-- Coordinate transport preserves lattice membership and quadratic values. -/
theorem v15CoordinateData (M : NumberFieldLattice (F := C.1) (V := V)) :
    (∀ x : V, x ∈ M.L ↔ M.v15CoordinateEquiv C x ∈ M.v15CoordinateLattice C) ∧
    (∀ x : V, M.v15CoordinateForm C (M.v15CoordinateEquiv C x) = M.Q x) := by
  constructor
  · intro x
    simp [v15CoordinateLattice, Submodule.mem_map, v15CoordinateEquiv]
  · intro x
    simp [v15CoordinateForm]

/-- The transported integer submodule is still a full lattice. -/
theorem v15CoordinateLattice_full (M : NumberFieldLattice (F := C.1) (V := V)) :
    (M.v15CoordinateLattice C).IsLattice C.1 := by
  let e := M.v15CoordinateEquiv C
  let eR := e.toLinearMap.restrictScalars (𝓞 C.1)
  have hfg : (M.v15CoordinateLattice C).FG := by
    exact M.full.fg.map eR
  refine ⟨hfg, ?_⟩
  change Submodule.span C.1 (e '' (M.L : Set V)) = ⊤
  have hspan : Submodule.span C.1 (e '' (M.L : Set V)) =
      (Submodule.span C.1 (M.L : Set V)).map e.toLinearMap := by
    simpa using (Submodule.span_image (f := e.toLinearMap) (s := (M.L : Set V)))
  rw [hspan]
  change (Submodule.span C.1 (M.L : Set V)).map e.toLinearMap = ⊤
  rw [M.full.span_eq_top]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

/-- The transported form remains nondegenerate. -/
theorem v15CoordinateForm_nondegenerate
    (M : NumberFieldLattice (F := C.1) (V := V)) :
    (M.v15CoordinateForm C).Nondegenerate := by
  change (M.Q.basisRepr (Module.finBasis C.1 V)).Nondegenerate
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  have h := (M.Q.isometryEquivBasisRepr (Module.finBasis C.1 V)).map_radical
  simpa [M.nondegenerate.radical_eq_bot] using h.symm

/-- Every positive-rank abstract lattice over an already coded field has a
canonical coordinate presentation with no change to its quadratic data. -/
def v15CoordinatePresentation (M : NumberFieldLattice (F := C.1) (V := V))
    (hn : 0 < Module.finrank C.1 V) : GlobalLatticePresentation where
  field := C
  totallyReal := inferInstance
  rank := Module.finrank C.1 V
  rankPositive := hn
  Q := M.v15CoordinateForm C
  L := M.v15CoordinateLattice C
  full := M.v15CoordinateLattice_full C
  nondegenerate := M.v15CoordinateForm_nondegenerate C
  positiveDefinite := by
    intro x hx σ
    let e := M.v15CoordinateEquiv C
    have hv : e.symm x ≠ 0 := by
      intro hzero
      apply hx
      have h := congrArg e hzero
      simpa [e] using h
    simpa [v15CoordinateForm, e] using M.positiveDefinite (e.symm x) hv σ
  integral := by
    intro x
    obtain ⟨v, hv, heq⟩ := (Submodule.mem_map).mp x.2
    have hint := M.integral ⟨v, hv⟩
    have hQ : M.v15CoordinateForm C x.1 = M.Q v := by
      have hdata := (M.v15CoordinateData C).2 v
      simpa [v15CoordinateLattice, v15CoordinateEquiv] using heq ▸ hdata
    change IsIntegral ℤ (M.v15CoordinateForm C x.1)
    rw [hQ]
    exact hint

/-- The original abstract lattice is actually isometric to its coordinate
presentation, with the identity field map. -/
def v15CoordinateIsometry (M : NumberFieldLattice (F := C.1) (V := V))
    (hn : 0 < Module.finrank C.1 V) :
    NumberFieldLatticeEquiv M (M.v15CoordinatePresentation C hn).toNumberFieldLattice where
  fieldEquiv := RingEquiv.refl C.1
  spaceEquiv := (M.v15CoordinateEquiv C).toAddEquiv
  map_smul := by
    intro a x
    exact (M.v15CoordinateEquiv C).map_smul a x
  mapsLattice := (M.v15CoordinateData C).1
  mapQuadratic := (M.v15CoordinateData C).2

/-- Strict trace Euclideanity is equivalent on the abstract lattice and its
coordinate presentation at every real threshold. -/
theorem v15CoordinateTrace_iff (M : NumberFieldLattice (F := C.1) (V := V))
    (hn : 0 < Module.finrank C.1 V) (t : ℝ) :
    (M.v15CoordinatePresentation C hn).IsTraceEuclidean t ↔
      M.IsTraceEuclidean t := by
  change (∀ x : Fin (Module.finrank C.1 V) → C.1,
      ∃ y : M.v15CoordinateLattice C,
        ((Algebra.trace ℚ C.1 (M.v15CoordinateForm C (x - y.1)) : ℚ) : ℝ) < t) ↔
      M.IsTraceEuclidean t
  let e := M.v15CoordinateEquiv C
  have hdata := M.v15CoordinateData C
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h (e x)
    let z : M.L := ⟨e.symm y.1, by
      apply (hdata.1 (e.symm y.1)).mpr
      simpa [e] using y.2⟩
    refine ⟨z, ?_⟩
    have hQ : M.v15CoordinateForm C (e x - y.1) =
        M.Q (x - z.1) := by
      have heq : e (x - z.1) = e x - y.1 := by simp [z]
      rw [← heq]
      exact hdata.2 (x - z.1)
    change ((Algebra.trace ℚ C.1 (M.Q (x - z.1)) : ℚ) : ℝ) < t
    rw [← hQ]
    exact hy
  · intro h x
    obtain ⟨z, hz⟩ := h (e.symm x)
    let y : M.v15CoordinateLattice C :=
      ⟨e z.1, (hdata.1 z.1).mp z.2⟩
    refine ⟨y, ?_⟩
    have hQ : M.v15CoordinateForm C (x - y.1) =
        M.Q (e.symm x - z.1) := by
      have heq : e (e.symm x - z.1) = x - y.1 := by simp [y]
      rw [← heq]
      exact hdata.2 (e.symm x - z.1)
    change ((Algebra.trace ℚ C.1 (M.v15CoordinateForm C (x - y.1)) : ℚ) : ℝ) < t
    rw [hQ]
    exact hz

/-- The associated bilinear value is unchanged by coordinate transport. -/
theorem v15CoordinateAssociated (M : NumberFieldLattice (F := C.1) (V := V))
    (x y : V) :
    QuadraticMap.associated (M.v15CoordinateForm C)
        (M.v15CoordinateEquiv C x) (M.v15CoordinateEquiv C y) =
      QuadraticMap.associated M.Q x y := by
  simp only [QuadraticMap.associated_apply]
  rw [← (M.v15CoordinateEquiv C).map_add]
  simp only [(M.v15CoordinateData C).2]

/-- Classic integrality is also equivalent before and after coordinates. -/
theorem v15CoordinateClassic_iff (M : NumberFieldLattice (F := C.1) (V := V))
    (hn : 0 < Module.finrank C.1 V) :
    (M.v15CoordinatePresentation C hn).IsClassicIntegral ↔
      M.IsClassicIntegral := by
  change (∀ x y : M.v15CoordinateLattice C,
      IsIntegral ℤ (QuadraticMap.associated (M.v15CoordinateForm C) x.1 y.1)) ↔
      (∀ x y : M.L, IsIntegral ℤ (QuadraticMap.associated M.Q x.1 y.1))
  let e := M.v15CoordinateEquiv C
  have hmem := (M.v15CoordinateData C).1
  constructor
  · intro h x y
    let x' : (M.v15CoordinatePresentation C hn).L := ⟨e x.1, (hmem x.1).mp x.2⟩
    let y' : (M.v15CoordinatePresentation C hn).L := ⟨e y.1, (hmem y.1).mp y.2⟩
    have hxy := h x' y'
    change IsIntegral ℤ (QuadraticMap.associated M.Q x.1 y.1)
    rw [← M.v15CoordinateAssociated C x.1 y.1]
    exact hxy
  · intro h x y
    let x' : M.L := ⟨e.symm x.1, by
      apply (hmem (e.symm x.1)).mpr
      simpa [e] using x.2⟩
    let y' : M.L := ⟨e.symm y.1, by
      apply (hmem (e.symm y.1)).mpr
      simpa [e] using y.2⟩
    have hxy := h x' y'
    have hassoc := M.v15CoordinateAssociated C (e.symm x.1) (e.symm y.1)
    change QuadraticMap.associated (M.v15CoordinateForm C)
        (e (e.symm x.1)) (e (e.symm y.1)) =
      QuadraticMap.associated M.Q (e.symm x.1) (e.symm y.1) at hassoc
    simp only [LinearEquiv.apply_symm_apply] at hassoc
    rw [hassoc]
    exact hxy

/-- Every positive-rank abstract lattice over an already coded field is
represented by an actual canonical-coordinate lattice.  The two integrality
and trace predicates used in the main finiteness results are preserved. -/
theorem v15AbstractToCanonical
    (M : NumberFieldLattice (F := C.1) (V := V))
    (hn : 0 < Module.finrank C.1 V) :
    ∃ P : GlobalLatticePresentation,
      P.field = C ∧ P.rank = Module.finrank C.1 V ∧
      Nonempty (NumberFieldLatticeEquiv M P.toNumberFieldLattice) ∧
      (P.IsTraceEuclidean (P.degree : ℝ) ↔
        M.IsTraceEuclidean (M.degree : ℝ)) ∧
      (P.IsClassicIntegral ↔ M.IsClassicIntegral) := by
  let P := M.v15CoordinatePresentation C hn
  refine ⟨P, rfl, rfl, ⟨M.v15CoordinateIsometry C hn⟩, ?_, ?_⟩
  · exact M.v15CoordinateTrace_iff C hn P.degree
  · exact M.v15CoordinateClassic_iff C hn

/-- An arbitrary positive rank-one lattice over a coded totally real field
has the fractional-ideal description, with the same trace threshold. -/
theorem v15AbstractRankOneIdealBridge
    (M : NumberFieldLattice (F := C.1) (V := V))
    (hrank : Module.finrank C.1 V = 1) (t : ℝ) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (𝓞 C.1)) C.1) (α : C.1),
      I ≠ 0 ∧
      (∀ x : V, x ∈ M.L ↔
        (M.v15CoordinateEquiv C x) ⟨0, by omega⟩ ∈ I) ∧
      (∀ x : V, M.Q x = α *
        ((M.v15CoordinateEquiv C x) ⟨0, by omega⟩) ^ 2) ∧
      (∀ σ : C.1 →+* ℝ, 0 < σ α) ∧
      v15ValueFractionalIdeal I α ≤ 1 ∧
      (M.IsTraceEuclidean t ↔ GlobalLatticePresentation.V15IdealTraceEuclideanAt I α t) := by
  let P := M.v15CoordinatePresentation C (hrank ▸ Nat.zero_lt_one)
  have hPrank : P.rank = 1 := hrank
  obtain ⟨I, α, hI, hmem, hQ, hpos, hint, hE⟩ := P.rankOne_ideal_bridge_at hPrank t
  refine ⟨I, α, hI, ?_, ?_, hpos, hint, ?_⟩
  · intro x
    exact ((M.v15CoordinateData C).1 x).trans (hmem (M.v15CoordinateEquiv C x))
  · intro x
    exact ((M.v15CoordinateData C).2 x).symm.trans (hQ (M.v15CoordinateEquiv C x))
  · exact (M.v15CoordinateTrace_iff C (hrank ▸ Nat.zero_lt_one) t).symm.trans hE

end NumberFieldLattice

end

end TraceEuclidean
