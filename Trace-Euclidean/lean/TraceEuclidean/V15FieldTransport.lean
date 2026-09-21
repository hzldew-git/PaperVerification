import TraceEuclidean.V15AbstractCoordinates
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
Transport of an abstract number-field lattice across a field isomorphism.  This
closes the field-level gap left by `V15AbstractCoordinates`: the source field
need not already be represented by a `CodedNumberField`.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

namespace NumberFieldLattice

variable {F V : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
variable [AddCommGroup V] [Module F V]
variable [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
variable [FiniteDimensional F V]
variable (C : CodedNumberField) [NumberField.IsTotallyReal C.1]

/-- Coordinates followed by a field isomorphism give an additive equivalence
from an arbitrary vector space to the canonical coordinate space. -/
def v15FieldCoordinateEquiv (e : F ≃ₐ[ℚ] C.1) :
    V ≃+ (Fin (Module.finrank F V) → C.1) where
  toFun x i := e ((Module.finBasis F V).equivFun x i)
  invFun z := (Module.finBasis F V).equivFun.symm (fun i ↦ e.symm (z i))
  left_inv x := by
    apply (Module.finBasis F V).equivFun.injective
    apply funext
    intro i
    simp
  right_inv z := by
    apply funext
    intro i
    change e (((Module.finBasis F V).equivFun
      ((Module.finBasis F V).equivFun.symm (fun j ↦ e.symm (z j)))) i) = z i
    rw [(Module.finBasis F V).equivFun.apply_symm_apply]
    exact e.apply_symm_apply (z i)
  map_add' x y := by
    apply funext
    intro i
    simp
/-- The coordinate equivalence is semilinear over the field isomorphism. -/
theorem v15FieldCoordinateEquiv_map_smul (e : F ≃ₐ[ℚ] C.1) (a : F) (x : V) :
    v15FieldCoordinateEquiv C e (a • x) =
      e a • v15FieldCoordinateEquiv C e x := by
  apply funext
  intro i
  simp [v15FieldCoordinateEquiv]

/-- The inverse coordinate equivalence is semilinear over the inverse field
isomorphism. -/
theorem v15FieldCoordinateEquiv_symm_map_smul
    (e : F ≃ₐ[ℚ] C.1) (a : C.1)
    (x : Fin (Module.finrank F V) → C.1) :
    (v15FieldCoordinateEquiv C e).symm (a • x) =
      e.symm a • (v15FieldCoordinateEquiv C e).symm x := by
  apply (v15FieldCoordinateEquiv C e).injective
  rw [(v15FieldCoordinateEquiv C e).apply_symm_apply,
    v15FieldCoordinateEquiv_map_smul]
  simp

/-- The additive coordinate equivalence as a field-semilinear map. -/
def v15FieldCoordinateMap (e : F ≃ₐ[ℚ] C.1) :
    V →ₛₗ[e.toRingEquiv.toRingHom] (Fin (Module.finrank F V) → C.1) where
  toFun := v15FieldCoordinateEquiv C e
  map_add' := (v15FieldCoordinateEquiv C e).map_add
  map_smul' a x := by
    exact v15FieldCoordinateEquiv_map_smul C e a x

/-- The same coordinate map, regarded as semilinear over the induced
isomorphism of rings of integers. -/
def v15FieldCoordinateIntegerMap (e : F ≃ₐ[ℚ] C.1) :
    V →ₛₗ[(NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv).toRingHom]
      (Fin (Module.finrank F V) → C.1) where
  toFun := v15FieldCoordinateEquiv C e
  map_add' := (v15FieldCoordinateEquiv C e).map_add
  map_smul' a x := by
    apply funext
    intro i
    change e ((Module.finBasis F V).equivFun (a • x) i) =
      ((NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv a : 𝓞 C.1) : C.1) *
        e ((Module.finBasis F V).equivFun x i)
    calc
      e ((Module.finBasis F V).equivFun (a • x) i) =
          e ((Module.finBasis F V).equivFun ((a : F) • x) i) := by
            rw [IsScalarTower.algebraMap_smul F a x]
      _ = e ((a : F) * (Module.finBasis F V).equivFun x i) := by
            rw [(Module.finBasis F V).equivFun.map_smul]
            rfl
      _ = e (a : F) * e ((Module.finBasis F V).equivFun x i) := e.map_mul _ _
      _ = ((NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv a : 𝓞 C.1) : C.1) *
          e ((Module.finBasis F V).equivFun x i) := by
            rw [NumberField.RingOfIntegers.mapRingEquiv_apply]
            simp only [AlgEquiv.coe_ringEquiv]

/-- The integer lattice transported to the coded field and canonical
coordinate space. -/
def v15FieldCoordinateLattice
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) :
    Submodule (𝓞 C.1) (Fin (Module.finrank F V) → C.1) := by
  letI : RingHomSurjective
      (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv).toRingHom :=
    ⟨(NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv).surjective⟩
  exact M.L.map (v15FieldCoordinateIntegerMap C e)

/-- Membership in the transported lattice is exactly membership before
transport. -/
theorem v15FieldCoordinateLattice_mem_iff
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) (x : V) :
    x ∈ M.L ↔
      v15FieldCoordinateEquiv C e x ∈ M.v15FieldCoordinateLattice C e := by
  letI : RingHomSurjective
      (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv).toRingHom :=
    ⟨(NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv).surjective⟩
  constructor
  · intro hx
    exact Submodule.mem_map_of_mem hx
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (Submodule.mem_map).mp hx
    have hyx : y = x := (v15FieldCoordinateEquiv C e).injective hxy
    simpa [hyx] using hy

/-- Transport along a number-field isomorphism preserves the full-lattice
condition. -/
theorem v15FieldCoordinateLattice_full
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) :
    (M.v15FieldCoordinateLattice C e).IsLattice C.1 := by
  letI : RingHomSurjective
      (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv).toRingHom :=
    ⟨(NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv).surjective⟩
  letI : RingHomSurjective e.toRingEquiv.toRingHom := ⟨e.surjective⟩
  constructor
  · exact M.full.fg.map (v15FieldCoordinateIntegerMap C e)
  · change Submodule.span C.1
      ((v15FieldCoordinateEquiv C e) '' (M.L : Set V)) = ⊤
    calc
      Submodule.span C.1 ((v15FieldCoordinateEquiv C e) '' (M.L : Set V)) =
          (Submodule.span F (M.L : Set V)).map (v15FieldCoordinateMap C e) := by
            have hspan :=
              Submodule.span_image (s := (M.L : Set V)) (v15FieldCoordinateMap C e)
            change Submodule.span C.1
              ((v15FieldCoordinateEquiv C e) '' (M.L : Set V)) =
                (Submodule.span F (M.L : Set V)).map
                  (v15FieldCoordinateMap C e) at hspan
            exact hspan
      _ = (⊤ : Submodule F V).map (v15FieldCoordinateMap C e) := by
            rw [M.full.span_eq_top]
      _ = (v15FieldCoordinateMap C e).range := Submodule.map_top _
      _ = ⊤ := LinearMap.range_eq_top_of_surjective _
        (v15FieldCoordinateEquiv C e).surjective

/-- Transport a bilinear form through the field and coordinate equivalences. -/
def v15FieldCoordinateBilin (e : F ≃ₐ[ℚ] C.1)
    (B : LinearMap.BilinForm F V) :
    LinearMap.BilinForm C.1 (Fin (Module.finrank F V) → C.1) where
  toFun x :=
    { toFun := fun y ↦ e (B ((v15FieldCoordinateEquiv C e).symm x)
        ((v15FieldCoordinateEquiv C e).symm y))
      map_add' := by
        intro y z
        rw [(v15FieldCoordinateEquiv C e).symm.map_add]
        simp
      map_smul' := by
        intro a y
        rw [v15FieldCoordinateEquiv_symm_map_smul]
        simp }
  map_add' x y := by
    ext z
    rw [(v15FieldCoordinateEquiv C e).symm.map_add]
    simp
  map_smul' a x := by
    ext y
    rw [v15FieldCoordinateEquiv_symm_map_smul]
    simp

/-- The quadratic form transported through the field and coordinate
equivalences. -/
def v15FieldCoordinateForm
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) :
    QuadraticForm C.1 (Fin (Module.finrank F V) → C.1) where
  toFun x := e (M.Q ((v15FieldCoordinateEquiv C e).symm x))
  toFun_smul a x := by
    rw [v15FieldCoordinateEquiv_symm_map_smul, M.Q.map_smul]
    simp
  exists_companion' := by
    obtain ⟨B, hB⟩ := M.Q.exists_companion
    refine ⟨v15FieldCoordinateBilin C e B, ?_⟩
    intro x y
    rw [(v15FieldCoordinateEquiv C e).symm.map_add, hB]
    simp [v15FieldCoordinateBilin]

@[simp]
theorem v15FieldCoordinateForm_apply
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1)
    (x : Fin (Module.finrank F V) → C.1) :
    M.v15FieldCoordinateForm C e x =
      e (M.Q ((v15FieldCoordinateEquiv C e).symm x)) :=
  rfl

@[simp]
theorem v15FieldCoordinateForm_equiv_apply
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) (x : V) :
    M.v15FieldCoordinateForm C e (v15FieldCoordinateEquiv C e x) = e (M.Q x) := by
  simp [v15FieldCoordinateForm]

/-- The associated bilinear form is carried through the field isomorphism. -/
theorem v15FieldCoordinateAssociated
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) (x y : V) :
    QuadraticMap.associated (M.v15FieldCoordinateForm C e)
        (v15FieldCoordinateEquiv C e x) (v15FieldCoordinateEquiv C e y) =
      e (QuadraticMap.associated M.Q x y) := by
  simp only [QuadraticMap.associated_apply]
  rw [← (v15FieldCoordinateEquiv C e).map_add]
  simp only [v15FieldCoordinateForm_equiv_apply]
  simp only [Module.End.smul_def,
    QuadraticMap.half_moduleEnd_apply_eq_half_smul, invOf_eq_inv, smul_eq_mul,
    map_mul, map_inv₀, map_sub]
  rw [map_ofNat]

/-- Nondegeneracy is preserved by field and coordinate transport. -/
theorem v15FieldCoordinateForm_nondegenerate
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) :
    (M.v15FieldCoordinateForm C e).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  ext z
  simp only [Submodule.mem_bot]
  constructor
  · intro hz
    have hz' := QuadraticMap.mem_radical_iff'.mp hz
    have hxrad : (v15FieldCoordinateEquiv C e).symm z ∈ M.Q.radical := by
      apply QuadraticMap.mem_radical_iff'.mpr
      constructor
      · apply e.injective
        simpa [v15FieldCoordinateForm] using hz'.1
      · intro y
        have h := hz'.2 (v15FieldCoordinateEquiv C e y)
        apply e.injective
        simpa [v15FieldCoordinateForm] using h
    have hxzero : (v15FieldCoordinateEquiv C e).symm z = 0 := by
      have : (v15FieldCoordinateEquiv C e).symm z ∈ (⊥ : Submodule F V) := by
        rw [← M.nondegenerate.radical_eq_bot]
        exact hxrad
      simpa only [Submodule.mem_bot] using this
    apply (v15FieldCoordinateEquiv C e).symm.injective
    simpa using hxzero
  · rintro rfl
    exact (M.v15FieldCoordinateForm C e).radical.zero_mem

/-- Total positive definiteness is preserved by field and coordinate
transport. -/
theorem v15FieldCoordinateForm_positiveDefinite
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) :
    TotallyPositiveDefinite (M.v15FieldCoordinateForm C e) := by
  intro x hx σ
  have hpre : (v15FieldCoordinateEquiv C e).symm x ≠ 0 := by
    intro hzero
    apply hx
    apply (v15FieldCoordinateEquiv C e).symm.injective
    simpa using hzero
  have hpos := M.positiveDefinite ((v15FieldCoordinateEquiv C e).symm x) hpre
    (σ.comp e.toRingEquiv.toRingHom)
  simpa [v15FieldCoordinateForm] using hpos

/-- Integrality of the quadratic values is preserved by field and coordinate
transport. -/
theorem v15FieldCoordinateForm_integral
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) :
    LatticeIntegral (M.v15FieldCoordinateForm C e)
      (M.v15FieldCoordinateLattice C e) := by
  intro x
  letI : RingHomSurjective
      (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv).toRingHom :=
    ⟨(NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv).surjective⟩
  obtain ⟨y, hy, hxy⟩ := (Submodule.mem_map).mp x.2
  have hint := M.integral ⟨y, hy⟩
  have hmap : _root_.IsIntegral ℤ (e (M.Q y)) :=
    IsIntegral.map_of_comp_eq (RingHom.id ℤ) e.toRingEquiv.toRingHom
      (by ext z; simp) hint
  change _root_.IsIntegral ℤ (M.v15FieldCoordinateForm C e x.1)
  rw [← hxy]
  change _root_.IsIntegral ℤ
    (M.v15FieldCoordinateForm C e (v15FieldCoordinateEquiv C e y))
  rw [v15FieldCoordinateForm_equiv_apply]
  exact hmap

/-- The transported data form a canonical presentation over the coded field. -/
def v15FieldCoordinatePresentation
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1)
    (hn : 0 < Module.finrank F V) : GlobalLatticePresentation where
  field := C
  totallyReal := inferInstance
  rank := Module.finrank F V
  rankPositive := hn
  Q := M.v15FieldCoordinateForm C e
  L := M.v15FieldCoordinateLattice C e
  full := M.v15FieldCoordinateLattice_full C e
  nondegenerate := M.v15FieldCoordinateForm_nondegenerate C e
  positiveDefinite := M.v15FieldCoordinateForm_positiveDefinite C e
  integral := M.v15FieldCoordinateForm_integral C e

/-- The source lattice is isometric, over the field isomorphism, to the
transported canonical presentation. -/
def v15FieldCoordinateIsometry
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1)
    (hn : 0 < Module.finrank F V) :
    NumberFieldLatticeEquiv M
      (M.v15FieldCoordinatePresentation C e hn).toNumberFieldLattice where
  fieldEquiv := e.toRingEquiv
  spaceEquiv := v15FieldCoordinateEquiv C e
  map_smul := v15FieldCoordinateEquiv_map_smul C e
  mapsLattice := M.v15FieldCoordinateLattice_mem_iff C e
  mapQuadratic := M.v15FieldCoordinateForm_equiv_apply C e

/-- Rational trace is preserved by the transported quadratic form. -/
theorem v15FieldCoordinateTrace_map
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1) (x : V) :
    Algebra.trace ℚ C.1
        (M.v15FieldCoordinateForm C e (v15FieldCoordinateEquiv C e x)) =
      Algebra.trace ℚ F (M.Q x) := by
  rw [v15FieldCoordinateForm_equiv_apply]
  exact Algebra.trace_eq_of_algEquiv e (M.Q x)

/-- Strict trace Euclideanity is invariant under field and coordinate
transport at every real threshold. -/
theorem v15FieldCoordinateTrace_iff
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1)
    (hn : 0 < Module.finrank F V) (t : ℝ) :
    (M.v15FieldCoordinatePresentation C e hn).IsTraceEuclidean t ↔
      M.IsTraceEuclidean t := by
  change (∀ x : Fin (Module.finrank F V) → C.1,
      ∃ y : M.v15FieldCoordinateLattice C e,
        ((Algebra.trace ℚ C.1
          (M.v15FieldCoordinateForm C e (x - y.1)) : ℚ) : ℝ) < t) ↔
    M.IsTraceEuclidean t
  let s : V ≃+ (Fin (Module.finrank F V) → C.1) :=
    v15FieldCoordinateEquiv C e
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h (s x)
    let z : M.L := ⟨s.symm y.1, by
      apply (M.v15FieldCoordinateLattice_mem_iff C e (s.symm y.1)).mpr
      simpa [s] using y.2⟩
    refine ⟨z, ?_⟩
    have hxy : s (x - z.1) = s x - y.1 := by
      rw [s.map_sub]
      simp [z]
    have htrace := M.v15FieldCoordinateTrace_map C e (x - z.1)
    rw [hxy] at htrace
    have htraceReal := congrArg (fun q : ℚ ↦ (q : ℝ)) htrace
    change ((Algebra.trace ℚ F (M.Q (x - z.1)) : ℚ) : ℝ) < t
    exact htraceReal ▸ hy
  · intro h x
    obtain ⟨z, hz⟩ := h (s.symm x)
    change ((Algebra.trace ℚ F (M.Q (s.symm x - z.1)) : ℚ) : ℝ) < t at hz
    let y : M.v15FieldCoordinateLattice C e :=
      ⟨s z.1, (M.v15FieldCoordinateLattice_mem_iff C e z.1).mp z.2⟩
    refine ⟨y, ?_⟩
    have hxy : s (s.symm x - z.1) = x - y.1 := by
      rw [s.map_sub, s.apply_symm_apply]
    have htrace := M.v15FieldCoordinateTrace_map C e (s.symm x - z.1)
    rw [hxy] at htrace
    have htraceReal := congrArg (fun q : ℚ ↦ (q : ℝ)) htrace
    exact htraceReal.symm ▸ hz

/-- Algebraic integrality over `ℤ` is invariant under the field
isomorphism. -/
theorem v15FieldCoordinate_isIntegral_iff (e : F ≃ₐ[ℚ] C.1) (a : F) :
    _root_.IsIntegral ℤ (e a) ↔ _root_.IsIntegral ℤ a := by
  constructor
  · intro h
    have h' := IsIntegral.map_of_comp_eq (RingHom.id ℤ)
      e.symm.toRingEquiv.toRingHom (by ext z; simp) h
    simpa using h'
  · intro h
    exact IsIntegral.map_of_comp_eq (RingHom.id ℤ) e.toRingEquiv.toRingHom
      (by ext z; simp) h

/-- Classic integrality is invariant under field and coordinate transport. -/
theorem v15FieldCoordinateClassic_iff
    (M : NumberFieldLattice (F := F) (V := V)) (e : F ≃ₐ[ℚ] C.1)
    (hn : 0 < Module.finrank F V) :
    (M.v15FieldCoordinatePresentation C e hn).IsClassicIntegral ↔
      M.IsClassicIntegral := by
  change (∀ x y : M.v15FieldCoordinateLattice C e,
      _root_.IsIntegral ℤ
        (QuadraticMap.associated (M.v15FieldCoordinateForm C e) x.1 y.1)) ↔
    (∀ x y : M.L,
      _root_.IsIntegral ℤ (QuadraticMap.associated M.Q x.1 y.1))
  let s : V ≃+ (Fin (Module.finrank F V) → C.1) :=
    v15FieldCoordinateEquiv C e
  constructor
  · intro h x y
    let x' : M.v15FieldCoordinateLattice C e :=
      ⟨s x.1, (M.v15FieldCoordinateLattice_mem_iff C e x.1).mp x.2⟩
    let y' : M.v15FieldCoordinateLattice C e :=
      ⟨s y.1, (M.v15FieldCoordinateLattice_mem_iff C e y.1).mp y.2⟩
    have hxy := h x' y'
    change _root_.IsIntegral ℤ
      (QuadraticMap.associated (M.v15FieldCoordinateForm C e)
        (s x.1) (s y.1)) at hxy
    rw [M.v15FieldCoordinateAssociated C e x.1 y.1] at hxy
    exact (v15FieldCoordinate_isIntegral_iff C e _).mp hxy
  · intro h x y
    let x' : M.L := ⟨s.symm x.1, by
      apply (M.v15FieldCoordinateLattice_mem_iff C e (s.symm x.1)).mpr
      simpa [s] using x.2⟩
    let y' : M.L := ⟨s.symm y.1, by
      apply (M.v15FieldCoordinateLattice_mem_iff C e (s.symm y.1)).mpr
      simpa [s] using y.2⟩
    have hxy := h x' y'
    have hmap := (v15FieldCoordinate_isIntegral_iff C e _).mpr hxy
    have hassoc := M.v15FieldCoordinateAssociated C e x'.1 y'.1
    have hassoc' :
        QuadraticMap.associated (M.v15FieldCoordinateForm C e) x.1 y.1 =
          e (QuadraticMap.associated M.Q x'.1 y'.1) := by
      simpa [x', y', s] using hassoc
    rw [← hassoc'] at hmap
    exact hmap

/-- The field isomorphism preserves the number-field degree. -/
theorem v15FieldCoordinate_degree_eq (e : F ≃ₐ[ℚ] C.1) :
    Module.finrank ℚ C.1 = Module.finrank ℚ F :=
  e.toLinearEquiv.finrank_eq.symm

/-- Every positive-rank abstract lattice over an arbitrary totally real number
field has a coded canonical presentation, with trace Euclideanity and classic
integrality preserved. -/
theorem v15AbstractToCanonicalAnyField
    (M : NumberFieldLattice (F := F) (V := V))
    (hn : 0 < Module.finrank F V) :
    ∃ (C : CodedNumberField) (P : GlobalLatticePresentation),
      P.field = C ∧ P.rank = Module.finrank F V ∧
      Nonempty (NumberFieldLatticeEquiv M P.toNumberFieldLattice) ∧
      (P.IsTraceEuclidean (P.degree : ℝ) ↔
        M.IsTraceEuclidean (M.degree : ℝ)) ∧
      (P.IsClassicIntegral ↔ M.IsClassicIntegral) := by
  obtain ⟨C, e, hC, _, _⟩ := v15_totally_real_field_code F
  letI : NumberField.IsTotallyReal C.1 := hC
  let P := M.v15FieldCoordinatePresentation C e hn
  refine ⟨C, P, rfl, rfl, ⟨M.v15FieldCoordinateIsometry C e hn⟩, ?_, ?_⟩
  · have hdeg : P.degree = M.degree := by
      exact v15FieldCoordinate_degree_eq C e
    rw [hdeg]
    exact M.v15FieldCoordinateTrace_iff C e hn M.degree
  · exact M.v15FieldCoordinateClassic_iff C e hn

/-- The rank-one ideal presentation is available for an abstract lattice over
an arbitrary totally real number field, after transport to a coded isomorphic
field. -/
theorem v15AbstractRankOneIdealBridgeAnyField
    (M : NumberFieldLattice (F := F) (V := V))
    (hrank : Module.finrank F V = 1) (t : ℝ) :
    ∃ (C : CodedNumberField) (e : F ≃ₐ[ℚ] C.1)
      (I : FractionalIdeal (nonZeroDivisors (𝓞 C.1)) C.1) (α : C.1),
      I ≠ 0 ∧
      (∀ x : V, x ∈ M.L ↔
        (v15FieldCoordinateEquiv C e x) ⟨0, hrank ▸ Nat.zero_lt_one⟩ ∈ I) ∧
      (∀ x : V, e (M.Q x) = α *
        ((v15FieldCoordinateEquiv C e x) ⟨0, hrank ▸ Nat.zero_lt_one⟩) ^ 2) ∧
      (∀ σ : C.1 →+* ℝ, 0 < σ α) ∧
      v15ValueFractionalIdeal I α ≤ 1 ∧
      (M.IsTraceEuclidean t ↔
        GlobalLatticePresentation.V15IdealTraceEuclideanAt I α t) := by
  obtain ⟨C, e, hC, _, _⟩ := v15_totally_real_field_code F
  letI : NumberField.IsTotallyReal C.1 := hC
  let P := M.v15FieldCoordinatePresentation C e (hrank ▸ Nat.zero_lt_one)
  have hPrank : P.rank = 1 := hrank
  obtain ⟨I, α, hI, hmem, hQ, hpos, hint, htrace⟩ :=
    P.rankOne_ideal_bridge_at hPrank t
  refine ⟨C, e, I, α, hI, ?_, ?_, hpos, hint, ?_⟩
  · intro x
    exact (M.v15FieldCoordinateLattice_mem_iff C e x).trans
      (hmem (v15FieldCoordinateEquiv C e x))
  · intro x
    exact (M.v15FieldCoordinateForm_equiv_apply C e x).symm.trans
      (hQ (v15FieldCoordinateEquiv C e x))
  · exact (M.v15FieldCoordinateTrace_iff C e
      (hrank ▸ Nat.zero_lt_one) t).symm.trans htrace

end NumberFieldLattice

end

end TraceEuclidean
