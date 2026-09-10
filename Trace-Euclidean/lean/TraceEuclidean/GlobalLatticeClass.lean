import TraceEuclidean.ArithmeticFiniteness
import TraceEuclidean.NumberFieldLattice
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Concrete presentations and equivalence classes for the field--lattice pairs
that occur in Theorems 1.2 and 1.3.  Every ground field is represented as a
finite intermediate extension of `ℚ` inside one fixed algebraic closure.  The
relation is the paper's field isomorphism together with a semilinear isometry
carrying one lattice onto the other.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

/-- One ambient algebraic closure in which number fields are coded. -/
abbrev UniversalNumberFieldAmbient := AlgebraicClosure ℚ

/-- A finite extension of `ℚ` inside the fixed algebraic closure. -/
abbrev CodedNumberField := NumberFieldCode UniversalNumberFieldAmbient

/--
A concrete representative of a positive definite integral lattice over a
totally real coded number field.  The ambient quadratic space is put in the
canonical coordinate form `Fin rank → field`; this loses no isometry class.
-/
structure GlobalLatticePresentation where
  field : CodedNumberField
  totallyReal : NumberField.IsTotallyReal field.1
  rank : ℕ
  rankPositive : 0 < rank
  Q : QuadraticForm field.1 (Fin rank → field.1)
  L : Submodule (𝓞 field.1) (Fin rank → field.1)
  full : L.IsLattice field.1
  nondegenerate : Q.Nondegenerate
  positiveDefinite :
    ∀ x : Fin rank → field.1, x ≠ 0 →
      ∀ σ : field.1 →+* ℝ, 0 < σ (Q x)
  integral : ∀ x : L, _root_.IsIntegral ℤ (Q x.1)

namespace GlobalLatticePresentation

/-- The field degree attached to a presentation. -/
def degree (P : GlobalLatticePresentation) : ℕ :=
  Module.finrank ℚ P.field.1

/-- The additional scale-integrality condition in Theorem 1.2. -/
def IsClassicIntegral (P : GlobalLatticePresentation) : Prop :=
  ∀ x y : P.L,
    _root_.IsIntegral ℤ (QuadraticMap.associated P.Q x.1 y.1)

/-- Strict `t`-trace Euclideanity for a concrete presentation. -/
def IsTraceEuclidean (P : GlobalLatticePresentation) (t : ℝ) : Prop :=
  ∀ x : Fin P.rank → P.field.1, ∃ y : P.L,
    ((Algebra.trace ℚ P.field.1 (P.Q (x - y.1)) : ℚ) : ℝ) < t

/-- The bundled one-field object represented by `P`. -/
def toNumberFieldLattice (P : GlobalLatticePresentation) :
    NumberFieldLattice (F := P.field.1) (V := Fin P.rank → P.field.1) := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  refine
    { Q := P.Q
      L := P.L
      full := P.full
      nondegenerate := P.nondegenerate
      positiveDefinite := ?_
      integral := P.integral }
  intro x hx σ
  exact P.positiveDefinite x hx σ

/--
The equivalence relation stated immediately before Theorem 1.2.  The rank and
degree equalities are recorded explicitly as the standard dimension
invariants of the semilinear equivalences; recording them makes the quotient
invariants available without adding any mathematical conclusion.
-/
structure EquivalenceData (P P' : GlobalLatticePresentation) where
  fieldEquiv : P.field.1 ≃ₐ[ℚ] P'.field.1
  spaceEquiv : (Fin P.rank → P.field.1) ≃+ (Fin P'.rank → P'.field.1)
  map_smul : ∀ (a : P.field.1) x,
    spaceEquiv (a • x) = fieldEquiv a • spaceEquiv x
  mapsLattice : ∀ x,
    x ∈ P.L ↔ spaceEquiv x ∈ P'.L
  mapQuadratic : ∀ x,
    P'.Q (spaceEquiv x) = fieldEquiv (P.Q x)
  rank_eq : P.rank = P'.rank
  degree_eq : P.degree = P'.degree

namespace EquivalenceData

/-- Reverse a field--lattice equivalence. -/
protected def symm {P P' : GlobalLatticePresentation}
    (e : EquivalenceData P P') : EquivalenceData P' P where
  fieldEquiv := e.fieldEquiv.symm
  spaceEquiv := e.spaceEquiv.symm
  map_smul := by
    intro a x
    apply e.spaceEquiv.injective
    rw [AddEquiv.apply_symm_apply, e.map_smul,
      AlgEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  mapsLattice := by
    intro x
    simpa using (e.mapsLattice (e.spaceEquiv.symm x)).symm
  mapQuadratic := by
    intro x
    apply e.fieldEquiv.injective
    simpa using (e.mapQuadratic (e.spaceEquiv.symm x)).symm
  rank_eq := e.rank_eq.symm
  degree_eq := e.degree_eq.symm

/-- Compose two field--lattice equivalences. -/
protected def trans {P P' P'' : GlobalLatticePresentation}
    (e : EquivalenceData P P') (e' : EquivalenceData P' P'') :
    EquivalenceData P P'' where
  fieldEquiv := e.fieldEquiv.trans e'.fieldEquiv
  spaceEquiv := e.spaceEquiv.trans e'.spaceEquiv
  map_smul := by
    intro a x
    rw [AddEquiv.trans_apply, e.map_smul, e'.map_smul]
    rfl
  mapsLattice := by
    intro x
    exact (e.mapsLattice x).trans (e'.mapsLattice (e.spaceEquiv x))
  mapQuadratic := by
    intro x
    rw [AddEquiv.trans_apply, e'.mapQuadratic, e.mapQuadratic]
    rfl
  rank_eq := e.rank_eq.trans e'.rank_eq
  degree_eq := e.degree_eq.trans e'.degree_eq

/-- The trace of a quadratic displacement is preserved by equivalence data. -/
theorem trace_quadratic_sub_map {P P' : GlobalLatticePresentation}
    (e : EquivalenceData P P') (x y : Fin P.rank → P.field.1) :
    Algebra.trace ℚ P'.field.1
        (P'.Q (e.spaceEquiv x - e.spaceEquiv y)) =
      Algebra.trace ℚ P.field.1 (P.Q (x - y)) := by
  rw [← e.spaceEquiv.map_sub, e.mapQuadratic]
  exact Algebra.trace_eq_of_algEquiv e.fieldEquiv (P.Q (x - y))

/-- The associated bilinear value is carried through the field equivalence. -/
theorem associated_map {P P' : GlobalLatticePresentation}
    (e : EquivalenceData P P') (x y : Fin P.rank → P.field.1) :
    QuadraticMap.associated P'.Q (e.spaceEquiv x) (e.spaceEquiv y) =
      e.fieldEquiv (QuadraticMap.associated P.Q x y) := by
  simp only [QuadraticMap.associated_apply]
  rw [← e.spaceEquiv.map_add, e.mapQuadratic, e.mapQuadratic,
    e.mapQuadratic]
  simp only [Module.End.smul_def,
    QuadraticMap.half_moduleEnd_apply_eq_half_smul, invOf_eq_inv, smul_eq_mul,
    map_mul, map_inv₀, map_sub]
  rw [map_ofNat]

/-- Classic integrality is transported by equivalence data. -/
theorem isClassicIntegral_imp {P P' : GlobalLatticePresentation}
    (e : EquivalenceData P P')
    (hP : P.IsClassicIntegral) : P'.IsClassicIntegral := by
  intro x' y'
  let x : P.L :=
    ⟨e.spaceEquiv.symm x'.1,
      (e.mapsLattice (e.spaceEquiv.symm x'.1)).mpr (by
        rw [e.spaceEquiv.apply_symm_apply]
        exact x'.2)⟩
  let y : P.L :=
    ⟨e.spaceEquiv.symm y'.1,
      (e.mapsLattice (e.spaceEquiv.symm y'.1)).mpr (by
        rw [e.spaceEquiv.apply_symm_apply]
        exact y'.2)⟩
  have hIntegral :
      _root_.IsIntegral ℤ
        (e.fieldEquiv (QuadraticMap.associated P.Q x.1 y.1)) :=
    IsIntegral.map_of_comp_eq (RingHom.id ℤ) e.fieldEquiv.toRingHom
      (by ext z; simp) (hP x y)
  rw [← e.associated_map x.1 y.1] at hIntegral
  simpa [x, y] using hIntegral

/-- Classic integrality is invariant under equivalence data. -/
theorem isClassicIntegral_iff {P P' : GlobalLatticePresentation}
    (e : EquivalenceData P P') :
    P.IsClassicIntegral ↔ P'.IsClassicIntegral :=
  ⟨e.isClassicIntegral_imp, e.symm.isClassicIntegral_imp⟩

/-- Strict trace Euclideanity is transported by equivalence data. -/
theorem isTraceEuclidean_imp {P P' : GlobalLatticePresentation}
    (e : EquivalenceData P P') {t : ℝ}
    (hP : P.IsTraceEuclidean t) : P'.IsTraceEuclidean t := by
  intro x'
  obtain ⟨y, hy⟩ := hP (e.spaceEquiv.symm x')
  let y' : P'.L :=
    ⟨e.spaceEquiv y.1, (e.mapsLattice y.1).mp y.2⟩
  refine ⟨y', ?_⟩
  have htrace := e.trace_quadratic_sub_map (e.spaceEquiv.symm x') y.1
  have htraceReal := congrArg (fun q : ℚ ↦ (q : ℝ)) htrace
  simpa [y', AddEquiv.apply_symm_apply] using htraceReal.trans_lt hy

/-- Strict trace Euclideanity is invariant under equivalence data. -/
theorem isTraceEuclidean_iff {P P' : GlobalLatticePresentation}
    (e : EquivalenceData P P') (t : ℝ) :
    P.IsTraceEuclidean t ↔ P'.IsTraceEuclidean t :=
  ⟨e.isTraceEuclidean_imp, e.symm.isTraceEuclidean_imp⟩

end EquivalenceData

/-- Two presentations are equivalent when the paper's equivalence data exist. -/
def IsEquivalent (P P' : GlobalLatticePresentation) : Prop :=
  Nonempty (EquivalenceData P P')

namespace IsEquivalent

protected theorem refl (P : GlobalLatticePresentation) : P.IsEquivalent P :=
  ⟨
    { fieldEquiv := AlgEquiv.refl
      spaceEquiv := AddEquiv.refl (Fin P.rank → P.field.1)
      map_smul := by simp
      mapsLattice := by simp
      mapQuadratic := by simp
      rank_eq := rfl
      degree_eq := rfl }
  ⟩

protected theorem symm {P P' : GlobalLatticePresentation}
    (h : P.IsEquivalent P') : P'.IsEquivalent P := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

protected theorem trans {P P' P'' : GlobalLatticePresentation}
    (h : P.IsEquivalent P') (h' : P'.IsEquivalent P'') :
    P.IsEquivalent P'' := by
  rcases h with ⟨e⟩
  rcases h' with ⟨e'⟩
  exact ⟨e.trans e'⟩

/-- Strict trace Euclideanity is independent of the chosen presentation. -/
theorem isTraceEuclidean_iff {P P' : GlobalLatticePresentation}
    (h : P.IsEquivalent P') (t : ℝ) :
    P.IsTraceEuclidean t ↔ P'.IsTraceEuclidean t := by
  rcases h with ⟨e⟩
  exact e.isTraceEuclidean_iff t

/-- Classic integrality is independent of the chosen presentation. -/
theorem isClassicIntegral_iff {P P' : GlobalLatticePresentation}
    (h : P.IsEquivalent P') :
    P.IsClassicIntegral ↔ P'.IsClassicIntegral := by
  rcases h with ⟨e⟩
  exact e.isClassicIntegral_iff

end IsEquivalent

instance globalLatticePresentationSetoid : Setoid GlobalLatticePresentation where
  r := IsEquivalent
  iseqv :=
    { refl := IsEquivalent.refl
      symm := IsEquivalent.symm
      trans := IsEquivalent.trans }

end GlobalLatticePresentation

/-- Actual equivalence classes of the varying field--lattice pairs. -/
abbrev GlobalLatticeClass := Quotient
  GlobalLatticePresentation.globalLatticePresentationSetoid

namespace GlobalLatticeClass

/-- Rank is well defined on field--lattice equivalence classes. -/
def rank : GlobalLatticeClass → ℕ :=
  Quotient.lift GlobalLatticePresentation.rank
    (fun _ _ e ↦ e.elim fun data ↦ data.rank_eq)

/-- Field degree is well defined on field--lattice equivalence classes. -/
def degree : GlobalLatticeClass → ℕ :=
  Quotient.lift GlobalLatticePresentation.degree
    (fun _ _ e ↦ e.elim fun data ↦ data.degree_eq)

/-- Strict trace Euclideanity as a well-defined predicate on actual classes. -/
def IsTraceEuclidean (t : ℝ) : GlobalLatticeClass → Prop :=
  Quotient.lift (fun P ↦ P.IsTraceEuclidean t)
    (fun _ _ h ↦ propext (h.isTraceEuclidean_iff t))

/-- Classic integrality as a well-defined predicate on actual classes. -/
def IsClassicIntegral : GlobalLatticeClass → Prop :=
  Quotient.lift GlobalLatticePresentation.IsClassicIntegral
    (fun _ _ h ↦ propext h.isClassicIntegral_iff)

/-- A noncomputably selected concrete representative of an equivalence class. -/
def representative (c : GlobalLatticeClass) : GlobalLatticePresentation :=
  Quotient.out c

/-- The selected coded ground field of a global lattice class. -/
def fieldCode (c : GlobalLatticeClass) : CodedNumberField :=
  c.representative.field

/-- The selected representative denotes the original quotient class. -/
theorem mk_representative (c : GlobalLatticeClass) :
    Quotient.mk _ c.representative = c :=
  Quotient.out_eq c

@[simp]
theorem rank_mk (P : GlobalLatticePresentation) :
    rank (Quotient.mk _ P) = P.rank :=
  rfl

@[simp]
theorem degree_mk (P : GlobalLatticePresentation) :
    degree (Quotient.mk _ P) = P.degree :=
  rfl

@[simp]
theorem isTraceEuclidean_mk (P : GlobalLatticePresentation) (t : ℝ) :
    IsTraceEuclidean t (Quotient.mk _ P) ↔ P.IsTraceEuclidean t :=
  Iff.rfl

@[simp]
theorem isClassicIntegral_mk (P : GlobalLatticePresentation) :
    IsClassicIntegral (Quotient.mk _ P) ↔ P.IsClassicIntegral :=
  Iff.rfl

@[simp]
theorem representative_rank (c : GlobalLatticeClass) :
    c.representative.rank = c.rank := by
  rw [← rank_mk c.representative, c.mk_representative]

@[simp]
theorem representative_degree (c : GlobalLatticeClass) :
    c.representative.degree = c.degree := by
  rw [← degree_mk c.representative, c.mk_representative]

/-- Every class has the positive rank required in the manuscript. -/
theorem rank_pos (c : GlobalLatticeClass) : 0 < c.rank := by
  rw [← c.representative_rank]
  exact c.representative.rankPositive

end GlobalLatticeClass

end

end TraceEuclidean
