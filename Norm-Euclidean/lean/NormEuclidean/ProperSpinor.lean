import NormEuclidean.SpinorBridge

/-!
# Proper integral stabilizers and their spinor-norm subgroups

All groups here consist of actual ambient linear equivalences. Multiplication
has the usual function-composition order. The integral stabilizer preserves the
given submodule in both directions; its proper subgroup also has determinant one.
The spinor homomorphisms use the genuine Wall spinor norm from the pinned upstream
dependency. Unit-squareclass containment is proved by the integral reflections
constructed in `SpinorBridge`, including at the actual finite completions.
-/

namespace NormEuclidean.ProperSpinor

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The ambient orthogonal group as a subgroup of actual linear automorphisms. -/
def ambientGroup (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x, Q (g x) = Q x}
  one_mem' := fun _ ↦ rfl
  mul_mem' := by
    intro f g hf hg x
    exact (hf (g x)).trans (hg x)
  inv_mem' := by
    intro g hg x
    simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using (hg (g.symm x)).symm

@[simp] theorem mem_ambientGroup_iff (Q : QuadraticForm K V) (g : V ≃ₗ[K] V) :
    g ∈ ambientGroup Q ↔ ∀ x, Q (g x) = Q x := Iff.rfl

/-- Quadratic values are preserved by the actual underlying linear equivalence. -/
@[simp] theorem ambientGroup_map_q (Q : QuadraticForm K V) (g : ambientGroup Q) (x : V) :
    Q (g.1 x) = Q x := g.2 x

/-- The determinant character restricted to the ambient orthogonal group. -/
noncomputable def determinantHom (Q : QuadraticForm K V) : ambientGroup Q →* Kˣ :=
  (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).comp (ambientGroup Q).subtype

@[simp] theorem determinantHom_apply (Q : QuadraticForm K V) (g : ambientGroup Q) :
    determinantHom Q g = LinearEquiv.det g.1 := rfl

/-- The proper ambient orthogonal group is the kernel of the determinant character. -/
noncomputable def properGroup (Q : QuadraticForm K V) : Subgroup (ambientGroup Q) :=
  (determinantHom Q).ker

@[simp] theorem mem_properGroup_iff (Q : QuadraticForm K V) (g : ambientGroup Q) :
    g ∈ properGroup Q ↔ LinearEquiv.det g.1 = 1 := Iff.rfl

/-- The ambient isometries which carry an integral submodule exactly onto itself. -/
def integralStabilizer (Q : QuadraticForm K V) {R : Subring K} (L : Submodule R V) :
    Subgroup (ambientGroup Q) where
  carrier := {g | ∀ x, g.1 x ∈ L ↔ x ∈ L}
  one_mem' := fun _ ↦ Iff.rfl
  mul_mem' := by
    intro f g hf hg x
    exact (hf (g.1 x)).trans (hg x)
  inv_mem' := by
    intro g hg x
    simpa only [Subgroup.coe_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
      using (hg (g.1.symm x)).symm

@[simp] theorem mem_integralStabilizer_iff (Q : QuadraticForm K V)
    {R : Subring K} (L : Submodule R V) (g : ambientGroup Q) :
    g ∈ integralStabilizer Q L ↔ ∀ x, g.1 x ∈ L ↔ x ∈ L := Iff.rfl

/-- Proper integral isometries preserve the lattice and have determinant one. -/
noncomputable def properStabilizer (Q : QuadraticForm K V) {R : Subring K}
    (L : Submodule R V) : Subgroup (ambientGroup Q) :=
  integralStabilizer Q L ⊓ properGroup Q

@[simp] theorem mem_properStabilizer_iff (Q : QuadraticForm K V)
    {R : Subring K} (L : Submodule R V) (g : ambientGroup Q) :
    g ∈ properStabilizer Q L ↔
      (∀ x, g.1 x ∈ L ↔ x ∈ L) ∧ LinearEquiv.det g.1 = 1 := Iff.rfl

variable {Q : QuadraticForm K V} {R : Subring K} {L : Submodule R V}

/-- Forget the integral condition on an existing lattice isometry. -/
def ambientOfLatticeIsometry (e : LatticeIsometry Q Q L L) : ambientGroup Q :=
  ⟨e.toLinearEquiv, e.q_eq⟩

/-- Package an existing integral isometry as an element of the full stabilizer. -/
def ofLatticeIsometry (e : LatticeIsometry Q Q L L) : integralStabilizer Q L :=
  ⟨ambientOfLatticeIsometry e, e.mem_iff⟩

/-- Package a determinant-one lattice isometry as a proper ambient isometry. -/
noncomputable def properAmbientOfLatticeIsometry (e : LatticeIsometry Q Q L L)
    (he : LinearEquiv.det e.toLinearEquiv = 1) : properGroup Q :=
  ⟨ambientOfLatticeIsometry e, he⟩

/-- Package a determinant-one lattice isometry as a proper integral group element. -/
noncomputable def ofProperLatticeIsometry (e : LatticeIsometry Q Q L L)
    (he : LinearEquiv.det e.toLinearEquiv = 1) : properStabilizer Q L :=
  ⟨ambientOfLatticeIsometry e, e.mem_iff, he⟩

/-- A proper integral group element gives the original ambient lattice-isometry structure. -/
def toLatticeIsometry (g : properStabilizer Q L) : LatticeIsometry Q Q L L where
  toLinearEquiv := g.1.1
  q_eq := g.1.2
  mem_iff := g.2.1

/-- Properness is the determinant-one property of the actual ambient equivalence. -/
theorem toLatticeIsometry_det (g : properStabilizer Q L) :
    LinearEquiv.det (toLatticeIsometry g).toLinearEquiv = 1 := g.2.2

section SpinorNorm

variable [CharZero K] [FiniteDimensional K V]

/-- Convert an actual ambient isometry to the upstream half-polar convention. -/
noncomputable def ambientToBong (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (g : ambientGroup Q) :
    Bong.QuadraticSpace.Isometry (SpinorBridge.quadraticSpace Q hQ)
      (SpinorBridge.quadraticSpace Q hQ) where
  toLinearEquiv := g.1
  map_bilin x y := by
    simp only [SpinorBridge.quadraticSpace_bilin, QuadraticMap.polar]
    rw [← g.1.map_add, g.2, g.2, g.2]

omit [FiniteDimensional K V] in
/-- Group multiplication is composition with the right factor applied first. -/
theorem ambientToBong_mul (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (f g : ambientGroup Q) :
    ambientToBong Q hQ (f * g) =
      (ambientToBong Q hQ g).trans (ambientToBong Q hQ f) := by
  apply Bong.QuadraticSpace.Isometry.ext
  intro x
  rfl

omit [FiniteDimensional K V] in
@[simp] theorem ambientToBong_one (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) :
    ambientToBong Q hQ 1 = Bong.QuadraticSpace.Isometry.refl _ := by
  apply Bong.QuadraticSpace.Isometry.ext
  intro x
  rfl

/-- The actual Wall spinor norm as a homomorphism on the ambient orthogonal group. -/
noncomputable def ambientSpinorNormHom (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) : ambientGroup Q →* Bong.Dyadic.SquareClass K where
  toFun g := Bong.QuadraticSpace.spinorNorm (ambientToBong Q hQ g)
  map_one' := by rw [ambientToBong_one, Bong.QuadraticSpace.spinorNorm_refl]
  map_mul' f g := by
    rw [ambientToBong_mul, Bong.QuadraticSpace.spinorNorm_trans, mul_comm]

/-- Restrict the same spinor norm to the proper ambient orthogonal group. -/
noncomputable def properAmbientSpinorNormHom (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) : properGroup Q →* Bong.Dyadic.SquareClass K :=
  (ambientSpinorNormHom Q hQ).comp (properGroup Q).subtype

/-- Restrict the same spinor norm to the proper integral stabilizer. -/
noncomputable def properSpinorNormHom (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) {R : Subring K} (L : Submodule R V) :
    properStabilizer Q L →* Bong.Dyadic.SquareClass K :=
  (ambientSpinorNormHom Q hQ).comp (properStabilizer Q L).subtype

/-- Agreement with the earlier spinor norm on an actual lattice-isometry witness. -/
@[simp] theorem ambientSpinorNormHom_ofLatticeIsometry (hQ : Q.polarBilin.Nondegenerate)
    (e : LatticeIsometry Q Q L L) :
    ambientSpinorNormHom Q hQ (ambientOfLatticeIsometry e) =
      SpinorBridge.spinorNorm hQ e := rfl

@[simp] theorem properAmbientSpinorNormHom_ofLatticeIsometry
    (hQ : Q.polarBilin.Nondegenerate) (e : LatticeIsometry Q Q L L)
    (he : LinearEquiv.det e.toLinearEquiv = 1) :
    properAmbientSpinorNormHom Q hQ (properAmbientOfLatticeIsometry e he) =
      SpinorBridge.spinorNorm hQ e := rfl

@[simp] theorem properSpinorNormHom_ofLatticeIsometry (hQ : Q.polarBilin.Nondegenerate)
    (e : LatticeIsometry Q Q L L) (he : LinearEquiv.det e.toLinearEquiv = 1) :
    properSpinorNormHom Q hQ L (ofProperLatticeIsometry e he) =
      SpinorBridge.spinorNorm hQ e := rfl

/-- The proper integral spinor-norm image is a subgroup, not just a set of values. -/
noncomputable def properSpinorImage (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) {R : Subring K} (L : Submodule R V) :
    Subgroup (Bong.Dyadic.SquareClass K) :=
  (properSpinorNormHom Q hQ L).range

/-- Image membership means an actual determinant-one integral isometry realizes the value. -/
theorem mem_properSpinorImage_iff (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) {R : Subring K} (L : Submodule R V)
    (a : Bong.Dyadic.SquareClass K) :
    a ∈ properSpinorImage Q hQ L ↔
      ∃ e : LatticeIsometry Q Q L L,
        LinearEquiv.det e.toLinearEquiv = 1 ∧ SpinorBridge.spinorNorm hQ e = a := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨toLatticeIsometry g, toLatticeIsometry_det g, hg⟩
  · rintro ⟨e, he, ha⟩
    exact ⟨ofProperLatticeIsometry e he, ha⟩

end SpinorNorm

/-- Unit square classes use the actual inclusion of the subring into its ambient field. -/
def unitSquareClassHom (R : Subring K) : Rˣ →* Bong.Dyadic.SquareClass K :=
  (QuotientGroup.mk' (Subgroup.square Kˣ)).comp (Units.map R.subtype.toMonoidHom)

@[simp] theorem unitSquareClassHom_apply (R : Subring K) (u : Rˣ) :
    unitSquareClassHom R u =
      Bong.Dyadic.squareClass K (Units.map R.subtype.toMonoidHom u) := rfl

/-- The subgroup of ambient square classes represented by units of the integral subring. -/
def unitSquareClasses (R : Subring K) : Subgroup (Bong.Dyadic.SquareClass K) :=
  (unitSquareClassHom R).range

theorem mem_unitSquareClasses_iff (R : Subring K) (a : Bong.Dyadic.SquareClass K) :
    a ∈ unitSquareClasses R ↔ ∃ u : Rˣ, unitSquareClassHom R u = a := Iff.rfl

section Units

variable [CharZero K] [FiniteDimensional K V]

/-- Representing a unit and one places that unit square class in the proper integral image. -/
theorem unitSquareClass_mem_properSpinorImage (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (R : Subring K) (L : Submodule R V)
    (hInt : ∀ x ∈ L, Q x ∈ R) (u : Rˣ)
    (hu : ∃ x ∈ L, Q x = ((u : R) : K)) (hOne : ∃ x ∈ L, Q x = 1) :
    unitSquareClassHom R u ∈ properSpinorImage Q hQ L := by
  exact (mem_properSpinorImage_iff Q hQ L _).2
    (SpinorBridge.exists_proper_isometry_of_represented_unit Q hQ R L hInt u hu hOne)

/-- An integral lattice representing every unit contains all unit square classes
in its proper spinor-norm image; representation of one is derived at the unit one. -/
theorem unitSquareClasses_le_properSpinorImage (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (R : Subring K) (L : Submodule R V)
    (hInt : ∀ x ∈ L, Q x ∈ R) (hUnits : ∀ u : Rˣ, ∃ x ∈ L, Q x = ((u : R) : K)) :
    unitSquareClasses R ≤ properSpinorImage Q hQ L := by
  have hOne : ∃ x ∈ L, Q x = 1 := by simpa only [Units.val_one, Subring.coe_one] using hUnits 1
  rintro a ⟨u, rfl⟩
  exact unitSquareClass_mem_properSpinorImage Q hQ R L hInt u (hUnits u) hOne

end Units

end NormEuclidean.ProperSpinor

namespace NormEuclidean.CompletedIntegralLattice

open IsDedekindDomain ProperSpinor

variable {K V : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- At every actual finite completion, the proper integral spinor-norm subgroup
of a hyperbolic enlargement contains the subgroup of all local unit square classes. -/
theorem hyperbolic_unitSquareClasses_le_properSpinorImage (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q) :
    unitSquareClasses (LocalRing R v) ≤
      properSpinorImage (form R v (Hyperbolic.form Q))
        (hyperbolic_form_polarBilin_nondegenerate R v Q hQ)
        (carrier R v L.hyperbolic.carrier) := by
  rintro a ⟨u, rfl⟩
  exact (mem_properSpinorImage_iff _ _ _ _).2
    (hyperbolic_exists_proper_isometry_unit R v Q hQ L u)

end NormEuclidean.CompletedIntegralLattice
