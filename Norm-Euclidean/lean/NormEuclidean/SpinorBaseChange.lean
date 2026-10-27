import NormEuclidean.AdelicSpinorKernel

/-!
# Reflection and two-reflection spinor norms under actual completion

The scalar extension of a reflection is the reflection in the image vector.
The two-reflection formulas then give the completion compatibility needed for
the global hyperbolic correction, without assuming a general naturality law
for the Wall spinor norm.
-/

noncomputable section

open scoped TensorProduct

namespace NormEuclidean.CompletedIntegralLattice

open IsDedekindDomain

variable {K V : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- Nonzero quadratic values stay nonzero at an actual finite completion. -/
theorem form_inclusion_ne_zero (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) :
    form R v Q (inclusion R v x) ≠ 0 := by
  rw [form_inclusion]
  intro h
  exact hx ((algebraMap K (LocalField R v)).injective (h.trans (map_zero _).symm))

/-- Scalar extension of a global reflection is the local reflection in the
same vector after inclusion. This also covers the dyadic completions. -/
theorem equiv_reflection (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) :
    equiv R v (IntegralReflection.linearEquiv Q x hx) =
      IntegralReflection.linearEquiv (form R v Q) (inclusion R v x)
        (form_inclusion_ne_zero R v Q x hx) := by
  have hinc (y : V) :
      equiv R v (IntegralReflection.linearEquiv Q x hx) (inclusion R v y) =
        IntegralReflection.linearEquiv (form R v Q) (inclusion R v x)
          (form_inclusion_ne_zero R v Q x hx) (inclusion R v y) := by
    rw [equiv_inclusion, IntegralReflection.linearEquiv_apply,
      IntegralReflection.linearEquiv_apply]
    simp only [QuadraticMap.polar, ← inclusion_add, form_inclusion,
      map_sub, map_smul]
    conv_lhs =>
      rw [← IsScalarTower.algebraMap_smul (R := K) (A := LocalField R v)]
    simp only [map_inv₀, map_mul, map_sub]
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      have h := congrArg (fun z ↦ a • z) (hinc y)
      simpa only [← map_smul, inclusion, TensorProduct.mk_apply,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add z w hz hw => simp only [map_add, hz, hw]

end NormEuclidean.CompletedIntegralLattice

namespace NormEuclidean.SpinorBaseChange

open ProperSpinor CompletedIntegralLattice IsDedekindDomain

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- Regard an ambient reflection as an isometry of the full ambient submodule. -/
def reflectionIsometry (x : V) (hx : Q x ≠ 0) :
    LatticeIsometry Q Q (⊤ : Submodule (⊤ : Subring K) V) ⊤ :=
  IntegralReflection.isometry Q ⊤ ⊤ (fun _ _ ↦ trivial) x (by trivial) hx (by trivial)

/-- The actual ambient reflection in a nonzero quadratic-value vector. -/
def ambientReflection (x : V) (hx : Q x ≠ 0) : ambientGroup Q :=
  ambientOfLatticeIsometry (reflectionIsometry Q x hx)

@[simp] theorem ambientReflection_det (hQ : Q.polarBilin.Nondegenerate)
    (x : V) (hx : Q x ≠ 0) :
    determinantHom Q (ambientReflection Q x hx) = (-1 : Kˣ) :=
  SpinorBridge.det_integralReflection Q hQ ⊤ ⊤ (fun _ _ ↦ trivial)
    x (by trivial) hx (by trivial)

@[simp] theorem ambientReflection_spinorNorm (hQ : Q.polarBilin.Nondegenerate)
    (x : V) (hx : Q x ≠ 0) :
    ambientSpinorNormHom Q hQ (ambientReflection Q x hx) =
      Bong.Dyadic.squareClass K (Units.mk0 (Q x) hx) :=
  SpinorBridge.spinorNorm_integralReflection Q hQ ⊤ ⊤ (fun _ _ ↦ trivial)
    x (by trivial) hx (by trivial)

/-- Two reflections give a genuine proper ambient transformation. -/
def doubleReflection (hQ : Q.polarBilin.Nondegenerate)
    (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0) : properGroup Q :=
  ⟨ambientReflection Q x hx * ambientReflection Q y hy, by
    change determinantHom Q (ambientReflection Q x hx * ambientReflection Q y hy) = 1
    rw [map_mul, ambientReflection_det Q hQ, ambientReflection_det Q hQ]
    simp⟩

/-- The global spinor norm of this double reflection is the product of its two values. -/
theorem doubleReflection_spinorNorm (hQ : Q.polarBilin.Nondegenerate)
    (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0) :
    properAmbientSpinorNormHom Q hQ (doubleReflection Q hQ x hx y hy) =
      Bong.Dyadic.squareClass K (Units.mk0 (Q x) hx * Units.mk0 (Q y) hy) := by
  change ambientSpinorNormHom Q hQ
    (ambientReflection Q x hx * ambientReflection Q y hy) = _
  rw [map_mul, ambientReflection_spinorNorm Q hQ, ambientReflection_spinorNorm Q hQ]
  exact (map_mul (QuotientGroup.mk' (Subgroup.square Kˣ)) _ _).symm

variable [Invertible (2 : K)]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- The scalar extension of the explicit double reflection is the local
double reflection in the two included vectors. -/
theorem equiv_doubleReflection (hQ : Q.polarBilin.Nondegenerate)
    (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0) (v : HeightOneSpectrum R) :
    equiv R v (doubleReflection Q hQ x hx y hy).1.1 =
      (doubleReflection (form R v Q) (form_polarBilin_nondegenerate R v Q hQ)
        (inclusion R v x) (form_inclusion_ne_zero R v Q x hx)
        (inclusion R v y) (form_inclusion_ne_zero R v Q y hy)).1.1 := by
  change equiv R v (IntegralReflection.linearEquiv Q x hx *
    IntegralReflection.linearEquiv Q y hy) = _
  rw [show equiv R v (IntegralReflection.linearEquiv Q x hx *
      IntegralReflection.linearEquiv Q y hy) =
        equiv R v (IntegralReflection.linearEquiv Q x hx) *
          equiv R v (IntegralReflection.linearEquiv Q y hy) from
      LinearEquiv.baseChange_mul K (LocalField R v) V _ _]
  rw [equiv_reflection, equiv_reflection]
  rfl

/-- Compute the local Wall spinor norm from the actual completed reflection
identity, rather than from an assumed naturality law. -/
theorem completed_doubleReflection_spinorNorm (hQ : Q.polarBilin.Nondegenerate)
    (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0) (v : HeightOneSpectrum R) :
    ambientSpinorNormHom (form R v Q) (form_polarBilin_nondegenerate R v Q hQ)
      ⟨equiv R v (doubleReflection Q hQ x hx y hy).1.1,
        equiv_form R v Q Q _ (doubleReflection Q hQ x hx y hy).1.2⟩ =
      Bong.Dyadic.squareClass (LocalField R v)
        (Units.map (algebraMap K (LocalField R v))
          (Units.mk0 (Q x) hx * Units.mk0 (Q y) hy)) := by
  have heq : (⟨equiv R v (doubleReflection Q hQ x hx y hy).1.1,
        equiv_form R v Q Q _ (doubleReflection Q hQ x hx y hy).1.2⟩ :
      ambientGroup (form R v Q)) =
        (doubleReflection (form R v Q) (form_polarBilin_nondegenerate R v Q hQ)
          (inclusion R v x) (form_inclusion_ne_zero R v Q x hx)
          (inclusion R v y) (form_inclusion_ne_zero R v Q y hy)).1 :=
    Subtype.ext (equiv_doubleReflection Q R hQ x hx y hy v)
  rw [heq]
  change properAmbientSpinorNormHom (form R v Q)
    (form_polarBilin_nondegenerate R v Q hQ)
    (doubleReflection (form R v Q) (form_polarBilin_nondegenerate R v Q hQ)
      (inclusion R v x) (form_inclusion_ne_zero R v Q x hx)
      (inclusion R v y) (form_inclusion_ne_zero R v Q y hy)) = _
  rw [doubleReflection_spinorNorm]
  congr 1
  apply Units.ext
  simp only [Units.val_mul, Units.val_mk0, Units.coe_map, form_inclusion, map_mul]
  rfl

end NormEuclidean.SpinorBaseChange

namespace NormEuclidean.SpinorBaseChange

open ProperSpinor CompletedIntegralLattice AdelicApproximation IsDedekindDomain

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)

/-- The explicit global proper correction associated to a field unit. Its
reflecting vectors have values `u` and one in the adjoined hyperbolic plane. -/
def hyperbolicCorrection (u : Kˣ) : properGroup (Hyperbolic.form Q) :=
  doubleReflection (Hyperbolic.form Q) (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
    (0, (u : K), 1) (by simp [Hyperbolic.q])
    (0, 1, 1) (by simp [Hyperbolic.q])

omit [FiniteDimensional K V] in
private theorem hyperbolicCorrection_valueUnits (u : Kˣ) :
    Units.mk0 (Hyperbolic.form Q (0, (u : K), 1))
        (by simp [Hyperbolic.q]) *
      Units.mk0 (Hyperbolic.form Q (0, 1, 1)) (by simp [Hyperbolic.q]) = u := by
  apply Units.ext
  simp [Hyperbolic.q]

/-- The explicit correction realizes the prescribed global spinor squareclass. -/
theorem hyperbolicCorrection_spinorNorm (u : Kˣ) :
    properAmbientSpinorNormHom (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ) (hyperbolicCorrection Q hQ u) =
      Bong.Dyadic.squareClass K u := by
  rw [hyperbolicCorrection, doubleReflection_spinorNorm,
    hyperbolicCorrection_valueUnits Q]

variable [NumberField K] [Invertible (2 : K)]

/-- Every actual finite completion of the chosen global correction has the
prescribed principal spinor squareclass. This proves the needed compatibility
for the same global element at all places, including the dyadic ones. -/
theorem hyperbolicCorrection_localSpinorNorm (u : Kˣ)
    (v : HeightOneSpectrum (integerSubring K)) :
    properAmbientSpinorNormHom (form (integerSubring K) v (Hyperbolic.form Q))
        (form_polarBilin_nondegenerate (integerSubring K) v (Hyperbolic.form Q)
          (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
        (localizeProper (Hyperbolic.form Q) (hyperbolicCorrection Q hQ u) v) =
      Bong.Dyadic.squareClass (LocalField (integerSubring K) v)
        (Units.map (algebraMap K (LocalField (integerSubring K) v)) u) := by
  have h := completed_doubleReflection_spinorNorm (Hyperbolic.form Q) (integerSubring K)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
    (0, (u : K), 1) (by simp [Hyperbolic.q])
    (0, 1, 1) (by simp [Hyperbolic.q]) v
  rw [hyperbolicCorrection_valueUnits Q] at h
  exact h

end NormEuclidean.SpinorBaseChange
