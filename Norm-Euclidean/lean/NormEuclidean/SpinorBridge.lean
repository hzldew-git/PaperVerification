import NormEuclidean.AllPlaceGenus
import NormEuclidean.IntegralReflection
import NormEuclidean.LocalHyperbolicUniversality
import NormEuclidean.QuadraticBaseChangeNondegenerate
import Bong.QuadraticSpace.SpinorNormMultiplicative

/-!
# Spinor norms of integral reflections over an arbitrary subring

The pinned BongTheory dependency constructs the spinor norm from the Wall form
over any characteristic-zero field. This file identifies its half-polar
convention with the quadratic forms used here. Two integral reflections give a
proper lattice isometry with any represented unit square class, provided the
lattice also represents one. No dyadic context or global genus theorem is assumed.
-/

namespace NormEuclidean.SpinorBridge

open QuadraticMap

variable {K V W U : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U]

/-- The nondegenerate quadratic space with the half-polar bilinear convention. -/
noncomputable def quadraticSpace (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) : Bong.QuadraticSpace K V where
  bilin := (2 : K)⁻¹ • Q.polarBilin
  isSymm := by
    constructor
    intro x y
    change (2 : K)⁻¹ * polar Q x y = (2 : K)⁻¹ * polar Q y x
    rw [polar_comm]
  nondegenerate := by
    constructor
    · intro x hx
      apply hQ.1 x
      intro y
      have h := hx y
      change (2 : K)⁻¹ * Q.polarBilin x y = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num))
    · intro y hy
      apply hQ.2 y
      intro x
      have h := hy x
      change (2 : K)⁻¹ * Q.polarBilin x y = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num))

@[simp] theorem quadraticSpace_bilin (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (x y : V) :
    (quadraticSpace Q hQ).bilin x y = (2 : K)⁻¹ * polar Q x y := rfl

/-- The convention change leaves every quadratic value unchanged. -/
@[simp] theorem quadraticSpace_quadratic (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (x : V) :
    (quadraticSpace Q hQ).quadratic x = Q x := by
  change (2 : K)⁻¹ * polar Q x x = Q x
  rw [polar_self]
  simp only [two_smul]
  field_simp
  ring

variable {R : Subring K} {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
  {Q'' : QuadraticForm K U} {L : Submodule R V} {L' : Submodule R W}
  {L'' : Submodule R U}

/-- An integral quadratic isometry induces the same ambient bilinear isometry. -/
noncomputable def toBongIsometry (hQ : Q.polarBilin.Nondegenerate)
    (hQ' : Q'.polarBilin.Nondegenerate) (e : LatticeIsometry Q Q' L L') :
    Bong.QuadraticSpace.Isometry (quadraticSpace Q hQ) (quadraticSpace Q' hQ') where
  toLinearEquiv := e.toLinearEquiv
  map_bilin x y := by
    simp only [quadraticSpace_bilin, polar]
    rw [← e.toLinearEquiv.map_add, e.q_eq, e.q_eq, e.q_eq]

@[simp] theorem toBongIsometry_toLinearEquiv (hQ : Q.polarBilin.Nondegenerate)
    (hQ' : Q'.polarBilin.Nondegenerate) (e : LatticeIsometry Q Q' L L') :
    (toBongIsometry hQ hQ' e).toLinearEquiv = e.toLinearEquiv := rfl

/-- The ambient conversion commutes with composition of integral isometries. -/
theorem toBongIsometry_compose (hQ : Q.polarBilin.Nondegenerate)
    (hQ' : Q'.polarBilin.Nondegenerate) (hQ'' : Q''.polarBilin.Nondegenerate)
    (e : LatticeIsometry Q Q' L L') (f : LatticeIsometry Q' Q'' L' L'') :
    toBongIsometry hQ hQ'' (e.compose f) =
      (toBongIsometry hQ hQ' e).trans (toBongIsometry hQ' hQ'' f) := by
  apply Bong.QuadraticSpace.Isometry.ext
  intro x
  rfl

/-- The existing integral reflection is the reflection in the half-polar convention. -/
theorem reflectionLinearEquiv_eq (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (v : V) (hv : Q v ≠ 0) :
    IntegralReflection.linearEquiv Q v hv =
      (quadraticSpace Q hQ).reflectionLinearEquiv v
        (by simpa [Bong.QuadraticSpace.IsAnisotropic] using hv) := by
  apply LinearEquiv.ext
  intro x
  rw [IntegralReflection.linearEquiv_apply,
    Bong.QuadraticSpace.reflectionLinearEquiv_apply]
  simp only [quadraticSpace_bilin, quadraticSpace_quadratic]
  have hc : (Q v)⁻¹ * polar Q v x =
      2 * ((2 : K)⁻¹ * polar Q v x) / Q v := by field_simp
  rw [hc]

/-- Conversion of an actual integral reflection agrees with BongTheory's reflection. -/
theorem toBongIsometry_integralReflection (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (R : Subring K) (L : Submodule R V)
    (hInt : ∀ x ∈ L, Q x ∈ R) (v : V) (hvL : v ∈ L)
    (hv : Q v ≠ 0) (hinv : (Q v)⁻¹ ∈ R) :
    toBongIsometry hQ hQ (IntegralReflection.isometry Q R L hInt v hvL hv hinv) =
      (quadraticSpace Q hQ).reflectionIsometry v
        (by simpa [Bong.QuadraticSpace.IsAnisotropic] using hv) := by
  apply Bong.QuadraticSpace.Isometry.ext
  intro x
  exact congrArg (fun f : V ≃ₗ[K] V ↦ f x) (reflectionLinearEquiv_eq Q hQ v hv)

variable [FiniteDimensional K V]

/-- The genuine Wall spinor norm of an integral lattice automorphism. -/
noncomputable def spinorNorm (hQ : Q.polarBilin.Nondegenerate)
    (e : LatticeIsometry Q Q L L) : Bong.Dyadic.SquareClass K :=
  Bong.QuadraticSpace.spinorNorm (toBongIsometry hQ hQ e)

/-- Integral composition preserves the upstream spinor-norm multiplication law. -/
theorem spinorNorm_compose (hQ : Q.polarBilin.Nondegenerate)
    (e f : LatticeIsometry Q Q L L) :
    spinorNorm hQ (e.compose f) = spinorNorm hQ e * spinorNorm hQ f := by
  unfold spinorNorm
  rw [toBongIsometry_compose, Bong.QuadraticSpace.spinorNorm_trans]

/-- An integral reflection has determinant minus one. -/
theorem det_integralReflection (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (R : Subring K) (L : Submodule R V)
    (hInt : ∀ x ∈ L, Q x ∈ R) (v : V) (hvL : v ∈ L)
    (hv : Q v ≠ 0) (hinv : (Q v)⁻¹ ∈ R) :
    LinearEquiv.det
      (IntegralReflection.isometry Q R L hInt v hvL hv hinv).toLinearEquiv =
      (-1 : Kˣ) := by
  change LinearEquiv.det (IntegralReflection.linearEquiv Q v hv) = (-1 : Kˣ)
  rw [reflectionLinearEquiv_eq Q hQ v hv]
  exact Bong.QuadraticSpace.det_reflectionLinearEquiv _ _

/-- The integral reflection's spinor norm is the square class of its quadratic value. -/
theorem spinorNorm_integralReflection (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (R : Subring K) (L : Submodule R V)
    (hInt : ∀ x ∈ L, Q x ∈ R) (v : V) (hvL : v ∈ L)
    (hv : Q v ≠ 0) (hinv : (Q v)⁻¹ ∈ R) :
    spinorNorm hQ (IntegralReflection.isometry Q R L hInt v hvL hv hinv) =
      Bong.Dyadic.squareClass K (Units.mk0 (Q v) hv) := by
  unfold spinorNorm
  rw [toBongIsometry_integralReflection, Bong.QuadraticSpace.spinorNorm_reflection]
  simp only [quadraticSpace_quadratic]

/-- If the integral lattice represents a unit and one, a proper integral isometry
has the prescribed unit square class as its spinor norm. -/
theorem exists_proper_isometry_of_represented_unit (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (R : Subring K) (L : Submodule R V)
    (hInt : ∀ x ∈ L, Q x ∈ R) (u : Rˣ)
    (hu : ∃ v ∈ L, Q v = ((u : R) : K)) (hOne : ∃ w ∈ L, Q w = 1) :
    ∃ e : LatticeIsometry Q Q L L, LinearEquiv.det e.toLinearEquiv = 1 ∧
      spinorNorm hQ e = Bong.Dyadic.squareClass K (Units.map R.subtype.toMonoidHom u) := by
  obtain ⟨v, hvL, hvu⟩ := hu
  obtain ⟨w, hwL, hwOne⟩ := hOne
  let uK : Kˣ := Units.map R.subtype.toMonoidHom u
  have hv : Q v ≠ 0 := by
    rw [hvu]
    exact Units.ne_zero uK
  have hw : Q w ≠ 0 := by simp [hwOne]
  have hvInv : (Q v)⁻¹ ∈ R := by
    have huInv : (uK : K)⁻¹ = (((u⁻¹ : Rˣ) : R) : K) := by
      rw [← Units.val_inv_eq_inv_val]
      rfl
    rw [hvu]
    change (uK : K)⁻¹ ∈ R
    rw [huInv]
    exact (↑(u⁻¹) : R).property
  have hwInv : (Q w)⁻¹ ∈ R := by rw [hwOne, inv_one]; exact R.one_mem
  let e := IntegralReflection.isometry Q R L hInt v hvL hv hvInv
  let f := IntegralReflection.isometry Q R L hInt w hwL hw hwInv
  refine ⟨e.compose f, ?_, ?_⟩
  · change LinearEquiv.det (e.toLinearEquiv.trans f.toLinearEquiv) = 1
    rw [LinearEquiv.det_trans]
    have he : LinearEquiv.det e.toLinearEquiv = (-1 : Kˣ) :=
      det_integralReflection Q hQ R L hInt v hvL hv hvInv
    have hf : LinearEquiv.det f.toLinearEquiv = (-1 : Kˣ) :=
      det_integralReflection Q hQ R L hInt w hwL hw hwInv
    rw [he, hf]
    simp
  · rw [spinorNorm_compose]
    have he : spinorNorm hQ e = Bong.Dyadic.squareClass K uK := by
      rw [spinorNorm_integralReflection]
      congr 1
      apply Units.ext
      exact hvu
    have hf : spinorNorm hQ f = 1 := by
      rw [spinorNorm_integralReflection]
      have hunit : Units.mk0 (Q w) hw = (1 : Kˣ) := by
        apply Units.ext
        exact hwOne
      rw [hunit]
      rfl
    rw [he, hf, mul_one]

end NormEuclidean.SpinorBridge

namespace NormEuclidean.CompletedIntegralLattice

open IsDedekindDomain

variable {K V : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- Characteristic zero is inherited from the global field by its actual completion. -/
instance localField_charZero : CharZero (LocalField R v) :=
  Algebra.charZero_of_charZero K (LocalField R v)

/-- At each actual finite completion, every local unit square class is the spinor
norm of a proper integral automorphism of the completed hyperbolic extension.
This includes dyadic places: two is inverted only in the ambient field. -/
theorem hyperbolic_exists_proper_isometry_unit (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q) (u : (LocalRing R v)ˣ) :
    ∃ e : LatticeIsometry (form R v (Hyperbolic.form Q))
        (form R v (Hyperbolic.form Q))
        (carrier R v L.hyperbolic.carrier) (carrier R v L.hyperbolic.carrier),
      LinearEquiv.det e.toLinearEquiv = 1 ∧
        SpinorBridge.spinorNorm (hyperbolic_form_polarBilin_nondegenerate R v Q hQ) e =
          Bong.Dyadic.squareClass (LocalField R v)
            (Units.map (LocalRing R v).subtype.toMonoidHom u) := by
  apply SpinorBridge.exists_proper_isometry_of_represented_unit
    (form R v (Hyperbolic.form Q))
    (hyperbolic_form_polarBilin_nondegenerate R v Q hQ)
    (LocalRing R v) (carrier R v L.hyperbolic.carrier)
    (carrier_integral R v (Hyperbolic.form Q) L.hyperbolic.carrier L.hyperbolic.integral) u
  · exact hyperbolic_represents R v Q L.carrier (u : LocalRing R v)
  · exact hyperbolic_represents R v Q L.carrier (1 : LocalRing R v)

end NormEuclidean.CompletedIntegralLattice
