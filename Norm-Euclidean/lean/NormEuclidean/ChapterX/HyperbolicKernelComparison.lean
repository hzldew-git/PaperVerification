import NormEuclidean.ChapterX.HyperbolicAbelianization
import NormEuclidean.ChapterX.ReflectionAbelianization

/-!
# The actual spinor kernel in a space containing a hyperbolic plane

Conjugacy of equal-value reflections and the explicit hyperbolic dilation
identify the proper Wall kernel with the ambient commutator subgroup.
The comparison holds over every characteristic-zero field, without a
local-field classification premise or assumed generation law.
-/

noncomputable section

namespace NormEuclidean.HyperbolicKernelComparison

open ProperSpinor SpinorBaseChange ReflectionApproximation ProperReflectionGeneration
  CommutatorSquares HyperbolicAbelianization FixedValueTransitivity

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)

include hQ in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Equal-value transitivity identifies any reflection with its hyperbolic representative. -/
theorem reflection_class (x : Hyperbolic F E) (hx : Hyperbolic.form Q x ≠ 0) :
    Abelianization.of (ambientReflection (Hyperbolic.form Q) x hx) =
      Abelianization.of (ambientReflection (Hyperbolic.form Q)
        (vector (Units.mk0 (Hyperbolic.form Q x) hx))
        (by simpa only [value_vector, Units.val_mk0] using hx)) := by
  exact ReflectionAbelianization.class_of_equal_value (Hyperbolic.form Q) x
    (vector (Units.mk0 (Hyperbolic.form Q x) hx)) hx _
    (by simp only [value_vector, Units.val_mk0])

/-- The hyperbolic scalar representative differs from a reflection by one fixed reflection. -/
theorem canonical_class (a : Fˣ) :
    Abelianization.of (ambientReflection (Hyperbolic.form Q) (vector a)
      (by simp [vector, Hyperbolic.q])) = scalarAbelianization Q hQ a *
        Abelianization.of (ambientReflection (Hyperbolic.form Q) (vector (1 : Fˣ))
          (by simp [vector, Hyperbolic.q])) := by
  let r := ambientReflection (Hyperbolic.form Q) (vector (1 : Fˣ))
    (by simp [vector, Hyperbolic.q])
  let s := ambientReflection (Hyperbolic.form Q) (vector a)
    (by simp [vector, Hyperbolic.q])
  change Abelianization.of s = Abelianization.of (s * r) * Abelianization.of r
  have hr : Abelianization.of r * Abelianization.of r = 1 := by
    have hs : r * r = 1 := by
      simpa only [pow_two] using reflection_sq (Hyperbolic.form Q) (vector (1 : Fˣ))
        (by simp [vector, Hyperbolic.q])
    rw [← map_mul, hs, map_one]
  calc
    _ = Abelianization.of s * 1 := (mul_one _).symm
    _ = Abelianization.of s * (Abelianization.of r * Abelianization.of r) := by rw [hr]
    _ = _ := by rw [map_mul, mul_assoc]

/-- The two actual homomorphisms agree on each anisotropic reflection pair. -/
theorem pair_class (x : Hyperbolic F E) (hx : Hyperbolic.form Q x ≠ 0)
    (y : Hyperbolic F E) (hy : Hyperbolic.form Q y ≠ 0) :
    Abelianization.of (doubleReflection (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) x hx y hy).1 =
    squareClassAbelianization Q hQ (properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
      (doubleReflection (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ) x hx y hy)) := by
  rw [doubleReflection_spinorNorm, squareClassAbelianization_apply]
  change Abelianization.of (ambientReflection (Hyperbolic.form Q) x hx *
    ambientReflection (Hyperbolic.form Q) y hy) = _
  rw [map_mul, reflection_class Q hQ x hx, reflection_class Q hQ y hy,
    canonical_class Q hQ (Units.mk0 (Hyperbolic.form Q x) hx),
    canonical_class Q hQ (Units.mk0 (Hyperbolic.form Q y) hy)]
  let r := ambientReflection (Hyperbolic.form Q) (vector (1 : Fˣ))
    (by simp [vector, Hyperbolic.q])
  have hr : Abelianization.of r * Abelianization.of r = 1 := by
    rw [← pow_two, ← map_pow, reflection_sq, map_one]
  calc
    _ = (scalarAbelianization Q hQ (Units.mk0 (Hyperbolic.form Q x) hx) *
        scalarAbelianization Q hQ (Units.mk0 (Hyperbolic.form Q y) hy)) *
          (Abelianization.of r * Abelianization.of r) := by ac_rfl
    _ = _ := by rw [hr, mul_one, map_mul]

/-- Proper abelianization is computed by the actual Wall spinor square class. -/
theorem proper_class (g : properGroup (Hyperbolic.form Q)) :
    Abelianization.of g.1 = squareClassAbelianization Q hQ
      (properAmbientSpinorNormHom (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ) g) := by
  let f := Abelianization.of.comp (properGroup (Hyperbolic.form Q)).subtype
  let h := (squareClassAbelianization Q hQ).comp
    (properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
  exact proper_mem_of_contains_doubleReflections (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ) (f.eqLocus h)
    (fun x hx y hy ↦ pair_class Q hQ x hx y hy) g

/-- In a hyperbolic extension the actual proper Wall kernel is the ambient derived group. -/
theorem kernel_iff_commutator (g : properGroup (Hyperbolic.form Q)) :
    properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) g = 1 ↔
        g.1 ∈ commutator (ambientGroup (Hyperbolic.form Q)) := by
  constructor
  · intro hg
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, proper_class Q hQ g, hg, map_one]
  · intro hg
    exact Abelianization.commutator_subset_ker
      (ambientSpinorNormHom (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) hg

end NormEuclidean.HyperbolicKernelComparison
