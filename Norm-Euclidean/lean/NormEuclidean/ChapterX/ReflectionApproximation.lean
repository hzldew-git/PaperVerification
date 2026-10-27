import NormEuclidean.ChapterX.MatrixValuation
import NormEuclidean.SpinorBaseChange

/-!
# Reflection pairs used in O'Meara 104:4, step 1(a)

Equal nonzero quadratic values put a pair of reflections in the actual Wall
spinor kernel. The pair varies continuously with the reflecting vectors and
is integral when both reflecting vectors have integral unit quadratic value.
These are proved construction lemmas, not an assertion of global approximation.
-/

noncomputable section

namespace NormEuclidean.ReflectionApproximation

open ProperSpinor SpinorBaseChange AdelicOrthogonal Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E]
variable (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)

/-- Reflections in equal nonzero quadratic values give an actual proper
isometry in the Wall spinor kernel, as in O'Meara 104:4, step 1(a). -/
theorem doubleReflection_spinorNorm_eq_one_of_value_eq
    (x : E) (hx : Q x ≠ 0) (y : E) (hy : Q y ≠ 0) (hxy : Q x = Q y) :
    properAmbientSpinorNormHom Q hQ (doubleReflection Q hQ x hx y hy) = 1 := by
  rw [doubleReflection_spinorNorm]
  have heq : Units.mk0 (Q y) hy = Units.mk0 (Q x) hx := Units.ext hxy.symm
  rw [heq, show Units.mk0 (Q x) hx * Units.mk0 (Q x) hx =
    (1 : Fˣ) * (Units.mk0 (Q x) hx) ^ 2 by simp [pow_two],
    Bong.Dyadic.squareClass_mul_square]
  rfl

/-- A pair of identical reflections is the identity transformation. -/
theorem doubleReflection_self (x : E) (hx : Q x ≠ 0) :
    doubleReflection Q hQ x hx x hx = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro y
  exact IntegralReflection.involutive Q x hx y

omit [CharZero F] [FiniteDimensional F E] in
theorem ambientReflection_inv (x : E) (hx : Q x ≠ 0) :
    (ambientReflection Q x hx)⁻¹ = ambientReflection Q x hx := by
  apply Subtype.ext
  change (IntegralReflection.linearEquiv Q x hx).symm =
    IntegralReflection.linearEquiv Q x hx
  simp only [IntegralReflection.linearEquiv, Module.reflection_symm]

omit [CharZero F] [FiniteDimensional F E] in
theorem polar_ambient (g : ambientGroup Q) (x y : E) :
    QuadraticMap.polar Q (g.1 x) (g.1 y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar]
  rw [← g.1.map_add, g.2, g.2, g.2]

omit [CharZero F] [FiniteDimensional F E] in
/-- Conjugation carries an actual reflection to the reflection in the image vector. -/
theorem ambientReflection_conjugate (g : ambientGroup Q) (x : E) (hx : Q x ≠ 0) :
    g * ambientReflection Q x hx * g⁻¹ =
      ambientReflection Q (g.1 x) ((g.2 x).trans_ne hx) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  change g.1 (IntegralReflection.linearEquiv Q x hx (g.1.symm z)) =
    IntegralReflection.linearEquiv Q (g.1 x) ((g.2 x).trans_ne hx) z
  rw [IntegralReflection.linearEquiv_apply, IntegralReflection.linearEquiv_apply,
    map_sub, map_smul, LinearEquiv.apply_symm_apply, g.2 x]
  have hp := polar_ambient Q g x (g.1.symm z)
  rw [LinearEquiv.apply_symm_apply] at hp
  rw [hp]

/-- The short commutator of 104:4, step 1(a), reduces to two reflections
in vectors of the same nonzero quadratic value. -/
theorem shortCommutator_eq_doubleReflection
    (x : E) (hx : Q x ≠ 0) (y : E) (hy : Q y ≠ 0) :
    (doubleReflection Q hQ x hx y hy) ^ 2 =
      doubleReflection Q hQ x hx ((ambientReflection Q y hy).1 x)
        (((ambientReflection Q y hy).2 x).trans_ne hx) := by
  apply Subtype.ext
  change (ambientReflection Q x hx * ambientReflection Q y hy) ^ 2 =
    ambientReflection Q x hx * ambientReflection Q ((ambientReflection Q y hy).1 x) _
  have hc := ambientReflection_conjugate Q (ambientReflection Q y hy) x hx
  rw [ambientReflection_inv] at hc
  rw [pow_two, ← hc]
  simp only [mul_assoc]

theorem shortCommutator_spinorNorm_eq_one
    (x : E) (hx : Q x ≠ 0) (y : E) (hy : Q y ≠ 0) :
    properAmbientSpinorNormHom Q hQ ((doubleReflection Q hQ x hx y hy) ^ 2) = 1 := by
  rw [shortCommutator_eq_doubleReflection]
  exact doubleReflection_spinorNorm_eq_one_of_value_eq Q hQ x hx _ _
    ((ambientReflection Q y hy).2 x).symm

/-- The integral step in O'Meara 104:4, step 1(a). It also applies at
residue characteristic two because the polar form is unhalved. -/
theorem doubleReflection_mem_properStabilizerWithin (R : Subring F) (L : Submodule R E)
    (hL : ∀ z ∈ L, Q z ∈ R)
    (x : E) (hx : Q x ≠ 0) (hxL : x ∈ L) (hxinv : (Q x)⁻¹ ∈ R)
    (y : E) (hy : Q y ≠ 0) (hyL : y ∈ L) (hyinv : (Q y)⁻¹ ∈ R) :
    doubleReflection Q hQ x hx y hy ∈ properStabilizerWithin Q L := by
  intro z
  change IntegralReflection.linearEquiv Q x hx
    (IntegralReflection.linearEquiv Q y hy z) ∈ L ↔ z ∈ L
  exact ((IntegralReflection.isometry Q R L hL x hxL hx hxinv).mem_iff _).trans
    ((IntegralReflection.isometry Q R L hL y hyL hy hyinv).mem_iff z)

section Topology

open OrthogonalTopology

variable [TopologicalSpace F] [IsTopologicalRing F] [ContinuousInv₀ F]
  [TopologicalSpace E] [IsModuleTopology F E] [Invertible (2 : F)]

/-- The actual proper two-reflection map is continuous on its natural domain. -/
theorem continuous_doubleReflection :
    Continuous (fun p : {x : E // Q x ≠ 0} × {y : E // Q y ≠ 0} ↦
      doubleReflection Q hQ p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (fun p : {x : E // Q x ≠ 0} × {y : E // Q y ≠ 0} ↦
    IntegralReflection.linearEquiv Q p.1.1 p.1.2 *
      IntegralReflection.linearEquiv Q p.2.1 p.2.2)
  exact ((continuous_reflection Q).comp continuous_fst).mul
    ((continuous_reflection Q).comp continuous_snd)

/-- Fixing the first vector and restricting the second to the same
quadratic value gives a continuous family entirely in the spinor kernel. -/
theorem continuous_sameValue_doubleReflection (x : E) (hx : Q x ≠ 0) :
    Continuous (fun y : {y : E // Q y = Q x} ↦
      doubleReflection Q hQ x hx y.1 (y.2.trans_ne hx)) := by
  have hy : Continuous (fun y : {y : E // Q y = Q x} ↦
      (⟨y.1, y.2.trans_ne hx⟩ : {y : E // Q y ≠ 0})) :=
    continuous_subtype_val.subtype_mk (fun y ↦ y.2.trans_ne hx)
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (fun y : {y : E // Q y = Q x} ↦
    IntegralReflection.linearEquiv Q x hx *
      IntegralReflection.linearEquiv Q y.1 (y.2.trans_ne hx))
  have hr : Continuous (fun y : {y : E // Q y = Q x} ↦
      IntegralReflection.linearEquiv Q y.1 (y.2.trans_ne hx)) :=
    (continuous_reflection Q).comp hy
  exact continuous_const.mul hr

/-- Every local transformation neighborhood can be met by taking the
replacement reflecting vector sufficiently close inside the fixed-value fiber.
The conclusion concerns local continuity; it supplies no global vector. -/
theorem sameValue_doubleReflection_preimage_mem_nhds
    (x : E) (hx : Q x ≠ 0) (y : {y : E // Q y = Q x})
    (U : Set (properGroup Q))
    (hU : U ∈ 𝓝 (doubleReflection Q hQ x hx y.1 (y.2.trans_ne hx))) :
    {z : {z : E // Q z = Q x} |
      doubleReflection Q hQ x hx z.1 (z.2.trans_ne hx) ∈ U} ∈ 𝓝 y :=
  (continuous_sameValue_doubleReflection Q hQ x hx).continuousAt.preimage_mem_nhds hU

/-- Near the original reflecting vector the pair lies in any prescribed
identity neighborhood. This controls the extra finite places in 104:4, step 1(a). -/
theorem sameValue_doubleReflection_identity_preimage_mem_nhds
    (x : E) (hx : Q x ≠ 0) (U : Set (properGroup Q)) (hU : U ∈ 𝓝 1) :
    {z : {z : E // Q z = Q x} |
      doubleReflection Q hQ x hx z.1 (z.2.trans_ne hx) ∈ U} ∈
        𝓝 (⟨x, rfl⟩ : {z : E // Q z = Q x}) := by
  apply sameValue_doubleReflection_preimage_mem_nhds Q hQ x hx ⟨x, rfl⟩ U
  simpa only [doubleReflection_self] using hU

end Topology

section Completions

open CompletedIntegralLattice AdelicApproximation AdelicSpinorKernel IsDedekindDomain

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (P : QuadraticForm K V) (hP : P.polarBilin.Nondegenerate)

/-- The same actual global reflection pair has trivial Wall spinor norm
at every finite completion, without assuming general spinor-norm naturality. -/
theorem finiteDiagonal_doubleReflection_inSpinorKernel
    (L : Lattice (integerSubring K) P)
    (x : V) (hx : P x ≠ 0) (y : V) (hy : P y ≠ 0) (hxy : P x = P y) :
    InSpinorKernel P hP L (finiteDiagonal P L (doubleReflection P hP x hx y hy)) := by
  intro v
  have heq : localizeProper P (doubleReflection P hP x hx y hy) v =
      doubleReflection (form (integerSubring K) v P)
        (form_polarBilin_nondegenerate (integerSubring K) v P hP)
        (inclusion (integerSubring K) v x)
        (form_inclusion_ne_zero (integerSubring K) v P x hx)
        (inclusion (integerSubring K) v y)
        (form_inclusion_ne_zero (integerSubring K) v P y hy) := by
    apply Subtype.ext
    apply Subtype.ext
    exact equiv_doubleReflection P (integerSubring K) hP x hx y hy v
  change properAmbientSpinorNormHom (form (integerSubring K) v P)
    (form_polarBilin_nondegenerate (integerSubring K) v P hP)
    (localizeProper P (doubleReflection P hP x hx y hy) v) = 1
  rw [heq]
  apply doubleReflection_spinorNorm_eq_one_of_value_eq
  rw [form_inclusion, form_inclusion, hxy]

end Completions

end NormEuclidean.ReflectionApproximation
