import NormEuclidean.ChapterX.OrthogonalTransport
import NormEuclidean.AllPlaceGenus

/-!
# Wall spinor norms under adjoining a hyperbolic plane

The actual block embedding sends each reflection to the reflection in the
included vector. Reflection-word induction proves preservation of the Wall
spinor norm, without a rank or local isotropy assumption.
-/

noncomputable section

namespace NormEuclidean.HyperbolicSpinorMap

open ProperSpinor SpinorBaseChange CommutatorGeneration

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Extend an actual orthogonal transformation by the identity on the plane. -/
def ambientMap : ambientGroup Q →* ambientGroup (Hyperbolic.form Q) where
  toFun g := ⟨g.1.prodCongr (LinearEquiv.refl F (F × F)), fun z ↦ by
    change Q (g.1 z.1) + z.2.1 * z.2.2 = Q z.1 + z.2.1 * z.2.2
    rw [g.2]⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    rfl

@[simp] theorem ambientMap_apply (g : ambientGroup Q) (z : Hyperbolic F V) :
    (ambientMap Q g).1 z = (g.1 z.1, z.2) := rfl

variable [FiniteDimensional F V]

/-- The block embedding preserves the determinant character. -/
theorem determinant_map (g : ambientGroup Q) :
    determinantHom (Hyperbolic.form Q) (ambientMap Q g) = determinantHom Q g := by
  apply Units.ext
  rw [determinantHom_apply, determinantHom_apply, LinearEquiv.coe_det, LinearEquiv.coe_det]
  change (LinearMap.prodMap g.1.toLinearMap (LinearMap.id : (F × F) →ₗ[F] F × F)).det = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, mul_one]

/-- The induced homomorphism on the actual proper orthogonal groups. -/
def properMap : properGroup Q →* properGroup (Hyperbolic.form Q) where
  toFun g := ⟨ambientMap Q g.1, by
    change determinantHom (Hyperbolic.form Q) (ambientMap Q g.1) = 1
    rw [determinant_map]
    exact g.2⟩
  map_one' := Subtype.ext (map_one (ambientMap Q))
  map_mul' g h := Subtype.ext (map_mul (ambientMap Q) g.1 h.1)

variable [CharZero F]

/-- A reflection extends to the reflection in the included original vector. -/
theorem reflection_map (x : V) (hx : Q x ≠ 0) :
    ambientMap Q (ambientReflection Q x hx) =
      ambientReflection (Hyperbolic.form Q) (x, 0, 0) (by simpa [Hyperbolic.q] using hx) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  have hp : QuadraticMap.polar (Hyperbolic.form Q) (x, 0, 0) z =
      QuadraticMap.polar Q x z.1 := by
    simp only [QuadraticMap.polar, Hyperbolic.form_apply, Hyperbolic.q,
      Prod.fst_add, Prod.snd_add, zero_add, zero_mul, add_zero]
    ring
  change (IntegralReflection.linearEquiv Q x hx z.1, z.2) =
    IntegralReflection.linearEquiv (Hyperbolic.form Q) (x, 0, 0)
      (by simpa [Hyperbolic.q] using hx) z
  rw [IntegralReflection.linearEquiv_apply, IntegralReflection.linearEquiv_apply, hp]
  ext <;> simp [Hyperbolic.q]

/-- The actual ambient Wall spinor norm is unchanged by the block embedding. -/
theorem spinorNorm_map (hQ : Q.polarBilin.Nondegenerate) (g : ambientGroup Q) :
    ambientSpinorNormHom (Hyperbolic.form Q) (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
      (ambientMap Q g) = ambientSpinorNormHom Q hQ g := by
  apply ambient_induction Q hQ
    (fun g ↦ ambientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) (ambientMap Q g) =
        ambientSpinorNormHom Q hQ g)
  · simp only [map_one]
  · intro g h hg hh
    simp only [map_mul, hg, hh]
  · intro x hx
    rw [reflection_map, ambientReflection_spinorNorm, ambientReflection_spinorNorm]
    congr 1
    exact Units.ext (by simp [Hyperbolic.q])

/-- The same equality on actual proper transformations. -/
theorem proper_spinorNorm_map (hQ : Q.polarBilin.Nondegenerate) (g : properGroup Q) :
    properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) (properMap Q g) =
        properAmbientSpinorNormHom Q hQ g := spinorNorm_map Q hQ g.1

end NormEuclidean.HyperbolicSpinorMap
