import NormEuclidean.ChapterX.OrthogonalTransport
import NormEuclidean.ChapterX.OrthogonalTopology

/-!
# Multiplicative and continuous transport of actual proper orthogonal groups
-/

noncomputable section

namespace NormEuclidean.ProperIsometryTransport

open ProperSpinor OrthogonalTransport OrthogonalTopology
open scoped NormEuclidean.OrthogonalTopology

variable {F E W : Type*} [Field F] [CharZero F]
  [AddCommGroup E] [Module F E] [AddCommGroup W] [Module F W]
  [FiniteDimensional F E] [FiniteDimensional F W]
  (Q : QuadraticForm F E) (P : QuadraticForm F W)
  (e : E ≃ₗ[F] W) (he : ∀ x, P (e x) = Q x)

/-- Conjugation as a homomorphism on the actual proper groups. -/
def hom : properGroup Q →* properGroup P where
  toFun := properMap Q P e he
  map_one' := Subtype.ext (map_one (ambientMap Q P e he))
  map_mul' g h := Subtype.ext (map_mul (ambientMap Q P e he) g.1 h.1)

/-- Conjugation as an equivalence of the actual proper groups. -/
def equiv : properGroup Q ≃* properGroup P where
  toFun := hom Q P e he
  invFun := hom P Q e.symm (inverse_value Q P e he)
  left_inv g := Subtype.ext ((ambientEquiv Q P e he).left_inv g.1)
  right_inv g := Subtype.ext ((ambientEquiv Q P e he).right_inv g.1)
  map_mul' := (hom Q P e he).map_mul

@[simp] theorem hom_apply (g : properGroup Q) (z : W) :
    (hom Q P e he g).1.1 z = e (g.1.1 (e.symm z)) := rfl

variable [TopologicalSpace F] [IsTopologicalRing F] [ContinuousInv₀ F]
  [TopologicalSpace E] [IsModuleTopology F E]
  [TopologicalSpace W] [IsModuleTopology F W]

/-- Actual isometric conjugation is continuous in the orthogonal group topology. -/
theorem continuous_hom : Continuous (hom Q P e he) := by
  letI := IsModuleTopology.topologicalAddGroup F W
  apply (isInducing_properLinearMap P).continuous_iff.mpr
  apply (continuous_end_iff_apply _).mpr
  intro z
  exact (IsModuleTopology.continuous_of_linearMap e.toLinearMap).comp
    (continuous_proper_apply Q (e.symm z))

end NormEuclidean.ProperIsometryTransport
