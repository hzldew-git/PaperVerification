import NormEuclidean.HyperbolicUnipotent

/-!
# The two opposite actual hyperbolic unipotent families

The coordinate swap conjugates the existing proper unipotent to the opposite
one. Conjugation preserves the actual Wall spinor norm and full integral
carrier, without requiring the swap itself to have determinant one.
-/

noncomputable section

namespace NormEuclidean.OppositeHyperbolicUnipotent

open ProperSpinor HyperbolicUnipotent

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)

/-- The actual orthogonal coordinate swap, with no properness assertion. -/
def swapAmbient : ambientGroup (Hyperbolic.form Q) :=
  ⟨Hyperbolic.swapEquiv, Hyperbolic.q_swap Q⟩

/-- Conjugation by the coordinate swap preserves the determinant-one subgroup. -/
def conjugate (g : properGroup (Hyperbolic.form Q)) : properGroup (Hyperbolic.form Q) :=
  ⟨swapAmbient Q * g.1 * (swapAmbient Q)⁻¹, by
    change determinantHom (Hyperbolic.form Q)
      (swapAmbient Q * g.1 * (swapAmbient Q)⁻¹) = 1
    rw [map_mul, map_mul, map_inv, show determinantHom (Hyperbolic.form Q) g.1 = 1 from g.2]
    simp⟩

/-- Conjugation has exactly the expected coordinate action. -/
theorem conjugate_apply (g : properGroup (Hyperbolic.form Q)) (z : Hyperbolic F E) :
    (conjugate Q g).1.1 z = Hyperbolic.swap (g.1.1 (Hyperbolic.swap z)) := rfl

/-- The second actual proper unipotent family. -/
def element (hA : Q.Anisotropic) (u : E) : properGroup (Hyperbolic.form Q) :=
  conjugate Q (HyperbolicUnipotent.element Q hQ hA u)

/-- The opposite family in full hyperbolic coordinates. -/
theorem element_apply (hA : Q.Anisotropic) (u : E) (z : Hyperbolic F E) :
    (element Q hQ hA u).1.1 z =
      (z.1 - z.2.2 • u, z.2.1 + QuadraticMap.polar Q z.1 u - z.2.2 * Q u, z.2.2) := by
  rw [element, conjugate_apply, HyperbolicUnipotent.element_apply]
  rfl

/-- Opposite unipotents also lie in the genuine proper Wall kernel. -/
theorem element_spinorNorm (hA : Q.Anisotropic) (u : E) :
    properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) (element Q hQ hA u) = 1 := by
  let theta := ambientSpinorNormHom (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
  have hu : theta (HyperbolicUnipotent.element Q hQ hA u).1 = 1 :=
    HyperbolicUnipotent.element_spinorNorm Q hQ hA u
  change theta (swapAmbient Q * (HyperbolicUnipotent.element Q hQ hA u).1 *
    (swapAmbient Q)⁻¹) = 1
  rw [map_mul, map_mul, map_inv, hu, mul_one, mul_inv_cancel]

/-- Opposite integral parameters preserve the whole hyperbolic integral module. -/
theorem element_integral (hA : Q.Anisotropic) (R : Subring F) (L : Submodule R E)
    (hInt : ∀ x ∈ L, Q x ∈ R) (u : E) (hu : u ∈ L) (z : Hyperbolic F E) :
    (element Q hQ hA u).1.1 z ∈ Hyperbolic.submodule L ↔ z ∈ Hyperbolic.submodule L := by
  rw [element, conjugate_apply]
  change Hyperbolic.Mem L
    (Hyperbolic.swap ((HyperbolicUnipotent.element Q hQ hA u).1.1 (Hyperbolic.swap z))) ↔ _
  rw [Hyperbolic.mem_swap]
  exact (HyperbolicUnipotent.element_integral Q hQ hA R L hInt u hu
    (Hyperbolic.swap z)).trans (Hyperbolic.mem_swap L z)

end NormEuclidean.OppositeHyperbolicUnipotent
