import NormEuclidean.CompletedIntegralLattice
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Nondegeneracy survives extension of fields

A finite-dimensional bilinear form has an invertible Gram matrix exactly when
it is nondegenerate. The Gram matrix after base change is the entrywise image
of the original matrix, so its determinant remains nonzero. This supplies
nondegeneracy of genuine quadratic scalar extensions, including finite
completions, without a local-nondegeneracy hypothesis.
-/

open scoped TensorProduct

namespace NormEuclidean

variable {K A V : Type*} [Field K] [Field A] [Algebra K A]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Scalar extension to any field preserves nondegeneracy of a finite-dimensional
bilinear form. The determinant argument requires no choice of an integral basis. -/
theorem bilinForm_baseChange_separatingLeft (B : LinearMap.BilinForm K V)
    (hB : B.SeparatingLeft) : (B.baseChange A).SeparatingLeft := by
  classical
  let b := Module.finBasis K V
  have hmatrix : LinearMap.BilinForm.toMatrix (b.baseChange A) (B.baseChange A) =
      (LinearMap.BilinForm.toMatrix b B).map (algebraMap K A) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
      LinearMap.BilinForm.baseChange_tmul, Matrix.map_apply, one_mul, mul_one,
      Algebra.smul_def]
  have hdet :
      (LinearMap.BilinForm.toMatrix (b.baseChange A) (B.baseChange A)).det ≠ 0 := by
    rw [hmatrix, ← RingHom.mapMatrix_apply, ← (algebraMap K A).map_det]
    exact (map_ne_zero (algebraMap K A)).2
      ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1
        (LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hB))
  exact (LinearMap.BilinForm.nondegenerate_of_det_ne_zero
    (B.baseChange A) (b.baseChange A) hdet).1

/-- Both left and right nondegeneracy survive field extension. -/
theorem bilinForm_baseChange_nondegenerate (B : LinearMap.BilinForm K V)
    (hB : LinearMap.Nondegenerate B) : LinearMap.Nondegenerate (B.baseChange A) := by
  exact LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    (bilinForm_baseChange_separatingLeft (A := A) B hB.1)

variable [Invertible (2 : K)] [Invertible (2 : A)]

/-- The polar bilinear form remains nondegenerate under extension of fields. -/
theorem quadraticForm_baseChange_polarBilin_nondegenerate (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) : (Q.baseChange A).polarBilin.Nondegenerate := by
  rw [QuadraticForm.polarBilin_baseChange]
  exact bilinForm_baseChange_nondegenerate Q.polarBilin hQ

/-- The associated bilinear form remains nondegenerate under extension of fields. -/
theorem quadraticForm_baseChange_associated_nondegenerate (Q : QuadraticForm K V)
    (hQ : Q.associated.Nondegenerate) : (Q.baseChange A).associated.Nondegenerate := by
  rw [QuadraticForm.associated_baseChange]
  exact bilinForm_baseChange_nondegenerate Q.associated hQ

end NormEuclidean

namespace NormEuclidean

variable {K V : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]

/-- Anisotropy implies nondegeneracy of the polar bilinear form in characteristic
different from two; no finite-dimensional hypothesis is needed. -/
theorem quadraticForm_polarBilin_nondegenerate_of_anisotropic (Q : QuadraticForm K V)
    (hQ : Q.Anisotropic) : Q.polarBilin.Nondegenerate := by
  have hleft : Q.polarBilin.SeparatingLeft := by
    intro x hx
    apply hQ x
    have h : (2 : K) * Q x = 0 := by
      simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
        two_smul, two_mul] using hx x
    exact (mul_eq_zero.mp h).resolve_left (Invertible.ne_zero (2 : K))
  refine ⟨hleft, ?_⟩
  intro z hz
  apply hleft z
  intro w
  simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using hz w

end NormEuclidean

namespace NormEuclidean.Hyperbolic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Adjoining a standard hyperbolic plane preserves nondegeneracy of the polar
bilinear form. This algebraic fact does not require finite dimension. -/
theorem form_polarBilin_nondegenerate (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) : (form Q).polarBilin.Nondegenerate := by
  have hp (z w : Hyperbolic K V) :
      (form Q).polarBilin z w =
        Q.polarBilin z.1 w.1 + z.2.1 * w.2.2 + w.2.1 * z.2.2 := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      form_apply, q, Prod.fst_add, Prod.snd_add]
    ring
  have hleft : (form Q).polarBilin.SeparatingLeft := by
    intro z hz
    have ha : z.2.1 = 0 := by
      simpa [hp, f] using hz f
    have hb : z.2.2 = 0 := by
      simpa [hp, e] using hz e
    have hx : z.1 = 0 := hQ.1 z.1 (fun w => by
      simpa [hp, embed] using hz (embed w))
    exact Prod.ext hx (Prod.ext ha hb)
  refine ⟨hleft, ?_⟩
  intro z hz
  apply hleft z
  intro w
  simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using hz w

end NormEuclidean.Hyperbolic

namespace NormEuclidean.CompletedIntegralLattice

open IsDedekindDomain
variable {K V : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- The genuinely completed quadratic space is nondegenerate whenever the
original finite-dimensional quadratic space is nondegenerate. -/
theorem form_polarBilin_nondegenerate (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) : (form R v Q).polarBilin.Nondegenerate := by
  letI : Invertible (2 : LocalField R v) :=
    (Invertible.map (algebraMap K (LocalField R v)) 2).copy 2 (map_ofNat _ _).symm
  exact quadraticForm_baseChange_polarBilin_nondegenerate Q hQ

/-- The genuine completed hyperbolic extension is nondegenerate, derived from
the original form rather than assumed as a local input. -/
theorem hyperbolic_form_polarBilin_nondegenerate (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) :
    (form R v (Hyperbolic.form Q)).polarBilin.Nondegenerate :=
  form_polarBilin_nondegenerate R v (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ)

/-- An anisotropic global space has nondegenerate completed hyperbolic
extensions at every finite place. -/
theorem hyperbolic_form_polarBilin_nondegenerate_of_anisotropic (Q : QuadraticForm K V)
    (hQ : Q.Anisotropic) :
    (form R v (Hyperbolic.form Q)).polarBilin.Nondegenerate :=
  hyperbolic_form_polarBilin_nondegenerate R v Q
    (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hQ)

end NormEuclidean.CompletedIntegralLattice
