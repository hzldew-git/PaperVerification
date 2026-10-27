import NormEuclidean.UnipotentContinuity
import NormEuclidean.ProperIsometryTransport
import NormEuclidean.CompletedHyperbolic
import NormEuclidean.ChapterX.CompletedTopology

/-!
# Actual finite completions of the two ternary unipotent families
-/

noncomputable section

namespace NormEuclidean.CompletedUnipotent

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicApproximation
  TernaryKernelGeneration QuadraticMap
open scoped TensorProduct NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)

local instance finiteCharZero (p : HeightOneSpectrum (integerSubring K)) :
    CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _

theorem local_finrank (hdim : Module.finrank K V = 1)
    (p : HeightOneSpectrum (integerSubring K)) :
    Module.finrank (LocalField (integerSubring K) p) (Space (V := V) (integerSubring K) p) =
      1 := by
  simp only [Space, Module.finrank_tensorProduct, Module.finrank_self, one_mul, hdim]

/-- The actual proper orthogonal group in tensor coordinates equals the product-coordinate group. -/
def toChart (p : HeightOneSpectrum (integerSubring K)) :
    properGroup (form (integerSubring K) p (Hyperbolic.form Q)) ≃*
      properGroup (Hyperbolic.form (form (integerSubring K) p Q)) :=
  ProperIsometryTransport.equiv _ _ (hyperbolicEquiv (integerSubring K) p)
    (hyperbolicEquiv_form (integerSubring K) p Q)

/-- The opposite unipotents, on the actual tensor-product completion of the global space. -/
def localFamily (hdim : Module.finrank K V = 1)
    (p : HeightOneSpectrum (integerSubring K)) (u : V) (b : Bool)
    (t : LocalField (integerSubring K) p) :
    properGroup (form (integerSubring K) p (Hyperbolic.form Q)) :=
  (toChart Q p).symm (family (form (integerSubring K) p Q)
    (form_polarBilin_nondegenerate _ p Q hQ)
    (UnaryClassNumber.anisotropic _ (form_polarBilin_nondegenerate _ p Q hQ)
      (local_finrank hdim p)) b (t • inclusion _ p u))

theorem inclusion_field_smul (p : HeightOneSpectrum (integerSubring K)) (a : K) (x : V) :
    inclusion (integerSubring K) p (a • x) =
      algebraMap K (LocalField (integerSubring K) p) a • inclusion (integerSubring K) p x := by
  rw [map_smul, IsScalarTower.algebraMap_smul]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Actual scalar extension of a unipotent agrees with its product-coordinate formula. -/
theorem toChart_family (hdim : Module.finrank K V = 1) (hA : Q.Anisotropic)
    (p : HeightOneSpectrum (integerSubring K)) (b : Bool) (u : V) :
    toChart Q p (localizeProper (Hyperbolic.form Q) (family Q hQ hA b u) p) =
      family (form (integerSubring K) p Q) (form_polarBilin_nondegenerate _ p Q hQ)
        (UnaryClassNumber.anisotropic _ (form_polarBilin_nondegenerate _ p Q hQ)
          (local_finrank hdim p)) b (inclusion _ p u) := by
  let e := hyperbolicEquiv (V := V) (integerSubring K) p
  let g := localizeProper (Hyperbolic.form Q) (family Q hQ hA b u) p
  let f := family (form (integerSubring K) p Q)
    (form_polarBilin_nondegenerate _ p Q hQ)
    (UnaryClassNumber.anisotropic _ (form_polarBilin_nondegenerate _ p Q hQ)
      (local_finrank hdim p)) b (inclusion _ p u)
  have hp (x y : V) : polar (form (integerSubring K) p Q)
      (inclusion _ p x) (inclusion _ p y) =
      algebraMap K (LocalField (integerSubring K) p) (polar Q x y) := by
    simp only [polar, ← inclusion_add, form_inclusion, map_sub]
  have hinc (x : Hyperbolic K V) :
      e (g.1.1 (inclusion _ p x)) = f.1.1 (e (inclusion _ p x)) := by
    change e (inclusion _ p ((family Q hQ hA b u).1.1 x)) = _
    dsimp only [e, f]
    rw [hyperbolicEquiv_inclusion, hyperbolicEquiv_inclusion]
    cases b
    · simp only [family, Bool.false_eq_true, if_false, HyperbolicUnipotentGroup.upper]
      rw [HyperbolicUnipotent.element_apply, HyperbolicUnipotent.element_apply]
      simp only [Hyperbolic.transvection, map_sub, inclusion_field_smul,
        hp, form_inclusion, map_add, map_mul]
    · simp only [family, if_pos rfl, if_true, HyperbolicUnipotentGroup.lower]
      rw [OppositeHyperbolicUnipotent.element_apply,
        OppositeHyperbolicUnipotent.element_apply]
      simp only [map_sub, inclusion_field_smul, hp, form_inclusion, map_add, map_mul]
  have hall (z : Space (V := Hyperbolic K V) (integerSubring K) p) :
      e (g.1.1 z) = f.1.1 (e z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        have h := congrArg (fun z ↦ a • z) (hinc x)
        simpa only [← map_smul, inclusion, TensorProduct.mk_apply,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
    | add x y hx hy => simp only [map_add, hx, hy]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  change e (g.1.1 (e.symm z)) = f.1.1 z
  simpa only [e.apply_symm_apply] using hall (e.symm z)

/-- The genuine global and local scalar-parameter families commute with completion. -/
theorem localize_family (hdim : Module.finrank K V = 1) (hA : Q.Anisotropic)
    (p : HeightOneSpectrum (integerSubring K)) (u : V) (b : Bool) (t : K) :
    localizeProper (Hyperbolic.form Q) (family Q hQ hA b (t • u)) p =
      localFamily Q hQ hdim p u b (algebraMap K (LocalField (integerSubring K) p) t) := by
  apply (toChart Q p).injective
  rw [toChart_family Q hQ hdim hA]
  simp only [localFamily, MulEquiv.apply_symm_apply, inclusion_field_smul]

/-- Each actual completed scalar family is continuous at all parameters. -/
theorem continuous_localFamily (hdim : Module.finrank K V = 1)
    (p : HeightOneSpectrum (integerSubring K)) (u : V) (b : Bool) :
    Continuous (localFamily Q hQ hdim p u b) := by
  exact (ProperIsometryTransport.continuous_hom _ _
    (hyperbolicEquiv (V := V) (integerSubring K) p).symm
    (OrthogonalTransport.inverse_value _ _ _ (hyperbolicEquiv_form _ p Q))).comp
      (UnipotentContinuity.continuous_family _ _ _ b (inclusion _ p u))

end NormEuclidean.CompletedUnipotent
