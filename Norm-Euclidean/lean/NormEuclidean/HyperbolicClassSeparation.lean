import NormEuclidean.AdelicComparisonTransport
import NormEuclidean.AdelicSpinorCorrection
import NormEuclidean.IdeleClassGroup

/-!
# Equal ordinary ideal labels separate hyperbolic genus classes

Equal classes of actual spinor ideles give a principal-times-local-unit
correction. Conjugation realizes the unit correction at the actual source
genus member. Uniform kernel approximation then supplies a proper global
integral isometry, without a PID hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.HyperbolicClassSeparation

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicApproximation AdelicSpinorKernel AdelicComparisonTransport

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)

set_option maxHeartbeats 1000000 in
/-- Equal actual ordinary ideal classes yield a proper integral isometry between genus members. -/
theorem properly_isometric_of_same_ideal_class
    (L : Lattice (integerSubring K) Q)
    (happrox : HasSpinorKernelStrongApproximation (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
    {M N : Lattice (integerSubring K) (Hyperbolic.form Q)}
    (c : FiniteAdelicProperComparison (Hyperbolic.form Q) L.hyperbolic M)
    (d : FiniteAdelicProperComparison (Hyperbolic.form Q) L.hyperbolic N)
    (a b : (FiniteAdeleRing (integerSubring K) K)ˣ)
    (ha : ∀ p : HeightOneSpectrum (integerSubring K),
      properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
        (form_polarBilin_nondegenerate _ p _ (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
        (c.toAdelic p) = Bong.Dyadic.squareClass (LocalField (integerSubring K) p)
          (FiniteIdele.componentUnit p a))
    (hb : ∀ p : HeightOneSpectrum (integerSubring K),
      properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
        (form_polarBilin_nondegenerate _ p _ (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
        (d.toAdelic p) = Bong.Dyadic.squareClass (LocalField (integerSubring K) p)
          (FiniteIdele.componentUnit p b))
    (hclass : FiniteIdele.classHom a = FiniteIdele.classHom b) :
    ProperlyGloballyIsometric (Hyperbolic.form Q) M N := by
  let H := Hyperbolic.form Q
  let hH := Hyperbolic.form_polarBilin_nondegenerate Q hQ
  have hkernel : FiniteIdele.classHom (b * a⁻¹) = 1 := by
    rw [map_mul, map_inv, hclass, mul_inv_cancel]
  obtain ⟨k, u, hdecomp⟩ :=
    FiniteIdele.exists_diagonal_mul_localUnit_of_classHom_eq_one (b * a⁻¹) hkernel
  have hu : u.1 ∈ AdelicSpinor.finiteSpinorIdeles (integerSubring K) H hH L.hyperbolic :=
    AdelicSpinor.hyperbolic_localUnits_le_finiteSpinorIdeles (integerSubring K) Q hQ L u.2
  obtain ⟨s, hs, hsnorm⟩ :=
    AdelicSpinorCorrection.exists_integralAdelic_of_finiteSpinorIdele H hH L.hyperbolic u.1 hu
  let g := SpinorBaseChange.hyperbolicCorrection Q hQ k
  let t := conjugateIntegral H c s hs
  have ht : IsIntegralAdelic H M t := conjugateIntegral_integral H c s hs
  apply properlyGloballyIsometric_of_spinorKernelApproximation H hH happrox
    (relative H c d) g t ht
  intro p
  dsimp only
  let theta := properAmbientSpinorNormHom (form (integerSubring K) p H)
    (form_polarBilin_nondegenerate _ p H hH)
  have hrep : theta ((relative H c d).toAdelic p) =
      Bong.Dyadic.squareClass (LocalField (integerSubring K) p)
        (FiniteIdele.componentUnit p (b * a⁻¹)) := by
    change theta (d.toAdelic p * (c.toAdelic p)⁻¹) = _
    rw [map_mul, map_inv]
    simpa only [Bong.Dyadic.squareClass, map_mul, map_inv] using
      congrArg₂ (fun x y ↦ x * y⁻¹) (hb p) (ha p)
  have hcomp : FiniteIdele.componentUnit p (b * a⁻¹) =
      Units.map (algebraMap K (LocalField (integerSubring K) p)) k *
        FiniteIdele.componentUnit p u.1 := by
    rw [hdecomp, map_mul, FiniteIdele.componentUnit_diagonal]
  change theta ((relative H c d).toAdelic p) = theta (localizeProper H g p) * theta (t p)
  rw [hrep, hcomp]
  exact (map_mul (QuotientGroup.mk' (Subgroup.square (LocalField (integerSubring K) p)ˣ))
    _ _).trans (congrArg₂ (· * ·)
      (SpinorBaseChange.hyperbolicCorrection_localSpinorNorm Q hQ k p).symm
      ((conjugateIntegral_norm H c s hs p theta).trans (hsnorm p)).symm)

end NormEuclidean.HyperbolicClassSeparation
