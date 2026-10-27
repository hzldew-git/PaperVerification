import NormEuclidean.CompletedHyperbolicSpinorMap
import NormEuclidean.QuadraticIdeleClassCorrection
import NormEuclidean.BinaryAdelicNorm
import NormEuclidean.GenusHyperbolicCancellation
import NormEuclidean.ChapterX.HyperbolicStrongApproximation
import NormEuclidean.AdelicSpinorCorrection

/-!
# Binary scalar norm correction through strong approximation and cancellation

The global and integral correcting transformations are constructed. The
hyperbolic kernel approximation theorem supplies the global lattice isometry.
The arithmetic unit-norm premise is retained explicitly until it is proved
for the discriminant extension from the original norm-Euclidean hypotheses.
-/

noncomputable section

namespace NormEuclidean.BinaryClassNumberCorrection

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
open AdelicApproximation AdelicSpinorKernel ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- A scalar comparison in the ordinary class kernel gives actual correcting
global and integral proper transformations, without a principal-ring hypothesis. -/
theorem exists_correction (L : Lattice (integerSubring K) Q)
    {M : Lattice (integerSubring K) (Hyperbolic.form Q)}
    (c : FiniteAdelicProperComparison (Hyperbolic.form Q) L.hyperbolic M)
    (a : (FiniteAdeleRing (integerSubring K) K)ˣ)
    (ha : ∀ p : HeightOneSpectrum (integerSubring K),
      properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
        (form_polarBilin_nondegenerate _ p _ (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
        (c.toAdelic p) = Bong.Dyadic.squareClass (LocalField (integerSubring K) p)
          (FiniteIdele.componentUnit p a))
    (hclass : FiniteIdele.classHom a = 1) :
    ∃ g : properGroup (Hyperbolic.form Q),
      ∃ s : FiniteAdelicProperOrthogonal (Hyperbolic.form Q) L.hyperbolic,
        IsIntegralAdelic (Hyperbolic.form Q) L.hyperbolic s ∧
          ∀ p : HeightOneSpectrum (integerSubring K),
            let theta := properAmbientSpinorNormHom
              (form (integerSubring K) p (Hyperbolic.form Q))
              (form_polarBilin_nondegenerate _ p _
                (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
            theta (c.toAdelic p) =
              theta (localizeProper (Hyperbolic.form Q) g p) * theta (s p) := by
  obtain ⟨k, u, hdecomp⟩ :=
    FiniteIdele.exists_diagonal_mul_localUnit_of_classHom_eq_one a hclass
  let hH := Hyperbolic.form_polarBilin_nondegenerate Q hQ
  have hu : u.1 ∈
      AdelicSpinor.finiteSpinorIdeles (integerSubring K) (Hyperbolic.form Q) hH L.hyperbolic :=
    AdelicSpinor.hyperbolic_localUnits_le_finiteSpinorIdeles (integerSubring K) Q hQ L u.2
  obtain ⟨s, hs, hsnorm⟩ :=
    AdelicSpinorCorrection.exists_integralAdelic_of_finiteSpinorIdele (Hyperbolic.form Q)
      hH L.hyperbolic u.1 hu
  refine ⟨SpinorBaseChange.hyperbolicCorrection Q hQ k, s, hs, ?_⟩
  intro p
  dsimp only
  have hcomp := congrArg
    (FiniteIdele.componentUnit (R := integerSubring K) (K := K) p) hdecomp
  rw [map_mul, FiniteIdele.componentUnit_diagonal] at hcomp
  rw [ha, hcomp]
  exact (map_mul (QuotientGroup.mk' (Subgroup.square (LocalField (integerSubring K) p)ˣ))
    _ _).trans (congrArg₂ (· * ·)
      (SpinorBaseChange.hyperbolicCorrection_localSpinorNorm Q hQ k p).symm
      (hsnorm p).symm)

/-- The proved kernel strong approximation turns the scalar correction into
an actual proper global isometry of the enlarged lattices. -/
theorem hyperbolic_isometry_of_class_kernel (hdim : 2 ≤ Module.finrank K V)
    (L : Lattice (integerSubring K) Q)
    {M : Lattice (integerSubring K) (Hyperbolic.form Q)}
    (c : FiniteAdelicProperComparison (Hyperbolic.form Q) L.hyperbolic M)
    (a : (FiniteAdeleRing (integerSubring K) K)ˣ)
    (ha : ∀ p : HeightOneSpectrum (integerSubring K),
      properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
        (form_polarBilin_nondegenerate _ p _ (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
        (c.toAdelic p) = Bong.Dyadic.squareClass (LocalField (integerSubring K) p)
          (FiniteIdele.componentUnit p a))
    (hclass : FiniteIdele.classHom a = 1) :
    ProperlyGloballyIsometric (Hyperbolic.form Q) L.hyperbolic M := by
  obtain ⟨g, s, hs, hnorm⟩ := exists_correction Q hQ L c a ha hclass
  exact properlyGloballyIsometric_of_spinorKernelApproximation (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
    (HyperbolicStrongApproximation.spinorKernelStrongApproximation Q hQ hdim)
    c g s hs hnorm

omit [FiniteDimensional K V] in
/-- The exceptional binary class-number conclusion after its arithmetic
unit-norm input. No hH, supplied approximation law, or correcting map remains. -/
theorem classNumberOne_of_norm_units (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2)
    (hunit : FullIdeleClassKernel.unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range) :
    HasLatticeClassNumberOne Q L := by
  letI := L.finiteDimensional
  let hQ := quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA
  apply hasLatticeClassNumberOne_of_genus_hyperbolic_isometry L hA hE
  intro M hgen
  let h := LocalIntegralReflection.sameProperGenus_of_sameGenus Q hQ L M hgen
  let c := CompletedHyperbolicSpinorMap.comparison Q h
  let a := AdelicComparison.finiteComparisonSpinorIdele hQ h
  let b := AdelicComparison.fullComparisonSpinorIdele hQ h
  have hnorm : b ∈ (quadraticExtensionIdeleNorm theta htheta).range :=
    BinaryAdelicNorm.comparison_mem_norm_range f htheta hQ h
  have hscalar : ∀ p : HeightOneSpectrum (integerSubring K),
      properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
        (form_polarBilin_nondegenerate _ p _ (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
        (c.toAdelic p) = Bong.Dyadic.squareClass (LocalField (integerSubring K) p)
          (FiniteIdele.componentUnit p a) := by
    intro p
    rw [show c.toAdelic p = (CompletedHyperbolicSpinorMap.comparison Q h).toAdelic p from rfl,
      CompletedHyperbolicSpinorMap.comparison_spinorNorm]
    exact (AdelicComparison.squareClass_component_finiteComparisonSpinorIdele hQ h p).symm
  have hprincipal : FiniteIdele.classHom a = 1 :=
    QuadraticIdeleClassCorrection.norm_class_eq_one theta htheta hclass hunit b hnorm
  exact ProperlyGloballyIsometric.globallyIsometric (Hyperbolic.form Q)
    (hyperbolic_isometry_of_class_kernel Q hQ (by omega) L c a hscalar
      hprincipal)

end NormEuclidean.BinaryClassNumberCorrection
