import NormEuclidean.HilbertQuadraticNorm
import NormEuclidean.BinaryClassNumberCorrection

/-!
# Binary stabilization from the discriminant Hilbert field equality

For every integral lattice in the original ordinary genus, equality of the
binary discriminant field with the ordinary Hilbert field supplies an
actual proper isometry after adjoining a hyperbolic plane. No Euclidean
approximation law, class number, or local norm premise is assumed.
-/

noncomputable section

namespace NormEuclidean.HilbertBinaryStabilization

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicComparison ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField IntermediateField

universe v
variable {K : Type} [Field K] [NumberField K]
  {V : Type v} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- A binary norm frame and the actual Hilbert field equality give proper stable isometry. -/
theorem proper_isometry_of_frame (L M : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hdim : Module.finrank K V = 2)
    (theta : Kˣ) (htheta : ¬IsSquare theta) (f : BinaryNormForm.Frame Q theta)
    (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K) (theta : K))
    (hfield : K⟮r⟯ = HilbertClassFieldArithmetic.field K) (hgen : SameGenus Q L M) :
    ProperlyGloballyIsometric (Hyperbolic.form Q) L.hyperbolic M.hyperbolic := by
  letI := L.finiteDimensional
  let hQ := quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA
  let h := LocalIntegralReflection.sameProperGenus_of_sameGenus Q hQ L M hgen
  let c := CompletedHyperbolicSpinorMap.comparison Q h
  let a := finiteComparisonSpinorIdele hQ h
  let b := fullComparisonSpinorIdele hQ h
  have hnorm : b ∈ (quadraticExtensionIdeleNorm theta htheta).range :=
    BinaryAdelicNorm.comparison_mem_norm_range f htheta hQ h
  have hartin : HilbertIdeleArtin.artin K b = 1 :=
    HilbertQuadraticNorm.artin_norm theta htheta r hr hfield b hnorm
  have hprincipal : FiniteIdele.classHom a = 1 := by
    change b ∈ (FullIdeleClassKernel.classHom (K := K)).ker
    rw [← HilbertIdeleArtin.ker_eq]
    exact hartin
  have hscalar : ∀ p : HeightOneSpectrum (integerSubring K),
      properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
        (form_polarBilin_nondegenerate _ p _
          (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) (c.toAdelic p) =
        Bong.Dyadic.squareClass (LocalField (integerSubring K) p)
          (FiniteIdele.componentUnit p a) := by
    intro p
    rw [show c.toAdelic p = (CompletedHyperbolicSpinorMap.comparison Q h).toAdelic p from rfl,
      CompletedHyperbolicSpinorMap.comparison_spinorNorm]
    exact (squareClass_component_finiteComparisonSpinorIdele hQ h p).symm
  exact BinaryClassNumberCorrection.hyperbolic_isometry_of_class_kernel
    Q hQ (by omega) L c a hscalar hprincipal

/-- The discriminant equality in any binary basis suffices; the norm frame is constructed. -/
theorem proper_isometry (L M : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (b : Module.Basis (Fin 2) K V) (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K)
      (-(LinearMap.toMatrix₂ b b Q.associated).det))
    (hfield : K⟮r⟯ = HilbertClassFieldArithmetic.field K) (hgen : SameGenus Q L M) :
    ProperlyGloballyIsometric (Hyperbolic.form Q) L.hyperbolic M.hyperbolic := by
  have hns : ¬IsSquare (-(LinearMap.toMatrix₂ b b Q.associated).det) := by
    intro hs
    obtain ⟨x, hx, hQx⟩ := (quadraticForm_binary_isotropic_iff_isSquare_neg_det Q b).mpr hs
    exact hx (hA x hQx)
  have hnz : -(LinearMap.toMatrix₂ b b Q.associated).det ≠ 0 := by
    intro hz
    exact hns (by rw [hz]; exact ⟨0, by simp⟩)
  let theta : Kˣ := Units.mk0 _ hnz
  have htheta : ¬IsSquare theta := by
    rintro ⟨s, hs⟩
    exact hns ⟨(s : K), congrArg Units.val hs⟩
  let f : BinaryNormForm.Frame Q theta :=
    { basis := b
      first_ne_zero := fun h ↦ b.ne_zero 0 (hA _ h)
      parameter_eq := by simp only [theta, Units.val_mk0, binary_gramDet_eq, neg_sub] }
  have hdim : Module.finrank K V = 2 := by
    simpa using Module.finrank_eq_card_basis b
  exact proper_isometry_of_frame L M hA hdim theta htheta f r hr hfield hgen

/-- Each original genus member stabilizes to the original lattice, without Euclideanity. -/
theorem hyperbolic_isometry (L M : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (b : Module.Basis (Fin 2) K V) (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K)
      (-(LinearMap.toMatrix₂ b b Q.associated).det))
    (hfield : K⟮r⟯ = HilbertClassFieldArithmetic.field K) (hgen : SameGenus Q L M) :
    GloballyIsometric (Hyperbolic.form Q) M.hyperbolic L.hyperbolic :=
  GloballyIsometric.symm _ (ProperlyGloballyIsometric.globallyIsometric _
    (proper_isometry L M hA b r hr hfield hgen))

end NormEuclidean.HilbertBinaryStabilization
