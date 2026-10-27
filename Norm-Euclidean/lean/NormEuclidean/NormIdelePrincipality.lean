import NormEuclidean.CompletedRayNeighborhoods
import NormEuclidean.NormRayTransformations
import NormEuclidean.ChapterX.HyperbolicStrongApproximation
import NormEuclidean.IdeleClassGroup

/-!
# Local binary norms have principal global ideal class

Strong approximation realizes a finite family of spinor-kernel ray
multipliers. Norm-Euclidean descent makes the resulting global isotropic
ray principal. Its local scalar contents recover the idele valuations.
No field class-number or unramifiedness hypothesis is used.
-/

noncomputable section

namespace NormEuclidean.NormIdelePrincipality

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicApproximation Filter Topology
open scoped NumberField NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {theta : Kˣ}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- An idele locally represented by the binary norm has a global scalar with all its valuations. -/
theorem exists_principal_valuations (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : 2 ≤ Module.finrank K V) (f : BinaryNormForm.Frame Q theta)
    (a : (FiniteAdeleRing (integerSubring K) K)ˣ)
    (hanorm : ∀ p : HeightOneSpectrum (integerSubring K),
      Bong.Dyadic.IsQuadraticNorm (LocalField (integerSubring K) p)
        (Units.map (algebraMap K (LocalField (integerSubring K) p)).toMonoidHom theta)
        (FiniteIdele.componentUnit p a)) :
    ∃ c : Kˣ, ∀ p : HeightOneSpectrum (integerSubring K),
      Valued.v (FiniteIdele.componentUnit p a).val = p.valuation K (c : K) := by
  classical
  letI := L.finiteDimensional
  let hQ := quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA
  let H := Hyperbolic.form Q
  let hH := Hyperbolic.form_polarBilin_nondegenerate Q hQ
  let e : Hyperbolic K V := Hyperbolic.e
  let T := (FiniteIdele.divisor a).support
  have hex (p : HeightOneSpectrum (integerSubring K)) :=
    NormRayTransformations.exists_completed_kernel_ray Q hQ f p
      (FiniteIdele.componentUnit p a) (hanorm p)
  choose s hs hse using hex
  let U (p : T) : Set (properGroup (form (integerSubring K) p.1 H)) :=
    {g | ValuationRayContent.HasContent (carrier (integerSubring K) p.1 L.hyperbolic.carrier)
      (g.1.1 (inclusion _ p.1 e)) (FiniteIdele.componentUnit p.1 a)}
  have hU (p : T) : U p ∈ 𝓝 (s p.1) := by
    have hn := CompletedRayNeighborhoods.eventually_hasContent L.carrier L.full p.1
      (FiniteIdele.componentUnit p.1 a)
    have ht := (OrthogonalTopology.continuous_proper_apply
      (form (integerSubring K) p.1 H) (inclusion _ p.1 e)).tendsto (s p.1)
    rw [hse p.1] at ht
    exact ht.eventually hn
  let q : NumberField.InfinitePlace K := Classical.arbitrary _
  have hr : 4 ≤ Module.finrank K (Hyperbolic K V) := by
    have heq : Module.finrank K (Hyperbolic K V) = Module.finrank K V + 2 := by
      simp [Hyperbolic, Module.finrank_prod]
    omega
  obtain ⟨g, _, hout, hnear⟩ := CommutatorStrongApproximation.exists_kernel_approximation H hH
    hr L.hyperbolic.carrier L.hyperbolic.finite L.hyperbolic.full q
    (CompletedHyperbolicKernel.infinite_isotropic Q q) T (fun p ↦ s p.1)
    (fun p ↦ (CompletedHyperbolicKernel.kernel_iff_commutator Q hQ p.1 (s p.1)).mp (hs p.1))
    U hU
  have he0 : e ≠ 0 := by
    intro he
    exact one_ne_zero (congrArg (fun z : Hyperbolic K V ↦ z.2.1) he)
  have hz0 : g.1.1 e ≠ 0 := g.1.1.map_ne_zero_iff.mpr he0
  have hzQ : Hyperbolic.q Q (g.1.1 e) = 0 := by
    change H (g.1.1 e) = 0
    rw [g.1.2]
    simp [H, e, Hyperbolic.q, Hyperbolic.e]
  obtain ⟨c, hc⟩ := IsotropicRayTerminal.exists_completed_contents L hA hE (g.1.1 e) hz0 hzQ
  refine ⟨c, fun p ↦ ?_⟩
  have hcontent : ValuationRayContent.HasContent
      (carrier (integerSubring K) p L.hyperbolic.carrier)
      (inclusion _ p (g.1.1 e)) (FiniteIdele.componentUnit p a) := by
    have heq : (localizeProper H g p).1.1 (inclusion _ p e) =
        inclusion (integerSubring K) p (g.1.1 e) := rfl
    rw [← heq]
    by_cases hp : p ∈ T
    · exact hnear ⟨p, hp⟩
    · apply (ValuationRayContent.equiv_iff (localizeProper H g p).1.1 (hout p hp) _ _).mpr
      have horder : FiniteIdele.order a p = 0 := Finsupp.notMem_support_iff.mp hp
      have hval : Valued.v (FiniteIdele.componentUnit p a).val = 1 :=
        (FiniteIdele.order_eq_zero_iff a p).mp horder
      intro b
      have he := IsotropicRayTerminal.hyperbolic_e_content L.carrier p
        (1 : (LocalField (integerSubring K) p)ˣ) b
      simpa only [Lattice.hyperbolic, e, Units.val_one, one_smul, mul_one, map_mul, hval] using he
  exact (ValuationRayContent.valuation_eq hcontent (hc p)).trans
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p (c : K))

set_option backward.isDefEq.respectTransparency false in
/-- Actual local binary norms have trivial ordinary ideal class under the original hypotheses. -/
theorem classHom_eq_one (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : 2 ≤ Module.finrank K V) (f : BinaryNormForm.Frame Q theta)
    (a : (FiniteAdeleRing (integerSubring K) K)ˣ)
    (hanorm : ∀ p : HeightOneSpectrum (integerSubring K),
      Bong.Dyadic.IsQuadraticNorm (LocalField (integerSubring K) p)
        (Units.map (algebraMap K (LocalField (integerSubring K) p)).toMonoidHom theta)
        (FiniteIdele.componentUnit p a)) : FiniteIdele.classHom a = 1 := by
  obtain ⟨c, hc⟩ := exists_principal_valuations L hA hE hdim f a hanorm
  let b := a * (FiniteAdeleRing.unitEmbedding (integerSubring K) K c)⁻¹
  have hb : b ∈ FiniteIdele.localUnitSubgroup := by
    apply (FiniteIdele.mem_localUnitSubgroup_component_iff b).mpr
    intro p
    change Valued.v (FiniteIdele.componentUnit p b).val = 1
    have heq : FiniteIdele.componentUnit p b = FiniteIdele.componentUnit p a *
        (Units.map (algebraMap K (LocalField (integerSubring K) p)).toMonoidHom c)⁻¹ := by
      simp only [b, map_mul, map_inv, FiniteIdele.componentUnit_diagonal]
      apply Units.ext
      rfl
    rw [heq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hc p]
    have hm : Valued.v
        (Units.map (algebraMap K (LocalField (integerSubring K) p)).toMonoidHom c).val =
        p.valuation K (c : K) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p _
    rw [hm]
    exact mul_inv_cancel₀ ((p.valuation K).ne_zero_iff.mpr c.ne_zero)
  have h := FiniteIdele.classHom_eq_one_of_localUnit hb
  simpa only [b, map_mul, map_inv, FiniteIdele.classHom_diagonal, inv_one, mul_one] using h

end NormEuclidean.NormIdelePrincipality
