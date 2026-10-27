import NormEuclidean.TernaryWordApproximation

/-!
# Uniform finite-adelic ternary spinor-kernel strong approximation

The auxiliary hyperbolic carrier is compared with an arbitrary full lattice.
Extra places introduced by this comparison are forced into its integral
stabilizer, so the original off-target integrality condition is retained.
-/

noncomputable section

namespace NormEuclidean.TernaryStrongApproximation

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicApproximation AdelicSpinorKernel Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- Arbitrary full ternary lattices, rather than just a chosen product lattice,
retain integrality at every place outside the originally specified target set. -/
theorem exists_kernel_approximation (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 1)
    (L : Lattice (integerSubring K) Q)
    (M : Lattice (integerSubring K) (Hyperbolic.form Q))
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : T) → properGroup (form (integerSubring K) v.1 (Hyperbolic.form Q)))
    (ha : ∀ v : T, properAmbientSpinorNormHom
      (form (integerSubring K) v.1 (Hyperbolic.form Q))
      (form_polarBilin_nondegenerate (integerSubring K) v.1 (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) (a v) = 1)
    (U : (v : T) → Set (properGroup (form (integerSubring K) v.1 (Hyperbolic.form Q))))
    (hU : ∀ v, U v ∈ 𝓝 (a v)) :
    ∃ g : properGroup (Hyperbolic.form Q),
      properAmbientSpinorNormHom (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ) g = 1 ∧
      (∀ w : HeightOneSpectrum (integerSubring K), w ∉ T →
        localizeProper (Hyperbolic.form Q) g w ∈ properStabilizerWithin
          (form (integerSubring K) w (Hyperbolic.form Q)) (carrier _ w M.carrier)) ∧
      ∀ v : T, localizeProper (Hyperbolic.form Q) g v.1 ∈ U v := by
  classical
  have hbad : {w | carrier (integerSubring K) w L.hyperbolic.carrier ≠
      carrier (integerSubring K) w M.carrier}.Finite :=
    eventually_cofinite.mp (carrier_eventually_eq (integerSubring K) L.hyperbolic M)
  let S := T ∪ hbad.toFinset
  let aS (v : S) : properGroup (form (integerSubring K) v.1 (Hyperbolic.form Q)) :=
    if hv : v.1 ∈ T then a ⟨v.1, hv⟩ else 1
  let B (w : HeightOneSpectrum (integerSubring K)) := properStabilizerWithin
    (form (integerSubring K) w (Hyperbolic.form Q)) (carrier _ w M.carrier)
  let US (v : S) : Set (properGroup (form (integerSubring K) v.1 (Hyperbolic.form Q))) :=
    if hv : v.1 ∈ T then U ⟨v.1, hv⟩ else B v.1
  have hopen (w : HeightOneSpectrum (integerSubring K)) :
      IsOpen (B w : Set (properGroup (form (integerSubring K) w (Hyperbolic.form Q)))) := by
    exact OrthogonalTopology.isOpen_properStabilizerWithin
      (form (integerSubring K) w (Hyperbolic.form Q)) (carrier _ w M.carrier)
      (carrier_fg _ w _ M.finite)
      (OrthogonalTopology.isOpen_completedCarrier (integerSubring K) w _ M)
  have haS (v : S) : properAmbientSpinorNormHom
      (form (integerSubring K) v.1 (Hyperbolic.form Q))
      (form_polarBilin_nondegenerate _ v.1 _
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) (aS v) = 1 := by
    by_cases hv : v.1 ∈ T
    · simpa only [aS, dif_pos hv] using ha ⟨v.1, hv⟩
    · simp only [aS, dif_neg hv, map_one]
  have hUS (v : S) : US v ∈ 𝓝 (aS v) := by
    by_cases hv : v.1 ∈ T
    · simpa only [US, aS, dif_pos hv] using hU ⟨v.1, hv⟩
    · simpa only [US, aS, dif_neg hv] using
        (hopen v.1).mem_nhds ((B v.1).one_mem)
  obtain ⟨g, hg, hout, hnear⟩ :=
    TernaryWordApproximation.exists_kernel_approximation Q hQ hdim L S aS haS US hUS
  refine ⟨g, hg, ?_, ?_⟩
  · intro w hw
    by_cases hS : w ∈ S
    · simpa only [US, dif_neg hw, B, SetLike.mem_coe] using hnear ⟨w, hS⟩
    · have heq : carrier (integerSubring K) w L.hyperbolic.carrier =
          carrier (integerSubring K) w M.carrier := by
        by_contra h
        exact hS (Finset.mem_union_right T (hbad.mem_toFinset.mpr h))
      simpa only [heq] using hout w hS
  · intro v
    have hvS : v.1 ∈ S := Finset.mem_union_left _ v.2
    simpa only [US, dif_pos v.2] using hnear ⟨v.1, hvS⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Uniform actual ternary Wall-kernel approximation, for every reference lattice. -/
theorem spinorKernelStrongApproximation (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 1)
    (L : Lattice (integerSubring K) Q) :
    HasSpinorKernelStrongApproximation (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) := by
  classical
  intro M a ha
  have hbad : {w | a w ∉ properStabilizerWithin
      (form (integerSubring K) w (Hyperbolic.form Q)) (carrier _ w M.carrier)}.Finite :=
    eventually_cofinite.mp a.2
  let T := hbad.toFinset
  let U (v : T) : Set (properGroup (form (integerSubring K) v.1 (Hyperbolic.form Q))) :=
    {g | (a v.1)⁻¹ * g ∈ properStabilizerWithin
      (form (integerSubring K) v.1 (Hyperbolic.form Q)) (carrier _ v.1 M.carrier)}
  have hU (v : T) : U v ∈ 𝓝 (a v.1) :=
    OrthogonalTopology.properStabilizerCoset_mem_nhds _ _ (carrier_fg _ v.1 _ M.finite)
      (OrthogonalTopology.isOpen_completedCarrier (integerSubring K) v.1 _ M) (a v.1)
  obtain ⟨g, hg, hout, hnear⟩ := exists_kernel_approximation Q hQ hdim L M T
    (fun v ↦ a v.1) (fun v ↦ ha v.1) U hU
  refine ⟨g, hg, ?_⟩
  intro w
  by_cases hw : w ∈ T
  · exact hnear ⟨w, hw⟩
  · have haw : a w ∈ properStabilizerWithin
        (form (integerSubring K) w (Hyperbolic.form Q)) (carrier _ w M.carrier) := by
      by_contra h
      exact hw (hbad.mem_toFinset.mpr h)
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haw) (hout w hw)

end NormEuclidean.TernaryStrongApproximation
