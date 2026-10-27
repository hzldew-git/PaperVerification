import NormEuclidean.FinitePlaceIsometry

/-!
# Recovering global integrality from all finite completions

The completed valuation rings detect membership in a Dedekind subring of its
fraction field. Consequently an actual finite local isometry transports
quadratic integrality globally. No inverse of two in the integral ring is used.
-/

namespace NormEuclidean.CompletedIntegralLattice

open IsDedekindDomain

variable {K V W : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

omit [Invertible (2 : K)] in
/-- Membership in every completed valuation ring detects global integrality. -/
theorem mem_of_forall_finite_integral (x : K)
    (h : ∀ v : HeightOneSpectrum R, algebraMap K (LocalField R v) x ∈ LocalRing R v) :
    x ∈ R := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := R) (K := K) x (by
    intro v
    have hv : Valued.v (algebraMap K (LocalField R v) x) ≤ 1 := h v
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self,
      RingHom.id_apply] using hv)
  change (r : K) = x at hr
  exact hr ▸ r.property

/-- Finite local integral isometries transport quadratic integrality globally. -/
theorem integral_of_finiteLocallyIsometric
    {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Submodule R V} {L' : Submodule R W}
    (hQ : ∀ x ∈ L, Q x ∈ R) (h : FiniteLocallyIsometric R Q Q' L L') :
    ∀ x ∈ L', Q' x ∈ R := by
  intro x hx
  apply mem_of_forall_finite_integral R
  intro v
  obtain ⟨e⟩ := h v
  let y := e.toLinearEquiv.symm (inclusion R v x)
  have hy : y ∈ carrier R v L := by
    apply (e.mem_iff y).mp
    change e.toLinearEquiv (e.toLinearEquiv.symm _) ∈ carrier R v L'
    rw [LinearEquiv.apply_symm_apply]
    exact inclusion_mem R v L' hx
  have hval := carrier_integral R v Q L hQ y hy
  have heq := e.q_eq y
  simp only [y, LinearEquiv.apply_symm_apply, form_inclusion] at heq
  exact heq.symm ▸ hval

end NormEuclidean.CompletedIntegralLattice
