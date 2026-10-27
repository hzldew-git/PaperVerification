import NormEuclidean.ChapterX.HasseMinkowski
import NormEuclidean.ChapterX.AllPlaceResidualCorrection

/-!
# Removing the 66:1 hypothesis from the prepared 104:3 construction

The negative-line transfer is now a theorem of number-field arithmetic.
The existing endpoint is preserved. This new endpoint retains the same
explicit preparation and infinite excluded place, with no Hasse premise.
-/

noncomputable section

namespace NormEuclidean.HasseResidualCorrection

open IsDedekindDomain CompletedIntegralLattice ProjectedComplement LocalPrimitivePairing
  QuadraticValueRepresentation ScalarIntegralApproximation Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Every negative-line transfer required by the residual construction is proved. -/
theorem negativeLineTransfer (P : QuadraticForm K V) :
    AllPlaceResidualCorrection.HasNegativeLineTransfer P :=
  fun _ hreg hf hi ↦ HasseMinkowski.isotropic_of_all_places _ hreg hf hi

set_option backward.isDefEq.respectTransparency false in
/-- The prepared infinite-excluded construction, with the last arithmetic premise removed. -/
theorem exists_prepared_vector (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (v : V) (hvL : v ∈ L) (hv : Q v ≠ 0)
    (a : (integerSubring K)ˣ) (c : integerSubring K) (hc : c ≠ 0)
    (hvalue : Q v = (c : K) ^ 2 * ((a : integerSubring K) : K))
    (T : Finset (HeightOneSpectrum (integerSubring K))) (hTc : ∀ p ∈ T, c ∉ p.asIdeal)
    (hdyadic : ∀ p : HeightOneSpectrum (integerSubring K),
      (2 : integerSubring K) ∈ p.asIdeal → p ∈ T)
    (hunimodular : ∀ p : HeightOneSpectrum (integerSubring K), p ∉ T →
      SelfDual (LocalRing (integerSubring K) p) (halfPolar (form _ p Q))
        (carrier (integerSubring K) p L))
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (W : (p : T) → Set (Space (V := V) (integerSubring K) p.1))
    (hW : ∀ p, W p ∈ 𝓝 (inclusion _ p.1 ((c : K)⁻¹ • v))) :
    ∃ z ∈ L, Q z = ((a : integerSubring K) : K) ∧
      ∀ p : T, inclusion (integerSubring K) p.1 z ∈ W p :=
  AllPlaceResidualCorrection.exists_vector_of_negative_line_transfer Q hQ hdim L hfg hfull
    v hvL hv a c hc hvalue T hTc hdyadic hunimodular q hiso W hW (negativeLineTransfer _)

end NormEuclidean.HasseResidualCorrection
