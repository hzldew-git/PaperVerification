import NormEuclidean.CompletedIntegralLattice
import NormEuclidean.NumberFieldNorm
import Bong.Dyadic.NumberFieldCompletion
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Hensel lifting at actual number-field completions

The residue-field finiteness proof reused here is number-field generic.
Compactness of the actual completed integer ring supplies adic completeness
and hence Hensel lifting. No dyadic context or assumed lifting law is used.
-/

noncomputable section

namespace NormEuclidean.CompletionHensel

open CompletedIntegralLattice IsDedekindDomain
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers K))

instance completedIntegerLocal (v : HeightOneSpectrum (integerSubring K)) :
    IsLocalRing (LocalRing (integerSubring K) v) :=
  inferInstanceAs (IsLocalRing (v.adicCompletionIntegers K))

/-- The residue field of the project's actual completed integer ring is finite. -/
theorem finite_residue_field (v : HeightOneSpectrum (integerSubring K)) :
    Finite (IsLocalRing.ResidueField (LocalRing (integerSubring K) v)) := by
  change Finite (IsLocalRing.ResidueField (Bong.NumberFieldCompletion.integerRing v))
  exact Bong.NumberFieldCompletion.finiteResidueField v

/-- The actual completed integer ring is compact. -/
theorem compact_completed_integers (v : HeightOneSpectrum (integerSubring K)) :
    CompactSpace (LocalRing (integerSubring K) v) := by
  change CompactSpace (Bong.NumberFieldCompletion.integerRing v)
  exact (Valued.integer.properSpace_iff_compactSpace_integer
    (K := v.adicCompletion K)).mp (Bong.NumberFieldCompletion.properSpace v)

/-- Every coherent sequence of maximal-ideal congruences has an actual limit
in the completed integer ring. This is proved by nested compact cosets. -/
theorem adic_complete_completed_integers (v : HeightOneSpectrum (integerSubring K)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (LocalRing (integerSubring K) v))
      (LocalRing (integerSubring K) v) := by
  let A := LocalRing (integerSubring K) v
  let I := IsLocalRing.maximalIdeal A
  letI : CompactSpace A := compact_completed_integers v
  letI : IsPrincipalIdealRing A :=
    inferInstanceAs (IsPrincipalIdealRing (v.adicCompletionIntegers K))
  refine { __ := (inferInstance : IsHausdorff I A), prec' := ?_ }
  intro f hf
  let S n : Set A := f n +ᵥ ((I ^ n : Ideal A) : Set A)
  have hS n : S (n + 1) ⊆ S n := by
    apply (Set.vadd_set_subset_vadd_set_iff.mpr
      (Ideal.pow_le_pow_right n.le_succ)).trans
    simpa [S] using (hf n.le_succ).symm
  have hclosed n : IsClosed (S n) :=
    (IsNoetherianRing.isClosed_ideal (I ^ n)).vadd (f n)
  obtain ⟨a, ha⟩ :=
    (hclosed 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hS (by simp [S]) hclosed
  refine ⟨a, fun n ↦ ?_⟩
  obtain ⟨b, hb, rfl⟩ := Set.mem_iInter.mp ha n
  simpa [SModEq.sub_mem] using hb

/-- Hensel lifting holds at every actual finite completion, including dyadic places. -/
theorem henselian_completed_integers (v : HeightOneSpectrum (integerSubring K)) :
    HenselianRing (LocalRing (integerSubring K) v)
      (IsLocalRing.maximalIdeal (LocalRing (integerSubring K) v)) := by
  letI := adic_complete_completed_integers v
  infer_instance

end NormEuclidean.CompletionHensel
