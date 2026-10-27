import NormEuclidean.ChapterX.CompletedComplementFrames
import NormEuclidean.ChapterX.InfiniteResidualConditions
import NormEuclidean.ChapterX.ExceptionalResidualCorrection
import NormEuclidean.ChapterX.AllPlaceValueReduction

/-!
# The prepared infinite-excluded 104:3 construction with all local values proved

Unimodularity outside the target set constructs the binary frames. Local
isotropy at the excluded infinite place constructs the opposite value;
the actual infinite conditions and all finite residual vectors then follow.
The only arithmetic transfer still supplied is 66:1 for the negative-line
forms. This conditional endpoint does not assert that theorem or full 104:3.
-/

noncomputable section

namespace NormEuclidean.AllPlaceResidualCorrection

open IsDedekindDomain CompletedIntegralLattice ProjectedComplement LocalPrimitivePairing
  QuadraticValueRepresentation Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The explicit remaining 66:1 input for the negative lines of one form.
This proposition has no instance and no asserted inhabitant. -/
def HasNegativeLineTransfer (P : QuadraticForm K V) : Prop :=
  ∀ d : K, (negativeLine P d).polarBilin.Nondegenerate →
    (∀ p : HeightOneSpectrum (integerSubring K),
      ¬ (form (integerSubring K) p (negativeLine P d)).Anisotropic) →
    (∀ w : NumberField.InfinitePlace K,
      ¬ (QuadraticForm.baseChange w.Completion (negativeLine P d)).Anisotropic) →
    ¬ (negativeLine P d).Anisotropic

set_option backward.isDefEq.respectTransparency false in
/-- In the prepared infinite-excluded branch, finite and infinite local
representation premises are removed. The remaining arithmetic premise is
literally the all-place isotropy transfer of 66:1 for the residual negative lines. -/
theorem exists_vector_of_negative_line_transfer (Q : QuadraticForm K V)
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
    (hW : ∀ p, W p ∈ 𝓝 (inclusion _ p.1 ((c : K)⁻¹ • v)))
    (hHasse : HasNegativeLineTransfer (Q.comp (complement Q v).subtype)) :
    ∃ z ∈ L, Q z = ((a : integerSubring K) : K) ∧
      ∀ p : T, inclusion (integerSubring K) p.1 z ∈ W p := by
  classical
  let U := complement Q v
  let P : QuadraticForm K U := Q.comp U.subtype
  have hP : P.polarBilin.Nondegenerate := complement_regular Q hQ v hv
  have hdimU := complement_finrank Q v hv
  have hposU : 0 < Module.finrank K U := by
    change 0 < Module.finrank K (complement Q v)
    omega
  let N := ComplementIntersection.onSubspace (integerSubring K) L U
  obtain ⟨x, _, hx⟩ := InitialLocalVectors.exists_nonzero_value P hP hposU N
    (ComplementIntersection.onSubspace_full _ L hfull U)
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
  have haK : ((a : integerSubring K) : K) ≠ 0 := by exact_mod_cast Units.ne_zero a
  letI : Invertible (2 : q.Completion) := invertibleOfNonzero (by norm_num)
  have hminus : ∃ u, P.baseChange q.Completion u =
      -algebraMap K q.Completion ((a : integerSubring K) : K) :=
    OrthogonalBaseChange.represents_negative_normalized_value
      (F := q.Completion) Q hQ v hv _ _ hcK hvalue hiso
  have hconditions := InfiniteResidualConditions.exists_conditions
    (K := K) (V := U) P x hx ((a : integerSubring K) : K) (c : K) haK hcK q hminus
  obtain ⟨t, A, B, hA, hinf⟩ := hconditions
  have htwo (p : HeightOneSpectrum (integerSubring K)) (hp : c ∈ p.asIdeal) :
      IsUnit (2 : LocalRing (integerSubring K) p) := by
    have hpT : p ∉ T := fun h ↦ hTc p h hp
    have hp2 : (2 : integerSubring K) ∉ p.asIdeal := fun h ↦ hpT (hdyadic p h)
    have h := isUnit_algebraMap_localRing (integerSubring K) p hp2
    convert h using 1
    apply Subtype.ext
    change (2 : LocalField (integerSubring K) p) = algebraMap K (LocalField _ p) (2 : K)
    exact (map_ofNat _ 2).symm
  have hframes (p : HeightOneSpectrum (integerSubring K)) (hp : c ∈ p.asIdeal) :
      ExceptionalResidualSelection.binaryUnitFrame p (form (integerSubring K) p P)
        ((carrier (integerSubring K) p L).comap
          ((U.subtype.baseChange (LocalField (integerSubring K) p)).restrictScalars
            (LocalRing (integerSubring K) p))) :=
    CompletedComplementFrames.binary_frame_of_selfDual Q hQ hdim L hfg hfull v hvL hv p
      (htwo p hp) (hunimodular p (fun h ↦ hTc p h hp))
  obtain ⟨M, _, _, _, _, β, hβinf, hβq, hlocal, hcorrect⟩ :=
    ExceptionalResidualCorrection.exists_correction_of_binary_frames
      Q hQ hdim L hfg hfull v hvL hv a c hc hvalue T hTc q W hW htwo hframes t A hA B
  have hfinite (p : HeightOneSpectrum (integerSubring K)) :
      ∃ u, form (integerSubring K) p P u = algebraMap K (LocalField _ p)
        (((a : integerSubring K) : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2)) := by
    obtain ⟨u, _, hu⟩ := hlocal p
    exact ⟨u, hu⟩
  have hglobal := AllPlaceValueReduction.represents_of_local_representations_and_isotropy_transfer
    P hP (((a : integerSubring K) : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2))
      (hHasse _) hfinite (hinf (β : K) hβinf hβq)
  obtain ⟨u, _, _, hzL, hzQ, hzW⟩ := hcorrect hglobal
  exact ⟨(β : K) • v + (u : V), hzL, hzQ, hzW⟩

end NormEuclidean.AllPlaceResidualCorrection
