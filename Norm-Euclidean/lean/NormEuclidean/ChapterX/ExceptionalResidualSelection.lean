import NormEuclidean.ChapterX.UnitResidualSelection
import NormEuclidean.ChapterX.NonunitInitialVectors

/-!
# Residual selection with only the denominator-divisor geometry left explicit

Unit-denominator places use the constructed small vector and near-one root.
At nonunit-denominator places a binary unit frame constructs beta zero and
the required represented unit. There is no supplied initial or selected-beta
local representation law. Derivation of the frames from unimodularity remains
the geometric premise, corresponding to the use of 82:17 in 104:3.
-/

noncomputable section

namespace NormEuclidean.ExceptionalResidualSelection

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation Filter Topology

variable {K E : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup E] [Module K E]

/-- A literal binary orthogonal unit frame in the actual completed module;
this definition includes vectors and their pairings, not a value-set assertion. -/
def binaryUnitFrame (v : HeightOneSpectrum (integerSubring K))
    (Q : QuadraticForm (LocalField (integerSubring K) v) (Space (V := E) (integerSubring K) v))
    (N : Submodule (LocalRing (integerSubring K) v) (Space (V := E) (integerSubring K) v)) :
    Prop :=
  ∃ (a b : (LocalRing (integerSubring K) v)ˣ)
    (e f : Space (V := E) (integerSubring K) v), e ∈ N ∧ f ∈ N ∧
      Q e = ((a : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ∧
      Q f = ((b : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ∧
      Q.polarBilin e f = 0

/-- For a unit target value, actual binary frames at denominator divisors
remove every finite local representation premise. Only the displayed frame
geometry and global residual representation remain unproved source inputs. -/
theorem exists_selection_of_binary_frames (Q : QuadraticForm K E)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 3 ≤ Module.finrank K E)
    (N : Submodule (integerSubring K) E) (hNfg : N.FG)
    (hN : Submodule.span K (N : Set E) = ⊤) (a : (integerSubring K)ˣ)
    (c : integerSubring K) (hc : c ≠ 0)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (hTc : ∀ v ∈ T, c ∉ v.asIdeal) (q : NumberField.InfinitePlace K)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝 (algebraMap K (LocalField (integerSubring K) v.1) (c : K))⁻¹)
    (hnondyadic : ∀ v : HeightOneSpectrum (integerSubring K), c ∈ v.asIdeal →
      IsUnit (2 : LocalRing (integerSubring K) v))
    (hframes : ∀ v : HeightOneSpectrum (integerSubring K), c ∈ v.asIdeal →
      binaryUnitFrame v (form (integerSubring K) v Q) (carrier (integerSubring K) v N))
    (t : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
    (A : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
    (hA : ∀ w, A w ∈ 𝓝 (t w)) (B : ℝ) :
    ∃ β : integerSubring K,
      (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) (β : K) ∈ W v) ∧
      (∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
        algebraMap K w.1.Completion (β : K) ∈ A w) ∧ B < q (β : K) ∧
      (∀ v : HeightOneSpectrum (integerSubring K),
        ∃ x ∈ carrier (integerSubring K) v N, form (integerSubring K) v Q x =
          algebraMap K (LocalField (integerSubring K) v)
            (((a : integerSubring K) : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2))) ∧
      ((∃ x : E, Q x = ((a : integerSubring K) : K) *
          (1 - (c : K) ^ 2 * (β : K) ^ 2)) →
        ∃ x ∈ N, Q x = ((a : integerSubring K) : K) *
          (1 - (c : K) ^ 2 * (β : K) ^ 2)) := by
  classical
  obtain ⟨S, _, hselect⟩ := FiniteResidualSelection.exists_selection_from_initial_vectors
    Q hQ hdim N hNfg hN a c hc T q W t A hA B
  apply hselect
  intro v
  by_cases hcv : c ∈ v.1.asIdeal
  · obtain ⟨d, e, x, y, hx, hy, hxQ, hyQ, hxy⟩ := hframes v.1 hcv
    let av := Units.map (integerMap (integerSubring K) v.1).toMonoidHom a
    obtain ⟨β, z, hz, hz0, hzQ⟩ := NonunitInitialVectors.exists_initial_vector_of_binary_frame
      v.1 _ _ (hnondyadic v.1 hcv) x y hx hy d e hxQ hyQ hxy av
      (algebraMap K (LocalField (integerSubring K) v.1) (c : K))
    refine ⟨β, fun hv ↦ False.elim (hTc v.1 hv hcv), z, hz, hz0, ?_⟩
    exact hzQ
  · have hu : IsUnit (integerMap (integerSubring K) v.1 c) :=
      isUnit_algebraMap_localRing (integerSubring K) v.1 hcv
    let cv := hu.unit
    have hcvF : ((cv : LocalRing (integerSubring K) v.1) :
        LocalField (integerSubring K) v.1) =
        algebraMap K (LocalField (integerSubring K) v.1) (c : K) :=
      congrArg (fun z : LocalRing (integerSubring K) v.1 ↦
        (z : LocalField (integerSubring K) v.1)) hu.unit_spec
    let C : Set (LocalField (integerSubring K) v.1) :=
      if h : v.1 ∈ T then W ⟨v.1, h⟩ else Set.univ
    have hC : C ∈ 𝓝 (((cv : LocalRing (integerSubring K) v.1) :
        LocalField (integerSubring K) v.1)⁻¹) := by
      rw [hcvF]
      by_cases hv : v.1 ∈ T
      · simpa only [C, dif_pos hv] using hW ⟨v.1, hv⟩
      · simp only [C, dif_neg hv, Filter.univ_mem]
    have haF : algebraMap K (LocalField (integerSubring K) v.1)
        ((a : integerSubring K) : K) ≠ 0 := by
      apply (map_ne_zero _).mpr
      exact_mod_cast a.ne_zero
    obtain ⟨β, hβC, hCβ, x, hx, hx0, hxQ⟩ :=
      InitialLocalVectors.exists_initial_completed_vector Q hQ (by omega) N hN v.1
        _ haF cv C hC
    refine ⟨(β : LocalRing (integerSubring K) v.1), ?_, x, hx, hx0, ?_⟩
    · intro hv
      exact ⟨by simpa only [C, dif_pos hv] using hβC,
        by simpa only [C, dif_pos hv] using hCβ⟩
    · rw [hcvF] at hxQ
      exact hxQ

end NormEuclidean.ExceptionalResidualSelection
