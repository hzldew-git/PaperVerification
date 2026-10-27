import NormEuclidean.ChapterX.InitialLocalVectors
import NormEuclidean.ChapterX.FiniteResidualSelection

/-!
# Residual selection without initial local representation premises

When the denominator is a global unit, it is a unit at every exceptional
finite place. The initial vectors are constructed, including at dyadic
places, and fed to the existing finite selection theorem. Global residual
representation remains a separate arithmetic question.
-/

noncomputable section

namespace NormEuclidean.UnitResidualSelection

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation Filter Topology

variable {K E : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The global-unit denominator branch has no initial or final finite local
representation input. The beta precision is centered at its actual reciprocal. -/
theorem exists_selection (Q : QuadraticForm K E) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 3 ≤ Module.finrank K E) (N : Submodule (integerSubring K) E) (hNfg : N.FG)
    (hN : Submodule.span K (N : Set E) = ⊤) (a : integerSubring K) (ha : a ≠ 0)
    (c : (integerSubring K)ˣ)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (q : NumberField.InfinitePlace K)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝
      (algebraMap K (LocalField (integerSubring K) v.1) ((c : integerSubring K) : K))⁻¹)
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
            ((a : K) * (1 - ((c : integerSubring K) : K) ^ 2 * (β : K) ^ 2))) ∧
      ((∃ x : E, Q x = (a : K) *
          (1 - ((c : integerSubring K) : K) ^ 2 * (β : K) ^ 2)) →
        ∃ x ∈ N, Q x = (a : K) *
          (1 - ((c : integerSubring K) : K) ^ 2 * (β : K) ^ 2)) := by
  classical
  obtain ⟨S, _, hselect⟩ := FiniteResidualSelection.exists_selection_from_initial_vectors
    Q hQ hdim N hNfg hN a c c.ne_zero T q W t A hA B
  apply hselect
  intro v
  let cv : (LocalRing (integerSubring K) v.1)ˣ :=
    Units.map (integerMap (integerSubring K) v.1).toMonoidHom c
  have hcv : ((cv : LocalRing (integerSubring K) v.1) :
      LocalField (integerSubring K) v.1) =
      algebraMap K (LocalField (integerSubring K) v.1) ((c : integerSubring K) : K) := rfl
  let C : Set (LocalField (integerSubring K) v.1) :=
    if h : v.1 ∈ T then W ⟨v.1, h⟩ else Set.univ
  have hC : C ∈ 𝓝 (((cv : LocalRing (integerSubring K) v.1) :
      LocalField (integerSubring K) v.1)⁻¹) := by
    rw [hcv]
    by_cases hv : v.1 ∈ T
    · simpa only [C, dif_pos hv] using hW ⟨v.1, hv⟩
    · simp only [C, dif_neg hv, Filter.univ_mem]
  have haF : algebraMap K (LocalField (integerSubring K) v.1) (a : K) ≠ 0 := by
    apply (map_ne_zero _).mpr
    exact_mod_cast ha
  obtain ⟨β, hβC, hCβ, x, hx, hx0, hxQ⟩ :=
    InitialLocalVectors.exists_initial_completed_vector Q hQ (by omega) N hN v.1
      _ haF cv C hC
  refine ⟨(β : LocalRing (integerSubring K) v.1), ?_, x, hx, hx0, ?_⟩
  · intro hv
    exact ⟨by simpa only [C, dif_pos hv] using hβC,
      by simpa only [C, dif_pos hv] using hCβ⟩
  · rw [hcv] at hxQ
    exact hxQ

end NormEuclidean.UnitResidualSelection
