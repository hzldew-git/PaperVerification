import NormEuclidean.ChapterX.LocalValueNeighborhoods
import NormEuclidean.ChapterX.MixedResidualScalar
import NormEuclidean.ChapterX.ResidualLocalRepresentation
import NormEuclidean.ChapterX.FractionalValueMultiplier

/-!
# Residual selection from finitely many initial local vectors

An actual finite exceptional set is constructed. A nonzero represented
residual at each of those places gives a proved represented-value neighborhood.
Mixed approximation and the 104:1 multiplier then select one integral beta
whose residual is represented in every finite completed module. The remaining
global residual representation is explicit. Initial exceptional-place vectors
are not inferred from scalar approximation or class finiteness.
-/

noncomputable section

namespace NormEuclidean.FiniteResidualSelection

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation ResidualScalar
  Filter Topology

variable {K E : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup E] [Module K E]

/-- Only finitely many initial nonzero local representation vectors are
requested. From them the scalar, every-finite-place residual representation
and integral global correction (given global representation) are derived. -/
theorem exists_selection_from_initial_vectors (Q : QuadraticForm K E)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 3 ≤ Module.finrank K E)
    (N : Submodule (integerSubring K) E) (hNfg : N.FG)
    (hN : Submodule.span K (N : Set E) = ⊤) (a c : integerSubring K) (hc : c ≠ 0)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (q : NumberField.InfinitePlace K)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (t : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
    (A : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
    (hA : ∀ w, A w ∈ 𝓝 (t w)) (B : ℝ) :
    ∃ S : Finset (HeightOneSpectrum (integerSubring K)), T ⊆ S ∧
      ((∀ v : S, ∃ β₀ : LocalRing (integerSubring K) v.1,
        (∀ h : v.1 ∈ T, (β₀ : LocalField (integerSubring K) v.1) ∈ W ⟨v.1, h⟩ ∧
          W ⟨v.1, h⟩ ∈ 𝓝 (β₀ : LocalField (integerSubring K) v.1)) ∧
        ∃ x ∈ carrier (integerSubring K) v.1 N,
          form (integerSubring K) v.1 Q x ≠ 0 ∧
          form (integerSubring K) v.1 Q x =
            algebraMap K (LocalField (integerSubring K) v.1) (a : K) *
              (1 - algebraMap K (LocalField (integerSubring K) v.1) (c : K) ^ 2 *
                (β₀ : LocalField (integerSubring K) v.1) ^ 2)) →
        ∃ β : integerSubring K,
          (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) (β : K) ∈ W v) ∧
          (∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
            algebraMap K w.1.Completion (β : K) ∈ A w) ∧ B < q (β : K) ∧
          (∀ v : HeightOneSpectrum (integerSubring K),
            ∃ x ∈ carrier (integerSubring K) v N, form (integerSubring K) v Q x =
              algebraMap K (LocalField (integerSubring K) v)
                ((a : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2))) ∧
          ((∃ x : E, Q x = (a : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2)) →
            ∃ x ∈ N, Q x = (a : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2))) := by
  classical
  obtain ⟨D, hD⟩ := ResidualLocalRepresentation.exists_finite_exceptional_set
    Q hQ N hNfg hN hdim
  let S := D ∪ T
  refine ⟨S, Finset.subset_union_right, ?_⟩
  intro hlocal
  choose β₀ hβ₀ x hx hx0 hxvalue using hlocal
  choose U hU hrep using fun v : S ↦ LocalValueNeighborhoods.exists_residual_neighborhood
    v.1 (form (integerSubring K) v.1 Q) (carrier (integerSubring K) v.1 N)
    (algebraMap K (LocalField (integerSubring K) v.1) (a : K))
    (algebraMap K (LocalField (integerSubring K) v.1) (c : K)) (β₀ v) (x v) (hx v)
    (hxvalue v) (hx0 v)
  let C (v : S) := U v ∩ if h : v.1 ∈ T then W ⟨v.1, h⟩ else Set.univ
  have hC (v : S) : C v ∈ 𝓝 (β₀ v : LocalField (integerSubring K) v.1) := by
    apply inter_mem (hU v)
    by_cases hv : v.1 ∈ T
    · simpa only [dif_pos hv] using (hβ₀ v hv).2
    · simp only [dif_neg hv, Filter.univ_mem]
  let Tc := (finite_primes_containing (K := K) (integerSubring K) c hc).toFinset
  obtain ⟨m, hm0, hmT, hcorrect⟩ := FractionalValueMultiplier.exists_divided_value_multiplier
    Q hQ N hNfg hN hdim (S ∪ Tc)
  have hmavoid (v : HeightOneSpectrum (integerSubring K)) (hv : v ∈ S ∪ Tc) :
      m ∉ v.asIdeal := not_mem_of_isUnit_integerMap (integerSubring K) v m (hmT v hv)
  have hcm : IsCoprime c m := isCoprime_of_avoiding_divisors (integerSubring K) c m hc
    (fun v hv ↦ hmavoid v (Finset.mem_union_right S (by simpa only [Tc,
      Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hv)))
  obtain ⟨β, ⟨d, hd⟩, hβS, hβinf, hβq⟩ := MixedResidualScalar.exists_divisible_residual_scalar
    S q c m hm0 hcm (fun v hv ↦ hmavoid v (Finset.mem_union_left Tc hv)) β₀ C hC t A hA B
  have hall (v : HeightOneSpectrum (integerSubring K)) :
      ∃ x ∈ carrier (integerSubring K) v N, form (integerSubring K) v Q x =
        algebraMap K (LocalField (integerSubring K) v)
          ((a : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2)) := by
    by_cases hv : v ∈ S
    · obtain ⟨x, hx, hQx⟩ := hrep ⟨v, hv⟩ _ (hβS ⟨v, hv⟩).1
      refine ⟨x, hx, ?_⟩
      simp only [map_mul, map_sub, map_one, map_pow]
      exact hQx
    · exact hD v (fun hvD ↦ hv (Finset.mem_union_left T hvD)) a c β
  refine ⟨β, ?_, hβinf, hβq, hall, ?_⟩
  · intro v
    have h := (hβS ⟨v.1, Finset.mem_union_right D v.2⟩).2
    simpa only [C, dif_pos v.2] using h
  · intro hglobal
    apply hcorrect _ _ hglobal hall
    refine ⟨a * d, ?_⟩
    rw [hd, Subring.coe_mul]
    ring

end NormEuclidean.FiniteResidualSelection
