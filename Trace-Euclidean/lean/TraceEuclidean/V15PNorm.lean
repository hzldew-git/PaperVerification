import TraceEuclidean.V15RankOneIntegral
import TraceEuclidean.ShortFieldBasis
import Mathlib.Analysis.MeanInequalitiesPow

/-!
The varying-field `p`-norm finiteness corollary. The finite exponents are real
numbers at least one; the remaining constructor is the house (`p = ∞`) mean.
-/

namespace TraceEuclidean

noncomputable section

/-- Exactly the exponent range `[1, ∞]` used in Corollary 1.6. -/
inductive V15PNormExponent where
  | finite (p : ℝ) (hp : 1 ≤ p)
  | infinity

namespace GlobalLatticePresentation

private abbrev v15Embeddings (P : GlobalLatticePresentation) :=
  P.field.1 →ₐ[ℚ] ℂ

private instance v15EmbeddingsNonempty (P : GlobalLatticePresentation) :
    Nonempty P.v15Embeddings := ⟨IsAlgClosed.lift⟩

private def v15EmbeddingWeight (P : GlobalLatticePresentation) : ℝ :=
  (Fintype.card P.v15Embeddings : ℝ)⁻¹

private def v15EmbeddingValue (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) (σ : P.v15Embeddings) : ℝ :=
  (σ (P.Q x)).re

/-- The paper's normalized power mean of the conjugate quadratic values. -/
def v15PNormMean (P : GlobalLatticePresentation) (p : V15PNormExponent)
    (x : Fin P.rank → P.field.1) : ℝ :=
  match p with
  | .finite q _ =>
      (∑ σ : P.v15Embeddings,
        P.v15EmbeddingWeight * (P.v15EmbeddingValue x σ) ^ q) ^ (1 / q)
  | .infinity =>
      Finset.univ.sup' Finset.univ_nonempty (P.v15EmbeddingValue x)

/-- Strict `p`-norm Euclideanity on the same positive integral global objects
used by the v15 finiteness theorem. -/
def IsV15PNormEuclidean (P : GlobalLatticePresentation)
    (p : V15PNormExponent) : Prop :=
  ∀ x : Fin P.rank → P.field.1, ∃ y : P.L,
    P.v15PNormMean p (x - y.1) < 1

private theorem v15EmbeddingCount (P : GlobalLatticePresentation) :
    Fintype.card P.v15Embeddings = P.degree := by
  exact AlgHom.card ℚ P.field.1 ℂ

private theorem v15EmbeddingCount_pos (P : GlobalLatticePresentation) :
    0 < Fintype.card P.v15Embeddings := by
  rw [P.v15EmbeddingCount]
  exact Module.finrank_pos

private theorem v15EmbeddingWeight_pos (P : GlobalLatticePresentation) :
    0 < P.v15EmbeddingWeight := by
  unfold v15EmbeddingWeight
  exact inv_pos.mpr (by exact_mod_cast P.v15EmbeddingCount_pos)

private theorem v15EmbeddingWeight_sum (P : GlobalLatticePresentation) :
    (∑ _ : P.v15Embeddings, P.v15EmbeddingWeight) = 1 := by
  have hcard : (Fintype.card P.v15Embeddings : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.v15EmbeddingCount_pos)
  calc
    (∑ _ : P.v15Embeddings, P.v15EmbeddingWeight) =
        (Fintype.card P.v15Embeddings : ℝ) * P.v15EmbeddingWeight := by simp
    _ = 1 := by
      unfold v15EmbeddingWeight
      exact mul_inv_cancel₀ hcard

private theorem v15EmbeddingValue_nonneg (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) (σ : P.v15Embeddings) :
    0 ≤ P.v15EmbeddingValue x σ := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  by_cases hx : x = 0
  · simp [v15EmbeddingValue, hx]
  · let hreal : NumberField.ComplexEmbedding.IsReal σ.toRingHom :=
      NumberField.IsTotallyReal.complexEmbedding_isReal σ.toRingHom
    exact (P.positiveDefinite x hx hreal.embedding).le

private theorem v15MeanOne_eq_trace_div_degree (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) :
    (∑ σ : P.v15Embeddings,
        P.v15EmbeddingWeight * P.v15EmbeddingValue x σ) =
      ((Algebra.trace ℚ P.field.1 (P.Q x) : ℚ) : ℝ) / P.degree := by
  have htrace := P.real_trace_eq_sum_embeddings (P.Q x)
  rw [← Finset.mul_sum]
  simp only [v15EmbeddingWeight, P.v15EmbeddingCount, v15EmbeddingValue] at *
  rw [← htrace]
  ring

private theorem v15MeanOne_le_p (P : GlobalLatticePresentation)
    (p : V15PNormExponent) (x : Fin P.rank → P.field.1) :
    (∑ σ : P.v15Embeddings,
        P.v15EmbeddingWeight * P.v15EmbeddingValue x σ) ≤
      P.v15PNormMean p x := by
  let w : P.v15Embeddings → ℝ := fun _ ↦ P.v15EmbeddingWeight
  let z : P.v15Embeddings → ℝ := P.v15EmbeddingValue x
  have hw : ∀ σ ∈ (Finset.univ : Finset P.v15Embeddings), 0 ≤ w σ := by
    intro σ _
    exact P.v15EmbeddingWeight_pos.le
  have hwsum : (∑ σ : P.v15Embeddings, w σ) = 1 :=
    P.v15EmbeddingWeight_sum
  have hz : ∀ σ ∈ (Finset.univ : Finset P.v15Embeddings), 0 ≤ z σ := by
    intro σ _
    exact P.v15EmbeddingValue_nonneg x σ
  cases p with
  | finite q hq =>
      simpa [v15PNormMean, w, z] using
        (Real.arith_mean_le_rpow_mean Finset.univ w z hw hwsum hz hq)
  | infinity =>
      have hterm (σ : P.v15Embeddings) :
          w σ * z σ ≤ w σ *
            Finset.univ.sup' Finset.univ_nonempty z := by
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' z (Finset.mem_univ σ)) (hw σ (Finset.mem_univ σ))
      have hsum : (∑ σ : P.v15Embeddings, w σ * z σ) ≤
          ∑ σ : P.v15Embeddings,
            w σ * Finset.univ.sup' Finset.univ_nonempty z :=
        Finset.sum_le_sum (fun σ _ ↦ hterm σ)
      have h : (∑ σ : P.v15Embeddings, w σ * z σ) ≤
          Finset.univ.sup' Finset.univ_nonempty z := calc
        _ ≤ ∑ σ : P.v15Embeddings,
              w σ * Finset.univ.sup' Finset.univ_nonempty z := hsum
        _ = (∑ σ : P.v15Embeddings, w σ) *
              Finset.univ.sup' Finset.univ_nonempty z := by rw [Finset.sum_mul]
        _ = _ := by rw [hwsum, one_mul]
      simpa [v15PNormMean, w, z] using h

/-- Every `p`-norm Euclidean lattice with `p ≥ 1`, including `p = ∞`, is
strictly trace Euclidean at its field degree. -/
theorem v15_pnorm_implies_trace (P : GlobalLatticePresentation)
    (p : V15PNormExponent) (hp : P.IsV15PNormEuclidean p) :
    P.IsTraceEuclidean (P.degree : ℝ) := by
  intro x
  obtain ⟨y, hy⟩ := hp x
  refine ⟨y, ?_⟩
  have hmean := P.v15MeanOne_le_p p (x - y.1)
  have htrace := P.v15MeanOne_eq_trace_div_degree (x - y.1)
  rw [htrace] at hmean
  have hlt :
      ((Algebra.trace ℚ P.field.1 (P.Q (x - y.1)) : ℚ) : ℝ) /
          P.degree < 1 := lt_of_le_of_lt hmean hy
  have hd : (0 : ℝ) < P.degree := by
    exact_mod_cast P.v15EmbeddingCount_pos.trans_eq P.v15EmbeddingCount
  exact (div_lt_iff₀ hd).mp hlt |>.trans_eq (one_mul _)

end GlobalLatticePresentation

/-- Corollary 1.6: finite isometry classes for each exponent in `[1, ∞]`,
while the totally real field, degree, and positive rank all vary. -/
theorem v15_pnorm_finite_of_odlyzko_table4
    (hTable : V15OdlyzkoTable4Input) (p : V15PNormExponent) :
    {c : GlobalLatticeClass |
      ∃ P : GlobalLatticePresentation,
        (Quotient.mk _ P : GlobalLatticeClass) = c ∧
          P.IsV15PNormEuclidean p}.Finite := by
  apply (v15_integral_finite_of_odlyzko_table4_source hTable).subset
  intro c hc
  obtain ⟨P, rfl, hp⟩ := hc
  change P.IsTraceEuclidean (P.degree : ℝ)
  exact P.v15_pnorm_implies_trace p hp

/-- Corollary 1.6 from the degree-restricted Table 4 premise actually used by
the degree cutoff. -/
theorem v15_pnorm_finite_of_odlyzko_table4_from_fifteen
    (hTable : V15OdlyzkoTable4InputFrom 15) (p : V15PNormExponent) :
    {c : GlobalLatticeClass |
      ∃ P : GlobalLatticePresentation,
        (Quotient.mk _ P : GlobalLatticeClass) = c ∧
          P.IsV15PNormEuclidean p}.Finite := by
  apply (v15_integral_finite_of_odlyzko_table4_from_fifteen_source hTable).subset
  intro c hc
  obtain ⟨P, rfl, hp⟩ := hc
  change P.IsTraceEuclidean (P.degree : ℝ)
  exact P.v15_pnorm_implies_trace p hp

/-- Corollary 1.6 from the literature-facing complete Table 4 row. -/
theorem v15_pnorm_finite_of_odlyzko_table4_description
    (hDescription : V15OdlyzkoTable4DescriptionInput)
    (p : V15PNormExponent) :
    {c : GlobalLatticeClass |
      ∃ P : GlobalLatticePresentation,
        (Quotient.mk _ P : GlobalLatticeClass) = c ∧
          P.IsV15PNormEuclidean p}.Finite :=
  v15_pnorm_finite_of_odlyzko_table4_from_fifteen
    (v15_odlyzkoTable4InputFrom_of_description hDescription 15) p

end

end TraceEuclidean
