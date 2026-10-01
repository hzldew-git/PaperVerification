import TraceEuclidean.RankOneIntegral
import TraceEuclidean.ShortFieldBasis
import Mathlib.Analysis.MeanInequalitiesPow

/-!
The varying-field `p`-norm finiteness corollary. The finite exponents are real
numbers at least one; the remaining constructor is the house (`p = ∞`) mean.
-/

namespace TraceEuclidean

noncomputable section

/-- Exactly the exponent range `[1, ∞]` used in Corollary 1.6. -/
inductive PNormExponent where
  | finite (p : ℝ) (hp : 1 ≤ p)
  | infinity

namespace GlobalLatticePresentation

private abbrev embeddings (P : GlobalLatticePresentation) :=
  P.field.1 →ₐ[ℚ] ℂ

private instance embeddingsNonempty (P : GlobalLatticePresentation) :
    Nonempty P.embeddings := ⟨IsAlgClosed.lift⟩

private def embeddingWeight (P : GlobalLatticePresentation) : ℝ :=
  (Fintype.card P.embeddings : ℝ)⁻¹

private def embeddingValue (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) (σ : P.embeddings) : ℝ :=
  (σ (P.Q x)).re

/-- The paper's normalized power mean of the conjugate quadratic values. -/
def pNormMean (P : GlobalLatticePresentation) (p : PNormExponent)
    (x : Fin P.rank → P.field.1) : ℝ :=
  match p with
  | .finite q _ =>
      (∑ σ : P.embeddings,
        P.embeddingWeight * (P.embeddingValue x σ) ^ q) ^ (1 / q)
  | .infinity =>
      Finset.univ.sup' Finset.univ_nonempty (P.embeddingValue x)

/-- Strict `p`-norm Euclideanity on the same positive integral global objects
used by the  finiteness theorem. -/
def IsPNormEuclidean (P : GlobalLatticePresentation)
    (p : PNormExponent) : Prop :=
  ∀ x : Fin P.rank → P.field.1, ∃ y : P.L,
    P.pNormMean p (x - y.1) < 1

private theorem embeddingCount (P : GlobalLatticePresentation) :
    Fintype.card P.embeddings = P.degree := by
  exact AlgHom.card ℚ P.field.1 ℂ

private theorem embeddingCount_pos (P : GlobalLatticePresentation) :
    0 < Fintype.card P.embeddings := by
  rw [P.embeddingCount]
  exact Module.finrank_pos

private theorem embeddingWeight_pos (P : GlobalLatticePresentation) :
    0 < P.embeddingWeight := by
  unfold embeddingWeight
  exact inv_pos.mpr (by exact_mod_cast P.embeddingCount_pos)

private theorem embeddingWeight_sum (P : GlobalLatticePresentation) :
    (∑ _ : P.embeddings, P.embeddingWeight) = 1 := by
  have hcard : (Fintype.card P.embeddings : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.embeddingCount_pos)
  calc
    (∑ _ : P.embeddings, P.embeddingWeight) =
        (Fintype.card P.embeddings : ℝ) * P.embeddingWeight := by simp
    _ = 1 := by
      unfold embeddingWeight
      exact mul_inv_cancel₀ hcard

private theorem embeddingValue_nonneg (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) (σ : P.embeddings) :
    0 ≤ P.embeddingValue x σ := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  by_cases hx : x = 0
  · simp [embeddingValue, hx]
  · let hreal : NumberField.ComplexEmbedding.IsReal σ.toRingHom :=
      NumberField.IsTotallyReal.complexEmbedding_isReal σ.toRingHom
    exact (P.positiveDefinite x hx hreal.embedding).le

private theorem meanOne_eq_trace_div_degree (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) :
    (∑ σ : P.embeddings,
        P.embeddingWeight * P.embeddingValue x σ) =
      ((Algebra.trace ℚ P.field.1 (P.Q x) : ℚ) : ℝ) / P.degree := by
  have htrace := P.real_trace_eq_sum_embeddings (P.Q x)
  rw [← Finset.mul_sum]
  simp only [embeddingWeight, P.embeddingCount, embeddingValue] at *
  rw [← htrace]
  ring

private theorem meanOne_le_p (P : GlobalLatticePresentation)
    (p : PNormExponent) (x : Fin P.rank → P.field.1) :
    (∑ σ : P.embeddings,
        P.embeddingWeight * P.embeddingValue x σ) ≤
      P.pNormMean p x := by
  let w : P.embeddings → ℝ := fun _ ↦ P.embeddingWeight
  let z : P.embeddings → ℝ := P.embeddingValue x
  have hw : ∀ σ ∈ (Finset.univ : Finset P.embeddings), 0 ≤ w σ := by
    intro σ _
    exact P.embeddingWeight_pos.le
  have hwsum : (∑ σ : P.embeddings, w σ) = 1 :=
    P.embeddingWeight_sum
  have hz : ∀ σ ∈ (Finset.univ : Finset P.embeddings), 0 ≤ z σ := by
    intro σ _
    exact P.embeddingValue_nonneg x σ
  cases p with
  | finite q hq =>
      simpa [pNormMean, w, z] using
        (Real.arith_mean_le_rpow_mean Finset.univ w z hw hwsum hz hq)
  | infinity =>
      have hterm (σ : P.embeddings) :
          w σ * z σ ≤ w σ *
            Finset.univ.sup' Finset.univ_nonempty z := by
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' z (Finset.mem_univ σ)) (hw σ (Finset.mem_univ σ))
      have hsum : (∑ σ : P.embeddings, w σ * z σ) ≤
          ∑ σ : P.embeddings,
            w σ * Finset.univ.sup' Finset.univ_nonempty z :=
        Finset.sum_le_sum (fun σ _ ↦ hterm σ)
      have h : (∑ σ : P.embeddings, w σ * z σ) ≤
          Finset.univ.sup' Finset.univ_nonempty z := calc
        _ ≤ ∑ σ : P.embeddings,
              w σ * Finset.univ.sup' Finset.univ_nonempty z := hsum
        _ = (∑ σ : P.embeddings, w σ) *
              Finset.univ.sup' Finset.univ_nonempty z := by rw [Finset.sum_mul]
        _ = _ := by rw [hwsum, one_mul]
      simpa [pNormMean, w, z] using h

/-- Every `p`-norm Euclidean lattice with `p ≥ 1`, including `p = ∞`, is
strictly trace Euclidean at its field degree. -/
theorem pnorm_implies_trace (P : GlobalLatticePresentation)
    (p : PNormExponent) (hp : P.IsPNormEuclidean p) :
    P.IsTraceEuclidean (P.degree : ℝ) := by
  intro x
  obtain ⟨y, hy⟩ := hp x
  refine ⟨y, ?_⟩
  have hmean := P.meanOne_le_p p (x - y.1)
  have htrace := P.meanOne_eq_trace_div_degree (x - y.1)
  rw [htrace] at hmean
  have hlt :
      ((Algebra.trace ℚ P.field.1 (P.Q (x - y.1)) : ℚ) : ℝ) /
          P.degree < 1 := lt_of_le_of_lt hmean hy
  have hd : (0 : ℝ) < P.degree := by
    exact_mod_cast P.embeddingCount_pos.trans_eq P.embeddingCount
  exact (div_lt_iff₀ hd).mp hlt |>.trans_eq (one_mul _)

end GlobalLatticePresentation

/-- Corollary 1.6: finite isometry classes for each exponent in `[1, ∞]`,
while the totally real field, degree, and positive rank all vary. -/
theorem pnorm_finite_of_odlyzko_table4
    (hTable : OdlyzkoTable4Input) (p : PNormExponent) :
    {c : GlobalLatticeClass |
      ∃ P : GlobalLatticePresentation,
        (Quotient.mk _ P : GlobalLatticeClass) = c ∧
          P.IsPNormEuclidean p}.Finite := by
  apply (integral_finite_of_odlyzko_table4_source hTable).subset
  intro c hc
  obtain ⟨P, rfl, hp⟩ := hc
  change P.IsTraceEuclidean (P.degree : ℝ)
  exact P.pnorm_implies_trace p hp

/-- Corollary 1.6 from the degree-restricted Table 4 premise actually used by
the degree cutoff. -/
theorem pnorm_finite_of_odlyzko_table4_from_fifteen
    (hTable : OdlyzkoTable4InputFrom 15) (p : PNormExponent) :
    {c : GlobalLatticeClass |
      ∃ P : GlobalLatticePresentation,
        (Quotient.mk _ P : GlobalLatticeClass) = c ∧
          P.IsPNormEuclidean p}.Finite := by
  apply (integral_finite_of_odlyzko_table4_from_fifteen_source hTable).subset
  intro c hc
  obtain ⟨P, rfl, hp⟩ := hc
  change P.IsTraceEuclidean (P.degree : ℝ)
  exact P.pnorm_implies_trace p hp

/-- Corollary 1.6 from the literature-facing complete Table 4 row. -/
theorem pnorm_finite_of_odlyzko_table4_description
    (hDescription : OdlyzkoTable4DescriptionInput)
    (p : PNormExponent) :
    {c : GlobalLatticeClass |
      ∃ P : GlobalLatticePresentation,
        (Quotient.mk _ P : GlobalLatticeClass) = c ∧
          P.IsPNormEuclidean p}.Finite :=
  pnorm_finite_of_odlyzko_table4_from_fifteen
    (odlyzkoTable4InputFrom_of_description hDescription 15) p

end

end TraceEuclidean
