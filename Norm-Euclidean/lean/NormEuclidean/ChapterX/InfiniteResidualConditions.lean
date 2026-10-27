import NormEuclidean.ChapterX.ArchimedeanResidualValues
import NormEuclidean.ChapterX.ScalarNeighborhoods

/-!
# All infinite residual conditions for the infinite-excluded branch of 104:3

Actual neighborhoods are constructed at every other infinite place.
At the excluded real place, an explicit norm bound makes the residual
lie in the ray of the opposite target value. Complex places represent
all values by square-root rescaling. Scalar growth is thus connected to
representation at every actual infinite completion.
-/

noncomputable section

namespace NormEuclidean.InfiniteResidualConditions

open Filter Topology ArchimedeanResidualValues
open scoped TensorProduct

section RealBound

variable {F E : Type*} [NormedField F] [AddCommGroup E] [Module F E]

/-- A precise norm bound is sufficient at the excluded real place. -/
theorem represents_residual_of_norm_large (Q : QuadraticForm F E) (e : F ≃+* ℝ)
    (hnorm : ∀ t : F, ‖e t‖ = ‖t‖) (x : E) (a : F) (ha : a ≠ 0)
    (hx : Q x = -a) (c : F) (hc : c ≠ 0) (β : F) (hβ : ‖c‖⁻¹ < ‖β‖) :
    ∃ y : E, Q y = a * (1 - c ^ 2 * β ^ 2) := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hlarge : 1 < ‖c‖ * ‖β‖ := by
    have h := mul_lt_mul_of_pos_left hβ hcpos
    rwa [mul_inv_cancel₀ (ne_of_gt hcpos)] at h
  have hsq : 1 < e (c * β) ^ 2 := by
    have h : 1 < |e (c * β)| := by
      rw [← Real.norm_eq_abs, hnorm, norm_mul]
      exact hlarge
    nlinarith [sq_abs (e (c * β))]
  apply represents_of_nonnegative_ratio Q e x (hx ▸ neg_ne_zero.mpr ha)
  have heq : a * (1 - c ^ 2 * β ^ 2) / (-a) = (c * β) ^ 2 - 1 := by
    field_simp
    <;> ring
  rw [hx, heq, map_sub, map_pow, map_one]
  exact sub_nonneg.mpr hsq.le

end RealBound

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable [Invertible (2 : K)]

/-- All infinite local representations follow from the constructed other-place
neighborhoods and one explicit excluded-place growth bound. The sole
opposite-value input is intended to be derived from ambient local isotropy. -/
theorem exists_conditions (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0)
    (a c : K) (ha : a ≠ 0) (hc : c ≠ 0) (q : NumberField.InfinitePlace K)
    (hminus : ∃ u, Q.baseChange q.Completion u = -algebraMap K q.Completion a) :
    ∃ (t : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
      (A : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
      (B : ℝ), (∀ w, A w ∈ 𝓝 (t w)) ∧
      ∀ β : K, (∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
        algebraMap K w.1.Completion β ∈ A w) → B < q β →
        ∀ w : NumberField.InfinitePlace K, ∃ u, Q.baseChange w.Completion u =
          algebraMap K w.Completion (a * (1 - c ^ 2 * β ^ 2)) := by
  classical
  choose t A hA hrep using fun w : {w : NumberField.InfinitePlace K // w ≠ q} ↦
    exists_completed_residual_neighborhood Q x hx a c ha hc w.1
  refine ⟨t, A, (q c)⁻¹, hA, ?_⟩
  intro β hβA hβq w
  by_cases hwq : w = q
  · subst w
    obtain ⟨u, hu⟩ := hminus
    have haF : algebraMap K q.Completion a ≠ 0 := (map_ne_zero _).mpr ha
    have hcF : algebraMap K q.Completion c ≠ 0 := (map_ne_zero _).mpr hc
    rcases q.isReal_or_isComplex with hq | hq
    · have hnorm (s : q.Completion) :
          ‖NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hq s‖ = ‖s‖ := by
        have h :=
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hq).dist_eq s 0
        change dist (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hq s)
          (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hq 0) = dist s 0 at h
        simpa only [map_zero, dist_zero_right] using h
      have hβ : ‖algebraMap K q.Completion c‖⁻¹ <
          ‖algebraMap K q.Completion β‖ := by
        simpa only [ScalarNeighborhoods.norm_infinite_algebraMap] using hβq
      obtain ⟨y, hy⟩ := represents_residual_of_norm_large (Q.baseChange q.Completion)
        (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hq) hnorm
        u _ haF hu _ hcF _ hβ
      exact ⟨y, by simpa only [map_mul, map_sub, map_one, map_pow] using hy⟩
    · have hu0 : Q.baseChange q.Completion u ≠ 0 := hu ▸ neg_ne_zero.mpr haF
      exact represents_of_complex_comparison (Q.baseChange q.Completion)
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hq) u hu0 _
  · obtain ⟨u, hu⟩ := hrep ⟨w, hwq⟩ _ (hβA ⟨w, hwq⟩)
    exact ⟨u, by simpa only [map_mul, map_sub, map_one, map_pow] using hu⟩

end NormEuclidean.InfiniteResidualConditions
