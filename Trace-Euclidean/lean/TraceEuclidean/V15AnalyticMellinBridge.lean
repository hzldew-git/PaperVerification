import TraceEuclidean.AnalyticMellinPrinciple
import TraceEuclidean.V15DedekindZetaZeros

/-!
# A pole-removed Mellin continuation and its reflection law

The abstract Mellin theorem imported above supplies a globally analytic tail
and identifies the meromorphic expression with the reduced Mellin integral on
its convergence half-plane. Here we remove both possible poles and prove the
resulting entire function's functional equation. A number-field theta/Mellin
identity is still needed to identify it with Dedekind zeta.
-/

namespace TraceEuclidean.V15AnalyticMellin

noncomputable section

open MeasureTheory Set Complex DedekindZeta.MellinPrinciple
open scoped Topology

variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}

/-- The entire candidate obtained by removing the poles at `0` and `k`
from the abstract Mellin continuation. The polynomial expression gives the
correct values at the former pole locations as well. -/
def poleRemovedMellin (f g : ℝ → ℂ) (a₀ b₀ C : ℂ) (k : ℝ) (s : ℂ) : ℂ :=
  -a₀ * (s - (k : ℂ)) + C * b₀ * s +
    s * (s - (k : ℂ)) * mellinTail f g a₀ b₀ C k s

/-- The pole-removed Mellin expression is entire under the proved abstract
Mellin hypotheses. -/
theorem poleRemovedMellin_analyticOn
    (h : IsMellinPair f g a₀ b₀ C k c α) :
    AnalyticOnNhd ℂ (poleRemovedMellin f g a₀ b₀ C k) Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro s
  have ht : DifferentiableAt ℂ (mellinTail f g a₀ b₀ C k) s :=
    (analyticOnNhd_univ_iff_differentiable.mp (mellinTail_analyticOn h)) s
  unfold poleRemovedMellin
  fun_prop

/-- Away from the two poles, the entire expression is exactly their product
with the meromorphic continuation. -/
theorem poleRemovedMellin_eq_mul_continuation
    (s : ℂ) (hs₀ : s ≠ 0) (hsk : s ≠ (k : ℂ)) :
    poleRemovedMellin f g a₀ b₀ C k s =
      s * (s - (k : ℂ)) * mellinContinuation f g a₀ b₀ C k s := by
  unfold poleRemovedMellin mellinContinuation
  field_simp [hs₀, sub_ne_zero.mpr hsk]

/-- The two tail integrals exchange under `s ↦ k-s`. -/
theorem mellinTail_reflection (h : IsMellinPair f g a₀ b₀ C k c α)
    (s : ℂ) :
    mellinTail f g a₀ b₀ C k s =
      C * mellinTail g f b₀ a₀ C⁻¹ k ((k : ℂ) - s) := by
  unfold mellinTail
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro y hy
  have h₂ : (k : ℂ) - ((k : ℂ) - s) - 1 = s - 1 := by ring
  rw [h₂]
  field_simp [h.hC]
  ring

/-- The pole-removed function satisfies the abstract Mellin functional
equation on the whole complex plane, including the former pole locations. -/
theorem poleRemovedMellin_reflection
    (h : IsMellinPair f g a₀ b₀ C k c α) (s : ℂ) :
    poleRemovedMellin f g a₀ b₀ C k s =
      C * poleRemovedMellin g f b₀ a₀ C⁻¹ k ((k : ℂ) - s) := by
  unfold poleRemovedMellin
  rw [mellinTail_reflection h s]
  have h₁ : (k : ℂ) - s - (k : ℂ) = -s := by ring
  rw [h₁]
  field_simp [h.hC]
  ring

/-- The meromorphic Mellin continuation satisfies the corresponding
functional equation away from its two possible poles. -/
theorem mellinContinuation_reflection
    (h : IsMellinPair f g a₀ b₀ C k c α) (s : ℂ)
    (hs₀ : s ≠ 0) (hsk : s ≠ (k : ℂ)) :
    mellinContinuation f g a₀ b₀ C k s =
      C * mellinContinuation g f b₀ a₀ C⁻¹ k ((k : ℂ) - s) := by
  have hRef := poleRemovedMellin_reflection h s
  have ht₀ : (k : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsk)
  have htk : (k : ℂ) - s ≠ (k : ℂ) := by
    intro heq
    apply hs₀
    linear_combination -heq
  rw [poleRemovedMellin_eq_mul_continuation s hs₀ hsk,
    poleRemovedMellin_eq_mul_continuation ((k : ℂ) - s) ht₀ htk] at hRef
  have hfactor : ((k : ℂ) - s) * (((k : ℂ) - s) - (k : ℂ)) =
      s * (s - (k : ℂ)) := by ring
  rw [hfactor] at hRef
  have hfactor_ne : s * (s - (k : ℂ)) ≠ 0 :=
    mul_ne_zero hs₀ (sub_ne_zero.mpr hsk)
  apply mul_left_cancel₀ hfactor_ne
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hRef

/-- A theta/Mellin identity and an entire normalization factor produce the
regularization required by the zero-count development. For Dedekind zeta,
the factor must remove the archimedean Gamma factors and the extra pole factor.
Both its analyticity and the right-half-plane identity remain field-specific
proof obligations. -/
def regularizationOfMellinPair (K : Type*) [Field K] [NumberField K]
    (h : IsMellinPair f g a₀ b₀ C k c α)
    (m : ℂ → ℂ) (hm : AnalyticOnNhd ℂ m Set.univ)
    (hThetaZeta : ∀ s : ℂ, 1 < s.re →
      m s * poleRemovedMellin f g a₀ b₀ C k s =
        (s - 1) * NumberField.dedekindZeta K s) :
    V15DedekindZetaRegularization K where
  value := fun s ↦ m s * poleRemovedMellin f g a₀ b₀ C k s
  analytic := hm.mul (poleRemovedMellin_analyticOn h)
  agrees_right := hThetaZeta

end
end TraceEuclidean.V15AnalyticMellin
