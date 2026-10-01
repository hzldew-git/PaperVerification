import TraceEuclidean.OdlyzkoContourFinite
import TraceEuclidean.OdlyzkoHorizontalLimit

/-!
# A sequence of finite Odlyzko contour identities

This module combines the finite weighted argument principle with the proved
good-height sequence.  Each rectangle has zero-free boundary, its exact
finite zero set is recorded with multiplicity in the residue identity, and
the two horizontal boundary integrals vanish along the sequence.
-/

namespace TraceEuclidean

noncomputable section

open Complex Set Filter Topology

/-- The integrand used throughout the completed-zeta contour argument. -/
abbrev odlyzkoCompletedIntegrand
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  odlyzkoPhi s *
    logDeriv (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s

/-- All finite-contour data along one sequence of expanding, zero-free
rectangles. -/
structure OdlyzkoContourSequenceData
    (K : Type*) [Field K] [NumberField K] where
  Cg : ℝ
  Cg_nonneg : 0 ≤ Cg
  R : ℕ → ℝ
  R_tendsto : Tendsto R atTop atTop
  R_lower : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n
  R_upper : ∀ n : ℕ, R n ≤ 2 * ((n : ℝ) + 1)
  horizontal_bound : ∀ (n : ℕ) (s : ℂ),
    (s.im = R n ∨ s.im = -R n) → -1 ≤ s.re → s.re ≤ 2 →
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 ∧
      ‖logDeriv
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖ ≤
          Cg * ((n : ℝ) + 2) ^ 3
  boundary_nonzero : ∀ n : ℕ, ∀ s ∈
    RectangleBorder (odlyzkoContourLower 2 (R n))
      (odlyzkoContourUpper 2 (R n)),
    DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0
  zeros : ℕ → Finset ℂ
  zero_set : ∀ n : ℕ,
    (zeros n : Set ℂ) =
      Rectangle (odlyzkoContourLower 2 (R n))
          (odlyzkoContourUpper 2 (R n)) ∩
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ⁻¹'
          ({0} : Set ℂ)
  rectangle_identity : ∀ n : ℕ,
    RectangleIntegral' (odlyzkoCompletedIntegrand K)
        (odlyzkoContourLower 2 (R n))
        (odlyzkoContourUpper 2 (R n)) =
      ∑ ρ ∈ zeros n,
        (analyticOrderNatAt
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
            odlyzkoPhi ρ
  zero_sum_re_nonneg : ∀ n : ℕ, 0 ≤
    (∑ ρ ∈ zeros n,
      (analyticOrderNatAt
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
          odlyzkoPhi ρ).re
  horizontal_top_vanish :
    Tendsto (fun n : ℕ ↦ HIntegral (odlyzkoCompletedIntegrand K)
      (-1) 2 (R n)) atTop (𝓝 0)
  horizontal_bottom_vanish :
    Tendsto (fun n : ℕ ↦ HIntegral (odlyzkoCompletedIntegrand K)
      (-1) 2 (-(R n))) atTop (𝓝 0)

/-- The constructed completed Dedekind zeta and exact Odlyzko transform
supply a sequence carrying all finite-contour data needed for the remaining
vertical limiting argument. -/
theorem exists_odlyzkoContourSequenceData
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (OdlyzkoContourSequenceData K) := by
  classical
  obtain ⟨Cg, hCg, R, hRTop, hR, hTop, hBottom⟩ :=
    exists_completedZetaPoleRemoved_horizontal_vanishing_sequence K
  have hBoundary : ∀ n : ℕ, ∀ s ∈
      RectangleBorder (odlyzkoContourLower 2 (R n))
        (odlyzkoContourUpper 2 (R n)),
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 := by
    intro n s hs
    obtain ⟨⟨hbottom | hleft⟩ | htop⟩ | hright := hs
    · obtain ⟨-, -, hgood⟩ := hR n
      have hre : -1 ≤ s.re ∧ s.re ≤ 2 := by
        have hre' := hbottom.1
        simp [odlyzkoContourLower, odlyzkoContourUpper,
          Set.mem_uIcc] at hre'
        rcases hre' with h | h
        · constructor <;> linarith
        · exfalso; linarith
      exact (hgood s (Or.inr (by
        simpa [odlyzkoContourLower] using hbottom.2)) hre.1 hre.2).1
    · apply completedZetaPoleRemoved_ne_zero_of_re_lt_zero
      have hsre' : s.re = 1 - (2 : ℝ) := by
        simpa [odlyzkoContourLower] using hleft.1
      have hsre : s.re = -1 := by linarith
      rw [hsre]
      norm_num
    · obtain ⟨-, -, hgood⟩ := hR n
      have hre : -1 ≤ s.re ∧ s.re ≤ 2 := by
        have hre' := htop.1
        simp [odlyzkoContourLower, odlyzkoContourUpper,
          Set.mem_uIcc] at hre'
        rcases hre' with h | h
        · constructor <;> linarith
        · exfalso; linarith
      exact (hgood s (Or.inl (by
        simpa [odlyzkoContourUpper] using htop.2)) hre.1 hre.2).1
    · apply completedZetaPoleRemoved_ne_zero_of_one_lt_re
      have hsre : s.re = 2 := by
        simpa [odlyzkoContourUpper] using hright.1
      rw [hsre]
      norm_num
  have hFinite : ∀ n : ℕ, ∃ Z : Finset ℂ,
      (Z : Set ℂ) =
        Rectangle (odlyzkoContourLower 2 (R n))
            (odlyzkoContourUpper 2 (R n)) ∩
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ⁻¹'
            ({0} : Set ℂ) ∧
      RectangleIntegral' (odlyzkoCompletedIntegrand K)
          (odlyzkoContourLower 2 (R n))
          (odlyzkoContourUpper 2 (R n)) =
        ∑ ρ ∈ Z,
          (analyticOrderNatAt
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
              odlyzkoPhi ρ := by
    intro n
    have hRn : 0 ≤ R n := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [(hR n).1]
    simpa only [odlyzkoCompletedIntegrand] using
      (exists_odlyzko_symmetric_rectangle_identity
        (K := K) (c := 2) (R := R n) (by norm_num) hRn (hBoundary n))
  choose Z hZset hIdentity using hFinite
  have hNonneg : ∀ n : ℕ, 0 ≤
      (∑ ρ ∈ Z n,
        (analyticOrderNatAt
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
            odlyzkoPhi ρ).re := by
    intro n
    apply completedZetaPoleRemoved_zero_finset_re_nonneg
    intro ρ hρ
    have hρSet : ρ ∈ (Z n : Set ℂ) := hρ
    rw [hZset n] at hρSet
    exact hρSet.2
  refine ⟨{
    Cg := Cg
    Cg_nonneg := hCg
    R := R
    R_tendsto := hRTop
    R_lower := fun n ↦ (hR n).1
    R_upper := fun n ↦ (hR n).2.1
    horizontal_bound := fun n ↦ (hR n).2.2
    boundary_nonzero := hBoundary
    zeros := Z
    zero_set := hZset
    rectangle_identity := hIdentity
    zero_sum_re_nonneg := hNonneg
    horizontal_top_vanish := ?_
    horizontal_bottom_vanish := ?_
  }⟩
  · simpa only [odlyzkoCompletedIntegrand] using hTop
  · simpa only [odlyzkoCompletedIntegrand] using hBottom

end

end TraceEuclidean
