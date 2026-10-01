/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in
`../THIRD_PARTY_LICENSES/formal-math_APACHE-2.0.txt`.
SPDX-License-Identifier: Apache-2.0
-/

import DedekindZeta.DigammaSeries

/-!
# The real digamma series on a vertical line

This file adapts the initial vertical-line development from
`Zeta23/GammaFacts/Mu.lean` in `anthropics/formal-math`, commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`. Imports and namespaces were
changed for the pinned Lean 4.32.1 project.

For `0 < a < 1`, it rewrites `Re ψ(a + it)` as an absolutely convergent real
series. This is the pointwise input for the remaining Gauss-integral and
hyperbolic-kernel argument.
-/

noncomputable section

namespace DedekindZeta.DigammaVertical

open Complex Filter Topology

variable {a : ℝ}

/-- Points `a + it` with `a ∈ (0,1)` avoid the integer poles. -/
lemma abscissa_mem (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    ((a : ℂ) + Complex.I * (t : ℂ)) ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp only [intCast_re, add_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero] at hre
  have h0 : (0 : ℤ) < k := by
    have h : (0 : ℝ) < (k : ℝ) := by
      rw [hre]
      exact ha0
    exact_mod_cast h
  have h1 : k < 1 := by
    have h : (k : ℝ) < 1 := by
      rw [hre]
      exact ha1
    exact_mod_cast h
  omega

/-- The real part of the `n`th series term on the vertical line `Re z = a`. -/
lemma re_term_eq (t : ℝ) (n : ℕ) :
    ((1 : ℂ) / ((n : ℂ) + 1) -
          1 / (((a : ℂ) + Complex.I * t) + n + 1)).re =
      1 / ((n : ℝ) + 1) -
        ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2) := by
  rw [Complex.sub_re]
  congr 1
  · rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by
          push_cast
          ring,
      show (1 : ℂ) / ((((n : ℝ) + 1 : ℝ)) : ℂ) =
          ((((1 : ℝ) / ((n : ℝ) + 1)) : ℝ) : ℂ) by
        push_cast
        ring]
    exact Complex.ofReal_re _
  · rw [one_div, Complex.inv_re]
    have hre : (((a : ℂ) + Complex.I * t) + n + 1).re =
        (n : ℝ) + 1 + a := by
      simp
      ring
    have him : (((a : ℂ) + Complex.I * t) + n + 1).im = t := by simp
    rw [hre, Complex.normSq_apply, hre, him]
    ring

/-- The real part of `1 / (a + it)`. -/
lemma re_inv_eq (t : ℝ) :
    ((1 : ℂ) / ((a : ℂ) + Complex.I * t)).re =
      a / (a ^ 2 + t ^ 2) := by
  rw [one_div, Complex.inv_re]
  have hre : ((a : ℂ) + Complex.I * t).re = a := by simp
  have him : ((a : ℂ) + Complex.I * t).im = t := by simp
  rw [hre, Complex.normSq_apply, hre, him]
  ring

/-- Absolute summability of the real vertical-line series. -/
lemma summable_re_terms (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    Summable (fun n : ℕ ↦
      1 / ((n : ℝ) + 1) -
        ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hs := DigammaSeries.summable_digamma_series (abscissa_mem ha0 ha1 t)
  have hmap := hs.map Complex.reCLM Complex.continuous_re
  refine hmap.congr fun n ↦ ?_
  exact re_term_eq t n

/-- The real digamma partial-fraction series on `Re z = a`.

For `0 < a < 1`,
`Re ψ(a+it) = -γ - a/(a²+t²) + Σₙ(1/(n+1) - (n+1+a)/((n+1+a)²+t²))`.
-/
theorem re_digamma_vertical (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re =
      -Real.eulerMascheroniConstant - a / (a ^ 2 + t ^ 2) +
        ∑' n : ℕ,
          (1 / ((n : ℝ) + 1) -
            ((n : ℝ) + 1 + a) /
              (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hmem := abscissa_mem ha0 ha1 t
  have h := DigammaSeries.digamma_series hmem
  have hre := congrArg Complex.re h
  rw [hre]
  rw [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
  congr 1
  · congr 1
    exact re_inv_eq t
  · have hs := DigammaSeries.summable_digamma_series hmem
    have hmap := Complex.reCLM.map_tsum hs
    rw [show (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1) -
          1 / (((a : ℂ) + Complex.I * t) + n + 1))).re =
        Complex.reCLM (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1) -
          1 / (((a : ℂ) + Complex.I * t) + n + 1))) from rfl, hmap]
    congr 1
    funext n
    exact re_term_eq t n

end DedekindZeta.DigammaVertical
