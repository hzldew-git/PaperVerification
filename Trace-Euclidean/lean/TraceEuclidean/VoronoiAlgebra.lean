import Mathlib

/-!
Exact two-dimensional Gram and Voronoi-vertex calculations from the quadratic
field section.  The geometric assertion that the listed facets form the full
Voronoi cell is outside this algebraic module.
-/

namespace TraceEuclidean

noncomputable section

structure R2 where
  x : ℝ
  y : ℝ

def dot (u v : R2) : ℝ := u.x * v.x + u.y * v.y

def normSq (u : R2) : ℝ := dot u u

def sub (u v : R2) : R2 := ⟨u.x - v.x, u.y - v.y⟩

def neg (u : R2) : R2 := ⟨-u.x, -u.y⟩

def v1 : R2 := ⟨1, 1⟩

def caseI_v2 (s : ℝ) : R2 := ⟨s, -s⟩

def caseII_v2 (s : ℝ) : R2 := ⟨(1 + s) / 2, (1 - s) / 2⟩

def caseII_v3 (s : ℝ) : R2 := sub (caseII_v2 s) v1

theorem caseI_gram {s m : ℝ} (hs : s ^ 2 = m) :
    normSq v1 = 2 ∧ normSq (caseI_v2 s) = 2 * m ∧
      dot v1 (caseI_v2 s) = 0 := by
  constructor
  · norm_num [normSq, dot, v1]
  constructor
  · simp only [normSq, dot, caseI_v2]
    nlinarith
  · simp [dot, v1, caseI_v2]

theorem caseII_gram {s m : ℝ} (hs : s ^ 2 = m) :
    normSq v1 = 2 ∧
      normSq (caseII_v2 s) = (m + 1) / 2 ∧
      normSq (caseII_v3 s) = (m + 1) / 2 ∧
      dot v1 (caseII_v3 s) = -1 ∧
      dot v1 (neg (caseII_v2 s)) = -1 ∧
      dot (caseII_v3 s) (neg (caseII_v2 s)) = 1 - (m + 1) / 2 := by
  constructor
  · norm_num [normSq, dot, v1]
  constructor
  · simp only [normSq, dot, caseII_v2]
    nlinarith
  constructor
  · simp only [normSq, dot, caseII_v3, sub, caseII_v2, v1]
    nlinarith
  constructor
  · simp only [dot, caseII_v3, sub, caseII_v2, v1]
    ring
  constructor
  · simp only [dot, neg, caseII_v2, v1]
    ring
  · simp only [dot, caseII_v3, sub, neg, caseII_v2, v1]
    nlinarith

def vertexS (p q r : ℝ) : ℝ := q * (p - r) / (2 * (p * q - r ^ 2))

def vertexT (p q r : ℝ) : ℝ := p * (q - r) / (2 * (p * q - r ^ 2))

def vertexNormSq (p q r : ℝ) : ℝ :=
  (vertexS p q r) ^ 2 * p +
    2 * vertexS p q r * vertexT p q r * r +
    (vertexT p q r) ^ 2 * q

theorem vertex_coefficients_solve {p q r : ℝ} (hdet : p * q - r ^ 2 ≠ 0) :
    vertexS p q r * p + vertexT p q r * r = p / 2 ∧
      vertexS p q r * r + vertexT p q r * q = q / 2 := by
  constructor
  · unfold vertexS vertexT
    field_simp [hdet]
    rw [show q * p - r ^ 2 = p * q - r ^ 2 by ring]
    apply (div_eq_iff hdet).2
    ring
  · unfold vertexS vertexT
    field_simp [hdet]
    rw [show q * p - r ^ 2 = p * q - r ^ 2 by ring]
    apply (div_eq_iff hdet).2
    ring

/-- Equation (6.2) of the manuscript. -/
theorem voronoiVertexNorm_formula {p q r : ℝ} (hdet : p * q - r ^ 2 ≠ 0) :
    vertexNormSq p q r = p * q * (p + q - 2 * r) / (4 * (p * q - r ^ 2)) := by
  rcases vertex_coefficients_solve hdet with ⟨hs, ht⟩
  calc
    vertexNormSq p q r =
        vertexS p q r * (vertexS p q r * p + vertexT p q r * r) +
          vertexT p q r * (vertexS p q r * r + vertexT p q r * q) := by
            unfold vertexNormSq
            ring
    _ = vertexS p q r * (p / 2) + vertexT p q r * (q / 2) := by
          rw [hs, ht]
    _ = p * q * (p + q - 2 * r) / (4 * (p * q - r ^ 2)) := by
          unfold vertexS vertexT
          field_simp [hdet]
          ring

theorem caseI_vertexNorm (m : ℝ) :
    (normSq v1 + normSq (caseI_v2 m)) / 4 = (m ^ 2 + 1) / 2 := by
  simp only [normSq, dot, v1, caseI_v2]
  ring

theorem caseII_vertexNorm_first {m : ℝ} (hm : m ≠ 0) :
    let A := (m + 1) / 2
    vertexNormSq 2 A 1 = A ^ 2 / (2 * m) := by
  dsimp
  have hdetid : 2 * ((m + 1) / 2) - 1 ^ 2 = m := by ring
  rw [voronoiVertexNorm_formula]
  · rw [hdetid]
    field_simp [hm]
    ring
  · rw [hdetid]
    exact hm

theorem caseII_vertexNorm_middle {m : ℝ} (hm : m ≠ 0) :
    let A := (m + 1) / 2
    vertexNormSq A A (A - 1) = A ^ 2 / (2 * m) := by
  dsimp
  have hdetid :
      ((m + 1) / 2) * ((m + 1) / 2) - (((m + 1) / 2) - 1) ^ 2 = m := by
    ring
  rw [voronoiVertexNorm_formula]
  · rw [hdetid]
    field_simp [hm]
    ring
  · rw [hdetid]
    exact hm

theorem caseII_radius_algebra {m : ℝ} (hm : m ≠ 0) :
    (((m + 1) / 2) ^ 2) / (2 * m) = (m + 1) ^ 2 / (8 * m) := by
  field_simp [hm]
  ring

end

end TraceEuclidean
