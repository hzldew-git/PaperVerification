import TraceEuclidean.QuadraticGeometry

/-!
The arithmetic endgame of Theorem 1.8 in the explicit coordinate model of
the two integral bases of a real quadratic field.
-/

namespace TraceEuclidean

noncomputable section

abbrev RationalPoint := PlanePoint ℚ

def realQuadraticCostRat (m : ℕ) :
    RationalPoint → IntegralPoint → ℚ :=
  if m % 4 = 1 then caseIICostOver (m : ℚ)
  else caseICostOver (m : ℚ)

/-- Strict `2`-trace Euclideanity in rational coordinates. -/
def CoordinateTwoTraceEuclidean (m : ℕ) : Prop :=
  ∀ x : RationalPoint, ∃ z : IntegralPoint,
    realQuadraticCostRat m x z < 2

theorem caseII_radiusSqOver_eq (m : ℕ) :
    caseIIRadiusSqOver (m : ℚ) = caseIIRadiusSq m := by
  rfl

/-- Coordinate form of the real-quadratic classification theorem. -/
theorem coordinate_two_trace_euclidean_iff {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    CoordinateTwoTraceEuclidean m ↔ m = 2 ∨ m = 5 ∨ m = 13 := by
  constructor
  · intro hE
    by_cases hmod : m % 4 = 1
    · have hcase : ∀ x : RationalPoint,
          ∃ z : IntegralPoint, caseIICostOver (m : ℚ) x z < 2 := by
        simpa [CoordinateTwoTraceEuclidean, realQuadraticCostRat, hmod] using hE
      have hm5 : 5 ≤ m := by omega
      obtain ⟨z, hz⟩ := hcase (caseIIVertexOver (m : ℚ))
      have hlower := caseII_vertex_lower_over (K := ℚ)
        (m := (m : ℚ)) (by exact_mod_cast (show 3 ≤ m by omega)) z
      have hradius : caseIIRadiusSq m ≤ 2 := by
        rw [← caseII_radiusSqOver_eq]
        exact (hlower.trans_lt hz).le
      rcases caseII_closed_candidates hm hsq hmod hradius with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · have hcase : ∀ x : RationalPoint,
          ∃ z : IntegralPoint, caseICostOver (m : ℚ) x z < 2 := by
        simpa [CoordinateTwoTraceEuclidean, realQuadraticCostRat, hmod] using hE
      obtain ⟨z, hz⟩ := hcase (1 / 2, 1 / 2)
      have hlower := caseI_midpoint_lower_over (K := ℚ)
        (m := (m : ℚ)) (by positivity) z
      have hm_lt_three : (m : ℚ) < 3 := by
        unfold caseIRadiusSqOver at hlower
        linarith
      have hmnat : m < 3 := by exact_mod_cast hm_lt_three
      exact Or.inl (by omega)
  · rintro (rfl | rfl | rfl)
    · intro x
      simpa [CoordinateTwoTraceEuclidean, realQuadraticCostRat] using
        (caseI_two_upper_over (K := ℚ) x)
    · intro x
      obtain ⟨z, hz⟩ := caseII_upper_over (K := ℚ)
        (m := (5 : ℚ)) (by norm_num) x
      refine ⟨z, ?_⟩
      have hlt : caseIICostOver (5 : ℚ) x z < 2 :=
        hz.trans_lt (by norm_num [caseIIRadiusSqOver])
      simpa [realQuadraticCostRat] using hlt
    · intro x
      obtain ⟨z, hz⟩ := caseII_upper_over (K := ℚ)
        (m := (13 : ℚ)) (by norm_num) x
      refine ⟨z, ?_⟩
      have hlt : caseIICostOver (13 : ℚ) x z < 2 :=
        hz.trans_lt (by norm_num [caseIIRadiusSqOver])
      simpa [realQuadraticCostRat] using hlt

end

end TraceEuclidean
