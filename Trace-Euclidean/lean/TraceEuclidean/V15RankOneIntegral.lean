import TraceEuclidean.V15OdlyzkoBridge

/-!
Rank-one norm integrality implies scale integrality, including nonprincipal
fractional-ideal lattices. The proof uses the rank-one identity
`B(x,y)^2 = Q(x) Q(y)` and transitivity of integrality under powers.
-/

namespace TraceEuclidean

noncomputable section

private theorem rank_one_associated_sq
    {F : Type*} [Field F] [CharZero F]
    (Q : QuadraticForm F (Fin 1 → F)) (x y : Fin 1 → F) :
    (QuadraticMap.associated Q x y) ^ 2 = Q x * Q y := by
  by_cases hx : x = 0
  · subst x
    simp
  have hx0 : x 0 ≠ 0 := by
    intro h
    apply hx
    funext i
    fin_cases i
    exact h
  let a : F := y 0 / x 0
  have hy : y = a • x := by
    funext i
    fin_cases i
    dsimp [a]
    exact (div_mul_cancel₀ _ hx0).symm
  rw [hy, QuadraticMap.map_smul]
  simp only [map_smul, smul_eq_mul]
  rw [QuadraticMap.associated_eq_self_apply]
  ring

private theorem rank_one_associated_sq_of_rank
    {F : Type*} [Field F] [CharZero F] {n : ℕ} (hn : n = 1)
    (Q : QuadraticForm F (Fin n → F)) (x y : Fin n → F) :
    (QuadraticMap.associated Q x y) ^ 2 = Q x * Q y := by
  cases n with
  | zero => omega
  | succ k =>
    cases k with
    | zero => exact rank_one_associated_sq Q x y
    | succ k => omega

theorem GlobalLatticePresentation.classic_of_rank_one
    (P : GlobalLatticePresentation) (hrank : P.rank = 1) :
    P.IsClassicIntegral := by
  intro x y
  have hsq := rank_one_associated_sq_of_rank hrank P.Q x.1 y.1
  exact IsIntegral.of_pow (by norm_num : 0 < (2 : ℕ))
    (hsq ▸ (P.integral x).mul (P.integral y))

theorem v15_rank_one_classic_input : V15RankOneClassicInput := by
  intro c hrank
  have hrep : c.representative.IsClassicIntegral :=
    c.representative.classic_of_rank_one (by simpa using hrank)
  rw [← c.mk_representative]
  exact (GlobalLatticeClass.isClassicIntegral_mk c.representative).2 hrep

theorem v15_integral_finite_of_odlyzko_table4_source
    (hTable : V15OdlyzkoTable4Input) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_integral_finite_of_odlyzko_table4 hTable v15_rank_one_classic_input

end

end TraceEuclidean
