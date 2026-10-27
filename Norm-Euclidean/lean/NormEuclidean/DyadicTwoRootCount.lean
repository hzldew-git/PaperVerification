import NormEuclidean.DyadicSplitNormDensity

/-!
# Square roots of one in the actual quotient by two

If the ideal of two is the e-th maximal-ideal power in a DVR, roots of
one modulo two are the lifts of one modulo the ceiling half-power.
Their exact count is q^(floor(e/2)), including nilpotents and e=0.
-/

noncomputable section

namespace NormEuclidean.DyadicTwoRootCount

open IsLocalRing DyadicSplitNormDensity

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Maximal-ideal powers compare in reverse order to their exponents. -/
theorem power_le_iff (a b : ℕ) :
    maximalIdeal R ^ a ≤ maximalIdeal R ^ b ↔ b ≤ a :=
  (strictAnti_nat_of_succ_lt fun n ↦
    Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field R) n).le_iff_ge

/-- A square lies in the n-th power exactly when its root lies in the ceiling half-power. -/
theorem square_mem_power (x : R) (n : ℕ) :
    x ^ 2 ∈ maximalIdeal R ^ n ↔ x ∈ maximalIdeal R ^ ((n + 1) / 2) := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨r, hr⟩ := exists_maximalIdeal_pow_eq_of_principal R
    (IsPrincipalIdealRing.principal (maximalIdeal R)) (Ideal.span ({x} : Set R))
    (by simpa using hx)
  have hs : Ideal.span ({x ^ 2} : Set R) = maximalIdeal R ^ (2 * r) := by
    rw [← Ideal.span_singleton_pow, hr, ← pow_mul, Nat.mul_comm r 2]
  rw [← Ideal.span_singleton_le_iff_mem, hs, power_le_iff,
    ← Ideal.span_singleton_le_iff_mem, hr, power_le_iff]
  omega

/-- Squaring to one modulo two is precisely congruence to one modulo the half-power. -/
theorem root_iff_half (e : ℕ)
    (he : Ideal.span ({(2 : R)} : Set R) = maximalIdeal R ^ e) (x : R) :
    (Ideal.Quotient.mk (maximalIdeal R ^ e) x) ^ 2 = 1 ↔
      Ideal.Quotient.mk (maximalIdeal R ^ ((e + 1) / 2)) x = 1 := by
  have hq : (Ideal.Quotient.mk (maximalIdeal R ^ e) x) ^ 2 = 1 ↔
      x ^ 2 - 1 ∈ maximalIdeal R ^ e := by
    constructor
    · intro h
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_pow, map_one, h, sub_self]
    · intro h
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr h
      exact sub_eq_zero.mp (by simpa only [map_sub, map_pow, map_one] using hz)
  have ht : 2 * (x - 1) ∈ maximalIdeal R ^ e := by
    rw [← he]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (2 : R))
  have hs : x ^ 2 - 1 ∈ maximalIdeal R ^ e ↔ (x - 1) ^ 2 ∈ maximalIdeal R ^ e := by
    constructor
    · intro hx
      convert (maximalIdeal R ^ e).sub_mem hx ht using 1; ring
    · intro hx
      convert (maximalIdeal R ^ e).add_mem hx ht using 1; ring
  rw [hq, hs, square_mem_power]
  constructor
  · intro h
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact sub_eq_zero.mp (by simpa only [map_sub, map_one] using hz)
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, h, sub_self]

/-- The actual reduction to the ceiling half-power. -/
def halfReduction (e : ℕ) :
    R ⧸ maximalIdeal R ^ e →+* R ⧸ maximalIdeal R ^ ((e + 1) / 2) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))

/-- Root coordinates modulo two are exactly one additive reduction fiber. -/
def rootsKernelEquiv (e : ℕ)
    (he : Ideal.span ({(2 : R)} : Set R) = maximalIdeal R ^ e) :
    Roots (R ⧸ maximalIdeal R ^ e) ≃ (halfReduction R e).toAddMonoidHom.ker := by
  have hroot (x : R ⧸ maximalIdeal R ^ e) : x ^ 2 = 1 ↔ halfReduction R e x = 1 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact root_iff_half R e he x
  have hf : Function.Surjective (halfReduction R e) :=
    Ideal.Quotient.factor_surjective _
  exact (Equiv.subtypeEquivRight hroot).trans
    (AddMonoidHom.fiberEquivKerOfSurjective hf 1)

/-- Cardinalities of the actual maximal-ideal power quotients. -/
theorem quotient_card (n : ℕ) :
    Nat.card (R ⧸ maximalIdeal R ^ n) = Nat.card (ResidueField R) ^ n :=
  cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field R)

variable [Finite (ResidueField R)]

local instance quotientFinite (n : ℕ) : Finite (R ⧸ maximalIdeal R ^ n) := by
  letI : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

/-- The ceiling-half reduction kernel has q^(floor(e/2)) elements. -/
theorem half_kernel_card (e : ℕ) :
    Nat.card (halfReduction R e).toAddMonoidHom.ker = Nat.card (ResidueField R) ^ (e / 2) := by
  let f := (halfReduction R e).toAddMonoidHom
  have hf : Function.Surjective f := by
    exact Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (by omega))
  have hc := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    Nat.card_congr (AddSubgroup.topEquiv :
      (⊤ : AddSubgroup (R ⧸ maximalIdeal R ^ ((e + 1) / 2))) ≃+ _).toEquiv,
    quotient_card, quotient_card] at hc
  have he : Nat.card (ResidueField R) ^ e =
      Nat.card (ResidueField R) ^ (e / 2) * Nat.card (ResidueField R) ^ ((e + 1) / 2) := by
    rw [← pow_add]
    congr 1
    omega
  exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos _) (hc.trans he)

/-- Exact square-root count in the actual power quotient equal to the quotient by two. -/
theorem roots_power_card (e : ℕ)
    (he : Ideal.span ({(2 : R)} : Set R) = maximalIdeal R ^ e) :
    Nat.card (Roots (R ⧸ maximalIdeal R ^ e)) = Nat.card (ResidueField R) ^ (e / 2) := by
  rw [Nat.card_congr (rootsKernelEquiv R e he), half_kernel_card]

/-- Ring equivalences preserve the actual square-root solution set. -/
def rootsRingEquiv {A B : Type*} [CommRing A] [CommRing B] (f : A ≃+* B) :
    Roots A ≃ Roots B where
  toFun x := ⟨f x.val, by simpa only [map_pow, map_one] using congrArg f x.property⟩
  invFun x := ⟨f.symm x.val, by
    simpa only [map_pow, map_one] using congrArg f.symm x.property⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x.val)
  right_inv x := Subtype.ext (f.apply_symm_apply x.val)

/-- The explicit nilpotent correction modulo two is q^(floor(e/2)). -/
theorem roots_two_card (e : ℕ)
    (he : Ideal.span ({(2 : R)} : Set R) = maximalIdeal R ^ e) :
    Nat.card (Roots (TwoQuotient R)) = Nat.card (ResidueField R) ^ (e / 2) := by
  rw [Nat.card_congr (rootsRingEquiv (Ideal.quotEquivOfEq he))]
  exact roots_power_card R e he

end NormEuclidean.DyadicTwoRootCount
