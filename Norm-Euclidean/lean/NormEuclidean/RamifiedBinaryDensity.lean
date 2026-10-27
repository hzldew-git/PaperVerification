import NormEuclidean.UnramifiedBinaryDensity

/-!
# Odd ramified binary norm-model self-densities

The annihilator count is derived from actual multiplication fibers and
quotient rings. If the parameter generates the r-th power of the maximal
ideal, with r positive, then every level above r has self-density 2 q^r.
No dyadic formula or arbitrary-lattice normal-form theorem is assumed.
-/

noncomputable section

namespace NormEuclidean.RamifiedBinaryDensity

open BinaryCongruenceDensity LocalNormDensity UnramifiedBinaryDensity IsLocalRing

section FiniteRing

variable {R : Type*} [CommRing R] [Finite R]

/-- In a finite ring the parameter annihilator and principal quotient have equal size. -/
theorem annihilator_card (d : R) :
    Nat.card (annihilator d) = Nat.card (R ⧸ Ideal.span ({d} : Set R)) := by
  let I := Ideal.span ({d} : Set R)
  let f : R →+ I :=
    { toFun := fun x ↦ ⟨d * x, Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self d)⟩
      map_zero' := Subtype.ext (mul_zero d)
      map_add' := fun x y ↦ Subtype.ext (mul_add d x y) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp y.property
    exact ⟨x, Subtype.ext hx.symm⟩
  have hk : f.ker = (annihilator d).toAddSubgroup := by
    ext x
    change f x = 0 ↔ x ∈ annihilator d
    rw [mem_annihilator]
    exact Subtype.ext_iff
  have hc' := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup I) ≃+ I).toEquiv, hk] at hc'
  have hq := I.toAddSubgroup.card_mul_index
  change Nat.card I * Submodule.cardQuot I = Nat.card R at hq
  rw [Submodule.cardQuot_apply] at hq
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card I)
  exact hc'.trans (by simpa only [mul_comm] using hq.symm)

end FiniteRing

section Local

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Finite (ResidueField R)]

/-- At any odd positive level with nonzero parameter, the exact self-density
is the residue norm density times the actual parameter quotient cardinality. -/
theorem level_formula (d : R) (h2 : IsUnit (2 : R)) (n : ℕ)
    (hd : Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) d ≠ 0) :
    levelDensity R d n = density (ResidueField R) (residue R d) *
      Nat.card (Level R n ⧸ Ideal.span ({Ideal.Quotient.mk _ d} : Set (Level R n))) := by
  have h2n : IsUnit (2 : Level R n) := by
    simpa only [map_ofNat] using h2.map
      (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
  rw [levelDensity, selfDensity_odd _ hd h2n, annihilator_card,
    density_reduction (reduction R n) (Ideal.Quotient.factor_surjective _) h2n]
  rfl

end Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]

omit [Finite (ResidueField R)] in
private theorem level_parameter_ne_zero (d : R) (r n : ℕ)
    (hd : Ideal.span ({d} : Set R) = maximalIdeal R ^ r) :
    Ideal.Quotient.mk (maximalIdeal R ^ (r + n + 1)) d ≠ 0 := by
  intro he
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp he
  have hle : maximalIdeal R ^ r ≤ maximalIdeal R ^ (r + 1) := by
    rw [← hd]
    apply Ideal.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    exact Ideal.pow_le_pow_right (by omega : r + 1 ≤ r + n + 1) hm
  exact (not_le_of_gt (Ideal.pow_succ_lt_pow
    (IsDiscreteValuationRing.not_a_field R) r)) hle

/-- The actual annihilator at every level above the parameter valuation has q^r elements. -/
theorem level_annihilator_card (d : R) (r n : ℕ)
    (hd : Ideal.span ({d} : Set R) = maximalIdeal R ^ r) :
    Nat.card (annihilator (Ideal.Quotient.mk (maximalIdeal R ^ (r + n + 1)) d)) =
      Nat.card (ResidueField R) ^ r := by
  let J := maximalIdeal R ^ (r + n + 1)
  let I := Ideal.span ({d} : Set R)
  have hJI : J ≤ I := by
    dsimp [J, I]
    rw [hd]
    exact Ideal.pow_le_pow_right (by omega)
  rw [annihilator_card]
  have he : Ideal.span ({Ideal.Quotient.mk J d} : Set (R ⧸ J)) =
      I.map (Ideal.Quotient.mk J) := by simp [I, Ideal.map_span]
  rw [he, Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hJI).toEquiv]
  change Nat.card (R ⧸ Ideal.span ({d} : Set R)) = _
  rw [hd]
  exact cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field R)

/-- Odd ramified norm-model density at every level strictly above the valuation. -/
theorem ramified_level (d : R) (h2 : IsUnit (2 : R)) (r n : ℕ) (hr : 0 < r)
    (hd : Ideal.span ({d} : Set R) = maximalIdeal R ^ r) :
    levelDensity R d (r + n) = 2 * (Nat.card (ResidueField R) : ℝ) ^ r := by
  have hdn := level_parameter_ne_zero R d r n hd
  have h2n : IsUnit (2 : Level R (r + n)) := by
    simpa only [map_ofNat] using h2.map
      (Ideal.Quotient.mk (maximalIdeal R ^ (r + n + 1)))
  have hres : residue R d = 0 := by
    apply (residue_eq_zero_iff d).mpr
    apply Ideal.pow_le_self (Nat.ne_zero_of_lt hr)
    rw [← hd]
    exact Ideal.mem_span_singleton_self d
  have h2k : (2 : ResidueField R) ≠ 0 := by
    simpa only [map_ofNat] using (h2.map (residue R)).ne_zero
  rw [levelDensity, selfDensity_odd _ hdn h2n, level_annihilator_card R d r n hd,
    density_reduction (reduction R (r + n)) (Ideal.Quotient.factor_surjective _) h2n]
  change density (ResidueField R) (residue R d) * _ = _
  rw [hres, ramified_density h2k, Nat.cast_pow]

/-- The ramified factor is the limit of the literal full Gram congruence counts. -/
theorem ramified_limit (d : R) (h2 : IsUnit (2 : R)) (r : ℕ) (hr : 0 < r)
    (hd : Ideal.span ({d} : Set R) = maximalIdeal R ^ r) :
    Filter.Tendsto (levelDensity R d) Filter.atTop
      (nhds (2 * (Nat.card (ResidueField R) : ℝ) ^ r)) := by
  apply Filter.Tendsto.congr' (f₁ := fun _ ↦ 2 * (Nat.card (ResidueField R) : ℝ) ^ r)
    _ tendsto_const_nhds
  apply Filter.eventually_atTop.mpr
  refine ⟨r, fun n hn ↦ ?_⟩
  have h := ramified_level R d h2 r (n - r) hr hd
  simpa only [Nat.add_sub_of_le hn] using h.symm

end NormEuclidean.RamifiedBinaryDensity
