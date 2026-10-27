import NormEuclidean.ChapterX.GenusNormalization

/-!
# Improper integral reflections over discrete valuation integers

A nonzero represented value of least divisibility supplies an integral
reflection, even at residue characteristic two. The least divisibility
is constructed from the natural-number valuation exponents of integral
nonzero values, rather than supplied as a classification premise.
-/

noncomputable section

namespace NormEuclidean.LocalIntegralReflection

open QuadraticMap ProperSpinor SpinorBaseChange CompletedIntegralLattice IsDedekindDomain

section Discrete

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
variable (v : Valuation F (WithZero (Multiplicative ℤ)))

/-- A nonzero integral value has a natural-number divisibility exponent. -/
theorem exists_integral_exponent {a : F} (ha : a ≠ 0) (hint : v a ≤ 1) :
    ∃ n : ℕ, v a = WithZero.exp (-(n : ℤ)) := by
  have hva : v a ≠ 0 := (Valuation.ne_zero_iff v).mpr ha
  have hlog : WithZero.log (v a) ≤ 0 := by
    simpa only [WithZero.log_one] using
      (WithZero.log_le_log hva one_ne_zero).mpr hint
  let n := (-WithZero.log (v a)).toNat
  have hn : (n : ℤ) = -WithZero.log (v a) := Int.toNat_of_nonneg (neg_nonneg.mpr hlog)
  refine ⟨n, ?_⟩
  rw [hn, neg_neg, WithZero.exp_log hva]

/-- Least divisibility is attained by a nonzero represented value of any
norm-integral module having an anisotropic vector. Finite generation is unnecessary. -/
theorem exists_maximal_value (Q : QuadraticForm F E)
    (M : Submodule v.valuationSubring E) (hint : ∀ x ∈ M, v (Q x) ≤ 1)
    (hex : ∃ x ∈ M, Q x ≠ 0) :
    ∃ x ∈ M, Q x ≠ 0 ∧ ∀ y ∈ M, v (Q y) ≤ v (Q x) := by
  classical
  have he : ∃ n : ℕ, ∃ x ∈ M, Q x ≠ 0 ∧ v (Q x) = WithZero.exp (-(n : ℤ)) := by
    obtain ⟨x, hx, hx0⟩ := hex
    obtain ⟨n, hn⟩ := exists_integral_exponent v hx0 (hint x hx)
    exact ⟨n, x, hx, hx0, hn⟩
  obtain ⟨x, hx, hx0, hxv⟩ := Nat.find_spec he
  refine ⟨x, hx, hx0, ?_⟩
  intro y hy
  by_cases hy0 : Q y = 0
  · simp only [hy0, map_zero, zero_le]
  · obtain ⟨n, hn⟩ := exists_integral_exponent v hy0 (hint y hy)
    have hmin : Nat.find he ≤ n := Nat.find_min' he ⟨y, hy, hy0, hn⟩
    rw [hn, hxv, WithZero.exp_le_exp]
    exact neg_le_neg (Int.ofNat_le.mpr hmin)

/-- A vector of maximal quadratic valuation defines an actual integral
reflection. No integral inverse of two or of its quadratic value is assumed. -/
theorem reflection_mem_iff_of_maximal_value (Q : QuadraticForm F E)
    (M : Submodule v.valuationSubring E) (x : E) (hx : x ∈ M) (hx0 : Q x ≠ 0)
    (hmax : ∀ y ∈ M, v (Q y) ≤ v (Q x)) (y : E) :
    IntegralReflection.linearEquiv Q x hx0 y ∈ M ↔ y ∈ M := by
  have hforward : ∀ y ∈ M, IntegralReflection.linearEquiv Q x hx0 y ∈ M := by
    intro y hy
    have hpolar : v (polar Q x y) ≤ v (Q x) := by
      exact (v.map_sub _ _).trans (max_le
        ((v.map_sub _ _).trans (max_le (hmax _ (M.add_mem hx hy)) (hmax x hx)))
        (hmax y hy))
    have hval : v ((Q x)⁻¹ * polar Q x y) ≤ 1 := by
      rw [mul_comm, ← div_eq_mul_inv, map_div₀]
      exact (div_le_one₀ ((Valuation.ne_zero_iff v).mpr hx0).bot_lt).mpr hpolar
    rw [IntegralReflection.linearEquiv_apply]
    exact M.sub_mem hy (M.smul_mem
      (⟨(Q x)⁻¹ * polar Q x y, hval⟩ : v.valuationSubring) hx)
  constructor
  · intro hy
    simpa only [IntegralReflection.involutive Q x hx0 y] using hforward _ hy
  · exact hforward y

end Discrete

section NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- Every finite completed lattice in a regular positive-dimensional space
has an improper integral reflection, including dyadic completions. -/
theorem exists_completed_improper_reflection (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Lattice (integerSubring K) Q)
    (v : HeightOneSpectrum (integerSubring K)) :
    ∃ e : LatticeIsometry (form (integerSubring K) v Q) (form (integerSubring K) v Q)
      (carrier (integerSubring K) v L.carrier) (carrier (integerSubring K) v L.carrier),
      LinearEquiv.det e.toLinearEquiv = (-1 : (LocalField (integerSubring K) v)ˣ) := by
  let q := SpinorBridge.quadraticSpace Q hQ
  obtain ⟨u, hu⟩ := q.exists_isAnisotropic_of_finrank_pos hpos
  have hu0 : Q u ≠ 0 := by simpa [q, Bong.QuadraticSpace.IsAnisotropic] using hu
  obtain ⟨d, hd0, hdu⟩ := ScalarExtension.exists_denominator L.carrier L.full u
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  have hQdu : Q ((d : K) • u) ≠ 0 := by
    rw [Q.map_smul, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero hdK hdK) hu0
  let P := form (integerSubring K) v Q
  let M := carrier (integerSubring K) v L.carrier
  let value : Valuation (LocalField (integerSubring K) v) (WithZero (Multiplicative ℤ)) :=
    Valued.v
  have hint : ∀ x ∈ M, value (P x) ≤ 1 :=
    carrier_integral (integerSubring K) v Q L.carrier L.integral
  have hex : ∃ x ∈ M, P x ≠ 0 :=
    ⟨inclusion (integerSubring K) v ((d : K) • u),
      inclusion_mem (integerSubring K) v L.carrier hdu,
      form_inclusion_ne_zero (integerSubring K) v Q _ hQdu⟩
  obtain ⟨x, hx, hx0, hmax⟩ := exists_maximal_value value P M hint hex
  let e : LatticeIsometry P P M M :=
    { toLinearEquiv := IntegralReflection.linearEquiv P x hx0
      q_eq := IntegralReflection.q_eq P x hx0
      mem_iff := reflection_mem_iff_of_maximal_value value P M x hx hx0 hmax }
  refine ⟨e, ?_⟩
  change determinantHom P (ambientReflection P x hx0) = -1
  exact ambientReflection_det P (form_polarBilin_nondegenerate (integerSubring K) v Q hQ) x hx0

/-- Every ordinary finite-place comparison can be made proper. The integral
reflection is constructed for a general lattice, without a represented-unit premise. -/
theorem sameProperGenus_of_sameGenus (hQ : Q.polarBilin.Nondegenerate)
    (L M : Lattice (integerSubring K) Q) (h : SameGenus Q L M) : SameProperGenus Q L M := by
  by_cases hpos : 0 < Module.finrank K V
  · intro v
    obtain ⟨e⟩ := h.1 v
    have hQv := form_polarBilin_nondegenerate (integerSubring K) v Q hQ
    rcases (SpinorBridge.toBongIsometry hQv hQv e).det_eq_one_or_neg_one with he | he
    · exact ⟨e, he⟩
    · obtain ⟨r, hr⟩ := exists_completed_improper_reflection Q hQ hpos L v
      refine ⟨r.compose e, ?_⟩
      change LinearEquiv.det e.toLinearEquiv = -1 at he
      change LinearEquiv.det (r.toLinearEquiv.trans e.toLinearEquiv) = 1
      rw [LinearEquiv.det_trans, hr, he]
      simp
  · haveI : Subsingleton V := (Module.finrank_zero_iff (R := K) (M := V)).mp (by omega)
    intro v
    obtain ⟨e⟩ := h.1 v
    refine ⟨e, ?_⟩
    rw [show e.toLinearEquiv = LinearEquiv.refl _ _ from Subsingleton.elim _ _]
    exact LinearEquiv.det_refl

theorem sameGenus_iff_sameProperGenus (hQ : Q.polarBilin.Nondegenerate)
    (L M : Lattice (integerSubring K) Q) : SameGenus Q L M ↔ SameProperGenus Q L M :=
  ⟨sameProperGenus_of_sameGenus Q hQ L M, NormEuclidean.sameGenus_of_sameProperGenus Q⟩

end NumberField

end NormEuclidean.LocalIntegralReflection
