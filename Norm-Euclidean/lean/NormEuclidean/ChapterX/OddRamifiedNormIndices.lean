import NormEuclidean.ChapterX.LocalNormIndices
import NormEuclidean.ChapterX.OddSquareClasses

/-!
# Quadratic norm indices at all odd finite places

Odd Hensel lifting supplies the two unit square classes. A parameter of
valuation one has exactly the square units as its unit norms. A norm of
valuation one then reduces every element to a unit. Finally square-factor
normalization removes the restriction on the parameter valuation.
-/

noncomputable section

namespace NormEuclidean.OddRamifiedNormIndices

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation Bong.Dyadic
  QuadraticExtensionNorm ExtensionIdeleNorm
open scoped NumberField WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- An actual odd completion has a nonsquare valuation unit, and it
represents the other unit square class. -/
theorem exists_unit_class (p : HeightOneSpectrum (𝓞 K)) (htwo : (2 : 𝓞 K) ∉ p.asIdeal) :
    ∃ d : (p.adicCompletion K)ˣ, Valued.v d.val = 1 ∧ ¬ IsSquare d ∧
      ∀ a : (p.adicCompletion K)ˣ, Valued.v a.val = 1 →
        IsSquare a ∨ IsSquare (a * d) := by
  let S := LocalRing (integerSubring K) p
  letI : Finite (IsLocalRing.ResidueField S) := CompletionHensel.finite_residue_field p
  letI : HenselianRing S (IsLocalRing.maximalIdeal S) :=
    CompletionHensel.henselian_completed_integers p
  have htwoS : IsUnit (2 : S) := by
    have h := isUnit_algebraMap_localRing (integerSubring K) p htwo
    convert h using 1
    apply Subtype.ext
    exact (map_ofNat (algebraMap K (p.adicCompletion K)) 2).symm
  obtain ⟨d, hd⟩ := OddSquareClasses.exists_nonsquare_residue_unit htwoS
  let f : Sˣ →* (p.adicCompletion K)ˣ := Units.map S.subtype.toMonoidHom
  have hdval : Valued.v (f d).val = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp d.isUnit
  refine ⟨f d, hdval, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    have heq : S.subtype d.val = r.val ^ 2 := by
      have h := congrArg Units.val hr
      change S.subtype d.val = r.val * r.val at h
      exact h.trans (pow_two _).symm
    have hv : Valued.v r.val ^ 2 = 1 := by
      calc
        Valued.v r.val ^ 2 = Valued.v (r.val ^ 2) := (map_pow _ _ _).symm
        _ = Valued.v (S.subtype d.val) := congrArg Valued.v heq.symm
        _ = 1 := hdval
    have hrle : Valued.v r.val ≤ 1 := by
      by_contra! hgt
      exact (one_lt_pow₀ hgt (by decide : 2 ≠ 0)).ne hv.symm
    let z : S := ⟨r.val, hrle⟩
    have hz : d.val = z * z := by
      apply Subtype.ext
      change S.subtype d.val = r.val * r.val
      exact heq.trans (pow_two _)
    exact hd ⟨IsLocalRing.residue S z, by rw [← map_mul, ← hz]⟩
  · intro a ha
    let x : S := ⟨a.val, ha.le⟩
    have hx : IsUnit x :=
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr ha
    have hxa : f hx.unit = a := by
      apply Units.ext
      exact congrArg S.subtype hx.unit_spec
    rcases OddSquareClasses.henselian_square_or_twist htwoS d hx.unit hd with hs | hs
    · exact Or.inl (by simpa only [hxa] using hs.map f)
    · exact Or.inr (by simpa only [map_mul, hxa] using hs.map f)

/-- A parameter with valuation one has norm index two at an odd place. -/
theorem ramified_index_two (p : HeightOneSpectrum (𝓞 K))
    (htwo : (2 : 𝓞 K) ∉ p.asIdeal) (theta : (p.adicCompletion K)ˣ)
    (htheta : Valued.v theta.val = WithZero.exp (-1 : ℤ)) :
    (quadraticNormGroup (p.adicCompletion K) theta).index = 2 := by
  obtain ⟨d, hd, hdnot, hclasses⟩ := exists_unit_class p htwo
  have hdnotnorm : ¬ IsQuadraticNorm (p.adicCompletion K) theta d := by
    intro h
    exact hdnot (OddNormObstruction.square_of_uniformizer_norm p htwo d theta hd htheta h.symm)
  have hn : IsQuadraticNorm (p.adicCompletion K) theta (-theta) := by
    refine ⟨0, 1, ?_⟩
    simp
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨d, hdnotnorm, ?_⟩
  intro b
  let k := WithZero.log (Valued.v b.val)
  let q := (-theta) ^ k
  have hqnorm : q ∈ quadraticNormGroup (p.adicCompletion K) theta :=
    (quadraticNormGroup (p.adicCompletion K) theta).zpow_mem hn k
  have hq : Valued.v q.val = WithZero.exp (-k) := by
    dsimp only [q]
    rw [Units.val_zpow_eq_zpow_val, Units.val_neg, map_zpow₀, Valuation.map_neg,
      htheta, ← WithZero.exp_zsmul]
    congr 1
    simp only [Int.zsmul_eq_mul, mul_neg, mul_one]
  let a := b * q
  have hvb : Valued.v b.val ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr b.ne_zero
  have ha : Valued.v a.val = 1 := by
    change Valued.v (b.val * q.val) = 1
    rw [map_mul, hq, ← WithZero.exp_log hvb,
      ← WithZero.exp_add]
    simp only [k, add_neg_cancel, WithZero.exp_zero]
  rcases hclasses a ha with hs | hs
  · right
    change IsQuadraticNorm (p.adicCompletion K) theta b
    have h := IsQuadraticNorm.mul _ (isQuadraticNorm_of_isSquare_right _ hs)
      (IsQuadraticNorm.inv _ hqnorm)
    simpa only [a, mul_inv_cancel_right] using h
  · left
    change IsQuadraticNorm (p.adicCompletion K) theta (b * d)
    have h := IsQuadraticNorm.mul _ (isQuadraticNorm_of_isSquare_right _ hs)
      (IsQuadraticNorm.inv _ hqnorm)
    simpa [a, mul_assoc, mul_comm, mul_left_comm] using h

/-- Multiplying the parameter by a square does not change the norm subgroup. -/
theorem norm_group_mul_square {F : Type*} [Field F] [CharZero F] (theta q : Fˣ) :
    quadraticNormGroup F (theta * q ^ 2) = quadraticNormGroup F theta := by
  ext a
  exact isQuadraticNorm_mul_square_left_iff F theta a q

/-- A square factor cannot turn a nonsquare parameter into a square. -/
theorem not_square_mul_square {G : Type*} [CommGroup G] (theta q : G)
    (htheta : ¬ IsSquare theta) : ¬ IsSquare (theta * q ^ 2) := by
  rintro ⟨r, hr⟩
  apply htheta
  refine ⟨r / q, ?_⟩
  calc
    theta = (theta * q ^ 2) / q ^ 2 := by simp
    _ = (r / q) * (r / q) := by
      rw [hr]
      simp only [div_eq_mul_inv, pow_two, mul_inv_rev]
      ac_rfl

/-- The complete odd finite-place norm-index formula, without a unit
restriction on the parameter. -/
theorem quadraticNormGroup_index (p : HeightOneSpectrum (𝓞 K))
    (htwo : (2 : 𝓞 K) ∉ p.asIdeal) (theta : (p.adicCompletion K)ˣ) :
    (quadraticNormGroup (p.adicCompletion K) theta).index =
      (by
        classical
        exact if IsSquare theta then 1 else 2) := by
  classical
  split_ifs with hs
  · exact LocalNormIndices.quadraticNormGroup_index_one theta hs
  obtain ⟨pi, hpi⟩ := LocalNormIndices.exists_uniformizer p
  have hvt : Valued.v theta.val ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr theta.ne_zero
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (WithZero.log (Valued.v theta.val))
  · let q := pi ^ k
    have hq : Valued.v q.val = WithZero.exp (-k) := by
      dsimp only [q]
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hpi, ← WithZero.exp_zsmul]
      congr 1
      simp only [Int.zsmul_eq_mul, mul_neg, mul_one]
    have hu : Valued.v (theta * q ^ 2).val = 1 := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hq,
        ← WithZero.exp_log hvt,
        ← WithZero.exp_nsmul, ← WithZero.exp_add, hk]
      convert WithZero.exp_zero using 1 <;> simp
    rw [← norm_group_mul_square theta q]
    exact LocalNormIndices.quadraticNormGroup_index_two p htwo _ hu
      (not_square_mul_square theta q hs)
  · let q := pi ^ (k + 1)
    have hq : Valued.v q.val = WithZero.exp (-(k + 1)) := by
      dsimp only [q]
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hpi, ← WithZero.exp_zsmul]
      congr 1
      simp only [Int.zsmul_eq_mul, mul_neg, mul_one]
    have hu : Valued.v (theta * q ^ 2).val = WithZero.exp (-1 : ℤ) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hq,
        ← WithZero.exp_log hvt,
        ← WithZero.exp_nsmul, ← WithZero.exp_add, hk]
      congr 1
      simp only [Int.nsmul_eq_mul]
      ring
    rw [← norm_group_mul_square theta q]
    exact ramified_index_two p htwo _ hu

end NormEuclidean.OddRamifiedNormIndices
