import NormEuclidean.BinaryGramIdeals
import NormEuclidean.BinaryLocalMassFactors

/-!
# Odd density comparison for arbitrary primitive binary Gram matrices

Normal-form data are constructed from symmetry and primitivity. Integral
congruence counts, determinant ideals and the volume-normalized factors
are transported at every positive level. Nonunimodular factors are then
proved equal to two beyond a constructed valuation threshold.
-/

noncomputable section

namespace NormEuclidean.IntegralBinaryDensity

open IsLocalRing PrimitiveBinaryNormalForm
open scoped Matrix

section CoefficientMap

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An actual integral norm basis transports the full count through every coefficient map. -/
theorem density_map_norm (f : R →+* S) (G : Matrix (Fin 2) (Fin 2) R)
    (P : (Matrix (Fin 2) (Fin 2) R)ˣ) (a : Rˣ) (d : R)
    (h : P.val.transpose * G * P.val = (a : R) • BinaryCongruenceDensity.gram d) :
    GramDensityTransport.density (G.map f) = BinaryCongruenceDensity.selfDensity S (f d) := by
  let Q := Units.map f.mapMatrix.toMonoidHom P
  let b := Units.map f.toMonoidHom a
  have hQ : Q.val = P.val.map f := rfl
  have hb : b.val = f a.val := rfl
  have he : ((a : R) • BinaryCongruenceDensity.gram d).map f =
      (b : S) • BinaryCongruenceDensity.gram (f d) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [BinaryCongruenceDensity.gram, hb]
  have hmap : Q.val.transpose * G.map f * Q.val =
      (b : S) • BinaryCongruenceDensity.gram (f d) := by
    rw [hQ, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h, he]
  calc
    _ = GramDensityTransport.density (Q.val.transpose * G.map f * Q.val) :=
      (GramDensityTransport.density_basis _ Q).symm
    _ = GramDensityTransport.density ((b : S) • BinaryCongruenceDensity.gram (f d)) := by
      rw [hmap]
    _ = _ := GramDensityTransport.density_unit _ b

end CoefficientMap

section Discriminant

variable {R : Type*} [CommRing R]

/-- A constructed norm parameter differs from minus the determinant by a unit square. -/
theorem parameter_unit_square (G : Matrix (Fin 2) (Fin 2) R)
    (P : (Matrix (Fin 2) (Fin 2) R)ˣ) (a : Rˣ) (d : R)
    (h : P.val.transpose * G * P.val = (a : R) • BinaryCongruenceDensity.gram d) :
    ∃ u : Rˣ, d = -G.det * u.val ^ 2 := by
  have hp : IsUnit P.val.det := (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
  let p := hp.unit
  let v := (a⁻¹ : Rˣ).val
  have hi : (a : R) * v = 1 := a.val_inv
  have hd := congrArg Matrix.det h
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at hd
  have hg : (BinaryCongruenceDensity.gram d).det = -d := by
    simp [BinaryCongruenceDensity.gram, Matrix.det_fin_two]
  rw [hg] at hd
  refine ⟨p * a⁻¹, ?_⟩
  change d = -G.det * (p.val * v) ^ 2
  rw [show p.val = P.val.det from hp.unit_spec]
  linear_combination v ^ 2 * hd - d * ((a : R) * v + 1) * hi

private theorem square_iff_unit_square (x d : R) (u : Rˣ) (he : d = x * u.val ^ 2) :
    IsSquare d ↔ IsSquare x := by
  constructor
  · intro h
    have h' := h.mul (IsSquare.sq (u⁻¹ : Rˣ).val)
    rw [he, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one] at h'
    exact h'
  · intro h
    rw [he]
    exact h.mul (IsSquare.sq u.val)

/-- Residue-square behavior is the intrinsic discriminant behavior of the original matrix. -/
theorem residue_square_iff {k : Type*} [Field k] (f : R →+* k)
    (G : Matrix (Fin 2) (Fin 2) R) (P : (Matrix (Fin 2) (Fin 2) R)ˣ) (a : Rˣ) (d : R)
    (h : P.val.transpose * G * P.val = (a : R) • BinaryCongruenceDensity.gram d) :
    IsSquare (f d) ↔ IsSquare (f (-G.det)) := by
  obtain ⟨u, hu⟩ := parameter_unit_square G P a d h
  apply square_iff_unit_square _ _ (Units.map f.toMonoidHom u)
  change f d = f (-G.det) * (f u.val) ^ 2
  simpa only [map_mul, map_pow] using congrArg f hu

end Discriminant

section Local

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The actual Gram congruence density on the quotient by m^(n+1). -/
def levelDensity (G : Matrix (Fin 2) (Fin 2) R) (n : ℕ) : ℝ :=
  GramDensityTransport.density (G.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))))

/-- Division by the actual Gram determinant quotient cardinality. -/
def factor (G : Matrix (Fin 2) (Fin 2) R) (n : ℕ) : ℝ :=
  levelDensity R G n / Nat.card (R ⧸ BinaryGramIdeals.volume G)

/-- Every primitive symmetric odd Gram matrix has a constructed norm parameter
which works simultaneously at all levels and for the actual volume factor. -/
theorem exists_norm_comparison (G : Matrix (Fin 2) (Fin 2) R) (hs : G.IsSymm)
    (hp : Primitive G) (h2 : IsUnit (2 : R)) :
    ∃ d : R, BinaryGramIdeals.volume G = Ideal.span ({d} : Set R) ∧
      (∀ n, levelDensity R G n = UnramifiedBinaryDensity.levelDensity R d n) ∧
      (∀ n, factor R G n = BinaryLocalMassFactors.factor R d n) := by
  obtain ⟨P, a, d, he⟩ := exists_norm_basis G hs hp h2
  have hv := BinaryGramIdeals.volume_of_norm_basis G P a d he
  have hc (n : ℕ) : levelDensity R G n = UnramifiedBinaryDensity.levelDensity R d n :=
    density_map_norm (Ideal.Quotient.mk _) G P a d he
  refine ⟨d, hv, hc, fun n ↦ ?_⟩
  unfold factor BinaryLocalMassFactors.factor
  rw [hc, hv, BinaryLocalMassFactors.gram_volume]

/-- Basis invariance holds before taking any limit or assuming nondegeneracy. -/
theorem level_basis (G : Matrix (Fin 2) (Fin 2) R)
    (P : (Matrix (Fin 2) (Fin 2) R)ˣ) (n : ℕ) :
    levelDensity R (P.val.transpose * G * P.val) n = levelDensity R G n := by
  let f := Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))
  let Q := Units.map f.mapMatrix.toMonoidHom P
  have hQ : Q.val = P.val.map f := rfl
  have he : ((P.val.transpose * G * P.val).map f) = Q.val.transpose * G.map f * Q.val := by
    rw [hQ, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  unfold levelDensity
  rw [he]
  exact GramDensityTransport.density_basis _ Q

/-- The residue character is defined directly from the original Gram determinant. -/
def character (G : Matrix (Fin 2) (Fin 2) R) : ℤ := by
  classical
  exact if IsSquare (residue R (-G.det)) then 1 else -1

/-- Every odd unimodular symmetric binary matrix has its intrinsic Euler
factor at every level. No primitive or normal-basis premise is supplied. -/
theorem unimodular_density [IsNoetherianRing R] [Finite (ResidueField R)]
    (G : Matrix (Fin 2) (Fin 2) R) (hs : G.IsSymm) (hd : IsUnit G.det)
    (h2 : IsUnit (2 : R)) (n : ℕ) :
    levelDensity R G n = 1 - (character R G : ℝ) / Nat.card (ResidueField R) := by
  obtain ⟨P, a, d, he⟩ := exists_norm_basis G hs (BinaryGramIdeals.primitive_of_unit_det G hd) h2
  have hv := BinaryGramIdeals.volume_of_norm_basis G P a d he
  have hdu : IsUnit d := by
    apply Ideal.span_singleton_eq_top.mp
    rw [← hv]
    exact Ideal.span_singleton_eq_top.mpr hd
  have hsquare := residue_square_iff (residue R) G P a d he
  have hc : levelDensity R G n = UnramifiedBinaryDensity.levelDensity R d n :=
    density_map_norm (Ideal.Quotient.mk _) G P a d he
  rw [hc, UnramifiedBinaryDensity.levelDensity_eq R d hdu h2 n]
  by_cases ht : IsSquare (residue R (-G.det))
  · obtain ⟨s, hval⟩ := hsquare.mpr ht
    have hs0 : s ≠ 0 := by
      intro hzero
      have hd0 := (residue_ne_zero_iff_isUnit d).mpr hdu
      apply hd0
      simpa [hzero] using hval
    have h2k : (2 : ResidueField R) ≠ 0 := by
      simpa only [map_ofNat] using (h2.map (residue R)).ne_zero
    rw [hval, ← pow_two, LocalNormDensity.split_density s hs0 h2k]
    have hχ : character R G = 1 := if_pos ht
    rw [hχ]
    norm_num
  · rw [LocalNormDensity.nonsplit_density _ (fun h ↦ ht (hsquare.mp h))]
    have hχ : character R G = -1 := if_neg ht
    rw [hχ]
    simp
    ring

/-- The unit determinant's actual volume quotient has cardinality one. -/
theorem factor_unimodular (G : Matrix (Fin 2) (Fin 2) R) (hd : IsUnit G.det) (n : ℕ) :
    factor R G n = levelDensity R G n := by
  unfold factor BinaryGramIdeals.volume
  rw [Ideal.span_singleton_eq_top.mpr hd]
  simp

end Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]

/-- No norm-form or valuation premise is supplied: a primitive nonunimodular
Gram matrix has a constructed positive threshold and eventual factor two. -/
theorem nonunimodular_factor (G : Matrix (Fin 2) (Fin 2) R) (hs : G.IsSymm)
    (hp : Primitive G) (h2 : IsUnit (2 : R)) (hd : G.det ≠ 0) (hu : ¬ IsUnit G.det) :
    ∃ r : ℕ, 0 < r ∧ ∀ n, factor R G (r + n) = 2 := by
  obtain ⟨d, hv, hc, hf⟩ := exists_norm_comparison R G hs hp h2
  have hd0 : d ≠ 0 := by
    intro he
    have hvol : BinaryGramIdeals.volume G = ⊥ := by simpa [he] using hv
    exact hd (Ideal.span_singleton_eq_bot.mp hvol)
  have hv0 : Ideal.span ({d} : Set R) ≠ ⊥ := by simpa using hd0
  obtain ⟨r, hr⟩ := exists_maximalIdeal_pow_eq_of_principal R
    (IsPrincipalIdealRing.principal (maximalIdeal R)) _ hv0
  have hrpos : 0 < r := by
    by_contra hn
    have hz : r = 0 := by omega
    have htop : BinaryGramIdeals.volume G = ⊤ := by simp [hv, hr, hz]
    exact hu (Ideal.span_singleton_eq_top.mp htop)
  refine ⟨r, hrpos, fun n ↦ ?_⟩
  rw [hf]
  exact BinaryLocalMassFactors.factor_positive_valuation R d h2 r n hrpos hr

end NormEuclidean.IntegralBinaryDensity
