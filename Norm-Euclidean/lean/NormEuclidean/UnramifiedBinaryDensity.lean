import NormEuclidean.BinaryCongruenceDensity
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Binary self-density at every odd unimodular congruence level

The coefficient rings are the actual quotients by positive powers of the
maximal ideal. Over a DVR their cardinalities are q to that power. The
normalized full Gram counts are constant at all positive levels, so their
limits are proved without assuming a smoothness or lifting theorem.
-/

noncomputable section

namespace NormEuclidean.UnramifiedBinaryDensity

open IsLocalRing BinaryCongruenceDensity LocalNormDensity

section Local

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The positive congruence level indexed by n has exponent n+1. -/
abbrev Level (n : ℕ) := R ⧸ maximalIdeal R ^ (n + 1)

/-- The actual reduction from a positive level to the original residue field. -/
def reduction (n : ℕ) : Level R n →+* ResidueField R :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))

instance levelNontrivial (n : ℕ) : Nontrivial (Level R n) :=
  (reduction R n).domain_nontrivial

instance levelLocal (n : ℕ) : IsLocalRing (Level R n) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

instance reductionLocal (n : ℕ) : IsLocalHom (reduction R n) :=
  IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective _)

instance levelFinite [IsNoetherianRing R] [Finite (ResidueField R)] (n : ℕ) :
    Finite (Level R n) := by
  letI : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) (n + 1)

/-- The literal normalized matrix count at each positive congruence level. -/
def levelDensity (d : R) (n : ℕ) : ℝ :=
  selfDensity (Level R n) (Ideal.Quotient.mk _ d)

/-- At an odd unimodular level the complete normalized Gram count equals
the residue norm-one density. All lifting and determinant counts are proved. -/
theorem levelDensity_eq [IsNoetherianRing R] [Finite (ResidueField R)]
    (d : R) (hd : IsUnit d) (h2 : IsUnit (2 : R)) (n : ℕ) :
    levelDensity R d n = density (ResidueField R) (residue R d) := by
  have h2n : IsUnit (2 : Level R n) := by
    simpa only [map_ofNat] using h2.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
  rw [levelDensity, selfDensity_unimodular _ (hd.map _) h2n]
  exact density_reduction (reduction R n) (Ideal.Quotient.factor_surjective _) h2n _

/-- Split, non-dyadic and unimodular: the full local factor is 1-1/q. -/
theorem split_level [IsNoetherianRing R] [Finite (ResidueField R)]
    (d : R) (hd : IsUnit d) (h2 : IsUnit (2 : R))
    (s : ResidueField R) (hs : s ^ 2 = residue R d) (n : ℕ) :
    levelDensity R d n = 1 - 1 / Nat.card (ResidueField R) := by
  have hd0 : residue R d ≠ 0 := (residue_ne_zero_iff_isUnit d).mpr hd
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; exact hd0 hs.symm
  have h2k : (2 : ResidueField R) ≠ 0 := by
    simpa only [map_ofNat] using (h2.map (residue R)).ne_zero
  rw [levelDensity_eq R d hd h2 n, ← hs]
  exact split_density s hs0 h2k

/-- Unramified nonsplit, non-dyadic and unimodular: the factor is 1+1/q. -/
theorem nonsplit_level [IsNoetherianRing R] [Finite (ResidueField R)]
    (d : R) (hd : IsUnit d) (h2 : IsUnit (2 : R))
    (hs : ¬ IsSquare (residue R d)) (n : ℕ) :
    levelDensity R d n = 1 + 1 / Nat.card (ResidueField R) := by
  rw [levelDensity_eq R d hd h2 n]
  exact nonsplit_density _ hs

/-- The residue factor is the actual limit of the complete matrix counts. -/
theorem density_limit [IsNoetherianRing R] [Finite (ResidueField R)]
    (d : R) (hd : IsUnit d) (h2 : IsUnit (2 : R)) :
    Filter.Tendsto (levelDensity R d) Filter.atTop
      (nhds (density (ResidueField R) (residue R d))) := by
  have he : levelDensity R d = fun _ ↦ density (ResidueField R) (residue R d) :=
    funext (levelDensity_eq R d hd h2)
  rw [he]
  exact tendsto_const_nhds

end Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The denominator is the expected power of the actual residue cardinality. -/
theorem level_card (n : ℕ) :
    Nat.card (Level R n) = Nat.card (ResidueField R) ^ (n + 1) :=
  cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field R)

/-- The definition agrees exactly with half the q-normalized Gram solution count. -/
theorem levelDensity_normalization (d : R) (n : ℕ) : levelDensity R d n =
    (Nat.card (Solutions (Level R n) (Ideal.Quotient.mk _ d)) : ℝ) /
      (2 * (Nat.card (ResidueField R) : ℝ) ^ (n + 1)) := by
  unfold levelDensity selfDensity
  rw [level_card, Nat.cast_pow]

end NormEuclidean.UnramifiedBinaryDensity
