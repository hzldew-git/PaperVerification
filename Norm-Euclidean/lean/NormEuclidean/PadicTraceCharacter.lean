import NormEuclidean.RationalPrimaryCharacter
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.LocallyConstant.Basic

/-!
# A constructed continuous p-adic additive character

Rational approximation modulo the integral ball extends the actual
rational primary character. Independence is proved from its computed
kernel. The resulting locally constant character has kernel exactly Z_p,
and the annihilator of Z_p under multiplication is Z_p itself.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.PadicTraceCharacter

open Filter Topology
open scoped Classical

variable (p : ℕ) [hp : Fact p.Prime]

/-- The rational kernel condition is exactly the actual p-adic integral norm condition. -/
theorem rational_norm_iff (q : ℚ) : ‖(q : ℚ_[p])‖ ≤ 1 ↔ ¬ p ∣ q.den := by
  constructor
  · intro h
    have hunit := PadicInt.isUnit_iff.mp (PadicInt.isUnit_den q h)
    rw [PadicInt.norm_def, PadicInt.coe_natCast, Padic.norm_natCast_eq_one_iff] at hunit
    exact hp.out.coprime_iff_not_dvd.mp hunit
  · exact Padic.norm_rat_le_one

/-- The actual rational character vanishes precisely on rational p-adic integers. -/
theorem rational_kernel (q : ℚ) :
    RationalPrimaryCharacter.character p q = 0 ↔ ‖(q : ℚ_[p])‖ ≤ 1 :=
  (RationalPrimaryCharacter.character_eq_zero_iff p q).trans (rational_norm_iff p q).symm

/-- One actual rational approximation modulo the open unit ball. -/
def approximation (x : ℚ_[p]) : ℚ := Classical.choose (Padic.rat_dense p x zero_lt_one)

/-- The chosen rational approximation has error strictly less than one. -/
theorem approximation_spec (x : ℚ_[p]) : ‖x - (approximation p x : ℚ_[p])‖ < 1 :=
  Classical.choose_spec (Padic.rat_dense p x zero_lt_one)

/-- The character value is defined by an actual rational approximation. -/
def value (x : ℚ_[p]) : RationalPrimaryCharacter.Circle :=
  RationalPrimaryCharacter.character p (approximation p x)

/-- Any rational representative within the integral ball gives the same value. -/
theorem value_eq (x : ℚ_[p]) (q : ℚ) (hq : ‖x - (q : ℚ_[p])‖ ≤ 1) :
    value p x = RationalPrimaryCharacter.character p q := by
  have hnorm : ‖((approximation p x - q : ℚ) : ℚ_[p])‖ ≤ 1 := by
    push_cast
    have he : (approximation p x : ℚ_[p]) - q =
        - (x - approximation p x) + (x - q) := by ring
    rw [he]
    exact (Padic.nonarchimedean _ _).trans (max_le
      (by rw [norm_neg]; exact (approximation_spec p x).le) hq)
  have h := (rational_kernel p _).mpr hnorm
  rw [map_sub, sub_eq_zero] at h
  exact h

/-- The extended value respects the original rational character. -/
theorem value_rat (q : ℚ) : value p (q : ℚ_[p]) = RationalPrimaryCharacter.character p q :=
  value_eq p _ q (by simp)

/-- The independently constructed p-adic character is an actual additive homomorphism. -/
def character : ℚ_[p] →+ RationalPrimaryCharacter.Circle where
  toFun := value p
  map_zero' := by simpa using value_rat p 0
  map_add' x y := by
    rw [value_eq p (x + y) (approximation p x + approximation p y) (by
      have he : x + y - ((approximation p x + approximation p y : ℚ) : ℚ_[p]) =
          (x - approximation p x) + (y - approximation p y) := by push_cast; ring
      rw [he]
      exact (Padic.nonarchimedean _ _).trans
        (max_le (approximation_spec p x).le (approximation_spec p y).le))]
    exact map_add _ _ _

/-- The character retains its literal value on every original rational. -/
theorem character_rat (q : ℚ) :
    character p (q : ℚ_[p]) = RationalPrimaryCharacter.character p q := value_rat p q

/-- The exact conductor is proved, rather than imposed on a chosen character. -/
theorem kernel_iff (x : ℚ_[p]) : character p x = 0 ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    have hrat : ‖(approximation p x : ℚ_[p])‖ ≤ 1 := (rational_kernel p _).mp h
    have he : x = (x - approximation p x) + approximation p x := by ring
    rw [he]
    exact (Padic.nonarchimedean _ _).trans (max_le (approximation_spec p x).le hrat)
  · intro h
    have hq : ‖x - ((0 : ℚ) : ℚ_[p])‖ ≤ 1 := by simpa using h
    change value p x = 0
    rw [value_eq p x 0 hq, map_zero]

/-- The actual p-adic character is locally constant on integral balls. -/
theorem locallyConstant : IsLocallyConstant (character p) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one, ?_⟩
  intro y hy
  have hnorm : ‖y - x‖ ≤ 1 := (show ‖y - x‖ < 1 from hy).le
  have h := (kernel_iff p (y - x)).mpr hnorm
  rw [map_sub, sub_eq_zero] at h
  exact h

/-- Local constancy proves continuity of the constructed character. -/
theorem continuous : Continuous (character p) := (locallyConstant p).continuous

/-- Every actual p-adic integer lies in the computed character kernel. -/
theorem on_integers (z : ℤ_[p]) : character p (z : ℚ_[p]) = 0 :=
  (kernel_iff p _).mpr z.property

/-- The annihilator of the actual integral ring under the actual multiplication pairing. -/
theorem integral_annihilator (x : ℚ_[p]) :
    (∀ z : ℤ_[p], character p (x * (z : ℚ_[p])) = 0) ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    have h1 := h 1
    simpa using (kernel_iff p _).mp h1
  · intro h z
    apply (kernel_iff p _).mpr
    rw [norm_mul]
    exact mul_le_one₀ h (norm_nonneg _) z.property

/-- The character is nontrivial, witnessed by the original inverse prime. -/
theorem nontrivial : character p (p : ℚ_[p])⁻¹ ≠ 0 := by
  rw [ne_eq, kernel_iff, norm_inv, Padic.norm_p, inv_inv, not_le]
  exact_mod_cast hp.out.one_lt

end NormEuclidean.PadicTraceCharacter
