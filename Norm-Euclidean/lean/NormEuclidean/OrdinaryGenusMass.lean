import NormEuclidean.PositiveLatticeAutomorphisms
import NormEuclidean.IntegralAutomorphismTransport
import NormEuclidean.ChapterX.GenusFiniteness

/-!
# The ordinary genus mass as an actual finite weighted class sum

Each ordinary integral-isometry class contributes the reciprocal of its
full orthogonal automorphism-group order. Representative independence is
proved by group conjugation. The positive-rank bound is h(L)/2 because the
two signs are distinct automorphisms. This is the arithmetic class-sum
side of the mass formula, not a proof of a Siegel product formula.
-/

noncomputable section

namespace NormEuclidean.OrdinaryGenusMass

open ProperSpinor PositivePairingBounds

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- The actual ordinary lattice class number, distinct from the ideal class number of K. -/
def classNumber (L : Lattice (integerSubring K) Q) : ℕ := Nat.card (GenusClassSet Q L)

/-- The reciprocal of the full orthogonal automorphism-group order. -/
def weight (L : Lattice (integerSubring K) Q) : ℚ :=
  (Nat.card (integralStabilizer Q L.carrier) : ℚ)⁻¹

/-- The inverse-order weight is invariant under actual integral lattice isometry. -/
theorem weight_eq {L M : Lattice (integerSubring K) Q}
    (e : LatticeIsometry Q Q L.carrier M.carrier) : weight L = weight M := by
  simp only [weight, IntegralAutomorphismTransport.card_eq e]

/-- Each actual ordinary genus class has a representative-independent automorphism weight. -/
def classWeight (L : Lattice (integerSubring K) Q) : GenusClassSet Q L → ℚ :=
  Quotient.lift (fun M : GenusMember Q L ↦ weight M.1) (by
    intro A B h
    obtain ⟨e⟩ := h
    exact weight_eq e)

/-- The class weight of a concrete genus member is its genuine inverse automorphism order. -/
theorem classWeight_mk (L : Lattice (integerSubring K) Q) (M : GenusMember Q L) :
    classWeight L (Quotient.mk _ M) = weight M.1 := rfl

/-- The ordinary mass is a finite sum over the actual ordinary integral genus classes. -/
def mass (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q) : ℚ := by
  letI := GenusFiniteness.finite_integral_genus_classes Q hQ L
  letI := Fintype.ofFinite (GenusClassSet Q L)
  exact ∑ c : GenusClassSet Q L, classWeight L c

variable [NumberField.IsTotallyReal K]

/-- A positive lattice has positive weight because its actual automorphism group is finite. -/
theorem weight_pos (L : Lattice (integerSubring K) Q) (hpos : TotallyPositive Q) :
    0 < weight L := by
  letI := PositiveLatticeAutomorphisms.finite_group L hpos
  apply inv_pos.mpr
  exact_mod_cast (Nat.card_pos : 0 < Nat.card (integralStabilizer Q L.carrier))

/-- In positive rank the full ordinary automorphism weight is at most one half. -/
theorem weight_le_half [Nontrivial V] (L : Lattice (integerSubring K) Q)
    (hpos : TotallyPositive Q) : weight L ≤ 1 / 2 := by
  change (Nat.card (integralStabilizer Q L.carrier) : ℚ)⁻¹ ≤ 1 / 2
  rw [← one_div]
  exact one_div_le_one_div_of_le (by norm_num)
    (by exact_mod_cast PositiveLatticeAutomorphisms.two_le_card L hpos)

/-- Every positive ordinary genus class contributes strictly positively. -/
theorem classWeight_pos (L : Lattice (integerSubring K) Q) (hpos : TotallyPositive Q)
    (c : GenusClassSet Q L) : 0 < classWeight L c := by
  induction c using Quotient.inductionOn with
  | h M => exact weight_pos M.1 hpos

/-- The actual ordinary mass of a positive lattice is strictly positive. -/
theorem mass_pos (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (hpos : TotallyPositive Q) : 0 < mass hQ L := by
  letI := GenusFiniteness.finite_integral_genus_classes Q hQ L
  letI := Fintype.ofFinite (GenusClassSet Q L)
  change 0 < ∑ c : GenusClassSet Q L, classWeight L c
  exact Finset.sum_pos (fun c _ ↦ classWeight_pos L hpos c) Finset.univ_nonempty

/-- The class-sum side of the binary mass argument uses the full automorphism group:
ordinary mass is at most half the ordinary lattice class number in every positive rank. -/
theorem mass_le_classNumber_half [Nontrivial V] (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (hpos : TotallyPositive Q) :
    mass hQ L ≤ (classNumber L : ℚ) / 2 := by
  letI := GenusFiniteness.finite_integral_genus_classes Q hQ L
  letI := Fintype.ofFinite (GenusClassSet Q L)
  change (∑ c : GenusClassSet Q L, classWeight L c) ≤ (classNumber L : ℚ) / 2
  calc
    _ ≤ ∑ _c : GenusClassSet Q L, (1 / 2 : ℚ) := by
      apply Finset.sum_le_sum
      intro c _
      induction c using Quotient.inductionOn with
      | h M => exact weight_le_half M.1 hpos
    _ = _ := by simp [classNumber, Nat.card_eq_fintype_card, nsmul_eq_mul, div_eq_mul_inv]

/-- A one-class ordinary genus has mass exactly the inverse of the original automorphism order. -/
theorem mass_eq_weight_of_classNumberOne (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (hH : HasLatticeClassNumberOne Q L) :
    mass hQ L = weight L := by
  letI := GenusFiniteness.finite_integral_genus_classes Q hQ L
  letI := Fintype.ofFinite (GenusClassSet Q L)
  letI : Subsingleton (GenusClassSet Q L) := hH
  letI : Unique (GenusClassSet Q L) :=
    ⟨⟨Quotient.mk _ (selfGenusMember Q L)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have hw (c : GenusClassSet Q L) : classWeight L c = weight L := by
    have heq : c = Quotient.mk _ (selfGenusMember Q L) := Subsingleton.elim _ _
    rw [heq]
    rfl
  change (∑ c : GenusClassSet Q L, classWeight L c) = weight L
  simp [hw]

end NormEuclidean.OrdinaryGenusMass
