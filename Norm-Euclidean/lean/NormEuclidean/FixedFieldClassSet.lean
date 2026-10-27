import NormEuclidean.FixedFieldRankFiniteness
import NormEuclidean.GenusClassNumber

/-!
# Actual isometry classes over a fixed totally real field

These classes allow the quadratic form to vary and retain the entire
integral module. Equality is genuine integral lattice isometry. Fixed-rank
positive norm-Euclidean classes are finite without a class-number or
Pfeuffer finiteness assumption. Varying-field finiteness remains separate.
-/

noncomputable section

namespace NormEuclidean.FixedFieldClassSet

open FixedFieldRankFiniteness PositivePairingBounds

variable (K : Type*) [Field K] [NumberField K]

/-- Equivalence of coordinate models by ambient field isometry of their integral modules. -/
def modelSetoid (n : ℕ) : Setoid (Model K n) where
  r M N := Nonempty (LatticeIsometry M.1 N.1 M.2.carrier N.2.carrier)
  iseqv := ⟨fun M ↦ ⟨LatticeIsometry.identity M.1 M.2⟩,
    fun ⟨e⟩ ↦ ⟨e.inverse⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.compose f⟩⟩

/-- All integral lattice isometry classes, allowing the ambient form to vary. -/
def ClassSet (n : ℕ) := Quotient (modelSetoid K n)

/-- The actual isometry class of a coordinate model. -/
def classOf {n : ℕ} (M : Model K n) : ClassSet K n := Quotient.mk (modelSetoid K n) M

omit [NumberField K] in
/-- Equality in this quotient has exactly the integral-isometry meaning, not genus equivalence. -/
theorem classOf_eq_iff {n : ℕ} (M N : Model K n) :
    classOf K M = classOf K N ↔ Nonempty
      (LatticeIsometry M.1 N.1 M.2.carrier N.2.carrier) := Quotient.eq

/-- The fixed-rank positive norm-Euclidean classes. No rank-three restriction is imposed. -/
def positiveEuclideanClasses (n : ℕ) : Set (ClassSet K n) :=
  {c | ∃ M : Model K n, TotallyPositive M.1 ∧
    HasNumberFieldApproximation M.1 M.2.carrier ∧ classOf K M = c}

/-- Finiteness of actual positive norm-Euclidean lattice isometry classes over a fixed field and
fixed rank, with no freeness, genus, class-number or analytic finiteness premise. -/
theorem finite_positiveEuclideanClasses [NumberField.IsTotallyReal K] (n : ℕ) :
    (positiveEuclideanClasses K n).Finite := by
  obtain ⟨A, hA, hcover⟩ := exists_finite_models K n
  apply (hA.image (classOf K)).subset
  rintro c ⟨M, hpos, hE, rfl⟩
  obtain ⟨N, hN, hMN⟩ := hcover (Fin n → K) M.1 M.2
    hpos.anisotropic hE hpos.nonnegative (by simp)
  exact ⟨N, hN, ((classOf_eq_iff K M N).mpr hMN).symm⟩

/-- In particular, the fixed-field binary finite-class conclusion is now unconditional. -/
theorem finite_binary_classes [NumberField.IsTotallyReal K] :
    (positiveEuclideanClasses K 2).Finite := finite_positiveEuclideanClasses K 2

/-- A bounded finite range of ranks also gives finitely many classes over this fixed field. -/
theorem finite_bounded_rank_classes [NumberField.IsTotallyReal K] (N : ℕ) :
    {p : (n : ℕ) × ClassSet K n | p.1 ≤ N ∧ p.2 ∈ positiveEuclideanClasses K p.1}.Finite := by
  have h := (Set.finite_Iic N).biUnion (fun n _ ↦
    (finite_positiveEuclideanClasses K n).image (Sigma.mk n))
  apply h.subset
  rintro ⟨n, c⟩ ⟨hn, hc⟩
  exact Set.mem_iUnion_of_mem n (Set.mem_iUnion_of_mem hn ⟨c, hc, rfl⟩)

end NormEuclidean.FixedFieldClassSet
