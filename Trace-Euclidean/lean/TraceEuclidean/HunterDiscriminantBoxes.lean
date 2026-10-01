import TraceEuclidean.HunterPrimeDegreeBoxes

/-!
# Discriminant-filtered Hunter boxes

The refined Hunter boxes are finite but still contain many polynomials that
cannot generate a number field with a prescribed discriminant.  This module
adds the exact power-basis index equation as an executable filter.  Every
field-realizable Hunter candidate survives the filter together with its
strictly positive index.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- A uniform natural bound for the absolute discriminants occurring in a
finite polynomial box. -/
def polynomialBoxDiscriminantBound (S : Finset ℤ[X]) : ℕ :=
  ∑ f ∈ S, f.discr.natAbs

/-- Each member's absolute discriminant is bounded by the sum of all absolute
discriminants in the finite box. -/
theorem discriminant_le_polynomialBoxDiscriminantBound
    {S : Finset ℤ[X]} {f : ℤ[X]} (hf : f ∈ S) :
    f.discr.natAbs ≤ polynomialBoxDiscriminantBound S := by
  rw [polynomialBoxDiscriminantBound]
  exact Finset.single_le_sum (fun g _ ↦ Nat.zero_le g.discr.natAbs) hf

/-- A finite executable box of polynomial-index pairs satisfying the exact
field-discriminant relation. -/
def indexedDiscriminantBox
    (S : Finset ℤ[X]) (D : ℤ) : Finset (ℤ[X] × ℕ) :=
  S.biUnion fun f ↦
    ((Finset.Icc 1 f.discr.natAbs).filter fun index : ℕ ↦
      f.discr = (index : ℤ) ^ 2 * D).image fun index : ℕ ↦
        (f, index)

/-- Membership in the indexed box exposes the polynomial condition, the
positive bounded index, and the exact discriminant equation. -/
theorem mem_indexedDiscriminantBox_iff
    (S : Finset ℤ[X]) (D : ℤ) (f : ℤ[X]) (index : ℕ) :
    (f, index) ∈ indexedDiscriminantBox S D ↔
      f ∈ S ∧ 1 ≤ index ∧
        index ≤ f.discr.natAbs ∧
        f.discr = (index : ℤ) ^ 2 * D := by
  simp [indexedDiscriminantBox, and_assoc]

/-- In a nonzero discriminant equation, a positive index is bounded by the
absolute polynomial discriminant. -/
theorem index_le_natAbs_discriminant
    {f : ℤ[X]} {D : ℤ} {index : ℕ}
    (hD : D ≠ 0) (hindex : 0 < index)
    (hdiscr : f.discr = (index : ℤ) ^ 2 * D) :
    index ≤ f.discr.natAbs := by
  have hDnat : 1 ≤ D.natAbs := by
    exact (Nat.one_le_iff_ne_zero).2 (Int.natAbs_ne_zero.mpr hD)
  rw [hdiscr, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  nlinarith

/-- A polynomial-index pair satisfying the exact relation belongs to the
finite indexed box as soon as its polynomial belongs to the original box. -/
theorem mem_indexedDiscriminantBox_of_relation
    {S : Finset ℤ[X]} {D : ℤ} {f : ℤ[X]} {index : ℕ}
    (hf : f ∈ S) (hD : D ≠ 0) (hindex : 0 < index)
    (hdiscr : f.discr = (index : ℤ) ^ 2 * D) :
    (f, index) ∈ indexedDiscriminantBox S D := by
  rw [mem_indexedDiscriminantBox_iff]
  refine ⟨hf, hindex, ?_, hdiscr⟩
  exact index_le_natAbs_discriminant hD hindex hdiscr

/-- A field-realizable Hunter polynomial in a finite box carries an index
that belongs to the corresponding exact discriminant filter. -/
theorem hunterFieldPolynomialCandidate_exists_mem_indexedDiscriminantBox
    {K : Type*} [Field K] [NumberField K]
    {d : ℕ} {B : ℝ} {S : Finset ℤ[X]} {f : ℤ[X]}
    (hfbox : f ∈ S)
    (hf : HunterFieldPolynomialCandidate K d B f) :
    ∃ index : ℕ,
      (f, index) ∈ indexedDiscriminantBox S
        (NumberField.discr K) ∧
      0 < index ∧
      f.discr = (index : ℤ) ^ 2 * NumberField.discr K := by
  obtain ⟨_, _, _, index, hindex, hdiscr⟩ := hf.2
  refine ⟨index, ?_, hindex, hdiscr⟩
  exact mem_indexedDiscriminantBox_of_relation
    hfbox (NumberField.discr_ne_zero K) hindex hdiscr

/-- An existential field candidate in a finite polynomial box can be lifted
as a whole to an existential candidate in the exact discriminant filter. -/
theorem exists_hunterFieldPolynomialCandidate_mem_indexedDiscriminantBox
    {K : Type*} [Field K] [NumberField K]
    {d : ℕ} {B : ℝ} {S : Finset ℤ[X]}
    (h : ∃ f ∈ S, HunterFieldPolynomialCandidate K d B f) :
    ∃ f index,
      (f, index) ∈ indexedDiscriminantBox S
        (NumberField.discr K) ∧
      HunterFieldPolynomialCandidate K d B f ∧
      0 < index ∧
      f.discr = (index : ℤ) ^ 2 * NumberField.discr K := by
  obtain ⟨f, hfbox, hf⟩ := h
  obtain ⟨index, hmem, hindex, hdiscr⟩ :=
    hunterFieldPolynomialCandidate_exists_mem_indexedDiscriminantBox
      hfbox hf
  exact ⟨f, index, hmem, hf, hindex, hdiscr⟩

/-- The polynomial projection of the indexed discriminant box. -/
def discriminantCompatiblePolynomialBox
    (S : Finset ℤ[X]) (D : ℤ) : Finset ℤ[X] :=
  (indexedDiscriminantBox S D).image Prod.fst

/-- A polynomial is retained precisely when one of the bounded positive
indices gives the exact discriminant relation. -/
theorem mem_discriminantCompatiblePolynomialBox_iff
    (S : Finset ℤ[X]) (D : ℤ) (f : ℤ[X]) :
    f ∈ discriminantCompatiblePolynomialBox S D ↔
      ∃ index : ℕ,
        f ∈ S ∧ 1 ≤ index ∧
          index ≤ f.discr.natAbs ∧
          f.discr = (index : ℤ) ^ 2 * D := by
  simp only [discriminantCompatiblePolynomialBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2, ?_⟩
    exact (mem_indexedDiscriminantBox_iff S D p.1 p.2).1 hp
  · rintro ⟨index, hf, hindexLower, hindexUpper, hdiscr⟩
    refine ⟨(f, index), ?_, rfl⟩
    exact (mem_indexedDiscriminantBox_iff S D f index).2
      ⟨hf, hindexLower, hindexUpper, hdiscr⟩

/-- Every qualifying quintic field has a Hunter polynomial in the refined
box that survives the exact field-discriminant filter. -/
theorem exists_degreeFive_hunterFieldCandidate_mem_discriminantBox
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 5)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 5) :
    ∃ f index,
      (f, index) ∈ indexedDiscriminantBox
        degreeFiveHunterRefinedBox (NumberField.discr K) ∧
      HunterFieldPolynomialCandidate K 5 180 f ∧
      0 < index ∧
      f.discr = (index : ℤ) ^ 2 * NumberField.discr K := by
  exact exists_hunterFieldPolynomialCandidate_mem_indexedDiscriminantBox
    (K := K) (d := 5) (B := 180)
    (S := degreeFiveHunterRefinedBox)
    (exists_degreeFive_hunterFieldCandidate_mem_refinedBox
      K hreal hdegree hdisc)

/-- Every qualifying septic field has a Hunter polynomial in the refined box
that survives the exact field-discriminant filter. -/
theorem exists_degreeSeven_hunterFieldCandidate_mem_discriminantBox
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 7)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 7) :
    ∃ f index,
      (f, index) ∈ indexedDiscriminantBox
        degreeSevenHunterRefinedBox (NumberField.discr K) ∧
      HunterFieldPolynomialCandidate K 7 343 f ∧
      0 < index ∧
      f.discr = (index : ℤ) ^ 2 * NumberField.discr K := by
  exact exists_hunterFieldPolynomialCandidate_mem_indexedDiscriminantBox
    (K := K) (d := 7) (B := 343)
    (S := degreeSevenHunterRefinedBox)
    (exists_degreeSeven_hunterFieldCandidate_mem_refinedBox
      K hreal hdegree hdisc)

end

end TraceEuclidean
