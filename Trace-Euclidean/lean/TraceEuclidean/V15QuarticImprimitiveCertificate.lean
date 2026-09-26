import TraceEuclidean.V15QuarticSubfieldReduction
import TraceEuclidean.V15QuadraticDiscriminantRows
import TraceEuclidean.V15QuadraticSieve

/-!
# Finite certificate for imprimitive totally real quartic fields

For a proper quadratic subfield `E` of a quartic field `K`, the preceding
module proves

`|D_K| = N(different(K/E)) * |D_E|^2`.

Below `|D_K| = 725`, the quadratic discriminant has absolute value at most
`26`.  The present module records the seven possible positive quadratic
discriminants in that range and the exact relative-different norm needed in
each row.  All arithmetic after those finite rows is checked by Lean.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module
open scoped NumberField

/-- The positive quadratic field discriminants below `27`. -/
def v15QuadraticDiscriminantsBelowTwentySeven : Finset ℕ :=
  {5, 8, 12, 13, 17, 21, 24}

/-- The least integral relative-different norm that makes
`r * d^2 >= 725` for each possible quadratic subfield discriminant `d`. -/
def v15QuarticRelativeDifferentLowerBound (d : ℕ) : ℕ :=
  if d = 5 then 29
  else if d = 8 then 12
  else if d = 12 then 6
  else if d = 13 then 5
  else if d = 17 then 3
  else 2

/-- Square-free radicands whose quadratic field discriminant is at most `26`.
This is the finite arithmetic part of the quadratic-subfield classification. -/
theorem v15_bounded_quadratic_radicands_twentySix {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hdisc : v15QuadraticDiscriminant m ≤ 26) :
    m = 2 ∨ m = 3 ∨ m = 5 ∨ m = 6 ∨ m = 13 ∨ m = 17 ∨ m = 21 := by
  have hle : m ≤ 26 := by
    unfold v15QuadraticDiscriminant at hdisc
    split at hdisc <;> omega
  have nonsquare (k : ℕ) (hk : 1 < k) (hk2 : k * k ∣ m) : False := by
    have hk1 := hsq k hk2
    omega
  have h4 : m ≠ 4 := by
    intro h
    subst m
    exact nonsquare 2 (by norm_num) (by norm_num)
  have h8 : m ≠ 8 := by
    intro h
    subst m
    exact nonsquare 2 (by norm_num) (by norm_num)
  have h9 : m ≠ 9 := squarefreeNat_ne_nine hsq
  have h12 : m ≠ 12 := by
    intro h
    subst m
    exact nonsquare 2 (by norm_num) (by norm_num)
  have h16 : m ≠ 16 := by
    intro h
    subst m
    exact nonsquare 2 (by norm_num) (by norm_num)
  have h18 : m ≠ 18 := by
    intro h
    subst m
    exact nonsquare 3 (by norm_num) (by norm_num)
  have h20 : m ≠ 20 := by
    intro h
    subst m
    exact nonsquare 2 (by norm_num) (by norm_num)
  have h24 : m ≠ 24 := by
    intro h
    subst m
    exact nonsquare 2 (by norm_num) (by norm_num)
  have h25 : m ≠ 25 := by
    intro h
    subst m
    exact nonsquare 5 (by norm_num) (by norm_num)
  interval_cases m <;> simp_all [v15QuadraticDiscriminant]

/-- Consequently, every quadratic field discriminant represented by the
standard square-free radicand formula and bounded by `26` belongs to the
seven-row list. -/
theorem v15_bounded_quadratic_discriminant_mem_twentySevenRows {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hdisc : v15QuadraticDiscriminant m ≤ 26) :
    v15QuadraticDiscriminant m ∈
      v15QuadraticDiscriminantsBelowTwentySeven := by
  rcases v15_bounded_quadratic_radicands_twentySix hm hsq hdisc with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [v15QuadraticDiscriminant,
    v15QuadraticDiscriminantsBelowTwentySeven]

/-- Standard quadratic-field classification bridge needed only for a proper
subfield of a hypothetical quartic field below the target discriminant. -/
def V15QuarticSmallDiscriminantQuadraticRadicandInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 → |K.discriminant| < 725 →
    ∀ (E : IntermediateField ℚ K.1), E ≠ ⊥ → E ≠ ⊤ →
      ∃ m : ℕ, 1 < m ∧ IsSquarefreeNat m ∧
        (NumberField.discr E).natAbs = v15QuadraticDiscriminant m

/-- Relative Kummer-theory input after the quadratic subfield discriminant is
known: its relative different has at least the row-specific norm. -/
def V15QuarticSmallDiscriminantRelativeDifferentNormInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 → |K.discriminant| < 725 →
    ∀ (E : IntermediateField ℚ K.1), E ≠ ⊥ → E ≠ ⊤ →
      v15QuarticRelativeDifferentLowerBound
          (NumberField.discr E).natAbs ≤
        Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 K.1))

/-- The finite source-facing certificate for a hypothetical imprimitive
totally real quartic field below discriminant `725`.  It states both the
quadratic-subfield row and the required relative-different norm bound. -/
def V15QuarticSmallDiscriminantRelativeDifferentRowsInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 → |K.discriminant| < 725 →
    ∀ (E : IntermediateField ℚ K.1), E ≠ ⊥ → E ≠ ⊤ →
      let d := (NumberField.discr E).natAbs
      d ∈ v15QuadraticDiscriminantsBelowTwentySeven ∧
        v15QuarticRelativeDifferentLowerBound d ≤
          Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 K.1))

/-- The quadratic-subfield row of a hypothetical quartic field below `725`
is now proved internally. -/
theorem v15_quartic_properSubfield_discriminant_mem_twentySevenRows
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 4) (hsmall : |K.discriminant| < 725)
    (E : IntermediateField ℚ K.1) (hbot : E ≠ ⊥) (htop : E ≠ ⊤) :
    (NumberField.discr E).natAbs ∈
      v15QuadraticDiscriminantsBelowTwentySeven := by
  letI : NumberField.IsTotallyReal K.1 := hreal
  have hEdegree : Module.finrank ℚ E = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K.1 hdegree E hbot htop).1
  have hupper := v15_quartic_properSubfield_natAbs_discr_le_twentySix
    K.1 hdegree hsmall E hbot htop
  have hrows := v15_totallyReal_quadratic_discriminant_rows
    E (inferInstance : NumberField.IsTotallyReal E) hEdegree hupper
  rcases hrows with h | h | h | h | h | h | h
  all_goals simp only [v15QuadraticDiscriminantsBelowTwentySeven,
    Finset.mem_insert, Finset.mem_singleton]
  all_goals simp_all

/-- The internally proved quadratic row classification combines with the
relative-different norm bounds to give the full seven-row certificate. -/
theorem v15_relativeDifferentRows_of_norm
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput) :
    V15QuarticSmallDiscriminantRelativeDifferentRowsInput := by
  intro K hreal hdegree hsmall E hbot htop
  constructor
  · exact v15_quartic_properSubfield_discriminant_mem_twentySevenRows
      K hreal hdegree hsmall E hbot htop
  · exact hNorm K hreal hdegree hsmall E hbot htop

/-- The radicand classification bridge and the relative-different bound
construct the combined seven-row certificate. -/
theorem v15_relativeDifferentRows_of_radicand_and_norm
    (hRadicand : V15QuarticSmallDiscriminantQuadraticRadicandInput)
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput) :
    V15QuarticSmallDiscriminantRelativeDifferentRowsInput := by
  intro K hreal hdegree hsmall E hbot htop
  obtain ⟨m, hm, hsq, hdiscEq⟩ :=
    hRadicand K hreal hdegree hsmall E hbot htop
  have hsubfieldBound :=
    v15_quartic_properSubfield_natAbs_discr_le_twentySix
      K.1 hdegree hsmall E hbot htop
  have hmBound : v15QuadraticDiscriminant m ≤ 26 := by
    rw [← hdiscEq]
    exact hsubfieldBound
  constructor
  · rw [hdiscEq]
    exact v15_bounded_quadratic_discriminant_mem_twentySevenRows
      hm hsq hmBound
  · exact hNorm K hreal hdegree hsmall E hbot htop

/-- Every row of the finite relative-different certificate forces the target
quartic discriminant product. -/
theorem v15_quartic_relativeDifferent_row_product_ge_725
    {d r : ℕ}
    (hd : d ∈ v15QuadraticDiscriminantsBelowTwentySeven)
    (hr : v15QuarticRelativeDifferentLowerBound d ≤ r) :
    725 ≤ r * d ^ 2 := by
  simp only [v15QuadraticDiscriminantsBelowTwentySeven, Finset.mem_insert,
    Finset.mem_singleton] at hd
  rcases hd with h | h | h | h | h | h | h
  all_goals subst d
  all_goals norm_num [v15QuarticRelativeDifferentLowerBound] at hr ⊢
  all_goals omega

/-- The seven-row relative-different certificate implies the source-facing
minimum for imprimitive totally real quartic fields. -/
theorem v15_imprimitiveMinimum_of_relativeDifferentRows
    (hRows : V15QuarticSmallDiscriminantRelativeDifferentRowsInput) :
    V15ImprimitiveTotallyRealQuarticMinimumInput := by
  intro K hreal hdegree hproper
  by_contra hnot
  have hsmall : |K.discriminant| < 725 := by omega
  obtain ⟨E, hbot, htop⟩ := hproper
  have hrow := hRows K hreal hdegree hsmall E hbot htop
  have hproduct :
      725 ≤ Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 K.1)) *
        (NumberField.discr E).natAbs ^ 2 :=
    v15_quartic_relativeDifferent_row_product_ge_725 hrow.1 hrow.2
  have htower :=
    v15_quartic_discriminant_tower_of_properIntermediateField
      K.1 hdegree E hbot htop
  have hnat : 725 ≤ (NumberField.discr K.1).natAbs := by
    rw [htower]
    exact hproduct
  have hsmallNat : (NumberField.discr K.1).natAbs < 725 := by
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs]
    exact hsmall
  omega

/-- The finite relative-different rows, together with the internal primitive
quartic argument, prove the full degree-four lower bound. -/
theorem v15_coded_degree_four_discriminant_ge_725_of_relativeDifferentRows
    (hRows : V15QuarticSmallDiscriminantRelativeDifferentRowsInput)
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 4) :
    725 ≤ |K.discriminant| := by
  exact v15_coded_degree_four_discriminant_ge_725_of_imprimitiveMinimum
    (v15_imprimitiveMinimum_of_relativeDifferentRows hRows)
    K hreal hdegree

/-- Strongest finite endpoint: the relative-different norm bounds alone
suffice, because the seven possible quadratic discriminants are now derived
inside Lean. -/
theorem v15_coded_degree_four_discriminant_ge_725_of_relativeDifferentNorm
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 4) :
    725 ≤ |K.discriminant| := by
  exact v15_coded_degree_four_discriminant_ge_725_of_relativeDifferentRows
    (v15_relativeDifferentRows_of_norm hNorm) K hreal hdegree

/-- Fully split endpoint: the standard quadratic-radicand bridge and the
seven relative-different norm bounds suffice for the degree-four result. -/
theorem v15_coded_degree_four_discriminant_ge_725_of_radicand_and_norm
    (hRadicand : V15QuarticSmallDiscriminantQuadraticRadicandInput)
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 4) :
    725 ≤ |K.discriminant| := by
  exact v15_coded_degree_four_discriminant_ge_725_of_relativeDifferentRows
    (v15_relativeDifferentRows_of_radicand_and_norm hRadicand hNorm)
    K hreal hdegree

end

end TraceEuclidean
