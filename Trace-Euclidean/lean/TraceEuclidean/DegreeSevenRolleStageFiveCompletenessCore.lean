import TraceEuclidean.DegreeSevenRolleStageFiveCompact

/-!
# Data-independent completeness of the fifth septic Rolle stage

This module isolates the logical bridge from a finite collection of certified
rows to the fifth-stage completeness theorem.  Generated data only has to
instantiate `DegreeSevenStageFiveCertifiedData`; the proof below then
classifies every fourth-stage candidate and rejects both exceptional cases.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The finite facts needed to close the fifth degree-seven Rolle stage. -/
structure DegreeSevenStageFiveCertifiedData where
  entries : List DegreeSevenStageFiveDyadicEntry
  coverages : List DegreeSevenStageFiveCoverage
  multipleRootWitnesses :
    List DegreeSevenStageFiveMultipleRootWitness
  criticalSignWitnesses :
    List DegreeSevenStageFiveCriticalSignWitness
  coverageRangesChecked :
    coverages.map DegreeSevenStageFiveCoverage.rangeRecord =
      degreeSevenStageFourExpectedRanges
  coveragesValid :
    coverages.Forall DegreeSevenStageFiveCoverage.Valid
  entriesValid :
    entries.Forall DegreeSevenStageFiveDyadicEntry.Valid
  topQuadruplesChecked :
    entries.map (fun entry ↦
      (entry.a6, entry.a5, entry.a4, entry.a3)) =
        coverages.flatMap DegreeSevenStageFiveCoverage.topQuadruples
  multipleRootWitnessesChecked :
    coverages.flatMap
        DegreeSevenStageFiveCoverage.multipleRootWitnesses =
      multipleRootWitnesses
  criticalSignWitnessesChecked :
    coverages.flatMap
        DegreeSevenStageFiveCoverage.criticalSignWitnesses =
      criticalSignWitnesses
  multipleRootWitnessesValid :
    multipleRootWitnesses.Forall
      DegreeSevenStageFiveMultipleRootWitness.Valid
  criticalSignWitnessesValid :
    criticalSignWitnesses.Forall
      DegreeSevenStageFiveCriticalSignWitness.Valid

/-- A fourth-stage row and one of its certified `a3` values are classified
by one coverage row as surviving, multiple-root, or critical-sign rejected. -/
theorem degreeSevenStageFour_candidate_classified_of_data
    (data : DegreeSevenStageFiveCertifiedData)
    (entry : DegreeSevenStageFourEntry)
    (hentry : entry ∈ degreeSevenStageFourEntries)
    {a3 : ℤ} (ha3 : a3 ∈ entry.a3Candidates) :
    ∃ coverage ∈ data.coverages,
      coverage.parent.a6 = entry.a6 ∧
      coverage.parent.a5 = entry.a5 ∧
      coverage.parent.a4 = entry.a4 ∧
      (a3 ∈ coverage.survivingA3 ∨
        (∃ root, (a3, root) ∈ coverage.multipleRootA3Roots) ∨
        ∃ witness ∈ coverage.criticalSignWitnesses,
          witness.a3 = a3) := by
  have hrange :
      (entry.a6, entry.a5, entry.a4,
        quarticTranslationLowerBound entry.baseCoefficients
          (-16) 16 entry.secondRoot,
        quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot) ∈
        degreeSevenStageFourExpectedRanges := by
    rw [← degreeSevenStageFourRanges_checked]
    exact List.mem_map_of_mem hentry
  rw [← data.coverageRangesChecked] at hrange
  obtain ⟨coverage, hcoverage, hrangeEq⟩ := List.mem_map.mp hrange
  have hcoverageValid : coverage.Valid :=
    (List.forall_iff_forall_mem.mp data.coveragesValid)
      coverage hcoverage
  have ha3Bounds :
      quarticTranslationLowerBound entry.baseCoefficients
          (-16) 16 entry.secondRoot ≤ a3 ∧
        a3 ≤ quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot := by
    simpa [DegreeSevenStageFourEntry.a3Candidates,
      quarticTranslationCandidates, integerIcc] using ha3
  have hcomponents :
      coverage.parent.a6 = entry.a6 ∧
      coverage.parent.a5 = entry.a5 ∧
      coverage.parent.a4 = entry.a4 ∧
      coverage.lower =
        quarticTranslationLowerBound entry.baseCoefficients
          (-16) 16 entry.secondRoot ∧
      coverage.upper =
        quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot := by
    simpa [DegreeSevenStageFiveCoverage.rangeRecord,
      Prod.mk.injEq] using hrangeEq
  rcases hcomponents with ⟨ha6, ha5, ha4, hlower, hupper⟩
  have ha3Coverage :
      a3 ∈ integerIcc coverage.lower coverage.upper := by
    rw [integerIcc, Finset.mem_Icc, hlower, hupper]
    exact ha3Bounds
  rw [hcoverageValid.1] at ha3Coverage
  have ha3List :
      a3 ∈ coverage.survivingA3 ++
        coverage.multipleRootA3Roots.map Prod.fst ++
        coverage.criticalSignWitnesses.map
          DegreeSevenStageFiveCriticalSignWitness.a3 :=
    List.mem_toFinset.mp ha3Coverage
  simp only [List.mem_append] at ha3List
  refine ⟨coverage, hcoverage, ha6, ha5, ha4, ?_⟩
  rcases ha3List with hleft | hcritical
  · rcases hleft with hsurviving | hmultiple
    · exact Or.inl hsurviving
    · obtain ⟨pair, hpair, hpairFirst⟩ := List.mem_map.mp hmultiple
      rcases pair with ⟨candidate, root⟩
      simp only at hpairFirst
      subst candidate
      exact Or.inr (Or.inl ⟨root, hpair⟩)
  · obtain ⟨witness, hwitness, hwitnessA3⟩ :=
      List.mem_map.mp hcritical
    exact Or.inr (Or.inr ⟨witness, hwitness, hwitnessA3⟩)

/-- Every split separable fourth-stage quartic reaches a generated compact
root certificate; the other two finite coverage classes are contradictory. -/
theorem degreeSevenStageFive_exists_entry_of_data
    (data : DegreeSevenStageFiveCertifiedData)
    (parent : DegreeSevenStageFourEntry)
    (hparent : parent ∈ degreeSevenStageFourEntries)
    {a3 : ℤ} (ha3 : a3 ∈ parent.a3Candidates)
    (hsplit :
      (integerPolynomialReal
        [a3, 4 * parent.a4, 10 * parent.a5,
          20 * parent.a6, 35]).Splits)
    (hseparable :
      (integerPolynomialReal
        [a3, 4 * parent.a4, 10 * parent.a5,
          20 * parent.a6, 35]).Separable) :
    ∃ entry ∈ data.entries,
      entry.a6 = parent.a6 ∧
      entry.a5 = parent.a5 ∧
      entry.a4 = parent.a4 ∧
      entry.a3 = a3 := by
  obtain ⟨coverage, hcoverage, ha6, ha5, ha4,
      hclassification⟩ :=
    degreeSevenStageFour_candidate_classified_of_data
      data parent hparent ha3
  have hcoverageValid : coverage.Valid :=
    (List.forall_iff_forall_mem.mp data.coveragesValid)
      coverage hcoverage
  rcases hclassification with hsurviving | hmultiple | hcritical
  · have htop :
        (coverage.parent.a6, coverage.parent.a5,
          coverage.parent.a4, a3) ∈
          data.coverages.flatMap
            DegreeSevenStageFiveCoverage.topQuadruples := by
      exact List.mem_flatMap.mpr
        ⟨coverage, hcoverage,
          List.mem_map.mpr ⟨a3, hsurviving, rfl⟩⟩
    rw [← data.topQuadruplesChecked] at htop
    obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp htop
    have hcomponents :
        entry.a6 = coverage.parent.a6 ∧
        entry.a5 = coverage.parent.a5 ∧
        entry.a4 = coverage.parent.a4 ∧
        entry.a3 = a3 := by
      simpa [Prod.mk.injEq] using hkey
    rcases hcomponents with ⟨he6, he5, he4, he3⟩
    exact ⟨entry, hentry, he6.trans ha6, he5.trans ha5,
      he4.trans ha4, he3⟩
  · obtain ⟨root, hroot⟩ := hmultiple
    let witness : DegreeSevenStageFiveMultipleRootWitness :=
      ⟨coverage.parent.a6, coverage.parent.a5,
        coverage.parent.a4, a3, root⟩
    have hwitnessCoverage :
        witness ∈ coverage.multipleRootWitnesses := by
      exact List.mem_map.mpr ⟨(a3, root), hroot, rfl⟩
    have hwitnessFlat :
        witness ∈ data.coverages.flatMap
          DegreeSevenStageFiveCoverage.multipleRootWitnesses :=
      List.mem_flatMap.mpr
        ⟨coverage, hcoverage, hwitnessCoverage⟩
    rw [data.multipleRootWitnessesChecked] at hwitnessFlat
    have hwitnessValid : witness.Valid :=
      (List.forall_iff_forall_mem.mp
        data.multipleRootWitnessesValid) witness hwitnessFlat
    have hnot :=
      degreeSevenStageFiveMultipleRootWitness_not_separable
        witness hwitnessValid
    apply (hnot ?_).elim
    simpa [witness,
      DegreeSevenStageFiveMultipleRootWitness.coefficients,
      ha6, ha5, ha4] using hseparable
  · obtain ⟨witness, hwitness, hwitnessA3⟩ := hcritical
    have hwitnessFlat :
        witness ∈ data.coverages.flatMap
          DegreeSevenStageFiveCoverage.criticalSignWitnesses :=
      List.mem_flatMap.mpr ⟨coverage, hcoverage, hwitness⟩
    rw [data.criticalSignWitnessesChecked] at hwitnessFlat
    have hwitnessValid : witness.Valid :=
      (List.forall_iff_forall_mem.mp
        data.criticalSignWitnessesValid) witness hwitnessFlat
    have haligned :=
      (List.forall_iff_forall_mem.mp hcoverageValid.2)
        witness hwitness
    have hnot :=
      degreeSevenStageFiveCriticalSignWitness_not_splits_and_separable
        witness hwitnessValid
    apply (hnot ?_).elim
    simpa [DegreeSevenStageFiveCriticalSignWitness.coefficients,
      hwitnessA3, haligned.1, haligned.2.1, haligned.2.2,
      ha6, ha5, ha4] using And.intro hsplit hseparable

/-- Any sharpened septic Hunter candidate reaches a certified compact
quartic row whose stored top coefficients are its actual coefficients. -/
theorem degreeSeven_minimumHunterCandidate_stageFive_complete_of_data
    (data : DegreeSevenStageFiveCertifiedData)
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ data.entries,
      entry.a6 = f.coeff 6 ∧
      entry.a5 = f.coeff 5 ∧
      entry.a4 = f.coeff 4 ∧
      entry.a3 = f.coeff 3 := by
  obtain ⟨parent, hparent, ha6, ha5, ha4, ha3⟩ :=
    degreeSeven_minimumHunterCandidate_stageFour_frontier_complete h
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 3, 4 * parent.a4, 10 * parent.a5,
      20 * parent.a6, 35]
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  have hqEq : q = voightDerivativeStage p 3 := by
    symm
    simpa [p, q, ha6, ha5, ha4] using
      degreeSeven_thirdDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    rw [hqEq]
    exact voightDerivativeStage_splits h.2.2.2.1 3
  have hqseparable : q.Separable := by
    rw [hqEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  obtain ⟨entry, hentry, he6, he5, he4, he3⟩ :=
    degreeSevenStageFive_exists_entry_of_data
      data parent hparent ha3 hqsplit hqseparable
  exact ⟨entry, hentry, he6.trans ha6, he5.trans ha5,
    he4.trans ha4, he3⟩

/-- The complete finite fifth-stage data places the actual coefficient `a2`
of every sharpened septic Hunter candidate in a kernel-checked interval. -/
theorem degreeSeven_minimumHunterCandidate_a2_mem_of_data
    (data : DegreeSevenStageFiveCertifiedData)
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ data.entries,
      entry.a6 = f.coeff 6 ∧
      entry.a5 = f.coeff 5 ∧
      entry.a4 = f.coeff 4 ∧
      entry.a3 = f.coeff 3 ∧
      f.coeff 2 ∈ entry.a2Candidates := by
  obtain ⟨entry, hentry, ha6, ha5, ha4, ha3⟩ :=
    degreeSeven_minimumHunterCandidate_stageFive_complete_of_data
      data h
  have hvalid : entry.Valid :=
    (List.forall_iff_forall_mem.mp data.entriesValid) entry hentry
  exact ⟨entry, hentry, ha6, ha5, ha4, ha3,
    degreeSeven_minimumHunterCandidate_a2_mem_of_valid_dyadic
      h entry hvalid ha6 ha5 ha4 ha3⟩

end

end TraceEuclidean
