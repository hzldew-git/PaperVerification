import TraceEuclidean.DegreeFiveFrontierArithmetic
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenScaledCandidates

/-!
# Pure-kernel arithmetic for the degree-seven final frontier

This module turns the final `a0` intervals into coefficient lists and reuses
the dense polynomial factor certificates from the degree-five frontier.
-/

namespace TraceEuclidean

open Polynomial

noncomputable section

/-- A monic septic is recovered from its eight displayed coefficients. -/
theorem degreeSeven_eq_polynomialOfCoefficients
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 7) :
    f = polynomialOfCoefficients
      [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
        f.coeff 4, f.coeff 5, f.coeff 6, 1] := by
  ext exponent
  rw [polynomialOfCoefficients, voightPolynomial_coeff]
  by_cases hle : exponent ≤ 7
  · interval_cases exponent <;> simp
    rw [← hdegree]
    exact hmonic.coeff_natDegree
  · have hlt : f.natDegree < exponent := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    change 0 = ([f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
      f.coeff 4, f.coeff 5, f.coeff 6, 1] : List ℤ).getD exponent 0
    symm
    exact List.getD_eq_default (l :=
      [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
        f.coeff 4, f.coeff 5, f.coeff 6, 1]) (d := 0) (by simp; omega)

/-- Coefficient lists obtained by expanding every exact final `a0` interval. -/
def degreeSevenStageSevenFinalCoefficients
    (entries : List DegreeSevenStageSevenScaledEntry) : List (List ℤ) :=
  entries.flatMap fun entry =>
    entry.scaledA0Candidates.toList.map fun a0 =>
      [a0, entry.a1, entry.a2, entry.a3,
        entry.a4, entry.a5, entry.a6, 1]

theorem degreeSevenStageSevenFinalCoefficients_append
    (left right : List DegreeSevenStageSevenScaledEntry) :
    degreeSevenStageSevenFinalCoefficients (left ++ right) =
      degreeSevenStageSevenFinalCoefficients left ++
        degreeSevenStageSevenFinalCoefficients right := by
  simp [degreeSevenStageSevenFinalCoefficients]

/-! A compact kernel certificate for the final candidate partition. -/

inductive DegreeSevenFinalCandidateCertificate where
  | reducible (certificate : PolynomialFactorCertificate)
  | survivor (coefficients : List ℤ)
deriving DecidableEq, Repr

namespace DegreeSevenFinalCandidateCertificate

def coefficients : DegreeSevenFinalCandidateCertificate → List ℤ
  | .reducible certificate => certificate.coefficients
  | .survivor values => values

def check : DegreeSevenFinalCandidateCertificate → Bool
  | .reducible certificate => certificate.check
  | .survivor _ => true

def survivorCoefficients :
    List DegreeSevenFinalCandidateCertificate → List (List ℤ)
  | [] => []
  | .reducible _ :: tail => survivorCoefficients tail
  | .survivor values :: tail => values :: survivorCoefficients tail

/-- An irreducible polynomial represented by a checked final-candidate list
must occur in the explicitly retained survivor sublist. -/
theorem mem_survivorCoefficients_of_irreducible
    {candidates : List DegreeSevenFinalCandidateCertificate}
    (hvalid : candidates.Forall fun candidate => candidate.check = true)
    {values : List ℤ}
    (hmem : values ∈ candidates.map coefficients)
    (hirreducible : Irreducible (polynomialOfCoefficients values)) :
    values ∈ survivorCoefficients candidates := by
  induction candidates with
  | nil => simp at hmem
  | cons candidate tail ih =>
      rw [List.forall_cons] at hvalid
      simp only [List.map_cons, List.mem_cons] at hmem
      cases candidate with
      | reducible certificate =>
          simp only [survivorCoefficients]
          rcases hmem with hvalues | htail
          · subst values
            exact (not_irreducible_of_factorCertificate certificate
              hvalid.1 hirreducible).elim
          · exact ih hvalid.2 htail
      | survivor candidateValues =>
          simp only [survivorCoefficients, List.mem_cons]
          rcases hmem with hvalues | htail
          · exact Or.inl hvalues
          · exact Or.inr (ih hvalid.2 htail)

end DegreeSevenFinalCandidateCertificate

structure DegreeSevenFinalEntryCertificate where
  entry : DegreeSevenStageSevenScaledEntry
  lowerBound : ℤ
  upperBound : ℤ
  candidates : List DegreeSevenFinalCandidateCertificate
deriving DecidableEq, Repr

namespace DegreeSevenFinalEntryCertificate

def expectedCoefficients
    (certificate : DegreeSevenFinalEntryCertificate) : List (List ℤ) :=
  (integerIccList certificate.lowerBound certificate.upperBound).map fun a0 =>
    [a0, certificate.entry.a1, certificate.entry.a2,
      certificate.entry.a3, certificate.entry.a4,
      certificate.entry.a5, certificate.entry.a6, 1]

def actualCoefficients
    (certificate : DegreeSevenFinalEntryCertificate) : List (List ℤ) :=
  certificate.entry.scaledA0Candidates.toList.map fun a0 =>
    [a0, certificate.entry.a1, certificate.entry.a2,
      certificate.entry.a3, certificate.entry.a4,
      certificate.entry.a5, certificate.entry.a6, 1]

def check (certificate : DegreeSevenFinalEntryCertificate) : Bool :=
  decide
      (certificate.entry.scaledA0LowerBound = certificate.lowerBound) &&
    decide
      (certificate.entry.scaledA0UpperBound = certificate.upperBound) &&
    decide
      (certificate.candidates.map
          DegreeSevenFinalCandidateCertificate.coefficients =
        certificate.expectedCoefficients) &&
    certificate.candidates.all
      DegreeSevenFinalCandidateCertificate.check

theorem candidateCoefficients_eq
    (certificate : DegreeSevenFinalEntryCertificate)
    (hcheck : certificate.check = true) :
    certificate.candidates.map
        DegreeSevenFinalCandidateCertificate.coefficients =
      certificate.expectedCoefficients := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hcheck
  exact hcheck.1.2

theorem lowerBound_eq
    (certificate : DegreeSevenFinalEntryCertificate)
    (hcheck : certificate.check = true) :
    certificate.entry.scaledA0LowerBound = certificate.lowerBound := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hcheck
  exact hcheck.1.1.1

theorem upperBound_eq
    (certificate : DegreeSevenFinalEntryCertificate)
    (hcheck : certificate.check = true) :
    certificate.entry.scaledA0UpperBound = certificate.upperBound := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hcheck
  exact hcheck.1.1.2

theorem candidates_valid
    (certificate : DegreeSevenFinalEntryCertificate)
    (hcheck : certificate.check = true) :
    certificate.candidates.Forall
      (fun candidate => candidate.check = true) := by
  apply List.forall_iff_forall_mem.mpr
  simp only [check, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hcheck
  exact hcheck.2

theorem a0_mem_expected_iff
    (certificate : DegreeSevenFinalEntryCertificate)
    (hcheck : certificate.check = true) (a0 : ℤ) :
    a0 ∈ certificate.entry.scaledA0Candidates.toList ↔
      a0 ∈ integerIccList certificate.lowerBound certificate.upperBound := by
  rw [Finset.mem_toList,
    DegreeSevenStageSevenScaledEntry.scaledA0Candidates,
    certificate.lowerBound_eq hcheck,
    certificate.upperBound_eq hcheck]
  exact mem_integerIccList_iff_mem_integerIcc.symm

theorem mem_actualCoefficients_iff
    (certificate : DegreeSevenFinalEntryCertificate)
    (hcheck : certificate.check = true) (values : List ℤ) :
    values ∈ certificate.actualCoefficients ↔
      values ∈ certificate.candidates.map
        DegreeSevenFinalCandidateCertificate.coefficients := by
  rw [certificate.candidateCoefficients_eq hcheck]
  unfold actualCoefficients expectedCoefficients
  constructor
  · intro hvalues
    rcases List.mem_map.mp hvalues with ⟨a0, ha0, hvalues⟩
    subst values
    exact List.mem_map.mpr
      ⟨a0, (certificate.a0_mem_expected_iff hcheck a0).mp ha0, rfl⟩
  · intro hvalues
    rcases List.mem_map.mp hvalues with ⟨a0, ha0, hvalues⟩
    subst values
    exact List.mem_map.mpr
      ⟨a0, (certificate.a0_mem_expected_iff hcheck a0).mpr ha0, rfl⟩

def allCandidates
    (certificates : List DegreeSevenFinalEntryCertificate) :
    List DegreeSevenFinalCandidateCertificate :=
  certificates.flatMap DegreeSevenFinalEntryCertificate.candidates

def survivorCoefficients
    (certificates : List DegreeSevenFinalEntryCertificate) : List (List ℤ) :=
  DegreeSevenFinalCandidateCertificate.survivorCoefficients
    (allCandidates certificates)

theorem mem_finalCoefficients_iff
    (certificates : List DegreeSevenFinalEntryCertificate)
    (hvalid : certificates.Forall fun certificate => certificate.check = true)
    (values : List ℤ) :
    values ∈ degreeSevenStageSevenFinalCoefficients
        (certificates.map DegreeSevenFinalEntryCertificate.entry) ↔
      values ∈ (allCandidates certificates).map
        DegreeSevenFinalCandidateCertificate.coefficients := by
  induction certificates with
  | nil => simp [allCandidates, degreeSevenStageSevenFinalCoefficients]
  | cons certificate tail ih =>
      rw [List.forall_cons] at hvalid
      change
        values ∈ certificate.actualCoefficients ++
            degreeSevenStageSevenFinalCoefficients (tail.map entry) ↔
          values ∈ (certificate.candidates ++ allCandidates tail).map
            DegreeSevenFinalCandidateCertificate.coefficients
      simp only [List.map_append, List.mem_append]
      rw [certificate.mem_actualCoefficients_iff hvalid.1,
        ih hvalid.2]

theorem allCandidates_valid
    (certificates : List DegreeSevenFinalEntryCertificate)
    (hvalid : certificates.Forall fun certificate => certificate.check = true) :
    (allCandidates certificates).Forall
      (fun candidate => candidate.check = true) := by
  induction certificates with
  | nil => simp [allCandidates]
  | cons certificate tail ih =>
      rw [List.forall_cons] at hvalid
      rw [allCandidates, List.flatMap_cons, List.forall_append]
      exact ⟨certificate.candidates_valid hvalid.1, ih hvalid.2⟩

/-- A checked entry-certificate list reduces every irreducible member of its
exact final coefficient frontier to the retained survivor list. -/
theorem mem_survivorCoefficients_of_irreducible
    {certificates : List DegreeSevenFinalEntryCertificate}
    (hvalid : certificates.Forall fun certificate => certificate.check = true)
    {values : List ℤ}
    (hmem : values ∈ degreeSevenStageSevenFinalCoefficients
      (certificates.map DegreeSevenFinalEntryCertificate.entry))
    (hirreducible : Irreducible (polynomialOfCoefficients values)) :
    values ∈ survivorCoefficients certificates := by
  have hmemCandidates :=
    (mem_finalCoefficients_iff certificates hvalid values).mp hmem
  exact
    DegreeSevenFinalCandidateCertificate.mem_survivorCoefficients_of_irreducible
      (allCandidates_valid certificates hvalid) hmemCandidates hirreducible

end DegreeSevenFinalEntryCertificate

theorem DegreeSevenStageSevenScaledEntry.coefficients_mem_final
    {entries : List DegreeSevenStageSevenScaledEntry}
    {entry : DegreeSevenStageSevenScaledEntry} (hentry : entry ∈ entries)
    (hvalid : entry.ArithmeticValid)
    {a0 : ℤ} (ha0 : a0 ∈ entry.toEntry.a0Candidates) :
    [a0, entry.a1, entry.a2, entry.a3,
        entry.a4, entry.a5, entry.a6, 1] ∈
      degreeSevenStageSevenFinalCoefficients entries := by
  have ha0Scaled : a0 ∈ entry.scaledA0Candidates := by
    rw [← entry.a0Candidates_eq_scaledA0Candidates hvalid]
    exact ha0
  apply List.mem_flatMap.mpr
  refine ⟨entry, hentry, ?_⟩
  apply List.mem_map.mpr
  exact ⟨a0, Finset.mem_toList.mpr ha0Scaled, rfl⟩

/-- A checked list of nontrivial factorizations rules out irreducibility for
every coefficient list represented by one of its certificates. -/
theorem not_irreducible_of_mem_factorCertificates
    {certificates : List PolynomialFactorCertificate}
    (hvalid : certificates.Forall fun certificate => certificate.check = true)
    {coefficients : List ℤ}
    (hmem : coefficients ∈
      certificates.map PolynomialFactorCertificate.coefficients) :
    ¬Irreducible (polynomialOfCoefficients coefficients) := by
  obtain ⟨certificate, hcertificate, rfl⟩ := List.mem_map.mp hmem
  exact not_irreducible_of_factorCertificate certificate
    ((List.forall_iff_forall_mem.mp hvalid) certificate hcertificate)

end

end TraceEuclidean
