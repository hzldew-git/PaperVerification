import TraceEuclidean.DegreeSevenRolleStageSixStrongCompact
import TraceEuclidean.DegreeSevenRolleStageSixScaledFamily

/-!
# Piecewise parametric refinement of the degree-seven sixth Rolle stage

A compact Stage Six coverage uses one five-root interval certificate for the
whole surviving `a2` interval.  That certificate is sufficient for
completeness, but its induced `a1` set can be unnecessarily wide.  This module
allows the same interval to be partitioned into consecutive subintervals,
each with its own kernel-checked dyadic root certificate.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- A compact coverage together with a consecutive list of refined families. -/
structure DegreeSevenStageSixPiecewiseCoverage where
  coverage : DegreeSevenStageSixStrongCompactCoverage
  pieces : List DegreeSevenStageSixScaledFamily
deriving DecidableEq, Repr

namespace DegreeSevenStageSixPiecewiseCoverage

/-- A refined family has the same four fixed coefficients as the coarse
family that it refines. -/
def SameTop (piece : DegreeSevenStageSixScaledFamily)
    (coarse : DegreeSevenStageSixDyadicFamily) : Prop :=
  piece.a6 = coarse.a6 ∧
    piece.a5 = coarse.a5 ∧
    piece.a4 = coarse.a4 ∧
    piece.a3 = coarse.a3

/-- Starting at `next`, the listed valid pieces consecutively cover the
coarse family's interval through its upper endpoint. -/
def CoversFrom (coarse : DegreeSevenStageSixDyadicFamily) :
    ℤ → List DegreeSevenStageSixScaledFamily → Prop
  | next, [] => coarse.a2Upper < next
  | next, piece :: rest =>
      piece.ArithmeticValid ∧
        SameTop piece coarse ∧
        piece.a2Lower = next ∧
        piece.a2Upper ≤ coarse.a2Upper ∧
        CoversFrom coarse (piece.a2Upper + 1) rest

instance coversFromDecidable
    (coarse : DegreeSevenStageSixDyadicFamily) :
    ∀ next pieces, Decidable (CoversFrom coarse next pieces)
  | next, [] => by
      change Decidable (coarse.a2Upper < next)
      infer_instance
  | next, piece :: rest => by
      haveI := coversFromDecidable coarse (piece.a2Upper + 1) rest
      change Decidable
        (piece.ArithmeticValid ∧
          SameTop piece coarse ∧
          piece.a2Lower = next ∧
          piece.a2Upper ≤ coarse.a2Upper ∧
          CoversFrom coarse (piece.a2Upper + 1) rest)
      unfold SameTop
      infer_instance

/-- Entirely integer-checkable validity of the added piece list. -/
def PiecesValid
    (refinement : DegreeSevenStageSixPiecewiseCoverage) : Prop :=
  match refinement.coverage.family with
  | none => refinement.pieces = []
  | some coarse => CoversFrom coarse coarse.a2Lower refinement.pieces

/-- Arithmetic validity combines the existing compact coverage check with the
new integer piece-list check. -/
def ArithmeticValid
    (refinement : DegreeSevenStageSixPiecewiseCoverage) : Prop :=
  refinement.coverage.ArithmeticValid ∧ refinement.PiecesValid

/-- Proof-facing validity reuses the established validity of the coarse
coverage and adds the checked piece-list partition. -/
def Valid (refinement : DegreeSevenStageSixPiecewiseCoverage) : Prop :=
  refinement.coverage.Valid ∧ refinement.PiecesValid

instance (refinement : DegreeSevenStageSixPiecewiseCoverage) :
    Decidable refinement.PiecesValid := by
  unfold PiecesValid
  cases hfamily : refinement.coverage.family with
  | none => infer_instance
  | some coarse => infer_instance

instance (refinement : DegreeSevenStageSixPiecewiseCoverage) :
    Decidable refinement.ArithmeticValid := by
  unfold ArithmeticValid
  cases hfamily : refinement.coverage.family with
  | none => infer_instance
  | some coarse => infer_instance

theorem valid_of_arithmeticValid
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (h : refinement.ArithmeticValid) : refinement.Valid :=
  ⟨refinement.coverage.valid_of_arithmeticValid h.1, h.2⟩

theorem list_forall_valid_of_parts
    (refinements : List DegreeSevenStageSixPiecewiseCoverage)
    (hcoverages :
      (refinements.map DegreeSevenStageSixPiecewiseCoverage.coverage).Forall
        DegreeSevenStageSixStrongCompactCoverage.Valid)
    (hpieces : refinements.Forall PiecesValid) :
    refinements.Forall Valid := by
  induction refinements with
  | nil => simp
  | cons refinement rest ih =>
      simp only [List.map_cons, List.forall_cons] at hcoverages hpieces ⊢
      exact ⟨⟨hcoverages.1, hpieces.1⟩,
        ih hcoverages.2 hpieces.2⟩

theorem exists_piece_of_coversFrom
    (coarse : DegreeSevenStageSixDyadicFamily)
    {pieces : List DegreeSevenStageSixScaledFamily}
    {next a2 : ℤ}
    (hcover : CoversFrom coarse next pieces)
    (hnext : next ≤ a2)
    (hupper : a2 ≤ coarse.a2Upper) :
    ∃ piece ∈ pieces,
      piece.ArithmeticValid ∧
        SameTop piece coarse ∧
        a2 ∈ piece.toFamily.a2Candidates := by
  induction pieces generalizing next with
  | nil =>
      simp only [CoversFrom] at hcover
      omega
  | cons piece rest ih =>
      simp only [CoversFrom] at hcover
      rcases hcover with
        ⟨hpieceValid, hpieceTop, hpieceLower, hpieceUpper, hrest⟩
      by_cases ha2Upper : a2 ≤ piece.a2Upper
      · refine ⟨piece, List.mem_cons_self, hpieceValid, hpieceTop, ?_⟩
        rw [DegreeSevenStageSixFamily.a2Candidates,
          integerIcc, Finset.mem_Icc]
        exact ⟨by
          simpa [DegreeSevenStageSixScaledFamily.toFamily,
            hpieceLower] using hnext, ha2Upper⟩
      · obtain ⟨result, hresult, hresultValid, hresultTop, ha2⟩ :=
          ih hrest (by omega)
        exact ⟨result, List.mem_cons_of_mem piece hresult,
          hresultValid, hresultTop, ha2⟩

/-- Every member of a consecutive piecewise cover carries the integer
certificate recorded in the cover. -/
theorem forall_arithmeticValid_of_coversFrom
    (coarse : DegreeSevenStageSixDyadicFamily)
    {pieces : List DegreeSevenStageSixScaledFamily} {next : ℤ}
    (hcover : CoversFrom coarse next pieces) :
    pieces.Forall DegreeSevenStageSixScaledFamily.ArithmeticValid := by
  induction pieces generalizing next with
  | nil => simp
  | cons piece rest ih =>
      simp only [CoversFrom] at hcover
      simp only [List.forall_cons]
      exact ⟨hcover.1, ih hcover.2.2.2.2⟩

/-- Integer validity of a piecewise cover gives integer validity of every
listed refined family. -/
theorem pieces_forall_arithmeticValid
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hvalid : refinement.PiecesValid) :
    refinement.pieces.Forall
      DegreeSevenStageSixScaledFamily.ArithmeticValid := by
  unfold PiecesValid at hvalid
  split at hvalid
  next hnone =>
    simp [hvalid]
  next coarse hsome =>
    exact forall_arithmeticValid_of_coversFrom coarse hvalid

/-- Every Hunter candidate represented by the coarse coverage belongs to one
of its refined pieces and hence to the sharper `a1` set of that piece. -/
theorem hunter_a1_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hvalid : refinement.Valid)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3) :
    ∃ piece ∈ refinement.pieces,
      f.coeff 2 ∈ piece.toFamily.a2Candidates ∧
        f.coeff 1 ∈
          (piece.toFamily.toEntry (f.coeff 2)).a1Candidates := by
  have hcoverageValid : refinement.coverage.Valid := hvalid.1
  obtain ⟨coarse, hcoarse, _, ha2⟩ :=
    refinement.coverage.hunter_a2_mem_family h hcoverageValid
      ha6 ha5 ha4 ha3
  have hcover := hvalid.2
  unfold PiecesValid at hcover
  rw [hcoarse] at hcover
  have ha2Bounds :
      coarse.a2Lower ≤ f.coeff 2 ∧ f.coeff 2 ≤ coarse.a2Upper := by
    simpa [DegreeSevenStageSixFamily.a2Candidates,
      DegreeSevenStageSixDyadicFamily.toFamily,
      integerIcc] using ha2
  obtain ⟨piece, hpiece, hpieceValid, hpieceTop, ha2Piece⟩ :=
    exists_piece_of_coversFrom coarse hcover ha2Bounds.1 ha2Bounds.2
  have hcoarseRecord := hcoverageValid.2.2.2
  rw [hcoarse] at hcoarseRecord
  have hcoarseTop :
      coarse.a6 = refinement.coverage.parent.a6 ∧
        coarse.a5 = refinement.coverage.parent.a5 ∧
        coarse.a4 = refinement.coverage.parent.a4 ∧
        coarse.a3 = refinement.coverage.parent.a3 :=
    ⟨hcoarseRecord.2.1, hcoarseRecord.2.2.1,
      hcoarseRecord.2.2.2.1, hcoarseRecord.2.2.2.2.1⟩
  have hpieceA6 : piece.a6 = f.coeff 6 :=
    hpieceTop.1.trans (hcoarseTop.1.trans ha6)
  have hpieceA5 : piece.a5 = f.coeff 5 :=
    hpieceTop.2.1.trans (hcoarseTop.2.1.trans ha5)
  have hpieceA4 : piece.a4 = f.coeff 4 :=
    hpieceTop.2.2.1.trans (hcoarseTop.2.2.1.trans ha4)
  have hpieceA3 : piece.a3 = f.coeff 3 :=
    hpieceTop.2.2.2.trans (hcoarseTop.2.2.2.trans ha3)
  refine ⟨piece, hpiece, ha2Piece, ?_⟩
  exact
    DegreeSevenStageSixFamily.degreeSeven_minimumHunterCandidate_a1_mem_of_family
      h piece.toFamily (piece.valid_of_arithmeticValid hpieceValid)
        hpieceA6 hpieceA5 hpieceA4 hpieceA3 ha2Piece

end DegreeSevenStageSixPiecewiseCoverage

end

end TraceEuclidean
