import TraceEuclidean.OdlyzkoQuadraturePieceData

/-!
# Small subintervals for pure-kernel Odlyzko quadrature certificates

Each existing quadrature interval is bisected.  The two composite
trapezoidal sums and their analytic error allowances add exactly to those of
the parent interval, while the separate proof terms keep kernel reduction
within a reproducible memory bound.
-/

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core

def sinhMiddleOneLeftA : IntervalRat := ⟨1 / 2, 19 / 24, by norm_num⟩
def sinhMiddleOneLeftB : IntervalRat := ⟨19 / 24, 13 / 12, by norm_num⟩
def sinhMiddleOneRightA : IntervalRat := ⟨13 / 12, 11 / 8, by norm_num⟩
def sinhMiddleOneRightB : IntervalRat := ⟨11 / 8, 5 / 3, by norm_num⟩
def sinhMiddleTwoLeftA : IntervalRat := ⟨5 / 3, 47 / 24, by norm_num⟩
def sinhMiddleTwoLeftB : IntervalRat := ⟨47 / 24, 9 / 4, by norm_num⟩
def sinhMiddleTwoRightA : IntervalRat := ⟨9 / 4, 61 / 24, by norm_num⟩
def sinhMiddleTwoRightB : IntervalRat := ⟨61 / 24, 17 / 6, by norm_num⟩
def sinhMiddleThreeA : IntervalRat := ⟨17 / 6, 41 / 12, by norm_num⟩
def sinhMiddleThreeB : IntervalRat := ⟨41 / 12, 4, by norm_num⟩

def unitZeroHalfA : IntervalRat := ⟨0, 1 / 4, by norm_num⟩
def unitZeroHalfB : IntervalRat := ⟨1 / 4, 1 / 2, by norm_num⟩
def unitHalfOneA : IntervalRat := ⟨1 / 2, 3 / 4, by norm_num⟩
def unitHalfOneB : IntervalRat := ⟨3 / 4, 1, by norm_num⟩
def unitOneTwoA : IntervalRat := ⟨1, 3 / 2, by norm_num⟩
def unitOneTwoB : IntervalRat := ⟨3 / 2, 2, by norm_num⟩
def unitTwoThreeA : IntervalRat := ⟨2, 5 / 2, by norm_num⟩
def unitTwoThreeB : IntervalRat := ⟨5 / 2, 3, by norm_num⟩
def unitThreeFourA : IntervalRat := ⟨3, 7 / 2, by norm_num⟩
def unitThreeFourB : IntervalRat := ⟨7 / 2, 4, by norm_num⟩
def unitFourFiveA : IntervalRat := ⟨4, 9 / 2, by norm_num⟩
def unitFourFiveB : IntervalRat := ⟨9 / 2, 5, by norm_num⟩
def unitFiveSixA : IntervalRat := ⟨5, 11 / 2, by norm_num⟩
def unitFiveSixB : IntervalRat := ⟨11 / 2, 6, by norm_num⟩
def unitSixSevenA : IntervalRat := ⟨6, 13 / 2, by norm_num⟩
def unitSixSevenB : IntervalRat := ⟨13 / 2, 7, by norm_num⟩
def unitSevenEightA : IntervalRat := ⟨7, 15 / 2, by norm_num⟩
def unitSevenEightB : IntervalRat := ⟨15 / 2, 8, by norm_num⟩

def unitFourFourHalfA : IntervalRat := ⟨4, 17 / 4, by norm_num⟩
def unitFourFourHalfB : IntervalRat := ⟨17 / 4, 9 / 2, by norm_num⟩
def unitFourHalfFiveA : IntervalRat := ⟨9 / 2, 19 / 4, by norm_num⟩
def unitFourHalfFiveB : IntervalRat := ⟨19 / 4, 5, by norm_num⟩
def unitFiveFiveHalfA : IntervalRat := ⟨5, 21 / 4, by norm_num⟩
def unitFiveFiveHalfB : IntervalRat := ⟨21 / 4, 11 / 2, by norm_num⟩
def unitFiveHalfSixA : IntervalRat := ⟨11 / 2, 23 / 4, by norm_num⟩
def unitFiveHalfSixB : IntervalRat := ⟨23 / 4, 6, by norm_num⟩
def unitSixSixHalfA : IntervalRat := ⟨6, 25 / 4, by norm_num⟩
def unitSixSixHalfB : IntervalRat := ⟨25 / 4, 13 / 2, by norm_num⟩
def unitSixHalfSevenA : IntervalRat := ⟨13 / 2, 27 / 4, by norm_num⟩
def unitSixHalfSevenB : IntervalRat := ⟨27 / 4, 7, by norm_num⟩

end TraceEuclidean.OdlyzkoNumerical.Certificate
