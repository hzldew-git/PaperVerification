import TraceEuclidean.OdlyzkoNumericalPieceData

/-!
# Additional subintervals for the  Odlyzko quadrature certificates

The two 128-node checks are split at rational midpoints so that each closed
kernel computation has a predictable reconstruction cost.
-/

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core

def sinhMiddleOneLeft : IntervalRat := ⟨1 / 2, 13 / 12, by norm_num⟩
def sinhMiddleOneRight : IntervalRat := ⟨13 / 12, 5 / 3, by norm_num⟩
def sinhMiddleTwoLeft : IntervalRat := ⟨5 / 3, 9 / 4, by norm_num⟩
def sinhMiddleTwoRight : IntervalRat := ⟨9 / 4, 17 / 6, by norm_num⟩

def unitZeroHalf : IntervalRat := ⟨0, 1 / 2, by norm_num⟩
def unitHalfOne : IntervalRat := ⟨1 / 2, 1, by norm_num⟩
def unitFourFourHalf : IntervalRat := ⟨4, 9 / 2, by norm_num⟩
def unitFourHalfFive : IntervalRat := ⟨9 / 2, 5, by norm_num⟩
def unitFiveFiveHalf : IntervalRat := ⟨5, 11 / 2, by norm_num⟩
def unitFiveHalfSix : IntervalRat := ⟨11 / 2, 6, by norm_num⟩
def unitSixSixHalf : IntervalRat := ⟨6, 13 / 2, by norm_num⟩
def unitSixHalfSeven : IntervalRat := ⟨13 / 2, 7, by norm_num⟩

end TraceEuclidean.OdlyzkoNumerical.Certificate
