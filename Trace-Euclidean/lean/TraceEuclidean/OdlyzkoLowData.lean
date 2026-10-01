import TraceEuclidean.OdlyzkoNumericalPieceData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine

def sinhCoreLowOne : IntervalRat := ⟨1 / 5, 11 / 40, by norm_num⟩
def sinhCoreLowTwo : IntervalRat := ⟨11 / 40, 7 / 20, by norm_num⟩
def sinhCoreLowThree : IntervalRat := ⟨7 / 20, 17 / 40, by norm_num⟩
def sinhCoreLowFour : IntervalRat := ⟨17 / 40, 1 / 2, by norm_num⟩

def fastLowQuadratureConfig : DyadicConfig :=
  { precision := -21, taylorDepth := 10 }

end TraceEuclidean.OdlyzkoNumerical.Certificate
