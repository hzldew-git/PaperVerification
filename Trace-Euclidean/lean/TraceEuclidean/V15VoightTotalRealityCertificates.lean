import TraceEuclidean.V15VoightTotalRealityCertificates.FiveChunk0
import TraceEuclidean.V15VoightTotalRealityCertificates.FiveChunk1
import TraceEuclidean.V15VoightTotalRealityCertificates.FiveChunk2
import TraceEuclidean.V15VoightTotalRealityCertificates.FiveChunk3
import TraceEuclidean.V15VoightTotalRealityCertificates.FiveChunk4
import TraceEuclidean.V15VoightTotalRealityCertificates.FiveChunk5
import TraceEuclidean.V15VoightTotalRealityCertificates.FiveChunk6
import TraceEuclidean.V15VoightTotalRealityCertificates.SixChunk0
import TraceEuclidean.V15VoightTotalRealityCertificates.SixChunk1
import TraceEuclidean.V15VoightTotalRealityCertificates.SixChunk2
import TraceEuclidean.V15VoightTotalRealityCertificates.SixChunk3
import TraceEuclidean.V15VoightTotalRealityCertificates.SixChunk4
import TraceEuclidean.V15VoightTotalRealityCertificates.SixChunk5
import TraceEuclidean.V15VoightTotalRealityCertificates.SixChunk6
import TraceEuclidean.V15VoightTotalRealityCertificates.SixChunk7
import TraceEuclidean.V15VoightTotalRealityCertificates.SixChunk8
import TraceEuclidean.V15VoightTotalRealityCertificates.SevenChunk0
import TraceEuclidean.V15VoightTotalRealityCertificates.SevenChunk1
import TraceEuclidean.V15VoightTotalRealityCertificates.SevenChunk2
import TraceEuclidean.V15VoightTotalRealityCertificates.SevenChunk3
import TraceEuclidean.V15VoightTotalRealityCertificates.EightChunk0
import TraceEuclidean.V15VoightTotalRealityCertificates.EightChunk1
import TraceEuclidean.V15VoightTotalRealityCertificates.NineChunk0
import TraceEuclidean.V15VoightTotalRealityCertificates.TenChunk0
import TraceEuclidean.V15VoightTotalRealityCertificates.TenChunk1
import TraceEuclidean.V15VoightTotalRealityCertificates.TenChunk2
import TraceEuclidean.V15VoightTotalRealityCertificates.TenChunk3
import TraceEuclidean.V15VoightTotalRealityCertificates.TenChunk4
import TraceEuclidean.V15VoightTotalRealityCertificates.TenChunk5
import TraceEuclidean.V15VoightTotalRealityCertificates.TenChunk6
import TraceEuclidean.V15VoightTotalRealityCertificates.TenChunk7
import TraceEuclidean.V15VoightAllIrreducible

/-! Real splitting of all archived Voight defining polynomials. -/

namespace TraceEuclidean

set_option linter.style.longLine false

theorem v15_voightPolynomialRowsFive_splits :
    ∀ row ∈ v15VoightPolynomialRowsFive,
      row.realPolynomial.Splits := by
  dsimp [v15VoightPolynomialRowsFive]
  exact v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_voightRowsFiveChunk0_splits) v15_voightRowsFiveChunk1_splits) v15_voightRowsFiveChunk2_splits) v15_voightRowsFiveChunk3_splits) v15_voightRowsFiveChunk4_splits) v15_voightRowsFiveChunk5_splits) v15_voightRowsFiveChunk6_splits

theorem v15_voightPolynomialRowsSix_splits :
    ∀ row ∈ v15VoightPolynomialRowsSix,
      row.realPolynomial.Splits := by
  dsimp [v15VoightPolynomialRowsSix]
  exact v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_voightRowsSixChunk0_splits) v15_voightRowsSixChunk1_splits) v15_voightRowsSixChunk2_splits) v15_voightRowsSixChunk3_splits) v15_voightRowsSixChunk4_splits) v15_voightRowsSixChunk5_splits) v15_voightRowsSixChunk6_splits) v15_voightRowsSixChunk7_splits) v15_voightRowsSixChunk8_splits

theorem v15_voightPolynomialRowsSeven_splits :
    ∀ row ∈ v15VoightPolynomialRowsSeven,
      row.realPolynomial.Splits := by
  dsimp [v15VoightPolynomialRowsSeven]
  exact v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_voightRowsSevenChunk0_splits) v15_voightRowsSevenChunk1_splits) v15_voightRowsSevenChunk2_splits) v15_voightRowsSevenChunk3_splits

theorem v15_voightPolynomialRowsEight_splits :
    ∀ row ∈ v15VoightPolynomialRowsEight,
      row.realPolynomial.Splits := by
  dsimp [v15VoightPolynomialRowsEight]
  exact v15_forall_mem_append (v15_voightRowsEightChunk0_splits) v15_voightRowsEightChunk1_splits

theorem v15_voightPolynomialRowsNine_splits :
    ∀ row ∈ v15VoightPolynomialRowsNine,
      row.realPolynomial.Splits := by
  dsimp [v15VoightPolynomialRowsNine]
  exact v15_voightRowsNineChunk0_splits

theorem v15_voightPolynomialRowsTen_splits :
    ∀ row ∈ v15VoightPolynomialRowsTen,
      row.realPolynomial.Splits := by
  dsimp [v15VoightPolynomialRowsTen]
  exact v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_voightRowsTenChunk0_splits) v15_voightRowsTenChunk1_splits) v15_voightRowsTenChunk2_splits) v15_voightRowsTenChunk3_splits) v15_voightRowsTenChunk4_splits) v15_voightRowsTenChunk5_splits) v15_voightRowsTenChunk6_splits) v15_voightRowsTenChunk7_splits

/-- Every one of the 2,773 archived defining polynomials splits
completely over the real numbers. -/
theorem v15_allVoightPolynomialRows_splits :
    ∀ row ∈ v15AllVoightPolynomialRows,
      row.realPolynomial.Splits := by
  dsimp [v15AllVoightPolynomialRows]
  exact v15_forall_mem_append
    v15_voightPolynomialRowsFive_splits
    (v15_forall_mem_append
      v15_voightPolynomialRowsSix_splits
      (v15_forall_mem_append
        v15_voightPolynomialRowsSeven_splits
        (v15_forall_mem_append
          v15_voightPolynomialRowsEight_splits
          (v15_forall_mem_append
            v15_voightPolynomialRowsNine_splits
            v15_voightPolynomialRowsTen_splits))))

end TraceEuclidean
