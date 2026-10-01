import TraceEuclidean.VoightTotalRealityCertificates.FiveChunk0
import TraceEuclidean.VoightTotalRealityCertificates.FiveChunk1
import TraceEuclidean.VoightTotalRealityCertificates.FiveChunk2
import TraceEuclidean.VoightTotalRealityCertificates.FiveChunk3
import TraceEuclidean.VoightTotalRealityCertificates.FiveChunk4
import TraceEuclidean.VoightTotalRealityCertificates.FiveChunk5
import TraceEuclidean.VoightTotalRealityCertificates.FiveChunk6
import TraceEuclidean.VoightTotalRealityCertificates.SixChunk0
import TraceEuclidean.VoightTotalRealityCertificates.SixChunk1
import TraceEuclidean.VoightTotalRealityCertificates.SixChunk2
import TraceEuclidean.VoightTotalRealityCertificates.SixChunk3
import TraceEuclidean.VoightTotalRealityCertificates.SixChunk4
import TraceEuclidean.VoightTotalRealityCertificates.SixChunk5
import TraceEuclidean.VoightTotalRealityCertificates.SixChunk6
import TraceEuclidean.VoightTotalRealityCertificates.SixChunk7
import TraceEuclidean.VoightTotalRealityCertificates.SixChunk8
import TraceEuclidean.VoightTotalRealityCertificates.SevenChunk0
import TraceEuclidean.VoightTotalRealityCertificates.SevenChunk1
import TraceEuclidean.VoightTotalRealityCertificates.SevenChunk2
import TraceEuclidean.VoightTotalRealityCertificates.SevenChunk3
import TraceEuclidean.VoightTotalRealityCertificates.EightChunk0
import TraceEuclidean.VoightTotalRealityCertificates.EightChunk1
import TraceEuclidean.VoightTotalRealityCertificates.NineChunk0
import TraceEuclidean.VoightTotalRealityCertificates.TenChunk0
import TraceEuclidean.VoightTotalRealityCertificates.TenChunk1
import TraceEuclidean.VoightTotalRealityCertificates.TenChunk2
import TraceEuclidean.VoightTotalRealityCertificates.TenChunk3
import TraceEuclidean.VoightTotalRealityCertificates.TenChunk4
import TraceEuclidean.VoightTotalRealityCertificates.TenChunk5
import TraceEuclidean.VoightTotalRealityCertificates.TenChunk6
import TraceEuclidean.VoightTotalRealityCertificates.TenChunk7
import TraceEuclidean.VoightAllIrreducible

/-! Real splitting of all archived Voight defining polynomials. -/

namespace TraceEuclidean

set_option linter.style.longLine false

theorem voightPolynomialRowsFive_splits :
    ∀ row ∈ voightPolynomialRowsFive,
      row.realPolynomial.Splits := by
  dsimp [voightPolynomialRowsFive]
  exact forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (voightRowsFiveChunk0_splits) voightRowsFiveChunk1_splits) voightRowsFiveChunk2_splits) voightRowsFiveChunk3_splits) voightRowsFiveChunk4_splits) voightRowsFiveChunk5_splits) voightRowsFiveChunk6_splits

theorem voightPolynomialRowsSix_splits :
    ∀ row ∈ voightPolynomialRowsSix,
      row.realPolynomial.Splits := by
  dsimp [voightPolynomialRowsSix]
  exact forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (voightRowsSixChunk0_splits) voightRowsSixChunk1_splits) voightRowsSixChunk2_splits) voightRowsSixChunk3_splits) voightRowsSixChunk4_splits) voightRowsSixChunk5_splits) voightRowsSixChunk6_splits) voightRowsSixChunk7_splits) voightRowsSixChunk8_splits

theorem voightPolynomialRowsSeven_splits :
    ∀ row ∈ voightPolynomialRowsSeven,
      row.realPolynomial.Splits := by
  dsimp [voightPolynomialRowsSeven]
  exact forall_mem_append (forall_mem_append (forall_mem_append (voightRowsSevenChunk0_splits) voightRowsSevenChunk1_splits) voightRowsSevenChunk2_splits) voightRowsSevenChunk3_splits

theorem voightPolynomialRowsEight_splits :
    ∀ row ∈ voightPolynomialRowsEight,
      row.realPolynomial.Splits := by
  dsimp [voightPolynomialRowsEight]
  exact forall_mem_append (voightRowsEightChunk0_splits) voightRowsEightChunk1_splits

theorem voightPolynomialRowsNine_splits :
    ∀ row ∈ voightPolynomialRowsNine,
      row.realPolynomial.Splits := by
  dsimp [voightPolynomialRowsNine]
  exact voightRowsNineChunk0_splits

theorem voightPolynomialRowsTen_splits :
    ∀ row ∈ voightPolynomialRowsTen,
      row.realPolynomial.Splits := by
  dsimp [voightPolynomialRowsTen]
  exact forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (voightRowsTenChunk0_splits) voightRowsTenChunk1_splits) voightRowsTenChunk2_splits) voightRowsTenChunk3_splits) voightRowsTenChunk4_splits) voightRowsTenChunk5_splits) voightRowsTenChunk6_splits) voightRowsTenChunk7_splits

/-- Every one of the 2,773 archived defining polynomials splits
completely over the real numbers. -/
theorem allVoightPolynomialRows_splits :
    ∀ row ∈ allVoightPolynomialRows,
      row.realPolynomial.Splits := by
  dsimp [allVoightPolynomialRows]
  exact forall_mem_append
    voightPolynomialRowsFive_splits
    (forall_mem_append
      voightPolynomialRowsSix_splits
      (forall_mem_append
        voightPolynomialRowsSeven_splits
        (forall_mem_append
          voightPolynomialRowsEight_splits
          (forall_mem_append
            voightPolynomialRowsNine_splits
            voightPolynomialRowsTen_splits))))

end TraceEuclidean
