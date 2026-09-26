import TraceEuclidean.V15VoightIrreducibilityCertificates.FiveChunk0Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.FiveChunk1Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.FiveChunk2Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.FiveChunk3Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.FiveChunk4Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.FiveChunk5Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.FiveChunk6Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SixChunk0Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SixChunk1Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SixChunk2Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SixChunk3Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SixChunk4Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SixChunk5Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SixChunk6Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SixChunk7Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SixChunk8Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SevenChunk0Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SevenChunk1Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SevenChunk2Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.SevenChunk3Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.EightChunk0Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.EightChunk1Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.NineChunk0Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.TenChunk0Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.TenChunk1Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.TenChunk2Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.TenChunk3Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.TenChunk4Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.TenChunk5Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.TenChunk6Part0
import TraceEuclidean.V15VoightIrreducibilityCertificates.TenChunk7Part0

/-! Rabin irreducibility theorems for all single-prime rows. -/

namespace TraceEuclidean

set_option linter.style.longLine false

theorem v15_voightPolynomialRowsFive_rabin_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsFive.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsFive)), Irreducible row.polynomial := by
  have hsplit : v15VoightPolynomialRowsFive.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsFive)) =
      (((v15VoightPolynomialRowsFiveChunk0.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsFive)) ++
      (((v15VoightPolynomialRowsFiveChunk1.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsFive)) ++
      (((v15VoightPolynomialRowsFiveChunk2.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsFive)) ++
      (((v15VoightPolynomialRowsFiveChunk3.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsFive)) ++
      (((v15VoightPolynomialRowsFiveChunk4.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsFive)) ++
      (((v15VoightPolynomialRowsFiveChunk5.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsFive)) ++
      (((v15VoightPolynomialRowsFiveChunk6.drop 0).take 74).filter fun row => decide (row ∉ v15VoightRabinExceptionsFive)) := by
    native_decide
  rw [hsplit]
  exact v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_voightRowsFiveChunk0Part0_irreducible) v15_voightRowsFiveChunk1Part0_irreducible) v15_voightRowsFiveChunk2Part0_irreducible) v15_voightRowsFiveChunk3Part0_irreducible) v15_voightRowsFiveChunk4Part0_irreducible) v15_voightRowsFiveChunk5Part0_irreducible) v15_voightRowsFiveChunk6Part0_irreducible

theorem v15_voightPolynomialRowsSix_rabin_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsSix.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsSix)), Irreducible row.polynomial := by
  have hsplit : v15VoightPolynomialRowsSix.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsSix)) =
      (((v15VoightPolynomialRowsSixChunk0.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSix)) ++
      (((v15VoightPolynomialRowsSixChunk1.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSix)) ++
      (((v15VoightPolynomialRowsSixChunk2.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSix)) ++
      (((v15VoightPolynomialRowsSixChunk3.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSix)) ++
      (((v15VoightPolynomialRowsSixChunk4.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSix)) ++
      (((v15VoightPolynomialRowsSixChunk5.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSix)) ++
      (((v15VoightPolynomialRowsSixChunk6.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSix)) ++
      (((v15VoightPolynomialRowsSixChunk7.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSix)) ++
      (((v15VoightPolynomialRowsSixChunk8.drop 0).take 27).filter fun row => decide (row ∉ v15VoightRabinExceptionsSix)) := by
    native_decide
  rw [hsplit]
  exact v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_voightRowsSixChunk0Part0_irreducible) v15_voightRowsSixChunk1Part0_irreducible) v15_voightRowsSixChunk2Part0_irreducible) v15_voightRowsSixChunk3Part0_irreducible) v15_voightRowsSixChunk4Part0_irreducible) v15_voightRowsSixChunk5Part0_irreducible) v15_voightRowsSixChunk6Part0_irreducible) v15_voightRowsSixChunk7Part0_irreducible) v15_voightRowsSixChunk8Part0_irreducible

theorem v15_voightPolynomialRowsSeven_rabin_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsSeven.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsSeven)), Irreducible row.polynomial := by
  have hsplit : v15VoightPolynomialRowsSeven.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsSeven)) =
      (((v15VoightPolynomialRowsSevenChunk0.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSeven)) ++
      (((v15VoightPolynomialRowsSevenChunk1.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSeven)) ++
      (((v15VoightPolynomialRowsSevenChunk2.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsSeven)) ++
      (((v15VoightPolynomialRowsSevenChunk3.drop 0).take 1).filter fun row => decide (row ∉ v15VoightRabinExceptionsSeven)) := by
    native_decide
  rw [hsplit]
  exact v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_voightRowsSevenChunk0Part0_irreducible) v15_voightRowsSevenChunk1Part0_irreducible) v15_voightRowsSevenChunk2Part0_irreducible) v15_voightRowsSevenChunk3Part0_irreducible

theorem v15_voightPolynomialRowsEight_rabin_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsEight.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsEight)), Irreducible row.polynomial := by
  have hsplit : v15VoightPolynomialRowsEight.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsEight)) =
      (((v15VoightPolynomialRowsEightChunk0.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsEight)) ++
      (((v15VoightPolynomialRowsEightChunk1.drop 0).take 64).filter fun row => decide (row ∉ v15VoightRabinExceptionsEight)) := by
    native_decide
  rw [hsplit]
  exact v15_forall_mem_append (v15_voightRowsEightChunk0Part0_irreducible) v15_voightRowsEightChunk1Part0_irreducible

theorem v15_voightPolynomialRowsNine_rabin_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsNine.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsNine)), Irreducible row.polynomial := by
  have hsplit : v15VoightPolynomialRowsNine.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsNine)) =
      (((v15VoightPolynomialRowsNineChunk0.drop 0).take 15).filter fun row => decide (row ∉ v15VoightRabinExceptionsNine)) := by
    native_decide
  rw [hsplit]
  exact v15_voightRowsNineChunk0Part0_irreducible

theorem v15_voightPolynomialRowsTen_rabin_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsTen.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsTen)), Irreducible row.polynomial := by
  have hsplit : v15VoightPolynomialRowsTen.filter
      (fun row => decide (row ∉ v15VoightRabinExceptionsTen)) =
      (((v15VoightPolynomialRowsTenChunk0.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsTen)) ++
      (((v15VoightPolynomialRowsTenChunk1.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsTen)) ++
      (((v15VoightPolynomialRowsTenChunk2.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsTen)) ++
      (((v15VoightPolynomialRowsTenChunk3.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsTen)) ++
      (((v15VoightPolynomialRowsTenChunk4.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsTen)) ++
      (((v15VoightPolynomialRowsTenChunk5.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsTen)) ++
      (((v15VoightPolynomialRowsTenChunk6.drop 0).take 100).filter fun row => decide (row ∉ v15VoightRabinExceptionsTen)) ++
      (((v15VoightPolynomialRowsTenChunk7.drop 0).take 92).filter fun row => decide (row ∉ v15VoightRabinExceptionsTen)) := by
    native_decide
  rw [hsplit]
  exact v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_forall_mem_append (v15_voightRowsTenChunk0Part0_irreducible) v15_voightRowsTenChunk1Part0_irreducible) v15_voightRowsTenChunk2Part0_irreducible) v15_voightRowsTenChunk3Part0_irreducible) v15_voightRowsTenChunk4Part0_irreducible) v15_voightRowsTenChunk5Part0_irreducible) v15_voightRowsTenChunk6Part0_irreducible) v15_voightRowsTenChunk7Part0_irreducible

end TraceEuclidean
