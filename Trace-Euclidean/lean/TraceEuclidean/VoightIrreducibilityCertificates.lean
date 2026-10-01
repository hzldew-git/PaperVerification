import TraceEuclidean.VoightIrreducibilityCertificates.FiveChunk0Part0
import TraceEuclidean.VoightIrreducibilityCertificates.FiveChunk1Part0
import TraceEuclidean.VoightIrreducibilityCertificates.FiveChunk2Part0
import TraceEuclidean.VoightIrreducibilityCertificates.FiveChunk3Part0
import TraceEuclidean.VoightIrreducibilityCertificates.FiveChunk4Part0
import TraceEuclidean.VoightIrreducibilityCertificates.FiveChunk5Part0
import TraceEuclidean.VoightIrreducibilityCertificates.FiveChunk6Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SixChunk0Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SixChunk1Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SixChunk2Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SixChunk3Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SixChunk4Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SixChunk5Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SixChunk6Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SixChunk7Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SixChunk8Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SevenChunk0Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SevenChunk1Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SevenChunk2Part0
import TraceEuclidean.VoightIrreducibilityCertificates.SevenChunk3Part0
import TraceEuclidean.VoightIrreducibilityCertificates.EightChunk0Part0
import TraceEuclidean.VoightIrreducibilityCertificates.EightChunk1Part0
import TraceEuclidean.VoightIrreducibilityCertificates.NineChunk0Part0
import TraceEuclidean.VoightIrreducibilityCertificates.TenChunk0Part0
import TraceEuclidean.VoightIrreducibilityCertificates.TenChunk1Part0
import TraceEuclidean.VoightIrreducibilityCertificates.TenChunk2Part0
import TraceEuclidean.VoightIrreducibilityCertificates.TenChunk3Part0
import TraceEuclidean.VoightIrreducibilityCertificates.TenChunk4Part0
import TraceEuclidean.VoightIrreducibilityCertificates.TenChunk5Part0
import TraceEuclidean.VoightIrreducibilityCertificates.TenChunk6Part0
import TraceEuclidean.VoightIrreducibilityCertificates.TenChunk7Part0

/-! Rabin irreducibility theorems for all single-prime rows. -/

namespace TraceEuclidean

set_option linter.style.longLine false

theorem voightPolynomialRowsFive_rabin_irreducible :
    ∀ row ∈ voightPolynomialRowsFive.filter
      (fun row => decide (row ∉ voightRabinExceptionsFive)), Irreducible row.polynomial := by
  have hsplit : voightPolynomialRowsFive.filter
      (fun row => decide (row ∉ voightRabinExceptionsFive)) =
      (((voightPolynomialRowsFiveChunk0.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsFive)) ++
      (((voightPolynomialRowsFiveChunk1.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsFive)) ++
      (((voightPolynomialRowsFiveChunk2.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsFive)) ++
      (((voightPolynomialRowsFiveChunk3.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsFive)) ++
      (((voightPolynomialRowsFiveChunk4.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsFive)) ++
      (((voightPolynomialRowsFiveChunk5.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsFive)) ++
      (((voightPolynomialRowsFiveChunk6.drop 0).take 74).filter fun row => decide (row ∉ voightRabinExceptionsFive)) := by
    native_decide
  rw [hsplit]
  exact forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (voightRowsFiveChunk0Part0_irreducible) voightRowsFiveChunk1Part0_irreducible) voightRowsFiveChunk2Part0_irreducible) voightRowsFiveChunk3Part0_irreducible) voightRowsFiveChunk4Part0_irreducible) voightRowsFiveChunk5Part0_irreducible) voightRowsFiveChunk6Part0_irreducible

theorem voightPolynomialRowsSix_rabin_irreducible :
    ∀ row ∈ voightPolynomialRowsSix.filter
      (fun row => decide (row ∉ voightRabinExceptionsSix)), Irreducible row.polynomial := by
  have hsplit : voightPolynomialRowsSix.filter
      (fun row => decide (row ∉ voightRabinExceptionsSix)) =
      (((voightPolynomialRowsSixChunk0.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSix)) ++
      (((voightPolynomialRowsSixChunk1.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSix)) ++
      (((voightPolynomialRowsSixChunk2.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSix)) ++
      (((voightPolynomialRowsSixChunk3.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSix)) ++
      (((voightPolynomialRowsSixChunk4.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSix)) ++
      (((voightPolynomialRowsSixChunk5.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSix)) ++
      (((voightPolynomialRowsSixChunk6.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSix)) ++
      (((voightPolynomialRowsSixChunk7.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSix)) ++
      (((voightPolynomialRowsSixChunk8.drop 0).take 27).filter fun row => decide (row ∉ voightRabinExceptionsSix)) := by
    native_decide
  rw [hsplit]
  exact forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (voightRowsSixChunk0Part0_irreducible) voightRowsSixChunk1Part0_irreducible) voightRowsSixChunk2Part0_irreducible) voightRowsSixChunk3Part0_irreducible) voightRowsSixChunk4Part0_irreducible) voightRowsSixChunk5Part0_irreducible) voightRowsSixChunk6Part0_irreducible) voightRowsSixChunk7Part0_irreducible) voightRowsSixChunk8Part0_irreducible

theorem voightPolynomialRowsSeven_rabin_irreducible :
    ∀ row ∈ voightPolynomialRowsSeven.filter
      (fun row => decide (row ∉ voightRabinExceptionsSeven)), Irreducible row.polynomial := by
  have hsplit : voightPolynomialRowsSeven.filter
      (fun row => decide (row ∉ voightRabinExceptionsSeven)) =
      (((voightPolynomialRowsSevenChunk0.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSeven)) ++
      (((voightPolynomialRowsSevenChunk1.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSeven)) ++
      (((voightPolynomialRowsSevenChunk2.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsSeven)) ++
      (((voightPolynomialRowsSevenChunk3.drop 0).take 1).filter fun row => decide (row ∉ voightRabinExceptionsSeven)) := by
    native_decide
  rw [hsplit]
  exact forall_mem_append (forall_mem_append (forall_mem_append (voightRowsSevenChunk0Part0_irreducible) voightRowsSevenChunk1Part0_irreducible) voightRowsSevenChunk2Part0_irreducible) voightRowsSevenChunk3Part0_irreducible

theorem voightPolynomialRowsEight_rabin_irreducible :
    ∀ row ∈ voightPolynomialRowsEight.filter
      (fun row => decide (row ∉ voightRabinExceptionsEight)), Irreducible row.polynomial := by
  have hsplit : voightPolynomialRowsEight.filter
      (fun row => decide (row ∉ voightRabinExceptionsEight)) =
      (((voightPolynomialRowsEightChunk0.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsEight)) ++
      (((voightPolynomialRowsEightChunk1.drop 0).take 64).filter fun row => decide (row ∉ voightRabinExceptionsEight)) := by
    native_decide
  rw [hsplit]
  exact forall_mem_append (voightRowsEightChunk0Part0_irreducible) voightRowsEightChunk1Part0_irreducible

theorem voightPolynomialRowsNine_rabin_irreducible :
    ∀ row ∈ voightPolynomialRowsNine.filter
      (fun row => decide (row ∉ voightRabinExceptionsNine)), Irreducible row.polynomial := by
  have hsplit : voightPolynomialRowsNine.filter
      (fun row => decide (row ∉ voightRabinExceptionsNine)) =
      (((voightPolynomialRowsNineChunk0.drop 0).take 15).filter fun row => decide (row ∉ voightRabinExceptionsNine)) := by
    native_decide
  rw [hsplit]
  exact voightRowsNineChunk0Part0_irreducible

theorem voightPolynomialRowsTen_rabin_irreducible :
    ∀ row ∈ voightPolynomialRowsTen.filter
      (fun row => decide (row ∉ voightRabinExceptionsTen)), Irreducible row.polynomial := by
  have hsplit : voightPolynomialRowsTen.filter
      (fun row => decide (row ∉ voightRabinExceptionsTen)) =
      (((voightPolynomialRowsTenChunk0.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsTen)) ++
      (((voightPolynomialRowsTenChunk1.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsTen)) ++
      (((voightPolynomialRowsTenChunk2.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsTen)) ++
      (((voightPolynomialRowsTenChunk3.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsTen)) ++
      (((voightPolynomialRowsTenChunk4.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsTen)) ++
      (((voightPolynomialRowsTenChunk5.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsTen)) ++
      (((voightPolynomialRowsTenChunk6.drop 0).take 100).filter fun row => decide (row ∉ voightRabinExceptionsTen)) ++
      (((voightPolynomialRowsTenChunk7.drop 0).take 92).filter fun row => decide (row ∉ voightRabinExceptionsTen)) := by
    native_decide
  rw [hsplit]
  exact forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (forall_mem_append (voightRowsTenChunk0Part0_irreducible) voightRowsTenChunk1Part0_irreducible) voightRowsTenChunk2Part0_irreducible) voightRowsTenChunk3Part0_irreducible) voightRowsTenChunk4Part0_irreducible) voightRowsTenChunk5Part0_irreducible) voightRowsTenChunk6Part0_irreducible) voightRowsTenChunk7Part0_irreducible

end TraceEuclidean
