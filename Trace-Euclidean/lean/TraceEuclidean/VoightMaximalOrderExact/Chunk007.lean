import TraceEuclidean.VoightMaximalOrderExact.Chunk003
import TraceEuclidean.VoightMaximalOrderIndexOneCertificates
import TraceEuclidean.VoightMaximalOrderExactBase
import Mathlib.Tactic

set_option linter.all false

namespace TraceEuclidean

namespace VoightMaximalOrderD5R392

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R392

namespace VoightMaximalOrderD5R393

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R393

namespace VoightMaximalOrderD5R396

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R396

namespace VoightMaximalOrderD5R397

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R397

namespace VoightMaximalOrderD5R398

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R398

namespace VoightMaximalOrderD5R401

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R401

namespace VoightMaximalOrderD5R403

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R403

namespace VoightMaximalOrderD5R404

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R404

namespace VoightMaximalOrderD5R406

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R406

namespace VoightMaximalOrderD5R408

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R408

namespace VoightMaximalOrderD5R410

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R410

namespace VoightMaximalOrderD5R412

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R412

namespace VoightMaximalOrderD5R413

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R413

namespace VoightMaximalOrderD5R417

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R417

namespace VoightMaximalOrderD5R418

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R418

namespace VoightMaximalOrderD5R422

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R422

namespace VoightMaximalOrderD5R423

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R423

namespace VoightMaximalOrderD5R424

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R424

namespace VoightMaximalOrderD5R425

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R425

namespace VoightMaximalOrderD5R427

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R427

namespace VoightMaximalOrderD5R428

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R428

namespace VoightMaximalOrderD5R429

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R429

namespace VoightMaximalOrderD5R431

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R431

namespace VoightMaximalOrderD5R433

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R433

namespace VoightMaximalOrderD5R435

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inl row_mem)
  have hbase :=
    allVoightPolynomialRows_present_totallyRealNumberField row
      hrowAll
  rcases hbase with ⟨hirrQ, hreal, hdegree⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  refine ⟨hirrQ, hreal, hdegree, ?_⟩
  change NumberField.discr (AdjoinRoot row.rationalPolynomial) =
    (row.fieldDiscriminant : ℤ)
  convert field_discriminant_eq_recorded using 1
  all_goals subsingleton

end VoightMaximalOrderD5R435

namespace VoightMaximalOrderExactChunk007

def entries : List VoightExactFieldCertificate := [
  ⟨VoightMaximalOrderD5R392.row, VoightMaximalOrderD5R392.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R393.row, VoightMaximalOrderD5R393.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R396.row, VoightMaximalOrderD5R396.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R397.row, VoightMaximalOrderD5R397.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R398.row, VoightMaximalOrderD5R398.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R401.row, VoightMaximalOrderD5R401.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R403.row, VoightMaximalOrderD5R403.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R404.row, VoightMaximalOrderD5R404.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R406.row, VoightMaximalOrderD5R406.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R408.row, VoightMaximalOrderD5R408.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R410.row, VoightMaximalOrderD5R410.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R412.row, VoightMaximalOrderD5R412.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R413.row, VoightMaximalOrderD5R413.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R417.row, VoightMaximalOrderD5R417.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R418.row, VoightMaximalOrderD5R418.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R422.row, VoightMaximalOrderD5R422.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R423.row, VoightMaximalOrderD5R423.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R424.row, VoightMaximalOrderD5R424.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R425.row, VoightMaximalOrderD5R425.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R427.row, VoightMaximalOrderD5R427.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R428.row, VoightMaximalOrderD5R428.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R429.row, VoightMaximalOrderD5R429.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R431.row, VoightMaximalOrderD5R431.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R433.row, VoightMaximalOrderD5R433.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R435.row, VoightMaximalOrderD5R435.row_presents_exact_totallyRealNumberField⟩
]

end VoightMaximalOrderExactChunk007
end TraceEuclidean
