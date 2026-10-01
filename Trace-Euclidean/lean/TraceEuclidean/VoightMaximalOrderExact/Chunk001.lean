import TraceEuclidean.VoightMaximalOrderIndexOneCertificates
import TraceEuclidean.VoightMaximalOrderExactBase
import Mathlib.Tactic

set_option linter.all false

namespace TraceEuclidean

namespace VoightMaximalOrderD5R85

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

end VoightMaximalOrderD5R85

namespace VoightMaximalOrderD5R86

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

end VoightMaximalOrderD5R86

namespace VoightMaximalOrderD5R87

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

end VoightMaximalOrderD5R87

namespace VoightMaximalOrderD5R92

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

end VoightMaximalOrderD5R92

namespace VoightMaximalOrderD5R96

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

end VoightMaximalOrderD5R96

namespace VoightMaximalOrderD5R100

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

end VoightMaximalOrderD5R100

namespace VoightMaximalOrderD5R101

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

end VoightMaximalOrderD5R101

namespace VoightMaximalOrderD5R102

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

end VoightMaximalOrderD5R102

namespace VoightMaximalOrderD5R103

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

end VoightMaximalOrderD5R103

namespace VoightMaximalOrderD5R104

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

end VoightMaximalOrderD5R104

namespace VoightMaximalOrderD5R106

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

end VoightMaximalOrderD5R106

namespace VoightMaximalOrderD5R107

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

end VoightMaximalOrderD5R107

namespace VoightMaximalOrderD5R109

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

end VoightMaximalOrderD5R109

namespace VoightMaximalOrderD5R110

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

end VoightMaximalOrderD5R110

namespace VoightMaximalOrderD5R112

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

end VoightMaximalOrderD5R112

namespace VoightMaximalOrderD5R113

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

end VoightMaximalOrderD5R113

namespace VoightMaximalOrderD5R118

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

end VoightMaximalOrderD5R118

namespace VoightMaximalOrderD5R119

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

end VoightMaximalOrderD5R119

namespace VoightMaximalOrderD5R123

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

end VoightMaximalOrderD5R123

namespace VoightMaximalOrderD5R126

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

end VoightMaximalOrderD5R126

namespace VoightMaximalOrderD5R131

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

end VoightMaximalOrderD5R131

namespace VoightMaximalOrderD5R134

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

end VoightMaximalOrderD5R134

namespace VoightMaximalOrderD5R135

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

end VoightMaximalOrderD5R135

namespace VoightMaximalOrderD5R137

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

end VoightMaximalOrderD5R137

namespace VoightMaximalOrderD5R143

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

end VoightMaximalOrderD5R143

namespace VoightMaximalOrderExactChunk001

def entries : List VoightExactFieldCertificate := [
  ⟨VoightMaximalOrderD5R85.row, VoightMaximalOrderD5R85.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R86.row, VoightMaximalOrderD5R86.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R87.row, VoightMaximalOrderD5R87.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R92.row, VoightMaximalOrderD5R92.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R96.row, VoightMaximalOrderD5R96.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R100.row, VoightMaximalOrderD5R100.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R101.row, VoightMaximalOrderD5R101.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R102.row, VoightMaximalOrderD5R102.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R103.row, VoightMaximalOrderD5R103.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R104.row, VoightMaximalOrderD5R104.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R106.row, VoightMaximalOrderD5R106.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R107.row, VoightMaximalOrderD5R107.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R109.row, VoightMaximalOrderD5R109.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R110.row, VoightMaximalOrderD5R110.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R112.row, VoightMaximalOrderD5R112.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R113.row, VoightMaximalOrderD5R113.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R118.row, VoightMaximalOrderD5R118.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R119.row, VoightMaximalOrderD5R119.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R123.row, VoightMaximalOrderD5R123.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R126.row, VoightMaximalOrderD5R126.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R131.row, VoightMaximalOrderD5R131.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R134.row, VoightMaximalOrderD5R134.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R135.row, VoightMaximalOrderD5R135.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R137.row, VoightMaximalOrderD5R137.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R143.row, VoightMaximalOrderD5R143.row_presents_exact_totallyRealNumberField⟩
]

end VoightMaximalOrderExactChunk001
end TraceEuclidean
