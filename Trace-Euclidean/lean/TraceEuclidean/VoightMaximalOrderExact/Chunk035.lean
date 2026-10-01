import TraceEuclidean.VoightMaximalOrderExact.Chunk031
import TraceEuclidean.VoightMaximalOrderIndexOneCertificates
import TraceEuclidean.VoightMaximalOrderExactBase
import Mathlib.Tactic

set_option linter.all false

namespace TraceEuclidean

namespace VoightMaximalOrderD7R17

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R17

namespace VoightMaximalOrderD7R19

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R19

namespace VoightMaximalOrderD7R31

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R31

namespace VoightMaximalOrderD7R42

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R42

namespace VoightMaximalOrderD7R43

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R43

namespace VoightMaximalOrderD7R47

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R47

namespace VoightMaximalOrderD7R49

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R49

namespace VoightMaximalOrderD7R57

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R57

namespace VoightMaximalOrderD7R59

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R59

namespace VoightMaximalOrderD7R67

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R67

namespace VoightMaximalOrderD7R69

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R69

namespace VoightMaximalOrderD7R71

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R71

namespace VoightMaximalOrderD7R72

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R72

namespace VoightMaximalOrderD7R85

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R85

namespace VoightMaximalOrderD7R96

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R96

namespace VoightMaximalOrderD7R105

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R105

namespace VoightMaximalOrderD7R106

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R106

namespace VoightMaximalOrderD7R107

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R107

namespace VoightMaximalOrderD7R111

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R111

namespace VoightMaximalOrderD7R118

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R118

namespace VoightMaximalOrderD7R123

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R123

namespace VoightMaximalOrderD7R130

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R130

namespace VoightMaximalOrderD7R135

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R135

namespace VoightMaximalOrderD7R142

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R142

namespace VoightMaximalOrderD7R144

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl row_mem)))))
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

end VoightMaximalOrderD7R144

namespace VoightMaximalOrderExactChunk035

def entries : List VoightExactFieldCertificate := [
  ⟨VoightMaximalOrderD7R17.row, VoightMaximalOrderD7R17.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R19.row, VoightMaximalOrderD7R19.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R31.row, VoightMaximalOrderD7R31.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R42.row, VoightMaximalOrderD7R42.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R43.row, VoightMaximalOrderD7R43.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R47.row, VoightMaximalOrderD7R47.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R49.row, VoightMaximalOrderD7R49.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R57.row, VoightMaximalOrderD7R57.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R59.row, VoightMaximalOrderD7R59.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R67.row, VoightMaximalOrderD7R67.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R69.row, VoightMaximalOrderD7R69.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R71.row, VoightMaximalOrderD7R71.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R72.row, VoightMaximalOrderD7R72.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R85.row, VoightMaximalOrderD7R85.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R96.row, VoightMaximalOrderD7R96.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R105.row, VoightMaximalOrderD7R105.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R106.row, VoightMaximalOrderD7R106.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R107.row, VoightMaximalOrderD7R107.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R111.row, VoightMaximalOrderD7R111.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R118.row, VoightMaximalOrderD7R118.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R123.row, VoightMaximalOrderD7R123.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R130.row, VoightMaximalOrderD7R130.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R135.row, VoightMaximalOrderD7R135.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R142.row, VoightMaximalOrderD7R142.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD7R144.row, VoightMaximalOrderD7R144.row_presents_exact_totallyRealNumberField⟩
]

end VoightMaximalOrderExactChunk035
end TraceEuclidean
