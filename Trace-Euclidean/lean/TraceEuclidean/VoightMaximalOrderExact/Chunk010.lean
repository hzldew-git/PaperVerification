import TraceEuclidean.VoightMaximalOrderExact.Chunk006
import TraceEuclidean.VoightMaximalOrderIndexOneCertificates
import TraceEuclidean.VoightMaximalOrderExactBase
import Mathlib.Tactic

set_option linter.all false

namespace TraceEuclidean

namespace VoightMaximalOrderD5R556

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

end VoightMaximalOrderD5R556

namespace VoightMaximalOrderD5R557

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

end VoightMaximalOrderD5R557

namespace VoightMaximalOrderD5R558

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

end VoightMaximalOrderD5R558

namespace VoightMaximalOrderD5R559

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

end VoightMaximalOrderD5R559

namespace VoightMaximalOrderD5R560

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

end VoightMaximalOrderD5R560

namespace VoightMaximalOrderD5R562

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

end VoightMaximalOrderD5R562

namespace VoightMaximalOrderD5R565

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

end VoightMaximalOrderD5R565

namespace VoightMaximalOrderD5R566

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

end VoightMaximalOrderD5R566

namespace VoightMaximalOrderD5R570

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

end VoightMaximalOrderD5R570

namespace VoightMaximalOrderD5R572

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

end VoightMaximalOrderD5R572

namespace VoightMaximalOrderD5R576

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

end VoightMaximalOrderD5R576

namespace VoightMaximalOrderD5R579

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

end VoightMaximalOrderD5R579

namespace VoightMaximalOrderD5R581

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

end VoightMaximalOrderD5R581

namespace VoightMaximalOrderD5R582

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

end VoightMaximalOrderD5R582

namespace VoightMaximalOrderD5R583

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

end VoightMaximalOrderD5R583

namespace VoightMaximalOrderD5R587

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

end VoightMaximalOrderD5R587

namespace VoightMaximalOrderD5R589

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

end VoightMaximalOrderD5R589

namespace VoightMaximalOrderD5R593

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

end VoightMaximalOrderD5R593

namespace VoightMaximalOrderD5R594

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

end VoightMaximalOrderD5R594

namespace VoightMaximalOrderD5R595

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

end VoightMaximalOrderD5R595

namespace VoightMaximalOrderD5R596

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

end VoightMaximalOrderD5R596

namespace VoightMaximalOrderD5R598

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

end VoightMaximalOrderD5R598

namespace VoightMaximalOrderD5R599

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

end VoightMaximalOrderD5R599

namespace VoightMaximalOrderD5R601

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

end VoightMaximalOrderD5R601

namespace VoightMaximalOrderD5R603

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

end VoightMaximalOrderD5R603

namespace VoightMaximalOrderExactChunk010

def entries : List VoightExactFieldCertificate := [
  ⟨VoightMaximalOrderD5R556.row, VoightMaximalOrderD5R556.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R557.row, VoightMaximalOrderD5R557.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R558.row, VoightMaximalOrderD5R558.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R559.row, VoightMaximalOrderD5R559.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R560.row, VoightMaximalOrderD5R560.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R562.row, VoightMaximalOrderD5R562.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R565.row, VoightMaximalOrderD5R565.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R566.row, VoightMaximalOrderD5R566.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R570.row, VoightMaximalOrderD5R570.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R572.row, VoightMaximalOrderD5R572.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R576.row, VoightMaximalOrderD5R576.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R579.row, VoightMaximalOrderD5R579.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R581.row, VoightMaximalOrderD5R581.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R582.row, VoightMaximalOrderD5R582.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R583.row, VoightMaximalOrderD5R583.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R587.row, VoightMaximalOrderD5R587.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R589.row, VoightMaximalOrderD5R589.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R593.row, VoightMaximalOrderD5R593.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R594.row, VoightMaximalOrderD5R594.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R595.row, VoightMaximalOrderD5R595.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R596.row, VoightMaximalOrderD5R596.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R598.row, VoightMaximalOrderD5R598.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R599.row, VoightMaximalOrderD5R599.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R601.row, VoightMaximalOrderD5R601.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD5R603.row, VoightMaximalOrderD5R603.row_presents_exact_totallyRealNumberField⟩
]

end VoightMaximalOrderExactChunk010
end TraceEuclidean
