import TraceEuclidean.VoightMaximalOrderExact.Chunk045
import TraceEuclidean.VoightMaximalOrderIndexOneCertificates
import TraceEuclidean.VoightMaximalOrderExactBase
import Mathlib.Tactic

set_option linter.all false

namespace TraceEuclidean

namespace VoightMaximalOrderD10R294

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R294

namespace VoightMaximalOrderD10R295

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R295

namespace VoightMaximalOrderD10R297

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R297

namespace VoightMaximalOrderD10R298

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R298

namespace VoightMaximalOrderD10R300

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R300

namespace VoightMaximalOrderD10R301

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R301

namespace VoightMaximalOrderD10R302

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R302

namespace VoightMaximalOrderD10R304

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R304

namespace VoightMaximalOrderD10R305

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R305

namespace VoightMaximalOrderD10R306

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R306

namespace VoightMaximalOrderD10R308

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R308

namespace VoightMaximalOrderD10R309

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R309

namespace VoightMaximalOrderD10R310

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R310

namespace VoightMaximalOrderD10R312

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R312

namespace VoightMaximalOrderD10R313

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R313

namespace VoightMaximalOrderD10R318

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R318

namespace VoightMaximalOrderD10R321

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R321

namespace VoightMaximalOrderD10R322

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R322

namespace VoightMaximalOrderD10R324

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R324

namespace VoightMaximalOrderD10R327

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R327

namespace VoightMaximalOrderD10R328

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R328

namespace VoightMaximalOrderD10R329

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R329

namespace VoightMaximalOrderD10R330

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R330

namespace VoightMaximalOrderD10R331

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R331

namespace VoightMaximalOrderD10R332

theorem row_presents_exact_totallyRealNumberField :
    row.PresentsExactTotallyRealNumberField := by
  have hrowAll : row ∈ allVoightPolynomialRows := by
    dsimp [allVoightPolynomialRows]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr row_mem)))))))))
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

end VoightMaximalOrderD10R332

namespace VoightMaximalOrderExactChunk049

def entries : List VoightExactFieldCertificate := [
  ⟨VoightMaximalOrderD10R294.row, VoightMaximalOrderD10R294.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R295.row, VoightMaximalOrderD10R295.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R297.row, VoightMaximalOrderD10R297.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R298.row, VoightMaximalOrderD10R298.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R300.row, VoightMaximalOrderD10R300.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R301.row, VoightMaximalOrderD10R301.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R302.row, VoightMaximalOrderD10R302.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R304.row, VoightMaximalOrderD10R304.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R305.row, VoightMaximalOrderD10R305.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R306.row, VoightMaximalOrderD10R306.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R308.row, VoightMaximalOrderD10R308.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R309.row, VoightMaximalOrderD10R309.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R310.row, VoightMaximalOrderD10R310.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R312.row, VoightMaximalOrderD10R312.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R313.row, VoightMaximalOrderD10R313.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R318.row, VoightMaximalOrderD10R318.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R321.row, VoightMaximalOrderD10R321.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R322.row, VoightMaximalOrderD10R322.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R324.row, VoightMaximalOrderD10R324.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R327.row, VoightMaximalOrderD10R327.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R328.row, VoightMaximalOrderD10R328.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R329.row, VoightMaximalOrderD10R329.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R330.row, VoightMaximalOrderD10R330.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R331.row, VoightMaximalOrderD10R331.row_presents_exact_totallyRealNumberField⟩,
  ⟨VoightMaximalOrderD10R332.row, VoightMaximalOrderD10R332.row_presents_exact_totallyRealNumberField⟩
]

end VoightMaximalOrderExactChunk049
end TraceEuclidean
