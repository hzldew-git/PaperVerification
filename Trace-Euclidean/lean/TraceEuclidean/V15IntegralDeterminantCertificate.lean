import TraceEuclidean.V15VoightDiscriminantData

/-!
# Integer Bareiss determinant certificates

This module replays fraction-free integer row reduction.  Exact divisibility
is checked at every division, while the proof maps each accepted operation to
the corresponding rational row operation and tracks its determinant factor.
-/

namespace TraceEuclidean

open Matrix

/-- Reify a functional integer matrix through nested vectors.  This is
extensionally the identity, but it prevents long chains of `updateRow`
closures during native certificate evaluation. -/
def v15MaterializeIntMatrix {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  let rows : Vector (Vector ℤ n) n :=
    Vector.ofFn fun row => Vector.ofFn fun column => matrix row column
  fun row column => (rows.get row).get column

@[simp]
theorem v15MaterializeIntMatrix_apply {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℤ) (row column : Fin n) :
    v15MaterializeIntMatrix matrix row column = matrix row column := by
  simp [v15MaterializeIntMatrix]

@[simp]
theorem v15MaterializeIntMatrix_eq {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℤ) :
    v15MaterializeIntMatrix matrix = matrix := by
  ext row column
  simp

/-- Integer row operations used by fraction-free elimination. -/
inductive V15IntegralRowOperation (n : ℕ) where
  | combine (target source : Fin n) (scale sourceScale : ℤ)
  | divide (target : Fin n) (divisor : ℤ)
  | swap (first second : Fin n)
deriving DecidableEq, Repr

namespace V15IntegralRowOperation

/-- Replay one integer row operation.  Degenerate operations are identities;
the certificate validity predicate rejects them. -/
def apply {n : ℕ} (operation : V15IntegralRowOperation n)
    (matrix : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  v15MaterializeIntMatrix <| match operation with
  | .combine target source scale sourceScale =>
      if target = source then matrix
      else matrix.updateRow target
        (scale • matrix target + sourceScale • matrix source)
  | .divide target divisor =>
      if divisor = 0 then matrix
      else matrix.updateRow target (fun column => matrix target column / divisor)
  | .swap first second =>
      matrix.submatrix (Equiv.swap first second) id

/-- Executable validity test for one operation at the matrix where it is
applied. -/
def valid {n : ℕ} (operation : V15IntegralRowOperation n)
    (matrix : Matrix (Fin n) (Fin n) ℤ) : Bool :=
  match operation with
  | .combine target source scale _ =>
      decide (target ≠ source ∧ scale ≠ 0)
  | .divide target divisor =>
      decide (divisor ≠ 0) &&
        (List.finRange n).all fun column =>
          decide (matrix target column % divisor = 0)
  | .swap _ _ => true

/-- Rational determinant factor of one accepted integer operation. -/
def multiplier {n : ℕ} : V15IntegralRowOperation n → ℚ
  | .combine _ _ scale _ => (scale : ℚ)
  | .divide _ divisor => ((divisor : ℚ)⁻¹)
  | .swap first second => if first = second then 1 else -1

/-- Exact integer division becomes rational division after casting. -/
theorem cast_ediv_of_emod_eq_zero {value divisor : ℤ}
    (hdivisor : divisor ≠ 0) (hexact : value % divisor = 0) :
    ((value / divisor : ℤ) : ℚ) = (divisor : ℚ)⁻¹ * (value : ℚ) := by
  rw [inv_mul_eq_div]
  apply (eq_div_iff (by exact_mod_cast hdivisor)).2
  exact_mod_cast Int.ediv_mul_cancel
    (Int.dvd_iff_emod_eq_zero.mpr hexact)

/-- One accepted integer operation changes the rational determinant by its
recorded multiplier. -/
theorem det_map_apply_of_valid {n : ℕ}
    (operation : V15IntegralRowOperation n)
    (matrix : Matrix (Fin n) (Fin n) ℤ)
    (hvalid : operation.valid matrix = true) :
    ((Int.castRingHom ℚ).mapMatrix (operation.apply matrix)).det =
      operation.multiplier *
        ((Int.castRingHom ℚ).mapMatrix matrix).det := by
  cases operation with
  | combine target source scale sourceScale =>
      have hconditions : target ≠ source ∧ scale ≠ 0 := by
        simpa [valid] using of_decide_eq_true hvalid
      have hmap :
          (Int.castRingHom ℚ).mapMatrix
              ((V15IntegralRowOperation.combine target source scale sourceScale).apply matrix) =
            ((Int.castRingHom ℚ).mapMatrix matrix).updateRow target
              ((scale : ℚ) • (Int.castRingHom ℚ).mapMatrix matrix target +
                (sourceScale : ℚ) •
                  (Int.castRingHom ℚ).mapMatrix matrix source) := by
        ext row column
        by_cases hrow : row = target
        · subst row
          simp [apply, hconditions.1]
        · simp [apply, hconditions.1, hrow]
      rw [hmap, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
        Matrix.updateRow_eq_self, Matrix.det_updateRow_smul,
        Matrix.det_updateRow_eq_zero hconditions.1.symm, mul_zero, add_zero]
      rfl
  | divide target divisor =>
      have hall :
          decide (divisor ≠ 0) = true ∧
            (List.finRange n).all (fun column =>
              decide (matrix target column % divisor = 0)) = true := by
        simpa [valid] using hvalid
      have hdivisor : divisor ≠ 0 := by
        exact of_decide_eq_true hall.1
      have hexact : ∀ column, matrix target column % divisor = 0 := by
        intro column
        have hcolumn :=
          (List.all_eq_true.mp hall.2) column (List.mem_finRange column)
        exact of_decide_eq_true hcolumn
      have hmap :
          (Int.castRingHom ℚ).mapMatrix
              ((V15IntegralRowOperation.divide target divisor).apply matrix) =
            ((Int.castRingHom ℚ).mapMatrix matrix).updateRow target
              ((divisor : ℚ)⁻¹ •
                (Int.castRingHom ℚ).mapMatrix matrix target) := by
        ext row column
        by_cases hrow : row = target
        · subst row
          simp [apply, hdivisor, cast_ediv_of_emod_eq_zero hdivisor (hexact column)]
        · simp [apply, hdivisor, hrow]
      rw [hmap, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
      rfl
  | swap first second =>
      rw [apply, v15MaterializeIntMatrix_eq]
      change
        (((Int.castRingHom ℚ).mapMatrix matrix).submatrix
          (Equiv.swap first second) id).det = _
      rw [Matrix.det_permute]
      by_cases h : first = second
      · simp [multiplier, h]
      · simp [multiplier, h, Equiv.Perm.sign_swap h]

/-- Replay a list, rejecting the first invalid operation. -/
def applyAll? {n : ℕ} :
    List (V15IntegralRowOperation n) →
      Matrix (Fin n) (Fin n) ℤ → Option (Matrix (Fin n) (Fin n) ℤ)
  | [], matrix => some matrix
  | operation :: operations, matrix =>
      if operation.valid matrix then
        applyAll? operations (operation.apply matrix)
      else none

/-- Product of all rational determinant factors. -/
def multiplierAll {n : ℕ} : List (V15IntegralRowOperation n) → ℚ
  | [] => 1
  | operation :: operations =>
      operation.multiplier * multiplierAll operations

/-- Successful replay carries the exact rational determinant relation. -/
theorem det_map_eq_of_applyAll?_eq_some {n : ℕ}
    {operations : List (V15IntegralRowOperation n)}
    {initial reduced : Matrix (Fin n) (Fin n) ℤ}
    (hreplay : applyAll? operations initial = some reduced) :
    ((Int.castRingHom ℚ).mapMatrix reduced).det =
      multiplierAll operations *
        ((Int.castRingHom ℚ).mapMatrix initial).det := by
  induction operations generalizing initial reduced with
  | nil =>
      simp [applyAll?] at hreplay
      subst reduced
      simp [multiplierAll]
  | cons operation operations induction =>
      by_cases hvalid : operation.valid initial = true
      · simp only [applyAll?, hvalid, if_true] at hreplay
        rw [induction hreplay, det_map_apply_of_valid operation initial hvalid]
        simp only [multiplierAll]
        ring
      · have : operation.valid initial = false := Bool.eq_false_of_not_eq_true hvalid
        simp [applyAll?, this] at hreplay

end V15IntegralRowOperation

/-- Strict vector-backed representation used only by the executable
certificate generator and replay engine. -/
abbrev V15IntVectorMatrix (n : ℕ) := Vector (Vector ℤ n) n

/-- Reify a mathematical matrix as a strict vector-backed matrix. -/
def v15IntVectorMatrixOfMatrix {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℤ) : V15IntVectorMatrix n :=
  Vector.ofFn fun row => Vector.ofFn fun column => matrix row column

/-- View a vector-backed matrix as a mathematical matrix. -/
def V15IntVectorMatrix.toMatrix {n : ℕ}
    (matrix : V15IntVectorMatrix n) : Matrix (Fin n) (Fin n) ℤ :=
  fun row column => matrix[row.val][column.val]

@[simp]
theorem v15IntVectorMatrixOfMatrix_toMatrix {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℤ) :
    (v15IntVectorMatrixOfMatrix matrix).toMatrix = matrix := by
  ext row column
  simp [v15IntVectorMatrixOfMatrix, V15IntVectorMatrix.toMatrix]

namespace V15IntegralRowOperation

/-- Strict replay of one operation on the vector-backed runtime matrix. -/
def applyVector {n : ℕ} (operation : V15IntegralRowOperation n)
    (matrix : V15IntVectorMatrix n) : V15IntVectorMatrix n :=
  match operation with
  | .combine target source scale sourceScale =>
      if target = source then matrix
      else
        let targetRow := matrix.get target
        let sourceRow := matrix.get source
        let newRow := Vector.zipWith
          (fun value sourceValue => scale * value + sourceScale * sourceValue)
          targetRow sourceRow
        matrix.set target.val newRow target.isLt
  | .divide target divisor =>
      if divisor = 0 then matrix
      else matrix.set target.val
        ((matrix.get target).map (fun value => value / divisor)) target.isLt
  | .swap first second =>
      if first = second then matrix
      else
        let firstRow := matrix.get first
        let secondRow := matrix.get second
        (matrix.set first.val secondRow first.isLt).set
          second.val firstRow second.isLt

/-- Validity test using the strict runtime representation. -/
def validVector {n : ℕ} (operation : V15IntegralRowOperation n)
    (matrix : V15IntVectorMatrix n) : Bool :=
  operation.valid matrix.toMatrix

/-- Strict replay of a list, rejecting the first invalid operation. -/
def applyAllVector? {n : ℕ} :
    List (V15IntegralRowOperation n) →
      V15IntVectorMatrix n → Option (V15IntVectorMatrix n)
  | [], matrix => some matrix
  | operation :: operations, matrix =>
      if operation.validVector matrix then
        applyAllVector? operations (operation.applyVector matrix)
      else none

/-- Strict replay and mathematical replay have the same entries. -/
theorem applyVector_toMatrix {n : ℕ}
    (operation : V15IntegralRowOperation n)
    (matrix : V15IntVectorMatrix n) :
    (operation.applyVector matrix).toMatrix =
      operation.apply matrix.toMatrix := by
  cases operation with
  | combine target source scale sourceScale =>
      by_cases h : target = source
      · simp [applyVector, apply, h]
      · ext row column
        by_cases hrow : row = target
        · subst row
          simp [applyVector, apply, h, V15IntVectorMatrix.toMatrix,
            Vector.getElem_set_self, Vector.getElem_zipWith,
            Vector.get_eq_getElem]
        · have hval : target.val ≠ row.val := by
            intro hval
            apply hrow
            exact Fin.ext hval.symm
          simp [applyVector, apply, h, hrow,
            V15IntVectorMatrix.toMatrix,
            Vector.getElem_set_ne target.isLt row.isLt hval,
            Vector.get_eq_getElem]
  | divide target divisor =>
      by_cases h : divisor = 0
      · simp [applyVector, apply, h]
      · ext row column
        by_cases hrow : row = target
        · subst row
          simp [applyVector, apply, h, V15IntVectorMatrix.toMatrix,
            Vector.getElem_set_self, Vector.getElem_map,
            Vector.get_eq_getElem]
        · have hval : target.val ≠ row.val := by
            intro hval
            apply hrow
            exact Fin.ext hval.symm
          simp [applyVector, apply, h, hrow,
            V15IntVectorMatrix.toMatrix,
            Vector.getElem_set_ne target.isLt row.isLt hval,
            Vector.get_eq_getElem]
  | swap first second =>
      by_cases h : first = second
      · simp [applyVector, apply, h]
      · ext row column
        by_cases hfirst : row = first
        · subst row
          have hval : second.val ≠ first.val := by
            intro hval
            apply h
            exact Fin.ext hval.symm
          simp [applyVector, apply, h, V15IntVectorMatrix.toMatrix,
            Vector.getElem_set_self,
            Vector.getElem_set_ne second.isLt first.isLt hval,
            Vector.get_eq_getElem]
        · by_cases hsecond : row = second
          · subst row
            simp [applyVector, apply, h, V15IntVectorMatrix.toMatrix,
              Vector.getElem_set_self,
              Vector.get_eq_getElem]
          · have hfirstVal : first.val ≠ row.val := by
              intro hval
              apply hfirst
              exact Fin.ext hval.symm
            have hsecondVal : second.val ≠ row.val := by
              intro hval
              apply hsecond
              exact Fin.ext hval.symm
            simp [applyVector, apply, h,
              V15IntVectorMatrix.toMatrix,
              Vector.getElem_set_ne first.isLt row.isLt hfirstVal,
              Vector.getElem_set_ne second.isLt row.isLt hsecondVal,
              Vector.get_eq_getElem,
              Equiv.swap_apply_of_ne_of_ne hfirst hsecond]

/-- Mapping strict replay back to matrices gives the mathematical replay. -/
theorem applyAllVector?_toMatrix {n : ℕ}
    (operations : List (V15IntegralRowOperation n))
    (matrix : V15IntVectorMatrix n) :
    Option.map V15IntVectorMatrix.toMatrix
        (applyAllVector? operations matrix) =
      applyAll? operations matrix.toMatrix := by
  induction operations generalizing matrix with
  | nil => rfl
  | cons operation operations induction =>
      by_cases hvalid : operation.valid matrix.toMatrix = true
      · simp [applyAllVector?, applyAll?, validVector, hvalid,
          induction, applyVector_toMatrix]
      · have hfalse : operation.valid matrix.toMatrix = false :=
          Bool.eq_false_of_not_eq_true hvalid
        simp [applyAllVector?, applyAll?, validVector, hfalse]

end V15IntegralRowOperation

/-- Executable upper-triangularity test for integer matrices. -/
def v15IsUpperTriangularInt {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℤ) : Bool :=
  (List.finRange n).all fun row =>
    (List.finRange n).all fun column =>
      decide (column < row → matrix row column = 0)

/-- Passing the executable integer test gives mathlib's predicate after
casting to the rationals. -/
theorem blockTriangular_map_of_v15IsUpperTriangularInt {n : ℕ}
    {matrix : Matrix (Fin n) (Fin n) ℤ}
    (h : v15IsUpperTriangularInt matrix = true) :
    ((Int.castRingHom ℚ).mapMatrix matrix).BlockTriangular id := by
  intro row column hcolumn
  have hrow := (List.all_eq_true.mp h) row (List.mem_finRange row)
  have hentry :=
    (List.all_eq_true.mp hrow) column (List.mem_finRange column)
  have := (of_decide_eq_true hentry) hcolumn
  simpa using congrArg (Int.castRingHom ℚ) this

/-- Find a nonzero integer pivot at or below the diagonal. -/
def v15FindIntegralPivot {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℤ)
    (pivot : Fin n) : Option (Fin n) :=
  (List.finRange n).find? fun row =>
    decide (pivot ≤ row ∧ matrix row pivot ≠ 0)

/-- Strict-vector form of pivot search. -/
def v15FindIntegralPivotVector {n : ℕ}
    (matrix : V15IntVectorMatrix n)
    (pivot : Fin n) : Option (Fin n) :=
  (List.finRange n).find? fun row =>
    decide (pivot ≤ row ∧ (matrix.get row).get pivot ≠ 0)

/-- One Bareiss elimination round below a fixed pivot. -/
def v15BareissEliminateBelow {n : ℕ}
    (pivot : Fin n) (previousPivot : ℤ) :
    List (Fin n) → Matrix (Fin n) (Fin n) ℤ →
      List (V15IntegralRowOperation n) × Matrix (Fin n) (Fin n) ℤ
  | [], matrix => ([], matrix)
  | row :: rows, matrix =>
      if pivot < row then
        let combineOperation := V15IntegralRowOperation.combine row pivot
          (matrix pivot pivot) (-matrix row pivot)
        let combined := combineOperation.apply matrix
        let divideOperation :=
          V15IntegralRowOperation.divide row previousPivot
        let divided := divideOperation.apply combined
        let result :=
          v15BareissEliminateBelow pivot previousPivot rows divided
        (combineOperation :: divideOperation :: result.1, result.2)
      else
        v15BareissEliminateBelow pivot previousPivot rows matrix

/-- Strict-vector Bareiss elimination below one pivot. -/
def v15BareissEliminateBelowVector {n : ℕ}
    (pivot : Fin n) (previousPivot : ℤ) :
    List (Fin n) → V15IntVectorMatrix n →
      List (V15IntegralRowOperation n) × V15IntVectorMatrix n
  | [], matrix => ([], matrix)
  | row :: rows, matrix =>
      if pivot < row then
        let combineOperation := V15IntegralRowOperation.combine row pivot
          ((matrix.get pivot).get pivot) (-((matrix.get row).get pivot))
        let combined := combineOperation.applyVector matrix
        let divideOperation :=
          V15IntegralRowOperation.divide row previousPivot
        let divided := divideOperation.applyVector combined
        let result :=
          v15BareissEliminateBelowVector pivot previousPivot rows divided
        (combineOperation :: divideOperation :: result.1, result.2)
      else
        v15BareissEliminateBelowVector pivot previousPivot rows matrix

/-- Fraction-free Bareiss operations proposed for a square integer matrix. -/
def v15BareissAux {n : ℕ} :
    List (Fin n) → ℤ → Matrix (Fin n) (Fin n) ℤ →
      List (V15IntegralRowOperation n) × Matrix (Fin n) (Fin n) ℤ
  | [], _, matrix => ([], matrix)
  | pivot :: pivots, previousPivot, matrix =>
      match v15FindIntegralPivot matrix pivot with
      | none => v15BareissAux pivots previousPivot matrix
      | some pivotRow =>
          let swapOperation := V15IntegralRowOperation.swap pivot pivotRow
          let swapped := swapOperation.apply matrix
          let pivotValue := swapped pivot pivot
          let eliminated := v15BareissEliminateBelow pivot previousPivot
            (List.finRange n) swapped
          let remaining := v15BareissAux pivots pivotValue eliminated.2
          (swapOperation :: eliminated.1 ++ remaining.1, remaining.2)

/-- Strict-vector Bareiss operation generator. -/
def v15BareissAuxVector {n : ℕ} :
    List (Fin n) → ℤ → V15IntVectorMatrix n →
      List (V15IntegralRowOperation n) × V15IntVectorMatrix n
  | [], _, matrix => ([], matrix)
  | pivot :: pivots, previousPivot, matrix =>
      match v15FindIntegralPivotVector matrix pivot with
      | none => v15BareissAuxVector pivots previousPivot matrix
      | some pivotRow =>
          let swapOperation := V15IntegralRowOperation.swap pivot pivotRow
          let swapped := swapOperation.applyVector matrix
          let pivotValue := (swapped.get pivot).get pivot
          let eliminated := v15BareissEliminateBelowVector pivot previousPivot
            (List.finRange n) swapped
          let remaining := v15BareissAuxVector pivots pivotValue eliminated.2
          (swapOperation :: eliminated.1 ++ remaining.1, remaining.2)

/-- Bareiss operation list generated from a matrix. -/
def v15BareissOperations {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℤ) :
    List (V15IntegralRowOperation n) :=
  (v15BareissAuxVector (List.finRange n) 1
    (v15IntVectorMatrixOfMatrix matrix)).1

/-- Executable exact determinant certificate over the integers. -/
def V15IntegralDeterminantCertificate {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℤ) (expected : ℤ) : Bool :=
  let initial := v15IntVectorMatrixOfMatrix matrix
  let operations := v15BareissOperations matrix
  match V15IntegralRowOperation.applyAllVector? operations initial with
  | none => false
  | some reduced =>
      v15IsUpperTriangularInt reduced.toMatrix &&
        decide (((∏ i, reduced.toMatrix i i : ℤ) : ℚ) =
          V15IntegralRowOperation.multiplierAll operations * (expected : ℚ)) &&
        decide (V15IntegralRowOperation.multiplierAll operations ≠ 0)

/-- An accepted Bareiss certificate proves the claimed rational determinant. -/
theorem det_map_eq_of_v15IntegralDeterminantCertificate {n : ℕ}
    {matrix : Matrix (Fin n) (Fin n) ℤ} {expected : ℤ}
    (hcertificate : V15IntegralDeterminantCertificate matrix expected = true) :
    ((Int.castRingHom ℚ).mapMatrix matrix).det = (expected : ℚ) := by
  let operations := v15BareissOperations matrix
  let initial := v15IntVectorMatrixOfMatrix matrix
  cases hreduced :
      V15IntegralRowOperation.applyAllVector? operations initial with
  | none =>
      simp [V15IntegralDeterminantCertificate, operations, initial,
        hreduced] at hcertificate
  | some reduced =>
      have hparts :
          v15IsUpperTriangularInt reduced.toMatrix = true ∧
            decide (((∏ i, reduced.toMatrix i i : ℤ) : ℚ) =
              V15IntegralRowOperation.multiplierAll operations *
                (expected : ℚ)) = true ∧
            decide (V15IntegralRowOperation.multiplierAll operations ≠ 0) = true := by
        simpa [V15IntegralDeterminantCertificate, operations, initial, hreduced,
          Bool.and_assoc] using hcertificate
      have htriangular :=
        blockTriangular_map_of_v15IsUpperTriangularInt hparts.1
      have hdiagonal :
          (((∏ i, reduced.toMatrix i i : ℤ) : ℚ) =
            V15IntegralRowOperation.multiplierAll operations *
              (expected : ℚ)) :=
        of_decide_eq_true hparts.2.1
      have hmultiplier :
          V15IntegralRowOperation.multiplierAll operations ≠ 0 :=
        of_decide_eq_true hparts.2.2
      have hreplayMatrix :
          V15IntegralRowOperation.applyAll? operations matrix =
            some reduced.toMatrix := by
        have hcompatibility :=
          V15IntegralRowOperation.applyAllVector?_toMatrix operations initial
        rw [hreduced] at hcompatibility
        simpa [initial] using hcompatibility.symm
      have hreplay :=
        V15IntegralRowOperation.det_map_eq_of_applyAll?_eq_some hreplayMatrix
      rw [Matrix.det_of_upperTriangular htriangular] at hreplay
      have hcastDiagonal :
          ∏ i, (Int.castRingHom ℚ).mapMatrix reduced.toMatrix i i =
            (((∏ i, reduced.toMatrix i i : ℤ) : ℚ)) := by
        push_cast
        rfl
      rw [hcastDiagonal, hdiagonal] at hreplay
      exact (mul_left_cancel₀ hmultiplier hreplay).symm

end TraceEuclidean
