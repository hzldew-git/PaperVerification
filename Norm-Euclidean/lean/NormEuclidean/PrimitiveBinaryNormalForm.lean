import NormEuclidean.GramDensityTransport
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Integral norm coordinates for primitive binary Gram matrices

Over a local ring in which two is invertible, a symmetric binary matrix
whose entries generate the unit ideal has an integral basis in which it
is a unit multiple of diag(1,-d). The basis and the unit leading value
are constructed; neither is a supplied normal-form hypothesis.
-/

noncomputable section

namespace NormEuclidean.PrimitiveBinaryNormalForm

open scoped Matrix Ring

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Primitivity of the actual Gram entries. -/
def Primitive (G : Matrix (Fin 2) (Fin 2) R) : Prop :=
  Ideal.span (Set.range (fun p : Fin 2 × Fin 2 ↦ G p.1 p.2)) = ⊤

/-- A primitive matrix over a local ring has a unit entry. -/
theorem exists_unit_entry (G : Matrix (Fin 2) (Fin 2) R) (hG : Primitive G) :
    ∃ i j, IsUnit (G i j) := by
  by_contra! h
  have hm : Ideal.span (Set.range (fun p : Fin 2 × Fin 2 ↦ G p.1 p.2)) ≤
      IsLocalRing.maximalIdeal R := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact h p.1 p.2
  rw [hG] at hm
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hm)

private def matrixUnit (P : Matrix (Fin 2) (Fin 2) R) (h : IsUnit P.det) :
    (Matrix (Fin 2) (Fin 2) R)ˣ := ((Matrix.isUnit_iff_isUnit_det _).mpr h).unit

omit [IsLocalRing R] in
private theorem matrixUnit_val (P : Matrix (Fin 2) (Fin 2) R) (h : IsUnit P.det) :
    (matrixUnit P h).val = P := ((Matrix.isUnit_iff_isUnit_det _).mpr h).unit_spec

/-- One of e1, e2 or e1+e2 has unit value and extends to an integral basis. -/
theorem exists_unit_leading_basis (G : Matrix (Fin 2) (Fin 2) R) (hs : G.IsSymm)
    (hp : Primitive G) (h2 : IsUnit (2 : R)) :
    ∃ P : (Matrix (Fin 2) (Fin 2) R)ˣ,
      IsUnit ((P.val.transpose * G * P.val) 0 0) := by
  by_cases ha : IsUnit (G 0 0)
  · exact ⟨1, by simpa using ha⟩
  by_cases hc : IsUnit (G 1 1)
  · let P : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]
    have hu : IsUnit P.det := by simp [P, Matrix.det_fin_two]
    refine ⟨matrixUnit P hu, ?_⟩
    simpa [matrixUnit_val, P, Matrix.mul_apply, Fin.sum_univ_two] using hc
  have hb : IsUnit (G 0 1) := by
    obtain ⟨i, j, hij⟩ := exists_unit_entry G hp
    fin_cases i <;> fin_cases j
    · exact (ha hij).elim
    · exact hij
    · change IsUnit (G 1 0) at hij
      rwa [hs.apply 0 1] at hij
    · exact (hc hij).elim
  have hv : IsUnit (G 0 0 + 2 * G 0 1 + G 1 1) := by
    by_contra hn
    have hbad := IsLocalRing.nonunits_add
      (IsLocalRing.nonunits_add hn (show ¬ IsUnit (-G 0 0) by simpa using ha))
      (show ¬ IsUnit (-G 1 1) by simpa using hc)
    apply hbad
    convert h2.mul hb using 1
    ring
  let P : Matrix (Fin 2) (Fin 2) R := !![1, 0; 1, 1]
  have hu : IsUnit P.det := by simp [P, Matrix.det_fin_two]
  refine ⟨matrixUnit P hu, ?_⟩
  have he : (P.transpose * G * P) 0 0 = G 0 0 + 2 * G 0 1 + G 1 1 := by
    simp [P, Matrix.mul_apply, Fin.sum_univ_two, hs.apply 0 1]
    ring
  rw [matrixUnit_val, he]
  exact hv

omit [IsLocalRing R] in
private theorem norm_basis_of_unit_leading (G : Matrix (Fin 2) (Fin 2) R)
    (hs : G.IsSymm) (ha : IsUnit (G 0 0)) :
    ∃ (P : (Matrix (Fin 2) (Fin 2) R)ˣ) (a : Rˣ) (d : R),
      P.val.transpose * G * P.val = (a : R) • BinaryCongruenceDensity.gram d := by
  let a := ha.unit
  let u := (a⁻¹ : Rˣ).val
  let b := G 0 1
  let c := G 1 1
  let d := (b ^ 2 - (a : R) * c) * u ^ 2
  let P : Matrix (Fin 2) (Fin 2) R := !![1, -u * b; 0, 1]
  have hu : IsUnit P.det := by simp [P, Matrix.det_fin_two]
  have hi : (a : R) * u = 1 := a.val_inv
  have h00 : G 0 0 = (a : R) := ha.unit_spec.symm
  have h10 : G 1 0 = b := hs.apply 0 1
  refine ⟨matrixUnit P hu, a, d, ?_⟩
  rw [matrixUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P, BinaryCongruenceDensity.gram, Matrix.mul_apply, Fin.sum_univ_two, h00, h10]
  · dsimp [b]
    linear_combination -G 0 1 * hi
  · dsimp [b]
    linear_combination -G 0 1 * hi
  · dsimp [d, c, b]
    linear_combination (2 * G 0 1 ^ 2 * u - G 1 1 * ((a : R) * u + 1)) * hi

/-- Constructed integral norm form for every primitive symmetric odd binary matrix. -/
theorem exists_norm_basis (G : Matrix (Fin 2) (Fin 2) R) (hs : G.IsSymm)
    (hp : Primitive G) (h2 : IsUnit (2 : R)) :
    ∃ (P : (Matrix (Fin 2) (Fin 2) R)ˣ) (a : Rˣ) (d : R),
      P.val.transpose * G * P.val = (a : R) • BinaryCongruenceDensity.gram d := by
  obtain ⟨P, hP⟩ := exists_unit_leading_basis G hs hp h2
  have hsym : (P.val.transpose * G * P.val).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have he := congrArg (fun A ↦ A i j)
      (show (P.val.transpose * G * P.val).transpose = P.val.transpose * G * P.val by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs.eq, Matrix.mul_assoc])
    exact he
  obtain ⟨T, a, d, hT⟩ := norm_basis_of_unit_leading _ hsym hP
  refine ⟨P * T, a, d, ?_⟩
  simpa only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc] using hT

end NormEuclidean.PrimitiveBinaryNormalForm
