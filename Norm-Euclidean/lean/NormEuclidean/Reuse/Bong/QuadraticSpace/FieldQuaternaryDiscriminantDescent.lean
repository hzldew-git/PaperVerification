/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldCodimensionOneDeterminant
import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldBinaryIsotropy
import NormEuclidean.ChapterX.DiagonalDeterminant
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic

/-!
# Quaternary descent from the discriminant quadratic field

This file proves the field algebra in O'Meara 58:7 for regular diagonal
quaternary forms.  The determinant calculation first treats two orthogonal
vectors whose represented values differ by the negative discriminant.  The
quadratic field `F(sqrt d)` is then realized by
`QuadraticAlgebra F d 0`, so an isotropic extension vector splits into the
two base field vectors required by that calculation.
-/

namespace Bong

universe u
variable {F : Type u} [Field F] [CharZero F]

open QuadraticSpace

/-- Field-generic completion of a represented regular binary diagonal form
inside a regular quaternary diagonal form. -/
theorem diagonalRepresents_binary_complete_to_quaternary_field
    (source : Fin 2 → Fˣ) (target : Fin 4 → Fˣ)
    (hrep : DiagonalRepresents (fun i ↦ (source i : F))
      (fun i ↦ (target i : F))) :
    ∃ c : Fin 2 → Fˣ,
      DiagonalRepresents
        (fun i : Fin 4 ↦ ((Fin.append source c : Fin 4 → Fˣ) i : F))
        (fun i ↦ (target i : F)) := by
  let qs := QuadraticSpace.finiteDiagonal
    (fun i ↦ (source i : F)) (fun i ↦ Units.ne_zero (source i))
  let qt := QuadraticSpace.finiteDiagonal
    (fun i ↦ (target i : F)) (fun i ↦ Units.ne_zero (target i))
  have hspace : qt.Represents qs :=
    DiagonalRepresents.toQuadraticSpaceRepresents
      (fun i ↦ Units.ne_zero (source i))
      (fun i ↦ Units.ne_zero (target i)) hrep
  rcases hspace with ⟨f⟩
  have hResidualRank : Module.finrank F f.representedResidual = 2 := by
    have hsum := f.representedSum_finrank
    simp [qs, qt] at hsum
    omega
  let e : Fin 2 ≃ Fin (Module.finrank F f.representedResidual) :=
    finCongr hResidualRank.symm
  let residual := f.representedResidualSpace
  let c : Fin 2 → Fˣ := fun i ↦
    QuadraticSpace.fieldDiagonalUnits residual (e i)
  let residualDiagonal : QuadraticSpace.Isometry residual
      (QuadraticSpace.finiteDiagonal (fun i ↦ (c i : F))
        (fun i ↦ Units.ne_zero (c i))) := by
    let diagonal := residual.fieldDiagonalizationIsometry
    let reindex := QuadraticSpace.finiteDiagonalReindexIsometry
      residual.fieldDiagonalCoefficients
      residual.fieldDiagonalCoefficients_ne_zero e
    exact diagonal.trans reindex
  let sumDiagonal : QuadraticSpace.Isometry
      (qs.orthogonalSum residual)
      (QuadraticSpace.finiteDiagonal
        (Fin.append (fun i ↦ (source i : F)) (fun i ↦ (c i : F)))
        (by
          intro i
          refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
          · rw [Fin.append_left]
            exact Units.ne_zero (source j)
          · rw [Fin.append_right]
            exact Units.ne_zero (c j))) :=
    ((QuadraticSpace.Isometry.refl qs).fieldOrthogonalSum residualDiagonal).trans
      (QuadraticSpace.fieldFiniteDiagonalOrthogonalSumIsometry
        (fun i ↦ (source i : F)) (fun i ↦ (c i : F))
        (fun i ↦ Units.ne_zero (source i))
        (fun i ↦ Units.ne_zero (c i)))
  let fullRep : QuadraticSpace.Representation
      (QuadraticSpace.finiteDiagonal
        (Fin.append (fun i ↦ (source i : F)) (fun i ↦ (c i : F)))
        (by
          intro i
          refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
          · rw [Fin.append_left]
            exact Units.ne_zero (source j)
          · rw [Fin.append_right]
            exact Units.ne_zero (c j))) qt :=
    f.representedSumIsometry.toRepresentation.trans
      sumDiagonal.symm.toRepresentation
  refine ⟨c, ⟨fullRep.toLinearMap, fullRep.injective, ?_⟩⟩
  intro z
  have hmap := fullRep.map_quadratic z
  rw [QuadraticSpace.finiteDiagonal_quadratic_apply,
    QuadraticSpace.finiteDiagonal_quadratic_apply] at hmap
  exact hmap

def fieldQuaternaryDiscriminantUnit (a : Fin 4 → Fˣ) : Fˣ :=
  ∏ i, a i

def fieldQuaternaryDescentBinary
    (a : Fin 4 → Fˣ) (e : Fˣ) : Fin 2 → Fˣ :=
  ![-(fieldQuaternaryDiscriminantUnit a * e), e]

/-- The distinguished square root of the discriminant in the quadratic
algebra `F(sqrt d)`. -/
def fieldQuaternaryDiscriminantSqrt
    (a : Fin 4 → Fˣ) : QuadraticAlgebra F
      (fieldQuaternaryDiscriminantUnit a : F) 0 :=
  ⟨0, 1⟩

omit [CharZero F] in
@[simp]
theorem fieldQuaternaryDiscriminantSqrt_sq (a : Fin 4 → Fˣ) :
    fieldQuaternaryDiscriminantSqrt a ^ 2 =
      QuadraticAlgebra.C (fieldQuaternaryDiscriminantUnit a : F) := by
  ext <;> simp [fieldQuaternaryDiscriminantSqrt, pow_two]

omit [CharZero F] in
/-- Every element of the discriminant quadratic algebra has its literal
`x + y sqrt(d)` decomposition. -/
theorem fieldQuaternaryDiscriminantExtension_decomposition
    (a : Fin 4 → Fˣ)
    (z : QuadraticAlgebra F (fieldQuaternaryDiscriminantUnit a : F) 0) :
    z = QuadraticAlgebra.C z.re +
      QuadraticAlgebra.C z.im * fieldQuaternaryDiscriminantSqrt a := by
  ext <;> simp [fieldQuaternaryDiscriminantSqrt]

private theorem fieldQuaternary_isotropic_of_descentBinary_representation
    (a : Fin 4 → Fˣ) (e : Fˣ)
    (hrep : DiagonalRepresents
      (fun i ↦ (fieldQuaternaryDescentBinary a e i : F))
      (fun i ↦ (a i : F))) :
    DiagonalIsotropic (fun i ↦ (a i : F)) := by
  rcases diagonalRepresents_binary_complete_to_quaternary_field
      (fieldQuaternaryDescentBinary a e) a hrep with ⟨c, hfull⟩
  rcases DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank hfull with
    ⟨p, hp⟩
  have hAppend0 :
      (Fin.append (fieldQuaternaryDescentBinary a e) c : Fin 4 → Fˣ) 0 =
        fieldQuaternaryDescentBinary a e 0 := rfl
  have hAppend1 :
      (Fin.append (fieldQuaternaryDescentBinary a e) c : Fin 4 → Fˣ) 1 =
        fieldQuaternaryDescentBinary a e 1 := rfl
  have hAppend2 :
      (Fin.append (fieldQuaternaryDescentBinary a e) c : Fin 4 → Fˣ) 2 =
        c 0 := by rfl
  have hAppend3 :
      (Fin.append (fieldQuaternaryDescentBinary a e) c : Fin 4 → Fˣ) 3 =
        c 1 := by rfl
  have hp' :
      (-((fieldQuaternaryDiscriminantUnit a : F) * (e : F))) * (e : F) *
          ((c 0 : F) * (c 1 : F)) =
        (fieldQuaternaryDiscriminantUnit a : F) * (p : F) ^ 2 := by
    simp only [Fin.prod_univ_four, hAppend0, hAppend1, hAppend2,
      hAppend3] at hp
    simpa [fieldQuaternaryDescentBinary,
      fieldQuaternaryDiscriminantUnit, Fin.prod_univ_four,
      mul_assoc] using hp
  have hcSquare : IsSquare (-((c 0 : F) * (c 1 : F))) := by
    refine ⟨(p : F) / (e : F), ?_⟩
    have hp'' :
        -((e : F) ^ 2 * (c 0 : F) * (c 1 : F)) = (p : F) ^ 2 := by
      apply (mul_left_cancel₀ (Units.ne_zero
        (fieldQuaternaryDiscriminantUnit a)))
      calc
        (fieldQuaternaryDiscriminantUnit a : F) *
              (-((e : F) ^ 2 * (c 0 : F) * (c 1 : F))) =
            (-((fieldQuaternaryDiscriminantUnit a : F) * (e : F))) *
              (e : F) * ((c 0 : F) * (c 1 : F)) := by ring
        _ = (fieldQuaternaryDiscriminantUnit a : F) * (p : F) ^ 2 := hp'
    calc
      -((c 0 : F) * (c 1 : F)) =
          (-((e : F) ^ 2 * (c 0 : F) * (c 1 : F))) / (e : F) ^ 2 := by
            field_simp [Units.ne_zero e]
      _ = (p : F) ^ 2 / (e : F) ^ 2 := by rw [hp'']
      _ = ((p : F) / (e : F)) * ((p : F) / (e : F)) := by
            field_simp [Units.ne_zero e]
  have hcIsotropic : DiagonalIsotropic (fun i ↦ (c i : F)) :=
    (fieldBinary_isotropic_iff_isSquare_neg_product
      (fun i ↦ (c i : F)) (fun i ↦ Units.ne_zero (c i))).2 hcSquare
  rcases hcIsotropic with ⟨z, hz, hquadratic⟩
  let w : Fin 4 → F := ![0, 0, z 0, z 1]
  have hw : w ≠ 0 := by
    intro hwzero
    apply hz
    funext i
    fin_cases i
    · exact congrFun hwzero 2
    · exact congrFun hwzero 3
  have hwquadratic :
      diagonalQuadratic
        (fun i : Fin 4 ↦
          ((Fin.append (fieldQuaternaryDescentBinary a e) c :
            Fin 4 → Fˣ) i : F)) w = 0 := by
    simpa [diagonalQuadratic, w, Fin.sum_univ_four, hAppend2, hAppend3,
      Fin.sum_univ_two] using hquadratic
  exact DiagonalRepresents.isotropic_of hfull ⟨w, hw, hwquadratic⟩

/-- The coordinate descent at the heart of O'Meara 58:7.  Two orthogonal
vectors whose values differ by the negative discriminant already force a
regular quaternary diagonal form to be isotropic. -/
theorem fieldQuaternary_isotropic_of_descent_pair
    (a : Fin 4 → Fˣ) (x y : Fin 4 → F)
    (hnonzero : x ≠ 0 ∨ y ≠ 0)
    (hquadratic :
      diagonalQuadratic (fun i ↦ (a i : F)) x =
        -(fieldQuaternaryDiscriminantUnit a : F) *
          diagonalQuadratic (fun i ↦ (a i : F)) y)
    (horthogonal : ∑ i, (a i : F) * x i * y i = 0) :
    DiagonalIsotropic (fun i ↦ (a i : F)) := by
  by_cases hyquadratic :
      diagonalQuadratic (fun i ↦ (a i : F)) y = 0
  · by_cases hy : y = 0
    · have hx : x ≠ 0 := hnonzero.resolve_right (fun hyne ↦ hyne hy)
      refine ⟨x, hx, ?_⟩
      rw [hquadratic, hyquadratic, mul_zero]
    · exact ⟨y, hy, hyquadratic⟩
  · have hxquadratic :
        diagonalQuadratic (fun i ↦ (a i : F)) x ≠ 0 := by
      rw [hquadratic]
      exact mul_ne_zero
        (neg_ne_zero.mpr (Units.ne_zero (fieldQuaternaryDiscriminantUnit a)))
        hyquadratic
    let e : Fˣ := Units.mk0
      (diagonalQuadratic (fun i ↦ (a i : F)) y) hyquadratic
    let f : (Fin 2 → F) →ₗ[F] (Fin 4 → F) := {
      toFun z := fun i ↦ z 0 * x i + z 1 * y i
      map_add' z w := by
        funext i
        simp only [Pi.add_apply]
        ring
      map_smul' r z := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    have hfzero (z : Fin 2 → F) (hz : f z = 0) : z = 0 := by
      have hpairX : ∑ i, (a i : F) * f z i * x i = 0 := by
        rw [hz]
        simp
      have hpairY : ∑ i, (a i : F) * f z i * y i = 0 := by
        rw [hz]
        simp
      have hz0mul :
          z 0 * diagonalQuadratic (fun i ↦ (a i : F)) x = 0 := by
        calc
          z 0 * diagonalQuadratic (fun i ↦ (a i : F)) x =
              z 0 * diagonalQuadratic (fun i ↦ (a i : F)) x +
                z 1 * (∑ i, (a i : F) * x i * y i) := by
                  rw [horthogonal]
                  ring
          _ = ∑ i, (a i : F) * f z i * x i := by
            simp [f, diagonalQuadratic, Fin.sum_univ_four]
            ring
          _ = 0 := hpairX
      have hz1mul :
          z 1 * diagonalQuadratic (fun i ↦ (a i : F)) y = 0 := by
        calc
          z 1 * diagonalQuadratic (fun i ↦ (a i : F)) y =
              z 0 * (∑ i, (a i : F) * x i * y i) +
                z 1 * diagonalQuadratic (fun i ↦ (a i : F)) y := by
                  rw [horthogonal]
                  ring
          _ = ∑ i, (a i : F) * f z i * y i := by
            simp [f, diagonalQuadratic, Fin.sum_univ_four]
            ring
          _ = 0 := hpairY
      have hz0 : z 0 = 0 := (mul_eq_zero.mp hz0mul).resolve_right hxquadratic
      have hz1 : z 1 = 0 := (mul_eq_zero.mp hz1mul).resolve_right hyquadratic
      funext i
      fin_cases i
      · exact hz0
      · exact hz1
    have hfinjective : Function.Injective f := by
      intro z w hzw
      have hdiff : f (z - w) = 0 := by
        rw [map_sub, hzw, sub_self]
      exact sub_eq_zero.mp (hfzero (z - w) hdiff)
    have hfrep : DiagonalRepresents
        (fun i ↦ (fieldQuaternaryDescentBinary a e i : F))
        (fun i ↦ (a i : F)) := by
      refine ⟨f, hfinjective, ?_⟩
      intro z
      calc
        diagonalQuadratic (fun i ↦ (a i : F)) (f z) =
            (z 0) ^ 2 * diagonalQuadratic (fun i ↦ (a i : F)) x +
              (z 1) ^ 2 * diagonalQuadratic (fun i ↦ (a i : F)) y +
                2 * z 0 * z 1 *
                  (∑ i, (a i : F) * x i * y i) := by
            simp [f, diagonalQuadratic, Fin.sum_univ_four]
            ring
        _ = diagonalQuadratic
              (fun i ↦ (fieldQuaternaryDescentBinary a e i : F)) z := by
            rw [hquadratic, horthogonal]
            simp [e, fieldQuaternaryDescentBinary, diagonalQuadratic,
              Fin.sum_univ_two]
            ring
    exact fieldQuaternary_isotropic_of_descentBinary_representation a e hfrep

/-- The discriminant quadratic algebra is a field when the discriminant is
nonsquare. -/
@[implicit_reducible]
noncomputable def fieldQuaternaryDiscriminantExtensionField
    (a : Fin 4 → Fˣ)
    (hnotSquare : ¬IsSquare (fieldQuaternaryDiscriminantUnit a : F)) :
    Field (QuadraticAlgebra F
      (fieldQuaternaryDiscriminantUnit a : F) 0) := by
  letI : Fact (∀ r : F,
      r ^ 2 ≠ (fieldQuaternaryDiscriminantUnit a : F) + 0 * r) := ⟨by
    intro r hr
    apply hnotSquare
    rw [isSquare_iff_exists_sq]
    refine ⟨r, ?_⟩
    simpa using hr.symm⟩
  infer_instance

/-- The scalar extension of a quaternary diagonal form to its discriminant
quadratic field has a nonzero isotropic vector. -/
noncomputable def FieldQuaternaryDiscriminantExtensionIsotropic
    (a : Fin 4 → Fˣ)
    (hnotSquare : ¬IsSquare (fieldQuaternaryDiscriminantUnit a : F)) : Prop :=
  @DiagonalIsotropic
    (QuadraticAlgebra F (fieldQuaternaryDiscriminantUnit a : F) 0)
    (fieldQuaternaryDiscriminantExtensionField a hnotSquare) 4
    (fun i ↦ QuadraticAlgebra.C (a i : F))

/-- O'Meara 58:7 in diagonal coordinates: for nonsquare discriminant, an
isotropic vector after adjoining its square root descends to the base field. -/
theorem fieldQuaternary_isotropic_of_discriminantExtension
    (a : Fin 4 → Fˣ)
    (hnotSquare : ¬IsSquare (fieldQuaternaryDiscriminantUnit a : F))
    (hiso : FieldQuaternaryDiscriminantExtensionIsotropic a hnotSquare) :
    DiagonalIsotropic (fun i ↦ (a i : F)) := by
  let d : F := (fieldQuaternaryDiscriminantUnit a : F)
  change ∃ z : Fin 4 → QuadraticAlgebra F
      (fieldQuaternaryDiscriminantUnit a : F) 0,
      z ≠ 0 ∧
        ∑ i, QuadraticAlgebra.C (a i : F) * (z i) ^ 2 = 0 at hiso
  rcases hiso with ⟨z, hz, hquadraticExtension⟩
  let x : Fin 4 → F := fun i ↦ (z i).re
  let y : Fin 4 → F := fun i ↦ (z i).im
  have hnonzero : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    funext i
    apply QuadraticAlgebra.ext
    · simpa [x] using congrFun h.1 i
    · simpa [y] using congrFun h.2 i
  have hre := congrArg QuadraticAlgebra.re hquadraticExtension
  have him := congrArg QuadraticAlgebra.im hquadraticExtension
  have hsum :
      diagonalQuadratic (fun i ↦ (a i : F)) x +
        d * diagonalQuadratic (fun i ↦ (a i : F)) y = 0 := by
    simp [x, y, d, diagonalQuadratic, pow_two,
      Fin.sum_univ_four] at hre ⊢
    ring_nf at hre ⊢
    exact hre
  have horthogonal : ∑ i, (a i : F) * x i * y i = 0 := by
    simp [x, y, pow_two, Fin.sum_univ_four] at him ⊢
    linear_combination (1 / 2) * him
  apply fieldQuaternary_isotropic_of_descent_pair a x y hnonzero
  · dsimp only [d] at hsum
    linear_combination hsum
  · exact horthogonal

omit [CharZero F] in
/-- Isotropy over the base field remains isotropy after extension to the
discriminant quadratic field. -/
theorem fieldQuaternary_discriminantExtension_isotropic_of_isotropic
    (a : Fin 4 → Fˣ)
    (hnotSquare : ¬IsSquare (fieldQuaternaryDiscriminantUnit a : F))
    (hiso : DiagonalIsotropic (fun i ↦ (a i : F))) :
    FieldQuaternaryDiscriminantExtensionIsotropic a hnotSquare := by
  rcases hiso with ⟨x, hx, hquadratic⟩
  change ∃ z : Fin 4 → QuadraticAlgebra F
      (fieldQuaternaryDiscriminantUnit a : F) 0,
      z ≠ 0 ∧
        ∑ i, QuadraticAlgebra.C (a i : F) * (z i) ^ 2 = 0
  refine ⟨fun i ↦ QuadraticAlgebra.C (x i), ?_, ?_⟩
  · intro hzero
    apply hx
    funext i
    have hi := congrFun hzero i
    simpa using congrArg QuadraticAlgebra.re hi
  · have hmap := congrArg
      (QuadraticAlgebra.C (a := (fieldQuaternaryDiscriminantUnit a : F))
        (b := 0)) hquadratic
    simpa [diagonalQuadratic, map_sum, map_mul, map_pow] using hmap

/-- Nonsquare-discriminant coordinate form of O'Meara 58:7. -/
theorem fieldQuaternary_discriminantExtension_isotropic_iff
    (a : Fin 4 → Fˣ)
    (hnotSquare : ¬IsSquare (fieldQuaternaryDiscriminantUnit a : F)) :
    FieldQuaternaryDiscriminantExtensionIsotropic a hnotSquare ↔
      DiagonalIsotropic (fun i ↦ (a i : F)) :=
  ⟨fieldQuaternary_isotropic_of_discriminantExtension a hnotSquare,
    fieldQuaternary_discriminantExtension_isotropic_of_isotropic a hnotSquare⟩

end Bong
