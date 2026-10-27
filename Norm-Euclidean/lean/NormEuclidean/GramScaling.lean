import NormEuclidean.IntegralBinaryDensity
import Mathlib.GroupTheory.Coset.Basic

/-!
# Congruence counts under nonunit Gram scaling

Scalar cancellation lowers the congruence level. All four matrix entries
lift independently; the full normalized binary count therefore acquires
the cube of the scalar-valuation factor. No oddness assumption is needed.
-/

noncomputable section

namespace NormEuclidean.GramScaling

open GramDensityTransport IsLocalRing UnramifiedBinaryDensity

section Reduction

/-- A surjective additive map has a kernel-sized fiber over every point of a subset. -/
def preimageEquiv {X Y : Type*} [AddGroup X] [AddGroup Y]
    (f : X →+ Y) (hf : Function.Surjective f) (S : Set Y) :
    {x : X // f x ∈ S} ≃ S × f.ker :=
  (Equiv.sigmaSubtypeFiberEquivSubtype f (fun _ ↦ Iff.rfl)).symm.trans
    ((Equiv.sigmaCongrRight fun y : S ↦
      AddMonoidHom.fiberEquivKerOfSurjective hf y.val).trans (Equiv.sigmaEquivProd _ _))

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The kernel of coefficientwise matrix reduction is the matrix of scalar kernels. -/
def matrixKernelEquiv (f : A →+* B) :
    (f.mapMatrix : Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) B).toAddMonoidHom.ker ≃
      (Fin 2 → Fin 2 → f.toAddMonoidHom.ker) where
  toFun M i j := ⟨M.val i j, congrFun (congrFun M.property i) j⟩
  invFun M := ⟨Matrix.of (fun i j ↦ (M i j).val), by ext i j; exact (M i j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Scalar cancellation is exactly reduction to the lower-level Gram equation. -/
theorem equation_iff (f : A →+* B) (c : A)
    (hc : ∀ x : A, c * x = 0 ↔ f x = 0)
    (G M : Matrix (Fin 2) (Fin 2) A) :
    M.transpose * (c • G) * M = c • G ↔
      (M.map f).transpose * G.map f * M.map f = G.map f := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  have hmap : (M.transpose * G * M).map f =
      (M.map f).transpose * G.map f * M.map f := by
    simp only [Matrix.map_mul, Matrix.transpose_map]
  rw [← hmap]
  constructor
  · intro h
    ext i j
    apply sub_eq_zero.mp
    change f ((M.transpose * G * M) i j) - f (G i j) = 0
    rw [← map_sub]
    apply (hc _).mp
    rw [mul_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h i) j)
  · intro h
    ext i j
    apply sub_eq_zero.mp
    change c * (M.transpose * G * M) i j - c * G i j = 0
    rw [← mul_sub]
    apply (hc _).mpr
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h i) j)

/-- The literal solution set is a product with four independent scalar lifting kernels. -/
def solutionEquiv (f : A →+* B) (hf : Function.Surjective f) (c : A)
    (hc : ∀ x : A, c * x = 0 ↔ f x = 0) (G : Matrix (Fin 2) (Fin 2) A) :
    Solutions (c • G) ≃ Solutions (G.map f) ×
      (Fin 2 → Fin 2 → f.toAddMonoidHom.ker) := by
  let F : Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) B := f.mapMatrix
  have hF : Function.Surjective F := by
    intro M
    choose x hx using fun i j ↦ hf (M i j)
    exact ⟨Matrix.of x, by ext i j; exact hx i j⟩
  let e := preimageEquiv F.toAddMonoidHom hF
    {M : Matrix (Fin 2) (Fin 2) B | M.transpose * G.map f * M = G.map f}
  exact (Equiv.subtypeEquivRight (equation_iff f c hc G)).trans
    (e.trans (Equiv.prodCongr (Equiv.refl _) (matrixKernelEquiv f)))

/-- The exact full count under scalar cancellation, before density normalization. -/
theorem solution_card [Finite A] [Finite B] (f : A →+* B)
    (hf : Function.Surjective f) (c : A) (hc : ∀ x : A, c * x = 0 ↔ f x = 0)
    (G : Matrix (Fin 2) (Fin 2) A) :
    Nat.card (Solutions (c • G)) =
      Nat.card (Solutions (G.map f)) * Nat.card f.toAddMonoidHom.ker ^ 4 := by
  rw [Nat.card_congr (solutionEquiv f hf c hc G), Nat.card_prod]
  simp only [Nat.card_fun, Nat.card_fin]
  ring

end Reduction

section DVR

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual map dropping t powers from a positive congruence level. -/
def reduction (t n : ℕ) : Level R (t + n) →+* Level R n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))

/-- A nonzero scalar of ideal valuation t cancels exactly t powers of the maximal ideal. -/
theorem scalar_cancel (s : R) (hs : s ≠ 0) (t n : ℕ)
    (hval : Ideal.span ({s} : Set R) = maximalIdeal R ^ t) (x : R) :
    s * x ∈ maximalIdeal R ^ (t + n + 1) ↔ x ∈ maximalIdeal R ^ (n + 1) := by
  have he : maximalIdeal R ^ (t + n + 1) =
      Ideal.span ({s} : Set R) * maximalIdeal R ^ (n + 1) := by
    rw [hval, ← pow_add, Nat.add_assoc]
  rw [he, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨y, hy, he⟩
    exact mul_left_cancel₀ hs he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Cancellation in the actual quotient rings, with no assumed lifting law. -/
theorem quotient_cancel (s : R) (hs : s ≠ 0) (t n : ℕ)
    (hval : Ideal.span ({s} : Set R) = maximalIdeal R ^ t) (x : Level R (t + n)) :
    Ideal.Quotient.mk _ s * x = 0 ↔ reduction R t n x = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  change _ ↔ Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) x = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact scalar_cancel R s hs t n hval x

/-- The scalar reduction kernel has exactly q^t elements. -/
theorem reduction_kernel_card [Finite (ResidueField R)] (t n : ℕ) :
    Nat.card (reduction R t n).toAddMonoidHom.ker = Nat.card (ResidueField R) ^ t := by
  let f := (reduction R t n).toAddMonoidHom
  have hf : Function.Surjective f := by
    dsimp [f, reduction]
    exact Ideal.Quotient.factor_surjective _
  have hc := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup (Level R n)) ≃+ _).toEquiv,
    level_card, level_card] at hc
  have he : Nat.card (ResidueField R) ^ (t + n + 1) =
      Nat.card (ResidueField R) ^ t * Nat.card (ResidueField R) ^ (n + 1) := by
    rw [Nat.add_assoc, pow_add]
  exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos _) (hc.trans he)

/-- Exact full binary counts after cancelling a scalar of ideal valuation t. -/
theorem level_solution_card [Finite (ResidueField R)] (s : R) (hs : s ≠ 0)
    (t n : ℕ) (hval : Ideal.span ({s} : Set R) = maximalIdeal R ^ t)
    (G : Matrix (Fin 2) (Fin 2) R) :
    Nat.card (Solutions ((s • G).map (Ideal.Quotient.mk
      (maximalIdeal R ^ (t + n + 1))))) =
      Nat.card (Solutions (G.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))))) *
        Nat.card (ResidueField R) ^ (4 * t) := by
  have he : (s • G).map (Ideal.Quotient.mk (maximalIdeal R ^ (t + n + 1))) =
      Ideal.Quotient.mk (maximalIdeal R ^ (t + n + 1)) s •
        G.map (Ideal.Quotient.mk (maximalIdeal R ^ (t + n + 1))) := by
    ext i j
    exact (Ideal.Quotient.mk (maximalIdeal R ^ (t + n + 1))).map_mul s (G i j)
  have hf : Function.Surjective (reduction R t n) := by
    exact Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (by omega : n + 1 ≤ t + n + 1))
  rw [he, solution_card (reduction R t n) hf
    _ (quotient_cancel R s hs t n hval), reduction_kernel_card]
  have hG : (G.map (Ideal.Quotient.mk (maximalIdeal R ^ (t + n + 1)))).map
      (reduction R t n) = G.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) := by
    ext i j
    rfl
  rw [hG, ← pow_mul, Nat.mul_comm t 4]

/-- The normalized count scales by q^(3t), rather than being invariant. -/
theorem level_density [Finite (ResidueField R)] (s : R) (hs : s ≠ 0) (t n : ℕ)
    (hval : Ideal.span ({s} : Set R) = maximalIdeal R ^ t)
    (G : Matrix (Fin 2) (Fin 2) R) :
    IntegralBinaryDensity.levelDensity R (s • G) (t + n) =
      (Nat.card (ResidueField R) : ℝ) ^ (3 * t) *
        IntegralBinaryDensity.levelDensity R G n := by
  unfold IntegralBinaryDensity.levelDensity GramDensityTransport.density
  rw [level_solution_card R s hs t n hval, level_card, level_card,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow]
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  let C : ℝ := Nat.card (Solutions
    (G.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))))
  change C * (Nat.card (ResidueField R) : ℝ) ^ (4 * t) /
    (2 * (Nat.card (ResidueField R) : ℝ) ^ (t + n + 1)) =
      (Nat.card (ResidueField R) : ℝ) ^ (3 * t) *
        (C / (2 * (Nat.card (ResidueField R) : ℝ) ^ (n + 1)))
  rw [show t + n + 1 = t + (n + 1) by omega, pow_add,
    show 4 * t = 3 * t + t by omega, pow_add]
  field_simp

end DVR

end NormEuclidean.GramScaling
