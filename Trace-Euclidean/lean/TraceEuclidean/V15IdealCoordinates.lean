import TraceEuclidean.PseudoBasisDeterminant
import TraceEuclidean.V15BinaryCriterion

/-!
The first intrinsic step from an arbitrary nonzero fractional ideal in a
quadratic number field to two integer coordinates. The construction does not
assume that the ideal is principal or free over the ring of integers.
-/

namespace TraceEuclidean

open Module
open scoped NumberField nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- A nonzero fractional ideal in a degree-two number field has exactly two
integer basis indices. -/
def v15IdealIndexEquiv
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) :
    Fin 2 ≃ Module.Free.ChooseBasisIndex ℤ I := by
  classical
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex]
  let U : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := Units.mk0 I hI
  calc
    2 = Module.finrank ℚ F := hdegree.symm
    _ = Module.finrank ℤ (𝓞 F) := (NumberField.RingOfIntegers.rank F).symm
    _ = Module.finrank ℤ I := by
      change Module.finrank ℤ (𝓞 F) = Module.finrank ℤ (U :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      exact (NumberField.fractionalIdeal_rank F U).symm

/-- An explicit `ℤ²`-indexed basis of any nonzero quadratic fractional ideal. -/
def v15IdealZBasis
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) : Basis (Fin 2) ℤ I :=
  (NumberField.fractionalIdealBasis F I).reindex
    (v15IdealIndexEquiv I hI hdegree).symm

/-- The same two ideal vectors, now viewed as a rational basis of the field. -/
def v15IdealFieldBasis
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) : Basis (Fin 2) ℚ F := by
  letI : IsLocalizedModule ℤ⁰
      ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) := by
    rw [← Units.val_mk0 hI]
    infer_instance
  exact (v15IdealZBasis I hI hdegree).ofIsLocalizedModule ℚ ℤ⁰
    ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ)

/-- The arbitrary ideal is additively equivalent to `ℤ²`; this gives the
integer coordinates used by the Gram argument. -/
def v15IdealIntegerCoordinates
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) : I ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (v15IdealZBasis I hI hdegree).equivFun

/-- The same basis yields rational coordinates on the ambient field. -/
def v15IdealRationalCoordinates
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) : F ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (v15IdealFieldBasis I hI hdegree).equivFun

/-- The field coordinates of an ideal element are precisely its integer
coordinates, viewed in `ℚ`. This is the semantic bridge for all fractional
ideals, including nonprincipal ones. -/
theorem v15_ideal_coordinates_compatible
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2)
    (x : I) (i : Fin 2) :
    v15IdealRationalCoordinates I hI hdegree (x : F) i =
      ((v15IdealIntegerCoordinates I hI hdegree x i : ℤ) : ℚ) := by
  letI : IsLocalizedModule ℤ⁰
      ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) := by
    rw [← Units.val_mk0 hI]
    infer_instance
  change ((v15IdealZBasis I hI hdegree).ofIsLocalizedModule ℚ ℤ⁰
      ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ)).repr (x : F) i =
    (((v15IdealZBasis I hI hdegree).repr x i : ℤ) : ℚ)
  exact (v15IdealZBasis I hI hdegree).ofIsLocalizedModule_repr_apply
    ℚ ℤ⁰ ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) x i

theorem v15_ideal_field_basis_apply
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (i : Fin 2) :
    v15IdealFieldBasis I hI hdegree i =
      ((v15IdealZBasis I hI hdegree i : I) : F) := by
  letI : IsLocalizedModule ℤ⁰
      ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) := by
    rw [← Units.val_mk0 hI]
    infer_instance
  exact (v15IdealZBasis I hI hdegree).ofIsLocalizedModule_apply
    ℚ ℤ⁰ ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) i

theorem v15_ideal_field_basis_decomposition
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (x : F) :
    x = (v15IdealRationalCoordinates I hI hdegree x 0) •
          v15IdealFieldBasis I hI hdegree 0 +
        (v15IdealRationalCoordinates I hI hdegree x 1) •
          v15IdealFieldBasis I hI hdegree 1 := by
  let B := v15IdealFieldBasis I hI hdegree
  have hs := (B.sum_repr x).symm
  simpa only [Fin.sum_univ_two, Basis.equivFun_apply,
    v15IdealRationalCoordinates, B] using hs

/-- The three rational trace Gram entries attached to an arbitrary ideal
basis and a rank-one quadratic coefficient. -/
def v15IdealTraceGram
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (α : F) : ℚ × ℚ × ℚ :=
  let β₀ := v15IdealFieldBasis I hI hdegree 0
  let β₁ := v15IdealFieldBasis I hI hdegree 1
  (Algebra.trace ℚ F (α * β₀ ^ 2),
    Algebra.trace ℚ F (α * β₀ * β₁),
    Algebra.trace ℚ F (α * β₁ ^ 2))

/-- If the rank-one lattice has integral cross-products, all three trace
Gram entries are integers, even when the underlying ideal is nonprincipal. -/
theorem v15_ideal_trace_gram_integral
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (α : F)
    (hclassic : ∀ x y : I,
      IsIntegral ℤ (α * (x : F) * (y : F))) :
    ∃ A B C : ℤ,
      v15IdealTraceGram I hI hdegree α =
        ((A : ℚ), (B : ℚ), (C : ℚ)) := by
  let β₀ : I := v15IdealZBasis I hI hdegree 0
  let β₁ : I := v15IdealZBasis I hI hdegree 1
  have hβ₀ := v15_ideal_field_basis_apply I hI hdegree 0
  have hβ₁ := v15_ideal_field_basis_apply I hI hdegree 1
  have hA : IsIntegral ℤ
      (Algebra.trace ℚ F
        (α * (v15IdealFieldBasis I hI hdegree 0) ^ 2)) := by
    apply Algebra.isIntegral_trace
    rw [hβ₀]
    convert hclassic β₀ β₀ using 1 <;> ring
  have hB : IsIntegral ℤ
      (Algebra.trace ℚ F
        (α * v15IdealFieldBasis I hI hdegree 0 *
          v15IdealFieldBasis I hI hdegree 1)) := by
    apply Algebra.isIntegral_trace
    rw [hβ₀, hβ₁]
    exact hclassic β₀ β₁
  have hC : IsIntegral ℤ
      (Algebra.trace ℚ F
        (α * (v15IdealFieldBasis I hI hdegree 1) ^ 2)) := by
    apply Algebra.isIntegral_trace
    rw [hβ₁]
    convert hclassic β₁ β₁ using 1 <;> ring
  obtain ⟨A, hA⟩ := IsIntegrallyClosed.isIntegral_iff.mp hA
  obtain ⟨B, hB⟩ := IsIntegrallyClosed.isIntegral_iff.mp hB
  obtain ⟨C, hC⟩ := IsIntegrallyClosed.isIntegral_iff.mp hC
  exact ⟨A, B, C, by
    dsimp [v15IdealTraceGram]
    exact Prod.ext hA.symm (Prod.ext hB.symm hC.symm)⟩

/-- In rank one, value integrality already gives the cross-product
integrality needed for the actual ideal Gram matrix. -/
theorem v15_ideal_classic_of_integral
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hintegral : ∀ x : I, IsIntegral ℤ (α * (x : F) ^ 2)) :
    ∀ x y : I, IsIntegral ℤ (α * (x : F) * (y : F)) := by
  intro x y
  have hsq : (α * (x : F) * (y : F)) ^ 2 =
      (α * (x : F) ^ 2) * (α * (y : F) ^ 2) := by ring
  exact IsIntegral.of_pow (by norm_num : 0 < (2 : ℕ))
    (hsq ▸ (hintegral x).mul (hintegral y))

theorem v15_ideal_trace_gram_integral_of_values
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (α : F)
    (hintegral : ∀ x : I, IsIntegral ℤ (α * (x : F) ^ 2)) :
    ∃ A B C : ℤ,
      v15IdealTraceGram I hI hdegree α =
        ((A : ℚ), (B : ℚ), (C : ℚ)) :=
  v15_ideal_trace_gram_integral I hI hdegree α
    (v15_ideal_classic_of_integral I α hintegral)

/-- The trace quadratic form of every rank-one fractional-ideal presentation
is the binary Gram polynomial in its two rational field coordinates. -/
theorem v15_ideal_trace_gram_formula
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (α x : F) :
    let u := v15IdealRationalCoordinates I hI hdegree x 0
    let v := v15IdealRationalCoordinates I hI hdegree x 1
    let G := v15IdealTraceGram I hI hdegree α
    Algebra.trace ℚ F (α * x ^ 2) =
      G.1 * u ^ 2 + 2 * G.2.1 * u * v + G.2.2 * v ^ 2 := by
  dsimp only
  let β₀ := v15IdealFieldBasis I hI hdegree 0
  let β₁ := v15IdealFieldBasis I hI hdegree 1
  let u := v15IdealRationalCoordinates I hI hdegree x 0
  let v := v15IdealRationalCoordinates I hI hdegree x 1
  change Algebra.trace ℚ F (α * x ^ 2) =
    Algebra.trace ℚ F (α * β₀ ^ 2) * u ^ 2 +
      2 * Algebra.trace ℚ F (α * β₀ * β₁) * u * v +
        Algebra.trace ℚ F (α * β₁ ^ 2) * v ^ 2
  have hx : x = u • β₀ + v • β₁ :=
    v15_ideal_field_basis_decomposition I hI hdegree x
  rw [hx]
  have hsq :
      α * (u • β₀ + v • β₁) ^ 2 =
        u ^ 2 • (α * β₀ ^ 2) +
          (2 * u * v) • (α * β₀ * β₁) +
            v ^ 2 • (α * β₁ ^ 2) := by
    simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat]
    ring
  rw [hsq]
  simp only [map_add, map_smul]
  ring

/-- Exact displacement-cost correspondence for any nonzero fractional ideal.
This is independent of Gauss reduction and of principality. -/
theorem v15_ideal_trace_cost_eq_binary_cost
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (α x : F) (y : I)
    {a b c : ℕ}
    (hGram : v15IdealTraceGram I hI hdegree α =
      ((a : ℚ), (b : ℚ), (c : ℚ))) :
    Algebra.trace ℚ F (α * (x - (y : F)) ^ 2) =
      v15GramCostRat a b c
        (v15IdealRationalCoordinates I hI hdegree x 0,
          v15IdealRationalCoordinates I hI hdegree x 1)
        (v15IdealIntegerCoordinates I hI hdegree y 0,
          v15IdealIntegerCoordinates I hI hdegree y 1) := by
  let C := v15IdealRationalCoordinates I hI hdegree
  let Z := v15IdealIntegerCoordinates I hI hdegree
  have hcoord (i : Fin 2) :
      C (x - (y : F)) i = C x i - (Z y i : ℚ) := by
    have hy := v15_ideal_coordinates_compatible I hI hdegree y i
    change C (y : F) i = (Z y i : ℚ) at hy
    rw [map_sub, Pi.sub_apply, hy]
  have hformula := v15_ideal_trace_gram_formula I hI hdegree α (x - (y : F))
  dsimp only at hformula
  rw [hcoord 0, hcoord 1, hGram] at hformula
  simpa only [v15GramCostRat, C, Z] using hformula

/-- Rank-one trace Euclideanity for an actual fractional-ideal presentation. -/
def V15IdealTraceEuclidean
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F) : Prop :=
  ∀ x : F, ∃ y : I,
    Algebra.trace ℚ F (α * (x - (y : F)) ^ 2) < 2

private def v15PairToFin {R : Type*} (x : R × R) : Fin 2 → R :=
  Fin.cases x.1 (fun _ ↦ x.2)

@[simp] private theorem v15PairToFin_zero {R : Type*} (x : R × R) :
    v15PairToFin x 0 = x.1 := rfl

@[simp] private theorem v15PairToFin_one {R : Type*} (x : R × R) :
    v15PairToFin x 1 = x.2 := rfl

/-- For any actual degree-two fractional ideal, a specified integral Gram
triple gives an equivalence between the paper's trace condition and the
rational-coordinate binary condition. No principal-ideal assumption occurs. -/
theorem v15_ideal_trace_euclidean_iff_binary
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (α : F)
    {a b c : ℕ}
    (hGram : v15IdealTraceGram I hI hdegree α =
      ((a : ℚ), (b : ℚ), (c : ℚ))) :
    V15IdealTraceEuclidean I α ↔ V15BinaryTraceEuclidean a b c := by
  let C := v15IdealRationalCoordinates I hI hdegree
  let Z := v15IdealIntegerCoordinates I hI hdegree
  constructor
  · intro h x
    let w : F := C.symm (v15PairToFin x)
    obtain ⟨y, hy⟩ := h w
    refine ⟨(Z y 0, Z y 1), ?_⟩
    rw [v15_ideal_trace_cost_eq_binary_cost I hI hdegree α w y hGram] at hy
    have h0 : C w 0 = x.1 := by simp [w, C]
    have h1 : C w 1 = x.2 := by simp [w, C]
    change v15GramCostRat a b c (C w 0, C w 1) (Z y 0, Z y 1) < 2 at hy
    simpa only [h0, h1] using hy
  · intro h x
    let p : PlanePoint ℚ := (C x 0, C x 1)
    obtain ⟨z, hz⟩ := h p
    let y : I := Z.symm (v15PairToFin z)
    refine ⟨y, ?_⟩
    rw [v15_ideal_trace_cost_eq_binary_cost I hI hdegree α x y hGram]
    have h0 : Z y 0 = z.1 := by simp [y, Z]
    have h1 : Z y 1 = z.2 := by simp [y, Z]
    change v15GramCostRat a b c (C x 0, C x 1) (Z y 0, Z y 1) < 2
    simpa only [h0, h1, p] using hz

end

end TraceEuclidean
