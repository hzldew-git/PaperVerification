import TraceEuclidean.V15IdealGaussBridge
import TraceEuclidean.V15BinaryCriterion

/-!
Coordinates and trace Gram data for an arbitrary selected integer basis of
one nonzero fractional ideal. This lets the Gauss-reduced basis replace the
initial arbitrary basis without changing the underlying ideal lattice.
-/

namespace TraceEuclidean

open Module
open scoped NumberField nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

def v15IdealFieldBasisOf
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) : Basis (Fin 2) ℚ F := by
  letI : IsLocalizedModule ℤ⁰
      ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) := by
    rw [← Units.val_mk0 hI]
    infer_instance
  exact B.ofIsLocalizedModule ℚ ℤ⁰
    ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ)

theorem v15_ideal_field_basis_of_apply
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) (i : Fin 2) :
    v15IdealFieldBasisOf I hI B i = ((B i : I.coeToSubmodule) : F) := by
  letI : IsLocalizedModule ℤ⁰
      ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) := by
    rw [← Units.val_mk0 hI]
    infer_instance
  exact B.ofIsLocalizedModule_apply ℚ ℤ⁰
    ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) i

def v15IdealIntegerCoordinatesOf
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) :
    I.coeToSubmodule ≃ₗ[ℤ] (Fin 2 → ℤ) := B.equivFun

def v15IdealRationalCoordinatesOf
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) :
    F ≃ₗ[ℚ] (Fin 2 → ℚ) := (v15IdealFieldBasisOf I hI B).equivFun

theorem v15_ideal_coordinates_of_compatible
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule)
    (x : I.coeToSubmodule) (i : Fin 2) :
    v15IdealRationalCoordinatesOf I hI B (x : F) i =
      ((v15IdealIntegerCoordinatesOf I B x i : ℤ) : ℚ) := by
  letI : IsLocalizedModule ℤ⁰
      ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) := by
    rw [← Units.val_mk0 hI]
    infer_instance
  change (B.ofIsLocalizedModule ℚ ℤ⁰
      ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ)).repr (x : F) i =
    ((B.repr x i : ℤ) : ℚ)
  exact B.ofIsLocalizedModule_repr_apply ℚ ℤ⁰
    ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) x i

theorem v15_ideal_field_basis_of_decomposition
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) (x : F) :
    x = (v15IdealRationalCoordinatesOf I hI B x 0) •
          v15IdealFieldBasisOf I hI B 0 +
        (v15IdealRationalCoordinatesOf I hI B x 1) •
          v15IdealFieldBasisOf I hI B 1 := by
  let C := v15IdealFieldBasisOf I hI B
  have hs := (C.sum_repr x).symm
  simpa only [Fin.sum_univ_two, Basis.equivFun_apply,
    v15IdealRationalCoordinatesOf, C] using hs

def v15IdealTraceGramOf
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) (α : F) : ℚ × ℚ × ℚ :=
  let β₀ := v15IdealFieldBasisOf I hI B 0
  let β₁ := v15IdealFieldBasisOf I hI B 1
  (Algebra.trace ℚ F (α * β₀ ^ 2),
    Algebra.trace ℚ F (α * β₀ * β₁),
    Algebra.trace ℚ F (α * β₁ ^ 2))

theorem v15_ideal_trace_gram_of_formula
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) (α x : F) :
    let u := v15IdealRationalCoordinatesOf I hI B x 0
    let v := v15IdealRationalCoordinatesOf I hI B x 1
    let G := v15IdealTraceGramOf I hI B α
    Algebra.trace ℚ F (α * x ^ 2) =
      G.1 * u ^ 2 + 2 * G.2.1 * u * v + G.2.2 * v ^ 2 := by
  dsimp only
  let β₀ := v15IdealFieldBasisOf I hI B 0
  let β₁ := v15IdealFieldBasisOf I hI B 1
  let u := v15IdealRationalCoordinatesOf I hI B x 0
  let v := v15IdealRationalCoordinatesOf I hI B x 1
  change Algebra.trace ℚ F (α * x ^ 2) =
    Algebra.trace ℚ F (α * β₀ ^ 2) * u ^ 2 +
      2 * Algebra.trace ℚ F (α * β₀ * β₁) * u * v +
        Algebra.trace ℚ F (α * β₁ ^ 2) * v ^ 2
  have hx : x = u • β₀ + v • β₁ :=
    v15_ideal_field_basis_of_decomposition I hI B x
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

theorem v15_ideal_trace_cost_of_eq_binary_cost
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule)
    (α x : F) (y : I.coeToSubmodule)
    {a b c : ℕ}
    (hGram : v15IdealTraceGramOf I hI B α =
      ((a : ℚ), (b : ℚ), (c : ℚ))) :
    Algebra.trace ℚ F (α * (x - (y : F)) ^ 2) =
      v15GramCostRat a b c
        (v15IdealRationalCoordinatesOf I hI B x 0,
          v15IdealRationalCoordinatesOf I hI B x 1)
        (v15IdealIntegerCoordinatesOf I B y 0,
          v15IdealIntegerCoordinatesOf I B y 1) := by
  let C := v15IdealRationalCoordinatesOf I hI B
  let Z := v15IdealIntegerCoordinatesOf I B
  have hcoord (i : Fin 2) :
      C (x - (y : F)) i = C x i - (Z y i : ℚ) := by
    have hy := v15_ideal_coordinates_of_compatible I hI B y i
    change C (y : F) i = (Z y i : ℚ) at hy
    rw [map_sub, Pi.sub_apply, hy]
  have hformula := v15_ideal_trace_gram_of_formula I hI B α (x - (y : F))
  dsimp only at hformula
  rw [hcoord 0, hcoord 1, hGram] at hformula
  simpa only [v15GramCostRat, C, Z] using hformula

private def v15PairToFinOf {R : Type*} (x : R × R) : Fin 2 → R :=
  Fin.cases x.1 (fun _ ↦ x.2)

@[simp] private theorem v15PairToFinOf_zero {R : Type*} (x : R × R) :
    v15PairToFinOf x 0 = x.1 := rfl

@[simp] private theorem v15PairToFinOf_one {R : Type*} (x : R × R) :
    v15PairToFinOf x 1 = x.2 := rfl

/-- Binary trace Euclideanity is equivalent to actual ideal trace
Euclideanity for every selected integer basis, including a Gauss-reduced one. -/
theorem v15_ideal_trace_euclidean_iff_binary_of
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) (α : F)
    {a b c : ℕ}
    (hGram : v15IdealTraceGramOf I hI B α =
      ((a : ℚ), (b : ℚ), (c : ℚ))) :
    V15IdealTraceEuclidean I α ↔ V15BinaryTraceEuclidean a b c := by
  let C := v15IdealRationalCoordinatesOf I hI B
  let Z := v15IdealIntegerCoordinatesOf I B
  constructor
  · intro h x
    let w : F := C.symm (v15PairToFinOf x)
    obtain ⟨y, hy⟩ := h w
    refine ⟨(Z y 0, Z y 1), ?_⟩
    rw [v15_ideal_trace_cost_of_eq_binary_cost I hI B α w y hGram] at hy
    have h0 : C w 0 = x.1 := by simp [w, C]
    have h1 : C w 1 = x.2 := by simp [w, C]
    change v15GramCostRat a b c (C w 0, C w 1) (Z y 0, Z y 1) < 2 at hy
    simpa only [h0, h1] using hy
  · intro h x
    let p : PlanePoint ℚ := (C x 0, C x 1)
    obtain ⟨z, hz⟩ := h p
    let y : I.coeToSubmodule := Z.symm (v15PairToFinOf z)
    refine ⟨y, ?_⟩
    rw [v15_ideal_trace_cost_of_eq_binary_cost I hI B α x y hGram]
    have h0 : Z y 0 = z.1 := by simp [y, Z]
    have h1 : Z y 1 = z.2 := by simp [y, Z]
    change v15GramCostRat a b c (C x 0, C x 1) (Z y 0, Z y 1) < 2
    simpa only [h0, h1, p] using hz

end

end TraceEuclidean
