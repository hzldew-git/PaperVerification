import NormEuclidean.MixedTraceBasis
import NormEuclidean.DifferentDiscriminantNormalization

/-!
# The actual archimedean dual of a nonzero fractional ideal

The dual is taken inside the entire real mixed space, so a frequency is
not assumed to be a diagonal field element. The dual-basis comparison
proves it is the mixed image of the algebraic trace-dual ideal, hence
the actual inverse different times the inverse original ideal.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.ArchimedeanIdealDual

open NumberField NumberField.mixedEmbedding Module MixedTracePairing
open scoped NumberField Classical nonZeroDivisors

variable (F : Type*) [Field F] [NumberField F]

/-- Mixed image of an actual integer submodule of the original field. -/
def image (J : Submodule ℤ F) : Submodule ℤ (mixedSpace F) :=
  J.map (mixedEmbedding F).toIntAlgHom.toLinearMap

/-- Image commutes with integer span for the actual mixed embedding. -/
theorem image_span {ι : Type*} [Fintype ι] (b : Basis ι ℚ F) :
    image F (Submodule.span ℤ (Set.range b)) =
      Submodule.span ℤ (Set.range (MixedTraceBasis.realBasis F b)) := by
  rw [image, Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℤ)
  apply congrArg Set.range
  funext i
  exact (MixedTraceBasis.realBasis_apply F b i).symm

/-- The image is precisely the unchanged original mixed ideal lattice. -/
theorem ideal_eq_image (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    idealLattice F I = image F ((I : Submodule (𝓞 F) F).restrictScalars ℤ) := by
  ext x
  rw [mem_idealLattice]
  rfl

/-- The actual algebraic trace-dual ideal, bundled as a nonzero fractional ideal. -/
def dual (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ I.1) (FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero I))

@[simp]
theorem dual_coe (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (dual F I).1 = FractionalIdeal.dual ℤ ℚ I.1 := rfl

/-- The original integer span of the actual fractional-ideal rational basis. -/
theorem ideal_span (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (I : Submodule (𝓞 F) F).restrictScalars ℤ =
      Submodule.span ℤ (Set.range (basisOfFractionalIdeal F I)) := by
  ext x
  exact (mem_span_basisOfFractionalIdeal (K := F) (I := I) (x := x)).symm

/-- The actual algebraic trace dual has the actual dual basis as its integer span. -/
theorem dual_ideal_span (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (dual F I : Submodule (𝓞 F) F).restrictScalars ℤ =
      Submodule.span ℤ (Set.range (basisOfFractionalIdeal F I).traceDual) := by
  change ((FractionalIdeal.dual ℤ ℚ I.1 : Submodule (𝓞 F) F).restrictScalars ℤ) = _
  rw [FractionalIdeal.coe_dual ℤ ℚ (Units.ne_zero I)]
  exact Submodule.traceDual_span_of_basis ℤ (I : Submodule (𝓞 F) F)
    (basisOfFractionalIdeal F I) (ideal_span F I)

/-- The complete mixed-space dual is exactly the actual algebraic trace-dual ideal image. -/
theorem dual_lattice (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (form F).dualSubmodule (idealLattice F I) = idealLattice F (dual F I) := by
  rw [ideal_eq_image F I, ideal_span, image_span, MixedTraceBasis.dual_span,
    ideal_eq_image F (dual F I), dual_ideal_span, image_span]

/-- Integral trace pairing with every original ideal element characterizes the actual dual. -/
theorem mem_dual_lattice (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (z : mixedSpace F) :
    z ∈ idealLattice F (dual F I) ↔
      ∀ x ∈ (I : Set F), form F z (mixedEmbedding F x) ∈ (1 : Submodule ℤ ℝ) := by
  rw [← dual_lattice, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hz x hx
    exact hz _ ((mem_idealLattice F I).mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice F I).mp hy
    exact h x hx

/-- Every mixed-space dual frequency is proved to be a diagonal trace-dual ideal element. -/
theorem dual_frequency_exists (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (z : mixedSpace F)
    (hz : ∀ x ∈ (I : Set F), form F z (mixedEmbedding F x) ∈ (1 : Submodule ℤ ℝ)) :
    ∃ y : F, y ∈ FractionalIdeal.dual ℤ ℚ I.1 ∧ mixedEmbedding F y = z :=
  (mem_idealLattice F (dual F I)).mp ((mem_dual_lattice F I z).mpr hz)

/-- The actual dual ideal is the inverse different times the inverse original ideal. -/
theorem dual_eq_codifferent (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (dual F I).1 = DifferentDiscriminantNormalization.codifferent F * I.1⁻¹ := by
  rw [dual_coe, FractionalIdeal.dual_eq_mul_inv,
    DifferentDiscriminantNormalization.codifferent_eq_traceDual]

/-- Duality is involutive on the unchanged nonzero fractional ideals. -/
theorem dual_dual (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : dual F (dual F I) = I := by
  apply Units.ext
  simp only [dual_coe, FractionalIdeal.dual_dual]

/-- The actual full mixed-space lattice is recovered by dualizing twice. -/
theorem bidual_lattice (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    (form F).dualSubmodule ((form F).dualSubmodule (idealLattice F I)) =
      idealLattice F I := by
  rw [dual_lattice, dual_lattice, dual_dual]

end NormEuclidean.ArchimedeanIdealDual
