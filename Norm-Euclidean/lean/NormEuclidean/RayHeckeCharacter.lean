import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Finite-order Hecke characters with their actual full conductor

The domain is the actual idelic ray class group for a finite modulus and
selected real places. The ideal character is transported by the proved
ideal-idelic equivalence. The conductor is the least full defining modulus
of the actual character kernel, including its necessary real places.
-/

noncomputable section

namespace NormEuclidean.RayHeckeCharacter

open NumberField GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

abbrev Character (m : RayClass.Modulus F) := RayClass.RayClassGroup m →* ℂ

/-- Evaluation on actual idèle classes, before quotienting by the ray modulus. -/
def onIdeleClass {m : RayClass.Modulus F} (χ : Character m) : IdeleClassGroup F →* ℂ :=
  χ.comp (QuotientGroup.mk' m.congruenceSubgroup)

theorem congruence_le_kernel {m : RayClass.Modulus F} (χ : Character m) :
    m.congruenceSubgroup ≤ (onIdeleClass χ).ker := by
  intro x hx
  change χ (QuotientGroup.mk' m.congruenceSubgroup x) = 1
  change χ (x : RayClass.RayClassGroup m) = 1
  rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]

theorem character_norm {m : RayClass.Modulus F} (χ : Character m)
    (C : RayClass.RayClassGroup m) : ‖χ C‖ = 1 :=
  (χ.isOfFinOrder (isOfFinOrder_of_finite C)).norm_eq_one

/-- The same character on the ideal-theoretic ray class group, with full modulus retained. -/
def idealCharacter {m : RayClass.Modulus F} (χ : Character m) :
    RayClass.IdealRayClassGroup m →* ℂ :=
  χ.comp (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.toMonoidHom

theorem idealCharacter_norm {m : RayClass.Modulus F} (χ : Character m)
    (C : RayClass.IdealRayClassGroup m) : ‖idealCharacter χ C‖ = 1 :=
  character_norm χ _

/-- Evaluation on prime-to-modulus fractional ideals. -/
def onIdeal {m : RayClass.Modulus F} (χ : Character m) :
    RayClass.primeToModulusIdeals m →* ℂ :=
  (idealCharacter χ).comp (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m))

theorem onIdeal_norm {m : RayClass.Modulus F} (χ : Character m)
    (I : RayClass.primeToModulusIdeals m) : ‖onIdeal χ I‖ = 1 :=
  idealCharacter_norm χ _

/-- Congruent principal ideals with the selected positive real signs have value one. -/
theorem onIdeal_principal {m : RayClass.Modulus F} (χ : Character m)
    (I : RayClass.primeToModulusIdeals m) (hI : I ∈ RayClass.principalRayIdealSubgroup m) :
    onIdeal χ I = 1 := by
  change idealCharacter χ (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m) I) = 1
  change idealCharacter χ (I : RayClass.IdealRayClassGroup m) = 1
  rw [(QuotientGroup.eq_one_iff I).mpr hI, map_one]

/-- The actual kernel is conductorial because the given full modulus defines it. -/
def kernel {m : RayClass.Modulus F} (χ : Character m) : ConductorialSubgroup F :=
  ⟨(onIdeleClass χ).ker, m, congruence_le_kernel χ⟩

/-- The least finite conductor together with exactly the necessary real-place signs. -/
def conductor {m : RayClass.Modulus F} (χ : Character m) : RayClass.Modulus F :=
  (kernel χ).fullConductor

theorem conductor_defines {m : RayClass.Modulus F} (χ : Character m) :
    (conductor χ).congruenceSubgroup ≤ (onIdeleClass χ).ker :=
  (kernel χ).fullConductor_isDefiningModulus

theorem conductor_le_iff {m : RayClass.Modulus F} (χ : Character m)
    (n : RayClass.Modulus F) :
    conductor χ ≤ n ↔ n.congruenceSubgroup ≤ (onIdeleClass χ).ker :=
  ((kernel χ).isDefiningModulus_iff_fullConductor_le n).symm

theorem conductor_le {m : RayClass.Modulus F} (χ : Character m) : conductor χ ≤ m :=
  (conductor_le_iff χ m).mpr (congruence_le_kernel χ)

/-- A real place occurs exactly when the local idèle-class character is nontrivial. -/
theorem conductor_real_place {m : RayClass.Modulus F} (χ : Character m)
    (v : RayClass.RealPlace F) :
    v ∈ (conductor χ).infinitePart ↔
      ∃ x, onIdeleClass χ (IdeleGroup.infinitePlaceIdeleClass v.1 x) ≠ 1 := by
  rw [conductor, ConductorialSubgroup.fullConductor,
    ConductorialSubgroup.mem_fullConductorInfinitePart_iff]
  change (¬ (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ (onIdeleClass χ).ker) ↔ _
  simp only [SetLike.le_def, MonoidHom.mem_range, MonoidHom.mem_ker]
  aesop

/-- The actual primitive character is constructed by descent to its full conductor. -/
def primitive {m : RayClass.Modulus F} (χ : Character m) : Character (conductor χ) :=
  QuotientGroup.lift (conductor χ).congruenceSubgroup (onIdeleClass χ)
    (conductor_defines χ)

theorem primitive_onIdeleClass {m : RayClass.Modulus F} (χ : Character m) :
    onIdeleClass (primitive χ) = onIdeleClass χ := by
  ext x
  rfl

theorem primitive_kernel {m : RayClass.Modulus F} (χ : Character m) :
    kernel (primitive χ) = kernel χ := by
  apply Subtype.ext
  change (onIdeleClass (primitive χ)).ker = (onIdeleClass χ).ker
  rw [primitive_onIdeleClass]

/-- Passing to the constructed primitive character leaves its full conductor unchanged. -/
theorem primitive_conductor {m : RayClass.Modulus F} (χ : Character m) :
    conductor (primitive χ) = conductor χ := by
  rw [conductor, primitive_kernel]
  rfl

end NormEuclidean.RayHeckeCharacter
