import NormEuclidean.ChapterX.ProjectedComplement
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# The value-to-isotropy reduction in O'Meara 66:3

A regular isotropic form represents every field scalar. Consequently a
prescribed value is represented precisely when adjoining its negative line
is isotropic. These are actual algebraic proofs. They do not assert the
arithmetic Hasse--Minkowski theorem 66:1 at all number-field places.
-/

noncomputable section

namespace NormEuclidean.QuadraticValueRepresentation

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A regular isotropic space represents every scalar by an explicit affine
line through a vector with nonzero pairing with the isotropic vector. -/
theorem represents_of_isotropic (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (e : V) (he : e ≠ 0) (hiso : Q e = 0) (a : K) : ∃ x : V, Q x = a := by
  classical
  have hex : ∃ u : V, Q.polarBilin e u ≠ 0 := by
    by_contra! h
    exact he (hQ.1 e h)
  obtain ⟨u, hu⟩ := hex
  let t := (a - Q u) / Q.polarBilin e u
  refine ⟨u + t • e, ?_⟩
  rw [QuadraticMap.map_add (Q : V → K), Q.map_smul, hiso,
    Q.polar_smul_right, QuadraticMap.polar_comm (Q : V → K) u e]
  simp only [smul_eq_mul, mul_zero, add_zero]
  change Q u + (a - Q u) / Q.polarBilin e u * Q.polarBilin e u = a
  rw [div_mul_cancel₀ _ hu]
  ring

/-- Adjoin the negative line of the target value. The actual quadratic value
on `(x,t)` is `Q x - a*t^2`. -/
def negativeLine (Q : QuadraticForm K V) (a : K) : QuadraticForm K (V × K) :=
  Q.prod (-a • QuadraticMap.sq)

@[simp] theorem negativeLine_apply (Q : QuadraticForm K V) (a : K) (x : V) (t : K) :
    negativeLine Q a (x, t) = Q x - a * t ^ 2 := by
  simp only [negativeLine, prod_apply, QuadraticMap.smul_apply, sq_apply, smul_eq_mul]
  ring

/-- The negative-line extension uses the original polar convention exactly. -/
theorem negativeLine_polar (Q : QuadraticForm K V) (a : K)
    (x y : V) (t s : K) :
    (negativeLine Q a).polarBilin (x, t) (y, s) =
      Q.polarBilin x y - (2 * a) * t * s := by
  simp only [polarBilin_apply_apply, polar, negativeLine_apply, Prod.mk_add_mk]
  ring

/-- A nonzero target gives a regular negative-line extension over a
characteristic-zero field. This proves the regularity needed to apply 66:1;
it does not supply that arithmetic theorem. -/
theorem negativeLine_regular [CharZero K] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (a : K) (ha : a ≠ 0) :
    (negativeLine Q a).polarBilin.Nondegenerate := by
  have hs : (negativeLine Q a).polarBilin.IsSymm :=
    ⟨fun x y ↦ QuadraticMap.polar_comm (negativeLine Q a : V × K → K) x y⟩
  apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
  rintro ⟨x, t⟩ hp
  have hx : x = 0 := hQ.1 x (fun y ↦ by
    simpa only [negativeLine_polar, mul_zero, sub_zero] using hp (y, 0))
  have ht : (2 * a) * t = 0 := by
    simpa only [negativeLine_polar, map_zero, mul_one, zero_sub, neg_eq_zero]
      using hp (0, 1)
  have ht0 : t = 0 := (mul_eq_zero.mp ht).resolve_left
    (mul_ne_zero (by norm_num : (2 : K) ≠ 0) ha)
  exact Prod.ext hx ht0

/-- The scalar representation reduction used in 66:3, including the case in
which the isotropic vector has zero line coordinate. The target may be zero. -/
theorem represents_iff_negativeLine_isotropic (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (a : K) :
    (∃ x : V, Q x = a) ↔ ¬ (negativeLine Q a).Anisotropic := by
  constructor
  · rintro ⟨x, hx⟩ hani
    have hzero : negativeLine Q a (x, 1) = 0 := by simp [hx]
    have h := hani (x, 1) hzero
    exact one_ne_zero (congrArg Prod.snd h)
  · intro hiso
    obtain ⟨⟨x, t⟩, hxt, hvalue⟩ := (negativeLine Q a).not_anisotropic_iff_exists.mp hiso
    rw [negativeLine_apply, sub_eq_zero] at hvalue
    by_cases ht : t = 0
    · have hx : x ≠ 0 := by
        intro hx
        exact hxt (Prod.ext hx ht)
      have hQx : Q x = 0 := by simpa only [ht, zero_pow (by decide : 2 ≠ 0), mul_zero]
        using hvalue
      exact represents_of_isotropic Q hQ x hx hQx a
    · refine ⟨t⁻¹ • x, ?_⟩
      rw [Q.map_smul, hvalue]
      simp only [smul_eq_mul]
      field_simp

/-- A global isotropic orthogonal complement already represents the residual
in 104:3. No local-to-global representation assumption is needed in this branch. -/
theorem complement_represents_residual [NumberField K] [Invertible (2 : K)]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (v : V) (hv : Q v ≠ 0) (e : ProjectedComplement.complement Q v)
    (he : e ≠ 0) (hiso : Q e = 0) (a c β : K) :
    ∃ u : ProjectedComplement.complement Q v, Q u = a * (1 - c ^ 2 * β ^ 2) :=
  represents_of_isotropic (Q.comp (ProjectedComplement.complement Q v).subtype)
    (ProjectedComplement.complement_regular Q hQ v hv) e he hiso _

end NormEuclidean.QuadraticValueRepresentation
