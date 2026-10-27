import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Binary isotropy and the negative Gram determinant

The Gram convention here is the matrix of `QuadraticForm.associated`, so
`Q(x,y) = a*x^2 + 2*b*x*y + c*y^2` and its determinant is `a*c-b^2`.
The criterion holds over every field in which two is invertible; finiteness
and nondegeneracy are not needed. It supplies the algebraic residue-field
step only, not a splitting-prime existence or binary class-number theorem.
-/

namespace NormEuclidean

/-- Coordinate binary isotropy is equivalent to the discriminant being a square.
The middle coefficient is `2*b`, so this discriminant is the negative
associated Gram determinant, rather than the polynomial discriminant `4*(b^2-a*c)`. -/
theorem binary_isotropic_iff_isSquare_neg_gramDet
    {K : Type*} [Field K] (a b c : K) :
    (∃ x y : K, (x ≠ 0 ∨ y ≠ 0) ∧ a*x^2 + 2*b*x*y + c*y^2 = 0) ↔
      IsSquare (-(a*c-b^2)) := by
  constructor
  · rintro ⟨x, y, hxy, hQ⟩
    by_cases hy : y = 0
    · subst y
      have hx : x ≠ 0 := hxy.resolve_right (not_not_intro rfl)
      have ha : a = 0 := by
        simpa [hx] using hQ
      subst a
      exact ⟨b, by ring⟩
    · refine ⟨(a*x+b*y)/y, ?_⟩
      field_simp
      linear_combination -a * hQ
  · rintro ⟨t, ht⟩
    by_cases ha : a = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [ha]⟩
    · refine ⟨t-b, a, Or.inr ha, ?_⟩
      linear_combination -a * ht

section QuadraticForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- Expansion in any two vectors, using the associated (half-polar) Gram convention. -/
theorem quadraticForm_binary_expansion (Q : QuadraticForm K V) (u v : V) (x y : K) :
    Q (x • u + y • v) = Q u*x^2 + 2*(Q.associated u v)*x*y + Q v*y^2 := by
  rw [← Q.associated_eq_self_apply K (x • u + y • v)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [Q.associated_eq_self_apply K, Q.associated_eq_self_apply K,
    QuadraticMap.associated_isSymm K Q v u]
  ring

/-- The determinant of the actual associated Gram matrix in a binary basis. -/
theorem binary_gramDet_eq (Q : QuadraticForm K V) (e : Module.Basis (Fin 2) K V) :
    (LinearMap.toMatrix₂ e e Q.associated).det =
      Q (e 0) * Q (e 1) - (Q.associated (e 0) (e 1))^2 := by
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix₂_apply]
  rw [Q.associated_eq_self_apply K, Q.associated_eq_self_apply K,
    QuadraticMap.associated_isSymm K Q (e 1) (e 0)]
  ring

/-- A genuine binary quadratic form is isotropic iff the negative determinant
of its associated Gram matrix is a square. No nondegeneracy assumption is
required; in the degenerate case the square may be zero. -/
theorem quadraticForm_binary_isotropic_iff_isSquare_neg_det
    (Q : QuadraticForm K V) (e : Module.Basis (Fin 2) K V) :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔
      IsSquare (-(LinearMap.toMatrix₂ e e Q.associated).det) := by
  rw [binary_gramDet_eq, ← binary_isotropic_iff_isSquare_neg_gramDet]
  constructor
  · rintro ⟨v, hv, hQv⟩
    have he : (e.repr v) 0 • e 0 + (e.repr v) 1 • e 1 = v := by
      simpa only [Fin.sum_univ_two] using e.sum_repr v
    refine ⟨(e.repr v) 0, (e.repr v) 1, ?_, ?_⟩
    · by_contra h
      push_neg at h
      exact hv (by simpa [h.1, h.2] using he.symm)
    · rw [← quadraticForm_binary_expansion, he, hQv]
  · rintro ⟨x, y, hxy, hQ⟩
    refine ⟨x • e 0 + y • e 1, ?_, ?_⟩
    · intro hz
      have h0 := congrArg (fun v => e.repr v 0) hz
      have h1 := congrArg (fun v => e.repr v 1) hz
      simp at h0 h1
      exact hxy.elim (fun hx => hx h0) (fun hy => hy h1)
    · rw [quadraticForm_binary_expansion]
      exact hQ

/-- The square test does not depend on the chosen basis. -/
theorem binary_neg_gramDet_isSquare_basis_independent
    (Q : QuadraticForm K V) (e f : Module.Basis (Fin 2) K V) :
    IsSquare (-(LinearMap.toMatrix₂ e e Q.associated).det) ↔
      IsSquare (-(LinearMap.toMatrix₂ f f Q.associated).det) :=
  (quadraticForm_binary_isotropic_iff_isSquare_neg_det Q e).symm.trans
    (quadraticForm_binary_isotropic_iff_isSquare_neg_det Q f)

/-- For a nonsingular Gram matrix, the square root is necessarily nonzero. -/
theorem quadraticForm_binary_isotropic_iff_nonzero_square_root
    (Q : QuadraticForm K V) (e : Module.Basis (Fin 2) K V)
    (hdet : (LinearMap.toMatrix₂ e e Q.associated).det ≠ 0) :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔
      ∃ s : K, s ≠ 0 ∧ s^2 = -(LinearMap.toMatrix₂ e e Q.associated).det := by
  rw [quadraticForm_binary_isotropic_iff_isSquare_neg_det]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_, by simpa only [pow_two] using hs.symm⟩
    intro hz
    subst s
    simp only [mul_zero, neg_eq_zero] at hs
    exact hdet hs
  · rintro ⟨s, _, hs⟩
    exact ⟨s, by simpa only [pow_two] using hs.symm⟩

end QuadraticForm

/-- The odd finite-residue-field version, with characteristic explicit.
The finite-field hypothesis records the intended application; the preceding
result proves the stronger statement for arbitrary fields of odd characteristic. -/
theorem finiteField_binary_isotropic_iff_isSquare_neg_det
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (e : Module.Basis (Fin 2) K V)
    (hchar : ringChar K ≠ 2) :
    letI : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hchar)
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔
      IsSquare (-(LinearMap.toMatrix₂ e e Q.associated).det) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hchar)
  exact quadraticForm_binary_isotropic_iff_isSquare_neg_det Q e


end NormEuclidean
