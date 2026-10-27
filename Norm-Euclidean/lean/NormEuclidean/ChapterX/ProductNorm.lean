import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Data.Fintype.Option

/-!
# Determinant norms in finite dependent products

The factors may have different dimensions. The proof splits off one factor
at a time, using the determinant of a product of two linear maps.
-/

noncomputable section

namespace NormEuclidean.ProductNorm

universe u v

variable {F : Type*} [Field F]

/-- The determinant norm in a product of two finite algebras is the product
of the two determinant norms. -/
theorem norm_prod {A B : Type*} [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] [Module.Finite F A] [Module.Finite F B]
    (a : A) (b : B) :
    Algebra.norm F (a, b) = Algebra.norm F a * Algebra.norm F b := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (A × B) (a, b) =
      LinearMap.prodMap (Algebra.lmul F A a) (Algebra.lmul F B b) := by
    ext x <;> rfl
  rw [h, LinearMap.det_prodMap]

/-- Splitting a dependent product over `Option` into its head and tail is
an algebra equivalence, with the ordinary componentwise scalar action. -/
def piOptionAlgEquiv {ι : Type*} (A : Option ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] :
    ((i : Option ι) → A i) ≃ₐ[F] A none × ((i : ι) → A (some i)) :=
  { RingEquiv.piOptionEquivProd with commutes' := fun _ ↦ rfl }

/-- The norm of an element of a finite dependent product equals the
product of its component norms. No equality of the factor dimensions is needed. -/
theorem norm_pi {ι : Type u} [Fintype ι] (A : ι → Type v)
    [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] [∀ i, Module.Finite F (A i)]
    (x : (i : ι) → A i) :
    Algebra.norm F x = ∏ i, Algebra.norm F (x i) := by
  classical
  let P (ι : Type u) : Prop := ∀ [Fintype ι] (A : ι → Type v)
    [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] [∀ i, Module.Finite F (A i)]
    (x : (i : ι) → A i), Algebra.norm F x = ∏ i, Algebra.norm F (x i)
  have h : P ι := by
    refine Finite.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro α β e ih _ A _ _ _ x
      letI : Fintype α := Fintype.ofEquiv β e.symm
      let t := (AlgEquiv.piCongrLeft F A e).symm
      rw [← Algebra.norm_eq_of_algEquiv t x, ih]
      exact Fintype.prod_equiv e _ _ (fun i ↦ rfl)
    · intro _ A _ _ _ x
      have hx : x = 1 := Subsingleton.elim _ _
      simp [hx]
    · intro α hα ih hOption A _ _ _ x
      have hOptionEq : hOption = @instFintypeOption α hα := Subsingleton.elim _ _
      subst hOption
      rw [← Algebra.norm_eq_of_algEquiv (piOptionAlgEquiv A) x]
      change Algebra.norm F (x none, fun i ↦ x (some i)) = _
      rw [norm_prod, ih]
      exact (Fintype.prod_option (fun i ↦ Algebra.norm F (x i))).symm
  exact h A x

end NormEuclidean.ProductNorm
