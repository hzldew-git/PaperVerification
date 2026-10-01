import LeanCert.Core.Expr
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Symbolic first and second derivatives for the smooth LeanCert fragment

This small verified layer covers the constructors used by the Odlyzko
quadrature certificates, including reciprocal, `sinh`, and `cosh`.  It is
separate from the interval engine's narrower automatic-differentiation
fragment because reciprocal expressions need an explicit nonvanishing
hypothesis.
-/

namespace LeanCert.Core

open Set

namespace Expr

/-- Formal derivative for a single real variable.  Every variable node is
interpreted as that same variable by `eval (fun _ => x)`. -/
def formalDeriv : Expr → Expr
  | .const _ | .namedConst _ => .const 0
  | .var _ => .const 1
  | .add a b => .add (formalDeriv a) (formalDeriv b)
  | .mul a b => .add (.mul (formalDeriv a) b) (.mul a (formalDeriv b))
  | .neg a => .neg (formalDeriv a)
  | .inv a => .neg (.div (formalDeriv a) (.mul a a))
  | .exp a => .mul (.exp a) (formalDeriv a)
  | .sin a => .mul (.cos a) (formalDeriv a)
  | .cos a => .neg (.mul (.sin a) (formalDeriv a))
  | .sinh a => .mul (.cosh a) (formalDeriv a)
  | .cosh a => .mul (.sinh a) (formalDeriv a)
  | _ => .const 0

/-- Compact quotient-rule expression for the second derivative of `n / d`.
Keeping this expression factored avoids the large duplicated term produced by
two direct expansions of `formalDeriv`. -/
def quotientSecond (n d : Expr) : Expr :=
  let n' := formalDeriv n
  let n'' := formalDeriv n'
  let d' := formalDeriv d
  let d'' := formalDeriv d'
  .add (.div n'' d)
    (.add
      (.neg (.div (.mul (.const 2) (.mul n' d')) (.mul d d)))
      (.add
        (.neg (.div (.mul n d'') (.mul d d)))
        (.div (.mul (.const 2) (.mul n (.mul d' d')))
          (.mul d (.mul d d)))))

/-- The compact quotient expression evaluates to the twice-expanded formal
derivative whenever the denominator is nonzero. -/
theorem eval_formalDeriv_two_div_eq_quotientSecond (n d : Expr) (x : ℝ)
    (hd : eval (fun _ ↦ x) d ≠ 0) :
    eval (fun _ ↦ x) (formalDeriv (formalDeriv (.div n d))) =
      eval (fun _ ↦ x) (quotientSecond n d) := by
  simp only [Expr.div, formalDeriv, quotientSecond, eval_add, eval_mul, eval_neg,
    eval_inv, eval_const]
  field_simp [hd]
  ring

/-- The smooth expression constructors supported by `formalDeriv`. -/
@[aesop safe constructors]
inductive DiffSupported : Expr → Prop where
  | const (q : ℚ) : DiffSupported (.const q)
  | namedConst (c : MathConst) : DiffSupported (.namedConst c)
  | var (i : ℕ) : DiffSupported (.var i)
  | add {a b} : DiffSupported a → DiffSupported b → DiffSupported (.add a b)
  | mul {a b} : DiffSupported a → DiffSupported b → DiffSupported (.mul a b)
  | neg {a} : DiffSupported a → DiffSupported (.neg a)
  | inv {a} : DiffSupported a → DiffSupported (.inv a)
  | exp {a} : DiffSupported a → DiffSupported (.exp a)
  | sin {a} : DiffSupported a → DiffSupported (.sin a)
  | cos {a} : DiffSupported a → DiffSupported (.cos a)
  | sinh {a} : DiffSupported a → DiffSupported (.sinh a)
  | cosh {a} : DiffSupported a → DiffSupported (.cosh a)

/-- All reciprocal nodes in an expression have nonzero arguments at `x`. -/
def RegularAt : Expr → ℝ → Prop
  | .const _, _ | .namedConst _, _ | .var _, _ => True
  | .add a b, x | .mul a b, x => RegularAt a x ∧ RegularAt b x
  | .neg a, x | .exp a, x | .sin a, x | .cos a, x |
      .sinh a, x | .cosh a, x => RegularAt a x
  | .inv a, x => RegularAt a x ∧ eval (fun _ => x) a ≠ 0
  | _, _ => False

theorem DiffSupported.formalDeriv {e : Expr} (h : DiffSupported e) :
    DiffSupported (formalDeriv e) := by
  induction h with
  | const q | namedConst q => exact .const 0
  | var i => exact .const 1
  | add ha hb iha ihb => exact .add iha ihb
  | mul ha hb iha ihb => exact .add (.mul iha hb) (.mul ha ihb)
  | neg ha ih => exact .neg ih
  | inv ha ih => exact .neg (.mul ih (.inv (.mul ha ha)))
  | exp ha ih => exact .mul (.exp ha) ih
  | sin ha ih => exact .mul (.cos ha) ih
  | cos ha ih => exact .neg (.mul (.sin ha) ih)
  | sinh ha ih => exact .mul (.cosh ha) ih
  | cosh ha ih => exact .mul (.sinh ha) ih

theorem regularAt_formalDeriv {e : Expr} (h : DiffSupported e) {x : ℝ}
    (hr : RegularAt e x) : RegularAt (formalDeriv e) x := by
  induction h with
  | const q | namedConst q | var q => trivial
  | add ha hb iha ihb => exact ⟨iha hr.1, ihb hr.2⟩
  | mul ha hb iha ihb =>
      exact ⟨⟨iha hr.1, hr.2⟩, hr.1, ihb hr.2⟩
  | neg ha ih => exact ih hr
  | inv ha ih =>
      refine ⟨ih hr.1, ?_, ?_⟩
      · exact ⟨hr.1, hr.1⟩
      · simp only [eval_mul]
        exact mul_ne_zero hr.2 hr.2
  | exp ha ih => exact ⟨hr, ih hr⟩
  | sin ha ih => exact ⟨hr, ih hr⟩
  | cos ha ih => exact ⟨hr, ih hr⟩
  | sinh ha ih => exact ⟨hr, ih hr⟩
  | cosh ha ih => exact ⟨hr, ih hr⟩

/-- Semantic correctness of one symbolic differentiation step. -/
theorem hasDerivAt_eval_formalDeriv {e : Expr} (h : DiffSupported e) {x : ℝ}
    (hr : RegularAt e x) :
    HasDerivAt (fun y => eval (fun _ => y) e)
      (eval (fun _ => x) (formalDeriv e)) x := by
  induction h with
  | const q =>
      simp only [formalDeriv, eval_const]
      norm_num
      exact hasDerivAt_const x (q : ℝ)
  | namedConst c =>
      simp only [formalDeriv, eval_namedConst, eval_const]
      norm_num
      exact hasDerivAt_const x c.toReal
  | var i =>
      simp only [formalDeriv, eval_var, eval_const]
      norm_num
      exact (hasDerivAt_id x).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
  | add ha hb iha ihb =>
      exact ((iha hr.1).add (ihb hr.2)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
  | mul ha hb iha ihb =>
      exact ((iha hr.1).mul (ihb hr.2)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
  | neg ha ih =>
      exact (ih hr).neg.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
  | inv ha ih =>
      have hd := (ih hr.1).inv hr.2
      refine (hd.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      simp only [formalDeriv, eval_neg, Expr.div, eval_mul, eval_inv]
      field_simp
  | exp ha ih =>
      exact (ih hr).exp.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
  | sin ha ih =>
      refine ((ih hr).sin.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      simp [formalDeriv, mul_comm]
  | cos ha ih =>
      refine ((ih hr).cos.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      simp [formalDeriv, mul_comm]
  | sinh ha ih =>
      refine ((ih hr).sinh.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      simp [formalDeriv, mul_comm]
  | cosh ha ih =>
      refine ((ih hr).cosh.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
      simp [formalDeriv, mul_comm]

/-- A supported expression is `C^n` on any set where all reciprocal
arguments stay nonzero. -/
theorem contDiffOn_eval {e : Expr} (h : DiffSupported e) {s : Set ℝ} (n : ℕ∞)
    (hr : ∀ x ∈ s, RegularAt e x) :
    ContDiffOn ℝ n (fun y => eval (fun _ => y) e) s := by
  induction h with
  | const q => simpa using (contDiff_const : ContDiff ℝ n (fun _ : ℝ => (q : ℝ))).contDiffOn
  | namedConst c =>
      simpa using (contDiff_const : ContDiff ℝ n (fun _ : ℝ => c.toReal)).contDiffOn
  | var i =>
      exact (contDiff_id : ContDiff ℝ n (id : ℝ → ℝ)).contDiffOn.congr (fun _ _ => rfl)
  | add ha hb iha ihb =>
      exact (iha (fun x hx => (hr x hx).1)).add (ihb (fun x hx => (hr x hx).2))
  | mul ha hb iha ihb =>
      exact (iha (fun x hx => (hr x hx).1)).mul (ihb (fun x hx => (hr x hx).2))
  | neg ha ih => exact (ih hr).neg
  | inv ha ih =>
      exact (ih (fun x hx => (hr x hx).1)).inv (fun x hx => (hr x hx).2)
  | exp ha ih => exact (ih hr).exp
  | sin ha ih => exact (ih hr).sin
  | cos ha ih => exact (ih hr).cos
  | sinh ha ih => exact (ih hr).sinh
  | cosh ha ih => exact (ih hr).cosh

/-- On an open regular set, the second ordinary derivative is the evaluation
of two formal differentiation steps. -/
theorem iteratedDeriv_two_eval_eq {e : Expr} (h : DiffSupported e)
    {s : Set ℝ} (hs : IsOpen s) {x : ℝ} (hx : x ∈ s)
    (hr : ∀ y ∈ s, RegularAt e y) :
    iteratedDeriv 2 (fun y => eval (fun _ => y) e) x =
      eval (fun _ => x) (formalDeriv (formalDeriv e)) := by
  let f : ℝ → ℝ := fun y => eval (fun _ => y) e
  let f' : ℝ → ℝ := fun y => eval (fun _ => y) (formalDeriv e)
  have hfirst : deriv f =ᶠ[nhds x] f' := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact (hasDerivAt_eval_formalDeriv h (hr y hy)).deriv
  have hsecond := hasDerivAt_eval_formalDeriv h.formalDeriv
    (regularAt_formalDeriv h (hr x hx))
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    show iteratedDeriv 1 f = deriv f by
      rw [show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero]]
  rw [hfirst.deriv_eq]
  exact hsecond.deriv

end Expr
end LeanCert.Core
