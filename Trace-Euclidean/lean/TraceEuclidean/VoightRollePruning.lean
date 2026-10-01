import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.FieldTheory.Separable

/-!
# Rolle-theoretic kernel for Voight coefficient pruning

Voight's recursive enumeration fixes the coefficients of a monic polynomial
from the top down.  At each step it uses the real roots of an iterated
derivative to restrict the next coefficient.  This file proves the part of
that argument which is independent of the numerical search: a real-split
polynomial has real-split derivatives of every order, with the expected
degree and root count.

The later finite certificates may therefore use exact isolating intervals for
the roots of a derivative stage without adding a real-rootedness premise.
-/

namespace TraceEuclidean

open Polynomial

/-- Rolle's theorem, stated in the form needed by the Voight recursion: the
derivative of a real-split polynomial is again real-split.  Multiplicities are
included. -/
theorem splits_derivative_of_splits_real {p : ℝ[X]}
    (hp : p.Splits) : p.derivative.Splits := by
  rw [Polynomial.splits_iff_card_roots] at hp ⊢
  have hlower := Polynomial.card_roots_le_derivative p
  have hupper := Polynomial.card_roots' p.derivative
  rw [hp] at hlower
  rw [Polynomial.natDegree_derivative] at hupper ⊢
  omega

/-- Every iterated derivative of a real-split polynomial is real-split. -/
theorem splits_iterateDerivative_of_splits_real {p : ℝ[X]}
    (hp : p.Splits) :
    ∀ k : ℕ, (Polynomial.derivative^[k] p).Splits := by
  intro k
  induction k with
  | zero => simpa using hp
  | succ k induction =>
      rw [Function.iterate_succ_apply']
      exact splits_derivative_of_splits_real induction

/-- Over the reals, the `k`-fold derivative has exactly the expected degree.
This includes the zero-polynomial convention once `k` exceeds the degree. -/
theorem natDegree_iterateDerivative_real (p : ℝ[X]) (k : ℕ) :
    (Polynomial.derivative^[k] p).natDegree = p.natDegree - k := by
  induction k with
  | zero => simp
  | succ k induction =>
      rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative,
        induction]
      omega

/-- The roots of every derivative stage account for its full degree. -/
theorem card_roots_iterateDerivative_of_splits_real {p : ℝ[X]}
    (hp : p.Splits) (k : ℕ) :
    (Polynomial.derivative^[k] p).roots.card = p.natDegree - k := by
  rw [(Polynomial.splits_iff_card_roots.mp
    (splits_iterateDerivative_of_splits_real hp k)),
    natDegree_iterateDerivative_real]

/-- If the first `j` entries of a list lie weakly to the left of `x` and the
remaining entries lie weakly to its right, the product of the signed
distances has the expected alternating sign. -/
theorem negOnePow_mul_listRootProduct_nonneg
    (l : List ℝ) (j : ℕ) (x : ℝ)
    (hleft : ∀ y ∈ l.take j, y ≤ x)
    (hright : ∀ y ∈ l.drop j, x ≤ y) :
    0 ≤ (-1 : ℝ) ^ (l.length - j) *
      (l.map fun y => x - y).prod := by
  let leftFactors := (l.take j).map fun y => x - y
  let rightFactors := (l.drop j).map fun y => y - x
  have hleftNonneg : 0 ≤ leftFactors.prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    exact sub_nonneg.mpr (hleft y hy)
  have hrightNonneg : 0 ≤ rightFactors.prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    exact sub_nonneg.mpr (hright y hy)
  have hsplit :
      (l.map fun y => x - y).prod =
        leftFactors.prod *
          ((l.drop j).map fun y => x - y).prod := by
    calc
      (l.map fun y => x - y).prod =
          ((l.take j ++ l.drop j).map fun y => x - y).prod := by
            rw [List.take_append_drop]
      _ = leftFactors.prod *
          ((l.drop j).map fun y => x - y).prod := by
            simp [leftFactors]
  have hrightSign :
      ((l.drop j).map fun y => x - y).prod =
        (-1 : ℝ) ^ (l.drop j).length * rightFactors.prod := by
    calc
      ((l.drop j).map fun y => x - y).prod =
          (rightFactors.map Neg.neg).prod := by
            congr 1
            simp only [rightFactors, List.map_map]
            apply List.map_congr_left
            intro y hy
            simp only [Function.comp_apply]
            ring
      _ = (-1 : ℝ) ^ rightFactors.length * rightFactors.prod :=
        List.prod_map_neg rightFactors
      _ = (-1 : ℝ) ^ (l.drop j).length * rightFactors.prod := by
        simp [rightFactors]
  rw [hsplit, hrightSign, List.length_drop]
  calc
    (-1 : ℝ) ^ (l.length - j) *
          (leftFactors.prod *
            ((-1 : ℝ) ^ (l.length - j) * rightFactors.prod)) =
        (((-1 : ℝ) ^ (l.length - j)) *
          ((-1 : ℝ) ^ (l.length - j))) *
            (leftFactors.prod * rightFactors.prod) := by ring
    _ = leftFactors.prod * rightFactors.prod := by
      rw [← mul_pow]
      norm_num
    _ ≥ 0 := mul_nonneg hleftNonneg hrightNonneg

/-- The real roots of `p`, sorted in increasing order. -/
noncomputable def voightSortedRoots (p : ℝ[X]) : List ℝ :=
  p.roots.sort (· ≤ ·)

/-- A split polynomial has one entry in the sorted root list for every unit of
its degree, counted with multiplicity. -/
theorem voightSortedRoots_length {p : ℝ[X]} (hp : p.Splits) :
    (voightSortedRoots p).length = p.natDegree := by
  simp [voightSortedRoots, hp.natDegree_eq_card_roots]

/-- Evaluation of a split polynomial as its leading coefficient times the
product over its sorted real root list. -/
theorem eval_eq_leadingCoeff_mul_sortedRoots_product {p : ℝ[X]}
    (hp : p.Splits) (x : ℝ) :
    p.eval x = p.leadingCoeff *
      ((voightSortedRoots p).map fun y => x - y).prod := by
  rw [hp.eval_eq_prod_roots]
  have hcoe :
      (↑((voightSortedRoots p).map fun y => x - y) :
          Multiset ℝ) =
        p.roots.map (fun y => x - y) := by
    dsimp [voightSortedRoots]
    rw [← Multiset.map_coe, Multiset.sort_eq]
  congr 1
  calc
    (p.roots.map fun y => x - y).prod =
        (↑((voightSortedRoots p).map fun y => x - y) :
          Multiset ℝ).prod := by
      exact congrArg (fun s : Multiset ℝ => s.prod) hcoe.symm
    _ = ((voightSortedRoots p).map fun y => x - y).prod :=
      Multiset.prod_coe _

/-- Evaluation of a monic split polynomial as the product over its sorted
real root list. -/
theorem eval_eq_sortedRoots_product {p : ℝ[X]}
    (hp : p.Splits) (hm : p.Monic) (x : ℝ) :
    p.eval x =
      ((voightSortedRoots p).map fun y => x - y).prod := by
  simpa [hm.leadingCoeff] using
    eval_eq_leadingCoeff_mul_sortedRoots_product hp x

/-- For a separable polynomial, the sorted roots are strictly increasing. -/
theorem voightSortedRoots_sortedLT {p : ℝ[X]}
    (hsep : p.Separable) :
    (voightSortedRoots p).SortedLT := by
  rw [List.sortedLT_iff_nodup_and_sortedLE]
  constructor
  · rw [← Multiset.coe_nodup]
    simpa [voightSortedRoots] using Polynomial.nodup_roots hsep
  · rw [List.sortedLE_iff_pairwise]
    exact Multiset.pairwise_sort p.roots (· ≤ ·)

/-- The `i`-th real root of a split polynomial in increasing order. -/
noncomputable def voightSortedRoot (p : ℝ[X]) (hp : p.Splits)
    (i : Fin p.natDegree) : ℝ :=
  (voightSortedRoots p).get ⟨i, by
    simpa [voightSortedRoots, hp.natDegree_eq_card_roots]
      using i.isLt⟩

/-- Every indexed sorted root is a root of the source polynomial. -/
theorem voightSortedRoot_mem_roots {p : ℝ[X]}
    (hp : p.Splits) (i : Fin p.natDegree) :
    voightSortedRoot p hp i ∈ p.roots := by
  exact (Multiset.mem_sort
    (s := p.roots) (r := fun x y : ℝ => x ≤ y)).mp
      (List.get_mem (voightSortedRoots p) ⟨i, by
        simpa [voightSortedRoots, hp.natDegree_eq_card_roots]
          using i.isLt⟩)

/-- Multiplication by a nonzero constant does not change the sorted root
list. -/
theorem voightSortedRoots_C_mul (p : ℝ[X]) {a : ℝ}
    (ha : a ≠ 0) :
    voightSortedRoots (C a * p) = voightSortedRoots p := by
  simp [voightSortedRoots, Polynomial.roots_C_mul p ha]

/-- The indexed sorted roots are unchanged by multiplication by a nonzero
constant. -/
theorem voightSortedRoot_C_mul (p : ℝ[X]) {a : ℝ}
    (ha : a ≠ 0) (hp : p.Splits) (i : Fin p.natDegree) :
    voightSortedRoot (C a * p) (hp.C_mul a)
        ⟨i, by rw [Polynomial.natDegree_C_mul ha]; exact i.isLt⟩ =
      voightSortedRoot p hp i := by
  simp only [voightSortedRoot, List.get_eq_getElem]
  simp only [voightSortedRoots_C_mul p ha]

/-- A polynomial identified with a nonzero constant multiple has the same
indexed sorted roots as the unscaled polynomial. -/
theorem voightSortedRoot_eq_of_eq_C_mul
    {q r : ℝ[X]} {a : ℝ} (ha : a ≠ 0)
    (hq : q.Splits) (hr : r.Splits) (heq : q = C a * r)
    (i : Fin r.natDegree) :
    voightSortedRoot q hq
        ⟨i, by rw [heq, Polynomial.natDegree_C_mul ha]; exact i.isLt⟩ =
      voightSortedRoot r hr i := by
  subst q
  simpa using voightSortedRoot_C_mul r ha hr i

/-- Between every two consecutive roots of a split separable polynomial lies
a root of its derivative.  This is the ordered Rolle step used by the exact
Voight enumeration. -/
theorem exists_derivativeRoot_between_sortedRoots {p : ℝ[X]}
    (hp : p.Splits) (hsep : p.Separable)
    (i : Fin p.natDegree) (hi : i + 1 < p.natDegree) :
    ∃ z : ℝ,
      voightSortedRoot p hp i < z ∧
      z < voightSortedRoot p hp ⟨i + 1, hi⟩ ∧
      p.derivative.eval z = 0 := by
  have hlength :
      (voightSortedRoots p).length = p.natDegree :=
    voightSortedRoots_length hp
  have hi0 : i < (voightSortedRoots p).length := by omega
  have hi1 : i + 1 < (voightSortedRoots p).length := by omega
  let left : Fin (voightSortedRoots p).length := ⟨i, hi0⟩
  let right : Fin (voightSortedRoots p).length := ⟨i + 1, hi1⟩
  have hleftRight : left < right := by simp [left, right]
  have hstrict :=
    (voightSortedRoots_sortedLT hsep).strictMono_get
  have hlt :
      (voightSortedRoots p).get left <
        (voightSortedRoots p).get right := by
    simpa [left, right] using hstrict hleftRight
  have hleftMem :
      (voightSortedRoots p).get left ∈ p.roots := by
    exact (Multiset.mem_sort
      (s := p.roots) (r := fun x y : ℝ => x ≤ y)).mp
        (List.get_mem (voightSortedRoots p) left)
  have hrightMem :
      (voightSortedRoots p).get right ∈ p.roots := by
    exact (Multiset.mem_sort
      (s := p.roots) (r := fun x y : ℝ => x ≤ y)).mp
        (List.get_mem (voightSortedRoots p) right)
  have hp0 : p ≠ 0 :=
    Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hleftRoot :
      p.eval ((voightSortedRoots p).get left) = 0 :=
    (Polynomial.mem_roots hp0).mp hleftMem
  have hrightRoot :
      p.eval ((voightSortedRoots p).get right) = 0 :=
    (Polynomial.mem_roots hp0).mp hrightMem
  obtain ⟨z, hzbetween, hzderiv⟩ :=
    exists_deriv_eq_zero hlt p.continuousOn
      (hleftRoot.trans hrightRoot.symm)
  refine ⟨z, ?_, ?_, ?_⟩
  · simpa [voightSortedRoot, left] using hzbetween.1
  · simpa [voightSortedRoot, right] using hzbetween.2
  · simpa only [p.deriv] using hzderiv

/-- A chosen Rolle root between the consecutive roots indexed by `i`. -/
noncomputable def rolleRoot (p : ℝ[X]) (hp : p.Splits)
    (hsep : p.Separable) (i : Fin p.derivative.natDegree) : ℝ :=
  Classical.choose
    (exists_derivativeRoot_between_sortedRoots hp hsep
      ⟨i, by
        have hi := i.isLt
        have hdeg := Polynomial.natDegree_derivative p
        omega⟩
      (by
        have hi := i.isLt
        have hdeg := Polynomial.natDegree_derivative p
        change i.val + 1 < p.natDegree
        omega))

/-- The chosen Rolle root lies in the stated interval and is a root of the
derivative. -/
theorem rolleRoot_spec (p : ℝ[X]) (hp : p.Splits)
    (hsep : p.Separable) (i : Fin p.derivative.natDegree) :
    voightSortedRoot p hp ⟨i, by
      have hi := i.isLt
      have hdeg := Polynomial.natDegree_derivative p
      omega⟩ < rolleRoot p hp hsep i ∧
    rolleRoot p hp hsep i <
      voightSortedRoot p hp ⟨i + 1, by
        have hi := i.isLt
        have hdeg := Polynomial.natDegree_derivative p
        omega⟩ ∧
    p.derivative.eval (rolleRoot p hp hsep i) = 0 := by
  exact Classical.choose_spec
    (exists_derivativeRoot_between_sortedRoots hp hsep
      ⟨i, by
        have hi := i.isLt
        have hdeg := Polynomial.natDegree_derivative p
        omega⟩
      (by
        have hi := i.isLt
        have hdeg := Polynomial.natDegree_derivative p
        change i.val + 1 < p.natDegree
        omega))

/-- The chosen Rolle roots are strictly increasing. -/
theorem rolleRoot_strictMono (p : ℝ[X]) (hp : p.Splits)
    (hsep : p.Separable) :
    StrictMono (rolleRoot p hp hsep) := by
  intro i j hij
  have hsorted := (voightSortedRoots_sortedLT hsep).sortedLE
  let i1 : Fin p.natDegree := ⟨i + 1, by
    have hi := i.isLt
    have hdeg := Polynomial.natDegree_derivative p
    omega⟩
  let jj : Fin p.natDegree := ⟨j, by
    have hj := j.isLt
    have hdeg := Polynomial.natDegree_derivative p
    omega⟩
  have hi1j : i1 ≤ jj := by
    simp [i1, jj]
    omega
  have hmiddle :
      voightSortedRoot p hp i1 ≤
        voightSortedRoot p hp jj := by
    exact hsorted.monotone_get hi1j
  exact lt_trans (rolleRoot_spec p hp hsep i).2.1
    (lt_of_le_of_lt hmiddle (rolleRoot_spec p hp hsep j).1)

/-- The complete ordered list of chosen Rolle roots. -/
noncomputable def rolleRoots (p : ℝ[X]) (hp : p.Splits)
    (hsep : p.Separable) : List ℝ :=
  List.ofFn (rolleRoot p hp hsep)

/-- The Rolle-root list exhausts the derivative roots, with multiplicity. -/
theorem rolleRoots_coe_eq_derivativeRoots
    (p : ℝ[X]) (hp : p.Splits) (hsep : p.Separable) :
    (↑(rolleRoots p hp hsep) : Multiset ℝ) =
      p.derivative.roots := by
  have hstrict : StrictMono (rolleRoot p hp hsep) :=
    rolleRoot_strictMono p hp hsep
  have hnodup :
      (↑(rolleRoots p hp hsep) : Multiset ℝ).Nodup := by
    rw [Multiset.coe_nodup]
    exact List.nodup_ofFn_ofInjective hstrict.injective
  have hle :
      (↑(rolleRoots p hp hsep) : Multiset ℝ) ≤
        p.derivative.roots := by
    rw [Multiset.le_iff_subset hnodup]
    intro z hz
    rw [Multiset.mem_coe] at hz
    rw [rolleRoots, List.mem_iff_get] at hz
    obtain ⟨i, hiEq⟩ := hz
    have hiBound : i.val < p.derivative.natDegree := by
      simpa [rolleRoots] using i.isLt
    let i' : Fin p.derivative.natDegree := ⟨i.val, hiBound⟩
    have hzEq : z = rolleRoot p hp hsep i' := by
      simpa [rolleRoots, i'] using hiEq.symm
    rw [hzEq, Polynomial.mem_roots]
    · exact (rolleRoot_spec p hp hsep i').2.2
    · exact Polynomial.ne_zero_of_natDegree_gt i'.isLt
  apply Multiset.eq_of_le_of_card_le hle
  have hpderiv : p.derivative.Splits :=
    splits_derivative_of_splits_real hp
  rw [Polynomial.splits_iff_card_roots] at hpderiv
  rw [hpderiv]
  simp [rolleRoots]

/-- The derivative of a split separable real polynomial of degree at least
two is again separable.  The proof uses the strictly interlacing Rolle roots,
so it does not require a separate discriminant calculation. -/
theorem separable_derivative_of_splits_separable_real {p : ℝ[X]}
    (hp : p.Splits) (hsep : p.Separable)
    (hdegree : 1 < p.natDegree) : p.derivative.Separable := by
  have hpderiv : p.derivative.Splits :=
    splits_derivative_of_splits_real hp
  have hpderiv0 : p.derivative ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt (n := 0)
    rw [Polynomial.natDegree_derivative]
    omega
  apply (Polynomial.nodup_roots_iff_of_splits hpderiv0 hpderiv).mp
  rw [← rolleRoots_coe_eq_derivativeRoots p hp hsep,
    Multiset.coe_nodup]
  exact List.nodup_ofFn_ofInjective
    (rolleRoot_strictMono p hp hsep).injective

/-- Every nonconstant iterated derivative of a split separable real
polynomial remains separable. -/
theorem separable_iterateDerivative_of_splits_separable_real
    {p : ℝ[X]} (hp : p.Splits) (hsep : p.Separable) :
    ∀ k : ℕ, k < p.natDegree →
      (Polynomial.derivative^[k] p).Separable := by
  intro k hk
  induction k with
  | zero => simpa using hsep
  | succ k induction =>
      rw [Function.iterate_succ_apply']
      apply separable_derivative_of_splits_separable_real
        (splits_iterateDerivative_of_splits_real hp k)
        (induction (by omega))
      rw [natDegree_iterateDerivative_real]
      omega

/-- Strict bounds containing all roots of a split separable polynomial also
contain all roots of its derivative. -/
theorem derivative_roots_strict_bounds
    {p : ℝ[X]} (hp : p.Splits) (hsep : p.Separable)
    {lower upper : ℝ}
    (hbound : ∀ z ∈ p.roots, lower < z ∧ z < upper) :
    ∀ z ∈ p.derivative.roots, lower < z ∧ z < upper := by
  intro z hz
  rw [← rolleRoots_coe_eq_derivativeRoots p hp hsep,
    Multiset.mem_coe, rolleRoots, List.mem_iff_get] at hz
  obtain ⟨i, hi⟩ := hz
  have hiBound : i.val < p.derivative.natDegree := by
    simpa [rolleRoots] using i.isLt
  let i' : Fin p.derivative.natDegree := ⟨i.val, hiBound⟩
  have hzEq : z = rolleRoot p hp hsep i' := by
    simpa [rolleRoots, i'] using hi.symm
  rw [hzEq]
  have hspec := rolleRoot_spec p hp hsep i'
  let left : Fin p.natDegree := ⟨i', by
    have hiLt := i'.isLt
    have hdegree : p.derivative.natDegree = p.natDegree - 1 :=
      Polynomial.natDegree_derivative p
    omega⟩
  let right : Fin p.natDegree := ⟨i' + 1, by
    have hiLt := i'.isLt
    have hdegree : p.derivative.natDegree = p.natDegree - 1 :=
      Polynomial.natDegree_derivative p
    omega⟩
  have hleft := hbound (voightSortedRoot p hp left)
    (voightSortedRoot_mem_roots hp left)
  have hright := hbound (voightSortedRoot p hp right)
    (voightSortedRoot_mem_roots hp right)
  constructor
  · exact hleft.1.trans hspec.1
  · exact hspec.2.1.trans hright.2

/-- Root bounds propagate through every nonconstant iterated derivative. -/
theorem iterateDerivative_roots_strict_bounds
    {p : ℝ[X]} (hp : p.Splits) (hsep : p.Separable)
    {lower upper : ℝ}
    (hbound : ∀ z ∈ p.roots, lower < z ∧ z < upper) :
    ∀ k : ℕ, k < p.natDegree →
      ∀ z ∈ (Polynomial.derivative^[k] p).roots,
        lower < z ∧ z < upper := by
  intro k hk
  induction k with
  | zero => simpa using hbound
  | succ k induction =>
      rw [Function.iterate_succ_apply']
      apply derivative_roots_strict_bounds
        (splits_iterateDerivative_of_splits_real hp k)
        (separable_iterateDerivative_of_splits_separable_real
          hp hsep k (by omega))
        (induction (by omega))

/-- Sorting the derivative roots returns the ordered Rolle-root list. -/
theorem rolleRoots_eq_derivativeSortedRoots
    (p : ℝ[X]) (hp : p.Splits) (hsep : p.Separable) :
    rolleRoots p hp hsep =
      voightSortedRoots p.derivative := by
  have hperm :
      (rolleRoots p hp hsep).Perm
        (voightSortedRoots p.derivative) := by
    rw [← Multiset.coe_eq_coe]
    rw [rolleRoots_coe_eq_derivativeRoots p hp hsep]
    exact Multiset.sort_eq p.derivative.roots
      (fun x y : ℝ => x ≤ y) |>.symm
  apply hperm.eq_of_sortedLE
  · exact (List.sortedLT_ofFn_iff.mpr
      (rolleRoot_strictMono p hp hsep)).sortedLE
  · rw [List.sortedLE_iff_pairwise]
    exact Multiset.pairwise_sort p.derivative.roots (· ≤ ·)

/-- The `i`-th sorted derivative root is the `i`-th chosen Rolle root. -/
theorem derivativeSortedRoot_eq_rolleRoot
    (p : ℝ[X]) (hp : p.Splits) (hsep : p.Separable)
    (i : Fin p.derivative.natDegree) :
    voightSortedRoot p.derivative
        (splits_derivative_of_splits_real hp) i =
      rolleRoot p hp hsep i := by
  have hlist := rolleRoots_eq_derivativeSortedRoots p hp hsep
  simp [voightSortedRoot, ← hlist, rolleRoots]

/-- The ordered roots of the derivative strictly interlace the ordered roots
of a split separable polynomial. -/
theorem derivativeSortedRoot_between_sortedRoots
    (p : ℝ[X]) (hp : p.Splits) (hsep : p.Separable)
    (i : Fin p.derivative.natDegree) :
    voightSortedRoot p hp ⟨i, by
      have hi := i.isLt
      have hdeg := Polynomial.natDegree_derivative p
      omega⟩ <
        voightSortedRoot p.derivative
          (splits_derivative_of_splits_real hp) i ∧
    voightSortedRoot p.derivative
        (splits_derivative_of_splits_real hp) i <
      voightSortedRoot p hp ⟨i + 1, by
        have hi := i.isLt
        have hdeg := Polynomial.natDegree_derivative p
        omega⟩ := by
  rw [derivativeSortedRoot_eq_rolleRoot p hp hsep i]
  exact ⟨(rolleRoot_spec p hp hsep i).1,
    (rolleRoot_spec p hp hsep i).2.1⟩

/-- A split separable polynomial with positive leading coefficient has the
expected alternating sign at every point between two consecutive ordered
roots. -/
theorem eval_sign_between_sortedRoots_of_leadingCoeff_pos {p : ℝ[X]}
    (hp : p.Splits) (hlead : 0 < p.leadingCoeff) (hsep : p.Separable)
    (i : Fin p.natDegree) (hi : i + 1 < p.natDegree) (x : ℝ)
    (hleft : voightSortedRoot p hp i ≤ x)
    (hright : x ≤ voightSortedRoot p hp ⟨i + 1, hi⟩) :
    0 ≤ (-1 : ℝ) ^ (p.natDegree - (i + 1)) * p.eval x := by
  let l := voightSortedRoots p
  have hlength : l.length = p.natDegree :=
    voightSortedRoots_length hp
  have hsorted : l.SortedLE :=
    (voightSortedRoots_sortedLT hsep).sortedLE
  have hleftAll : ∀ y ∈ l.take (i + 1), y ≤ x := by
    intro y hy
    obtain ⟨k, hk⟩ := List.get_of_mem hy
    have hklt : k.val < i + 1 := by
      have hkBound := k.isLt
      have htakeLength :
          (l.take (i.val + 1)).length =
            min (i.val + 1) l.length :=
        List.length_take
      omega
    let k' : Fin l.length := ⟨k.val, by omega⟩
    let leftIndex : Fin l.length := ⟨i, by omega⟩
    have hkle : k' ≤ leftIndex := by
      simp [k', leftIndex]
      omega
    have hrootLe : l.get k' ≤ l.get leftIndex :=
      hsorted.monotone_get hkle
    have hyget : l.get k' = y := by
      simpa [k', l, List.get_eq_getElem] using hk
    calc
      y = l.get k' := hyget.symm
      _ ≤ l.get leftIndex := hrootLe
      _ = voightSortedRoot p hp i := by
        simp [voightSortedRoot, leftIndex, l]
      _ ≤ x := hleft
  have hrightAll : ∀ y ∈ l.drop (i + 1), x ≤ y := by
    intro y hy
    obtain ⟨k, hk⟩ := List.get_of_mem hy
    let global : Fin l.length := ⟨i + 1 + k.val, by
      have hkBound := k.isLt
      have hdropLength :
          (l.drop (i + 1)).length = l.length - (i + 1) :=
        List.length_drop
      omega⟩
    let rightIndex : Fin l.length := ⟨i + 1, by omega⟩
    have hrle : rightIndex ≤ global := by
      simp [rightIndex, global]
    have hrootLe : l.get rightIndex ≤ l.get global :=
      hsorted.monotone_get hrle
    have hyget : l.get global = y := by
      simpa [global, l, List.get_eq_getElem, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hk
    calc
      x ≤ voightSortedRoot p hp ⟨i + 1, hi⟩ := hright
      _ = l.get rightIndex := by
        simp [voightSortedRoot, rightIndex, l]
      _ ≤ l.get global := hrootLe
      _ = y := hyget
  have hsign :=
    negOnePow_mul_listRootProduct_nonneg
      l (i + 1) x hleftAll hrightAll
  rw [hlength] at hsign
  have heval :
      p.eval x = p.leadingCoeff * (l.map fun y => x - y).prod :=
    eval_eq_leadingCoeff_mul_sortedRoots_product hp x
  rw [heval]
  rw [show (-1 : ℝ) ^ (p.natDegree - (i + 1)) *
      (p.leadingCoeff * (l.map fun y => x - y).prod) =
        p.leadingCoeff *
          ((-1 : ℝ) ^ (p.natDegree - (i + 1)) *
            (l.map fun y => x - y).prod) by ring]
  exact mul_nonneg hlead.le hsign

/-- The monic specialization of the alternating-sign theorem. -/
theorem eval_sign_between_sortedRoots {p : ℝ[X]}
    (hp : p.Splits) (hm : p.Monic) (hsep : p.Separable)
    (i : Fin p.natDegree) (hi : i + 1 < p.natDegree) (x : ℝ)
    (hleft : voightSortedRoot p hp i ≤ x)
    (hright : x ≤ voightSortedRoot p hp ⟨i + 1, hi⟩) :
    0 ≤ (-1 : ℝ) ^ (p.natDegree - (i + 1)) * p.eval x := by
  apply eval_sign_between_sortedRoots_of_leadingCoeff_pos
    hp (by simp [hm.leadingCoeff]) hsep i hi x hleft hright

/-- Evaluation at the `i`-th derivative root has the alternating sign used
to bound the next coefficient in Voight's recursion when the leading
coefficient is positive. -/
theorem eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
    {p : ℝ[X]} (hp : p.Splits) (hlead : 0 < p.leadingCoeff)
    (hsep : p.Separable)
    (i : Fin p.derivative.natDegree) :
    0 ≤ (-1 : ℝ) ^ (p.natDegree - (i + 1)) *
      p.eval (voightSortedRoot p.derivative
        (splits_derivative_of_splits_real hp) i) := by
  let ip : Fin p.natDegree := ⟨i, by
    have hi := i.isLt
    have hdeg := Polynomial.natDegree_derivative p
    omega⟩
  have hiNext : ip + 1 < p.natDegree := by
    have hi := i.isLt
    have hdeg := Polynomial.natDegree_derivative p
    change i.val + 1 < p.natDegree
    omega
  have hinterlace :=
    derivativeSortedRoot_between_sortedRoots p hp hsep i
  exact eval_sign_between_sortedRoots_of_leadingCoeff_pos
    hp hlead hsep ip hiNext _
    (by simpa [ip] using hinterlace.1.le)
    (by simpa [ip] using hinterlace.2.le)

/-- The monic specialization of the derivative-root sign theorem. -/
theorem eval_sign_at_derivativeSortedRoot {p : ℝ[X]}
    (hp : p.Splits) (hm : p.Monic) (hsep : p.Separable)
    (i : Fin p.derivative.natDegree) :
    0 ≤ (-1 : ℝ) ^ (p.natDegree - (i + 1)) *
      p.eval (voightSortedRoot p.derivative
        (splits_derivative_of_splits_real hp) i) := by
  apply eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
    hp (by simp [hm.leadingCoeff]) hsep i

/-- To the left of all roots, a split polynomial with positive leading
coefficient has sign `(-1) ^ degree`. -/
theorem eval_sign_left_of_all_roots_of_leadingCoeff_pos {p : ℝ[X]}
    (hp : p.Splits) (hlead : 0 < p.leadingCoeff) (x : ℝ)
    (hroot : ∀ y ∈ p.roots, x ≤ y) :
    0 ≤ (-1 : ℝ) ^ p.natDegree * p.eval x := by
  let l := voightSortedRoots p
  have hlength : l.length = p.natDegree :=
    voightSortedRoots_length hp
  have hright : ∀ y ∈ l.drop 0, x ≤ y := by
    intro y hy
    have hsortedMem : y ∈ l := by simpa using hy
    have hrootMem : y ∈ p.roots := by
      exact (Multiset.mem_sort
        (s := p.roots) (r := fun a b : ℝ => a ≤ b)).mp
          hsortedMem
    exact hroot y hrootMem
  have hsign := negOnePow_mul_listRootProduct_nonneg
    l 0 x (by simp) hright
  rw [hlength, Nat.sub_zero] at hsign
  have heval :
      p.eval x = p.leadingCoeff * (l.map fun y => x - y).prod :=
    eval_eq_leadingCoeff_mul_sortedRoots_product hp x
  rw [heval]
  rw [show (-1 : ℝ) ^ p.natDegree *
      (p.leadingCoeff * (l.map fun y => x - y).prod) =
        p.leadingCoeff *
          ((-1 : ℝ) ^ p.natDegree *
            (l.map fun y => x - y).prod) by ring]
  exact mul_nonneg hlead.le hsign

/-- The monic specialization of the left-endpoint sign theorem. -/
theorem eval_sign_left_of_all_roots {p : ℝ[X]}
    (hp : p.Splits) (hm : p.Monic) (x : ℝ)
    (hroot : ∀ y ∈ p.roots, x ≤ y) :
    0 ≤ (-1 : ℝ) ^ p.natDegree * p.eval x := by
  apply eval_sign_left_of_all_roots_of_leadingCoeff_pos
    hp (by simp [hm.leadingCoeff]) x hroot

/-- To the right of all roots, a split polynomial with positive leading
coefficient is nonnegative. -/
theorem eval_nonneg_right_of_all_roots_of_leadingCoeff_pos {p : ℝ[X]}
    (hp : p.Splits) (hlead : 0 < p.leadingCoeff) (x : ℝ)
    (hroot : ∀ y ∈ p.roots, y ≤ x) :
    0 ≤ p.eval x := by
  let l := voightSortedRoots p
  have hleft : ∀ y ∈ l.take l.length, y ≤ x := by
    intro y hy
    have hsortedMem : y ∈ l := by simpa using hy
    have hrootMem : y ∈ p.roots := by
      exact (Multiset.mem_sort
        (s := p.roots) (r := fun a b : ℝ => a ≤ b)).mp
          hsortedMem
    exact hroot y hrootMem
  have hsign := negOnePow_mul_listRootProduct_nonneg
    l l.length x hleft (by simp)
  simp only [Nat.sub_self, pow_zero, one_mul] at hsign
  have heval :
      p.eval x = p.leadingCoeff * (l.map fun y => x - y).prod :=
    eval_eq_leadingCoeff_mul_sortedRoots_product hp x
  rw [heval]
  exact mul_nonneg hlead.le hsign

/-- The monic specialization of the right-endpoint sign theorem. -/
theorem eval_nonneg_right_of_all_roots {p : ℝ[X]}
    (hp : p.Splits) (hm : p.Monic) (x : ℝ)
    (hroot : ∀ y ∈ p.roots, y ≤ x) :
    0 ≤ p.eval x := by
  apply eval_nonneg_right_of_all_roots_of_leadingCoeff_pos
    hp (by simp [hm.leadingCoeff]) x hroot

/-- The normalized derivative stage used in Voight's coefficient recursion.
The scalar normalization does not affect its roots. -/
noncomputable def voightDerivativeStage (p : ℝ[X]) (k : ℕ) :
    ℝ[X] :=
  C (((k.factorial : ℕ) : ℝ)⁻¹) *
    (Polynomial.derivative^[k] p)

/-- Factorial normalization does not change the roots of a derivative stage. -/
theorem voightDerivativeStage_roots (p : ℝ[X]) (k : ℕ) :
    (voightDerivativeStage p k).roots =
      (Polynomial.derivative^[k] p).roots := by
  rw [voightDerivativeStage, Polynomial.roots_C_mul]
  positivity

/-- A normalized derivative stage of a real-split polynomial is real-split. -/
theorem voightDerivativeStage_splits {p : ℝ[X]}
    (hp : p.Splits) (k : ℕ) :
    (voightDerivativeStage p k).Splits := by
  exact (splits_iterateDerivative_of_splits_real hp k).C_mul _

/-- A nonconstant normalized derivative stage of a split separable real
polynomial is separable. -/
theorem voightDerivativeStage_separable {p : ℝ[X]}
    (hp : p.Splits) (hsep : p.Separable) {k : ℕ}
    (hk : k < p.natDegree) :
    (voightDerivativeStage p k).Separable := by
  have hiter : (Polynomial.derivative^[k] p).Separable :=
    separable_iterateDerivative_of_splits_separable_real hp hsep k hk
  have hfactorial : (((k.factorial : ℕ) : ℝ)⁻¹) ≠ 0 := by
    positivity
  have hunit : IsUnit (C (((k.factorial : ℕ) : ℝ)⁻¹) : ℝ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hfactorial)
  have hassociated : Associated
      (Polynomial.derivative^[k] p)
      (C (((k.factorial : ℕ) : ℝ)⁻¹) *
        (Polynomial.derivative^[k] p)) := by
    simpa using
      ((associated_one_iff_isUnit.mpr hunit).mul_right
        (Polynomial.derivative^[k] p)).symm
  exact hassociated.separable hiter

/-- Strict root bounds for the source polynomial propagate to every
nonconstant normalized derivative stage. -/
theorem voightDerivativeStage_roots_strict_bounds
    {p : ℝ[X]} (hp : p.Splits) (hsep : p.Separable)
    {lower upper : ℝ}
    (hbound : ∀ z ∈ p.roots, lower < z ∧ z < upper)
    {k : ℕ} (hk : k < p.natDegree) :
    ∀ z ∈ (voightDerivativeStage p k).roots,
      lower < z ∧ z < upper := by
  rw [voightDerivativeStage_roots]
  exact iterateDerivative_roots_strict_bounds hp hsep hbound k hk

/-- Factorial normalization preserves the exact degree of a derivative
stage. -/
theorem voightDerivativeStage_natDegree (p : ℝ[X]) (k : ℕ) :
    (voightDerivativeStage p k).natDegree = p.natDegree - k := by
  rw [voightDerivativeStage,
    Polynomial.natDegree_C_mul]
  · exact natDegree_iterateDerivative_real p k
  · positivity

/-- The coefficient formula used to evaluate a derivative stage with exact
rational arithmetic. -/
theorem voightDerivativeStage_coeff (p : ℝ[X]) (k m : ℕ) :
    (voightDerivativeStage p k).coeff m =
      (((k.factorial : ℕ) : ℝ)⁻¹) *
        ((m + k).descFactorial k : ℝ) * p.coeff (m + k) := by
  rw [voightDerivativeStage, Polynomial.coeff_C_mul,
    Polynomial.coeff_iterate_derivative]
  simp only [nsmul_eq_mul]
  ring

/-- Every normalized derivative stage up to the degree of a monic polynomial
has positive leading coefficient. -/
theorem voightDerivativeStage_leadingCoeff_pos {p : ℝ[X]}
    (hm : p.Monic) {k : ℕ} (hk : k ≤ p.natDegree) :
    0 < (voightDerivativeStage p k).leadingCoeff := by
  rw [Polynomial.leadingCoeff, voightDerivativeStage_natDegree,
    voightDerivativeStage_coeff, Nat.sub_add_cancel hk,
    hm.coeff_natDegree, mul_one]
  exact mul_pos (by positivity)
    (by exact_mod_cast (Nat.descFactorial_pos.mpr hk))

/-- Adding the coefficient of `X ^ k` translates the normalized `k`-th
derivative by exactly that coefficient.  This is the algebraic identity behind
Voight's one-coefficient-at-a-time Rolle bounds. -/
theorem voightDerivativeStage_add_coefficient
    (p : ℝ[X]) (a : ℝ) (k : ℕ) :
    voightDerivativeStage (p + C a * X ^ k) k =
      voightDerivativeStage p k + C a := by
  rw [voightDerivativeStage, voightDerivativeStage]
  rw [show Polynomial.derivative^[k] (p + C a * X ^ k) =
      Polynomial.derivative^[k] p +
        Polynomial.derivative^[k] (C a * X ^ k) by
    simpa only [← Module.End.pow_apply] using
      (map_add (Polynomial.derivative ^ k) p (C a * X ^ k))]
  rw [Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul]
  rw [mul_add, add_left_cancel_iff]
  simp only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one]
  change C (((k.factorial : ℕ) : ℝ)⁻¹) *
      (C a * C ((k.factorial : ℕ) : ℝ)) = C a
  rw [← C_mul, ← C_mul]
  congr 1
  field_simp

/-- A coefficient below a derivative stage has no effect on that stage. -/
theorem voightDerivativeStage_add_lowerCoefficient
    (p : ℝ[X]) (a : ℝ) {k j : ℕ} (hkj : k < j) :
    voightDerivativeStage (p + C a * X ^ k) j =
      voightDerivativeStage p j := by
  rw [voightDerivativeStage, voightDerivativeStage]
  rw [show Polynomial.derivative^[j] (p + C a * X ^ k) =
      Polynomial.derivative^[j] p +
        Polynomial.derivative^[j] (C a * X ^ k) by
    simpa only [← Module.End.pow_apply] using
      (map_add (Polynomial.derivative ^ j) p (C a * X ^ k))]
  rw [Polynomial.iterate_derivative_C_mul]
  have hzero : Polynomial.derivative^[j] (X ^ k : ℝ[X]) = 0 :=
    Polynomial.iterate_derivative_eq_zero (by simpa using hkj)
  rw [hzero]
  simp

end TraceEuclidean
