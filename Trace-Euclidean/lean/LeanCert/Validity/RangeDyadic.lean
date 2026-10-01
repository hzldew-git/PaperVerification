import LeanCert.Validity.IntegrationDyadic

/-!
# Checked range bounds on dyadic interval partitions

The checker evaluates an expression on every cell of a certified covering
partition.  The bridge theorem then gives a pointwise bound on the whole
interval.  This is useful for derivative bounds in rigorous quadrature.
-/

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic

namespace LeanCert.Validity.RangeDyadic

/-- Check domains and a common two-sided range bound on every partition cell. -/
def checkRangeDyadicList (e : Expr) (parts : List IntervalRat)
    (lower upper : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  parts.all fun J =>
    let Jd := IntervalDyadic.ofIntervalRat J cfg.precision
    let result := LeanCert.Internal.Dyadic.evalUnchecked e (fun _ => Jd) cfg
    checkDomainValidDyadic e (fun _ => Jd) cfg &&
      decide (lower ≤ result.lo.toRat ∧ result.hi.toRat ≤ upper)

/-- A self-contained range check, including exact coverage of the target interval. -/
def checkRangeDyadicListFull (e : Expr) (parts : List IntervalRat) (I : IntervalRat)
    (lower upper : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  checkListPartitionCovers parts I && checkRangeDyadicList e parts lower upper cfg

private theorem exists_part_mem_of_covers (parts : List IntervalRat) (I : IntervalRat)
    (hcover : ListPartitionCovers parts I) {x : ℝ}
    (hx : x ∈ Set.Icc (I.lo : ℝ) I.hi) :
    ∃ J ∈ parts, x ∈ J := by
  induction parts generalizing I with
  | nil => exact (hcover.nonempty rfl).elim
  | cons p ps ih =>
    cases ps with
    | nil =>
      refine ⟨p, by simp, ?_⟩
      have hlo : p.lo = I.lo := by simpa using hcover.head_lo
      have hhi : p.hi = I.hi := by simpa using hcover.last_hi
      exact ⟨by exact_mod_cast hlo.symm ▸ hx.1, by exact_mod_cast hhi.symm ▸ hx.2⟩
    | cons q qs =>
      by_cases hxp : x ≤ (p.hi : ℝ)
      · refine ⟨p, by simp, ?_⟩
        have hlo : p.lo = I.lo := by simpa using hcover.head_lo
        exact ⟨by exact_mod_cast hlo.symm ▸ hx.1, hxp⟩
      · have hpq : p.hi = q.lo := by
          simpa using hcover.adjacent 0 (by simp)
        let I' : IntervalRat := ⟨q.lo, I.hi, by
          have : (q.lo : ℝ) ≤ I.hi := by
            rw [← hpq]
            exact (lt_of_not_ge hxp).le.trans hx.2
          exact_mod_cast this⟩
        have htail : ListPartitionCovers (q :: qs) I' := by
          refine ⟨by simp, rfl, ?_, ?_⟩
          · simpa [I'] using hcover.last_hi
          · intro k hk
            have hfull := hcover.adjacent (k + 1) (by simpa using hk)
            simpa [Nat.add_assoc] using hfull
        have hx' : x ∈ Set.Icc (I'.lo : ℝ) I'.hi := by
          constructor
          · dsimp [I']
            rw [← hpq]
            exact (lt_of_not_ge hxp).le
          · exact hx.2
        obtain ⟨J, hJ, hxJ⟩ := ih I' htail hx'
        exact ⟨J, by simp [hJ], hxJ⟩

/-- A successful list check gives a pointwise real range bound. -/
theorem range_bounds_of_check_dyadic_list (e : Expr) (parts : List IntervalRat)
    (I : IntervalRat) (lower upper : ℚ) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0)
    (hcheck : checkRangeDyadicListFull e parts I lower upper cfg = true) :
    ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi,
      (lower : ℝ) ≤ Expr.eval (fun _ => x) e ∧ Expr.eval (fun _ => x) e ≤ (upper : ℝ) := by
  simp only [checkRangeDyadicListFull, Bool.and_eq_true] at hcheck
  have hcover := checkListPartitionCovers_correct parts I hcheck.1
  unfold checkRangeDyadicList at hcheck
  rw [List.all_eq_true] at hcheck
  intro x hx
  obtain ⟨J, hJ, hxJ⟩ := exists_part_mem_of_covers parts I hcover hx
  have hcell := hcheck.2 J hJ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
  let Jd := IntervalDyadic.ofIntervalRat J cfg.precision
  have henv : envMemDyadic (fun _ => x) (fun _ => Jd) := by
    intro i
    exact IntervalDyadic.mem_ofIntervalRat hxJ cfg.precision hprec
  have hmem := evalIntervalDyadic_correct_of_domain e _ _ henv cfg hprec
    (checkDomainValidDyadic_correct _ _ _ hcell.1)
  have hrat := IntervalDyadic.mem_toIntervalRat.mpr hmem
  constructor
  · exact le_trans (by exact_mod_cast hcell.2.1) hrat.1
  · exact le_trans hrat.2 (by exact_mod_cast hcell.2.2)

end LeanCert.Validity.RangeDyadic
