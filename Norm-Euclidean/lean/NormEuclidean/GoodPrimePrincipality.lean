import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

namespace NormEuclidean

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Every nonzero maximal ideal admits a coprime integral representative of its
inverse ideal class, with a nonzero generator for the product. -/
theorem exists_coprime_ideal_mul_eq_span (p : Ideal R)
    (hp : p.IsMaximal) (hp0 : p ≠ ⊥) :
    ∃ i : Ideal R, i ≠ ⊥ ∧ IsCoprime i p ∧
      ∃ a : R, a ≠ 0 ∧ i * p = Ideal.span {a} := by
  obtain ⟨a, ha, ha2⟩ := p.exists_mem_pow_notMem_pow_succ hp0 hp.ne_top 1
  simp only [pow_one] at ha
  have ha0 : a ≠ 0 := by
    intro h
    exact ha2 (h ▸ Ideal.zero_mem _)
  obtain ⟨i, hi⟩ := Ideal.dvd_span_singleton.mpr ha
  have hip : i * p = Ideal.span {a} := by simpa [mul_comm] using hi.symm
  have hi0 : i ≠ ⊥ := by
    intro h
    have : Ideal.span ({a} : Set R) = ⊥ := by simpa [h] using hip.symm
    exact ha0 (Ideal.span_singleton_eq_bot.mp this)
  have hinp : ¬ i ≤ p := by
    intro h
    apply ha2
    have hle : Ideal.span ({a} : Set R) ≤ p ^ 2 := by
      rw [← hip, pow_two]
      exact Ideal.mul_mono_left h
    exact hle (Ideal.mem_span_singleton_self a)
  refine ⟨i, hi0, Ideal.isCoprime_iff_sup_eq.mpr ?_, a, ha0, hip⟩
  by_contra h
  have heq : p = i ⊔ p := hp.eq_of_le h le_sup_right
  exact hinp (heq ▸ le_sup_left)

/-- Cancelling a nonzero principal ideal from a principal product preserves
principality. -/
theorem isPrincipal_of_mul_eq_span (i p : Ideal R) (hi : i ≠ ⊥)
    [i.IsPrincipal] {a : R} (hgen : i * p = Ideal.span {a}) : p.IsPrincipal := by
  let b := Submodule.IsPrincipal.generator i
  have hb : Ideal.span ({b} : Set R) = i := Ideal.span_singleton_generator i
  have hai : a ∈ i := by
    have hle : Ideal.span ({a} : Set R) ≤ i := by
      rw [← hgen]
      exact Ideal.mul_le_right
    exact hle (Ideal.mem_span_singleton_self a)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hb.symm ▸ hai)
  have hprod : i * p = i * Ideal.span {c} := by
    rw [hgen, ← hb, Ideal.span_singleton_mul_span_singleton, hc]
  have hp : p = Ideal.span {c} := mul_left_cancel₀ hi hprod
  rw [hp]
  infer_instance

/-- Principality cancels from a nonzero principal factor of a principal product. -/
theorem isPrincipal_of_mul_isPrincipal (p i : Ideal R) (hi : i ≠ ⊥)
    [i.IsPrincipal] [(p * i).IsPrincipal] : p.IsPrincipal := by
  apply isPrincipal_of_mul_eq_span i p hi
  rw [mul_comm]
  exact (Ideal.span_singleton_generator (p * i)).symm

end NormEuclidean
