import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import NormEuclidean.GoodPrimePrincipality

namespace NormEuclidean

open Ideal UniqueFactorizationMonoid

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- An ideal whose prime divisors are principal is principal. -/
theorem ideal_isPrincipal_of_prime_divisors (I : Ideal R)
    (h : ∀ p : Ideal R, Prime p → p ∣ I → p.IsPrincipal) : I.IsPrincipal := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact ⟨⟨0, (Submodule.span_singleton_eq_bot.mpr rfl).symm⟩⟩
  | h₂ I hI =>
    have : I = ⊤ := Ideal.isUnit_iff.mp hI
    subst I
    exact inferInstance
  | h₃ I p hI hp ih =>
    have hp' := h p hp (dvd_mul_right p I)
    have hI' := ih (fun q hq hd => h q hq (dvd_mul_of_dvd_right hd p))
    obtain ⟨a, ha⟩ := hp'.principal
    obtain ⟨b, hb⟩ := hI'.principal
    refine ⟨⟨a * b, ?_⟩⟩
    rw [ha, hb]
    exact Ideal.span_singleton_mul_span_singleton a b

/-- Choose an element with valuation one at a chosen prime and zero at all
other prime divisors of a prescribed nonzero element. -/
theorem exists_mem_prime_not_square_avoiding (d : R) (hd : d ≠ 0)
    (p : Ideal R) (hp : Prime p) :
    ∃ b : R, b ∈ p ∧ b ∉ p ^ 2 ∧
      ∀ q : Ideal R, Prime q → d ∈ q → q ≠ p → b ∉ q := by
  classical
  let s : Finset (Ideal R) := insert p (normalizedFactors (Ideal.span {d})).toFinset
  have hspan : Ideal.span ({d} : Set R) ≠ ⊥ := by simpa using hd
  have hs : ∀ q ∈ s, Prime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact prime_of_normalized_factor q (Multiset.mem_toFinset.mp hq)
  obtain ⟨a, ha, ha2⟩ := p.exists_mem_pow_notMem_pow_succ hp.ne_zero
    (Ideal.isPrime_of_prime hp).ne_top 1
  simp only [pow_one] at ha
  let e : Ideal R → ℕ := fun q => if q = p then 2 else 1
  let x : s → R := fun q => if (q : Ideal R) = p then a else 1
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := s) id e hs (fun _ _ _ _ h => h) x
  have hb2 : b - a ∈ p ^ 2 := by
    simpa [e, x] using hb p (Finset.mem_insert_self _ _)
  have hbp : b ∈ p := by
    have hba : b - a ∈ p := (Ideal.pow_le_self (by omega)) hb2
    simpa using p.add_mem hba ha
  refine ⟨b, hbp, ?_, ?_⟩
  · intro h
    exact ha2 (by simpa using (p ^ 2).sub_mem h hb2)
  · intro q hq hdq hqp hbq
    have hqs : q ∈ s := Finset.mem_insert_of_mem <| Multiset.mem_toFinset.mpr <|
      (Ideal.mem_normalizedFactors_iff hspan).mpr
        ⟨Ideal.isPrime_of_prime hq, Ideal.span_le.mpr (by simpa using hdq)⟩
    have hbq1 : b - 1 ∈ q := by simpa [e, x, hqp] using hb q hqs
    have hone : (1 : R) ∈ q := by simpa using q.sub_mem hbq hbq1
    exact (Ideal.isPrime_of_prime hq).ne_top (Ideal.eq_top_of_isUnit_mem q hone isUnit_one)

/-- If every nonzero maximal ideal away from one nonzero element is principal,
then the Dedekind domain is a principal ideal ring. -/
theorem isPrincipalIdealRing_of_principal_primes_away (d : R) (hd : d ≠ 0)
    (hgood : ∀ p : Ideal R, p.IsMaximal → p ≠ ⊥ → d ∉ p → p.IsPrincipal) :
    IsPrincipalIdealRing R := by
  have hprime : ∀ p : Ideal R, Prime p → p.IsPrincipal := by
    intro p hp
    have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    by_cases hdp : d ∈ p
    · obtain ⟨b, hbp, hb2, hbavoid⟩ := exists_mem_prime_not_square_avoiding d hd p hp
      have hb0 : b ≠ 0 := by
        intro heq
        exact hb2 (heq ▸ (p ^ 2).zero_mem)
      have hspan : Ideal.span ({b} : Set R) ≠ ⊥ := by simpa using hb0
      have hdiv : p ∣ Ideal.span ({b} : Set R) :=
        Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (by simpa using hbp))
      obtain ⟨J, hJ⟩ := hdiv
      have hJ0 : J ≠ ⊥ := by
        intro heq
        apply hspan
        simpa [heq] using hJ
      have hJprincipal : J.IsPrincipal := ideal_isPrincipal_of_prime_divisors J (by
        intro q hq hqJ
        apply hgood q ((Ideal.isPrime_of_prime hq).isMaximal hq.ne_zero) hq.ne_zero
        intro hdq
        by_cases hqp : q = p
        · subst q
          have hsq : p ^ 2 ∣ Ideal.span ({b} : Set R) := by
            rw [hJ, pow_two]
            exact mul_dvd_mul_left p hqJ
          exact hb2 ((Ideal.dvd_iff_le.mp hsq) (Ideal.mem_span_singleton_self b))
        · apply hbavoid q hq hdq hqp
          have hqb : q ∣ Ideal.span ({b} : Set R) := by
            rw [hJ]
            exact dvd_mul_of_dvd_right hqJ p
          exact (Ideal.dvd_iff_le.mp hqb) (Ideal.mem_span_singleton_self b))
      letI := hJprincipal
      have hprod : (p * J).IsPrincipal := by
        rw [← hJ]
        exact inferInstance
      letI := hprod
      exact isPrincipal_of_mul_isPrincipal p J hJ0
    · exact hgood p hpmax hp.ne_zero hdp
  exact ⟨fun I => ideal_isPrincipal_of_prime_divisors I (fun p hp _ => hprime p hp)⟩

end NormEuclidean
