import Mathlib

/-!
Finite-parameter assembly lemmas used by the finiteness argument.  Analytic
and arithmetic inputs are kept explicit.
-/

namespace TraceEuclidean

/-- A finite set of keys with finite fibers gives a finite total family. -/
theorem finite_of_finite_keys_and_fibers {α β : Type*}
    (P : α → Prop) (key : α → β) (keys : Set β)
    (hkeys : keys.Finite)
    (hmem : ∀ a, P a → key a ∈ keys)
    (hfiber : ∀ b, {a | P a ∧ key a = b}.Finite) :
    {a | P a}.Finite := by
  apply Set.Finite.of_finite_fibers key
  · exact hkeys.subset fun b hb ↦ by
      obtain ⟨a, ha, rfl⟩ := hb
      exact hmem a ha
  · intro b _hb
    exact (hfiber b).subset fun a ha ↦
      ⟨ha.1, by simpa using ha.2⟩

/-- Eventual nonpositivity leaves only finitely many positive integer inputs. -/
theorem finite_positive_of_eventually_nonpositive {h : ℕ → ℝ}
    (hbound : ∃ N, ∀ n, N ≤ n → h n ≤ 0) :
    Set.Finite {n | 0 < h n} := by
  obtain ⟨N, hN⟩ := hbound
  apply (Set.finite_Iio N).subset
  intro n hn
  change 0 < h n at hn
  change n < N
  by_contra hnot
  exact (not_lt_of_ge (hN n (Nat.le_of_not_gt hnot))) hn

/-- A function tending to minus infinity is eventually nonpositive. -/
theorem finite_positive_of_tendsto_atTop_atBot {h : ℕ → ℝ}
    (hh : Filter.Tendsto h Filter.atTop Filter.atBot) :
    Set.Finite {n | 0 < h n} := by
  have hevent : ∀ᶠ n in Filter.atTop, h n < 0 :=
    hh (Filter.eventually_lt_atBot (0 : ℝ))
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hevent)
  exact finite_positive_of_eventually_nonpositive
    ⟨N, fun n hn ↦ le_of_lt (hN n hn)⟩

/-- A set of rank-degree pairs contained in a finite rectangle is finite. -/
theorem finite_parameter_pairs_of_bounds (P : ℕ → ℕ → Prop) (N D : ℕ)
    (hbound : ∀ n d, P n d → n < N ∧ d < D) :
    Set.Finite {p : ℕ × ℕ | P p.1 p.2} := by
  apply ((Set.finite_Iio N).prod (Set.finite_Iio D)).subset
  intro p hp
  exact hbound p.1 p.2 hp

/-- A finite set of parameter values with finite fibers has a finite total family. -/
theorem finite_sigma_family {ι : Type*} (s : Set ι) (β : ι → Type*)
    (hs : s.Finite) (hβ : ∀ i ∈ s, Finite (β i)) :
    Finite (Σ i : s, β i.1) := by
  classical
  letI : Fintype s := hs.fintype
  letI (i : s) : Finite (β i.1) := hβ i.1 i.2
  infer_instance

end TraceEuclidean
