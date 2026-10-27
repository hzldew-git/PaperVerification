import NormEuclidean.Lattice
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Cast.Order

/-!
# Norm descent on arbitrary integral submodules

The descent measure is natural valued on integral scalars. The approximation
hypothesis uses the multiplicative rational-valued absolute norm. These are
separate fields: no Euclidean remainder algorithm is assumed. In the number
field application the two functions are the actual absolute field norm and
its integral natural value.
-/

namespace NormEuclidean

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The arithmetic facts needed by norm descent. Values of `measure` outside
`R` are immaterial. The number field instance uses the absolute field norm. -/
structure IntegralNorm (R : Subring K) where
  norm : K → ℚ
  measure : K → ℕ
  map_mul : ∀ a b, norm (a * b) = norm a * norm b
  map_neg : ∀ a, norm (-a) = norm a
  pos : ∀ a, a ≠ 0 → 0 < norm a
  measure_spec : ∀ a, a ∈ R → (measure a : ℚ) = norm a

/-- The manuscript's approximation property, without a freeness assumption. -/
def IsNormEuclidean {R : Subring K} (N : IntegralNorm R)
    (Q : QuadraticForm K V) (L : Submodule R V) : Prop :=
  ∀ x : V, ∃ u ∈ L, N.norm (Q (x - u)) < 1

namespace Hyperbolic

variable {R : Subring K} (Q : QuadraticForm K V) (L : Submodule R V)

/-- Unit scaling of the hyperbolic plane. -/
def diagonalEquiv (c : K) (hc : c ≠ 0) :
    Hyperbolic K V ≃ₗ[K] Hyperbolic K V where
  toFun := fun z => (z.1, c⁻¹ * z.2.1, c * z.2.2)
  invFun := fun z => (z.1, c * z.2.1, c⁻¹ * z.2.2)
  left_inv := by
    intro z
    ext <;> simp [hc]
  right_inv := by
    intro z
    ext <;> simp [hc]
  map_add' := by
    intro x y
    ext <;> simp [mul_add]
  map_smul' := by
    intro a z
    ext <;> simp [smul_eq_mul] <;> ring

/-- The diagonal scaling is integral when both `c` and its inverse lie in R. -/
def Aut.diagonal (c : K) (hc0 : c ≠ 0) (hc : c ∈ R) (hci : c⁻¹ ∈ R) :
    Aut (Q := Q) L where
  toLinearEquiv := diagonalEquiv c hc0
  q_eq := by
    intro z
    change Q z.1 + (c⁻¹ * z.2.1) * (c * z.2.2) = Q z.1 + z.2.1 * z.2.2
    congr 1
    calc
      (c⁻¹ * z.2.1) * (c * z.2.2) = (c⁻¹ * c) * (z.2.1 * z.2.2) := by ring
      _ = z.2.1 * z.2.2 := by simp [hc0]
  mem_iff := by
    intro z
    change (z.1 ∈ L ∧ c⁻¹ * z.2.1 ∈ R ∧ c * z.2.2 ∈ R) ↔
      (z.1 ∈ L ∧ z.2.1 ∈ R ∧ z.2.2 ∈ R)
    constructor
    · rintro ⟨hv, ha, hb⟩
      refine ⟨hv, ?_, ?_⟩
      · simpa [← mul_assoc, hc0] using R.mul_mem hc ha
      · simpa [← mul_assoc, hc0] using R.mul_mem hci hb
    · rintro ⟨hv, ha, hb⟩
      exact ⟨hv, R.mul_mem hci ha, R.mul_mem hc hb⟩

@[simp] theorem Aut.diagonal_apply_smul_e (c : K) (hc0 : c ≠ 0)
    (hc : c ∈ R) (hci : c⁻¹ ∈ R) :
    Aut.diagonal Q L c hc0 hc hci (c • (e : Hyperbolic K V)) = e := by
  simp [Aut.diagonal, diagonalEquiv, e, hc0]

/-- A nonzero isotropic vector has a nonzero hyperbolic coordinate. -/
theorem coordinate_ne_zero (hA : Q.Anisotropic) {z : Hyperbolic K V}
    (hz : z ≠ 0) (hiso : q Q z = 0) : z.2.1 ≠ 0 ∨ z.2.2 ≠ 0 := by
  by_contra h
  push_neg at h
  have hv : z.1 = 0 := hA _ (by simpa [q, h.1, h.2] using hiso)
  exact hz (by ext <;> simp [hv, h.1, h.2])

/-- One norm-Euclidean approximation gives a strictly smaller second
coordinate after the explicit integral transvection. -/
theorem exists_reducing_transvection (N : IntegralNorm R)
    (hQ : ∀ v ∈ L, Q v ∈ R) (hE : IsNormEuclidean N Q L)
    {z : Hyperbolic K V} (hz : Mem L z) (hiso : q Q z = 0)
    (ha : z.2.1 ≠ 0) :
    ∃ u ∈ L, N.measure (transvection Q u z).2.2 < N.measure z.2.1 := by
  obtain ⟨u, hu, happ⟩ := hE (z.2.1⁻¹ • z.1)
  refine ⟨u, hu, ?_⟩
  have hT : Mem L (transvection Q u z) := mem_transvection L hQ hu hz
  have hlt : N.norm (transvection Q u z).2.2 < N.norm z.2.1 := by
    rw [descent_identity Q z u hiso ha, N.map_mul, N.map_neg]
    simpa using mul_lt_mul_of_pos_left happ (N.pos _ ha)
  rw [← N.measure_spec _ hT.2.2, ← N.measure_spec _ hz.2.1] at hlt
  exact_mod_cast hlt

/-- Lemma 2.4, orbit-normal-form assertion. The minimum is taken over natural
norms of nonzero first hyperbolic coordinates in the entire integral orbit.
Finite generation and freeness of `L` are not used. -/
theorem norm_descent (N : IntegralNorm R)
    (hQ : ∀ v ∈ L, Q v ∈ R) (hA : Q.Anisotropic)
    (hE : IsNormEuclidean N Q L)
    {z : Hyperbolic K V} (hz : Mem L z) (hz0 : z ≠ 0) (hiso : q Q z = 0) :
    ∃ g : Aut (Q := Q) L, ∃ c : K,
      c ∈ R ∧ c ≠ 0 ∧ g z = c • (e : Hyperbolic K V) := by
  classical
  have hstart : ∃ g : Aut (Q := Q) L, (g z).2.1 ≠ 0 := by
    rcases coordinate_ne_zero Q hA hz0 hiso with ha | hb
    · exact ⟨Aut.refl L, ha⟩
    · exact ⟨Aut.swap L, hb⟩
  let P : ℕ → Prop := fun n => ∃ g : Aut (Q := Q) L,
    (g z).2.1 ≠ 0 ∧ N.measure (g z).2.1 = n
  have hex : ∃ n, P n := by
    obtain ⟨g, hg⟩ := hstart
    exact ⟨N.measure (g z).2.1, g, hg, rfl⟩
  obtain ⟨g₀, ha, hmin⟩ := Nat.find_spec hex
  have hz₀ : Mem L (g₀ z) := (g₀.mem_iff z).mpr hz
  have hiso₀ : q Q (g₀ z) = 0 := (g₀.q_eq z).trans hiso
  obtain ⟨u, hu, hdecrease⟩ :=
    exists_reducing_transvection Q L N hQ hE hz₀ hiso₀ ha
  let g₁ : Aut (Q := Q) L := Aut.comp L (Aut.transvection L hQ u hu) g₀
  have hzero : (g₁ z).2.2 = 0 := by
    by_contra hb
    have hcandidate : P (N.measure (g₁ z).2.2) := by
      refine ⟨Aut.comp L (Aut.swap L) g₁, ?_, ?_⟩
      · exact hb
      · rfl
    have hbound := Nat.find_min' hex hcandidate
    rw [← hmin] at hbound
    exact (not_lt_of_ge hbound) hdecrease
  have hiso₁ : q Q (g₁ z) = 0 := (g₁.q_eq z).trans hiso
  have hv : (g₁ z).1 = 0 := hA _ (by simpa [q, hzero] using hiso₁)
  refine ⟨g₁, (g₀ z).2.1, hz₀.2.1, ha, ?_⟩
  apply Prod.ext
  · simpa [e] using hv
  · apply Prod.ext
    · simp [g₁, e, transvection]
    · simpa [e] using hzero

/-- The coefficient-set form of the content conclusion of Lemma 2.4.
For a full lattice over a Dedekind domain, taking inverse fractional ideals
turns this identity into `content(z) = cR`. -/
theorem norm_descent_with_coefficients (N : IntegralNorm R)
    (hQ : ∀ v ∈ L, Q v ∈ R) (hA : Q.Anisotropic)
    (hE : IsNormEuclidean N Q L)
    {z : Hyperbolic K V} (hz : Mem L z) (hz0 : z ≠ 0) (hiso : q Q z = 0) :
    ∃ g : Aut (Q := Q) L, ∃ c : K,
      c ∈ R ∧ c ≠ 0 ∧ g z = c • (e : Hyperbolic K V) ∧
      coefficientSet L z = {a | a * c ∈ R} := by
  obtain ⟨g, c, hc, hc0, hg⟩ := norm_descent Q L N hQ hA hE hz hz0 hiso
  refine ⟨g, c, hc, hc0, hg, ?_⟩
  rw [← coefficientSet_aut L g z, hg, coefficientSet_smul_e]

/-- Primitive isotropic vectors are in the orbit of `e`. The explicit
nonzero condition is essential for the coefficient-set formulation over a
general subring; the manuscript's definition of content also excludes zero. -/
theorem primitive_orbit_transitivity (N : IntegralNorm R)
    (hQ : ∀ v ∈ L, Q v ∈ R) (hA : Q.Anisotropic)
    (hE : IsNormEuclidean N Q L)
    {z : Hyperbolic K V} (hz : Mem L z) (hz0 : z ≠ 0) (hiso : q Q z = 0)
    (hprimitive : coefficientSet L z = (R : Set K)) :
    ∃ g : Aut (Q := Q) L, g z = (e : Hyperbolic K V) := by
  obtain ⟨g, c, hc, hc0, hg, hcoeff⟩ :=
    norm_descent_with_coefficients Q L N hQ hA hE hz hz0 hiso
  have hci : c⁻¹ ∈ R := by
    have hset : {a : K | a * c ∈ R} = (R : Set K) := hcoeff.symm.trans hprimitive
    change c⁻¹ ∈ (R : Set K)
    rw [← hset]
    simp [hc0]
  refine ⟨Aut.comp L (Aut.diagonal Q L c hc0 hc hci) g, ?_⟩
  simp only [Aut.comp_apply, hg, Aut.diagonal_apply_smul_e]

end Hyperbolic
end NormEuclidean
