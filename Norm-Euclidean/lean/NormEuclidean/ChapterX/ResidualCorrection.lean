import NormEuclidean.ChapterX.GenusFiniteness
import NormEuclidean.ChapterX.FractionalValueMultiplier
import NormEuclidean.ChapterX.FixedValueVectors
import NormEuclidean.ChapterX.ProjectedComplement

/-!
# The actual 104:1 input to the residual correction in 104:3

The regular orthogonal complement has rank at least three when the original
space has rank at least four. Its divided-value multiplier is now constructed
without a class-finiteness input. Global and every-finite local representation
of a divisible residual then give an actual integral correction of the original
value. Choosing the scalar and proving those residual representations remain
the separate arithmetic obligations of the full 104:3 theorem.
-/

noncomputable section

namespace NormEuclidean.ResidualCorrection

open Module ProjectedComplement CompletedIntegralLattice IsDedekindDomain

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An actual regular complementary lattice supplies the 104:1 multiplier
needed by 104:3. Complement regularity, dimension and genus finiteness are derived. -/
theorem exists_complement_multiplier (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (y : V) (hy : Q y ≠ 0)
    (N : Lattice (integerSubring K) (Q.comp (complement Q y).subtype))
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ d : K, (∃ b : integerSubring K, d = (γ : K) * (b : K)) →
        (∃ u : complement Q y, Q u = d) →
        (∀ v : HeightOneSpectrum (integerSubring K),
          ∃ z ∈ carrier (integerSubring K) v N.carrier,
            form (integerSubring K) v (Q.comp (complement Q y).subtype) z =
              algebraMap K (LocalField (integerSubring K) v) d) →
        ∃ u ∈ N.carrier, Q u = d := by
  have hdimU := complement_finrank Q y hy
  exact GenusFiniteness.exists_integral_divided_value_multiplier
    (Q.comp (complement Q y).subtype) (complement_regular Q hQ y hy) N (by omega) T

/-- The residual representation supplied by the proved multiplier produces
an actual original-lattice vector of value a. The remaining scalar, global
representation and local representation obligations are displayed literally. -/
theorem exists_integral_correction (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (L : Lattice (integerSubring K) Q) (y : V) (hyL : y ∈ L.carrier) (hy : Q y ≠ 0)
    (N : Lattice (integerSubring K) (Q.comp (complement Q y).subtype))
    (hNL : ∀ u ∈ N.carrier, (u : V) ∈ L.carrier)
    (a c : K) (hvalue : Q y = c ^ 2 * a)
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ β : integerSubring K,
        (∃ b : integerSubring K, a * (1 - c ^ 2 * (β : K) ^ 2) = (γ : K) * (b : K)) →
        (∃ u : complement Q y, Q u = a * (1 - c ^ 2 * (β : K) ^ 2)) →
        (∀ v : HeightOneSpectrum (integerSubring K),
          ∃ z ∈ carrier (integerSubring K) v N.carrier,
            form (integerSubring K) v (Q.comp (complement Q y).subtype) z =
              algebraMap K (LocalField (integerSubring K) v)
                (a * (1 - c ^ 2 * (β : K) ^ 2))) →
        ∃ u ∈ N.carrier, (β : K) • y + (u : V) ∈ L.carrier ∧
          Q ((β : K) • y + (u : V)) = a := by
  obtain ⟨γ, hγ, hγT, hrep⟩ := exists_complement_multiplier Q hQ hdim y hy N T
  refine ⟨γ, hγ, hγT, ?_⟩
  intro β hdiv hglobal hlocal
  obtain ⟨u, hu, hQu⟩ := hrep _ hdiv hglobal hlocal
  have horth : QuadraticMap.polar Q y (u : V) = 0 := by
    have h := u.property y (Submodule.subset_span (Set.mem_singleton y))
    rw [← two_mul_halfPolar]
    exact mul_eq_zero_of_right _ h
  exact ⟨u, hu, L.carrier.add_mem (L.carrier.smul_mem β hyL) (hNL u hu),
    FixedValueVectors.value_of_orthogonal_correction Q y u c β a hvalue hQu horth⟩

/-- The source complementary multiplier also applies to any actual finite
full complementary module, even when its quadratic values are fractional. -/
theorem exists_fractional_complement_multiplier (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (y : V) (hy : Q y ≠ 0)
    (N : Submodule (integerSubring K) (complement Q y)) (hfg : N.FG)
    (hfull : Submodule.span K (N : Set (complement Q y)) = ⊤)
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ d : K, (∃ b : integerSubring K, d = (γ : K) * (b : K)) →
        (∃ u : complement Q y, Q u = d) →
        (∀ v : HeightOneSpectrum (integerSubring K),
          ∃ z ∈ carrier (integerSubring K) v N,
            form (integerSubring K) v (Q.comp (complement Q y).subtype) z =
              algebraMap K (LocalField (integerSubring K) v) d) →
        ∃ u ∈ N, Q u = d := by
  have hdimU := complement_finrank Q y hy
  exact FractionalValueMultiplier.exists_divided_value_multiplier
    (Q.comp (complement Q y).subtype) (complement_regular Q hQ y hy) N hfg hfull (by omega) T

/-- The actual source correction with a finite full fractional-valued
complementary module. Its residual arithmetic obligations remain explicit. -/
theorem exists_fractional_integral_correction (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (L : Submodule (integerSubring K) V) (y : V) (hyL : y ∈ L) (hy : Q y ≠ 0)
    (N : Submodule (integerSubring K) (complement Q y)) (hfg : N.FG)
    (hfull : Submodule.span K (N : Set (complement Q y)) = ⊤)
    (hNL : ∀ u ∈ N, (u : V) ∈ L) (a c : K) (hvalue : Q y = c ^ 2 * a)
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ β : integerSubring K,
        (∃ b : integerSubring K, a * (1 - c ^ 2 * (β : K) ^ 2) = (γ : K) * (b : K)) →
        (∃ u : complement Q y, Q u = a * (1 - c ^ 2 * (β : K) ^ 2)) →
        (∀ v : HeightOneSpectrum (integerSubring K),
          ∃ z ∈ carrier (integerSubring K) v N,
            form (integerSubring K) v (Q.comp (complement Q y).subtype) z =
              algebraMap K (LocalField (integerSubring K) v)
                (a * (1 - c ^ 2 * (β : K) ^ 2))) →
        ∃ u ∈ N, (β : K) • y + (u : V) ∈ L ∧ Q ((β : K) • y + (u : V)) = a := by
  obtain ⟨γ, hγ, hγT, hrep⟩ :=
    exists_fractional_complement_multiplier Q hQ hdim y hy N hfg hfull T
  refine ⟨γ, hγ, hγT, ?_⟩
  intro β hdiv hglobal hlocal
  obtain ⟨u, hu, hQu⟩ := hrep _ hdiv hglobal hlocal
  have horth : QuadraticMap.polar Q y (u : V) = 0 := by
    have h := u.property y (Submodule.subset_span (Set.mem_singleton y))
    rw [← two_mul_halfPolar]
    exact mul_eq_zero_of_right _ h
  exact ⟨u, hu, L.add_mem (L.smul_mem β hyL) (hNL u hu),
    FixedValueVectors.value_of_orthogonal_correction Q y u c β a hvalue hQu horth⟩

end NormEuclidean.ResidualCorrection
