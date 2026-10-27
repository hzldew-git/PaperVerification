import NormEuclidean.ChapterX.GenusPatching
import NormEuclidean.ChapterX.LocalIntegralReflection
import NormEuclidean.ChapterX.GenusValueMultiplier

/-!
# The finite-class representation transfer toward O'Meara 104:1

The local proper comparisons required by normalization are now derived for
general regular lattices. The scalar case of 102:5 supplies the actual genus
representative. Class finiteness remains an explicit mathematical premise;
neither 103:4 nor the full divided-value conclusion of 104:1 is asserted here.
-/

noncomputable section

namespace NormEuclidean.GenusRepresentationTransfer

open IsDedekindDomain CompletedIntegralLattice

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- The general genus value multiplier requires actual finite classes but
no longer requires a caller-supplied upgrade to proper local comparisons. -/
theorem exists_genus_value_multiplier_of_finite_classes (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Lattice (integerSubring K) Q)
    (hfinite : Finite (GenusClassSet Q L))
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ (M : Lattice (integerSubring K) Q), SameGenus Q L M →
        ∀ b : K, (∃ x ∈ M.carrier, Q x = b) → ∃ z ∈ L.carrier, Q z = (γ : K) * b :=
  GenusValueMultiplier.exists_genus_value_multiplier Q hQ hpos L hfinite
    (fun M hM ↦ LocalIntegralReflection.sameProperGenus_of_sameGenus Q hQ L M hM) T

/-- Combine the proved scalar local-to-genus theorem with the finite-class
multiplier. Global representability and all finite integral representations
yield an actual integral representation of the multiplied value in the base lattice. -/
theorem exists_local_global_value_multiplier_of_finite_classes
    (hQ : Q.polarBilin.Nondegenerate) (hpos : 0 < Module.finrank K V)
    (L : Lattice (integerSubring K) Q) (hfinite : Finite (GenusClassSet Q L))
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ a : K, (∃ x : V, Q x = a) →
        (∀ v : HeightOneSpectrum (integerSubring K),
          ∃ z ∈ carrier (integerSubring K) v L.carrier,
            form (integerSubring K) v Q z =
              algebraMap K (LocalField (integerSubring K) v) a) →
        ∃ z ∈ L.carrier, Q z = (γ : K) * a := by
  obtain ⟨γ, hγ0, hγunit, hγ⟩ :=
    exists_genus_value_multiplier_of_finite_classes Q hQ hpos L hfinite T
  refine ⟨γ, hγ0, hγunit, ?_⟩
  intro a hglobal hlocal
  obtain ⟨P, hP, hrep⟩ := GenusPatching.exists_genus_lattice_representing Q hQ L a hglobal hlocal
  exact hγ P hP a hrep

end NormEuclidean.GenusRepresentationTransfer
