import NormEuclidean.ShortResidueVectors
import NormEuclidean.BoundedValueNormalization
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Full lattice frames with values in a finite field-dependent set

Small residue representatives span every norm-Euclidean lattice over its
field. Rescaling each basis vector by an integral unit then places its
quadratic value in a finite set depending only on the base field. These
are ambient field bases contained in the lattice, not integral bases.
-/

noncomputable section

namespace NormEuclidean.NormalizedSmallFrames

open Module
open scoped NumberField

universe v
variable (K : Type*) [Field K] [NumberField K]

/-- A single finite value set works for all anisotropic norm-Euclidean lattices over the field,
including varying spaces, ranks, and nonfree integral modules. -/
theorem exists_uniform_values :
    ∃ Φ : Set K, Φ.Finite ∧ 0 ∉ Φ ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic →
        HasNumberFieldApproximation Q L.carrier →
          ∃ b : Basis (Fin (Module.finrank K V)) K V,
            ∀ i, b i ∈ L.carrier ∧ Q (b i) ∈ Φ := by
  classical
  obtain ⟨A, hA, hAvalues, hcover⟩ :=
    BoundedValueNormalization.exists_finite_representatives K (4 ^ Module.finrank ℚ K)
  let Φ : Set K := ((↑) : (𝓞 K) → K) '' A
  refine ⟨Φ, hA.image _, ?_, ?_⟩
  · rintro ⟨a, ha, hz⟩
    exact (hAvalues a ha).1 (Subtype.ext hz)
  · intro V _ _ Q L hanis hE
    obtain ⟨b, hb⟩ := ShortResidueVectors.exists_basis L hE
    let a (i : Fin (Module.finrank K V)) : 𝓞 K :=
      ⟨Q (b i), L.integral _ (hb i).1⟩
    have ha (i : Fin (Module.finrank K V)) : a i ≠ 0 := by
      intro h
      exact b.ne_zero i (hanis _ (congrArg (fun t : 𝓞 K ↦ (t : K)) h))
    have habound (i : Fin (Module.finrank K V)) :
        Ideal.absNorm (Ideal.span {a i}) < 4 ^ Module.finrank ℚ K := by
      have h := (hb i).2
      change fieldAbsNorm K (a i : K) < (4 : ℚ) ^ Module.finrank ℚ K at h
      rw [← BoundedValueNormalization.principal_absNorm] at h
      exact_mod_cast h
    choose u hu using fun i ↦ hcover (a i) (ha i) (habound i)
    let b' := b.unitsSMul (fun i ↦ Units.map (algebraMap (𝓞 K) K).toMonoidHom (u i))
    have hbi (i : Fin (Module.finrank K V)) :
        b' i = (((u i : (𝓞 K)ˣ) : 𝓞 K) : K) • b i := by
      simp only [b', Basis.unitsSMul_apply, Units.smul_def]
      rfl
    refine ⟨b', ?_⟩
    intro i
    constructor
    · rw [hbi]
      exact L.carrier.smul_mem (show integerSubring K from (u i : 𝓞 K)) (hb i).1
    · refine ⟨a i * (u i : 𝓞 K) ^ 2, hu i, ?_⟩
      rw [hbi, Q.map_smul]
      change ((a i : K) * ((u i : 𝓞 K) : K) ^ 2) = _
      simp only [smul_eq_mul]
      change Q (b i) * ((u i : 𝓞 K) : K) ^ 2 = _
      ring

end NormEuclidean.NormalizedSmallFrames
