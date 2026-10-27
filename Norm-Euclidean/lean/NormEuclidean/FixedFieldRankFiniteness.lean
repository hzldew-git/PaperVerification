import NormEuclidean.CoordinateFormFiniteness
import NormEuclidean.IntegralFrameIntervals

/-!
# Actual finite integral isometry representatives for fixed field and rank

For anisotropic norm-Euclidean lattices with nonnegative real values over
a fixed totally real number field, the finite coordinate forms and finite
integral overmodule intervals give finitely many actual lattice models.
The rank is fixed. No field finiteness, mass formula, class-number bound,
integral freeness, or conditional lattice-finiteness input is assumed.
-/

noncomputable section

namespace NormEuclidean.FixedFieldRankFiniteness

open Module PositivePairingBounds IntegralFrameIntervals

universe v
variable (K : Type*) [Field K] [NumberField K]

/-- Coordinate lattice models with the quadratic form and actual full integral module retained. -/
abbrev Model (n : ℕ) :=
  (Q : QuadraticForm K (Fin n → K)) × Lattice (integerSubring K) Q

/-- A finite family of actual lattice models covers every original fixed-rank lattice.
Equivalence is an ambient K-linear isometry identifying the entire integral modules. -/
theorem exists_finite_models [NumberField.IsTotallyReal K] (n : ℕ) :
    ∃ A : Set (Model K n), A.Finite ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic →
        HasNumberFieldApproximation Q L.carrier → TotallyNonnegative Q →
        Module.finrank K V = n →
          ∃ M ∈ A, Nonempty (LatticeIsometry Q M.1 L.carrier M.2.carrier) := by
  classical
  obtain ⟨F, hF, hcover⟩ := CoordinateFormFiniteness.exists_finite_forms (K := K) n
  let F' : Set (QuadraticForm K (Fin n → K)) := {P | P ∈ F ∧ P.polarBilin.Nondegenerate}
  have hF' : F'.Finite := hF.subset (fun _ h ↦ h.1)
  let T (P : QuadraticForm K (Fin n → K)) : Set (Lattice (integerSubring K) P) :=
    {L | ∀ i, Pi.single i 1 ∈ L.carrier}
  have hT (P) (hP : P ∈ F') : (T P).Finite := by
    simpa only [T, Pi.basisFun_apply] using
      finite_overmodules hP.2 (Pi.basisFun K (Fin n))
  let A : Set (Model K n) := ⋃ P ∈ F', Sigma.mk P '' T P
  have hA : A.Finite := hF'.biUnion (fun P hP ↦ (hT P hP).image (Sigma.mk P))
  refine ⟨A, hA, ?_⟩
  intro V _ _ Q L hAq hE hpos hdim
  obtain ⟨b, hb, hP⟩ := hcover V Q L hAq hE hpos hdim
  let P := Q.basisRepr b
  let e := Q.isometryEquivBasisRepr b
  let M := IntegralFrameIntervals.map L e
  have hAP : P.Anisotropic := by
    intro x hx
    have hQ : Q (e.symm x) = 0 := (e.symm.map_app x).trans hx
    have hz := hAq _ hQ
    have := congrArg e hz
    simpa using this
  have hregular : P.polarBilin.Nondegenerate := by
    letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
    exact quadraticForm_polarBilin_nondegenerate_of_anisotropic P hAP
  have hMP : M ∈ T P := by
    intro i
    have hei : e (b i) = Pi.single i 1 := by
      change b.equivFun (b i) = Pi.single i 1
      ext j
      simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
    exact ⟨b i, hb i, hei⟩
  refine ⟨⟨P, M⟩, ?_, ⟨mapIsometry L e⟩⟩
  exact Set.mem_iUnion_of_mem P (Set.mem_iUnion_of_mem ⟨hP, hregular⟩ ⟨M, hMP, rfl⟩)

end NormEuclidean.FixedFieldRankFiniteness
