import NormEuclidean.FixedFieldClassSet

/-!
# Fixed-field finiteness for all integral unary norm-Euclidean lattices

A one-dimensional polar matrix has only its diagonal entry. Normalized small
frames therefore give finitely many coordinate forms without any restriction
on the real signatures. The finite integral overmodule interval retains all
nonfree lattices. The final quotient is by actual integral isometry.
-/

noncomputable section

namespace NormEuclidean.UnaryRankFiniteness

open Module CoordinateFormFiniteness IntegralFrameIntervals FixedFieldRankFiniteness

universe v
variable (K : Type*) [Field K] [NumberField K]

/-- Unary coordinate forms belong to a finite set over any fixed number field.
Neither total reality, positivity, nor an integral basis is required. -/
theorem exists_finite_forms :
    ∃ F : Set (QuadraticForm K (Fin 1 → K)), F.Finite ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic →
        HasNumberFieldApproximation Q L.carrier → Module.finrank K V = 1 →
          ∃ b : Basis (Fin 1) K V, (∀ i, b i ∈ L.carrier) ∧ Q.basisRepr b ∈ F := by
  obtain ⟨Φ, hΦ, _, hframe⟩ := NormalizedSmallFrames.exists_uniform_values K
  let Ψ : Set K := (fun a ↦ 2 * a) '' Φ
  let S : Set (Matrix (Fin 1) (Fin 1) K) := {M | ∀ i j, M i j ∈ Ψ}
  have hS : S.Finite := FinitePolarFrames.finite_matrices 1 Ψ (hΦ.image _)
  refine ⟨polarMatrix 1 ⁻¹' S,
    Set.Finite.preimage (polarMatrix_injective 1).injOn hS, ?_⟩
  intro V _ _ Q L hA hE hdim
  obtain ⟨b, hb⟩ := hframe V Q L hA hE
  let b' := b.reindex (finCongr hdim)
  have hb' (i : Fin 1) : b' i ∈ L.carrier ∧ Q (b' i) ∈ Φ := by
    simpa only [b', Basis.reindex_apply] using hb ((finCongr hdim).symm i)
  refine ⟨b', fun i ↦ (hb' i).1, ?_⟩
  change polarMatrix 1 (Q.basisRepr b') ∈ S
  rw [polarMatrix_basisRepr]
  intro i j
  have hji : j = i := Subsingleton.elim _ _
  subst j
  refine ⟨Q (b' i), (hb' i).2, ?_⟩
  simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul]

/-- A finite set of actual unary lattice models covers every anisotropic norm-Euclidean
lattice over the fixed number field, including all signatures and nonfree modules. -/
theorem exists_finite_models :
    ∃ A : Set (Model K 1), A.Finite ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic →
        HasNumberFieldApproximation Q L.carrier → Module.finrank K V = 1 →
          ∃ M ∈ A, Nonempty (LatticeIsometry Q M.1 L.carrier M.2.carrier) := by
  classical
  obtain ⟨F, hF, hcover⟩ := exists_finite_forms K
  let F' : Set (QuadraticForm K (Fin 1 → K)) := {P | P ∈ F ∧ P.polarBilin.Nondegenerate}
  have hF' : F'.Finite := hF.subset (fun _ h ↦ h.1)
  let T (P : QuadraticForm K (Fin 1 → K)) : Set (Lattice (integerSubring K) P) :=
    {L | ∀ i, Pi.single i 1 ∈ L.carrier}
  have hT (P) (hP : P ∈ F') : (T P).Finite := by
    simpa only [T, Pi.basisFun_apply] using
      finite_overmodules hP.2 (Pi.basisFun K (Fin 1))
  let A : Set (Model K 1) := ⋃ P ∈ F', Sigma.mk P '' T P
  have hA : A.Finite := hF'.biUnion (fun P hP ↦ (hT P hP).image (Sigma.mk P))
  refine ⟨A, hA, ?_⟩
  intro V _ _ Q L hAq hE hdim
  obtain ⟨b, hb, hP⟩ := hcover V Q L hAq hE hdim
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

/-- All unary anisotropic norm-Euclidean integral-isometry classes over this field. -/
def euclideanClasses : Set (FixedFieldClassSet.ClassSet K 1) :=
  {c | ∃ M : Model K 1, M.1.Anisotropic ∧
    HasNumberFieldApproximation M.1 M.2.carrier ∧ FixedFieldClassSet.classOf K M = c}

/-- Fixed-field unary finiteness in the actual integral-isometry quotient.
There is no freeness, class-number, positivity, or external finiteness premise. -/
theorem finite_euclideanClasses : (euclideanClasses K).Finite := by
  obtain ⟨A, hA, hcover⟩ := exists_finite_models K
  apply (hA.image (FixedFieldClassSet.classOf K)).subset
  rintro c ⟨M, hAq, hE, rfl⟩
  obtain ⟨N, hN, hMN⟩ := hcover (Fin 1 → K) M.1 M.2 hAq hE (by simp)
  exact ⟨N, hN, ((FixedFieldClassSet.classOf_eq_iff K M N).mpr hMN).symm⟩

end NormEuclidean.UnaryRankFiniteness
