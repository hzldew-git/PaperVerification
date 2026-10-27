import NormEuclidean.ChapterX.WittExtension
import NormEuclidean.ChapterX.GenusPatching
import NormEuclidean.ChapterX.ModuleGenusPatching

/-!
# The regular sublattice case of O'Meara 102:5

Actual local quadratic representations extend to ambient transformations by
the proved Witt theorem. Finite local patching then gives a genus member
containing the original embedded lattice. No ambient transporter is an input.
-/

noncomputable section

namespace NormEuclidean.RegularSublatticePatching

open IsDedekindDomain CompletedIntegralLattice ProperSpinor
open scoped TensorProduct

section CompletedMaps

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- Completing a linear map commutes with the actual ambient inclusions. -/
theorem baseChange_inclusion (v : HeightOneSpectrum R) (f : W →ₗ[K] V) (x : W) :
    f.baseChange (LocalField R v) (inclusion R v x) = inclusion R v (f x) := rfl

/-- Completed carriers commute with the image of any ambient linear map,
including embeddings of a smaller-rank lattice. -/
theorem carrier_map (v : HeightOneSpectrum R) (A : Submodule R W) (f : W →ₗ[K] V) :
    (carrier R v A).map ((f.baseChange (LocalField R v)).restrictScalars (LocalRing R v)) =
      carrier R v (A.map (f.restrictScalars R)) := by
  rw [carrier, Submodule.map_span, carrier]
  apply congrArg (Submodule.span (LocalRing R v))
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    exact (baseChange_inclusion R v f x).symm
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨inclusion R v x, ⟨x, hx, rfl⟩, baseChange_inclusion R v f x⟩

variable [Invertible (2 : K)]

/-- Completing an actual quadratic isometry gives a quadratic isometry
between the actual completed ambient spaces. -/
def completedIsometry (v : HeightOneSpectrum R)
    {P : QuadraticForm K W} {Q : QuadraticForm K V} (i : P →qᵢ Q) :
    form R v P →qᵢ form R v Q where
  toLinearMap := i.toLinearMap.baseChange (LocalField R v)
  map_app' z := by
    have hforms : (form R v Q).comp (i.toLinearMap.baseChange (LocalField R v)) =
        form R v P := by
      apply _root_.baseChange_ext
      intro x
      simp only [form, QuadraticMap.comp_apply, LinearMap.baseChange_tmul,
        QuadraticForm.baseChange_tmul, QuadraticMap.Isometry.coe_toLinearMap, i.map_app]
    exact congrArg (fun H : QuadraticForm (LocalField R v) (Space (V := W) R v) ↦ H z) hforms

end CompletedMaps

section NumberField

variable {K V W : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

/-- O'Meara 102:5 for a regular source lattice with a fixed global
quadratic embedding. Actual local lattice representations are extended and
patched; neither their ambient transporters nor the resulting genus member is assumed. -/
theorem exists_genus_lattice_containing_embedded_regular
    (P : QuadraticForm K W) (hP : P.polarBilin.Nondegenerate)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : Lattice (integerSubring K) P) (L : Lattice (integerSubring K) Q) (i : P →qᵢ Q)
    (hlocal : ∀ v : HeightOneSpectrum (integerSubring K),
      ∃ f : form (integerSubring K) v P →qᵢ form (integerSubring K) v Q,
        ∀ x ∈ carrier (integerSubring K) v A.carrier,
          f x ∈ carrier (integerSubring K) v L.carrier) :
    ∃ M : Lattice (integerSubring K) Q, SameGenus Q L M ∧
      ∀ x ∈ A.carrier, i x ∈ M.carrier := by
  classical
  letI := A.finiteDimensional
  by_cases hpos : 0 < Module.finrank K V
  · let B := A.carrier.map (i.toLinearMap.restrictScalars (integerSubring K))
    have hBfg : B.FG := A.finite.map _
    obtain ⟨d, hd0, hd⟩ := exists_lattice_denominator B L.carrier hBfg L.full
    let T := (finite_primes_containing (K := K) (integerSubring K) d hd0).toFinset
    choose f hf using hlocal
    have htrans (v : HeightOneSpectrum (integerSubring K)) :
        ∃ g : ambientGroup (form (integerSubring K) v Q),
          ∀ x : Space (V := W) (integerSubring K) v,
            g.1 (completedIsometry (integerSubring K) v i x) = f v x :=
      WittExtension.exists_extension_of_quadratic_isometries (form (integerSubring K) v P)
        (form_polarBilin_nondegenerate (integerSubring K) v P hP)
        (form (integerSubring K) v Q)
        (form_polarBilin_nondegenerate (integerSubring K) v Q hQ)
        (completedIsometry (integerSubring K) v i) (f v)
    choose g hg using htrans
    have hin : ∀ v ∈ T, ∀ x ∈ carrier (integerSubring K) v B,
        ((g v)⁻¹).1.symm x ∈ carrier (integerSubring K) v L.carrier := by
      intro v _ x hx
      rw [← carrier_map (integerSubring K) v A.carrier i.toLinearMap] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      change (g v).1 (completedIsometry (integerSubring K) v i y) ∈ _
      rw [hg v y]
      exact hf v y hy
    have hout : ∀ v ∉ T, carrier (integerSubring K) v B ≤
        carrier (integerSubring K) v L.carrier := by
      intro v hv
      have hdv : d ∉ v.asIdeal := by
        intro hdv
        exact hv ((finite_primes_containing (K := K) (integerSubring K) d hd0).mem_toFinset.mpr hdv)
      exact carrier_le_of_scaled_le_of_not_mem (integerSubring K) v B L.carrier d hd hdv
    obtain ⟨M, hM, hBM⟩ := GenusPatching.exists_genus_lattice_containing Q hQ hpos L B T
      (fun v ↦ (g v)⁻¹) hin hout
    exact ⟨M, hM, fun x hx ↦ hBM ⟨x, hx, rfl⟩⟩
  · haveI : Subsingleton V := (Module.finrank_zero_iff (R := K) (M := V)).mp (by omega)
    refine ⟨L, (sameGenus_iff_finite Q L L).mpr (finiteLocallyIsometric_refl _ Q L.carrier), ?_⟩
    intro x _
    rw [Subsingleton.elim (i x) 0]
    exact L.carrier.zero_mem

/-- The literal embedded regular-sublattice specialization of 102:5.
The source is a regular subspace of the original ambient space and its
integral lattice may be nonfree and have smaller rank. -/
theorem exists_genus_lattice_containing_regular_sublattice
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (U : Submodule K V)
    (hU : (Q.comp U.subtype).polarBilin.Nondegenerate)
    (A : Lattice (integerSubring K) (Q.comp U.subtype)) (L : Lattice (integerSubring K) Q)
    (hlocal : ∀ v : HeightOneSpectrum (integerSubring K),
      ∃ f : form (integerSubring K) v (Q.comp U.subtype) →qᵢ form (integerSubring K) v Q,
        ∀ x ∈ carrier (integerSubring K) v A.carrier,
          f x ∈ carrier (integerSubring K) v L.carrier) :
    ∃ M : Lattice (integerSubring K) Q, SameGenus Q L M ∧
      ∀ x ∈ A.carrier, (x : V) ∈ M.carrier := by
  let i : Q.comp U.subtype →qᵢ Q :=
    { toLinearMap := U.subtype
      map_app' := fun _ ↦ rfl }
  exact exists_genus_lattice_containing_embedded_regular (Q.comp U.subtype) hU Q hQ A L i hlocal

/-- The finite full module version of 102:5, with no quadratic integrality
premise on either lattice. The output includes all finite integral comparisons
and the automatic infinite ambient comparisons of the fixed-space genus. -/
theorem exists_genus_module_containing_embedded_regular
    (P : QuadraticForm K W) (hP : P.polarBilin.Nondegenerate)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : Submodule (integerSubring K) W) (hAfg : A.FG)
    (hA : Submodule.span K (A : Set W) = ⊤)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) (i : P →qᵢ Q)
    (hlocal : ∀ v : HeightOneSpectrum (integerSubring K),
      ∃ f : form (integerSubring K) v P →qᵢ form (integerSubring K) v Q,
        ∀ x ∈ carrier (integerSubring K) v A, f x ∈ carrier (integerSubring K) v L) :
    ∃ M : Submodule (integerSubring K) V, M.FG ∧ Submodule.span K (M : Set V) = ⊤ ∧
      AllPlaceLocallyIsometric Q Q L M ∧ ∀ x ∈ A, i x ∈ M := by
  classical
  letI := ModuleGenusPatching.finiteDimensional_of_fg_full (integerSubring K) A hAfg hA
  by_cases hpos : 0 < Module.finrank K V
  · let B := A.map (i.toLinearMap.restrictScalars (integerSubring K))
    have hBfg : B.FG := hAfg.map _
    obtain ⟨d, hd0, hd⟩ := exists_lattice_denominator B L hBfg hL
    let T := (finite_primes_containing (K := K) (integerSubring K) d hd0).toFinset
    choose f hf using hlocal
    have htrans (v : HeightOneSpectrum (integerSubring K)) :
        ∃ g : ambientGroup (form (integerSubring K) v Q),
          ∀ x : Space (V := W) (integerSubring K) v,
            g.1 (completedIsometry (integerSubring K) v i x) = f v x :=
      WittExtension.exists_extension_of_quadratic_isometries (form (integerSubring K) v P)
        (form_polarBilin_nondegenerate (integerSubring K) v P hP)
        (form (integerSubring K) v Q)
        (form_polarBilin_nondegenerate (integerSubring K) v Q hQ)
        (completedIsometry (integerSubring K) v i) (f v)
    choose g hg using htrans
    have hin : ∀ v ∈ T, ∀ x ∈ carrier (integerSubring K) v B,
        ((g v)⁻¹).1.symm x ∈ carrier (integerSubring K) v L := by
      intro v _ x hx
      rw [← carrier_map (integerSubring K) v A i.toLinearMap] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      change (g v).1 (completedIsometry (integerSubring K) v i y) ∈ _
      rw [hg v y]
      exact hf v y hy
    have hout : ∀ v ∉ T, carrier (integerSubring K) v B ≤ carrier (integerSubring K) v L := by
      intro v hv
      have hdv : d ∉ v.asIdeal := by
        intro hdv
        exact hv ((finite_primes_containing (K := K) (integerSubring K) d hd0).mem_toFinset.mpr hdv)
      exact carrier_le_of_scaled_le_of_not_mem (integerSubring K) v B L d hd hdv
    obtain ⟨M, hMfg, hM, hgen, hBM⟩ := ModuleGenusPatching.exists_module_containing Q hQ hpos
      L hLfg hL B T (fun v ↦ (g v)⁻¹) hin hout
    exact ⟨M, hMfg, hM, ⟨hgen, ArchimedeanComparison.infinitelyLocallyIsometric_refl Q⟩,
      fun x hx ↦ hBM ⟨x, hx, rfl⟩⟩
  · haveI : Subsingleton V := (Module.finrank_zero_iff (R := K) (M := V)).mp (by omega)
    refine ⟨L, hLfg, hL, allPlaceLocallyIsometric_refl Q L, ?_⟩
    intro x _
    rw [Subsingleton.elim (i x) 0]
    exact L.zero_mem

/-- O'Meara 102:5 for an embedded regular sublattice, with fractional
quadratic values permitted for both source and target. All local representations
are actual maps; the global containing genus member is constructed. -/
theorem exists_genus_module_containing_regular_sublattice
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (U : Submodule K V)
    (hU : (Q.comp U.subtype).polarBilin.Nondegenerate)
    (A : Submodule (integerSubring K) U) (hAfg : A.FG)
    (hA : Submodule.span K (A : Set U) = ⊤)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤)
    (hlocal : ∀ v : HeightOneSpectrum (integerSubring K),
      ∃ f : form (integerSubring K) v (Q.comp U.subtype) →qᵢ form (integerSubring K) v Q,
        ∀ x ∈ carrier (integerSubring K) v A, f x ∈ carrier (integerSubring K) v L) :
    ∃ M : Submodule (integerSubring K) V, M.FG ∧ Submodule.span K (M : Set V) = ⊤ ∧
      AllPlaceLocallyIsometric Q Q L M ∧ ∀ x ∈ A, (x : V) ∈ M := by
  let i : Q.comp U.subtype →qᵢ Q :=
    { toLinearMap := U.subtype
      map_app' := fun _ ↦ rfl }
  exact exists_genus_module_containing_embedded_regular (Q.comp U.subtype) hU Q hQ
    A hAfg hA L hLfg hL i hlocal

end NumberField

end NormEuclidean.RegularSublatticePatching
