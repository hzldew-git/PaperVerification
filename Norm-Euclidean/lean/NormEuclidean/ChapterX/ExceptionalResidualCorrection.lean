import NormEuclidean.ChapterX.CompletedSmallComplement
import NormEuclidean.ChapterX.ExceptionalResidualSelection
import NormEuclidean.ChapterX.FixedValueVectors

/-!
# The 104:3 correction with constructed finite local representations

The target vector is the original exact-value vector v/c, while v is in the
global lattice and c is a unit at the targets. The actual completed local
intersection supplies the off-target geometry. Given binary unit frames at
denominator divisors, every initial and final finite local residual vector
is constructed. The only subsequent representation input is global residual
representation; its 66:1 dependency is not asserted to be closed here.
-/

noncomputable section

namespace NormEuclidean.ExceptionalResidualCorrection

open IsDedekindDomain CompletedIntegralLattice ProjectedComplement Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The small module, scalar, every finite local representation and actual
integral vector correction are derived. The remaining source premises are
binary-frame geometry at denominator divisors and global residual representation. -/
theorem exists_correction_of_binary_frames (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) (v : V) (hvL : v ∈ L) (hv : Q v ≠ 0)
    (a : (integerSubring K)ˣ) (c : integerSubring K) (hc : c ≠ 0)
    (hvalue : Q v = (c : K) ^ 2 * ((a : integerSubring K) : K))
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (hTc : ∀ w ∈ T, c ∉ w.asIdeal) (q : NumberField.InfinitePlace K)
    (W : (w : T) → Set (Space (V := V) (integerSubring K) w.1))
    (hW : ∀ w, W w ∈ 𝓝 (inclusion (integerSubring K) w.1 ((c : K)⁻¹ • v)))
    (hnondyadic : ∀ w : HeightOneSpectrum (integerSubring K), c ∈ w.asIdeal →
      IsUnit (2 : LocalRing (integerSubring K) w))
    (hframes : ∀ w : HeightOneSpectrum (integerSubring K), c ∈ w.asIdeal →
      ExceptionalResidualSelection.binaryUnitFrame w
        (form (integerSubring K) w (Q.comp (complement Q v).subtype))
        ((carrier (integerSubring K) w L).comap
          (((complement Q v).subtype.baseChange (LocalField (integerSubring K) w)).restrictScalars
            (LocalRing (integerSubring K) w))))
    (t : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
    (A : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
    (hA : ∀ w, A w ∈ 𝓝 (t w)) (B : ℝ) :
    ∃ M : Submodule (integerSubring K) (complement Q v),
      M.FG ∧ Submodule.span K (M : Set (complement Q v)) = ⊤ ∧
      (∀ u ∈ M, (u : V) ∈ L) ∧
      (∀ w : HeightOneSpectrum (integerSubring K), w ∉ T →
        carrier (integerSubring K) w M = (carrier (integerSubring K) w L).comap
          (((complement Q v).subtype.baseChange (LocalField (integerSubring K) w)).restrictScalars
            (LocalRing (integerSubring K) w))) ∧
      ∃ β : integerSubring K,
        (∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
          algebraMap K w.1.Completion (β : K) ∈ A w) ∧ B < q (β : K) ∧
        (∀ w : HeightOneSpectrum (integerSubring K),
          ∃ x ∈ carrier (integerSubring K) w M,
            form (integerSubring K) w (Q.comp (complement Q v).subtype) x =
              algebraMap K (LocalField (integerSubring K) w)
                (((a : integerSubring K) : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2))) ∧
        ((∃ u : complement Q v, Q u = ((a : integerSubring K) : K) *
            (1 - (c : K) ^ 2 * (β : K) ^ 2)) →
          ∃ u ∈ M, Q u = ((a : integerSubring K) : K) *
            (1 - (c : K) ^ 2 * (β : K) ^ 2) ∧
            (β : K) • v + (u : V) ∈ L ∧ Q ((β : K) • v + (u : V)) =
              ((a : integerSubring K) : K) ∧
            ∀ w : T, inclusion (integerSubring K) w.1 ((β : K) • v + (u : V)) ∈ W w) := by
  classical
  let y := (c : K)⁻¹ • v
  choose D Y hD hY hDY using fun w : T ↦ FixedValueVectors.exists_correction_neighborhoods
    (F := LocalField (integerSubring K) w.1)
    (inclusion (integerSubring K) w.1 y) (W w) (hW w)
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
  have hcF (w : HeightOneSpectrum (integerSubring K)) :
      algebraMap K (LocalField (integerSubring K) w) (c : K) ≠ 0 :=
    (map_ne_zero _).mpr hcK
  let C (w : T) := (fun b : LocalField (integerSubring K) w.1 ↦
    algebraMap K (LocalField (integerSubring K) w.1) (c : K) * b) ⁻¹' D w
  have hC (w : T) : C w ∈ 𝓝
      (algebraMap K (LocalField (integerSubring K) w.1) (c : K))⁻¹ := by
    have hcont : Continuous (fun b : LocalField (integerSubring K) w.1 ↦
        algebraMap K (LocalField (integerSubring K) w.1) (c : K) * b) :=
      continuous_const.mul continuous_id
    apply hcont.continuousAt.preimage_mem_nhds
    change D w ∈ 𝓝 (algebraMap K (LocalField (integerSubring K) w.1) (c : K) *
      (algebraMap K (LocalField (integerSubring K) w.1) (c : K))⁻¹)
    rw [mul_inv_cancel₀ (hcF w.1)]
    exact hD w
  obtain ⟨M, hMfg, hM, hML, hMY, hout⟩ := CompletedSmallComplement.exists_small_on_subspace
    L hLfg hL (complement Q v) T Y hY
  have hMframes (w : HeightOneSpectrum (integerSubring K)) (hw : c ∈ w.asIdeal) :
      ExceptionalResidualSelection.binaryUnitFrame w
        (form (integerSubring K) w (Q.comp (complement Q v).subtype))
        (carrier (integerSubring K) w M) := by
    rw [hout w (fun hwT ↦ hTc w hwT hw)]
    exact hframes w hw
  have hdimU := complement_finrank Q v hv
  obtain ⟨β, hβC, hβinf, hβq, hlocal, hcorrect⟩ :=
    ExceptionalResidualSelection.exists_selection_of_binary_frames
      (Q.comp (complement Q v).subtype) (complement_regular Q hQ v hv) (by omega)
      M hMfg hM a c hc T hTc q C hC hnondyadic hMframes t A hA B
  refine ⟨M, hMfg, hM, hML, hout, β, hβinf, hβq, hlocal, ?_⟩
  intro hglobal
  obtain ⟨u, hu, huQ⟩ := hcorrect hglobal
  have horth : QuadraticMap.polar Q v (u : V) = 0 := by
    rw [← two_mul_halfPolar]
    exact mul_eq_zero_of_right _ (u.property v (Submodule.subset_span (Set.mem_singleton v)))
  refine ⟨u, hu, huQ, L.add_mem (L.smul_mem β hvL) (hML u hu),
    FixedValueVectors.value_of_orthogonal_correction Q v u c β a hvalue huQ horth, ?_⟩
  intro w
  have hsmall : inclusion (integerSubring K) w.1 (u : V) ∈ Y w := by
    have h := hMY w _ (inclusion_mem (integerSubring K) w.1 M hu)
    rw [RegularSublatticePatching.baseChange_inclusion] at h
    exact h
  have hcy : algebraMap K (LocalField (integerSubring K) w.1) (c : K) •
      inclusion (integerSubring K) w.1 y = inclusion (integerSubring K) w.1 v := by
    have h : (c : K) • y = v := by simp [y, smul_smul, hcK]
    have hloc := congrArg (inclusion (integerSubring K) w.1) h
    rw [map_smul, ← IsScalarTower.algebraMap_smul
      (R := K) (A := LocalField (integerSubring K) w.1)] at hloc
    exact hloc
  have hfinal := hDY w _ (hβC w) _ hsmall
  change (algebraMap K (LocalField (integerSubring K) w.1) (c : K) *
    algebraMap K (LocalField (integerSubring K) w.1) (β : K)) •
      inclusion (integerSubring K) w.1 y + inclusion (integerSubring K) w.1 (u : V) ∈ W w
    at hfinal
  rw [mul_comm (algebraMap K (LocalField (integerSubring K) w.1) (c : K)),
    mul_smul, hcy] at hfinal
  rw [map_add, map_smul, ← IsScalarTower.algebraMap_smul
    (R := K) (A := LocalField (integerSubring K) w.1)]
  exact hfinal

end NormEuclidean.ExceptionalResidualCorrection
