import NormEuclidean.CompletedUnipotent
import NormEuclidean.ScalarUnipotentWords

/-!
# Common finite unipotent words for actual completed ternary kernel targets
-/

noncomputable section

namespace NormEuclidean.FiniteUnipotentWords

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicApproximation
  TernaryKernelGeneration CompletedUnipotent

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)

local instance finiteCharZero (p : HeightOneSpectrum (integerSubring K)) :
    CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _

theorem localFamily_zero (hdim : Module.finrank K V = 1)
    (p : HeightOneSpectrum (integerSubring K)) (u : V) (b : Bool) :
    localFamily Q hQ hdim p u b 0 = 1 := by
  simp only [localFamily, zero_smul, family_zero, map_one]

theorem localFamily_inv (hdim : Module.finrank K V = 1)
    (p : HeightOneSpectrum (integerSubring K)) (u : V) (b : Bool)
    (t : LocalField (integerSubring K) p) :
    (localFamily Q hQ hdim p u b t)⁻¹ = localFamily Q hQ hdim p u b (-t) := by
  simp only [localFamily, ← map_inv, family_inv]
  congr 2
  exact (neg_smul t (inclusion (integerSubring K) p u)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Each actual completed kernel element is a finite word using one fixed global line vector. -/
theorem exists_local_word (hdim : Module.finrank K V = 1) (u : V) (hu : Q u ≠ 0)
    (p : HeightOneSpectrum (integerSubring K))
    (g : properGroup (form (integerSubring K) p (Hyperbolic.form Q)))
    (hg : properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
      (form_polarBilin_nondegenerate _ p _
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) g = 1) :
    ∃ l : List (Bool × LocalField (integerSubring K) p),
      (l.map (fun r ↦ localFamily Q hQ hdim p u r.1 r.2)).prod = g := by
  let P := form (integerSubring K) p Q
  have hP := form_polarBilin_nondegenerate (integerSubring K) p Q hQ
  have hH := form_polarBilin_nondegenerate (integerSubring K) p (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
  let hA := UnaryClassNumber.anisotropic P hP (local_finrank hdim p)
  have hnorm := OrthogonalTransport.proper_spinorNorm_map _ _
    (hyperbolicEquiv (V := V) (integerSubring K) p) (hyperbolicEquiv_form _ p Q)
    hH (Hyperbolic.form_polarBilin_nondegenerate P hP) g
  have hinc : inclusion (integerSubring K) p u ≠ 0 := by
    intro hz
    apply form_inclusion_ne_zero (integerSubring K) p Q u hu
    rw [hz, map_zero]
  obtain ⟨l, hl⟩ := exists_scalar_word P hP hA (local_finrank hdim p)
    (inclusion _ p u) hinc (toChart Q p g) (hnorm.trans hg)
  refine ⟨l, ?_⟩
  apply (toChart Q p).injective
  rw [map_list_prod, List.map_map]
  simpa only [localFamily, Function.comp_def, MulEquiv.apply_symm_apply] using hl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Finite tuples of actual local kernel elements admit a common finite word. -/
theorem exists_word (hdim : Module.finrank K V = 1) (u : V) (hu : Q u ≠ 0)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : T) → properGroup (form (integerSubring K) v.1 (Hyperbolic.form Q)))
    (ha : ∀ v : T, properAmbientSpinorNormHom
      (form (integerSubring K) v.1 (Hyperbolic.form Q))
      (form_polarBilin_nondegenerate (integerSubring K) v.1 (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) (a v) = 1) :
    ∃ l : List (ScalarUnipotentWords.Parameters T),
      ScalarUnipotentWords.wordImage (Hyperbolic.form Q)
        (fun w ↦ localFamily Q hQ hdim w u) T l = a := by
  classical
  let G : T → Type _ := fun v ↦
    ↥(properGroup (form (integerSubring K) v.1 (Hyperbolic.form Q)))
  let f : ScalarUnipotentWords.Parameters T → ((v : T) → G v) :=
    fun r v ↦ localFamily Q hQ hdim v.1 u r.1 (r.2 v)
  let H := Subgroup.closure (Set.range f)
  let A (v : T) : Subgroup (G v) := (properAmbientSpinorNormHom
    (form (integerSubring K) v.1 (Hyperbolic.form Q))
    (form_polarBilin_nondegenerate _ v.1 _
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ))).ker
  have hs (v : T) (g : G v) (hg : g ∈ A v) : MonoidHom.mulSingle G v g ∈ H := by
    obtain ⟨l, hl⟩ := exists_local_word Q hQ hdim u hu v.1 g hg
    rw [← hl, MonoidHom.map_list_prod, List.map_map]
    apply H.list_prod_mem
    intro x hx
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    let p : ScalarUnipotentWords.Parameters T :=
      (r.1, Function.update (fun _ ↦ 0) v r.2)
    have heq : f p = MonoidHom.mulSingle G v
        (localFamily Q hQ hdim v.1 u r.1 r.2) := by
      funext w
      by_cases hw : w = v
      · subst w
        simp [f, p]
      · simp [f, p, hw, localFamily_zero]
    dsimp only [Function.comp_apply]
    rw [← heq]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  have hmem : a ∈ H := GeneratedWords.mem_of_singles H A hs a ha
  obtain ⟨l, hl⟩ := GeneratedWords.exists_word f (fun r ↦ (r.1, fun v ↦ -r.2 v))
    (fun r ↦ by funext v; exact localFamily_inv Q hQ hdim v.1 u r.1 (r.2 v)) hmem
  refine ⟨l, ?_⟩
  funext v
  have he := (Pi.evalMonoidHom G v).map_list_prod (l.map f)
  have hh := congrFun hl v
  simp only [List.map_map] at he
  exact he.symm.trans hh

end NormEuclidean.FiniteUnipotentWords
