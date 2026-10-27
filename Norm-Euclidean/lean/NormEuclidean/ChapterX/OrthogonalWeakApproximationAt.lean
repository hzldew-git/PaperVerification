import NormEuclidean.ChapterX.ProperWeakApproximation

/-!
# One-place weak approximation for the full orthogonal group

A local orthogonal transformation has one of the two determinant signs.
In the improper case a genuine global reflection reduces approximation to
the already proved proper-group theorem. Only one place is specified, so
different determinant signs at different places are not simultaneously imposed.
-/

noncomputable section

namespace NormEuclidean.OrthogonalWeakApproximationAt

open ProperSpinor ProperWeakApproximation CompletedIntegralLattice IsDedekindDomain
open AdelicApproximation SpinorBaseChange ReflectionApproximation Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- Complete an actual ambient orthogonal transformation. -/
def localizeAmbient (g : ambientGroup Q) (v : HeightOneSpectrum (integerSubring K)) :
    ambientGroup (form (integerSubring K) v Q) :=
  ⟨equiv (integerSubring K) v g.1, equiv_form (integerSubring K) v Q Q g.1 g.2⟩

omit [FiniteDimensional K V] in
@[simp] theorem localizeAmbient_mul (f g : ambientGroup Q)
    (v : HeightOneSpectrum (integerSubring K)) :
    localizeAmbient Q (f * g) v = localizeAmbient Q f v * localizeAmbient Q g v := by
  apply Subtype.ext
  exact LinearEquiv.baseChange_mul K (LocalField (integerSubring K) v) V f.1 g.1

@[simp] theorem localizeAmbient_proper (g : properGroup Q)
    (v : HeightOneSpectrum (integerSubring K)) :
    localizeAmbient Q g.1 v = (localizeProper Q g v).1 := rfl

omit [FiniteDimensional K V] in
@[simp] theorem localizeAmbient_reflection (x : V) (hx : Q x ≠ 0)
    (v : HeightOneSpectrum (integerSubring K)) :
    localizeAmbient Q (ambientReflection Q x hx) v =
      ambientReflection (form (integerSubring K) v Q) (inclusion (integerSubring K) v x)
        (form_inclusion_ne_zero (integerSubring K) v Q x hx) := by
  apply Subtype.ext
  exact equiv_reflection (integerSubring K) v Q x hx

/-- Proper weak approximation at a single actual finite place. -/
theorem exists_global_proper_weak_at (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (v : HeightOneSpectrum (integerSubring K))
    (a : properGroup (form (integerSubring K) v Q))
    (U : Set (properGroup (form (integerSubring K) v Q))) (hU : U ∈ 𝓝 a) :
    ∃ g : properGroup Q, localizeProper Q g v ∈ U := by
  classical
  let T : Finset (HeightOneSpectrum (integerSubring K)) := {v}
  let v0 : T := ⟨v, by simp [T]⟩
  let aT : (w : T) → properGroup (form (integerSubring K) w.1 Q) :=
    Function.update (fun _ ↦ 1) v0 a
  have hnb : {b : (w : T) → properGroup (form (integerSubring K) w.1 Q) |
      b v0 ∈ U} ∈ 𝓝 aT := by
    apply ((continuous_apply v0).tendsto aT).eventually
    change U ∈ 𝓝 (aT v0)
    rw [show aT v0 = a from Function.update_self _ _ _]
    exact hU
  obtain ⟨b, hb, g, rfl⟩ := (mem_closure_iff_nhds.mp
    (denseRange_finiteProperDiagonal Q hQ hpos T aT)) _ hnb
  exact ⟨g, hb⟩

/-- Full orthogonal weak approximation at one finite place. Improper local
targets are handled by an actual global reflection, rather than excluded. -/
theorem exists_global_orthogonal_weak_at (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (v : HeightOneSpectrum (integerSubring K))
    (a : ambientGroup (form (integerSubring K) v Q))
    (U : Set (ambientGroup (form (integerSubring K) v Q))) (hU : U ∈ 𝓝 a) :
    ∃ g : ambientGroup Q, localizeAmbient Q g v ∈ U := by
  have hQv := form_polarBilin_nondegenerate (integerSubring K) v Q hQ
  have hsign := (ambientToBong (form (integerSubring K) v Q) hQv a).det_eq_one_or_neg_one
  rcases hsign with hdet | hdet
  · let p : properGroup (form (integerSubring K) v Q) := ⟨a, hdet⟩
    have hp : (Subtype.val ⁻¹' U) ∈ 𝓝 p :=
      continuous_subtype_val.tendsto p |>.eventually hU
    obtain ⟨g, hg⟩ := exists_global_proper_weak_at Q hQ hpos v p _ hp
    exact ⟨g.1, hg⟩
  · let q := SpinorBridge.quadraticSpace Q hQ
    obtain ⟨x, hx⟩ := q.exists_isAnisotropic_of_finrank_pos hpos
    have hx0 : Q x ≠ 0 := by simpa [q, Bong.QuadraticSpace.IsAnisotropic] using hx
    let r := ambientReflection Q x hx0
    let rv := localizeAmbient Q r v
    have hdr : determinantHom (form (integerSubring K) v Q) rv = -1 := by
      rw [show rv = localizeAmbient Q (ambientReflection Q x hx0) v from rfl,
        localizeAmbient_reflection]
      exact ambientReflection_det _ hQv _ _
    have hdp : rv⁻¹ * a ∈ properGroup (form (integerSubring K) v Q) := by
      change determinantHom (form (integerSubring K) v Q) (rv⁻¹ * a) = 1
      change determinantHom (form (integerSubring K) v Q) a = -1 at hdet
      rw [map_mul, map_inv, hdr, hdet]
      simp
    let p : properGroup (form (integerSubring K) v Q) := ⟨rv⁻¹ * a, hdp⟩
    let f := fun b : properGroup (form (integerSubring K) v Q) ↦ rv * b.1
    have hf : Continuous f := continuous_const.mul continuous_subtype_val
    have hfp : f p = a := by simp [f, p]
    have hp : f ⁻¹' U ∈ 𝓝 p := hf.tendsto p |>.eventually (hfp.symm ▸ hU)
    obtain ⟨g, hg⟩ := exists_global_proper_weak_at Q hQ hpos v p _ hp
    refine ⟨r * g.1, ?_⟩
    change rv * (localizeProper Q g v).1 ∈ U at hg
    simpa only [localizeAmbient_mul, localizeAmbient_proper] using hg

end NormEuclidean.OrthogonalWeakApproximationAt
