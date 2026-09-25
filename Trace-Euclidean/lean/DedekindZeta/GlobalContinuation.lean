import DedekindZeta.ConeMellinBridge
import DedekindZeta.PerClass

/-!
# A global completed-zeta continuation candidate

The original `completedDedekindZeta` is a cone integral whose proved
identification with `ZInfty * dedekindZeta` holds on `Re s > 1`.
Replacing every partial cone integral by its Mellin continuation gives a
function defined at every complex parameter. The first theorem below checks
its exact normalization on the original convergence half-plane.
-/

open NumberField IsDedekindDomain Complex
open scoped nonZeroDivisors

namespace DedekindZeta.GlobalContinuation

open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

/-- The continuation formula for the completed partial zeta attached to an
integral ideal. Away from its two possible poles this is the usual Mellin
continuation of the source's cone integral. -/
def completedPartialZetaContinuation (𝔞 : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ s *
    (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
      mellinContinuation (radialTheta K 𝔞) (radialThetaDual K 𝔞)
        (surfaceVolume K) (surfaceVolume K)
        ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s

/-- Sum the continued partial zetas over the finite ideal class group. -/
def completedZetaContinuation (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K),
    completedPartialZetaContinuation K (idealClassRep K c) s

theorem idealClassRep_ne_zero (c : ClassGroup (𝓞 K)) :
    idealClassRep K c ≠ 0 := by
  unfold idealClassRep
  exact mem_nonZeroDivisors_iff_ne_zero.mp
    (Function.surjInv ClassGroup.mk0_surjective c).2

/-- On `Re s > 1`, this globally defined expression has precisely the
source's archimedean and discriminant normalization. -/
theorem completedZetaContinuation_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    completedZetaContinuation K s =
      ZInfty K s * NumberField.dedekindZeta K s := by
  rw [← DedekindZeta.completedDedekindZeta_eq K hs]
  unfold completedZetaContinuation DedekindZeta.completedDedekindZeta
  apply Finset.sum_congr rfl
  intro c _
  exact (ConeMellinBridge.completedPartialZeta_eq_mellinContinuation
    (K := K) (idealClassRep K c) (idealClassRep_ne_zero K c) hs).symm

/-- Remove the two possible Mellin poles without making a choice of values at
the old pole locations. Here the radial weight is one. -/
def poleRemovedRadial (𝔞 : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  -(surfaceVolume K) * (s - 1) +
    ((Theta.covolume K 𝔞 : ℂ)⁻¹) * (surfaceVolume K) * s +
      s * (s - 1) *
        mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
          (surfaceVolume K) (surfaceVolume K)
          ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s

private theorem poleRemovedRadial_analyticOn (𝔞 : Ideal (𝓞 K))
    (hne : 𝔞 ≠ 0) :
    AnalyticOnNhd ℂ (poleRemovedRadial K 𝔞) Set.univ := by
  obtain ⟨c, α, hpair⟩ := exists_isMellinPair_radialTheta (K := K) 𝔞 hne
  rw [analyticOnNhd_univ_iff_differentiable]
  intro s
  have htail : DifferentiableAt ℂ
      (mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
        (surfaceVolume K) (surfaceVolume K)
        ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1) s :=
    (analyticOnNhd_univ_iff_differentiable.mp (mellinTail_analyticOn hpair)) s
  unfold poleRemovedRadial
  fun_prop

private theorem poleRemovedRadial_eq (𝔞 : Ideal (𝓞 K)) (s : ℂ)
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    poleRemovedRadial K 𝔞 s =
      s * (s - 1) *
        mellinContinuation (radialTheta K 𝔞) (radialThetaDual K 𝔞)
          (surfaceVolume K) (surfaceVolume K)
          ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s := by
  unfold poleRemovedRadial mellinContinuation
  field_simp [hs₀, sub_ne_zero.mpr hs₁]
  norm_num
  ring

def partialFactor (𝔞 : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ s *
    (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))

private theorem partialFactor_analyticOn (𝔞 : Ideal (𝓞 K))
    (hne : 𝔞 ≠ 0) :
    AnalyticOnNhd ℂ (partialFactor K 𝔞) Set.univ := by
  have hA : (Ideal.absNorm 𝔞 : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff (I := 𝔞)).not.mpr hne
  have hD : (((|NumberField.discr K| : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast (abs_ne_zero.mpr (NumberField.discr_ne_zero K))
  rw [analyticOnNhd_univ_iff_differentiable]
  intro s
  have hA' : DifferentiableAt ℂ (fun z : ℂ => (Ideal.absNorm 𝔞 : ℂ) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl hA)
  have hD' : DifferentiableAt ℂ
      (fun z : ℂ => (((|NumberField.discr K| : ℤ) : ℂ) ^ (z / 2))) s :=
    (differentiableAt_id.div_const 2).const_cpow (Or.inl hD)
  unfold partialFactor
  exact ((differentiableAt_const _).mul hA').mul hD'

/-- The completed Dedekind zeta obtained from the radial theta integrals,
with both possible Mellin poles removed, is entire. -/
def completedZetaPoleRemoved (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K),
    partialFactor K (idealClassRep K c) s *
      poleRemovedRadial K (idealClassRep K c) s

theorem completedZetaPoleRemoved_analyticOn :
    AnalyticOnNhd ℂ (completedZetaPoleRemoved K) Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro s
  unfold completedZetaPoleRemoved
  have hsum : DifferentiableAt ℂ
      (∑ c : ClassGroup (𝓞 K),
        (fun z : ℂ => partialFactor K (idealClassRep K c) z *
          poleRemovedRadial K (idealClassRep K c) z)) s := by
    apply DifferentiableAt.sum
    intro c _
    exact ((analyticOnNhd_univ_iff_differentiable.mp
      (partialFactor_analyticOn K (idealClassRep K c) (idealClassRep_ne_zero K c))) s).mul
        ((analyticOnNhd_univ_iff_differentiable.mp
          (poleRemovedRadial_analyticOn K (idealClassRep K c)
            (idealClassRep_ne_zero K c))) s)
  simpa only [Finset.sum_fn] using hsum

/-- Away from the former pole locations, the entire function is exactly
`s(s-1)` times the global completed-zeta continuation candidate. -/
theorem completedZetaPoleRemoved_eq (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedZetaPoleRemoved K s =
      s * (s - 1) * completedZetaContinuation K s := by
  unfold completedZetaPoleRemoved completedZetaContinuation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [poleRemovedRadial_eq K (idealClassRep K c) s hs₀ hs₁]
  unfold completedPartialZetaContinuation partialFactor
  ring

/-- The entire function agrees with the usual pole-removed completed
Dedekind zeta on its original half-plane of convergence. -/
theorem completedZetaPoleRemoved_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    completedZetaPoleRemoved K s =
      s * (s - 1) * (ZInfty K s * NumberField.dedekindZeta K s) := by
  have hs₀ : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs₁ : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  rw [completedZetaPoleRemoved_eq K s hs₀ hs₁,
    completedZetaContinuation_eq_zeta K hs]

end
end DedekindZeta.GlobalContinuation
