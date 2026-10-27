import NormEuclidean.GlobalLatticeRecovery

/-!
# The spinor-kernel target for strong approximation

O'Meara 104:4 approximates elements of `O'(V)`, the kernel of the proper
spinor norm. A proper adelic comparison must first be corrected by a global
proper transformation and a completed integral stabilizer. This file proves
that algebraic correction and the transfer of a hit back to the original
comparison. It does not assert the correction witnesses exist or prove
strong approximation.
-/

noncomputable section

namespace NormEuclidean.AdelicSpinorKernel

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
open AdelicApproximation

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

private theorem correctionNorm_eq_one {G C : Type*} [Group G] [Group C]
    (θ : G →* C) (a g s : G) (h : θ a = θ g * θ s) :
    θ (g⁻¹ * a * s⁻¹) = 1 := by
  rw [map_mul, map_mul, map_inv, map_inv, h, inv_mul_cancel_left, mul_inv_cancel]

/-- Local scalar extension respects multiplication of proper isometries. -/
theorem localizeProper_mul (g k : properGroup Q)
    (v : HeightOneSpectrum (integerSubring K)) :
    localizeProper Q (g * k) v = localizeProper Q g v * localizeProper Q k v := by
  apply Subtype.ext
  apply Subtype.ext
  exact LinearEquiv.baseChange_mul K (LocalField (integerSubring K) v) V g.1.1 k.1.1

/-- The actual global diagonal respects multiplication in the restricted product. -/
theorem finiteDiagonal_mul (L : Lattice (integerSubring K) Q) (g k : properGroup Q) :
    finiteDiagonal Q L (g * k) = finiteDiagonal Q L g * finiteDiagonal Q L k := by
  apply Subtype.ext
  funext v
  exact localizeProper_mul Q g k v

/-- The exact stabilizer coset for any restricted proper adelic element. -/
def InStabilizerCoset (L : Lattice (integerSubring K) Q)
    (a b : FiniteAdelicProperOrthogonal Q L) : Prop :=
  ∀ v : HeightOneSpectrum (integerSubring K),
    (a v)⁻¹ * b v ∈ properStabilizerWithin (form (integerSubring K) v Q)
      (carrier (integerSubring K) v L.carrier)

/-- Every component stabilizes the completed base lattice. -/
def IsIntegralAdelic (L : Lattice (integerSubring K) Q)
    (s : FiniteAdelicProperOrthogonal Q L) : Prop :=
  ∀ v : HeightOneSpectrum (integerSubring K),
    s v ∈ properStabilizerWithin (form (integerSubring K) v Q)
      (carrier (integerSubring K) v L.carrier)

/-- The comparison corrected on the left globally and on the right integrally. -/
def corrected (L : Lattice (integerSubring K) Q)
    (a : FiniteAdelicProperOrthogonal Q L) (g : properGroup Q)
    (s : FiniteAdelicProperOrthogonal Q L) : FiniteAdelicProperOrthogonal Q L :=
  (finiteDiagonal Q L g)⁻¹ * a * s⁻¹

/-- An element has trivial proper Wall spinor norm at every finite place. -/
def InSpinorKernel (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (a : FiniteAdelicProperOrthogonal Q L) : Prop :=
  ∀ v : HeightOneSpectrum (integerSubring K),
    properAmbientSpinorNormHom (form (integerSubring K) v Q)
      (form_polarBilin_nondegenerate (integerSubring K) v Q hQ) (a v) = 1

/-- The scalar correction puts the actual proper adelic element in the
spinor kernel. The norm identity is an explicit hypothesis. -/
theorem corrected_inSpinorKernel (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q)
    (a : FiniteAdelicProperOrthogonal Q L) (g : properGroup Q)
    (s : FiniteAdelicProperOrthogonal Q L)
    (hnorm : ∀ v : HeightOneSpectrum (integerSubring K),
      let θ := properAmbientSpinorNormHom (form (integerSubring K) v Q)
        (form_polarBilin_nondegenerate (integerSubring K) v Q hQ)
      θ (a v) = θ (localizeProper Q g v) * θ (s v)) :
    InSpinorKernel Q hQ L (corrected Q L a g s) := by
  intro v
  let θ := properAmbientSpinorNormHom (form (integerSubring K) v Q)
    (form_polarBilin_nondegenerate (integerSubring K) v Q hQ)
  exact correctionNorm_eq_one θ (a v) (localizeProper Q g v) (s v) (hnorm v)

/-- A global hit of the corrected coset gives a global hit of the original
comparison after multiplying by the correcting global transformation. -/
theorem hasGlobalProperHit_of_corrected_hit
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M) (g k : properGroup Q)
    (s : FiniteAdelicProperOrthogonal Q L) (hs : IsIntegralAdelic Q L s)
    (hk : InStabilizerCoset Q L (corrected Q L c.toAdelic g s) (finiteDiagonal Q L k)) :
    HasGlobalProperHit Q c := by
  refine ⟨g * k, ?_⟩
  intro v
  have hkv := hk v
  have hmul := (properStabilizerWithin (form (integerSubring K) v Q)
    (carrier (integerSubring K) v L.carrier)).mul_mem
      (Subgroup.inv_mem _ (hs v)) hkv
  change (s v)⁻¹ * ((((localizeProper Q g v)⁻¹ * c.toAdelic v) * (s v)⁻¹)⁻¹ *
    localizeProper Q k v) ∈ _ at hmul
  change (c.toAdelic v)⁻¹ * localizeProper Q (g * k) v ∈ _
  rw [localizeProper_mul]
  convert hmul using 1
  group

/-- The exact adelic spinor-kernel approximation input. An eventual theorem
asserting this proposition must supply rank and indefiniteness hypotheses.
No assertion of this proposition is made in this file. -/
def HasSpinorKernelStrongApproximation (hQ : Q.polarBilin.Nondegenerate) : Prop :=
  ∀ (L : Lattice (integerSubring K) Q) (a : FiniteAdelicProperOrthogonal Q L),
    InSpinorKernel Q hQ L a →
      ∃ k : properGroup Q,
        properAmbientSpinorNormHom Q hQ k = 1 ∧
          InStabilizerCoset Q L a (finiteDiagonal Q L k)

/-- Correcting witnesses and spinor-kernel strong approximation give a hit
of the original comparison. These witnesses, the norm identities, and the
approximation principle are all explicit inputs. -/
theorem hasGlobalProperHit_of_spinorKernelApproximation
    (hQ : Q.polarBilin.Nondegenerate)
    (happrox : HasSpinorKernelStrongApproximation Q hQ)
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M) (g : properGroup Q)
    (s : FiniteAdelicProperOrthogonal Q L) (hs : IsIntegralAdelic Q L s)
    (hnorm : ∀ v : HeightOneSpectrum (integerSubring K),
      let θ := properAmbientSpinorNormHom (form (integerSubring K) v Q)
        (form_polarBilin_nondegenerate (integerSubring K) v Q hQ)
      θ (c.toAdelic v) = θ (localizeProper Q g v) * θ (s v)) :
    HasGlobalProperHit Q c := by
  obtain ⟨k, _, hk⟩ := happrox L (corrected Q L c.toAdelic g s)
    (corrected_inSpinorKernel Q hQ L c.toAdelic g s hnorm)
  exact hasGlobalProperHit_of_corrected_hit Q c g k s hs hk

/-- The same explicit spinor inputs now yield an actual proper global
lattice isometry. Completion descent is supplied by the proved theorem. -/
theorem properlyGloballyIsometric_of_spinorKernelApproximation
    (hQ : Q.polarBilin.Nondegenerate)
    (happrox : HasSpinorKernelStrongApproximation Q hQ)
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M) (g : properGroup Q)
    (s : FiniteAdelicProperOrthogonal Q L) (hs : IsIntegralAdelic Q L s)
    (hnorm : ∀ v : HeightOneSpectrum (integerSubring K),
      let θ := properAmbientSpinorNormHom (form (integerSubring K) v Q)
        (form_polarBilin_nondegenerate (integerSubring K) v Q hQ)
      θ (c.toAdelic v) = θ (localizeProper Q g v) * θ (s v)) :
    ProperlyGloballyIsometric Q L M :=
  properlyGloballyIsometric_of_globalProperHit Q c
    (hasGlobalProperHit_of_spinorKernelApproximation Q hQ happrox c g s hs hnorm)

end NormEuclidean.AdelicSpinorKernel
