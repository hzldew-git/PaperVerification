import NormEuclidean.HyperbolicSpinorMap
import NormEuclidean.AdelicComparison
import NormEuclidean.AdelicApproximation

/-!
# The hyperbolic block embedding at actual finite completions

The tensor/product equivalence transports the block embedding to the actual
completed space. It preserves integral comparisons and the Wall spinor norm.
-/

noncomputable section

namespace NormEuclidean.CompletedHyperbolicSpinorMap

open IsDedekindDomain CompletedIntegralLattice ProperSpinor OrthogonalTransport
open AdelicOrthogonal
open scoped TensorProduct

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

local instance finiteCharZero (p : HeightOneSpectrum (integerSubring K)) :
    CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _

/-- The actual completed hyperbolic block embedding. -/
def localMap (p : HeightOneSpectrum (integerSubring K))
    (g : properGroup (form (integerSubring K) p Q)) :
    properGroup (form (integerSubring K) p (Hyperbolic.form Q)) :=
  properMap (Hyperbolic.form (form (integerSubring K) p Q))
    (form (integerSubring K) p (Hyperbolic.form Q)) (hyperbolicEquiv _ p).symm
    (inverse_value _ _ (hyperbolicEquiv _ p) (hyperbolicEquiv_form _ p Q))
    (HyperbolicSpinorMap.properMap _ g)

@[simp] theorem localMap_apply (p : HeightOneSpectrum (integerSubring K))
    (g : properGroup (form (integerSubring K) p Q))
    (z : Space (V := Hyperbolic K V) (integerSubring K) p) :
    (localMap Q p g).1.1 z = (hyperbolicEquiv _ p).symm
      (g.1.1 (hyperbolicEquiv _ p z).1, (hyperbolicEquiv _ p z).2) := rfl

@[simp] theorem localMap_one (p : HeightOneSpectrum (integerSubring K)) :
    localMap Q p 1 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  exact (hyperbolicEquiv _ p).symm_apply_apply z

/-- At each actual completion the block embedding preserves the proper Wall norm. -/
theorem localMap_spinorNorm (hQ : Q.polarBilin.Nondegenerate)
    (p : HeightOneSpectrum (integerSubring K)) (g : properGroup (form (integerSubring K) p Q)) :
    properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
      (form_polarBilin_nondegenerate _ p _ (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
      (localMap Q p g) =
        properAmbientSpinorNormHom (form (integerSubring K) p Q)
          (form_polarBilin_nondegenerate _ p Q hQ) g := by
  rw [localMap, proper_spinorNorm_map]
  exact HyperbolicSpinorMap.proper_spinorNorm_map _
    (form_polarBilin_nondegenerate _ p Q hQ) g

/-- Actual local lattice comparisons remain comparisons after adjoining the plane. -/
theorem localMap_mem_iff (L M : Lattice (integerSubring K) Q)
    (p : HeightOneSpectrum (integerSubring K)) (g : properGroup (form (integerSubring K) p Q))
    (hg : ∀ x, g.1.1 x ∈ carrier (integerSubring K) p M.carrier ↔
      x ∈ carrier (integerSubring K) p L.carrier)
    (z : Space (V := Hyperbolic K V) (integerSubring K) p) :
    (localMap Q p g).1.1 z ∈ carrier (integerSubring K) p M.hyperbolic.carrier ↔
      z ∈ carrier (integerSubring K) p L.hyperbolic.carrier := by
  change (localMap Q p g).1.1 z ∈ carrier _ p (Hyperbolic.submodule M.carrier) ↔
    z ∈ carrier _ p (Hyperbolic.submodule L.carrier)
  rw [localMap_apply, ← hyperbolicEquiv_carrier, ← hyperbolicEquiv_carrier,
    LinearEquiv.apply_symm_apply]
  change (g.1.1 (hyperbolicEquiv _ p z).1 ∈ carrier _ p M.carrier ∧
      (hyperbolicEquiv _ p z).2.1 ∈ LocalRing _ p ∧
      (hyperbolicEquiv _ p z).2.2 ∈ LocalRing _ p) ↔ _
  rw [hg]
  rfl

/-- Completing a global block extension equals extending the completed transformation. -/
theorem localMap_localizeProper (g : properGroup Q)
    (p : HeightOneSpectrum (integerSubring K)) :
    localMap Q p (AdelicApproximation.localizeProper Q g p) =
      AdelicApproximation.localizeProper (Hyperbolic.form Q)
        (HyperbolicSpinorMap.properMap Q g) p := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  rw [localMap_apply]
  apply (hyperbolicEquiv _ p).symm_apply_eq.mpr
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      simp [AdelicApproximation.localizeProper, equiv, HyperbolicSpinorMap.properMap,
        HyperbolicSpinorMap.ambientMap, hyperbolicEquiv_tmul]
  | add z w hz hw =>
      simpa only [map_add, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] using
        congrArg₂ (· + ·) hz hw

/-- Extend the normalized original-genus comparison, retaining finite support. -/
def comparison {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M) :
    FiniteAdelicProperComparison (Hyperbolic.form Q) L.hyperbolic M.hyperbolic where
  toAdelic := ⟨fun p ↦ localMap Q p (localComparison h p), by
    filter_upwards [carrier_eventually_eq (integerSubring K) L M] with p hp
    rw [localComparison_of_carrier_eq h p hp, localMap_one]
    exact Subgroup.one_mem _⟩
  maps_carrier := fun p ↦ localMap_mem_iff Q L M p _ (localComparison_maps_carrier h p)

/-- Its spinor norms are precisely those of the original binary comparison. -/
theorem comparison_spinorNorm (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (p : HeightOneSpectrum (integerSubring K)) :
    properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
      (form_polarBilin_nondegenerate _ p _ (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
      ((comparison Q h).toAdelic p) = AdelicComparison.localSpinorNorm hQ h p :=
  localMap_spinorNorm Q hQ p (localComparison h p)

local instance infiniteCharZero (v : NumberField.InfinitePlace K) :
    CharZero v.Completion := Algebra.charZero_of_charZero K _

/-- The block embedding on the actual real or complex completed tensor space. -/
def infiniteMap (v : NumberField.InfinitePlace K)
    (g : properGroup (ArchimedeanComparison.form v Q)) :
    properGroup (ArchimedeanComparison.form v (Hyperbolic.form Q)) :=
  properMap (Hyperbolic.form (ArchimedeanComparison.form v Q))
    (ArchimedeanComparison.form v (Hyperbolic.form Q))
    (ArchimedeanComparison.hyperbolicIsometry v Q).toLinearEquiv.symm
    (inverse_value _ _ (ArchimedeanComparison.hyperbolicIsometry v Q).toLinearEquiv
      (ArchimedeanComparison.hyperbolicIsometry v Q).map_app)
    (HyperbolicSpinorMap.properMap _ g)

/-- The proper Wall norm equality also holds at every actual infinite completion. -/
theorem infiniteMap_spinorNorm (hQ : Q.polarBilin.Nondegenerate)
    (v : NumberField.InfinitePlace K) (g : properGroup (ArchimedeanComparison.form v Q)) :
    properAmbientSpinorNormHom (ArchimedeanComparison.form v (Hyperbolic.form Q))
      (archimedean_form_polarBilin_nondegenerate v
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) (infiniteMap Q v g) =
      properAmbientSpinorNormHom (ArchimedeanComparison.form v Q)
        (archimedean_form_polarBilin_nondegenerate v hQ) g := by
  rw [infiniteMap, proper_spinorNorm_map]
  exact HyperbolicSpinorMap.proper_spinorNorm_map _
    (archimedean_form_polarBilin_nondegenerate v hQ) g

end NormEuclidean.CompletedHyperbolicSpinorMap
