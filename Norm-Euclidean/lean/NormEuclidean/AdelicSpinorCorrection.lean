import NormEuclidean.SpinorBaseChange

/-!
# Realizing idelic spinor corrections by actual isometries

Membership in the lifted local spinor images supplies actual proper integral
isometries at every finite place. These form a restricted adelic stabilizer.
The scalar idele decomposition and the explicit two-reflection global
correction then supply the norm identities required by `AdelicSpinorKernel`.
Strong approximation remains a separate explicit input.
-/

noncomputable section

namespace NormEuclidean.AdelicSpinorCorrection

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
open AdelicApproximation AdelicSpinorKernel

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)

/-- Kernel approximation at one fixed base lattice. This is the geometric
input still to be proved, not an assertion of a density theorem. -/
def HasSpinorKernelApproximationAt (L : Lattice (integerSubring K) Q) : Prop :=
  ∀ a : FiniteAdelicProperOrthogonal Q L, InSpinorKernel Q hQ L a →
    ∃ k : properGroup Q, properAmbientSpinorNormHom Q hQ k = 1 ∧
      InStabilizerCoset Q L a (finiteDiagonal Q L k)

/-- A uniform spinor-kernel approximation theorem would supply the fixed-lattice input. -/
theorem kernelApproximationAt_of_uniform
    (happrox : HasSpinorKernelStrongApproximation Q hQ) (L : Lattice (integerSubring K) Q) :
    HasSpinorKernelApproximationAt Q hQ L := happrox L

/-- An idele in the lifted local spinor images is realized by an actual
restricted proper integral adelic stabilizer. -/
theorem exists_integralAdelic_of_finiteSpinorIdele
    (L : Lattice (integerSubring K) Q)
    (b : (FiniteAdeleRing (integerSubring K) K)ˣ)
    (hb : b ∈ AdelicSpinor.finiteSpinorIdeles (integerSubring K) Q hQ L) :
    ∃ s : FiniteAdelicProperOrthogonal Q L,
      IsIntegralAdelic Q L s ∧
        ∀ v : HeightOneSpectrum (integerSubring K),
          properAmbientSpinorNormHom (form (integerSubring K) v Q)
              (form_polarBilin_nondegenerate (integerSubring K) v Q hQ) (s v) =
            Bong.Dyadic.squareClass (LocalField (integerSubring K) v)
              (FiniteIdele.componentUnit v b) := by
  classical
  have hmem := (AdelicSpinor.mem_finiteSpinorIdeles_iff (integerSubring K) Q hQ L b).mp hb
  have hex : ∀ v : HeightOneSpectrum (integerSubring K),
      ∃ g : properGroup (form (integerSubring K) v Q),
        g ∈ properStabilizerWithin (form (integerSubring K) v Q)
            (carrier (integerSubring K) v L.carrier) ∧
          properAmbientSpinorNormHom (form (integerSubring K) v Q)
              (form_polarBilin_nondegenerate (integerSubring K) v Q hQ) g =
            Bong.Dyadic.squareClass (LocalField (integerSubring K) v)
              (FiniteIdele.componentUnit v b) := by
    intro v
    obtain ⟨e, he, hn⟩ := (mem_properSpinorImage_iff _ _ _ _).mp (hmem v)
    exact ⟨properAmbientOfLatticeIsometry e he, e.mem_iff, hn⟩
  choose g hg hn using hex
  let s : FiniteAdelicProperOrthogonal Q L := ⟨g, Filter.Eventually.of_forall hg⟩
  exact ⟨s, hg, hn⟩

set_option maxHeartbeats 800000 in
/-- In the PID branch, the scalar idele decomposition gives actual correcting
isometries and the local norm identities for the normalized hyperbolic comparison. -/
theorem exists_hyperbolicSpinorCorrection_of_sameProperGenus
    [IsPrincipalIdealRing (integerSubring K)]
    (L : Lattice (integerSubring K) Q)
    {M : Lattice (integerSubring K) (Hyperbolic.form Q)}
    (h : SameProperGenus (Hyperbolic.form Q) L.hyperbolic M) :
    ∃ g : properGroup (Hyperbolic.form Q),
      ∃ s : FiniteAdelicProperOrthogonal (Hyperbolic.form Q) L.hyperbolic,
        IsIntegralAdelic (Hyperbolic.form Q) L.hyperbolic s ∧
          ∀ v : HeightOneSpectrum (integerSubring K),
            let θ := properAmbientSpinorNormHom (form (integerSubring K) v (Hyperbolic.form Q))
              (form_polarBilin_nondegenerate (integerSubring K) v (Hyperbolic.form Q)
                (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
            θ ((comparisonOfSameProperGenus h).toAdelic v) =
              θ (localizeProper (Hyperbolic.form Q) g v) * θ (s v) := by
  let hH := Hyperbolic.form_polarBilin_nondegenerate Q hQ
  obtain ⟨k, b, hdecomp⟩ :=
    AdelicComparison.hyperbolic_fullComparisonSpinorIdele_decomposition Q hQ L h
  have hb : AdelicSpinor.finiteProjection (integerSubring K) b.1 ∈
      AdelicSpinor.finiteSpinorIdeles (integerSubring K) (Hyperbolic.form Q) hH L.hyperbolic :=
    b.2.1
  obtain ⟨s, hs, hsnorm⟩ := exists_integralAdelic_of_finiteSpinorIdele (Hyperbolic.form Q)
    hH L.hyperbolic (AdelicSpinor.finiteProjection (integerSubring K) b.1) hb
  refine ⟨SpinorBaseChange.hyperbolicCorrection Q hQ k, s, hs, ?_⟩
  intro v
  have hcomp :
      FiniteIdele.componentUnit v (AdelicComparison.finiteComparisonSpinorIdele hH h) =
        Units.map (algebraMap K (LocalField (integerSubring K) v)) k *
          FiniteIdele.componentUnit v (AdelicSpinor.finiteProjection (integerSubring K) b.1) := by
    have hcomponent := congrArg (fun a ↦
      FiniteIdele.componentUnit v (AdelicSpinor.finiteProjection (integerSubring K) a)) hdecomp
    simpa only [AdelicComparison.fullComparisonSpinorIdele,
      AdelicComparison.finiteProjection_fullOfFiniteIdele, map_mul,
      AdelicSpinor.finiteProjection_diagonal, FiniteIdele.componentUnit_diagonal] using hcomponent
  let θ := properAmbientSpinorNormHom (form (integerSubring K) v (Hyperbolic.form Q))
    (form_polarBilin_nondegenerate (integerSubring K) v (Hyperbolic.form Q) hH)
  calc
    θ ((comparisonOfSameProperGenus h).toAdelic v) =
        Bong.Dyadic.squareClass (LocalField (integerSubring K) v)
          (FiniteIdele.componentUnit v (AdelicComparison.finiteComparisonSpinorIdele hH h)) :=
      (AdelicComparison.squareClass_component_finiteComparisonSpinorIdele hH h v).symm
    _ = _ := congrArg (Bong.Dyadic.squareClass (LocalField (integerSubring K) v)) hcomp
    _ = Bong.Dyadic.squareClass (LocalField (integerSubring K) v)
          (Units.map (algebraMap K (LocalField (integerSubring K) v)) k) *
        Bong.Dyadic.squareClass (LocalField (integerSubring K) v)
          (FiniteIdele.componentUnit v (AdelicSpinor.finiteProjection (integerSubring K) b.1)) :=
      map_mul (QuotientGroup.mk' (Subgroup.square (LocalField (integerSubring K) v)ˣ)) _ _
    _ = θ (localizeProper (Hyperbolic.form Q) (SpinorBaseChange.hyperbolicCorrection Q hQ k) v) *
        θ (s v) := congrArg₂ (· * ·)
      (SpinorBaseChange.hyperbolicCorrection_localSpinorNorm Q hQ k v).symm (hsnorm v).symm

/-- The normalized hyperbolic comparison admits actual global and integral
corrections whose corrected adelic element lies in the spinor kernel. -/
theorem exists_hyperbolicComparison_inSpinorKernel
    [IsPrincipalIdealRing (integerSubring K)]
    (L : Lattice (integerSubring K) Q)
    {M : Lattice (integerSubring K) (Hyperbolic.form Q)}
    (h : SameProperGenus (Hyperbolic.form Q) L.hyperbolic M) :
    ∃ g : properGroup (Hyperbolic.form Q),
      ∃ s : FiniteAdelicProperOrthogonal (Hyperbolic.form Q) L.hyperbolic,
        IsIntegralAdelic (Hyperbolic.form Q) L.hyperbolic s ∧
          InSpinorKernel (Hyperbolic.form Q) (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
            L.hyperbolic (corrected (Hyperbolic.form Q) L.hyperbolic
              (comparisonOfSameProperGenus h).toAdelic g s) := by
  obtain ⟨g, s, hs, hn⟩ := exists_hyperbolicSpinorCorrection_of_sameProperGenus Q hQ L h
  exact ⟨g, s, hs, corrected_inSpinorKernel (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic
    (comparisonOfSameProperGenus h).toAdelic g s hn⟩

/-- The fixed hyperbolic kernel approximation input now gives a global hit
without any externally supplied correcting isometries or norm identity. -/
theorem hyperbolic_hasGlobalProperHit_of_kernelApproximation
    [IsPrincipalIdealRing (integerSubring K)]
    (L : Lattice (integerSubring K) Q)
    (happrox : HasSpinorKernelApproximationAt (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic)
    {M : Lattice (integerSubring K) (Hyperbolic.form Q)}
    (h : SameProperGenus (Hyperbolic.form Q) L.hyperbolic M) :
    HasGlobalProperHit (Hyperbolic.form Q) (comparisonOfSameProperGenus h) := by
  obtain ⟨g, s, hs, hkernel⟩ := exists_hyperbolicComparison_inSpinorKernel Q hQ L h
  obtain ⟨k, _, hk⟩ := happrox _ hkernel
  exact hasGlobalProperHit_of_corrected_hit (Hyperbolic.form Q)
    (comparisonOfSameProperGenus h) g k s hs hk

/-- The global integral isometry follows from the fixed-lattice kernel
approximation input, with both correction and completion descent proved. -/
theorem hyperbolic_properlyGloballyIsometric_of_kernelApproximation
    [IsPrincipalIdealRing (integerSubring K)]
    (L : Lattice (integerSubring K) Q)
    (happrox : HasSpinorKernelApproximationAt (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic)
    {M : Lattice (integerSubring K) (Hyperbolic.form Q)}
    (h : SameProperGenus (Hyperbolic.form Q) L.hyperbolic M) :
    ProperlyGloballyIsometric (Hyperbolic.form Q) L.hyperbolic M :=
  properlyGloballyIsometric_of_globalProperHit (Hyperbolic.form Q)
    (comparisonOfSameProperGenus h)
    (hyperbolic_hasGlobalProperHit_of_kernelApproximation Q hQ L happrox h)

/-- Proper class number one in the ordinary hyperbolic genus, conditional
only on spinor-kernel approximation at this fixed base lattice. -/
theorem hyperbolic_hasProperLatticeClassNumberOne_of_kernelApproximation
    [IsPrincipalIdealRing (integerSubring K)]
    (L : Lattice (integerSubring K) Q)
    (happrox : HasSpinorKernelApproximationAt (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic) :
    HasProperLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic := by
  rw [hasProperLatticeClassNumberOne_iff]
  intro M hgen
  have hproper := (hyperbolic_sameGenus_iff_sameProperGenus Q hQ L M).mp hgen
  exact hyperbolic_properlyGloballyIsometric_of_kernelApproximation Q hQ L happrox hproper

/-- The ordinary class-number conclusion follows by forgetting properness. -/
theorem hyperbolic_hasLatticeClassNumberOne_of_kernelApproximation
    [IsPrincipalIdealRing (integerSubring K)]
    (L : Lattice (integerSubring K) Q)
    (happrox : HasSpinorKernelApproximationAt (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic) :
    HasLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic :=
  hasLatticeClassNumberOne_of_proper (Hyperbolic.form Q) L.hyperbolic
    (hyperbolic_hasProperLatticeClassNumberOne_of_kernelApproximation Q hQ L happrox)

end NormEuclidean.AdelicSpinorCorrection
