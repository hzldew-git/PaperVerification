import NormEuclidean.ChapterX.LocalComplementFrames
import NormEuclidean.ChapterX.OrthogonalBaseChange
import NormEuclidean.ChapterX.ExceptionalResidualSelection

/-!
# Binary frames in the literal completed lattice intersection

At an odd finite place, self-duality of the original completed lattice
constructs the required frame in the extended global complement. The local
uniformizer, primitive representative, splitting and tensor comparison are
all proved or constructed, not additional inputs.
-/

noncomputable section

namespace NormEuclidean.CompletedComplementFrames

open IsDedekindDomain CompletedIntegralLattice ProjectedComplement LocalPrimitivePairing
open scoped TensorProduct

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The actual completed lattice and its literal local intersection supply
the binary unit frame from unimodularity, without a supplied frame premise. -/
theorem binary_frame_of_selfDual (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (v : V) (hvL : v ∈ L) (hv : Q v ≠ 0)
    (p : HeightOneSpectrum (integerSubring K)) (htwo : IsUnit (2 : LocalRing _ p))
    (hL : SelfDual (LocalRing (integerSubring K) p) (halfPolar (form _ p Q))
      (carrier (integerSubring K) p L)) :
    ExceptionalResidualSelection.binaryUnitFrame p
      (form (integerSubring K) p (Q.comp (complement Q v).subtype))
      ((carrier (integerSubring K) p L).comap
        (((complement Q v).subtype.baseChange (LocalField (integerSubring K) p)).restrictScalars
          (LocalRing (integerSubring K) p))) := by
  let F := LocalField (integerSubring K) p
  let S := LocalRing (integerSubring K) p
  let E := Space (V := V) (integerSubring K) p
  let P := form (integerSubring K) p Q
  let M := carrier (integerSubring K) p L
  let x := inclusion (integerSubring K) p v
  letI : IsDiscreteValuationRing S :=
    inferInstanceAs (IsDiscreteValuationRing (p.adicCompletionIntegers K))
  letI : IsFractionRing S F :=
    inferInstanceAs (IsFractionRing (p.adicCompletionIntegers K) (p.adicCompletion K))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hπF : (π : F) ≠ 0 := by exact_mod_cast hπ.ne_zero
  have hxval : P x = algebraMap K F (Q v) := form_inclusion _ p Q v
  have hx0 : x ≠ 0 := by
    intro hx
    have h : algebraMap K F (Q v) = 0 := by rw [← hxval, hx, P.map_zero]
    exact hv ((algebraMap K F).injective (h.trans (map_zero _).symm))
  have hP : P.polarBilin.Nondegenerate := form_polarBilin_nondegenerate _ p Q hQ
  have hdimE : 4 ≤ Module.finrank F E := by
    change 4 ≤ Module.finrank F (F ⊗[K] V)
    simpa only [Module.finrank_tensorProduct, Module.finrank_self, one_mul] using hdim
  obtain ⟨a, b, e, f, he, hf, ha, hb, hef, hxe, hxf⟩ :=
    LocalComplementFrames.exists_binary_frame_in_orthogonal S (halfPolar P)
      ⟨halfPolar_comm P⟩ (SpinorBridge.quadraticSpace P hP).nondegenerate
      M (carrier_fg _ p L hfg) (carrier_full _ p L hfull) hL hdimE
      ⟨x, inclusion_mem _ p L hvL⟩ hx0 π hπF hπ.not_isUnit hπ.maximalIdeal_eq htwo
  have hself (y : E) : halfPolar P y y = P y := by
    simp [halfPolar_apply, P.polar_self, nsmul_eq_mul]
  have hzero (y z : E) (h : halfPolar P y z = 0) : P.polarBilin y z = 0 := by
    change (2 : F)⁻¹ * P.polarBilin y z = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num))
  obtain ⟨eU, heU, heQ⟩ := OrthogonalBaseChange.exists_lift Q v e (hzero _ _ hxe)
  obtain ⟨fU, hfU, hfQ⟩ := OrthogonalBaseChange.exists_lift Q v f (hzero _ _ hxf)
  refine ⟨a, b, eU, fU, ?_, ?_, ?_, ?_, ?_⟩
  · change (complement Q v).subtype.baseChange F eU ∈ M
    rwa [heU]
  · change (complement Q v).subtype.baseChange F fU ∈ M
    rwa [hfU]
  · exact heQ.trans ((hself e).symm.trans ha)
  · exact hfQ.trans ((hself f).symm.trans hb)
  · change (QuadraticForm.baseChange F (Q.comp (complement Q v).subtype)).polarBilin eU fU = 0
    rw [← OrthogonalBaseChange.form_comp_subtype (F := F) Q v]
    rw [QuadraticMap.polarBilin_comp]
    change (Q.baseChange F).polarBilin
      ((complement Q v).subtype.baseChange F eU) ((complement Q v).subtype.baseChange F fU) = 0
    rw [heU, hfU]
    exact hzero _ _ hef

end NormEuclidean.CompletedComplementFrames
