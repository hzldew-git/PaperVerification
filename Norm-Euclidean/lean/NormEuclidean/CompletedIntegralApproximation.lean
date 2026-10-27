import NormEuclidean.CompletedIntegerDensity

/-!
# Simultaneous integral approximation in original finite completions

The actual prime-power quotient equivalences and Chinese remainders
give arbitrary independent integral precisions. Consequently the
global integers are dense in every finite product of distinct original
completed integer rings, without an approximation hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedIntegralApproximation

open IsDedekindDomain IsLocalRing Bong.NumberFieldCompletion
open CompletedIdealQuotients Filter Set Topology
open scoped NumberField WithZero

variable {F : Type*} [Field F] [NumberField F]
variable {J : Type*} [Fintype J] (v : J → HeightOneSpectrum (𝓞 F))

/-- Global integral representatives achieve every simultaneous completed prime-power precision. -/
theorem simultaneous (hv : Function.Injective v) (n : J → ℕ)
    (x : (j : J) → integerRing (v j)) :
    ∃ a : 𝓞 F, ∀ j, integerEmbedding (v j) a - x j ∈ maximalIdeal (integerRing (v j)) ^ n j := by
  classical
  choose b hb using fun j ↦ exists_integral_lift (v j) (n j) (x j)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun j ↦ (v j).asIdeal) n (fun j _ ↦ (v j).irreducible.prime)
    (fun i _ j _ hij h ↦ hij (hv (HeightOneSpectrum.ext_iff.mpr h))) (fun j ↦ b j.1)
  refine ⟨a, fun j ↦ ?_⟩
  have hab : integerEmbedding (v j) a - integerEmbedding (v j) (b j) ∈
      maximalIdeal (integerRing (v j)) ^ n j := by
    rw [← map_sub, embedding_mem_power]
    exact ha j (Finset.mem_univ j)
  simpa only [sub_add_sub_cancel] using
    (maximalIdeal (integerRing (v j)) ^ n j).add_mem hab (hb j)

/-- Density of the actual global integer diagonal in a finite product of original integral rings. -/
theorem denseRange (hv : Function.Injective v) :
    DenseRange (fun a : 𝓞 F ↦ fun j ↦ integerEmbedding (v j) a) := by
  intro x
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨S, _, W, hW, hWU⟩ := Filter.mem_pi.mp hU
  choose T hT hTW using fun j ↦ (mem_nhds_subtype _ (x j) (W j)).mp (hW j)
  choose γ hγ using fun j ↦ Valued.mem_nhds.mp (hT j)
  choose n hn using fun j ↦ WithZero.exists_exp_neg_natCast_lt
    (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero (γ j))
  obtain ⟨a, ha⟩ := simultaneous v hv n x
  refine ⟨fun j ↦ integerEmbedding (v j) a, hWU ?_, ⟨a, rfl⟩⟩
  intro j _
  apply hTW j
  apply hγ j
  apply (Valuation.restrict_lt_iff_lt_embedding _).mpr
  exact ((mem_maximal_power_iff (v j) _ (n j)).mp (ha j)).trans_lt (hn j)

end NormEuclidean.CompletedIntegralApproximation
