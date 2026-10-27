import NormEuclidean.CompletedIdealQuotients
import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Actual integral density and closure of completed global ideals

The canonical prime-power quotient equivalences imply approximation at
every original valuation precision. Thus the global integers are dense
in the original completed integer ring. Taking the topological closure
of a global ideal image agrees with extending that ideal to this ring.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedIntegerDensity

open IsDedekindDomain Bong.NumberFieldCompletion CompletedIdealQuotients
open Filter Set Topology
open scoped NumberField WithZero

variable {F : Type*} [Field F] [NumberField F]

/-- Every original completed integer has global integral approximations at all precisions. -/
theorem exists_valuation_close (v : HeightOneSpectrum (𝓞 F)) (x : integerRing v)
    (γ : (ℤᵐ⁰)ˣ) :
    ∃ a : 𝓞 F, Valued.v (((integerEmbedding v a : integerRing v) : v.adicCompletion F) -
      (x : v.adicCompletion F)) < γ := by
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt (Units.ne_zero γ)
  obtain ⟨a, ha⟩ := exists_integral_lift v n x
  exact ⟨a, ((mem_maximal_power_iff v _ n).mp ha).trans_lt hn⟩

/-- The original global integer embedding is dense in the actual completed integer ring. -/
theorem denseRange (v : HeightOneSpectrum (𝓞 F)) : DenseRange (integerEmbedding v) := by
  intro x
  apply mem_closure_iff_nhds.mpr
  intro U hU
  obtain ⟨T, hT, hTU⟩ := (mem_nhds_subtype _ x U).mp hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hT
  let δ : (ℤᵐ⁰)ˣ := Units.mk0 (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
    (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  obtain ⟨a, ha⟩ := exists_valuation_close v x δ
  refine ⟨integerEmbedding v a, hTU ?_, ⟨a, rfl⟩⟩
  apply hγ
  exact (Valuation.restrict_lt_iff_lt_embedding _).mpr ha

/-- Dense scalar coefficients identify the closures of the image and of the extended ideal. -/
theorem closure_image_eq_closure_map {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace S] [IsTopologicalRing S] (f : R →+* S) (hf : DenseRange f) (I : Ideal R) :
    closure (f '' (I : Set R)) = closure (I.map f : Set S) := by
  let A := I.toAddSubgroup.map f.toAddMonoidHom
  let J : Ideal S := {
    A.topologicalClosure with
    smul_mem' := by
      intro b x hx
      change b * x ∈ closure (A : Set S)
      refine hf.induction_on (p := fun c ↦ c * x ∈ closure (A : Set S)) b
        (isClosed_closure.preimage (continuous_id.mul continuous_const)) ?_
      intro a
      apply map_mem_closure (continuous_const.mul continuous_id) hx
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨a * c, I.mul_mem_left a hc, map_mul f a c⟩ }
  have hJ : I.map f ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact subset_closure ⟨a, ha, rfl⟩
  apply subset_antisymm
  · exact closure_mono (by rintro _ ⟨a, ha, rfl⟩; exact Ideal.mem_map_of_mem f ha)
  · exact closure_minimal hJ isClosed_closure

/-- Extension of a global ideal is literally the closure of its original integral image. -/
theorem ideal_closure (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) :
    closure (integerEmbedding v '' (I : Set (𝓞 F))) =
      (I.map (integerEmbedding v) : Set (integerRing v)) := by
  rw [closure_image_eq_closure_map _ (denseRange v)]
  let a := Submodule.IsPrincipal.generator (I.map (integerEmbedding v))
  have hs : Ideal.span ({a} : Set (integerRing v)) = I.map (integerEmbedding v) :=
    Ideal.span_singleton_generator _
  have he : (I.map (integerEmbedding v) : Set (integerRing v)) =
      range (fun x : integerRing v ↦ a * x) := by
    ext x
    change x ∈ I.map (integerEmbedding v) ↔ ∃ y, a * y = x
    rw [← hs, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩
  apply IsClosed.closure_eq
  rw [he]
  letI := CompletedHaarDensity.completedCompact v
  exact (isCompact_range (continuous_const.mul continuous_id)).isClosed

end NormEuclidean.CompletedIntegerDensity
