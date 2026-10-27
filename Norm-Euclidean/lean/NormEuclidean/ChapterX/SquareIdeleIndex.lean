import NormEuclidean.ChapterX.FiniteSquareWeight
import NormEuclidean.ChapterX.InfiniteSquareIndex
import NormEuclidean.ChapterX.SeparatingSUnitPrimes
import NormEuclidean.ChapterX.SquareIdeles

/-!
# O'Meara 65:12: the initial square-idele index

The local square indices are multiplied using the product formula at two.
The principal intersection is the S-unit square subgroup by 65:11.
Their index balance gives the initial index used by the strict chain.
-/

noncomputable section

namespace NormEuclidean.SquareIdeleIndex

open IsDedekindDomain ExtensionIdeleNorm NormIndexProduct SUnitNormArithmetic
open SquareIdeles
open scoped NumberField NormEuclidean.NormIndexProduct

variable {K : Type*} [Field K] [NumberField K]

/-- Local square subgroups at the excluded finite places and all infinite places. -/
def localSquare {S : Set (HeightOneSpectrum (𝓞 K))} (q : Index S) :
    Subgroup (UnitsAt q) := Subgroup.square (UnitsAt q)

/-- The product-formula weight of two at each relevant place. -/
def weight {S : Set (HeightOneSpectrum (𝓞 K))} : Index S → ℝ
  | .inl p => ‖(2 : p.1.adicCompletion K)‖
  | .inr v => v (2 : K) ^ v.mult

/-- Each local square index times its weight is four. -/
theorem local_balance {S : Set (HeightOneSpectrum (𝓞 K))} (q : Index S) :
    ((localSquare q).index : ℝ) * weight q = 4 := by
  cases q with
  | inl p => exact FiniteSquareWeight.index_mul_two p.1
  | inr v => exact InfiniteSquareIndex.index_mul_two v

/-- Omitting the odd finite places in S does not change the product formula at two. -/
theorem weight_product (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal) :
    letI : Fintype ↥(Sᶜ) := hS.fintype
    ∏ q : Index S, weight q = 1 := by
  classical
  letI : Fintype ↥(Sᶜ) := hS.fintype
  have hf : (∏ p : ↥(Sᶜ), ‖(2 : p.1.adicCompletion K)‖) =
      ∏ᶠ v : NumberField.FinitePlace K, v (2 : K) := by
    rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm]
    simp only [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply]
    have hs : Function.mulSupport
        (fun p : HeightOneSpectrum (𝓞 K) ↦ ‖(2 : p.adicCompletion K)‖) ⊆ Sᶜ := by
      intro p hp
      by_contra hn
      have hpS : p ∈ S := by simpa using hn
      exact hp (FiniteSquareWeight.norm_two_odd p (htwo p hpS))
    have h := finprod_eq_prod_of_mulSupport_subset_of_finite _ hs hS
    have he := Finset.prod_subtype (p := fun p ↦ p ∈ Sᶜ) (F := hS.fintype)
      hS.toFinset (fun p ↦ hS.mem_toFinset)
      (fun p : HeightOneSpectrum (𝓞 K) ↦ ‖(2 : p.adicCompletion K)‖)
    simpa only [map_ofNat] using (he.symm.trans h.symm)
  rw [Fintype.prod_sum_type]
  change (∏ p : ↥(Sᶜ), ‖(2 : p.1.adicCompletion K)‖) *
    (∏ v : NumberField.InfinitePlace K, v (2 : K) ^ v.mult) = 1
  rw [hf, mul_comm]
  exact NumberField.prod_abs_eq_one (by norm_num : (2 : K) ≠ 0)

/-- The number of excluded places, including all infinite places, is rank plus one. -/
theorem place_count (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    Nat.card (Index S) = Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1 := by
  letI : Finite ↥(Sᶜ) := hS.to_subtype
  rw [Nat.card_sum, SUnitRanks.finrank_sUnits S hS]
  have hK : 0 < Nat.card (NumberField.InfinitePlace K) := Nat.card_pos
  simp only [NumberField.Units.rank, ← Nat.card_eq_fintype_card]
  omega

/-- The product of the local square indices is four to rank plus one. -/
theorem local_index_product (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal) :
    letI : Fintype ↥(Sᶜ) := hS.fintype
    ∏ q : Index S, (localSquare q).index =
      4 ^ (Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1) := by
  classical
  letI : Fintype ↥(Sᶜ) := hS.fintype
  have h := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun q _ ↦ local_balance (S := S) q)
  rw [Finset.prod_mul_distrib, weight_product S hS htwo, mul_one,
    Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, place_count S hS] at h
  exact_mod_cast h

/-- Evaluation identifies square S-ideles with the local square product. -/
theorem square_preimage (S : Set (HeightOneSpectrum (𝓞 K))) :
    (Subgroup.pi Set.univ (localSquare (S := S))).comap (evaluation S) =
      (squareS S).subgroupOf (finitePlaceSIdeleSubgroup S) := by
  ext x
  change (∀ q ∈ Set.univ, IsSquare (evaluation S x q)) ↔ _
  simp only [Set.mem_univ, forall_const, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact ⟨x.property, fun p hp ↦ h (.inl ⟨p, hp⟩), fun v ↦ h (.inr v)⟩
  · rintro ⟨_, hf, hi⟩ q
    cases q with
    | inl p => exact hf p.1 p.2
    | inr v => exact hi v

/-- The relative index inside S-ideles is the proved product of local counts. -/
theorem relative_index (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal) :
    (squareS S).relIndex (finitePlaceSIdeleSubgroup S) =
      4 ^ (Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1) := by
  letI : Fintype ↥(Sᶜ) := hS.fintype
  change ((squareS S).subgroupOf (finitePlaceSIdeleSubgroup S)).index = _
  rw [← square_preimage]
  exact (Subgroup.index_comap_of_surjective _ (evaluation_surjective S hS)).trans
    ((index_dependent_pi _ _).trans (local_index_product S hS htwo))

/-- The principal preimage of square S-ideles is precisely the S-unit square subgroup. -/
theorem principal_preimage (S : Set (HeightOneSpectrum (𝓞 K)))
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) :
    (squareS S).comap (SUnitIdeleIndex.principalSUnits S) =
      Subgroup.square (sUnitSubgroup S) := by
  ext x
  constructor
  · intro hx
    change IsSquare x
    apply SeparatingSUnitPrimes.square_root_mem S x
    let e : Empty → sUnitSubgroup S := Empty.elim
    let p : Empty → HeightOneSpectrum (𝓞 K) := Empty.elim
    have hs : PrimeSquareDetection.Separates S e p := by
      refine ⟨?_, ?_, ?_⟩ <;> intro i <;> exact Empty.elim i
    apply PrimeSquareDetection.isSquare_of_punctured_units S e p hs htwo hprincipal x.val
    · exact fun q hq _ ↦ x.property q hq
    · intro q hq
      exact (GlobalSquare.unit_square_iff
        (Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom x.val)).mp (hx.2.1 q hq)
    · intro v
      exact (GlobalSquare.unit_square_iff
        (Units.map (algebraMap K v.Completion).toMonoidHom x.val)).mp (hx.2.2 v)
  · intro hx
    obtain ⟨y, hy⟩ := (show IsSquare x from hx)
    refine ⟨(sUnitSubgroup_eq_comap S).le x.property, ?_, ?_⟩
    · intro p hp
      rw [show x = y * y from hy, map_mul, map_mul]
      exact ⟨_, rfl⟩
    · intro v
      rw [show x = y * y from hy, map_mul, map_mul]
      exact ⟨_, rfl⟩

/-- The principal-intersection index is two to rank plus one. -/
theorem principal_index (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) :
    (squareS S).relIndex (idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) =
      2 ^ (Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1) := by
  let A := sUnitSubgroup S
  letI : Module.Finite ℤ (Additive A) := SUnitFiniteness.moduleFinite_sUnits S hS
  have hi := Subgroup.index_comap (squareS S) (SUnitIdeleIndex.principalSUnits S)
  rw [principal_preimage S htwo hprincipal, SUnitIdeleIndex.principalSUnits_range] at hi
  rw [← hi, ← LocalSquareIndex.doubles_index_eq_square,
    FinitelyGeneratedSquareIndex.doubles_index,
    FieldSquareIndex.twoTorsion_card A.subtype A.subtype_injective
      (⟨-1, fun p _ ↦ by simp⟩ : A) rfl]
  exact (pow_succ 2 _).symm

/-- O'Meara 65:12, with the initial square-idele index proved arithmetically. -/
theorem index (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) :
    (idelePrincipalEmbedding.range ⊔ squareS S).index =
      2 ^ (Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1) := by
  have h := NormIndexReduction.local_global_balance idelePrincipalEmbedding.range
    (finitePlaceSIdeleSubgroup S) (squareS S) hprincipal (fun _ hi ↦ hi.1)
  rw [principal_index S hS htwo hprincipal, relative_index S hS htwo] at h
  apply Nat.mul_left_cancel (by positivity :
    0 < (2 : ℕ) ^ (Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1))
  exact h.trans (by rw [← mul_pow]; norm_num)

end NormEuclidean.SquareIdeleIndex
