import NormEuclidean.ChapterX.LocalLatticePatching
import NormEuclidean.ChapterX.OrthogonalWeakApproximationAt
import NormEuclidean.ChapterX.FixedValueTransitivity

/-!
# Local-to-genus lattice patching in O'Meara 102:5

One-place orthogonal weak approximation realizes each local lattice image
by a global transport. The proved finite module patching theorem then gives
one actual lattice in the ordinary genus, with the prescribed local images
and the original completed carrier at every other finite prime.
-/

noncomputable section

namespace NormEuclidean.GenusPatching

open ProperSpinor CompletedIntegralLattice IsDedekindDomain OrthogonalTopology
open OrthogonalWeakApproximationAt AdelicApproximation Filter Topology
open SpinorBaseChange FixedValueTransitivity QuadraticMap
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- A global transport realizes the exact image of the base completed
lattice under one prescribed local orthogonal transformation. -/
theorem exists_global_transport_local_image (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Lattice (integerSubring K) Q)
    (v : HeightOneSpectrum (integerSubring K))
    (a : ambientGroup (form (integerSubring K) v Q)) :
    ∃ g : ambientGroup Q, ∀ x,
      a.1 x ∈ carrier (integerSubring K) v (transportLattice Q g L).carrier ↔
        x ∈ carrier (integerSubring K) v L.carrier := by
  let U := {b : ambientGroup (form (integerSubring K) v Q) |
    a⁻¹ * b ∈ integralStabilizer (form (integerSubring K) v Q)
      (carrier (integerSubring K) v L.carrier)}
  have hopen : IsOpen U :=
    (isOpen_integralStabilizer _ _ (carrier_fg (integerSubring K) v L.carrier L.finite)
      (isOpen_completedCarrier (integerSubring K) v Q L)).preimage
        (continuous_const.mul continuous_id)
  have hU : U ∈ 𝓝 a := hopen.mem_nhds (by simp [U])
  obtain ⟨g, hg⟩ := exists_global_orthogonal_weak_at Q hQ hpos v a U hU
  refine ⟨g, ?_⟩
  intro x
  let b := localizeAmbient Q g v
  let y := b.1.symm (a.1 x)
  have ht := equiv_carrier (integerSubring K) v L.carrier
    (transportLattice Q g L).carrier g.1 (mem_transportLattice Q g L) y
  change b.1 y ∈ _ ↔ y ∈ _ at ht
  have ht' : a.1 x ∈ carrier (integerSubring K) v (transportLattice Q g L).carrier ↔
      y ∈ carrier (integerSubring K) v L.carrier := by
    simpa only [y, LinearEquiv.apply_symm_apply] using ht
  have hs := hg y
  have hxy : (a⁻¹ * b).1 y = x := by
    simp only [y, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  change (a⁻¹ * b).1 y ∈ _ ↔ y ∈ _ at hs
  rw [hxy] at hs
  exact ht'.trans hs.symm

/-- Any finite family of actual local orthogonal images can be patched to
one global lattice in the ordinary genus. All other completed carriers agree exactly. -/
theorem exists_genus_lattice_of_local_images (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Lattice (integerSubring K) Q)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : HeightOneSpectrum (integerSubring K)) →
      ambientGroup (form (integerSubring K) v Q)) :
    ∃ P : Lattice (integerSubring K) Q, SameGenus Q L P ∧
      (∀ v ∈ T, ∀ x, (a v).1 x ∈ carrier (integerSubring K) v P.carrier ↔
        x ∈ carrier (integerSubring K) v L.carrier) ∧
      ∀ v ∉ T, carrier (integerSubring K) v P.carrier =
        carrier (integerSubring K) v L.carrier := by
  choose g hg using fun v ↦ exists_global_transport_local_image Q hQ hpos L v (a v)
  obtain ⟨P, hin, hout⟩ := LocalLatticePatching.exists_patched_lattice
    (integerSubring K) Q L T (fun v ↦ transportLattice Q (g v) L)
  have hmap : ∀ v ∈ T, ∀ x, (a v).1 x ∈ carrier (integerSubring K) v P.carrier ↔
      x ∈ carrier (integerSubring K) v L.carrier := by
    intro v hv x
    rw [hin v hv]
    exact hg v x
  refine ⟨P, (sameGenus_iff_finite Q L P).mpr ?_, hmap, hout⟩
  intro v
  by_cases hv : v ∈ T
  · exact ⟨{ toLinearEquiv := (a v).1
             q_eq := (a v).2
             mem_iff := hmap v hv }⟩
  · exact ⟨{ toLinearEquiv := LinearEquiv.refl _ _
             q_eq := fun _ ↦ rfl
             mem_iff := fun x ↦ by simp only [LinearEquiv.refl_apply, hout v hv] }⟩

/-- The sublattice-inclusion conclusion of 102:5, when its actual local
ambient transporters are given. No global patching witness is assumed. -/
theorem exists_genus_lattice_containing (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Lattice (integerSubring K) Q)
    (A : Submodule (integerSubring K) V)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : HeightOneSpectrum (integerSubring K)) →
      ambientGroup (form (integerSubring K) v Q))
    (hin : ∀ v ∈ T, ∀ x ∈ carrier (integerSubring K) v A,
      (a v).1.symm x ∈ carrier (integerSubring K) v L.carrier)
    (hout : ∀ v ∉ T, carrier (integerSubring K) v A ≤
      carrier (integerSubring K) v L.carrier) :
    ∃ P : Lattice (integerSubring K) Q, SameGenus Q L P ∧ A ≤ P.carrier := by
  obtain ⟨P, hgen, hmap, houtside⟩ := exists_genus_lattice_of_local_images Q hQ hpos L T a
  refine ⟨P, hgen, ?_⟩
  intro x hx
  apply FixedValueVectors.mem_of_all_completed (integerSubring K)
    (NumberField.RingOfIntegers.not_isField K) P.carrier
  intro v
  by_cases hv : v ∈ T
  · have hp := (hmap v hv ((a v).1.symm (inclusion (integerSubring K) v x))).mpr
      (hin v hv _ (inclusion_mem (integerSubring K) v A hx))
    simpa only [LinearEquiv.apply_symm_apply] using hp
  · rw [houtside v hv]
    exact hout v hv (inclusion_mem (integerSubring K) v A hx)

/-- Equal nonzero quadratic values are carried to one another by an actual
ambient isometry. This includes dimension one and does not require regularity. -/
theorem exists_ambient_map_of_value_eq {F E : Type*} [Field F] [CharZero F]
    [AddCommGroup E] [Module F E] (P : QuadraticForm F E) (x y : E)
    (hx : P x ≠ 0) (hxy : P x = P y) :
    ∃ g : ambientGroup P, g.1 x = y := by
  by_cases hd : P (x - y) ≠ 0
  · exact ⟨ambientReflection P (x - y) hd, reflection_sub_apply P x y hxy hd⟩
  · have hd0 : P (x - y) = 0 := not_ne_iff.mp hd
    have hsum : P (x + y) = 4 * P x := by
      have hsub : P (x - y) = P x + P y - polar P x y := by
        rw [sub_eq_add_neg, QuadraticMap.map_add (P : E → F), P.map_neg, P.polar_neg_right]
        ring
      rw [QuadraticMap.map_add (P : E → F)]
      rw [hxy] at hsub ⊢
      rw [hd0] at hsub
      linear_combination hsub
    have hs : P (x + y) ≠ 0 := by rw [hsum]; exact mul_ne_zero (by norm_num) hx
    have hy : P y ≠ 0 := hxy.symm.trans_ne hx
    refine ⟨ambientReflection P y hy * ambientReflection P (x + y) hs, ?_⟩
    have hr : IntegralReflection.linearEquiv P (x + y) hs x = -y := by
      have heq : P x = P (-y) := by simpa only [P.map_neg] using hxy
      have hdneg : P (x - -y) ≠ 0 := by simpa only [sub_neg_eq_add] using hs
      simpa only [sub_neg_eq_add] using reflection_sub_apply P x (-y) heq hdneg
    change IntegralReflection.linearEquiv P y hy
      (IntegralReflection.linearEquiv P (x + y) hs x) = y
    rw [hr, map_neg, IntegralReflection.linearEquiv_self, neg_neg]

/-- The scalar special case of O'Meara 102:5: a globally represented scalar
which is integrally represented at every finite place is represented by an
actual lattice in the ordinary genus. The zero scalar and dimension one are included. -/
theorem exists_genus_lattice_representing (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (a : K) (hglobal : ∃ x : V, Q x = a)
    (hlocal : ∀ v : HeightOneSpectrum (integerSubring K),
      ∃ z ∈ carrier (integerSubring K) v L.carrier,
        form (integerSubring K) v Q z = algebraMap K (LocalField (integerSubring K) v) a) :
    ∃ P : Lattice (integerSubring K) Q, SameGenus Q L P ∧ ∃ x ∈ P.carrier, Q x = a := by
  classical
  by_cases ha : a = 0
  · exact ⟨L, (sameGenus_iff_finite Q L L).mpr (finiteLocallyIsometric_refl _ Q L.carrier),
      0, L.carrier.zero_mem, by simp [ha]⟩
  obtain ⟨x, hx⟩ := hglobal
  have hx0 : Q x ≠ 0 := hx.trans_ne ha
  have hpos : 0 < Module.finrank K V :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, fun h ↦ hx0 (h ▸ Q.map_zero)⟩
  obtain ⟨d, hd0, hdx⟩ := ScalarExtension.exists_denominator L.carrier L.full x
  let T := (finite_primes_containing (K := K) (integerSubring K) d hd0).toFinset
  choose z hz hQz using hlocal
  have htrans (v : HeightOneSpectrum (integerSubring K)) :
      ∃ g : ambientGroup (form (integerSubring K) v Q),
        g.1 (z v) = inclusion (integerSubring K) v x := by
    apply exists_ambient_map_of_value_eq (form (integerSubring K) v Q)
    · rw [hQz v]
      intro hzero
      exact ha ((algebraMap K (LocalField (integerSubring K) v)).injective
        (hzero.trans (map_zero _).symm))
    · rw [hQz v, form_inclusion, hx]
  choose g hg using htrans
  obtain ⟨P, hgen, hmap, hout⟩ := exists_genus_lattice_of_local_images Q hQ hpos L T g
  refine ⟨P, hgen, x, ?_, hx⟩
  apply FixedValueVectors.mem_of_all_completed (integerSubring K)
    (NumberField.RingOfIntegers.not_isField K) P.carrier
  intro v
  by_cases hv : v ∈ T
  · rw [← hg v]
    exact (hmap v hv (z v)).mpr (hz v)
  · rw [hout v hv]
    have hdv : d ∉ v.asIdeal := by
      intro hdv
      exact hv ((finite_primes_containing (K := K) (integerSubring K) d hd0).mem_toFinset.mpr hdv)
    let A := Submodule.span (integerSubring K) ({x} : Set V)
    have hscale : ∀ y ∈ A, (d : K) • y ∈ L.carrier := by
      intro y hy
      obtain ⟨b, hby⟩ := Submodule.mem_span_singleton.mp hy
      rw [← hby, smul_comm]
      exact L.carrier.smul_mem b hdx
    exact carrier_le_of_scaled_le_of_not_mem (integerSubring K) v A L.carrier d hscale hdv
      (inclusion_mem (integerSubring K) v A (Submodule.subset_span (Set.mem_singleton x)))

/-- Ordinary genus representation is equivalent to global ambient
representation together with integral representation at every finite place. -/
theorem genus_represents_iff_global_and_all_finite (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (a : K) :
    (∃ P : Lattice (integerSubring K) Q, SameGenus Q L P ∧ ∃ x ∈ P.carrier, Q x = a) ↔
      (∃ x : V, Q x = a) ∧
      ∀ v : HeightOneSpectrum (integerSubring K),
        ∃ z ∈ carrier (integerSubring K) v L.carrier,
          form (integerSubring K) v Q z = algebraMap K (LocalField (integerSubring K) v) a := by
  constructor
  · rintro ⟨P, hgen, x, hx, hQx⟩
    refine ⟨⟨x, hQx⟩, ?_⟩
    intro v
    obtain ⟨e⟩ := hgen.1 v
    let z := e.toLinearEquiv.symm (inclusion (integerSubring K) v x)
    have hz : z ∈ carrier (integerSubring K) v L.carrier := by
      apply (e.mem_iff z).mp
      change e.toLinearEquiv (e.toLinearEquiv.symm (inclusion (integerSubring K) v x)) ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact inclusion_mem (integerSubring K) v P.carrier hx
    refine ⟨z, hz, ?_⟩
    have heq := e.q_eq z
    simpa only [z, LinearEquiv.apply_symm_apply, form_inclusion, hQx] using heq.symm
  · rintro ⟨hglobal, hlocal⟩
    exact exists_genus_lattice_representing Q hQ L a hglobal hlocal

end NormEuclidean.GenusPatching
