import NormEuclidean.ChapterX.NormFiberAssembly

/-!
# Actual square S-ideles and finite-support ideles

The subgroup J^{S,2} consists of S-ideles with square components outside
S, including all infinite places. Finite-support ideles implement the
single-prime subgroups in the ascending chain of O'Meara 65:21.
-/

noncomputable section

namespace NormEuclidean.SquareIdeles

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

local instance : DecidableEq (HeightOneSpectrum (𝓞 K)) := Classical.decEq _

/-- Units of an actual finite completed field. -/
abbrev FiniteUnits (p : HeightOneSpectrum (𝓞 K)) := (p.adicCompletion K)ˣ

/-- Equality of all actual components detects equality of full ideles. -/
theorem ext_components {i j : NumberFieldIdele K}
    (hf : ∀ p, ideleFiniteComponent p i = ideleFiniteComponent p j)
    (hi : ∀ v, ideleInfiniteComponent v i = ideleInfiniteComponent v j) : i = j := by
  apply Units.ext
  apply Prod.ext
  · funext v
    exact congrArg Units.val (hi v)
  · apply RestrictedProduct.ext
    intro p
    exact congrArg Units.val (hf p)

/-- Literal square S-ideles, with no condition on square classes at places in S. -/
def squareS (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (NumberFieldIdele K) where
  carrier := {i | i ∈ finitePlaceSIdeleSubgroup S ∧
    (∀ p ∉ S, IsSquare (ideleFiniteComponent p i)) ∧
    ∀ v, IsSquare (ideleInfiniteComponent v i)}
  one_mem' := ⟨Subgroup.one_mem _, fun _ _ ↦ ⟨1, by simp⟩, fun _ ↦ ⟨1, by simp⟩⟩
  mul_mem' := by
    intro i j hi hj
    exact ⟨Subgroup.mul_mem _ hi.1 hj.1,
      fun p hp ↦ by rw [map_mul]; exact (hi.2.1 p hp).mul (hj.2.1 p hp),
      fun v ↦ by rw [map_mul]; exact (hi.2.2 v).mul (hj.2.2 v)⟩
  inv_mem' := by
    intro i hi
    exact ⟨Subgroup.inv_mem _ hi.1,
      fun p hp ↦ by rw [map_inv]; exact (hi.2.1 p hp).inv,
      fun v ↦ by rw [map_inv]; exact (hi.2.2 v).inv⟩

/-- Ideles supported only on a specified set of finite primes. -/
def supported (T : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (NumberFieldIdele K) where
  carrier := {i | (∀ p ∉ T, ideleFiniteComponent p i = 1) ∧
    ∀ v, ideleInfiniteComponent v i = 1}
  one_mem' := ⟨fun _ _ ↦ map_one _, fun _ ↦ map_one _⟩
  mul_mem' := by
    intro i j hi hj
    exact ⟨fun p hp ↦ by rw [map_mul, hi.1 p hp, hj.1 p hp, one_mul],
      fun v ↦ by rw [map_mul, hi.2 v, hj.2 v, one_mul]⟩
  inv_mem' := by
    intro i hi
    exact ⟨fun p hp ↦ by rw [map_inv, hi.1 p hp, inv_one],
      fun v ↦ by rw [map_inv, hi.2 v, inv_one]⟩

/-- Enlarging finite support enlarges its actual idele subgroup. -/
theorem supported_mono {T U : Set (HeightOneSpectrum (𝓞 K))} (h : T ⊆ U) :
    supported T ≤ supported U := fun _ hi ↦
  ⟨fun p hp ↦ hi.1 p (fun ht ↦ hp (h ht)), hi.2⟩

/-- No support means the trivial idele subgroup. -/
theorem supported_empty : supported (K := K) ∅ = ⊥ := by
  ext i
  constructor
  · intro hi
    apply ext_components
    · intro p
      exact (hi.1 p (by simp)).trans (map_one _).symm
    · intro v
      exact (hi.2 v).trans (map_one _).symm
  · intro hi
    simpa only [Subgroup.mem_bot.mp hi] using (supported (K := K) ∅).one_mem

/-- A local unit can be placed at one finite prime with every other component one. -/
def single (p : HeightOneSpectrum (𝓞 K)) (a : (p.adicCompletion K)ˣ) : NumberFieldIdele K :=
  NormFiberAssembly.ofComponents (Pi.mulSingle p a) (by
    have he : ∀ᶠ q in Filter.cofinite, q ≠ p := by simp
    filter_upwards [he] with q hq
    simp [Pi.mulSingle_eq_of_ne hq]) (fun _ ↦ 1)

/-- The finite components of an actual single-prime idele. -/
theorem finite_single (p : HeightOneSpectrum (𝓞 K)) (a : (p.adicCompletion K)ˣ)
    (q : HeightOneSpectrum (𝓞 K)) :
    ideleFiniteComponent q (single p a) = Pi.mulSingle (M := FiniteUnits) p a q :=
  NormFiberAssembly.finiteComponent_ofComponents _ _ _ _

/-- Single-prime ideles have trivial infinite components. -/
theorem infinite_single (p : HeightOneSpectrum (𝓞 K)) (a : (p.adicCompletion K)ˣ)
    (v : NumberField.InfinitePlace K) : ideleInfiniteComponent v (single p a) = 1 :=
  NormFiberAssembly.infiniteComponent_ofComponents _ _ _ _

/-- A single-prime idele belongs to every support subgroup containing that prime. -/
theorem single_mem_supported (p : HeightOneSpectrum (𝓞 K)) (a : (p.adicCompletion K)ˣ)
    (T : Set (HeightOneSpectrum (𝓞 K))) (hp : p ∈ T) : single p a ∈ supported T := by
  constructor
  · intro q hq
    rw [finite_single]
    exact Pi.mulSingle_eq_of_ne (M := FiniteUnits) (i := p) (i' := q)
      (fun h ↦ hq (h.symm ▸ hp)) a
  · exact infinite_single p a

end NormEuclidean.SquareIdeles
