import NormEuclidean.ChapterX.GlobalSquare

/-!
# Mixed approximation adapter for the Hasse induction

The finite and infinite completions and their topologies are the project's
actual ones. The adapter supplies the coordinate approximation used in
the extracted higher-rank proof, from the already proved weak approximation.
-/

noncomputable section

namespace Bong.HeADCV5.Global

open IsDedekindDomain
open scoped NumberField Topology

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The nontrivial finite norm is proved for the actual completed field. -/
scoped instance finiteNontrivialForHasse (p : HeightOneSpectrum (𝓞 K)) :
    NontriviallyNormedField (p.adicCompletion K) := NormEuclidean.GlobalSquare.finiteNontrivial p

/-- Actual mixed completions, indexed by separate finite and infinite families. -/
abbrev mixedCompletion {ι κ : Type u} (p : ι → HeightOneSpectrum (𝓞 K))
    (q : κ → NumberField.InfinitePlace K) (s : ι ⊕ κ) :=
  NormEuclidean.MixedScalarWeakApproximation.FieldAt (Sum.map p q s)

/-- The genuine diagonal embedding in those actual completions. -/
def mixedAlgebraMap {ι κ : Type u} (p : ι → HeightOneSpectrum (𝓞 K))
    (q : κ → NumberField.InfinitePlace K) (a : K) : (s : ι ⊕ κ) → mixedCompletion p q s
  | .inl i => algebraMap K ((p i).adicCompletion K) a
  | .inr j => algebraMap K (q j).Completion a

/-- Simultaneous coordinate approximation in finite mixed families of open sets. -/
theorem exists_global_coordinate_in_mixed_local_opens
    {ι κ : Type u} [Finite ι] [Finite κ]
    (p : ι → HeightOneSpectrum (𝓞 K)) (q : κ → NumberField.InfinitePlace K)
    (hp : Function.Injective p) (hq : Function.Injective q) (n : ℕ)
    (U : (s : ι ⊕ κ) → Set (Fin n → mixedCompletion p q s))
    (hOpen : ∀ s, IsOpen (U s)) (y : (s : ι ⊕ κ) → Fin n → mixedCompletion p q s)
    (hy : ∀ s, y s ∈ U s) :
    ∃ x : Fin n → K, ∀ s, (fun j ↦ mixedAlgebraMap p q (x j) s) ∈ U s := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  let P := Sum.map p q
  have hP : Function.Injective P := Sum.map_injective.mpr ⟨hp, hq⟩
  have heq : (fun a : K ↦ fun s : ι ⊕ κ ↦
      algebraMap K (NormEuclidean.MixedScalarWeakApproximation.FieldAt (P s)) a) =
        mixedAlgebraMap p q := by
    funext a s
    cases s <;> rfl
  have hd : DenseRange (mixedAlgebraMap p q) := by
    rw [← heq]
    exact NormEuclidean.MixedScalarWeakApproximation.denseRange_diagonal_of_injective P hP
  let swap : (Fin n → (s : ι ⊕ κ) → mixedCompletion p q s) →
      (s : ι ⊕ κ) → Fin n → mixedCompletion p q s := fun f s j ↦ f j s
  have hs : Function.Surjective swap := fun f ↦ ⟨fun j s ↦ f s j, rfl⟩
  have hcont : Continuous swap := continuous_pi fun s ↦ continuous_pi fun j ↦
    (continuous_apply s).comp (continuous_apply j)
  have hc := hs.denseRange.comp (DenseRange.piMap (fun _ : Fin n ↦ hd)) hcont
  let B := Set.pi Set.univ U
  have hB : IsOpen B := isOpen_set_pi Set.finite_univ (fun s _ ↦ hOpen s)
  have hyB : y ∈ B := fun s _ ↦ hy s
  obtain ⟨x, hx⟩ := hc.exists_mem_open hB ⟨y, hyB⟩
  exact ⟨x, fun s ↦ hx s (Set.mem_univ s)⟩

end Bong.HeADCV5.Global

namespace Bong.QuadraticSpace

/-- The square-class openness theorem used by the extracted induction. -/
theorem hasOpenNonzeroSquareClasses_of_complete {F : Type*}
    [NontriviallyNormedField F] [CompleteSpace F] [CharZero F] (a : Fˣ) :
    IsOpen {z : F | ∃ c : Fˣ, z = a.val * c.val ^ 2} :=
  NormEuclidean.SquareClassTopology.isOpen_squareClass a

end Bong.QuadraticSpace
