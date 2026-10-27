import Bong.QuadraticSpace.ScalarExtension
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Exact all-place space-representation predicates

These are the original representation predicates used by the extracted
induction, with unrelated lattice results omitted. They are propositions,
not axioms or instances; their inhabitants will be proved arithmetically.
-/

namespace Bong.HeADCV5.Global

open scoped NumberField

/-- Characteristic zero of the actual finite completion follows from its field embedding. -/
scoped instance finiteCharZeroForHasse {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : CharZero (p.adicCompletion K) :=
  Algebra.charZero_of_charZero K (p.adicCompletion K)

end Bong.HeADCV5.Global

namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped NumberField TensorProduct

universe u v w
variable {K : Type u} [Field K] [NumberField K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Representation over the actual infinite completion. -/
def InfinitePlaceRepresents (p : NumberField.InfinitePlace K)
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) : Prop :=
  (q.scalarExtension (E := p.Completion)).Represents (r.scalarExtension (E := p.Completion))

/-- The exact rank-specific local-to-global representation statement. -/
def HasAllPlaceHasseRepresentationAtRank (q : QuadraticSpace K V) (n : ℕ) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (r : QuadraticSpace K W), Module.finrank K W = n →
    (∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (q.scalarExtension (E := p.adicCompletion K)).Represents
        (r.scalarExtension (E := p.adicCompletion K))) →
    (∀ p : NumberField.InfinitePlace K, InfinitePlaceRepresents p q r) → q.Represents r

end Bong.HeADCV5.Global.NumberFieldLattice
