import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
Elementary finiteness lemmas for the finite-index extension step.  They are
independent of quadratic forms: submodules above a fixed submodule are finite
as soon as the corresponding quotient module has finite carrier.
-/

namespace TraceEuclidean

noncomputable section

/-- A module with finite carrier has only finitely many submodules. -/
theorem finite_all_submodules_of_finite_carrier
    (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Finite M] :
    (Set.univ : Set (Submodule R M)).Finite := by
  letI : Finite (Set M) := inferInstance
  letI : Finite (Submodule R M) :=
    Finite.of_injective (fun P : Submodule R M ↦ (P : Set M))
      (fun _ _ h ↦ SetLike.coe_injective h)
  exact Set.toFinite _

/-- If `M/N` is finite, only finitely many submodules of `M` contain `N`. -/
theorem finite_submodules_above_of_finite_quotient
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Finite (M ⧸ N)] :
    {P : Submodule R M | N ≤ P}.Finite := by
  let f : Submodule R M → Submodule R (M ⧸ N) :=
    fun P ↦ P.map N.mkQ
  apply Set.Finite.of_injOn (f := f)
    (t := Set.univ)
  · intro P _hP
    exact Set.mem_univ (f P)
  · intro P hP Q hQ heq
    change N ≤ P at hP
    change N ≤ Q at hQ
    have hcomap := congrArg (Submodule.comap N.mkQ) heq
    simpa only [f, Submodule.comap_map_mkQ,
      sup_eq_right.mpr hP, sup_eq_right.mpr hQ] using hcomap
  · exact finite_all_submodules_of_finite_carrier R (M ⧸ N)

end

end TraceEuclidean
