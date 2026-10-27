import NormEuclidean.ClassNumberTransfer

/-!
# Cancellation only for hyperbolic extensions of the original genus

The input compares L plus a hyperbolic plane with M plus that plane for
M in the ordinary genus of L. It imposes no condition on other members of
the enlarged genus and does not assert that this enlarged genus is one class.
-/

namespace NormEuclidean

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

omit [Invertible (2 : K)] in
/-- Global hyperbolic equivalence cancels for the given norm-Euclidean lattice. -/
theorem globallyIsometric_of_hyperbolic (L M : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (h : GloballyIsometric (Hyperbolic.form Q) L.hyperbolic M.hyperbolic) :
    GloballyIsometric Q L M := by
  obtain ⟨e⟩ := h
  let φ : Hyperbolic.Isometry Q Q M.carrier L.carrier := {
    toLinearEquiv := e.inverse.toLinearEquiv
    q_eq := e.inverse.q_eq
    mem_iff := fun z ↦ by
      change e.inverse.toLinearEquiv z ∈ Hyperbolic.submodule L.carrier ↔
        z ∈ Hyperbolic.submodule M.carrier
      exact e.inverse.mem_iff z }
  obtain ⟨g⟩ := Hyperbolic.norm_euclidean_cancellation
    (numberFieldNorm K) L.integral hA hE φ
  exact ⟨g.inverse⟩

/-- Only hyperbolic extensions of members of the original genus need to be compared. -/
theorem hasLatticeClassNumberOne_of_genus_hyperbolic_isometry
    (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier)
    (h : ∀ M : Lattice (integerSubring K) Q, SameGenus Q L M →
      GloballyIsometric (Hyperbolic.form Q) L.hyperbolic M.hyperbolic) :
    HasLatticeClassNumberOne Q L := by
  rw [hasLatticeClassNumberOne_iff]
  intro M hgen
  exact globallyIsometric_of_hyperbolic L M hA hE (h M hgen)

/-- The restricted stable-genus condition is also necessary, so the new input is exact. -/
theorem hasLatticeClassNumberOne_iff_genus_hyperbolic_isometry
    (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) :
    HasLatticeClassNumberOne Q L ↔
      ∀ M : Lattice (integerSubring K) Q, SameGenus Q L M →
        GloballyIsometric (Hyperbolic.form Q) L.hyperbolic M.hyperbolic := by
  constructor
  · intro h M hgen
    obtain ⟨e⟩ := (hasLatticeClassNumberOne_iff Q L).mp h M hgen
    exact ⟨e.hyperbolic⟩
  · exact hasLatticeClassNumberOne_of_genus_hyperbolic_isometry L hA hE

end NormEuclidean
