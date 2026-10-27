import NormEuclidean.CompletedUnipotent

/-!
# Integral parameters preserve the actual completed hyperbolic carrier
-/

noncomputable section

namespace NormEuclidean.IntegralUnipotent

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  TernaryKernelGeneration CompletedUnipotent

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E]

theorem family_spinorNorm (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
    (hA : Q.Anisotropic) (b : Bool) (u : E) :
    properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) (family Q hQ hA b u) = 1 := by
  cases b
  · exact HyperbolicUnipotent.element_spinorNorm Q hQ hA u
  · exact OppositeHyperbolicUnipotent.element_spinorNorm Q hQ hA u

theorem family_integral (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
    (hA : Q.Anisotropic) (R : Subring F) (L : Submodule R E)
    (hInt : ∀ x ∈ L, Q x ∈ R) (u : E) (hu : u ∈ L) (b : Bool) (z : Hyperbolic F E) :
    (family Q hQ hA b u).1.1 z ∈ Hyperbolic.submodule L ↔ z ∈ Hyperbolic.submodule L := by
  cases b
  · exact HyperbolicUnipotent.element_integral Q hQ hA R L hInt u hu z
  · exact OppositeHyperbolicUnipotent.element_integral Q hQ hA R L hInt u hu z

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local instance finiteCharZero (p : HeightOneSpectrum (integerSubring K)) :
    CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _

set_option backward.isDefEq.respectTransparency false in
/-- Integral local scalars preserve both directions of the actual completed carrier,
including dyadic primes and a nonfree original line lattice. -/
theorem localFamily_integral (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 1) (L : Lattice (integerSubring K) Q)
    (u : V) (hu : u ∈ L.carrier) (p : HeightOneSpectrum (integerSubring K)) (b : Bool)
    (t : LocalField (integerSubring K) p) (ht : t ∈ LocalRing (integerSubring K) p) :
    localFamily Q hQ hdim p u b t ∈ properStabilizerWithin
      (form (integerSubring K) p (Hyperbolic.form Q)) (carrier _ p L.hyperbolic.carrier) := by
  intro z
  let P := form (integerSubring K) p Q
  let hP := form_polarBilin_nondegenerate (integerSubring K) p Q hQ
  let hA := UnaryClassNumber.anisotropic P hP (local_finrank hdim p)
  let e := hyperbolicEquiv (V := V) (integerSubring K) p
  have hparam : t • inclusion (integerSubring K) p u ∈ carrier _ p L.carrier :=
    (carrier _ p L.carrier).smul_mem (⟨t, ht⟩ : LocalRing (integerSubring K) p)
      (inclusion_mem _ p L.carrier hu)
  change (localFamily Q hQ hdim p u b t).1.1 z ∈
    carrier (integerSubring K) p (Hyperbolic.submodule L.carrier) ↔
      z ∈ carrier (integerSubring K) p (Hyperbolic.submodule L.carrier)
  rw [← hyperbolicEquiv_carrier (integerSubring K) p L.carrier,
    ← hyperbolicEquiv_carrier (integerSubring K) p L.carrier]
  change e (e.symm ((family P hP hA b (t • inclusion _ p u)).1.1 (e z))) ∈
    Hyperbolic.submodule (carrier _ p L.carrier) ↔ _
  rw [e.apply_symm_apply]
  exact family_integral P hP hA (LocalRing _ p) (carrier _ p L.carrier)
    (carrier_integral _ p Q L.carrier L.integral) _ hparam b (e z)

end NormEuclidean.IntegralUnipotent
