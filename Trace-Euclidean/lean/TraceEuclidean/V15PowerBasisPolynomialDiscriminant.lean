import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Power-basis and polynomial discriminants

Mathlib defines the discriminant of a family through the trace pairing and
the discriminant of a polynomial through a Sylvester determinant.  This
module proves that the two definitions agree for a separable power basis.
It also proves the integral-to-rational map identity needed to apply the
result to minimal polynomials of algebraic integers.
-/

namespace TraceEuclidean

noncomputable section

open Algebra Module Polynomial
open scoped Matrix

/-- The trace-pairing discriminant of a separable power basis equals the
discriminant of the minimal polynomial of its generator. -/
theorem v15_powerBasis_discr_eq_minpoly_discr
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) :
    Algebra.discr K pb.basis = (minpoly K pb.gen).discr := by
  classical
  let f : K[X] := minpoly K pb.gen
  let fE : (AlgebraicClosure K)[X] := f.map (algebraMap K (AlgebraicClosure K))
  have hfmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  have hfEmonic : fE.Monic := hfmonic.map _
  have hfsplit : fE.Splits := IsAlgClosed.splits fE
  have hfsep : f.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hfEnodup : fE.roots.Nodup :=
    Polynomial.nodup_roots (hfsep.map)
  have hprod :
      algebraMap K (AlgebraicClosure K)
          (Algebra.norm K (aeval pb.gen f.derivative)) =
        (fE.roots.map fun x => fE.derivative.eval x).prod := by
    rw [Algebra.norm_eq_prod_embeddings K (AlgebraicClosure K)]
    let e := pb.liftEquiv' (B := (AlgebraicClosure K))
    letI : Fintype {y : (AlgebraicClosure K) // y ∈ f.aroots (AlgebraicClosure K)} :=
      Fintype.ofEquiv (L →ₐ[K] (AlgebraicClosure K)) e
    calc
      (∏ σ : L →ₐ[K] (AlgebraicClosure K), σ (aeval pb.gen f.derivative)) =
          ∏ σ : L →ₐ[K] (AlgebraicClosure K),
            fE.derivative.eval (σ pb.gen) := by
        apply Finset.prod_congr rfl
        intro σ _
        rw [← aeval_algHom_apply, ← eval_map_algebraMap,
          ← Polynomial.derivative_map]
      _ = ∏ y : {y : (AlgebraicClosure K) // y ∈ f.aroots (AlgebraicClosure K)},
            fE.derivative.eval y.1 := by
        exact Fintype.prod_equiv e
          (fun σ : L →ₐ[K] (AlgebraicClosure K) => fE.derivative.eval (σ pb.gen))
          (fun y : {y : (AlgebraicClosure K) // y ∈ f.aroots (AlgebraicClosure K)} =>
            fE.derivative.eval y.1)
          (fun _ => rfl)
      _ = ∏ y ∈ fE.roots.toFinset, fE.derivative.eval y := by
        apply (Finset.prod_subtype fE.roots.toFinset ?_
          (fun y => fE.derivative.eval y)).symm
        intro y
        simp [fE, f, Polynomial.aroots_def]
      _ = (fE.roots.map fun x => fE.derivative.eval x).prod := by
        rw [← Multiset.toFinset_eq hfEnodup]
        rfl
  have hfdegpos : 0 < f.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    simpa [f] using pb.dim_pos
  have hres := Polynomial.resultant_deriv hfdegpos
  have hresmap := congrArg (algebraMap K (AlgebraicClosure K)) hres
  have hresmap' :
      fE.resultant fE.derivative fE.natDegree
          (fE.natDegree - 1) =
        algebraMap K (AlgebraicClosure K)
          (((-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
            f.discr) := by
    have hderiv :
        fE.derivative = f.derivative.map (algebraMap K (AlgebraicClosure K)) := by
      change (f.map (algebraMap K (AlgebraicClosure K))).derivative = _
      rw [Polynomial.derivative_map]
    have hnat : fE.natDegree = f.natDegree := by
      change (f.map (algebraMap K (AlgebraicClosure K))).natDegree = _
      exact hfmonic.natDegree_map (algebraMap K (AlgebraicClosure K))
    rw [hderiv, hnat]
    change (f.map (algebraMap K (AlgebraicClosure K))).resultant
        (f.derivative.map (algebraMap K (AlgebraicClosure K))) f.natDegree
          (f.natDegree - 1) = _
    rw [Polynomial.resultant_map_map, hresmap]
    simp [hfmonic.leadingCoeff]
  have hprodres := Polynomial.resultant_eq_prod_eval
    fE fE.derivative (fE.natDegree - 1)
      (Polynomial.natDegree_derivative_le fE) hfsplit
  have hnorm :
      algebraMap K (AlgebraicClosure K)
          (Algebra.norm K (aeval pb.gen f.derivative)) =
        algebraMap K (AlgebraicClosure K)
          (((-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
            f.discr) := by
    rw [hprod]
    rw [hfEmonic.leadingCoeff, one_pow, one_mul] at hprodres
    rw [← hprodres]
    exact hresmap'
  rw [Algebra.discr_powerBasis_eq_norm K pb]
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_mul]
  rw [hnorm]
  simp only [map_pow, map_neg, map_one]
  have hs :
      ((-1 : (AlgebraicClosure K)) ^ (Module.finrank K L *
        (Module.finrank K L - 1) / 2)) =
      ((-1 : (AlgebraicClosure K)) ^ (f.natDegree * (f.natDegree - 1) / 2)) := by
    rw [show Module.finrank K L = f.natDegree by
      simpa [f] using pb.finrank]
  rw [hs]
  simp only [f, map_mul, map_pow, map_neg, map_one]
  rw [← mul_assoc, ← pow_two]
  have hsign :
      (((-1 : (AlgebraicClosure K)) ^ ((minpoly K pb.gen).natDegree *
        ((minpoly K pb.gen).natDegree - 1) / 2)) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  rw [hsign, one_mul]

/-- Mapping a nonconstant monic integral polynomial to the rationals
preserves its polynomial discriminant. -/
theorem v15_intCast_discr_eq_discr_map
    (f : ℤ[X]) (hmonic : f.Monic) (hpos : 0 < f.natDegree) :
    ((f.discr : ℤ) : ℚ) =
      (f.map (algebraMap ℤ ℚ)).discr := by
  let fQ : ℚ[X] := f.map (algebraMap ℤ ℚ)
  have hdeg : 0 < f.degree := by
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hpos
  have hmonicQ : fQ.Monic := hmonic.map _
  have hnat : fQ.natDegree = f.natDegree := by
    change (f.map (algebraMap ℤ ℚ)).natDegree = f.natDegree
    exact hmonic.natDegree_map (algebraMap ℤ ℚ)
  have hdegQ : 0 < fQ.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hnat]
    exact hpos
  have hres := Polynomial.resultant_deriv hdeg
  have hresQ := Polynomial.resultant_deriv hdegQ
  have hresMap := congrArg (algebraMap ℤ ℚ) hres
  have hderiv :
      fQ.derivative = f.derivative.map (algebraMap ℤ ℚ) := by
    change (f.map (algebraMap ℤ ℚ)).derivative = _
    rw [Polynomial.derivative_map]
  have hmapped :
      fQ.resultant fQ.derivative fQ.natDegree
          (fQ.natDegree - 1) =
        ((-1 : ℚ) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
          ((f.discr : ℤ) : ℚ) := by
    rw [hderiv, hnat]
    change (f.map (algebraMap ℤ ℚ)).resultant
        (f.derivative.map (algebraMap ℤ ℚ)) f.natDegree
          (f.natDegree - 1) = _
    rw [Polynomial.resultant_map_map, hresMap]
    simp [hmonic.leadingCoeff]
  have heq :
      ((-1 : ℚ) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
          ((f.discr : ℤ) : ℚ) =
        ((-1 : ℚ) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
          fQ.discr := by
    rw [← hmapped]
    simpa [hnat, hmonicQ.leadingCoeff] using hresQ
  exact mul_left_cancel₀
    (pow_ne_zero _ (by norm_num : (-1 : ℚ) ≠ 0)) heq

end

end TraceEuclidean
