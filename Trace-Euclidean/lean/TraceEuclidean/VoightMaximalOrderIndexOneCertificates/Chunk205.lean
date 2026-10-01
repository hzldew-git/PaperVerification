import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk201
import TraceEuclidean.VoightAllIrreducible
import TraceEuclidean.VoightIntegralBasisCertificate
import TraceEuclidean.VoightPolynomialBridge
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertifyAdjoinRootCore
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.MaximalAPI
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertificateDedekind
import Mathlib.Tactic

set_option linter.all false
set_option maxHeartbeats 5000000

namespace TraceEuclidean

namespace VoightMaximalOrderD10R392

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4850450910896, [1, -17, 38, 63, -61, -55, 37, 18, -10, -2, 1], 1⟩
local notation "l" => [1, -17, 38, 63, -61, -55, 37, 18, -10, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsTen := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsTen_irreducible row row_mem
lemma T_monic : Monic T := by
  rw [← T_ofList]
  exact monic_ofList l rfl

abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)
instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1
    T_irreducible
instance KField : Field K := AdjoinRoot.instField
instance : Algebra ℤ K := Ring.toIntAlgebra K
instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
  AdjoinRoot.isAdjoinRoot _
local notation "θ" => Adj.root

def basisDenominator : ℤ := 1
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 17, -38, -63, 61, 55, -37, -18, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], ![-2, 33, -59, -164, 59, 171, -19, -73, 2, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], ![-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], ![-14, 236, -499, -941, 690, 829, -347, -271, 67, 30]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], ![-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], ![-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], ![-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], ![-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], ![-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], ![-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], ![-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], ![-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], ![-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], ![-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], ![-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283], ![-283, 4684, -8625, -22159, 8358, 20923, -2597, -7453, 263, 949]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], ![-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], ![-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], ![-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], ![-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283], ![-283, 4684, -8625, -22159, 8358, 20923, -2597, -7453, 263, 949], ![-949, 15850, -31378, -68412, 35730, 60553, -14190, -19679, 2037, 2161]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], ![-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], ![-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], ![-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], ![-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283], ![-283, 4684, -8625, -22159, 8358, 20923, -2597, -7453, 263, 949], ![-949, 15850, -31378, -68412, 35730, 60553, -14190, -19679, 2037, 2161], ![-2161, 35788, -66268, -167521, 63409, 154585, -19404, -53088, 1931, 6359]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], ![-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], ![-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], ![-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], ![-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283], ![-283, 4684, -8625, -22159, 8358, 20923, -2597, -7453, 263, 949], ![-949, 15850, -31378, -68412, 35730, 60553, -14190, -19679, 2037, 2161], ![-2161, 35788, -66268, -167521, 63409, 154585, -19404, -53088, 1931, 6359], ![-6359, 105942, -205854, -466885, 220378, 413154, -80698, -133866, 10502, 14649]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1], [-283, -127, -30, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1], [-283, -127, -30, -14, -2, -1], [-949, -283, -127, -30, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1], [-283, -127, -30, -14, -2, -1], [-949, -283, -127, -30, -14, -2, -1], [-2161, -949, -283, -127, -30, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1], [-283, -127, -30, -14, -2, -1], [-949, -283, -127, -30, -14, -2, -1], [-2161, -949, -283, -127, -30, -14, -2, -1], [-6359, -2161, -949, -283, -127, -30, -14, -2, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 10 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 10) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 10) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 10) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 17, -38, -63, 61, 55, -37, -18, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], [-2, 33, -59, -164, 59, 171, -19, -73, 2, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], [-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], [-14, 236, -499, -941, 690, 829, -347, -271, 67, 30]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], [-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], [-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], [-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], [-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], [-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], [-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], [-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], [-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], [-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], [-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], [-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283], [-283, 4684, -8625, -22159, 8358, 20923, -2597, -7453, 263, 949]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], [-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], [-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], [-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], [-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283], [-283, 4684, -8625, -22159, 8358, 20923, -2597, -7453, 263, 949], [-949, 15850, -31378, -68412, 35730, 60553, -14190, -19679, 2037, 2161]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], [-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], [-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], [-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], [-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283], [-283, 4684, -8625, -22159, 8358, 20923, -2597, -7453, 263, 949], [-949, 15850, -31378, -68412, 35730, 60553, -14190, -19679, 2037, 2161], [-2161, 35788, -66268, -167521, 63409, 154585, -19404, -53088, 1931, 6359]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 17, -38, -63, 61, 55, -37, -18, 10, 2], [-2, 33, -59, -164, 59, 171, -19, -73, 2, 14], [-14, 236, -499, -941, 690, 829, -347, -271, 67, 30], [-30, 496, -904, -2389, 889, 2340, -281, -887, 29, 127], [-127, 2129, -4330, -8905, 5358, 7874, -2359, -2567, 383, 283], [-283, 4684, -8625, -22159, 8358, 20923, -2597, -7453, 263, 949], [-949, 15850, -31378, -68412, 35730, 60553, -14190, -19679, 2037, 2161], [-2161, 35788, -66268, -167521, 63409, 154585, -19404, -53088, 1931, 6359], [-6359, 105942, -205854, -466885, 220378, 413154, -80698, -133866, 10502, 14649]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp283 : Fact (Nat.Prime 283) := fact_iff.2 (by norm_num)
instance hp6971 : Fact (Nat.Prime 6971) := fact_iff.2 (by norm_num)
instance hp4957 : Fact (Nat.Prime 4957) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1, 0, 1]
  b' := [0, 1, 1, 1, 0, 1, 1]
  k := [1, 1, 1, 0, 1, 0, 1]
  f := [0, 9, -18, -31, 31, 28, -18, -8, 6, 2]
  g := [1, 0, 1, 0, 0, 1, 0, 1, 1]
  h := [1, 1, 1]
  a := [1, 0, 0, 0, 1, 1, 1]
  b := [1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [4, 16, 5, 1, 21, 1, 27, 6]
  b' := [13, 27, 26, 4, 1, 6, 19, 15, 20]
  k := [19, 19, 21, 5, 20, 26, 16, 12, 1]
  f := [17, 9, 20, 12, 18, 21, 5, 19, 5, 1]
  g := [22, 10, 27, 17, 20, 24, 7, 25, 5, 1]
  h := [24, 1]
  a := [13, 12, 26, 22, 28, 4, 25, 30, 11]
  b := [21, 28, 5, 10, 11, 23, 10, 1, 20]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD283 : CertificateDedekindCriterionLists l 283 where
  n := 2
  a' := [200, 57, 205, 260, 116, 55, 269, 97]
  b' := [78, 21, 135, 278, 189, 153, 16, 54, 115]
  k := [215, 192, 225, 109, 251, 244, 232, 212, 1]
  f := [125, 30, 107, 103, 86, 112, 26, 117, 66, 1]
  g := [201, 47, 172, 165, 137, 179, 41, 188, 105, 1]
  h := [176, 1]
  a := [67, 155, 152, 278, 255, 134, 216, 247, 251]
  b := [40, 87, 199, 35, 225, 122, 81, 203, 32]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD6971 : CertificateDedekindCriterionLists l 6971 where
  n := 2
  a' := [3971, 3041, 5640, 2009, 599, 841, 2490, 5940]
  b' := [648, 5241, 4075, 1699, 2071, 3628, 5197, 4668, 6311]
  k := [1810, 3927, 946, 2951, 4314, 1389, 640, 3923, 1]
  f := [674, 331, 369, 1310, 1419, 127, 37, 267, 1190, 1]
  g := [3085, 1513, 1688, 5995, 6491, 577, 169, 1222, 5446, 1]
  h := [1523, 1]
  a := [2732, 6843, 3882, 3297, 1389, 4608, 851, 1685, 3271]
  b := [3475, 1002, 5053, 871, 3045, 2336, 6670, 5575, 3700]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4957 : CertificateDedekindCriterionLists l 4957 where
  n := 2
  a' := [2973, 3742, 1229, 2433, 3111, 4551, 4459, 565]
  b' := [3006, 2330, 1332, 3021, 4605, 467, 3156, 2523, 488]
  k := [861, 2336, 211, 982, 2451, 4005, 4265, 2023, 1]
  f := [931, 45, 1280, 679, 96, 1388, 226, 219, 1032, 1]
  g := [3148, 150, 4328, 2293, 323, 4693, 761, 740, 3489, 1]
  h := [1466, 1]
  a := [2108, 3251, 3041, 1261, 246, 537, 2271, 2753, 227]
  b := [3425, 3492, 2206, 706, 4661, 2347, 3049, 4759, 4730]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![2, 31, 283, 6971, 4957]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [2, 31, 283, 6971, 4957]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp31.out
    exact hp283.out
    exact hp6971.out
    exact hp4957.out
  a := [-1165056493875, -838840272206, 6216793239083, 2550041844279, -8461302135988, -2294620248928, 3779890508912, 492338167880, -525734225150]
  b := [-104197815161, 649887421849, 347234593790, -1986300818900, -741295129303, 1589938971605, 397698749404, -492215564669, -59748501291, 52573422515]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 283 T_ofList CD283
    exact satisfiesDedekindCriterion_of_certificate_lists T l 6971 T_ofList CD6971
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4957 T_ofList CD4957

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ []
  · fin_cases hbad
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 10) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 10 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 10
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 10 := T_degree

noncomputable def bQ : Basis (Fin 10) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 10) (Fin 10) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 10) :
    bQ i = Adj.root ^ (i : ℕ) := by
  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by
    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]
  rw [pb.basis_eq_pow, pb_gen]
  congr 1

lemma bOm_cast_eq_vecMul :
    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =
      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by
  funext j
  change (timesTableO.basis j).val = _
  rw [timesTableO_basis_apply]
  rw [ofList_eq_sum']
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  rw [_root_.map_mul, _root_.map_sum]
  rw [← IsAdjoinRoot.algebraMap_apply Adj]
  have hdist :
      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
          (∑ x : Fin 10,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 10,
          (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ)) := by
    exact Finset.mul_sum Finset.univ _ _
  rw [hdist]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,
    _root_.map_pow, IsAdjoinRoot.map_X Adj]
  rw [bQ_apply]
  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by
  calc
    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by
      simpa [bQ] using
        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
    _ = (minpoly ℚ pb.gen).discr :=
      powerBasis_discr_eq_minpoly_discr pb
    _ = (map (algebraMap ℤ ℚ) T).discr := by
      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=
        T_monic.map (algebraMap ℤ ℚ)
      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by
        rw [pb_gen]
        calc
          minpoly ℚ Adj.root =
              map (algebraMap ℤ ℚ) T *
                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=
            AdjoinRoot.minpoly_root hirr.out.ne_zero
          _ = map (algebraMap ℤ ℚ) T := by
            rw [hqmonic.leadingCoeff]
            simp]
    _ = (T.discr : ℚ) := by
      exact (intCast_discr_eq_discr_map T T_monic
        (T_degree ▸ by norm_num)).symm

lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 10 =>
          (List.ofFn fun j : Fin 10 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

theorem field_discriminant_eq_recorded :
    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by
  apply Rat.intCast_injective
  have hbOmCast :
      ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by
    rw [← bOm_discr]
    exact discr_ringOfIntegers_cast K bOm
  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T] using
      (voightPolynomialDiscriminantInput 10 row row_mem)
  have hrecordedQ :
      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *
        (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=
      hbOmCast
    _ = Algebra.discr ℚ
        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by
      rw [bOm_cast_eq_vecMul]
    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=
      Algebra.discr_of_matrix_vecMul bQ P
    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]
    _ = P.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by
      rw [P_det_index_sq, one_mul]

end

end VoightMaximalOrderD10R392

namespace VoightMaximalOrderD10R399

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4898519815625, [-1, 10, -31, 21, 44, -56, -10, 29, -4, -4, 1], 1⟩
local notation "l" => [-1, 10, -31, 21, 44, -56, -10, 29, -4, -4, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsTen := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsTen_irreducible row row_mem
lemma T_monic : Monic T := by
  rw [← T_ofList]
  exact monic_ofList l rfl

abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)
instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1
    T_irreducible
instance KField : Field K := AdjoinRoot.instField
instance : Algebra ℤ K := Ring.toIntAlgebra K
instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
  AdjoinRoot.isAdjoinRoot _
local notation "θ" => Adj.root

def basisDenominator : ℤ := 1
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 31, -21, -44, 56, 10, -29, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 31, -21, -44, 56, 10, -29, 4, 4], ![4, -39, 114, -53, -197, 180, 96, -106, -13, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 31, -21, -44, 56, 10, -29, 4, 4], ![4, -39, 114, -53, -197, 180, 96, -106, -13, 20], ![20, -196, 581, -306, -933, 923, 380, -484, -26, 67]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 31, -21, -44, 56, 10, -29, 4, 4], ![4, -39, 114, -53, -197, 180, 96, -106, -13, 20], ![20, -196, 581, -306, -933, 923, 380, -484, -26, 67], ![67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 31, -21, -44, 56, 10, -29, 4, 4], ![4, -39, 114, -53, -197, 180, 96, -106, -13, 20], ![20, -196, 581, -306, -933, 923, 380, -484, -26, 67], ![67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], ![242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 31, -21, -44, 56, 10, -29, 4, 4], ![4, -39, 114, -53, -197, 180, 96, -106, -13, 20], ![20, -196, 581, -306, -933, 923, 380, -484, -26, 67], ![67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], ![242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752], ![752, -7278, 20959, -8940, -36289, 30638, 17818, -16569, -2417, 2413]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 31, -21, -44, 56, 10, -29, 4, 4], ![4, -39, 114, -53, -197, 180, 96, -106, -13, 20], ![20, -196, 581, -306, -933, 923, 380, -484, -26, 67], ![67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], ![242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752], ![752, -7278, 20959, -8940, -36289, 30638, 17818, -16569, -2417, 2413], ![2413, -23378, 67525, -29714, -115112, 98839, 54768, -52159, -6917, 7235]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 31, -21, -44, 56, 10, -29, 4, 4], ![4, -39, 114, -53, -197, 180, 96, -106, -13, 20], ![20, -196, 581, -306, -933, 923, 380, -484, -26, 67], ![67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], ![242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752], ![752, -7278, 20959, -8940, -36289, 30638, 17818, -16569, -2417, 2413], ![2413, -23378, 67525, -29714, -115112, 98839, 54768, -52159, -6917, 7235], ![7235, -69937, 200907, -84410, -348054, 290048, 171189, -155047, -23219, 22023]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 31, -21, -44, 56, 10, -29, 4, 4], ![4, -39, 114, -53, -197, 180, 96, -106, -13, 20], ![20, -196, 581, -306, -933, 923, 380, -484, -26, 67], ![67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], ![242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752], ![752, -7278, 20959, -8940, -36289, 30638, 17818, -16569, -2417, 2413], ![2413, -23378, 67525, -29714, -115112, 98839, 54768, -52159, -6917, 7235], ![7235, -69937, 200907, -84410, -348054, 290048, 171189, -155047, -23219, 22023], ![22023, -212995, 612776, -261576, -1053422, 885234, 510278, -467478, -66955, 64873]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-242, -67, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-242, -67, -20, -4, -1], [-752, -242, -67, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-242, -67, -20, -4, -1], [-752, -242, -67, -20, -4, -1], [-2413, -752, -242, -67, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-242, -67, -20, -4, -1], [-752, -242, -67, -20, -4, -1], [-2413, -752, -242, -67, -20, -4, -1], [-7235, -2413, -752, -242, -67, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-242, -67, -20, -4, -1], [-752, -242, -67, -20, -4, -1], [-2413, -752, -242, -67, -20, -4, -1], [-7235, -2413, -752, -242, -67, -20, -4, -1], [-22023, -7235, -2413, -752, -242, -67, -20, -4, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 10 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 10) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 10) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 10) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 31, -21, -44, 56, 10, -29, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 31, -21, -44, 56, 10, -29, 4, 4], [4, -39, 114, -53, -197, 180, 96, -106, -13, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 31, -21, -44, 56, 10, -29, 4, 4], [4, -39, 114, -53, -197, 180, 96, -106, -13, 20], [20, -196, 581, -306, -933, 923, 380, -484, -26, 67]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 31, -21, -44, 56, 10, -29, 4, 4], [4, -39, 114, -53, -197, 180, 96, -106, -13, 20], [20, -196, 581, -306, -933, 923, 380, -484, -26, 67], [67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 31, -21, -44, 56, 10, -29, 4, 4], [4, -39, 114, -53, -197, 180, 96, -106, -13, 20], [20, -196, 581, -306, -933, 923, 380, -484, -26, 67], [67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], [242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 31, -21, -44, 56, 10, -29, 4, 4], [4, -39, 114, -53, -197, 180, 96, -106, -13, 20], [20, -196, 581, -306, -933, 923, 380, -484, -26, 67], [67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], [242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752], [752, -7278, 20959, -8940, -36289, 30638, 17818, -16569, -2417, 2413]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 31, -21, -44, 56, 10, -29, 4, 4], [4, -39, 114, -53, -197, 180, 96, -106, -13, 20], [20, -196, 581, -306, -933, 923, 380, -484, -26, 67], [67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], [242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752], [752, -7278, 20959, -8940, -36289, 30638, 17818, -16569, -2417, 2413], [2413, -23378, 67525, -29714, -115112, 98839, 54768, -52159, -6917, 7235]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 31, -21, -44, 56, 10, -29, 4, 4], [4, -39, 114, -53, -197, 180, 96, -106, -13, 20], [20, -196, 581, -306, -933, 923, 380, -484, -26, 67], [67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], [242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752], [752, -7278, 20959, -8940, -36289, 30638, 17818, -16569, -2417, 2413], [2413, -23378, 67525, -29714, -115112, 98839, 54768, -52159, -6917, 7235], [7235, -69937, 200907, -84410, -348054, 290048, 171189, -155047, -23219, 22023]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 31, -21, -44, 56, 10, -29, 4, 4], [4, -39, 114, -53, -197, 180, 96, -106, -13, 20], [20, -196, 581, -306, -933, 923, 380, -484, -26, 67], [67, -650, 1881, -826, -3254, 2819, 1593, -1563, -216, 242], [242, -2353, 6852, -3201, -11474, 10298, 5239, -5425, -595, 752], [752, -7278, 20959, -8940, -36289, 30638, 17818, -16569, -2417, 2413], [2413, -23378, 67525, -29714, -115112, 98839, 54768, -52159, -6917, 7235], [7235, -69937, 200907, -84410, -348054, 290048, 171189, -155047, -23219, 22023], [22023, -212995, 612776, -261576, -1053422, 885234, 510278, -467478, -66955, 64873]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1321 : Fact (Nat.Prime 1321) := fact_iff.2 (by norm_num)
instance hp1186621 : Fact (Nat.Prime 1186621) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 4, 1]
  b' := [1, 2, 3, 1, 2]
  k := [1]
  f := [2, -2, 11, -3, -2, 14, 7, -3, 3, 2]
  g := [3, 0, 4, 1, 3, 1]
  h := [3, 0, 4, 1, 3, 1]
  a := [2, 3, 4, 1, 1]
  b := [4, 1, 0, 2, 2, 2, 1, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1321 : CertificateDedekindCriterionLists l 1321 where
  n := 2
  a' := [1092, 1099, 137, 213, 576, 900, 642, 651]
  b' := [1087, 96, 1266, 61, 482, 937, 1320, 95, 368]
  k := [1147, 803, 334, 670, 127, 895, 1199, 407, 1]
  f := [31, 205, 296, 12, 114, 167, 299, 43, 297, 1]
  g := [90, 595, 858, 33, 331, 484, 867, 123, 862, 1]
  h := [455, 1]
  a := [935, 157, 363, 1303, 645, 759, 804, 1004, 1053]
  b := [177, 565, 839, 677, 321, 226, 757, 812, 268]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1186621 : CertificateDedekindCriterionLists l 1186621 where
  n := 2
  a' := [324431, 598670, 657335, 1046242, 815782, 548028, 443052, 80856]
  b' := [1043313, 1138635, 493864, 275770, 474835, 558272, 856373, 442723, 1177637]
  k := [537334, 1171587, 1055416, 454625, 243707, 1136163, 974422, 744751, 1]
  f := [93335, 71271, 81012, 220817, 82925, 132321, 73910, 115321, 179798, 1]
  g := [501298, 382791, 435110, 1185996, 445381, 710688, 396964, 619382, 965684, 1]
  h := [220933, 1]
  a := [258058, 1124676, 323848, 325667, 738887, 17691, 793580, 1089326, 171934]
  b := [723790, 529115, 691789, 883004, 1119887, 353410, 736400, 87549, 1014687]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 1321, 1186621]
  exp := ![1, 1, 1]
  pdgood := [5, 1321, 1186621]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1321.out
    exact hp1186621.out
  a := [3915132763365, -11057755669634, -8901915936464, 36020073255540, -2101695805454, -24643495363134, 6094958325652, 4282450265988, -1350122458180]
  b := [392297039507, -2588666685385, 3783270844138, 2863553339344, -7367204336863, 140960512138, 3580468842614, -740625252558, -482249924926, 135012245818]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1321 T_ofList CD1321
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1186621 T_ofList CD1186621

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ []
  · fin_cases hbad
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 10) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 10 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 10
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 10 := T_degree

noncomputable def bQ : Basis (Fin 10) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 10) (Fin 10) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 10) :
    bQ i = Adj.root ^ (i : ℕ) := by
  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by
    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]
  rw [pb.basis_eq_pow, pb_gen]
  congr 1

lemma bOm_cast_eq_vecMul :
    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =
      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by
  funext j
  change (timesTableO.basis j).val = _
  rw [timesTableO_basis_apply]
  rw [ofList_eq_sum']
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  rw [_root_.map_mul, _root_.map_sum]
  rw [← IsAdjoinRoot.algebraMap_apply Adj]
  have hdist :
      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
          (∑ x : Fin 10,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 10,
          (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ)) := by
    exact Finset.mul_sum Finset.univ _ _
  rw [hdist]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,
    _root_.map_pow, IsAdjoinRoot.map_X Adj]
  rw [bQ_apply]
  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by
  calc
    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by
      simpa [bQ] using
        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
    _ = (minpoly ℚ pb.gen).discr :=
      powerBasis_discr_eq_minpoly_discr pb
    _ = (map (algebraMap ℤ ℚ) T).discr := by
      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=
        T_monic.map (algebraMap ℤ ℚ)
      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by
        rw [pb_gen]
        calc
          minpoly ℚ Adj.root =
              map (algebraMap ℤ ℚ) T *
                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=
            AdjoinRoot.minpoly_root hirr.out.ne_zero
          _ = map (algebraMap ℤ ℚ) T := by
            rw [hqmonic.leadingCoeff]
            simp]
    _ = (T.discr : ℚ) := by
      exact (intCast_discr_eq_discr_map T T_monic
        (T_degree ▸ by norm_num)).symm

lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 10 =>
          (List.ofFn fun j : Fin 10 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

theorem field_discriminant_eq_recorded :
    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by
  apply Rat.intCast_injective
  have hbOmCast :
      ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by
    rw [← bOm_discr]
    exact discr_ringOfIntegers_cast K bOm
  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T] using
      (voightPolynomialDiscriminantInput 10 row row_mem)
  have hrecordedQ :
      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *
        (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=
      hbOmCast
    _ = Algebra.discr ℚ
        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by
      rw [bOm_cast_eq_vecMul]
    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=
      Algebra.discr_of_matrix_vecMul bQ P
    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]
    _ = P.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by
      rw [P_det_index_sq, one_mul]

end

end VoightMaximalOrderD10R399

namespace VoightMaximalOrderD10R401

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4923711940625, [-1, 2, 18, -10, -46, 11, 41, -1, -13, -1, 1], 1⟩
local notation "l" => [-1, 2, 18, -10, -46, 11, 41, -1, -13, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsTen := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsTen_irreducible row row_mem
lemma T_monic : Monic T := by
  rw [← T_ofList]
  exact monic_ofList l rfl

abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)
instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1
    T_irreducible
instance KField : Field K := AdjoinRoot.instField
instance : Algebra ℤ K := Ring.toIntAlgebra K
instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
  AdjoinRoot.isAdjoinRoot _
local notation "θ" => Adj.root

def basisDenominator : ℤ := 1
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -18, 10, 46, -11, -41, 1, 13, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -18, 10, 46, -11, -41, 1, 13, 1], ![1, -1, -20, -8, 56, 35, -52, -40, 14, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -18, 10, 46, -11, -41, 1, 13, 1], ![1, -1, -20, -8, 56, 35, -52, -40, 14, 14], ![14, -27, -253, 120, 636, -98, -539, -38, 142, 28]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -18, 10, 46, -11, -41, 1, 13, 1], ![1, -1, -20, -8, 56, 35, -52, -40, 14, 14], ![14, -27, -253, 120, 636, -98, -539, -38, 142, 28], ![28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -18, 10, 46, -11, -41, 1, 13, 1], ![1, -1, -20, -8, 56, 35, -52, -40, 14, 14], ![14, -27, -253, 120, 636, -98, -539, -38, 142, 28], ![28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], ![170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -18, 10, 46, -11, -41, 1, 13, 1], ![1, -1, -20, -8, 56, 35, -52, -40, 14, 14], ![14, -27, -253, 120, 636, -98, -539, -38, 142, 28], ![28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], ![170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496], ![496, -822, -9240, 1858, 23985, 2391, -20798, -6146, 5372, 2195]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -18, 10, 46, -11, -41, 1, 13, 1], ![1, -1, -20, -8, 56, 35, -52, -40, 14, 14], ![14, -27, -253, 120, 636, -98, -539, -38, 142, 28], ![28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], ![170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496], ![496, -822, -9240, 1858, 23985, 2391, -20798, -6146, 5372, 2195], ![2195, -3894, -40332, 12710, 102828, -160, -87604, -18603, 22389, 7567]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -18, 10, 46, -11, -41, 1, 13, 1], ![1, -1, -20, -8, 56, 35, -52, -40, 14, 14], ![14, -27, -253, 120, 636, -98, -539, -38, 142, 28], ![28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], ![170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496], ![496, -822, -9240, 1858, 23985, 2391, -20798, -6146, 5372, 2195], ![2195, -3894, -40332, 12710, 102828, -160, -87604, -18603, 22389, 7567], ![7567, -12939, -140100, 35338, 360792, 19591, -310407, -80037, 79768, 29956]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -18, 10, 46, -11, -41, 1, 13, 1], ![1, -1, -20, -8, 56, 35, -52, -40, 14, 14], ![14, -27, -253, 120, 636, -98, -539, -38, 142, 28], ![28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], ![170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496], ![496, -822, -9240, 1858, 23985, 2391, -20798, -6146, 5372, 2195], ![2195, -3894, -40332, 12710, 102828, -160, -87604, -18603, 22389, 7567], ![7567, -12939, -140100, 35338, 360792, 19591, -310407, -80037, 79768, 29956], ![29956, -52345, -552147, 159460, 1413314, 31276, -1208605, -280451, 309391, 109724]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-14, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-14, -1, -1], [-28, -14, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-14, -1, -1], [-28, -14, -1, -1], [-170, -28, -14, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-14, -1, -1], [-28, -14, -1, -1], [-170, -28, -14, -1, -1], [-496, -170, -28, -14, -1, -1]], ![[], [], [], [-1], [-1, -1], [-14, -1, -1], [-28, -14, -1, -1], [-170, -28, -14, -1, -1], [-496, -170, -28, -14, -1, -1], [-2195, -496, -170, -28, -14, -1, -1]], ![[], [], [-1], [-1, -1], [-14, -1, -1], [-28, -14, -1, -1], [-170, -28, -14, -1, -1], [-496, -170, -28, -14, -1, -1], [-2195, -496, -170, -28, -14, -1, -1], [-7567, -2195, -496, -170, -28, -14, -1, -1]], ![[], [-1], [-1, -1], [-14, -1, -1], [-28, -14, -1, -1], [-170, -28, -14, -1, -1], [-496, -170, -28, -14, -1, -1], [-2195, -496, -170, -28, -14, -1, -1], [-7567, -2195, -496, -170, -28, -14, -1, -1], [-29956, -7567, -2195, -496, -170, -28, -14, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 10 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 10) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 10) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 10) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -18, 10, 46, -11, -41, 1, 13, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -18, 10, 46, -11, -41, 1, 13, 1], [1, -1, -20, -8, 56, 35, -52, -40, 14, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -18, 10, 46, -11, -41, 1, 13, 1], [1, -1, -20, -8, 56, 35, -52, -40, 14, 14], [14, -27, -253, 120, 636, -98, -539, -38, 142, 28]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -18, 10, 46, -11, -41, 1, 13, 1], [1, -1, -20, -8, 56, 35, -52, -40, 14, 14], [14, -27, -253, 120, 636, -98, -539, -38, 142, 28], [28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -18, 10, 46, -11, -41, 1, 13, 1], [1, -1, -20, -8, 56, 35, -52, -40, 14, 14], [14, -27, -253, 120, 636, -98, -539, -38, 142, 28], [28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], [170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -18, 10, 46, -11, -41, 1, 13, 1], [1, -1, -20, -8, 56, 35, -52, -40, 14, 14], [14, -27, -253, 120, 636, -98, -539, -38, 142, 28], [28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], [170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496], [496, -822, -9240, 1858, 23985, 2391, -20798, -6146, 5372, 2195]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -18, 10, 46, -11, -41, 1, 13, 1], [1, -1, -20, -8, 56, 35, -52, -40, 14, 14], [14, -27, -253, 120, 636, -98, -539, -38, 142, 28], [28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], [170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496], [496, -822, -9240, 1858, 23985, 2391, -20798, -6146, 5372, 2195], [2195, -3894, -40332, 12710, 102828, -160, -87604, -18603, 22389, 7567]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -18, 10, 46, -11, -41, 1, 13, 1], [1, -1, -20, -8, 56, 35, -52, -40, 14, 14], [14, -27, -253, 120, 636, -98, -539, -38, 142, 28], [28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], [170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496], [496, -822, -9240, 1858, 23985, 2391, -20798, -6146, 5372, 2195], [2195, -3894, -40332, 12710, 102828, -160, -87604, -18603, 22389, 7567], [7567, -12939, -140100, 35338, 360792, 19591, -310407, -80037, 79768, 29956]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -18, 10, 46, -11, -41, 1, 13, 1], [1, -1, -20, -8, 56, 35, -52, -40, 14, 14], [14, -27, -253, 120, 636, -98, -539, -38, 142, 28], [28, -42, -531, 27, 1408, 328, -1246, -511, 326, 170], [170, -312, -3102, 1169, 7847, -462, -6642, -1076, 1699, 496], [496, -822, -9240, 1858, 23985, 2391, -20798, -6146, 5372, 2195], [2195, -3894, -40332, 12710, 102828, -160, -87604, -18603, 22389, 7567], [7567, -12939, -140100, 35338, 360792, 19591, -310407, -80037, 79768, 29956], [29956, -52345, -552147, 159460, 1413314, 31276, -1208605, -280451, 309391, 109724]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp461 : Fact (Nat.Prime 461) := fact_iff.2 (by norm_num)
instance hp919 : Fact (Nat.Prime 919) := fact_iff.2 (by norm_num)
instance hp3719 : Fact (Nat.Prime 3719) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 3]
  b' := [1, 1, 1, 4]
  k := [1]
  f := [2, 2, 2, 10, 18, 7, -1, 5, 5, 1]
  g := [3, 2, 4, 4, 2, 1]
  h := [3, 2, 4, 4, 2, 1]
  a := [1, 0, 3, 0, 4]
  b := [3, 4, 4, 1, 1, 4, 2, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD461 : CertificateDedekindCriterionLists l 461 where
  n := 2
  a' := [190, 241, 251, 114, 24, 245, 366, 241]
  b' := [215, 44, 248, 387, 258, 57, 96, 242, 383]
  k := [245, 375, 29, 167, 280, 287, 231, 184, 1]
  f := [47, 109, 69, 8, 25, 72, 107, 81, 97, 1]
  g := [157, 363, 228, 25, 83, 240, 356, 268, 322, 1]
  h := [138, 1]
  a := [336, 319, 76, 396, 212, 241, 113, 316]
  b := [11, 374, 37, 421, 31, 356, 454, 145]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD919 : CertificateDedekindCriterionLists l 919 where
  n := 2
  a' := [329, 254, 606, 872, 444, 29, 656, 388]
  b' := [911, 115, 213, 503, 4, 0, 218, 899, 59]
  k := [661, 624, 483, 278, 354, 361, 31, 500, 1]
  f := [68, 132, 110, 157, 170, 102, 93, 156, 162, 1]
  g := [299, 579, 481, 688, 744, 445, 407, 684, 709, 1]
  h := [209, 1]
  a := [159, 858, 167, 659, 121, 330, 599, 910, 457]
  b := [597, 767, 626, 91, 805, 215, 63, 20, 462]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3719 : CertificateDedekindCriterionLists l 3719 where
  n := 2
  a' := [524, 2152, 1971, 288, 2876, 1924, 1506, 2702]
  b' := [2589, 110, 2985, 2313, 2613, 1049, 1978, 779, 113]
  k := [3314, 1950, 124, 1166, 1146, 899, 3387, 1172, 1]
  f := [471, 470, 1234, 193, 745, 42, 763, 105, 837, 1]
  g := [1376, 1372, 3604, 561, 2176, 121, 2229, 305, 2445, 1]
  h := [1273, 1]
  a := [1586, 968, 1569, 2444, 293, 2153, 1860, 239, 539]
  b := [222, 3630, 593, 3483, 993, 1597, 737, 3665, 3180]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 461, 919, 3719]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 461, 919, 3719]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp461.out
    exact hp919.out
    exact hp3719.out
  a := [73192983931, 1550859882116, 683145767304, -6723876347984, -5797487289190, 3295807071238, 3673658866622, 27818395588, -353202368720]
  b := [40535461518, -27401350197, -766767627527, -516798458498, 1279767268836, 1080488584934, -418200380920, -462099139892, -6313863246, 35320236872]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 461 T_ofList CD461
    exact satisfiesDedekindCriterion_of_certificate_lists T l 919 T_ofList CD919
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3719 T_ofList CD3719

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ []
  · fin_cases hbad
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 10) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 10 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 10
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 10 := T_degree

noncomputable def bQ : Basis (Fin 10) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 10) (Fin 10) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 10) :
    bQ i = Adj.root ^ (i : ℕ) := by
  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by
    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]
  rw [pb.basis_eq_pow, pb_gen]
  congr 1

lemma bOm_cast_eq_vecMul :
    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =
      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by
  funext j
  change (timesTableO.basis j).val = _
  rw [timesTableO_basis_apply]
  rw [ofList_eq_sum']
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  rw [_root_.map_mul, _root_.map_sum]
  rw [← IsAdjoinRoot.algebraMap_apply Adj]
  have hdist :
      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
          (∑ x : Fin 10,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 10,
          (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ)) := by
    exact Finset.mul_sum Finset.univ _ _
  rw [hdist]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,
    _root_.map_pow, IsAdjoinRoot.map_X Adj]
  rw [bQ_apply]
  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by
  calc
    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by
      simpa [bQ] using
        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
    _ = (minpoly ℚ pb.gen).discr :=
      powerBasis_discr_eq_minpoly_discr pb
    _ = (map (algebraMap ℤ ℚ) T).discr := by
      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=
        T_monic.map (algebraMap ℤ ℚ)
      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by
        rw [pb_gen]
        calc
          minpoly ℚ Adj.root =
              map (algebraMap ℤ ℚ) T *
                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=
            AdjoinRoot.minpoly_root hirr.out.ne_zero
          _ = map (algebraMap ℤ ℚ) T := by
            rw [hqmonic.leadingCoeff]
            simp]
    _ = (T.discr : ℚ) := by
      exact (intCast_discr_eq_discr_map T T_monic
        (T_degree ▸ by norm_num)).symm

lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 10 =>
          (List.ofFn fun j : Fin 10 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

theorem field_discriminant_eq_recorded :
    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by
  apply Rat.intCast_injective
  have hbOmCast :
      ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by
    rw [← bOm_discr]
    exact discr_ringOfIntegers_cast K bOm
  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T] using
      (voightPolynomialDiscriminantInput 10 row row_mem)
  have hrecordedQ :
      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *
        (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=
      hbOmCast
    _ = Algebra.discr ℚ
        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by
      rw [bOm_cast_eq_vecMul]
    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=
      Algebra.discr_of_matrix_vecMul bQ P
    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]
    _ = P.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by
      rw [P_det_index_sq, one_mul]

end

end VoightMaximalOrderD10R401

namespace VoightMaximalOrderD10R402

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4958790149120, [-1, 14, -44, 20, 67, -62, -18, 32, -4, -4, 1], 1⟩
local notation "l" => [-1, 14, -44, 20, 67, -62, -18, 32, -4, -4, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsTen := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsTen_irreducible row row_mem
lemma T_monic : Monic T := by
  rw [← T_ofList]
  exact monic_ofList l rfl

abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)
instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1
    T_irreducible
instance KField : Field K := AdjoinRoot.instField
instance : Algebra ℤ K := Ring.toIntAlgebra K
instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
  AdjoinRoot.isAdjoinRoot _
local notation "θ" => Adj.root

def basisDenominator : ℤ := 1
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, 44, -20, -67, 62, 18, -32, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, 44, -20, -67, 62, 18, -32, 4, 4], ![4, -55, 162, -36, -288, 181, 134, -110, -16, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, 44, -20, -67, 62, 18, -32, 4, 4], ![4, -55, 162, -36, -288, 181, 134, -110, -16, 20], ![20, -276, 825, -238, -1376, 952, 541, -506, -30, 64]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, 44, -20, -67, 62, 18, -32, 4, 4], ![4, -55, 162, -36, -288, 181, 134, -110, -16, 20], ![20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], ![64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, 44, -20, -67, 62, 18, -32, 4, 4], ![4, -55, 162, -36, -288, 181, 134, -110, -16, 20], ![20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], ![64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], ![226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, 44, -20, -67, 62, 18, -32, 4, 4], ![4, -55, 162, -36, -288, 181, 134, -110, -16, 20], ![20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], ![64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], ![226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654], ![654, -8930, 25676, -4012, -45798, 24951, 21258, -14268, -2512, 2013]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, 44, -20, -67, 62, 18, -32, 4, 4], ![4, -55, 162, -36, -288, 181, 134, -110, -16, 20], ![20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], ![64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], ![226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654], ![654, -8930, 25676, -4012, -45798, 24951, 21258, -14268, -2512, 2013], ![2013, -27528, 79642, -14584, -138883, 79008, 61185, -43158, -6216, 5540]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, 44, -20, -67, 62, 18, -32, 4, 4], ![4, -55, 162, -36, -288, 181, 134, -110, -16, 20], ![20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], ![64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], ![226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654], ![654, -8930, 25676, -4012, -45798, 24951, 21258, -14268, -2512, 2013], ![2013, -27528, 79642, -14584, -138883, 79008, 61185, -43158, -6216, 5540], ![5540, -75547, 216232, -31158, -385764, 204597, 178728, -116095, -20998, 15944]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, 44, -20, -67, 62, 18, -32, 4, 4], ![4, -55, 162, -36, -288, 181, 134, -110, -16, 20], ![20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], ![64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], ![226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654], ![654, -8930, 25676, -4012, -45798, 24951, 21258, -14268, -2512, 2013], ![2013, -27528, 79642, -14584, -138883, 79008, 61185, -43158, -6216, 5540], ![5540, -75547, 216232, -31158, -385764, 204597, 178728, -116095, -20998, 15944], ![15944, -217676, 625989, -102648, -1099406, 602764, 491589, -331480, -52319, 42778]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-226, -64, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-226, -64, -20, -4, -1], [-654, -226, -64, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-226, -64, -20, -4, -1], [-654, -226, -64, -20, -4, -1], [-2013, -654, -226, -64, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-226, -64, -20, -4, -1], [-654, -226, -64, -20, -4, -1], [-2013, -654, -226, -64, -20, -4, -1], [-5540, -2013, -654, -226, -64, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-226, -64, -20, -4, -1], [-654, -226, -64, -20, -4, -1], [-2013, -654, -226, -64, -20, -4, -1], [-5540, -2013, -654, -226, -64, -20, -4, -1], [-15944, -5540, -2013, -654, -226, -64, -20, -4, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 10 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 10) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 10) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 10) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, 44, -20, -67, 62, 18, -32, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, 44, -20, -67, 62, 18, -32, 4, 4], [4, -55, 162, -36, -288, 181, 134, -110, -16, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, 44, -20, -67, 62, 18, -32, 4, 4], [4, -55, 162, -36, -288, 181, 134, -110, -16, 20], [20, -276, 825, -238, -1376, 952, 541, -506, -30, 64]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, 44, -20, -67, 62, 18, -32, 4, 4], [4, -55, 162, -36, -288, 181, 134, -110, -16, 20], [20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], [64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, 44, -20, -67, 62, 18, -32, 4, 4], [4, -55, 162, -36, -288, 181, 134, -110, -16, 20], [20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], [64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], [226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, 44, -20, -67, 62, 18, -32, 4, 4], [4, -55, 162, -36, -288, 181, 134, -110, -16, 20], [20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], [64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], [226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654], [654, -8930, 25676, -4012, -45798, 24951, 21258, -14268, -2512, 2013]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, 44, -20, -67, 62, 18, -32, 4, 4], [4, -55, 162, -36, -288, 181, 134, -110, -16, 20], [20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], [64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], [226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654], [654, -8930, 25676, -4012, -45798, 24951, 21258, -14268, -2512, 2013], [2013, -27528, 79642, -14584, -138883, 79008, 61185, -43158, -6216, 5540]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, 44, -20, -67, 62, 18, -32, 4, 4], [4, -55, 162, -36, -288, 181, 134, -110, -16, 20], [20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], [64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], [226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654], [654, -8930, 25676, -4012, -45798, 24951, 21258, -14268, -2512, 2013], [2013, -27528, 79642, -14584, -138883, 79008, 61185, -43158, -6216, 5540], [5540, -75547, 216232, -31158, -385764, 204597, 178728, -116095, -20998, 15944]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, 44, -20, -67, 62, 18, -32, 4, 4], [4, -55, 162, -36, -288, 181, 134, -110, -16, 20], [20, -276, 825, -238, -1376, 952, 541, -506, -30, 64], [64, -876, 2540, -455, -4526, 2592, 2104, -1507, -250, 226], [226, -3100, 9068, -1980, -15597, 9486, 6660, -5128, -603, 654], [654, -8930, 25676, -4012, -45798, 24951, 21258, -14268, -2512, 2013], [2013, -27528, 79642, -14584, -138883, 79008, 61185, -43158, -6216, 5540], [5540, -75547, 216232, -31158, -385764, 204597, 178728, -116095, -20998, 15944], [15944, -217676, 625989, -102648, -1099406, 602764, 491589, -331480, -52319, 42778]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp968513701 : Fact (Nat.Prime 968513701) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [1, 1, 0, 1]
  k := [1]
  f := [1, -7, 23, -10, -33, 32, 9, -15, 2, 2]
  g := [1, 0, 1, 0, 0, 1]
  h := [1, 0, 1, 0, 0, 1]
  a := [0, 0, 1]
  b := [1, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 3, 0, 4, 3, 0, 3]
  b' := [1, 2, 3, 3, 3, 0, 1, 3]
  k := [1, 2, 2, 4, 4, 0, 2, 0, 1]
  f := [2, -1, 11, -1, -12, 15, 5, -5, 3, 2]
  g := [3, 2, 3, 4, 1, 4, 1, 2, 3, 1]
  h := [3, 1]
  a := [1, 3, 4, 0, 4, 1, 2, 0, 4]
  b := [3, 3, 3, 0, 3, 3, 1, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD968513701 : CertificateDedekindCriterionLists l 968513701 where
  n := 2
  a' := [602040875, 729875478, 383071031, 759476370, 922784603, 465934031, 469425893, 591963123]
  b' := [678122459, 853980918, 846640885, 628843997, 347887918, 778404010, 744928917, 312005124, 257064220]
  k := [495603887, 188424599, 65523072, 885365433, 534061588, 171600384, 484894715, 800688810, 1]
  f := [211020195, 163991757, 185507545, 213467668, 304758639, 344649881, 160070679, 160454856, 234858213, 1]
  g := [359709601, 279543905, 316220184, 363881616, 519498185, 587497661, 272859950, 273514827, 400344403, 1]
  h := [568169294, 1]
  a := [18738820, 106847976, 630241771, 571095945, 420343175, 318583527, 312644274, 715188697, 132634771]
  b := [175137093, 803274761, 36850880, 110737399, 283588115, 629229111, 786889292, 549751704, 835878930]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 5, 968513701]
  exp := ![1, 1, 1]
  pdgood := [2, 5, 968513701]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp968513701.out
  a := [628548109074, -3302061994846, 195341418102, 11286759148464, -5593574589678, -7940185463422, 4275371358918, 1309918752222, -671886566420]
  b := [45588089006, -577855977811, 1463836768391, 140119698128, -2684759050408, 864464115613, 1275655497297, -525642976681, -157867337879, 67188656642]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 968513701 T_ofList CD968513701

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ []
  · fin_cases hbad
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 10) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 10 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 10
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 10 := T_degree

noncomputable def bQ : Basis (Fin 10) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 10) (Fin 10) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 10) :
    bQ i = Adj.root ^ (i : ℕ) := by
  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by
    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]
  rw [pb.basis_eq_pow, pb_gen]
  congr 1

lemma bOm_cast_eq_vecMul :
    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =
      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by
  funext j
  change (timesTableO.basis j).val = _
  rw [timesTableO_basis_apply]
  rw [ofList_eq_sum']
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  rw [_root_.map_mul, _root_.map_sum]
  rw [← IsAdjoinRoot.algebraMap_apply Adj]
  have hdist :
      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
          (∑ x : Fin 10,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 10,
          (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ)) := by
    exact Finset.mul_sum Finset.univ _ _
  rw [hdist]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,
    _root_.map_pow, IsAdjoinRoot.map_X Adj]
  rw [bQ_apply]
  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by
  calc
    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by
      simpa [bQ] using
        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
    _ = (minpoly ℚ pb.gen).discr :=
      powerBasis_discr_eq_minpoly_discr pb
    _ = (map (algebraMap ℤ ℚ) T).discr := by
      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=
        T_monic.map (algebraMap ℤ ℚ)
      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by
        rw [pb_gen]
        calc
          minpoly ℚ Adj.root =
              map (algebraMap ℤ ℚ) T *
                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=
            AdjoinRoot.minpoly_root hirr.out.ne_zero
          _ = map (algebraMap ℤ ℚ) T := by
            rw [hqmonic.leadingCoeff]
            simp]
    _ = (T.discr : ℚ) := by
      exact (intCast_discr_eq_discr_map T T_monic
        (T_degree ▸ by norm_num)).symm

lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 10 =>
          (List.ofFn fun j : Fin 10 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

theorem field_discriminant_eq_recorded :
    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by
  apply Rat.intCast_injective
  have hbOmCast :
      ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by
    rw [← bOm_discr]
    exact discr_ringOfIntegers_cast K bOm
  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T] using
      (voightPolynomialDiscriminantInput 10 row row_mem)
  have hrecordedQ :
      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *
        (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=
      hbOmCast
    _ = Algebra.discr ℚ
        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by
      rw [bOm_cast_eq_vecMul]
    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=
      Algebra.discr_of_matrix_vecMul bQ P
    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]
    _ = P.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by
      rw [P_det_index_sq, one_mul]

end

end VoightMaximalOrderD10R402

end TraceEuclidean
