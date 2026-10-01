import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk219
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

namespace VoightMaximalOrderD10R605

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6394969403125, [1, -5, 0, 25, -14, -37, 25, 15, -11, -1, 1], 1⟩
local notation "l" => [1, -5, 0, 25, -14, -37, 25, 15, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 0, -25, 14, 37, -25, -15, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], ![-1, 4, 5, -25, -11, 51, 12, -40, -4, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], ![-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], ![-12, 59, 4, -295, 143, 433, -249, -168, 92, 8]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], ![-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], ![-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], ![-8, 28, 59, -196, -183, 439, 233, -369, -80, 100]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], ![-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], ![-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], ![-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], ![-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], ![-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], ![-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], ![-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], ![-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20], ![-20, 0, 492, -472, -2161, 1944, 3017, -2361, -1047, 751]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], ![-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], ![-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], ![-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], ![-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20], ![-20, 0, 492, -472, -2161, 1944, 3017, -2361, -1047, 751], ![-751, 3735, 0, -18283, 10042, 25626, -16831, -8248, 5900, -296]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], ![-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], ![-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], ![-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], ![-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20], ![-20, 0, 492, -472, -2161, 1944, 3017, -2361, -1047, 751], ![-751, 3735, 0, -18283, 10042, 25626, -16831, -8248, 5900, -296], ![296, -2231, 3735, 7400, -22427, -910, 33026, -12391, -11504, 5604]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], ![-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], ![-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], ![-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], ![-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20], ![-20, 0, 492, -472, -2161, 1944, 3017, -2361, -1047, 751], ![-751, 3735, 0, -18283, 10042, 25626, -16831, -8248, 5900, -296], ![296, -2231, 3735, 7400, -22427, -910, 33026, -12391, -11504, 5604], ![-5604, 28316, -2231, -136365, 85856, 184921, -141010, -51034, 49253, -5900]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-8, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-8, -12, -1, -1], [-100, -8, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-8, -12, -1, -1], [-100, -8, -12, -1, -1], [-20, -100, -8, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-8, -12, -1, -1], [-100, -8, -12, -1, -1], [-20, -100, -8, -12, -1, -1], [-751, -20, -100, -8, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-8, -12, -1, -1], [-100, -8, -12, -1, -1], [-20, -100, -8, -12, -1, -1], [-751, -20, -100, -8, -12, -1, -1], [296, -751, -20, -100, -8, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-8, -12, -1, -1], [-100, -8, -12, -1, -1], [-20, -100, -8, -12, -1, -1], [-751, -20, -100, -8, -12, -1, -1], [296, -751, -20, -100, -8, -12, -1, -1], [-5604, 296, -751, -20, -100, -8, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 0, -25, 14, 37, -25, -15, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], [-1, 4, 5, -25, -11, 51, 12, -40, -4, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], [-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], [-12, 59, 4, -295, 143, 433, -249, -168, 92, 8]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], [-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], [-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], [-8, 28, 59, -196, -183, 439, 233, -369, -80, 100]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], [-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], [-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], [-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], [-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], [-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], [-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], [-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], [-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20], [-20, 0, 492, -472, -2161, 1944, 3017, -2361, -1047, 751]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], [-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], [-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], [-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], [-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20], [-20, 0, 492, -472, -2161, 1944, 3017, -2361, -1047, 751], [-751, 3735, 0, -18283, 10042, 25626, -16831, -8248, 5900, -296]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], [-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], [-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], [-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], [-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20], [-20, 0, 492, -472, -2161, 1944, 3017, -2361, -1047, 751], [-751, 3735, 0, -18283, 10042, 25626, -16831, -8248, 5900, -296], [296, -2231, 3735, 7400, -22427, -910, 33026, -12391, -11504, 5604]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 0, -25, 14, 37, -25, -15, 11, 1], [-1, 4, 5, -25, -11, 51, 12, -40, -4, 12], [-12, 59, 4, -295, 143, 433, -249, -168, 92, 8], [-8, 28, 59, -196, -183, 439, 233, -369, -80, 100], [-100, 492, 28, -2441, 1204, 3517, -2061, -1267, 731, 20], [-20, 0, 492, -472, -2161, 1944, 3017, -2361, -1047, 751], [-751, 3735, 0, -18283, 10042, 25626, -16831, -8248, 5900, -296], [296, -2231, 3735, 7400, -22427, -910, 33026, -12391, -11504, 5604], [-5604, 28316, -2231, -136365, 85856, 184921, -141010, -51034, 49253, -5900]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2046390209 : Fact (Nat.Prime 2046390209) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4]
  b' := [0, 4, 2]
  k := [1]
  f := [3, 1, 0, -5, 6, 9, -5, -3, 3, 1]
  g := [4, 0, 0, 0, 2, 1]
  h := [4, 0, 0, 0, 2, 1]
  a := [0, 0, 1, 2]
  b := [4, 0, 3, 2, 0, 4, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2046390209 : CertificateDedekindCriterionLists l 2046390209 where
  n := 2
  a' := [1443857255, 1816372794, 131120355, 1622553660, 1757721559, 1051341121, 237301966, 235075823]
  b' := [329477387, 1247439381, 546944444, 1315707858, 1541102144, 1590648293, 1669712130, 1781676222, 201257154]
  k := [985998562, 881241507, 1959691678, 2014568495, 528387131, 1756210306, 29082883, 1403388312, 1]
  f := [12057103, 106308773, 157291847, 263033802, 271075174, 173372181, 60110475, 232693616, 270991100, 1]
  g := [76744836, 676667467, 1001180547, 1674240152, 1725424400, 1103533704, 382610027, 1481121409, 1724889260, 1]
  h := [321500948, 1]
  a := [399300203, 233818678, 1665987973, 406185596, 577238762, 1318617510, 939211397, 865193048, 1119504539]
  b := [1212654411, 1940440294, 1349571637, 378278321, 1599681260, 829598027, 1417866216, 1941487102, 926885670]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 2046390209]
  exp := ![1, 1]
  pdgood := [5, 2046390209]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2046390209.out
  a := [-416093185245, -1171748628000, 3211143182750, 4162445818062, -6045362715470, -2576311383170, 3171238122677, 192937658036, -355351302540]
  b := [-85265027258, 181743459645, 535001855680, -777999745398, -920893486748, 1001326292608, 388925511300, -396569883969, -22847278829, 35535130254]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2046390209 T_ofList CD2046390209

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

end VoightMaximalOrderD10R605

namespace VoightMaximalOrderD10R607

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6406090532073, [1, 8, 13, -19, -42, 13, 36, -3, -11, 0, 1], 1⟩
local notation "l" => [1, 8, 13, -19, -42, 13, 36, -3, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -13, 19, 42, -13, -36, 3, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], ![0, -1, -8, -13, 19, 42, -13, -36, 3, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], ![0, -1, -8, -13, 19, 42, -13, -36, 3, 11], ![-11, -88, -144, 201, 449, -124, -354, 20, 85, 3]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], ![0, -1, -8, -13, 19, 42, -13, -36, 3, 11], ![-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], ![-3, -35, -127, -87, 327, 410, -232, -345, 53, 85]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], ![0, -1, -8, -13, 19, 42, -13, -36, 3, 11], ![-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], ![-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], ![-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], ![0, -1, -8, -13, 19, 42, -13, -36, 3, 11], ![-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], ![-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], ![-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53], ![-53, -509, -1372, -133, 3714, 2794, -2686, -2491, 606, 590]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], ![0, -1, -8, -13, 19, 42, -13, -36, 3, 11], ![-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], ![-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], ![-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53], ![-53, -509, -1372, -133, 3714, 2794, -2686, -2491, 606, 590], ![-590, -4773, -8179, 9838, 24647, -3956, -18446, -916, 3999, 606]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], ![0, -1, -8, -13, 19, 42, -13, -36, 3, 11], ![-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], ![-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], ![-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53], ![-53, -509, -1372, -133, 3714, 2794, -2686, -2491, 606, 590], ![-590, -4773, -8179, 9838, 24647, -3956, -18446, -916, 3999, 606], ![-606, -5438, -12651, 3335, 35290, 16769, -25772, -16628, 5750, 3999]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], ![0, -1, -8, -13, 19, 42, -13, -36, 3, 11], ![-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], ![-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], ![-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53], ![-53, -509, -1372, -133, 3714, 2794, -2686, -2491, 606, 590], ![-590, -4773, -8179, 9838, 24647, -3956, -18446, -916, 3999, 606], ![-606, -5438, -12651, 3335, 35290, 16769, -25772, -16628, 5750, 3999], ![-3999, -32598, -57425, 63330, 171293, -16697, -127195, -13775, 27361, 5750]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-85, -3, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-85, -3, -11, 0, -1], [-53, -85, -3, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-85, -3, -11, 0, -1], [-53, -85, -3, -11, 0, -1], [-590, -53, -85, -3, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-85, -3, -11, 0, -1], [-53, -85, -3, -11, 0, -1], [-590, -53, -85, -3, -11, 0, -1], [-606, -590, -53, -85, -3, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-85, -3, -11, 0, -1], [-53, -85, -3, -11, 0, -1], [-590, -53, -85, -3, -11, 0, -1], [-606, -590, -53, -85, -3, -11, 0, -1], [-3999, -606, -590, -53, -85, -3, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -13, 19, 42, -13, -36, 3, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], [0, -1, -8, -13, 19, 42, -13, -36, 3, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], [0, -1, -8, -13, 19, 42, -13, -36, 3, 11], [-11, -88, -144, 201, 449, -124, -354, 20, 85, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], [0, -1, -8, -13, 19, 42, -13, -36, 3, 11], [-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], [-3, -35, -127, -87, 327, 410, -232, -345, 53, 85]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], [0, -1, -8, -13, 19, 42, -13, -36, 3, 11], [-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], [-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], [-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], [0, -1, -8, -13, 19, 42, -13, -36, 3, 11], [-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], [-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], [-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53], [-53, -509, -1372, -133, 3714, 2794, -2686, -2491, 606, 590]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], [0, -1, -8, -13, 19, 42, -13, -36, 3, 11], [-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], [-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], [-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53], [-53, -509, -1372, -133, 3714, 2794, -2686, -2491, 606, 590], [-590, -4773, -8179, 9838, 24647, -3956, -18446, -916, 3999, 606]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], [0, -1, -8, -13, 19, 42, -13, -36, 3, 11], [-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], [-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], [-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53], [-53, -509, -1372, -133, 3714, 2794, -2686, -2491, 606, 590], [-590, -4773, -8179, 9838, 24647, -3956, -18446, -916, 3999, 606], [-606, -5438, -12651, 3335, 35290, 16769, -25772, -16628, 5750, 3999]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -13, 19, 42, -13, -36, 3, 11, 0], [0, -1, -8, -13, 19, 42, -13, -36, 3, 11], [-11, -88, -144, 201, 449, -124, -354, 20, 85, 3], [-3, -35, -127, -87, 327, 410, -232, -345, 53, 85], [-85, -683, -1140, 1488, 3483, -778, -2650, 23, 590, 53], [-53, -509, -1372, -133, 3714, 2794, -2686, -2491, 606, 590], [-590, -4773, -8179, 9838, 24647, -3956, -18446, -916, 3999, 606], [-606, -5438, -12651, 3335, 35290, 16769, -25772, -16628, 5750, 3999], [-3999, -32598, -57425, 63330, 171293, -16697, -127195, -13775, 27361, 5750]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp79087537433 : Fact (Nat.Prime 79087537433) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [2, 2, 0, 0, 2, 1]
  b' := [2, 0, 0, 0, 2, 0, 1]
  k := [1, 1, 0, 1, 2, 0, 0, 2, 0, 0, 1, 2, 2, 0, 1]
  f := [0, -2, -3, 8, 16, -3, -11, 2, 5, 1]
  g := [1, 1, 2, 2, 2, 0, 1, 2, 1]
  h := [1, 1, 1]
  a := [0, 0, 0, 0, 0, 0, 0, 1]
  b := [1, 2, 2, 1, 1, 1, 2, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD79087537433 : CertificateDedekindCriterionLists l 79087537433 where
  n := 2
  a' := [62171981325, 72039001755, 35295512848, 58821837373, 32091730722, 15830276206, 48376757884, 1049706520]
  b' := [11329134951, 43995583626, 36497540395, 12096626702, 64121607597, 70458989687, 629942459, 16468003547, 70183399216]
  k := [54353902729, 37606198409, 61360709452, 37038229733, 25449781287, 28127205514, 27750892218, 22927225240, 1]
  f := [2178130012, 38573573833, 63020242783, 58827726191, 37118909257, 64613433450, 2819605341, 52992098062, 9801980225, 1]
  g := [2547366769, 45112568856, 73703438892, 68800206584, 43411309435, 75566707356, 3297585041, 61975322354, 11463612620, 1]
  h := [67623924813, 1]
  a := [31382678137, 26620859981, 44638648333, 11074217103, 52208365709, 58351830294, 19644678218, 58655875722, 57698594359]
  b := [66400658606, 68862537283, 57457550291, 26937997169, 44223065807, 24576228996, 64056492776, 61387584858, 21388943074]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![3, 79087537433]
  exp := ![2, 1]
  pdgood := [3, 79087537433]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp79087537433.out
  a := [-19753031777599, 43274117416, 133173957847501, 8067531585406, -176914727798364, -7447564871310, 73512650653620, 2917499640200, -8545349141800]
  b := [2558102451812, 11433789544533, -3524678260327, -34525063869363, 456610068489, 29888337716918, 617524985213, -9231241876558, -291749964020, 854534914180]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 79087537433 T_ofList CD79087537433

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

end VoightMaximalOrderD10R607

namespace VoightMaximalOrderD10R611

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6431717565625, [1, 12, 47, 57, -31, -80, 9, 36, -7, -4, 1], 1⟩
local notation "l" => [1, 12, 47, 57, -31, -80, 9, 36, -7, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -47, -57, 31, 80, -9, -36, 7, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], ![-4, -49, -200, -275, 67, 351, 44, -153, -8, 23]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], ![-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], ![-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], ![-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], ![-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], ![-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], ![-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], ![-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], ![-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], ![-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], ![-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], ![-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], ![-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], ![-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180], ![-1180, -14504, -59672, -84459, 12744, 99146, 17993, -38418, -2973, 4248]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], ![-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], ![-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], ![-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], ![-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180], ![-1180, -14504, -59672, -84459, 12744, 99146, 17993, -38418, -2973, 4248], ![-4248, -52156, -214160, -301808, 47229, 352584, 60914, -134935, -8682, 14019]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], ![-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], ![-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], ![-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], ![-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180], ![-1180, -14504, -59672, -84459, 12744, 99146, 17993, -38418, -2973, 4248], ![-4248, -52156, -214160, -301808, 47229, 352584, 60914, -134935, -8682, 14019], ![-14019, -172476, -711049, -1013243, 132781, 1168749, 226413, -443770, -36802, 47394]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], ![-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], ![-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], ![-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], ![-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180], ![-1180, -14504, -59672, -84459, 12744, 99146, 17993, -38418, -2973, 4248], ![-4248, -52156, -214160, -301808, 47229, 352584, 60914, -134935, -8682, 14019], ![-14019, -172476, -711049, -1013243, 132781, 1168749, 226413, -443770, -36802, 47394], ![-47394, -582747, -2399994, -3412507, 455971, 3924301, 742203, -1479771, -112012, 152774]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-23, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-23, -4, -1], [-84, -23, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-23, -4, -1], [-84, -23, -4, -1], [-344, -84, -23, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-23, -4, -1], [-84, -23, -4, -1], [-344, -84, -23, -4, -1], [-1180, -344, -84, -23, -4, -1]], ![[], [], [], [-1], [-4, -1], [-23, -4, -1], [-84, -23, -4, -1], [-344, -84, -23, -4, -1], [-1180, -344, -84, -23, -4, -1], [-4248, -1180, -344, -84, -23, -4, -1]], ![[], [], [-1], [-4, -1], [-23, -4, -1], [-84, -23, -4, -1], [-344, -84, -23, -4, -1], [-1180, -344, -84, -23, -4, -1], [-4248, -1180, -344, -84, -23, -4, -1], [-14019, -4248, -1180, -344, -84, -23, -4, -1]], ![[], [-1], [-4, -1], [-23, -4, -1], [-84, -23, -4, -1], [-344, -84, -23, -4, -1], [-1180, -344, -84, -23, -4, -1], [-4248, -1180, -344, -84, -23, -4, -1], [-14019, -4248, -1180, -344, -84, -23, -4, -1], [-47394, -14019, -4248, -1180, -344, -84, -23, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -47, -57, 31, 80, -9, -36, 7, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], [-4, -49, -200, -275, 67, 351, 44, -153, -8, 23]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], [-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], [-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], [-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], [-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], [-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], [-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], [-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], [-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], [-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], [-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], [-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], [-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], [-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180], [-1180, -14504, -59672, -84459, 12744, 99146, 17993, -38418, -2973, 4248]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], [-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], [-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], [-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], [-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180], [-1180, -14504, -59672, -84459, 12744, 99146, 17993, -38418, -2973, 4248], [-4248, -52156, -214160, -301808, 47229, 352584, 60914, -134935, -8682, 14019]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], [-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], [-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], [-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], [-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180], [-1180, -14504, -59672, -84459, 12744, 99146, 17993, -38418, -2973, 4248], [-4248, -52156, -214160, -301808, 47229, 352584, 60914, -134935, -8682, 14019], [-14019, -172476, -711049, -1013243, 132781, 1168749, 226413, -443770, -36802, 47394]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -47, -57, 31, 80, -9, -36, 7, 4], [-4, -49, -200, -275, 67, 351, 44, -153, -8, 23], [-23, -280, -1130, -1511, 438, 1907, 144, -784, 8, 84], [-84, -1031, -4228, -5918, 1093, 7158, 1151, -2880, -196, 344], [-344, -4212, -17199, -23836, 4746, 28613, 4062, -11233, -472, 1180], [-1180, -14504, -59672, -84459, 12744, 99146, 17993, -38418, -2973, 4248], [-4248, -52156, -214160, -301808, 47229, 352584, 60914, -134935, -8682, 14019], [-14019, -172476, -711049, -1013243, 132781, 1168749, 226413, -443770, -36802, 47394], [-47394, -582747, -2399994, -3412507, 455971, 3924301, 742203, -1479771, -112012, 152774]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp619 : Fact (Nat.Prime 619) := fact_iff.2 (by norm_num)
instance hp27479 : Fact (Nat.Prime 27479) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 1, 3]
  b' := [4, 0, 0, 2, 1]
  k := [1]
  f := [3, 4, -3, -5, 15, 24, 3, -4, 4, 2]
  g := [4, 4, 2, 2, 3, 1]
  h := [4, 4, 2, 2, 3, 1]
  a := [3, 3, 1, 2, 2]
  b := [3, 3, 4, 4, 0, 2, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 3
  a' := [4, 0, 0, 7, 3, 4, 9]
  b' := [0, 3, 5, 4, 8, 10, 2, 3]
  k := [5, 6, 1, 1, 7, 10, 4, 9, 4, 10, 7, 7, 6, 2, 1]
  f := [1, 0, -4, -3, 5, 10, 5, 2, 3, 1]
  g := [3, 0, 0, 6, 0, 6, 10, 3, 1]
  h := [4, 4, 1]
  a := [9, 0, 9, 9, 5, 5, 8, 9]
  b := [1, 0, 9, 4, 10, 6, 1, 3, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD619 : CertificateDedekindCriterionLists l 619 where
  n := 2
  a' := [486, 436, 438, 79, 262, 485, 583, 141]
  b' := [56, 58, 306, 191, 310, 110, 97, 332, 397]
  k := [88, 15, 20, 280, 303, 504, 579, 312, 1]
  f := [248, 145, 424, 260, 52, 389, 12, 137, 115, 1]
  g := [333, 194, 569, 348, 69, 522, 15, 184, 154, 1]
  h := [461, 1]
  a := [518, 352, 198, 330, 89, 560, 391, 323, 261]
  b := [144, 540, 113, 381, 359, 55, 74, 571, 358]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD27479 : CertificateDedekindCriterionLists l 27479 where
  n := 2
  a' := [4062, 26068, 20937, 2809, 4681, 13874, 20382, 14076]
  b' := [19542, 22920, 13492, 9293, 10656, 8640, 8112, 12685, 25915]
  k := [23803, 3498, 21245, 27352, 3922, 26434, 6396, 25308, 1]
  f := [814, 11751, 4744, 3936, 9491, 6497, 2327, 1927, 6825, 1]
  g := [1509, 21784, 8793, 7296, 17594, 12043, 4313, 3572, 12652, 1]
  h := [14823, 1]
  a := [16929, 12452, 456, 20635, 14863, 21314, 19498, 20683, 6713]
  b := [13667, 22620, 6676, 23579, 19176, 4834, 12385, 20830, 20766]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 11, 619, 27479]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 11, 619, 27479]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp619.out
    exact hp27479.out
  a := [-894818142745, -3077285397634, 409626398400, 6968706495046, 286022781380, -4687846675288, 811725022296, 687871614594, -177981848740]
  b := [74646138775, 566530505477, 1046324486405, -185189366760, -1408540393113, -17325811978, 666993027335, -104204482688, -75906435409, 17798184874]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 619 T_ofList CD619
    exact satisfiesDedekindCriterion_of_certificate_lists T l 27479 T_ofList CD27479

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

end VoightMaximalOrderD10R611

namespace VoightMaximalOrderD10R620

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6489303270344, [-2, 2, 15, -9, -36, 12, 33, -4, -11, 0, 1], 1⟩
local notation "l" => [-2, 2, 15, -9, -36, 12, 33, -4, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, -2, -15, 9, 36, -12, -33, 4, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, -2, -15, 9, 36, -12, -33, 4, 11, 0], ![0, 2, -2, -15, 9, 36, -12, -33, 4, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, -2, -15, 9, 36, -12, -33, 4, 11, 0], ![0, 2, -2, -15, 9, 36, -12, -33, 4, 11], ![22, -22, -163, 97, 381, -123, -327, 32, 88, 4]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, -2, -15, 9, 36, -12, -33, 4, 11, 0], ![0, 2, -2, -15, 9, 36, -12, -33, 4, 11], ![22, -22, -163, 97, 381, -123, -327, 32, 88, 4], ![8, 14, -82, -127, 241, 333, -255, -311, 76, 88]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, -2, -15, 9, 36, -12, -33, 4, 11, 0], ![0, 2, -2, -15, 9, 36, -12, -33, 4, 11], ![22, -22, -163, 97, 381, -123, -327, 32, 88, 4], ![8, 14, -82, -127, 241, 333, -255, -311, 76, 88], ![176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, -2, -15, 9, 36, -12, -33, 4, 11, 0], ![0, 2, -2, -15, 9, 36, -12, -33, 4, 11], ![22, -22, -163, 97, 381, -123, -327, 32, 88, 4], ![8, 14, -82, -127, 241, 333, -255, -311, 76, 88], ![176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76], ![152, 24, -1308, -622, 3446, 2129, -3323, -2267, 933, 657]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, -2, -15, 9, 36, -12, -33, 4, 11, 0], ![0, 2, -2, -15, 9, 36, -12, -33, 4, 11], ![22, -22, -163, 97, 381, -123, -327, 32, 88, 4], ![8, 14, -82, -127, 241, 333, -255, -311, 76, 88], ![176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76], ![152, 24, -1308, -622, 3446, 2129, -3323, -2267, 933, 657], ![1314, -1162, -9831, 4605, 23030, -4438, -19552, -695, 4960, 933]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, -2, -15, 9, 36, -12, -33, 4, 11, 0], ![0, 2, -2, -15, 9, 36, -12, -33, 4, 11], ![22, -22, -163, 97, 381, -123, -327, 32, 88, 4], ![8, 14, -82, -127, 241, 333, -255, -311, 76, 88], ![176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76], ![152, 24, -1308, -622, 3446, 2129, -3323, -2267, 933, 657], ![1314, -1162, -9831, 4605, 23030, -4438, -19552, -695, 4960, 933], ![1866, -552, -15157, -1434, 38193, 11834, -35227, -15820, 9568, 4960]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, -2, -15, 9, 36, -12, -33, 4, 11, 0], ![0, 2, -2, -15, 9, 36, -12, -33, 4, 11], ![22, -22, -163, 97, 381, -123, -327, 32, 88, 4], ![8, 14, -82, -127, 241, 333, -255, -311, 76, 88], ![176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76], ![152, 24, -1308, -622, 3446, 2129, -3323, -2267, 933, 657], ![1314, -1162, -9831, 4605, 23030, -4438, -19552, -695, 4960, 933], ![1866, -552, -15157, -1434, 38193, 11834, -35227, -15820, 9568, 4960], ![9920, -8054, -74952, 29483, 177126, -21327, -151846, -15387, 38740, 9568]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1], [-76, -88, -4, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1], [-76, -88, -4, -11, 0, -1], [-657, -76, -88, -4, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1], [-76, -88, -4, -11, 0, -1], [-657, -76, -88, -4, -11, 0, -1], [-933, -657, -76, -88, -4, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1], [-76, -88, -4, -11, 0, -1], [-657, -76, -88, -4, -11, 0, -1], [-933, -657, -76, -88, -4, -11, 0, -1], [-4960, -933, -657, -76, -88, -4, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, -2, -15, 9, 36, -12, -33, 4, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, -2, -15, 9, 36, -12, -33, 4, 11, 0], [0, 2, -2, -15, 9, 36, -12, -33, 4, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, -2, -15, 9, 36, -12, -33, 4, 11, 0], [0, 2, -2, -15, 9, 36, -12, -33, 4, 11], [22, -22, -163, 97, 381, -123, -327, 32, 88, 4]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, -2, -15, 9, 36, -12, -33, 4, 11, 0], [0, 2, -2, -15, 9, 36, -12, -33, 4, 11], [22, -22, -163, 97, 381, -123, -327, 32, 88, 4], [8, 14, -82, -127, 241, 333, -255, -311, 76, 88]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, -2, -15, 9, 36, -12, -33, 4, 11, 0], [0, 2, -2, -15, 9, 36, -12, -33, 4, 11], [22, -22, -163, 97, 381, -123, -327, 32, 88, 4], [8, 14, -82, -127, 241, 333, -255, -311, 76, 88], [176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, -2, -15, 9, 36, -12, -33, 4, 11, 0], [0, 2, -2, -15, 9, 36, -12, -33, 4, 11], [22, -22, -163, 97, 381, -123, -327, 32, 88, 4], [8, 14, -82, -127, 241, 333, -255, -311, 76, 88], [176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76], [152, 24, -1308, -622, 3446, 2129, -3323, -2267, 933, 657]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, -2, -15, 9, 36, -12, -33, 4, 11, 0], [0, 2, -2, -15, 9, 36, -12, -33, 4, 11], [22, -22, -163, 97, 381, -123, -327, 32, 88, 4], [8, 14, -82, -127, 241, 333, -255, -311, 76, 88], [176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76], [152, 24, -1308, -622, 3446, 2129, -3323, -2267, 933, 657], [1314, -1162, -9831, 4605, 23030, -4438, -19552, -695, 4960, 933]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, -2, -15, 9, 36, -12, -33, 4, 11, 0], [0, 2, -2, -15, 9, 36, -12, -33, 4, 11], [22, -22, -163, 97, 381, -123, -327, 32, 88, 4], [8, 14, -82, -127, 241, 333, -255, -311, 76, 88], [176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76], [152, 24, -1308, -622, 3446, 2129, -3323, -2267, 933, 657], [1314, -1162, -9831, 4605, 23030, -4438, -19552, -695, 4960, 933], [1866, -552, -15157, -1434, 38193, 11834, -35227, -15820, 9568, 4960]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, -2, -15, 9, 36, -12, -33, 4, 11, 0], [0, 2, -2, -15, 9, 36, -12, -33, 4, 11], [22, -22, -163, 97, 381, -123, -327, 32, 88, 4], [8, 14, -82, -127, 241, 333, -255, -311, 76, 88], [176, -168, -1306, 710, 3041, -815, -2571, 97, 657, 76], [152, 24, -1308, -622, 3446, 2129, -3323, -2267, 933, 657], [1314, -1162, -9831, 4605, 23030, -4438, -19552, -695, 4960, 933], [1866, -552, -15157, -1434, 38193, 11834, -35227, -15820, 9568, 4960], [9920, -8054, -74952, 29483, 177126, -21327, -151846, -15387, 38740, 9568]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp173 : Fact (Nat.Prime 173) := fact_iff.2 (by norm_num)
instance hp4688802941 : Fact (Nat.Prime 4688802941) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1, 0, 1, 0, 1]
  b' := [1, 0, 0, 1, 0, 1, 0, 1]
  k := [1, 1, 0, 0, 1, 0, 1, 0, 1]
  f := [1, -1, -7, 5, 18, -6, -16, 2, 6]
  g := [0, 1, 1, 0, 0, 1, 0, 1, 0, 1]
  h := [0, 1]
  a := [1, 0, 0, 1, 1, 1, 1]
  b := [1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD173 : CertificateDedekindCriterionLists l 173 where
  n := 2
  a' := [144, 104, 27, 34, 96, 18, 87, 59]
  b' := [137, 47, 85, 38, 28, 41, 77, 122, 128]
  k := [145, 144, 129, 141, 121, 90, 51, 5, 1]
  f := [34, 64, 40, 18, 48, 34, 24, 61, 44, 1]
  g := [70, 131, 81, 36, 98, 69, 49, 125, 89, 1]
  h := [84, 1]
  a := [88, 172, 112, 50, 36, 97, 84, 171, 90]
  b := [24, 58, 12, 125, 18, 23, 132, 73, 83]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4688802941 : CertificateDedekindCriterionLists l 4688802941 where
  n := 2
  a' := [689501711, 3576432720, 1467492545, 3241768782, 803262033, 2111475989, 4476160519, 2316508709]
  b' := [815053525, 461091013, 2536982587, 1746086602, 568688790, 1923189772, 3346003228, 2423359359, 263588248]
  k := [4320050516, 3207785649, 1160724147, 3289800103, 3119498715, 4483854696, 700123104, 4201413217, 1]
  f := [169885866, 92974458, 95082057, 185752842, 132937608, 123179352, 127922333, 174592592, 231029117, 1]
  g := [3268683392, 1788871974, 1829423169, 3573971412, 2557781640, 2370028242, 2461285412, 3359242988, 4445108079, 1]
  h := [243694862, 1]
  a := [3087570720, 471368499, 3928101824, 2244979236, 954139222, 907494725, 2209578371, 1330853390, 4046130808]
  b := [2734834626, 1092002594, 3555794479, 3543963472, 3070603230, 581828343, 1482356440, 1778609378, 642672133]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 173, 4688802941]
  exp := ![2, 1, 1]
  pdgood := [2, 173, 4688802941]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp173.out
    exact hp4688802941.out
  a := [-6069300230672, -48280406015675, 338724296653540, -32635318331264, -654235502255434, 30979744611892, 324519609478924, 9227785855540, -38786912481030]
  b := [-4446974413086, 24493510411287, 5087643653289, -102402842894418, 13126174692562, 114032460525257, -5722291070694, -40985081693719, -922778585554, 3878691248103]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 173 T_ofList CD173
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4688802941 T_ofList CD4688802941

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

end VoightMaximalOrderD10R620

end TraceEuclidean
