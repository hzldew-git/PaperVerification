import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk179
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

namespace VoightMaximalOrderD10R150

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2681371403125, [1, -5, -5, 32, 2, -48, 11, 22, -7, -3, 1], 1⟩
local notation "l" => [1, -5, -5, 32, 2, -48, 11, 22, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -32, -2, 48, -11, -22, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], ![-3, 14, 20, -91, -38, 142, 15, -77, -1, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], ![-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], ![-16, 77, 94, -492, -123, 730, -34, -337, 35, 47]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], ![-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], ![-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], ![-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], ![-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], ![-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], ![-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], ![-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], ![-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], ![-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], ![-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], ![-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520], ![-520, 2424, 3433, -15541, -6360, 23198, 2142, -11243, -19, 1724]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], ![-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], ![-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], ![-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], ![-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520], ![-520, 2424, 3433, -15541, -6360, 23198, 2142, -11243, -19, 1724], ![-1724, 8100, 11044, -51735, -18989, 76392, 4234, -35786, 825, 5153]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], ![-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], ![-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], ![-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], ![-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520], ![-520, 2424, 3433, -15541, -6360, 23198, 2142, -11243, -19, 1724], ![-1724, 8100, 11044, -51735, -18989, 76392, 4234, -35786, 825, 5153], ![-5153, 24041, 33865, -153852, -62041, 228355, 19709, -109132, 285, 16284]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], ![-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], ![-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], ![-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], ![-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520], ![-520, 2424, 3433, -15541, -6360, 23198, 2142, -11243, -19, 1724], ![-1724, 8100, 11044, -51735, -18989, 76392, 4234, -35786, 825, 5153], ![-5153, 24041, 33865, -153852, -62041, 228355, 19709, -109132, 285, 16284], ![-16284, 76267, 105461, -487223, -186420, 719591, 49231, -338539, 4856, 49137]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-176, -47, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-176, -47, -16, -3, -1], [-520, -176, -47, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-176, -47, -16, -3, -1], [-520, -176, -47, -16, -3, -1], [-1724, -520, -176, -47, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-176, -47, -16, -3, -1], [-520, -176, -47, -16, -3, -1], [-1724, -520, -176, -47, -16, -3, -1], [-5153, -1724, -520, -176, -47, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-176, -47, -16, -3, -1], [-520, -176, -47, -16, -3, -1], [-1724, -520, -176, -47, -16, -3, -1], [-5153, -1724, -520, -176, -47, -16, -3, -1], [-16284, -5153, -1724, -520, -176, -47, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -32, -2, 48, -11, -22, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], [-3, 14, 20, -91, -38, 142, 15, -77, -1, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], [-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], [-16, 77, 94, -492, -123, 730, -34, -337, 35, 47]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], [-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], [-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], [-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], [-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], [-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], [-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], [-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], [-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], [-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], [-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], [-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520], [-520, 2424, 3433, -15541, -6360, 23198, 2142, -11243, -19, 1724]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], [-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], [-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], [-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], [-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520], [-520, 2424, 3433, -15541, -6360, 23198, 2142, -11243, -19, 1724], [-1724, 8100, 11044, -51735, -18989, 76392, 4234, -35786, 825, 5153]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], [-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], [-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], [-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], [-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520], [-520, 2424, 3433, -15541, -6360, 23198, 2142, -11243, -19, 1724], [-1724, 8100, 11044, -51735, -18989, 76392, 4234, -35786, 825, 5153], [-5153, 24041, 33865, -153852, -62041, 228355, 19709, -109132, 285, 16284]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -32, -2, 48, -11, -22, 7, 3], [-3, 14, 20, -91, -38, 142, 15, -77, -1, 16], [-16, 77, 94, -492, -123, 730, -34, -337, 35, 47], [-47, 219, 312, -1410, -586, 2133, 213, -1068, -8, 176], [-176, 833, 1099, -5320, -1762, 7862, 197, -3659, 164, 520], [-520, 2424, 3433, -15541, -6360, 23198, 2142, -11243, -19, 1724], [-1724, 8100, 11044, -51735, -18989, 76392, 4234, -35786, 825, 5153], [-5153, 24041, 33865, -153852, -62041, 228355, 19709, -109132, 285, 16284], [-16284, 76267, 105461, -487223, -186420, 719591, 49231, -338539, 4856, 49137]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp858038849 : Fact (Nat.Prime 858038849) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 3]
  b' := [4, 1, 0, 2, 3]
  k := [1]
  f := [0, 1, 1, -6, 0, 10, -2, -4, 2, 1]
  g := [1, 0, 0, 1, 1, 1]
  h := [1, 0, 0, 1, 1, 1]
  a := [1, 2, 3, 1, 3]
  b := [1, 4, 2, 0, 3, 2, 4, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD858038849 : CertificateDedekindCriterionLists l 858038849 where
  n := 2
  a' := [487558241, 268556103, 458982468, 157528553, 832584387, 666398239, 659231214, 702285175]
  b' := [184162758, 258913513, 134106459, 261512520, 52264181, 11674549, 70072838, 16793175, 684669513]
  k := [563739613, 103998219, 825841522, 450685567, 342254623, 82446999, 781592888, 832436067, 1]
  f := [38563043, 400545973, 64289724, 73979692, 249922738, 116420572, 384778300, 361654525, 214318723, 1]
  g := [74891422, 777880975, 124853964, 143672384, 485362870, 226094765, 747259339, 702351772, 416218032, 1]
  h := [441820814, 1]
  a := [420854708, 622799359, 212888621, 679815377, 473004224, 563924334, 75825538, 544203544, 208096408]
  b := [255118145, 754015053, 153386435, 507082091, 729134854, 794397030, 647206300, 375762533, 649942441]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 858038849]
  exp := ![1, 1]
  pdgood := [5, 858038849]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp858038849.out
  a := [-101746892220, -313464682810, 1629096611083, 1420332074510, -3645905952800, -1334454934948, 2053886758648, 353083928410, -278966635500]
  b := [-21207417293, 81468790244, 170910904733, -494298528029, -407090081639, 642951527134, 243885837696, -256447784458, -43677391906, 27896663550]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 858038849 T_ofList CD858038849

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

end VoightMaximalOrderD10R150

namespace VoightMaximalOrderD10R151

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2711793878125, [1, -4, -12, 29, 27, -63, 6, 26, -7, -3, 1], 1⟩
local notation "l" => [1, -4, -12, 29, 27, -63, 6, 26, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -29, -27, 63, -6, -26, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], ![-3, 11, 40, -75, -110, 162, 45, -84, -5, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], ![-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], ![-16, 61, 203, -424, -507, 898, 66, -371, 28, 43]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], ![-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], ![-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], ![-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], ![-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], ![-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], ![-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], ![-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], ![-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], ![-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], ![-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], ![-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401], ![-401, 1447, 5397, -9589, -14803, 19980, 5900, -9166, -635, 1250]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], ![-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], ![-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], ![-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], ![-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401], ![-401, 1447, 5397, -9589, -14803, 19980, 5900, -9166, -635, 1250], ![-1250, 4599, 16447, -30853, -43339, 63947, 12480, -26600, -416, 3115]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], ![-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], ![-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], ![-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], ![-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401], ![-401, 1447, 5397, -9589, -14803, 19980, 5900, -9166, -635, 1250], ![-1250, 4599, 16447, -30853, -43339, 63947, 12480, -26600, -416, 3115], ![-3115, 11210, 41979, -73888, -114958, 152906, 45257, -68510, -4795, 8929]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], ![-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], ![-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], ![-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], ![-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401], ![-401, 1447, 5397, -9589, -14803, 19980, 5900, -9166, -635, 1250], ![-1250, 4599, 16447, -30853, -43339, 63947, 12480, -26600, -416, 3115], ![-3115, 11210, 41979, -73888, -114958, 152906, 45257, -68510, -4795, 8929], ![-8929, 32601, 118358, -216962, -314971, 447569, 99332, -186897, -6007, 21992]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1], [-401, -157, -43, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1], [-401, -157, -43, -16, -3, -1], [-1250, -401, -157, -43, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1], [-401, -157, -43, -16, -3, -1], [-1250, -401, -157, -43, -16, -3, -1], [-3115, -1250, -401, -157, -43, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1], [-401, -157, -43, -16, -3, -1], [-1250, -401, -157, -43, -16, -3, -1], [-3115, -1250, -401, -157, -43, -16, -3, -1], [-8929, -3115, -1250, -401, -157, -43, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -29, -27, 63, -6, -26, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], [-3, 11, 40, -75, -110, 162, 45, -84, -5, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], [-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], [-16, 61, 203, -424, -507, 898, 66, -371, 28, 43]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], [-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], [-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], [-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], [-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], [-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], [-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], [-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], [-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], [-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], [-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], [-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401], [-401, 1447, 5397, -9589, -14803, 19980, 5900, -9166, -635, 1250]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], [-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], [-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], [-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], [-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401], [-401, 1447, 5397, -9589, -14803, 19980, 5900, -9166, -635, 1250], [-1250, 4599, 16447, -30853, -43339, 63947, 12480, -26600, -416, 3115]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], [-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], [-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], [-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], [-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401], [-401, 1447, 5397, -9589, -14803, 19980, 5900, -9166, -635, 1250], [-1250, 4599, 16447, -30853, -43339, 63947, 12480, -26600, -416, 3115], [-3115, 11210, 41979, -73888, -114958, 152906, 45257, -68510, -4795, 8929]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -29, -27, 63, -6, -26, 7, 3], [-3, 11, 40, -75, -110, 162, 45, -84, -5, 16], [-16, 61, 203, -424, -507, 898, 66, -371, 28, 43], [-43, 156, 577, -1044, -1585, 2202, 640, -1052, -70, 157], [-157, 585, 2040, -3976, -5283, 8306, 1260, -3442, 47, 401], [-401, 1447, 5397, -9589, -14803, 19980, 5900, -9166, -635, 1250], [-1250, 4599, 16447, -30853, -43339, 63947, 12480, -26600, -416, 3115], [-3115, 11210, 41979, -73888, -114958, 152906, 45257, -68510, -4795, 8929], [-8929, 32601, 118358, -216962, -314971, 447569, 99332, -186897, -6007, 21992]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp421 : Fact (Nat.Prime 421) := fact_iff.2 (by norm_num)
instance hp66491 : Fact (Nat.Prime 66491) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 3, 2]
  b' := [3, 3, 3, 1, 2]
  k := [1]
  f := [0, 2, 5, -3, -3, 15, 1, -4, 2, 1]
  g := [1, 3, 2, 1, 1, 1]
  h := [1, 3, 2, 1, 1, 1]
  a := [3, 4, 0, 0, 4]
  b := [1, 1, 2, 0, 0, 0, 4, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [13, 19, 27, 22, 30, 6, 9, 10]
  b' := [19, 26, 15, 11, 17, 29, 2, 25, 23]
  k := [7, 19, 30, 19, 18, 3, 7, 22, 1]
  f := [2, 1, 2, 2, 1, 5, 3, 1, 3, 1]
  g := [21, 2, 16, 25, 11, 27, 24, 11, 25, 1]
  h := [3, 1]
  a := [17, 9, 19, 25, 22, 3, 8, 19, 22]
  b := [25, 24, 25, 25, 1, 13, 0, 0, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD421 : CertificateDedekindCriterionLists l 421 where
  n := 2
  a' := [113, 154, 380, 278, 146, 232, 73, 188]
  b' := [101, 150, 261, 325, 347, 83, 61, 238, 213]
  k := [336, 417, 74, 387, 321, 302, 23, 91, 1]
  f := [183, 92, 273, 364, 32, 18, 56, 335, 40, 1]
  g := [206, 103, 307, 409, 35, 20, 63, 377, 44, 1]
  h := [374, 1]
  a := [77, 108, 135, 378, 27, 218, 107, 128, 176]
  b := [418, 331, 141, 175, 380, 41, 397, 155, 245]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD66491 : CertificateDedekindCriterionLists l 66491 where
  n := 2
  a' := [25101, 44077, 51061, 63970, 6652, 22081, 25840, 31427]
  b' := [31843, 4312, 41107, 18561, 18662, 33618, 31117, 38931, 3896]
  k := [36673, 3621, 8944, 30086, 51548, 44506, 37073, 30199, 1]
  f := [3529, 8930, 38636, 10250, 10724, 44418, 45874, 49267, 11670, 1]
  g := [4566, 11554, 49989, 13261, 13875, 57470, 59353, 63743, 15098, 1]
  h := [51390, 1]
  a := [9343, 59737, 43191, 60037, 25848, 25783, 17456, 29682, 13469]
  b := [43368, 61419, 21310, 30857, 31378, 52700, 36864, 63787, 53022]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 31, 421, 66491]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 31, 421, 66491]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp31.out
    exact hp421.out
    exact hp66491.out
  a := [3262030313, -19053359480, -111586774117, 258768704702, -28813400401, -168290543270, 55147630504, 26093887088, -10096729440]
  b := [-269209973, -6410110345, 13975920169, 26544658213, -54494263612, 5478426489, 24404712249, -6963323644, -2912290592, 1009672944]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 421 T_ofList CD421
    exact satisfiesDedekindCriterion_of_certificate_lists T l 66491 T_ofList CD66491

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

end VoightMaximalOrderD10R151

namespace VoightMaximalOrderD10R154

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2743063777817, [1, 9, 18, -15, -45, 7, 34, -1, -10, 0, 1], 1⟩
local notation "l" => [1, 9, 18, -15, -45, 7, 34, -1, -10, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -18, 15, 45, -7, -34, 1, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], ![0, -1, -9, -18, 15, 45, -7, -34, 1, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], ![0, -1, -9, -18, 15, 45, -7, -34, 1, 10], ![-10, -90, -181, 141, 432, -55, -295, 3, 66, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], ![0, -1, -9, -18, 15, 45, -7, -34, 1, 10], ![-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], ![-1, -19, -108, -166, 186, 425, -89, -294, 13, 66]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], ![0, -1, -9, -18, 15, 45, -7, -34, 1, 10], ![-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], ![-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], ![-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], ![0, -1, -9, -18, 15, 45, -7, -34, 1, 10], ![-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], ![-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], ![-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13], ![-13, -183, -829, -1012, 1467, 2713, -718, -1806, 107, 366]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], ![0, -1, -9, -18, 15, 45, -7, -34, 1, 10], ![-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], ![-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], ![-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13], ![-13, -183, -829, -1012, 1467, 2713, -718, -1806, 107, 366], ![-366, -3307, -6771, 4661, 15458, -1095, -9731, -352, 1854, 107]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], ![0, -1, -9, -18, 15, 45, -7, -34, 1, 10], ![-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], ![-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], ![-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13], ![-13, -183, -829, -1012, 1467, 2713, -718, -1806, 107, 366], ![-366, -3307, -6771, 4661, 15458, -1095, -9731, -352, 1854, 107], ![-107, -1329, -5233, -5166, 9476, 14709, -4733, -9624, 718, 1854]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], ![0, -1, -9, -18, 15, 45, -7, -34, 1, 10], ![-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], ![-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], ![-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13], ![-13, -183, -829, -1012, 1467, 2713, -718, -1806, 107, 366], ![-366, -3307, -6771, 4661, 15458, -1095, -9731, -352, 1854, 107], ![-107, -1329, -5233, -5166, 9476, 14709, -4733, -9624, 718, 1854], ![-1854, -16793, -34701, 22577, 78264, -3502, -48327, -2879, 8916, 718]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1], [-13, -66, -1, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1], [-13, -66, -1, -10, 0, -1], [-366, -13, -66, -1, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1], [-13, -66, -1, -10, 0, -1], [-366, -13, -66, -1, -10, 0, -1], [-107, -366, -13, -66, -1, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1], [-13, -66, -1, -10, 0, -1], [-366, -13, -66, -1, -10, 0, -1], [-107, -366, -13, -66, -1, -10, 0, -1], [-1854, -107, -366, -13, -66, -1, -10, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -18, 15, 45, -7, -34, 1, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], [0, -1, -9, -18, 15, 45, -7, -34, 1, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], [0, -1, -9, -18, 15, 45, -7, -34, 1, 10], [-10, -90, -181, 141, 432, -55, -295, 3, 66, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], [0, -1, -9, -18, 15, 45, -7, -34, 1, 10], [-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], [-1, -19, -108, -166, 186, 425, -89, -294, 13, 66]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], [0, -1, -9, -18, 15, 45, -7, -34, 1, 10], [-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], [-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], [-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], [0, -1, -9, -18, 15, 45, -7, -34, 1, 10], [-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], [-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], [-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13], [-13, -183, -829, -1012, 1467, 2713, -718, -1806, 107, 366]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], [0, -1, -9, -18, 15, 45, -7, -34, 1, 10], [-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], [-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], [-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13], [-13, -183, -829, -1012, 1467, 2713, -718, -1806, 107, 366], [-366, -3307, -6771, 4661, 15458, -1095, -9731, -352, 1854, 107]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], [0, -1, -9, -18, 15, 45, -7, -34, 1, 10], [-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], [-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], [-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13], [-13, -183, -829, -1012, 1467, 2713, -718, -1806, 107, 366], [-366, -3307, -6771, 4661, 15458, -1095, -9731, -352, 1854, 107], [-107, -1329, -5233, -5166, 9476, 14709, -4733, -9624, 718, 1854]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -18, 15, 45, -7, -34, 1, 10, 0], [0, -1, -9, -18, 15, 45, -7, -34, 1, 10], [-10, -90, -181, 141, 432, -55, -295, 3, 66, 1], [-1, -19, -108, -166, 186, 425, -89, -294, 13, 66], [-66, -595, -1207, 882, 2804, -276, -1819, -23, 366, 13], [-13, -183, -829, -1012, 1467, 2713, -718, -1806, 107, 366], [-366, -3307, -6771, 4661, 15458, -1095, -9731, -352, 1854, 107], [-107, -1329, -5233, -5166, 9476, 14709, -4733, -9624, 718, 1854], [-1854, -16793, -34701, 22577, 78264, -3502, -48327, -2879, 8916, 718]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp2293 : Fact (Nat.Prime 2293) := fact_iff.2 (by norm_num)
instance hp9886589 : Fact (Nat.Prime 9886589) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [2, 9, 5, 0, 3, 7]
  b' := [1, 6, 6, 9, 7, 6, 6]
  k := [4, 7, 7, 5, 5, 6, 1]
  f := [1, 5, 6, 7, 8, 2, 2, 5, 4, 1]
  g := [2, 8, 3, 5, 0, 4, 4, 3, 1]
  h := [6, 8, 1]
  a := [1, 5, 10, 8, 10, 4, 10, 6]
  b := [0, 6, 5, 6, 9, 6, 9, 6, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2293 : CertificateDedekindCriterionLists l 2293 where
  n := 2
  a' := [1296, 380, 559, 2042, 2236, 2223, 200, 1286]
  b' := [1753, 1756, 683, 1949, 1011, 1564, 174, 12, 1131]
  k := [199, 81, 1517, 1760, 1488, 1594, 1511, 552, 1]
  f := [95, 680, 887, 1648, 1337, 1584, 1658, 438, 243, 1]
  g := [108, 773, 1008, 1873, 1519, 1800, 1884, 497, 276, 1]
  h := [2017, 1]
  a := [901, 2185, 1500, 1868, 248, 322, 1888, 2012, 1644]
  b := [1458, 80, 519, 423, 506, 1232, 732, 1794, 649]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9886589 : CertificateDedekindCriterionLists l 9886589 where
  n := 2
  a' := [2040846, 6210859, 2439076, 7817971, 8118668, 3539501, 9262855, 4992271]
  b' := [8780923, 6026022, 8246077, 6540343, 8536860, 915805, 9585308, 2949983, 1642323]
  k := [6488895, 1123846, 1898972, 9386433, 648779, 7938745, 4943849, 9134605, 1]
  f := [365411, 33988, 369644, 2039, 129426, 214016, 334971, 62673, 361693, 1]
  g := [9608365, 893678, 9719668, 53589, 3403215, 5627473, 8807940, 1647943, 9510597, 1]
  h := [375992, 1]
  a := [4900220, 8639224, 1039953, 4381449, 8767783, 1028844, 8043016, 2079374, 4028750]
  b := [540498, 3162838, 2255455, 209164, 8515694, 1631861, 9755995, 7563221, 5857839]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![11, 2293, 9886589]
  exp := ![1, 1, 1]
  pdgood := [11, 2293, 9886589]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp2293.out
    exact hp9886589.out
  a := [-5655441096986, -831345508350, 29485382367069, 4383031027848, -34671434898784, -3070686416028, 13951457396440, 554499325600, -1777648958460]
  b := [656090059037, 3123452583988, -347285934786, -7607222119727, -554146294707, 5847434198904, 364639037969, -1750675531336, -55449932560, 177764895846]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2293 T_ofList CD2293
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9886589 T_ofList CD9886589

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

end VoightMaximalOrderD10R154

namespace VoightMaximalOrderD10R159

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2803275878125, [1, 2, -35, 65, 2, -73, 26, 22, -10, -2, 1], 1⟩
local notation "l" => [1, 2, -35, 65, 2, -73, 26, 22, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 35, -65, -2, 73, -26, -22, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], ![-2, -5, 68, -95, -69, 144, 21, -70, -2, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], ![-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], ![-14, -30, 485, -842, -123, 953, -220, -287, 70, 26]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], ![-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], ![-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], ![-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], ![-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], ![-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], ![-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], ![-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], ![-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], ![-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], ![-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], ![-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217], ![-217, -556, 7325, -9901, -7484, 14392, 2370, -6171, -237, 862]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], ![-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], ![-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], ![-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], ![-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217], ![-217, -556, 7325, -9901, -7484, 14392, 2370, -6171, -237, 862], ![-862, -1941, 29614, -48705, -11625, 55442, -8020, -16594, 2449, 1487]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], ![-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], ![-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], ![-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], ![-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217], ![-217, -556, 7325, -9901, -7484, 14392, 2370, -6171, -237, 862], ![-862, -1941, 29614, -48705, -11625, 55442, -8020, -16594, 2449, 1487], ![-1487, -3836, 50104, -67041, -51679, 96926, 16780, -40734, -1724, 5423]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], ![-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], ![-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], ![-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], ![-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217], ![-217, -556, 7325, -9901, -7484, 14392, 2370, -6171, -237, 862], ![-862, -1941, 29614, -48705, -11625, 55442, -8020, -16594, 2449, 1487], ![-1487, -3836, 50104, -67041, -51679, 96926, 16780, -40734, -1724, 5423], ![-5423, -12333, 185969, -302391, -77887, 344200, -44072, -102526, 13496, 9122]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-122, -26, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-122, -26, -14, -2, -1], [-217, -122, -26, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-122, -26, -14, -2, -1], [-217, -122, -26, -14, -2, -1], [-862, -217, -122, -26, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-122, -26, -14, -2, -1], [-217, -122, -26, -14, -2, -1], [-862, -217, -122, -26, -14, -2, -1], [-1487, -862, -217, -122, -26, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-122, -26, -14, -2, -1], [-217, -122, -26, -14, -2, -1], [-862, -217, -122, -26, -14, -2, -1], [-1487, -862, -217, -122, -26, -14, -2, -1], [-5423, -1487, -862, -217, -122, -26, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 35, -65, -2, 73, -26, -22, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], [-2, -5, 68, -95, -69, 144, 21, -70, -2, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], [-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], [-14, -30, 485, -842, -123, 953, -220, -287, 70, 26]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], [-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], [-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], [-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], [-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], [-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], [-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], [-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], [-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], [-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], [-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], [-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217], [-217, -556, 7325, -9901, -7484, 14392, 2370, -6171, -237, 862]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], [-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], [-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], [-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], [-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217], [-217, -556, 7325, -9901, -7484, 14392, 2370, -6171, -237, 862], [-862, -1941, 29614, -48705, -11625, 55442, -8020, -16594, 2449, 1487]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], [-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], [-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], [-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], [-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217], [-217, -556, 7325, -9901, -7484, 14392, 2370, -6171, -237, 862], [-862, -1941, 29614, -48705, -11625, 55442, -8020, -16594, 2449, 1487], [-1487, -3836, 50104, -67041, -51679, 96926, 16780, -40734, -1724, 5423]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 35, -65, -2, 73, -26, -22, 10, 2], [-2, -5, 68, -95, -69, 144, 21, -70, -2, 14], [-14, -30, 485, -842, -123, 953, -220, -287, 70, 26], [-26, -66, 880, -1205, -894, 1775, 277, -792, -27, 122], [-122, -270, 4204, -7050, -1449, 8012, -1397, -2407, 428, 217], [-217, -556, 7325, -9901, -7484, 14392, 2370, -6171, -237, 862], [-862, -1941, 29614, -48705, -11625, 55442, -8020, -16594, 2449, 1487], [-1487, -3836, 50104, -67041, -51679, 96926, 16780, -40734, -1724, 5423], [-5423, -12333, 185969, -302391, -77887, 344200, -44072, -102526, 13496, 9122]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp897048281 : Fact (Nat.Prime 897048281) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 1, 3]
  b' := [4, 3, 3, 0, 2]
  k := [1]
  f := [3, 6, 15, -5, 11, 25, 2, 0, 6, 2]
  g := [4, 4, 3, 2, 4, 1]
  h := [4, 4, 3, 2, 4, 1]
  a := [1, 2, 2, 2, 3]
  b := [2, 0, 4, 3, 4, 0, 3, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD897048281 : CertificateDedekindCriterionLists l 897048281 where
  n := 2
  a' := [110082166, 71204636, 530702414, 247127290, 50928842, 37342388, 546116673, 222924316]
  b' := [519470169, 662626785, 359902829, 181875654, 814978614, 322791541, 429765232, 681761165, 174574694]
  k := [410471018, 426808762, 254752765, 277008936, 631276947, 540373591, 645524196, 718811226, 1]
  f := [71208344, 434045024, 359646482, 360726039, 182738835, 344315530, 95140797, 343787001, 215408464, 1]
  g := [118809995, 724197253, 600064462, 601865686, 304896853, 574485012, 158740913, 573603170, 359405612, 1]
  h := [537642667, 1]
  a := [63418303, 813041658, 199054175, 17604080, 681903089, 646322233, 814813712, 136715739, 62985758]
  b := [684164921, 315225328, 569893939, 114533323, 432556372, 370676165, 200788141, 369113084, 834062523]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 897048281]
  exp := ![1, 1]
  pdgood := [5, 897048281]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp897048281.out
  a := [47046976431, -1432950816022, 2106761469432, 3118947521022, -3360320485918, -1376287709918, 1335661162024, 163549688328, -152370891560]
  b := [-21280867513, -75401931375, 638709153241, -480269101786, -712318617849, 549768034508, 214398011723, -166254652844, -19402386664, 15237089156]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 897048281 T_ofList CD897048281

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

end VoightMaximalOrderD10R159

end TraceEuclidean
