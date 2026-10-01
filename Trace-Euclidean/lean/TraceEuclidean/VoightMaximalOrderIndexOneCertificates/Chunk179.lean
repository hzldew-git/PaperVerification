import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk175
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

namespace VoightMaximalOrderD10R125

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2349838017113, [1, 0, -16, 12, 36, -29, -23, 22, 2, -5, 1], 1⟩
local notation "l" => [1, 0, -16, 12, 36, -29, -23, 22, 2, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -12, -36, 29, 23, -22, -2, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], ![-5, -1, 80, -44, -192, 109, 144, -87, -32, 23]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], ![-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], ![-23, -5, 367, -196, -872, 475, 638, -362, -133, 83]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], ![-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], ![-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], ![-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], ![-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], ![-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], ![-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], ![-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], ![-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], ![-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], ![-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], ![-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882], ![-882, -282, 14029, -6095, -33813, 14797, 25280, -11383, -5584, 2658]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], ![-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], ![-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], ![-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], ![-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882], ![-882, -282, 14029, -6095, -33813, 14797, 25280, -11383, -5584, 2658], ![-2658, -882, 42246, -17867, -101783, 43269, 75931, -33196, -16699, 7706]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], ![-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], ![-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], ![-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], ![-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882], ![-882, -282, 14029, -6095, -33813, 14797, 25280, -11383, -5584, 2658], ![-2658, -882, 42246, -17867, -101783, 43269, 75931, -33196, -16699, 7706], ![-7706, -2658, 122414, -50226, -295283, 121691, 220507, -93601, -48608, 21831]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], ![-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], ![-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], ![-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], ![-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882], ![-882, -282, 14029, -6095, -33813, 14797, 25280, -11383, -5584, 2658], ![-2658, -882, 42246, -17867, -101783, 43269, 75931, -33196, -16699, 7706], ![-7706, -2658, 122414, -50226, -295283, 121691, 220507, -93601, -48608, 21831], ![-21831, -7706, 346638, -139558, -836142, 337816, 623804, -259775, -137263, 60547]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-23, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-23, -5, -1], [-83, -23, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-23, -5, -1], [-83, -23, -5, -1], [-282, -83, -23, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-23, -5, -1], [-83, -23, -5, -1], [-282, -83, -23, -5, -1], [-882, -282, -83, -23, -5, -1]], ![[], [], [], [-1], [-5, -1], [-23, -5, -1], [-83, -23, -5, -1], [-282, -83, -23, -5, -1], [-882, -282, -83, -23, -5, -1], [-2658, -882, -282, -83, -23, -5, -1]], ![[], [], [-1], [-5, -1], [-23, -5, -1], [-83, -23, -5, -1], [-282, -83, -23, -5, -1], [-882, -282, -83, -23, -5, -1], [-2658, -882, -282, -83, -23, -5, -1], [-7706, -2658, -882, -282, -83, -23, -5, -1]], ![[], [-1], [-5, -1], [-23, -5, -1], [-83, -23, -5, -1], [-282, -83, -23, -5, -1], [-882, -282, -83, -23, -5, -1], [-2658, -882, -282, -83, -23, -5, -1], [-7706, -2658, -882, -282, -83, -23, -5, -1], [-21831, -7706, -2658, -882, -282, -83, -23, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -12, -36, 29, 23, -22, -2, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], [-5, -1, 80, -44, -192, 109, 144, -87, -32, 23]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], [-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], [-23, -5, 367, -196, -872, 475, 638, -362, -133, 83]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], [-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], [-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], [-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], [-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], [-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], [-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], [-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], [-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], [-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], [-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], [-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882], [-882, -282, 14029, -6095, -33813, 14797, 25280, -11383, -5584, 2658]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], [-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], [-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], [-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], [-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882], [-882, -282, 14029, -6095, -33813, 14797, 25280, -11383, -5584, 2658], [-2658, -882, 42246, -17867, -101783, 43269, 75931, -33196, -16699, 7706]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], [-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], [-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], [-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], [-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882], [-882, -282, 14029, -6095, -33813, 14797, 25280, -11383, -5584, 2658], [-2658, -882, 42246, -17867, -101783, 43269, 75931, -33196, -16699, 7706], [-7706, -2658, 122414, -50226, -295283, 121691, 220507, -93601, -48608, 21831]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -12, -36, 29, 23, -22, -2, 5], [-5, -1, 80, -44, -192, 109, 144, -87, -32, 23], [-23, -5, 367, -196, -872, 475, 638, -362, -133, 83], [-83, -23, 1323, -629, -3184, 1535, 2384, -1188, -528, 282], [-282, -83, 4489, -2061, -10781, 4994, 8021, -3820, -1752, 882], [-882, -282, 14029, -6095, -33813, 14797, 25280, -11383, -5584, 2658], [-2658, -882, 42246, -17867, -101783, 43269, 75931, -33196, -16699, 7706], [-7706, -2658, 122414, -50226, -295283, 121691, 220507, -93601, -48608, 21831], [-21831, -7706, 346638, -139558, -836142, 337816, 623804, -259775, -137263, 60547]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp83 : Fact (Nat.Prime 83) := fact_iff.2 (by norm_num)
instance hp353 : Fact (Nat.Prime 353) := fact_iff.2 (by norm_num)
instance hp983 : Fact (Nat.Prime 983) := fact_iff.2 (by norm_num)

def CD83 : CertificateDedekindCriterionLists l 83 where
  n := 2
  a' := [62, 47, 46, 39, 82, 11, 24]
  b' := [30, 25, 82, 24, 74, 18, 52, 80]
  k := [61, 53, 8, 43, 64, 80, 1]
  f := [1, 17, 66, 65, 21, 84, 48, 80, 79, 2]
  g := [12, 61, 64, 14, 81, 41, 74, 79, 1]
  h := [7, 82, 1]
  a := [43, 5, 8, 70, 41, 82, 6, 82]
  b := [38, 36, 41, 80, 10, 28, 9, 75, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD353 : CertificateDedekindCriterionLists l 353 where
  n := 2
  a' := [215, 33, 105, 158, 139, 112, 256, 179]
  b' := [157, 64, 33, 143, 282, 110, 132, 158, 137]
  k := [4, 16, 337, 273, 241, 109, 86, 349, 1]
  f := [175, 175, 13, 12, 164, 6, 33, 44, 86, 1]
  g := [351, 349, 24, 24, 329, 10, 66, 88, 172, 1]
  h := [176, 1]
  a := [34, 22, 337, 8, 232, 74, 118, 220, 135]
  b := [327, 10, 61, 39, 192, 257, 33, 94, 218]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD983 : CertificateDedekindCriterionLists l 983 where
  n := 2
  a' := [129, 399, 946, 319, 182, 180, 923]
  b' := [279, 490, 811, 779, 342, 725, 711, 499]
  k := [67, 53, 546, 767, 602, 980, 1]
  f := [153, 812, 150, 465, 356, 1004, 736, 980, 979, 2]
  g := [800, 67, 430, 185, 893, 584, 793, 979, 1]
  h := [188, 982, 1]
  a := [563, 940, 886, 390, 110, 249, 683, 186]
  b := [981, 200, 618, 884, 185, 187, 346, 839, 611]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![83, 353, 983]
  exp := ![1, 1, 1]
  pdgood := [83, 353, 983]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp83.out
    exact hp353.out
    exact hp983.out
  a := [28800917, -267624704, -363109808, 891335944, 418828728, -867055240, 5117080, 243344000, -60836000]
  b := [-8363272, -35156321, 95281359, 113569230, -184208060, -78220584, 126352688, 400832, -27376200, 6083600]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 83 T_ofList CD83
    exact satisfiesDedekindCriterion_of_certificate_lists T l 353 T_ofList CD353
    exact satisfiesDedekindCriterion_of_certificate_lists T l 983 T_ofList CD983

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

end VoightMaximalOrderD10R125

namespace VoightMaximalOrderD10R127

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2368117028125, [1, -4, -6, 32, -2, -47, 12, 22, -7, -3, 1], 1⟩
local notation "l" => [1, -4, -6, 32, -2, -47, 12, 22, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -32, 2, 47, -12, -22, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], ![-3, 11, 22, -90, -26, 143, 11, -78, -1, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], ![-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], ![-16, 61, 107, -490, -58, 726, -49, -341, 34, 47]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], ![-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], ![-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], ![-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], ![-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], ![-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], ![-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], ![-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], ![-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], ![-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], ![-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], ![-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513], ![-513, 1877, 3731, -15194, -4231, 23064, 1673, -11235, -97, 1681]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], ![-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], ![-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], ![-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], ![-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513], ![-513, 1877, 3731, -15194, -4231, 23064, 1673, -11235, -97, 1681], ![-1681, 6211, 11963, -50061, -11832, 74776, 2892, -35309, 532, 4946]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], ![-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], ![-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], ![-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], ![-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513], ![-513, 1877, 3731, -15194, -4231, 23064, 1673, -11235, -97, 1681], ![-1681, 6211, 11963, -50061, -11832, 74776, 2892, -35309, 532, 4946], ![-4946, 18103, 35887, -146309, -40169, 220630, 15424, -105920, -687, 15370]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], ![-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], ![-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], ![-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], ![-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513], ![-513, 1877, 3731, -15194, -4231, 23064, 1673, -11235, -97, 1681], ![-1681, 6211, 11963, -50061, -11832, 74776, 2892, -35309, 532, 4946], ![-4946, 18103, 35887, -146309, -40169, 220630, 15424, -105920, -687, 15370], ![-15370, 56534, 110323, -455953, -115569, 682221, 36190, -322716, 1670, 45423]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-175, -47, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-175, -47, -16, -3, -1], [-513, -175, -47, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-175, -47, -16, -3, -1], [-513, -175, -47, -16, -3, -1], [-1681, -513, -175, -47, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-175, -47, -16, -3, -1], [-513, -175, -47, -16, -3, -1], [-1681, -513, -175, -47, -16, -3, -1], [-4946, -1681, -513, -175, -47, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-175, -47, -16, -3, -1], [-513, -175, -47, -16, -3, -1], [-1681, -513, -175, -47, -16, -3, -1], [-4946, -1681, -513, -175, -47, -16, -3, -1], [-15370, -4946, -1681, -513, -175, -47, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -32, 2, 47, -12, -22, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], [-3, 11, 22, -90, -26, 143, 11, -78, -1, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], [-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], [-16, 61, 107, -490, -58, 726, -49, -341, 34, 47]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], [-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], [-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], [-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], [-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], [-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], [-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], [-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], [-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], [-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], [-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], [-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513], [-513, 1877, 3731, -15194, -4231, 23064, 1673, -11235, -97, 1681]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], [-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], [-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], [-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], [-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513], [-513, 1877, 3731, -15194, -4231, 23064, 1673, -11235, -97, 1681], [-1681, 6211, 11963, -50061, -11832, 74776, 2892, -35309, 532, 4946]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], [-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], [-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], [-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], [-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513], [-513, 1877, 3731, -15194, -4231, 23064, 1673, -11235, -97, 1681], [-1681, 6211, 11963, -50061, -11832, 74776, 2892, -35309, 532, 4946], [-4946, 18103, 35887, -146309, -40169, 220630, 15424, -105920, -687, 15370]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -32, 2, 47, -12, -22, 7, 3], [-3, 11, 22, -90, -26, 143, 11, -78, -1, 16], [-16, 61, 107, -490, -58, 726, -49, -341, 34, 47], [-47, 172, 343, -1397, -396, 2151, 162, -1083, -12, 175], [-175, 653, 1222, -5257, -1047, 7829, 51, -3688, 142, 513], [-513, 1877, 3731, -15194, -4231, 23064, 1673, -11235, -97, 1681], [-1681, 6211, 11963, -50061, -11832, 74776, 2892, -35309, 532, 4946], [-4946, 18103, 35887, -146309, -40169, 220630, 15424, -105920, -687, 15370], [-15370, 56534, 110323, -455953, -115569, 682221, 36190, -322716, 1670, 45423]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp400739 : Fact (Nat.Prime 400739) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 1]
  b' := [3, 1, 1, 1]
  k := [1]
  f := [0, 2, 3, -6, 2, 11, -1, -4, 2, 1]
  g := [1, 3, 0, 1, 1, 1]
  h := [1, 3, 0, 1, 1, 1]
  a := [3, 1, 2, 1, 2]
  b := [1, 1, 1, 2, 4, 0, 4, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [22, 26, 10, 0, 0, 2, 8, 23]
  b' := [9, 7, 29, 28, 26, 6, 0, 22, 25]
  k := [9, 3, 2, 1, 20, 6, 16, 17, 1]
  f := [2, 7, 10, 15, 13, 17, 1, 0, 5, 1]
  g := [3, 10, 14, 23, 18, 22, 1, 1, 7, 1]
  h := [21, 1]
  a := [0, 13, 8, 3, 16, 30, 0, 2, 4]
  b := [21, 4, 8, 19, 26, 21, 14, 6, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [18, 51, 45, 10, 35, 39, 33, 26]
  b' := [44, 3, 26, 47, 47, 35, 6, 7, 31]
  k := [25, 16, 41, 51, 1, 41, 48, 21, 1]
  f := [4, 13, 10, 31, 32, 48, 12, 32, 8, 1]
  g := [5, 16, 12, 39, 39, 58, 14, 40, 9, 1]
  h := [49, 1]
  a := [19, 33, 24, 56, 58, 28, 27, 32, 53]
  b := [46, 21, 21, 50, 55, 16, 13, 21, 8]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD400739 : CertificateDedekindCriterionLists l 400739 where
  n := 2
  a' := [221836, 15301, 221561, 322576, 124123, 232878, 324311, 1928]
  b' := [395586, 47823, 29035, 122759, 102468, 275576, 101601, 55029, 177892]
  k := [354901, 384482, 14248, 370039, 170420, 27954, 200637, 260065, 1]
  f := [207616, 12616, 186744, 200540, 27684, 204987, 73059, 47570, 87838, 1]
  g := [307345, 18675, 276447, 296869, 40981, 303453, 108152, 70420, 130031, 1]
  h := [270705, 1]
  a := [208459, 179544, 103456, 280150, 35064, 165950, 222357, 193292, 109356]
  b := [91438, 39761, 68948, 52228, 393339, 222409, 147596, 156309, 291383]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 31, 61, 400739]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 31, 61, 400739]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp31.out
    exact hp61.out
    exact hp400739.out
  a := [-269397515599, -1619768433468, 1737239602526, 4474002293588, -2800767977663, -3047895447762, 1543779439205, 549786130008, -239686031940]
  b := [-68296625711, 69345284365, 611019737339, -376445639554, -935955595148, 448769762799, 447510535140, -190854973079, -62169193959, 23968603194]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 400739 T_ofList CD400739

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

end VoightMaximalOrderD10R127

namespace VoightMaximalOrderD10R128

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2372267442176, [1, -4, -10, 24, 19, -38, -8, 22, -2, -4, 1], 1⟩
local notation "l" => [1, -4, -10, 24, 19, -38, -8, 22, -2, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -24, -19, 38, 8, -22, 2, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], ![-4, 15, 44, -86, -100, 133, 70, -80, -14, 18]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], ![-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], ![-18, 68, 195, -388, -428, 584, 277, -326, -44, 58]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], ![-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], ![-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], ![-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], ![-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], ![-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], ![-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], ![-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], ![-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], ![-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], ![-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], ![-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542], ![-542, 1980, 6114, -10914, -14162, 15827, 9990, -8644, -2004, 1545]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], ![-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], ![-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], ![-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], ![-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542], ![-542, 1980, 6114, -10914, -14162, 15827, 9990, -8644, -2004, 1545], ![-1545, 5638, 17430, -30966, -40269, 44548, 28187, -24000, -5554, 4176]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], ![-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], ![-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], ![-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], ![-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542], ![-542, 1980, 6114, -10914, -14162, 15827, 9990, -8644, -2004, 1545], ![-1545, 5638, 17430, -30966, -40269, 44548, 28187, -24000, -5554, 4176], ![-4176, 15159, 47398, -82794, -110310, 118419, 77956, -63685, -15648, 11150]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], ![-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], ![-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], ![-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], ![-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542], ![-542, 1980, 6114, -10914, -14162, 15827, 9990, -8644, -2004, 1545], ![-1545, 5638, 17430, -30966, -40269, 44548, 28187, -24000, -5554, 4176], ![-4176, 15159, 47398, -82794, -110310, 118419, 77956, -63685, -15648, 11150], ![-11150, 40424, 126659, -220202, -294644, 313390, 207619, -167344, -41385, 28952]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-18, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-188, -58, -18, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-188, -58, -18, -4, -1], [-542, -188, -58, -18, -4, -1]], ![[], [], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-188, -58, -18, -4, -1], [-542, -188, -58, -18, -4, -1], [-1545, -542, -188, -58, -18, -4, -1]], ![[], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-188, -58, -18, -4, -1], [-542, -188, -58, -18, -4, -1], [-1545, -542, -188, -58, -18, -4, -1], [-4176, -1545, -542, -188, -58, -18, -4, -1]], ![[], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-188, -58, -18, -4, -1], [-542, -188, -58, -18, -4, -1], [-1545, -542, -188, -58, -18, -4, -1], [-4176, -1545, -542, -188, -58, -18, -4, -1], [-11150, -4176, -1545, -542, -188, -58, -18, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -24, -19, 38, 8, -22, 2, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], [-4, 15, 44, -86, -100, 133, 70, -80, -14, 18]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], [-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], [-18, 68, 195, -388, -428, 584, 277, -326, -44, 58]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], [-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], [-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], [-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], [-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], [-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], [-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], [-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], [-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], [-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], [-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], [-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542], [-542, 1980, 6114, -10914, -14162, 15827, 9990, -8644, -2004, 1545]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], [-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], [-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], [-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], [-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542], [-542, 1980, 6114, -10914, -14162, 15827, 9990, -8644, -2004, 1545], [-1545, 5638, 17430, -30966, -40269, 44548, 28187, -24000, -5554, 4176]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], [-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], [-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], [-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], [-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542], [-542, 1980, 6114, -10914, -14162, 15827, 9990, -8644, -2004, 1545], [-1545, 5638, 17430, -30966, -40269, 44548, 28187, -24000, -5554, 4176], [-4176, 15159, 47398, -82794, -110310, 118419, 77956, -63685, -15648, 11150]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -24, -19, 38, 8, -22, 2, 4], [-4, 15, 44, -86, -100, 133, 70, -80, -14, 18], [-18, 68, 195, -388, -428, 584, 277, -326, -44, 58], [-58, 214, 648, -1197, -1490, 1776, 1048, -999, -210, 188], [-188, 694, 2094, -3864, -4769, 5654, 3280, -3088, -623, 542], [-542, 1980, 6114, -10914, -14162, 15827, 9990, -8644, -2004, 1545], [-1545, 5638, 17430, -30966, -40269, 44548, 28187, -24000, -5554, 4176], [-4176, 15159, 47398, -82794, -110310, 118419, 77956, -63685, -15648, 11150], [-11150, 40424, 126659, -220202, -294644, 313390, 207619, -167344, -41385, 28952]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp72395857 : Fact (Nat.Prime 72395857) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [1, 1, 0, 1]
  k := [1]
  f := [0, 2, 6, -12, -9, 20, 4, -10, 1, 2]
  g := [1, 0, 1, 0, 0, 1]
  h := [1, 0, 1, 0, 0, 1]
  a := [1, 1, 0, 0, 1]
  b := [1, 0, 1, 0, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD72395857 : CertificateDedekindCriterionLists l 72395857 where
  n := 2
  a' := [45136538, 2012659, 64254412, 4726241, 12346942, 30770067, 4646151, 970322]
  b' := [52934058, 35431412, 42079370, 42272056, 399977, 29145002, 10746413, 36164742, 40112107]
  k := [69525971, 6512773, 7134975, 21873503, 13045993, 64719227, 31830542, 57607529, 1]
  f := [5557249, 246607, 6359063, 5138016, 5956859, 2908423, 1489397, 2090611, 6638958, 1]
  g := [54410737, 2414509, 62261256, 50306040, 58323291, 28476211, 14582605, 20469062, 65001691, 1]
  h := [7394162, 1]
  a := [12243826, 6523942, 5411975, 22724309, 50450369, 54663594, 43851560, 59782426, 60635360]
  b := [50177587, 65504250, 70565390, 33646736, 17218087, 71732127, 54410010, 33864579, 11760497]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 72395857]
  exp := ![2, 1]
  pdgood := [2, 72395857]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp72395857.out
  a := [-3474548, -1840920664, -905959996, 6522222400, 434190004, -5932254552, 1067649710, 1456015794, -453399890]
  b := [-73264494, -90433148, 756521883, 315538503, -1409267964, -95237457, 873732597, -131949919, -163737575, 45339989]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 72395857 T_ofList CD72395857

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

end VoightMaximalOrderD10R128

namespace VoightMaximalOrderD10R129

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2383725278125, [1, 4, -5, -36, -27, 39, 42, -6, -12, 0, 1], 1⟩
local notation "l" => [1, 4, -5, -36, -27, 39, 42, -6, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 5, 36, 27, -39, -42, 6, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], ![0, -1, -4, 5, 36, 27, -39, -42, 6, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], ![0, -1, -4, 5, 36, 27, -39, -42, 6, 12], ![-12, -48, 59, 428, 329, -432, -477, 33, 102, 6]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], ![0, -1, -4, 5, 36, 27, -39, -42, 6, 12], ![-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], ![-6, -36, -18, 275, 590, 95, -684, -441, 105, 102]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], ![0, -1, -4, 5, 36, 27, -39, -42, 6, 12], ![-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], ![-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], ![-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], ![0, -1, -4, 5, 36, 27, -39, -42, 6, 12], ![-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], ![-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], ![-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105], ![-105, -522, 111, 4254, 6489, -1066, -7798, -3559, 1188, 783]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], ![0, -1, -4, 5, 36, 27, -39, -42, 6, 12], ![-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], ![-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], ![-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105], ![-105, -522, 111, 4254, 6489, -1066, -7798, -3559, 1188, 783], ![-783, -3237, 3393, 28299, 25395, -24048, -33952, -3100, 5837, 1188]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], ![0, -1, -4, 5, 36, 27, -39, -42, 6, 12], ![-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], ![-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], ![-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105], ![-105, -522, 111, 4254, 6489, -1066, -7798, -3559, 1188, 783], ![-783, -3237, 3393, 28299, 25395, -24048, -33952, -3100, 5837, 1188], ![-1188, -5535, 2703, 46161, 60375, -20937, -73944, -26824, 11156, 5837]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], ![0, -1, -4, 5, 36, 27, -39, -42, 6, 12], ![-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], ![-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], ![-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105], ![-105, -522, 111, 4254, 6489, -1066, -7798, -3559, 1188, 783], ![-783, -3237, 3393, 28299, 25395, -24048, -33952, -3100, 5837, 1188], ![-1188, -5535, 2703, 46161, 60375, -20937, -73944, -26824, 11156, 5837], ![-5837, -24536, 23650, 212835, 203760, -167268, -266091, -38922, 43220, 11156]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-102, -6, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-102, -6, -12, 0, -1], [-105, -102, -6, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-102, -6, -12, 0, -1], [-105, -102, -6, -12, 0, -1], [-783, -105, -102, -6, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-102, -6, -12, 0, -1], [-105, -102, -6, -12, 0, -1], [-783, -105, -102, -6, -12, 0, -1], [-1188, -783, -105, -102, -6, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-102, -6, -12, 0, -1], [-105, -102, -6, -12, 0, -1], [-783, -105, -102, -6, -12, 0, -1], [-1188, -783, -105, -102, -6, -12, 0, -1], [-5837, -1188, -783, -105, -102, -6, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 5, 36, 27, -39, -42, 6, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], [0, -1, -4, 5, 36, 27, -39, -42, 6, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], [0, -1, -4, 5, 36, 27, -39, -42, 6, 12], [-12, -48, 59, 428, 329, -432, -477, 33, 102, 6]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], [0, -1, -4, 5, 36, 27, -39, -42, 6, 12], [-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], [-6, -36, -18, 275, 590, 95, -684, -441, 105, 102]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], [0, -1, -4, 5, 36, 27, -39, -42, 6, 12], [-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], [-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], [-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], [0, -1, -4, 5, 36, 27, -39, -42, 6, 12], [-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], [-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], [-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105], [-105, -522, 111, 4254, 6489, -1066, -7798, -3559, 1188, 783]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], [0, -1, -4, 5, 36, 27, -39, -42, 6, 12], [-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], [-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], [-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105], [-105, -522, 111, 4254, 6489, -1066, -7798, -3559, 1188, 783], [-783, -3237, 3393, 28299, 25395, -24048, -33952, -3100, 5837, 1188]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], [0, -1, -4, 5, 36, 27, -39, -42, 6, 12], [-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], [-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], [-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105], [-105, -522, 111, 4254, 6489, -1066, -7798, -3559, 1188, 783], [-783, -3237, 3393, 28299, 25395, -24048, -33952, -3100, 5837, 1188], [-1188, -5535, 2703, 46161, 60375, -20937, -73944, -26824, 11156, 5837]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 5, 36, 27, -39, -42, 6, 12, 0], [0, -1, -4, 5, 36, 27, -39, -42, 6, 12], [-12, -48, 59, 428, 329, -432, -477, 33, 102, 6], [-6, -36, -18, 275, 590, 95, -684, -441, 105, 102], [-102, -414, 474, 3654, 3029, -3388, -4189, -72, 783, 105], [-105, -522, 111, 4254, 6489, -1066, -7798, -3559, 1188, 783], [-783, -3237, 3393, 28299, 25395, -24048, -33952, -3100, 5837, 1188], [-1188, -5535, 2703, 46161, 60375, -20937, -73944, -26824, 11156, 5837], [-5837, -24536, 23650, 212835, 203760, -167268, -266091, -38922, 43220, 11156]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp762792089 : Fact (Nat.Prime 762792089) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 2]
  b' := [2, 3, 1, 2, 4]
  k := [1]
  f := [3, 4, 6, 16, 11, -3, -4, 2, 4]
  g := [4, 3, 2, 4, 0, 1]
  h := [4, 3, 2, 4, 0, 1]
  a := [4, 0, 1, 4, 1]
  b := [1, 4, 1, 0, 2, 3, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD762792089 : CertificateDedekindCriterionLists l 762792089 where
  n := 2
  a' := [582982036, 361181458, 326209091, 525177914, 286841273, 457973801, 219172152, 31327082]
  b' := [114258892, 237983731, 272628980, 536784945, 342561537, 700553064, 161445256, 748006918, 589801949]
  k := [724247712, 172698036, 588893846, 88174646, 163077431, 139409155, 161659370, 393858325, 1]
  f := [53860401, 40295953, 97392339, 20409377, 90496091, 69038648, 45503786, 136009343, 139857046, 1]
  g := [222719045, 166628468, 402728689, 84395154, 374211899, 285482866, 188163465, 562414508, 578325207, 1]
  h := [184466882, 1]
  a := [389539219, 711191231, 248807415, 160992445, 217549706, 50785099, 589329350, 52661435, 24487947]
  b := [536340952, 90838294, 569406538, 743253026, 754789403, 15154281, 393883481, 18011614, 738304142]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 762792089]
  exp := ![1, 1]
  pdgood := [5, 762792089]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp762792089.out
  a := [-2492955625659, 11287913615644, 44431239371787, -21654831638534, -77692400530554, -1579266772022, 29123806663440, 1570605123670, -3116826645900]
  b := [624192396526, 1231458213063, -5580077751805, -11191867994139, 5558976191480, 13096762747500, -26156889379, -3660419061360, -157060512367, 311682664590]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 762792089 T_ofList CD762792089

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

end VoightMaximalOrderD10R129

end TraceEuclidean
