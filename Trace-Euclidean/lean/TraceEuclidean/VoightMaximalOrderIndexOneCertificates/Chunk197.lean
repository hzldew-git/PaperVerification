import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk193
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

namespace VoightMaximalOrderD10R309

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4235139828125, [5, -10, -20, 40, 24, -51, -6, 25, -3, -4, 1], 1⟩
local notation "l" => [5, -10, -20, 40, 24, -51, -6, 25, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 10, 20, -40, -24, 51, 6, -25, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], ![-20, 35, 90, -140, -136, 180, 75, -94, -13, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], ![-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], ![-95, 170, 415, -670, -596, 833, 294, -400, -37, 63]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], ![-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], ![-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], ![-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], ![-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], ![-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], ![-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], ![-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], ![-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], ![-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], ![-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], ![-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649], ![-3245, 5415, 14815, -21125, -22746, 25834, 12677, -12318, -2217, 1960]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], ![-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], ![-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], ![-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], ![-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649], ![-3245, 5415, 14815, -21125, -22746, 25834, 12677, -12318, -2217, 1960], ![-9800, 16355, 44615, -63585, -68165, 77214, 37594, -36323, -6438, 5623]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], ![-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], ![-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], ![-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], ![-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649], ![-3245, 5415, 14815, -21125, -22746, 25834, 12677, -12318, -2217, 1960], ![-9800, 16355, 44615, -63585, -68165, 77214, 37594, -36323, -6438, 5623], ![-28115, 46430, 128815, -180305, -198537, 218608, 110952, -102981, -19454, 16054]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], ![-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], ![-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], ![-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], ![-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649], ![-3245, 5415, 14815, -21125, -22746, 25834, 12677, -12318, -2217, 1960], ![-9800, 16355, 44615, -63585, -68165, 77214, 37594, -36323, -6438, 5623], ![-28115, 46430, 128815, -180305, -198537, 218608, 110952, -102981, -19454, 16054], ![-80270, 132425, 367510, -513345, -565601, 620217, 314932, -290398, -54819, 44762]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-215, -63, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-215, -63, -19, -4, -1], [-649, -215, -63, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-215, -63, -19, -4, -1], [-649, -215, -63, -19, -4, -1], [-1960, -649, -215, -63, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-215, -63, -19, -4, -1], [-649, -215, -63, -19, -4, -1], [-1960, -649, -215, -63, -19, -4, -1], [-5623, -1960, -649, -215, -63, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-215, -63, -19, -4, -1], [-649, -215, -63, -19, -4, -1], [-1960, -649, -215, -63, -19, -4, -1], [-5623, -1960, -649, -215, -63, -19, -4, -1], [-16054, -5623, -1960, -649, -215, -63, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 10, 20, -40, -24, 51, 6, -25, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], [-20, 35, 90, -140, -136, 180, 75, -94, -13, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], [-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], [-95, 170, 415, -670, -596, 833, 294, -400, -37, 63]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], [-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], [-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], [-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], [-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], [-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], [-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], [-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], [-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], [-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], [-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], [-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649], [-3245, 5415, 14815, -21125, -22746, 25834, 12677, -12318, -2217, 1960]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], [-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], [-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], [-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], [-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649], [-3245, 5415, 14815, -21125, -22746, 25834, 12677, -12318, -2217, 1960], [-9800, 16355, 44615, -63585, -68165, 77214, 37594, -36323, -6438, 5623]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], [-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], [-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], [-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], [-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649], [-3245, 5415, 14815, -21125, -22746, 25834, 12677, -12318, -2217, 1960], [-9800, 16355, 44615, -63585, -68165, 77214, 37594, -36323, -6438, 5623], [-28115, 46430, 128815, -180305, -198537, 218608, 110952, -102981, -19454, 16054]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 10, 20, -40, -24, 51, 6, -25, 3, 4], [-20, 35, 90, -140, -136, 180, 75, -94, -13, 19], [-95, 170, 415, -670, -596, 833, 294, -400, -37, 63], [-315, 535, 1430, -2105, -2182, 2617, 1211, -1281, -211, 215], [-1075, 1835, 4835, -7170, -7265, 8783, 3907, -4164, -636, 649], [-3245, 5415, 14815, -21125, -22746, 25834, 12677, -12318, -2217, 1960], [-9800, 16355, 44615, -63585, -68165, 77214, 37594, -36323, -6438, 5623], [-28115, 46430, 128815, -180305, -198537, 218608, 110952, -102981, -19454, 16054], [-80270, 132425, 367510, -513345, -565601, 620217, 314932, -290398, -54819, 44762]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp331 : Fact (Nat.Prime 331) := fact_iff.2 (by norm_num)
instance hp359 : Fact (Nat.Prime 359) := fact_iff.2 (by norm_num)
instance hp2281 : Fact (Nat.Prime 2281) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [2, 2, 4]
  b' := [2, 1, 0, 4]
  k := [4, 4, 4, 0, 2, 1, 1]
  f := [-1, 2, 4, -8, -3, 15, 8, 1, 4, 2]
  g := [0, 3, 4, 3, 1]
  h := [0, 0, 0, 3, 4, 3, 1]
  a := [4, 1]
  b := [1, 1, 2, 1, 4, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD331 : CertificateDedekindCriterionLists l 331 where
  n := 2
  a' := [265, 169, 0, 237, 89, 84, 92, 150]
  b' := [76, 118, 240, 209, 166, 86, 306, 91, 204]
  k := [270, 328, 211, 318, 310, 146, 203, 133, 1]
  f := [12, 91, 81, 81, 79, 71, 91, 58, 68, 1]
  g := [41, 310, 273, 274, 267, 239, 308, 195, 230, 1]
  h := [97, 1]
  a := [191, 148, 18, 110, 190, 193, 107, 91, 110]
  b := [41, 22, 222, 17, 237, 291, 88, 186, 221]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD359 : CertificateDedekindCriterionLists l 359 where
  n := 2
  a' := [268, 75, 36, 10, 338, 270, 227, 198]
  b' := [235, 128, 140, 32, 6, 198, 329, 189, 337]
  k := [151, 37, 49, 290, 198, 350, 310, 253, 1]
  f := [23, 35, 4, 17, 48, 15, 1, 41, 44, 1]
  g := [162, 243, 23, 120, 336, 98, 5, 289, 304, 1]
  h := [51, 1]
  a := [26, 121, 142, 44, 233, 193, 353, 123, 150]
  b := [229, 6, 306, 201, 82, 356, 233, 105, 209]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2281 : CertificateDedekindCriterionLists l 2281 where
  n := 2
  a' := [1176, 259, 1056, 649, 725, 716, 1358, 1196]
  b' := [1539, 1752, 575, 795, 2107, 2260, 52, 714, 374]
  k := [1687, 2200, 833, 1153, 759, 1638, 653, 192, 1]
  f := [1136, 480, 384, 1808, 1957, 2093, 1448, 82, 90, 1]
  g := [1187, 501, 401, 1889, 2044, 2186, 1512, 85, 94, 1]
  h := [2183, 1]
  a := [2050, 1690, 1910, 1825, 1672, 2160, 1526, 2040, 930]
  b := [738, 336, 1667, 1613, 291, 2154, 1894, 1680, 1351]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 331, 359, 2281]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 331, 359, 2281]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp331.out
    exact hp359.out
    exact hp2281.out
  a := [-7860117871, -46534635144, 18426380820, 120358939116, -33739331088, -88729942372, 27259320236, 18680544928, -6505913880]
  b := [-4065583410, 855133939, 19260524620, -2428204406, -26363413933, 4811905790, 13251122736, -3305916658, -2128291048, 650591388]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 331 T_ofList CD331
    exact satisfiesDedekindCriterion_of_certificate_lists T l 359 T_ofList CD359
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2281 T_ofList CD2281

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

end VoightMaximalOrderD10R309

namespace VoightMaximalOrderD10R310

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4252404503125, [1, -2, -19, 40, 45, -58, -22, 30, 0, -5, 1], 1⟩
local notation "l" => [1, -2, -19, 40, 45, -58, -22, 30, 0, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 19, -40, -45, 58, 22, -30, 0, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], ![-5, 9, 97, -181, -265, 245, 168, -128, -30, 25]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], ![-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], ![-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], ![-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], ![-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], ![-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], ![-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], ![-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], ![-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], ![-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], ![-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], ![-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], ![-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], ![-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153], ![-1153, 1959, 22506, -39362, -63915, 47943, 40314, -22752, -7135, 3710]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], ![-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], ![-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], ![-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], ![-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153], ![-1153, 1959, 22506, -39362, -63915, 47943, 40314, -22752, -7135, 3710], ![-3710, 6267, 72449, -125894, -206312, 151265, 129563, -70986, -22752, 11415]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], ![-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], ![-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], ![-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], ![-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153], ![-1153, 1959, 22506, -39362, -63915, 47943, 40314, -22752, -7135, 3710], ![-3710, 6267, 72449, -125894, -206312, 151265, 129563, -70986, -22752, 11415], ![-11415, 19120, 223152, -384151, -639569, 455758, 402395, -212887, -70986, 34323]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], ![-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], ![-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], ![-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], ![-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153], ![-1153, 1959, 22506, -39362, -63915, 47943, 40314, -22752, -7135, 3710], ![-3710, 6267, 72449, -125894, -206312, 151265, 129563, -70986, -22752, 11415], ![-11415, 19120, 223152, -384151, -639569, 455758, 402395, -212887, -70986, 34323], ![-34323, 57231, 671257, -1149768, -1928686, 1351165, 1210864, -627295, -212887, 100629]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1], [-1153, -347, -95, -25, -5, -1]], ![[], [], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1], [-1153, -347, -95, -25, -5, -1], [-3710, -1153, -347, -95, -25, -5, -1]], ![[], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1], [-1153, -347, -95, -25, -5, -1], [-3710, -1153, -347, -95, -25, -5, -1], [-11415, -3710, -1153, -347, -95, -25, -5, -1]], ![[], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1], [-1153, -347, -95, -25, -5, -1], [-3710, -1153, -347, -95, -25, -5, -1], [-11415, -3710, -1153, -347, -95, -25, -5, -1], [-34323, -11415, -3710, -1153, -347, -95, -25, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 19, -40, -45, 58, 22, -30, 0, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], [-5, 9, 97, -181, -265, 245, 168, -128, -30, 25]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], [-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], [-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], [-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], [-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], [-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], [-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], [-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], [-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], [-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], [-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], [-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], [-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], [-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153], [-1153, 1959, 22506, -39362, -63915, 47943, 40314, -22752, -7135, 3710]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], [-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], [-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], [-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], [-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153], [-1153, 1959, 22506, -39362, -63915, 47943, 40314, -22752, -7135, 3710], [-3710, 6267, 72449, -125894, -206312, 151265, 129563, -70986, -22752, 11415]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], [-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], [-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], [-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], [-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153], [-1153, 1959, 22506, -39362, -63915, 47943, 40314, -22752, -7135, 3710], [-3710, 6267, 72449, -125894, -206312, 151265, 129563, -70986, -22752, 11415], [-11415, 19120, 223152, -384151, -639569, 455758, 402395, -212887, -70986, 34323]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 19, -40, -45, 58, 22, -30, 0, 5], [-5, 9, 97, -181, -265, 245, 168, -128, -30, 25], [-25, 45, 484, -903, -1306, 1185, 795, -582, -128, 95], [-95, 165, 1850, -3316, -5178, 4204, 3275, -2055, -582, 347], [-347, 599, 6758, -12030, -18931, 14948, 11838, -7135, -2055, 1153], [-1153, 1959, 22506, -39362, -63915, 47943, 40314, -22752, -7135, 3710], [-3710, 6267, 72449, -125894, -206312, 151265, 129563, -70986, -22752, 11415], [-11415, 19120, 223152, -384151, -639569, 455758, 402395, -212887, -70986, 34323], [-34323, 57231, 671257, -1149768, -1928686, 1351165, 1210864, -627295, -212887, 100629]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1360769441 : Fact (Nat.Prime 1360769441) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := []
  b' := [4]
  k := [1]
  f := [0, 2, 7, -8, -9, 12, 6, -6, 0, 1]
  g := [1, 4, 0, 0, 0, 1]
  h := [1, 4, 0, 0, 0, 1]
  a := [1, 2, 1, 2, 3]
  b := [1, 4, 3, 0, 4, 2, 2, 3, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1360769441 : CertificateDedekindCriterionLists l 1360769441 where
  n := 2
  a' := [382812296, 550153505, 1130883847, 442978465, 1146573928, 575278492, 223953813, 855149037]
  b' := [769268421, 815693543, 137343614, 534616852, 273519039, 261487599, 937383485, 2721927, 358573254]
  k := [216138254, 1248388292, 1115868680, 1037551385, 617924788, 131769149, 867619788, 1093944241, 1]
  f := [37921015, 608695528, 663060778, 554063774, 794164899, 594386511, 678478393, 441567821, 327112316, 1]
  g := [63408612, 1017813963, 1108719362, 926462934, 1327941615, 993887521, 1134499515, 738355832, 546972118, 1]
  h := [813797318, 1]
  a := [697786659, 150859624, 738237837, 220033443, 1165144529, 174504782, 925433094, 420476627, 499982997]
  b := [1010019285, 107920075, 613807167, 514258328, 657634148, 518403903, 1091267984, 886526971, 860786444]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1360769441]
  exp := ![1, 1]
  pdgood := [5, 1360769441]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1360769441.out
  a := [-47490270521, -1203327672262, -717611927921, 2580703280018, 579219238732, -1717687763210, 106981993085, 350509242080, -83701319460]
  b := [-27147058863, -38379447213, 396065243518, 218529286707, -514833427753, -108447642524, 246566057004, -12005534083, -39235990181, 8370131946]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1360769441 T_ofList CD1360769441

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

end VoightMaximalOrderD10R310

namespace VoightMaximalOrderD10R312

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4263015503125, [1, -1, -18, 33, 22, -65, 10, 29, -11, -2, 1], 1⟩
local notation "l" => [1, -1, -18, 33, 22, -65, 10, 29, -11, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -33, -22, 65, -10, -29, 11, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], ![-2, 1, 37, -48, -77, 108, 45, -68, -7, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], ![-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], ![-15, 13, 271, -458, -378, 898, -42, -390, 97, 23]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], ![-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], ![-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], ![-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], ![-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], ![-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], ![-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], ![-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], ![-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], ![-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], ![-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], ![-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149], ![-149, 6, 2802, -2335, -7570, 6051, 6841, -4634, -1840, 1162]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], ![-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], ![-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], ![-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], ![-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149], ![-149, 6, 2802, -2335, -7570, 6051, 6841, -4634, -1840, 1162], ![-1162, 1013, 20922, -35544, -27899, 67960, -5569, -26857, 8148, 484]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], ![-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], ![-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], ![-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], ![-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149], ![-149, 6, 2802, -2335, -7570, 6051, 6841, -4634, -1840, 1162], ![-1162, 1013, 20922, -35544, -27899, 67960, -5569, -26857, 8148, 484], ![-484, -678, 9725, 4950, -46192, 3561, 63120, -19605, -21533, 9116]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], ![-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], ![-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], ![-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], ![-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149], ![-149, 6, 2802, -2335, -7570, 6051, 6841, -4634, -1840, 1162], ![-1162, 1013, 20922, -35544, -27899, 67960, -5569, -26857, 8148, 484], ![-484, -678, 9725, 4950, -46192, 3561, 63120, -19605, -21533, 9116], ![-9116, 8632, 163410, -291103, -195602, 546348, -87599, -201244, 80671, -3301]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-23, -15, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-23, -15, -2, -1], [-143, -23, -15, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-23, -15, -2, -1], [-143, -23, -15, -2, -1], [-149, -143, -23, -15, -2, -1]], ![[], [], [], [-1], [-2, -1], [-15, -2, -1], [-23, -15, -2, -1], [-143, -23, -15, -2, -1], [-149, -143, -23, -15, -2, -1], [-1162, -149, -143, -23, -15, -2, -1]], ![[], [], [-1], [-2, -1], [-15, -2, -1], [-23, -15, -2, -1], [-143, -23, -15, -2, -1], [-149, -143, -23, -15, -2, -1], [-1162, -149, -143, -23, -15, -2, -1], [-484, -1162, -149, -143, -23, -15, -2, -1]], ![[], [-1], [-2, -1], [-15, -2, -1], [-23, -15, -2, -1], [-143, -23, -15, -2, -1], [-149, -143, -23, -15, -2, -1], [-1162, -149, -143, -23, -15, -2, -1], [-484, -1162, -149, -143, -23, -15, -2, -1], [-9116, -484, -1162, -149, -143, -23, -15, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -33, -22, 65, -10, -29, 11, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], [-2, 1, 37, -48, -77, 108, 45, -68, -7, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], [-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], [-15, 13, 271, -458, -378, 898, -42, -390, 97, 23]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], [-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], [-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], [-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], [-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], [-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], [-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], [-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], [-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], [-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], [-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], [-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149], [-149, 6, 2802, -2335, -7570, 6051, 6841, -4634, -1840, 1162]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], [-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], [-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], [-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], [-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149], [-149, 6, 2802, -2335, -7570, 6051, 6841, -4634, -1840, 1162], [-1162, 1013, 20922, -35544, -27899, 67960, -5569, -26857, 8148, 484]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], [-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], [-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], [-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], [-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149], [-149, 6, 2802, -2335, -7570, 6051, 6841, -4634, -1840, 1162], [-1162, 1013, 20922, -35544, -27899, 67960, -5569, -26857, 8148, 484], [-484, -678, 9725, 4950, -46192, 3561, 63120, -19605, -21533, 9116]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -33, -22, 65, -10, -29, 11, 2], [-2, 1, 37, -48, -77, 108, 45, -68, -7, 15], [-15, 13, 271, -458, -378, 898, -42, -390, 97, 23], [-23, 8, 427, -488, -964, 1117, 668, -709, -137, 143], [-143, 120, 2582, -4292, -3634, 8331, -313, -3479, 864, 149], [-149, 6, 2802, -2335, -7570, 6051, 6841, -4634, -1840, 1162], [-1162, 1013, 20922, -35544, -27899, 67960, -5569, -26857, 8148, 484], [-484, -678, 9725, 4950, -46192, 3561, 63120, -19605, -21533, 9116], [-9116, 8632, 163410, -291103, -195602, 546348, -87599, -201244, 80671, -3301]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp71 : Fact (Nat.Prime 71) := fact_iff.2 (by norm_num)
instance hp2399 : Fact (Nat.Prime 2399) := fact_iff.2 (by norm_num)
instance hp8009 : Fact (Nat.Prime 8009) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 1, 2]
  b' := [0, 3, 3, 0, 3]
  k := [1]
  f := [3, 5, 7, 1, 7, 21, 4, 1, 7, 2]
  g := [4, 3, 1, 4, 4, 1]
  h := [4, 3, 1, 4, 4, 1]
  a := [4, 0, 3, 0, 2]
  b := [1, 3, 2, 2, 4, 2, 0, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD71 : CertificateDedekindCriterionLists l 71 where
  n := 2
  a' := [5, 15, 5, 30, 7, 8, 7, 67]
  b' := [70, 41, 7, 29, 21, 70, 38, 52, 32]
  k := [36, 29, 51, 29, 28, 43, 43, 45, 1]
  f := [1, 5, 1, 7, 2, 9, 11, 3, 10, 1]
  g := [6, 29, 2, 44, 10, 47, 62, 15, 57, 1]
  h := [12, 1]
  a := [34, 54, 60, 50, 12, 30, 67, 42, 40]
  b := [30, 7, 2, 16, 24, 23, 23, 63, 31]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2399 : CertificateDedekindCriterionLists l 2399 where
  n := 2
  a' := [1680, 2366, 507, 1634, 1218, 907, 423, 1710]
  b' := [1596, 1585, 999, 1217, 2304, 762, 584, 1192, 2209]
  k := [230, 155, 639, 2267, 766, 1881, 67, 1122, 1]
  f := [219, 1442, 680, 348, 916, 1228, 163, 337, 429, 1]
  g := [286, 1883, 887, 454, 1196, 1603, 212, 440, 560, 1]
  h := [1837, 1]
  a := [1991, 688, 1036, 1271, 881, 1849, 571, 2, 771]
  b := [1881, 2374, 1742, 129, 1372, 785, 600, 241, 1628]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD8009 : CertificateDedekindCriterionLists l 8009 where
  n := 2
  a' := [5194, 5959, 7640, 90, 1497, 3811, 6500, 2339]
  b' := [5305, 7024, 5451, 560, 3484, 655, 2751, 611, 630]
  k := [1589, 6481, 1622, 6678, 5424, 5600, 164, 5354, 1]
  f := [3625, 649, 2425, 1355, 1014, 980, 4595, 4175, 1782, 1]
  g := [5446, 974, 3643, 2035, 1523, 1472, 6903, 6271, 2676, 1]
  h := [5331, 1]
  a := [3549, 3147, 4628, 603, 2008, 7539, 5316, 7151, 1139]
  b := [6232, 6968, 3323, 4154, 4353, 4962, 3394, 1981, 6870]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 71, 2399, 8009]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 71, 2399, 8009]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp71.out
    exact hp2399.out
    exact hp8009.out
  a := [-15498682089, -829118814156, 1117763688117, 3104542501640, -3305833808625, -1908542396484, 2097022442278, 101237762818, -232141457760]
  b := [-22319506894, -10117883883, 380471417157, -263297169347, -723180215596, 567223069089, 312846943725, -267105702158, -14766605437, 23214145776]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 71 T_ofList CD71
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2399 T_ofList CD2399
    exact satisfiesDedekindCriterion_of_certificate_lists T l 8009 T_ofList CD8009

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

end VoightMaximalOrderD10R312

namespace VoightMaximalOrderD10R313

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4280150582504, [2, -10, -9, 69, -39, -52, 38, 13, -11, -1, 1], 1⟩
local notation "l" => [2, -10, -9, 69, -39, -52, 38, 13, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 10, 9, -69, 39, 52, -38, -13, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], ![-2, 8, 19, -60, -30, 91, 14, -51, -2, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], ![-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], ![-24, 118, 116, -809, 408, 594, -365, -142, 81, 10]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], ![-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], ![-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], ![-20, 76, 208, -574, -419, 928, 214, -495, -32, 91]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], ![-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], ![-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], ![-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], ![-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], ![-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], ![-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], ![-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], ![-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59], ![-118, 408, 1421, -3176, -3770, 6043, 2071, -3297, -320, 565]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], ![-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], ![-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], ![-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], ![-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59], ![-118, 408, 1421, -3176, -3770, 6043, 2071, -3297, -320, 565], ![-1130, 5532, 5493, -37564, 18859, 25610, -15427, -5274, 2918, 245]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], ![-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], ![-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], ![-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], ![-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59], ![-118, 408, 1421, -3176, -3770, 6043, 2071, -3297, -320, 565], ![-1130, 5532, 5493, -37564, 18859, 25610, -15427, -5274, 2918, 245], ![-490, 1320, 7737, -11412, -28009, 31599, 16300, -18612, -2579, 3163]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], ![-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], ![-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], ![-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], ![-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59], ![-118, 408, 1421, -3176, -3770, 6043, 2071, -3297, -320, 565], ![-1130, 5532, 5493, -37564, 18859, 25610, -15427, -5274, 2918, 245], ![-490, 1320, 7737, -11412, -28009, 31599, 16300, -18612, -2579, 3163], ![-6326, 31140, 29787, -210510, 111945, 136467, -88595, -24819, 16181, 584]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-91, -10, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-91, -10, -12, -1, -1], [-59, -91, -10, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-91, -10, -12, -1, -1], [-59, -91, -10, -12, -1, -1], [-565, -59, -91, -10, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-91, -10, -12, -1, -1], [-59, -91, -10, -12, -1, -1], [-565, -59, -91, -10, -12, -1, -1], [-245, -565, -59, -91, -10, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-91, -10, -12, -1, -1], [-59, -91, -10, -12, -1, -1], [-565, -59, -91, -10, -12, -1, -1], [-245, -565, -59, -91, -10, -12, -1, -1], [-3163, -245, -565, -59, -91, -10, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 10, 9, -69, 39, 52, -38, -13, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], [-2, 8, 19, -60, -30, 91, 14, -51, -2, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], [-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], [-24, 118, 116, -809, 408, 594, -365, -142, 81, 10]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], [-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], [-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], [-20, 76, 208, -574, -419, 928, 214, -495, -32, 91]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], [-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], [-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], [-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], [-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], [-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], [-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], [-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], [-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59], [-118, 408, 1421, -3176, -3770, 6043, 2071, -3297, -320, 565]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], [-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], [-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], [-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], [-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59], [-118, 408, 1421, -3176, -3770, 6043, 2071, -3297, -320, 565], [-1130, 5532, 5493, -37564, 18859, 25610, -15427, -5274, 2918, 245]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], [-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], [-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], [-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], [-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59], [-118, 408, 1421, -3176, -3770, 6043, 2071, -3297, -320, 565], [-1130, 5532, 5493, -37564, 18859, 25610, -15427, -5274, 2918, 245], [-490, 1320, 7737, -11412, -28009, 31599, 16300, -18612, -2579, 3163]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 10, 9, -69, 39, 52, -38, -13, 11, 1], [-2, 8, 19, -60, -30, 91, 14, -51, -2, 12], [-24, 118, 116, -809, 408, 594, -365, -142, 81, 10], [-20, 76, 208, -574, -419, 928, 214, -495, -32, 91], [-182, 890, 895, -6071, 2975, 4313, -2530, -969, 506, 59], [-118, 408, 1421, -3176, -3770, 6043, 2071, -3297, -320, 565], [-1130, 5532, 5493, -37564, 18859, 25610, -15427, -5274, 2918, 245], [-490, 1320, 7737, -11412, -28009, 31599, 16300, -18612, -2579, 3163], [-6326, 31140, 29787, -210510, 111945, 136467, -88595, -24819, 16181, 584]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp2153 : Fact (Nat.Prime 2153) := fact_iff.2 (by norm_num)
instance hp248499221 : Fact (Nat.Prime 248499221) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [1, 1]
  k := [1, 1, 1, 0, 0, 1, 1, 1, 1]
  f := [-1, 5, 5, -34, 20, 26, -19, -6, 6, 1]
  g := [0, 1, 1, 1, 0, 0, 1, 1, 1, 1]
  h := [0, 1]
  a := [1, 0, 0, 1, 0, 1]
  b := [1, 0, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2153 : CertificateDedekindCriterionLists l 2153 where
  n := 2
  a' := [888, 517, 203, 355, 2064, 1193, 1487, 310]
  b' := [1532, 1549, 1164, 2003, 309, 115, 1378, 1480, 444]
  k := [1725, 2038, 1628, 1094, 144, 943, 926, 58, 1]
  f := [905, 919, 671, 803, 561, 677, 786, 666, 538, 1]
  g := [1861, 1888, 1378, 1650, 1152, 1391, 1615, 1368, 1105, 1]
  h := [1047, 1]
  a := [921, 592, 2101, 2054, 1141, 1002, 728, 1414, 548]
  b := [554, 1097, 1264, 629, 1332, 1099, 1439, 1423, 1605]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD248499221 : CertificateDedekindCriterionLists l 248499221 where
  n := 2
  a' := [2430191, 161925153, 72222573, 138711352, 228560427, 237973997, 173963696, 22255277]
  b' := [178020178, 236433328, 103908701, 155461567, 129008059, 226701053, 140534009, 136141803, 25138216]
  k := [6182448, 44540022, 98056831, 22181751, 220521552, 150542412, 137873412, 80756683, 1]
  f := [83074195, 203813793, 140761611, 27873374, 31662723, 194558578, 73073953, 96591358, 33817313, 1]
  g := [99191743, 243356500, 168071318, 33281195, 37805731, 232305645, 87251314, 115331423, 40378341, 1]
  h := [208120879, 1]
  a := [122827228, 136209788, 88984815, 74929959, 66124634, 40156572, 172626588, 240954464, 32450875]
  b := [93046342, 37375736, 72601990, 121442609, 81907239, 156197809, 134707876, 204981330, 216048346]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 2153, 248499221]
  exp := ![2, 1, 1]
  pdgood := [2, 2153, 248499221]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp2153.out
    exact hp248499221.out
  a := [-6016823654544, -24484213882961, 85909869967528, 13040860230502, -116518728030046, 7881582972229, 48405791055134, -3104806157945, -6254557216350]
  b := [-1417372260034, 3671250946013, 11133471680029, -24716335828169, -4606520076610, 21125104501394, -415288959793, -6303920769637, 247935043631, 625455721635]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2153 T_ofList CD2153
    exact satisfiesDedekindCriterion_of_certificate_lists T l 248499221 T_ofList CD248499221

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

end VoightMaximalOrderD10R313

end TraceEuclidean
