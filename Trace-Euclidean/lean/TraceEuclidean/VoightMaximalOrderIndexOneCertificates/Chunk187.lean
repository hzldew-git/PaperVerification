import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk183
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

namespace VoightMaximalOrderD10R205

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3250106565625, [1, 2, -19, 11, 41, -33, -24, 25, 1, -5, 1], 1⟩
local notation "l" => [1, 2, -19, 11, 41, -33, -24, 25, 1, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 19, -11, -41, 33, 24, -25, -1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], ![-5, -11, 93, -36, -216, 124, 153, -101, -30, 24]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], ![-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], ![-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], ![-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], ![-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], ![-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], ![-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], ![-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], ![-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], ![-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], ![-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], ![-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], ![-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], ![-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088], ![-1088, -2501, 19932, -5997, -46526, 22034, 32976, -17450, -6477, 3565]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], ![-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], ![-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], ![-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], ![-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088], ![-1088, -2501, 19932, -5997, -46526, 22034, 32976, -17450, -6477, 3565], ![-3565, -8218, 65234, -19283, -152162, 71119, 107594, -56149, -21015, 11348]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], ![-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], ![-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], ![-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], ![-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088], ![-1088, -2501, 19932, -5997, -46526, 22034, 32976, -17450, -6477, 3565], ![-3565, -8218, 65234, -19283, -152162, 71119, 107594, -56149, -21015, 11348], ![-11348, -26261, 207394, -59594, -484551, 222322, 343471, -176106, -67497, 35725]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], ![-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], ![-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], ![-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], ![-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088], ![-1088, -2501, 19932, -5997, -46526, 22034, 32976, -17450, -6477, 3565], ![-3565, -8218, 65234, -19283, -152162, 71119, 107594, -56149, -21015, 11348], ![-11348, -26261, 207394, -59594, -484551, 222322, 343471, -176106, -67497, 35725], ![-35725, -82798, 652514, -185581, -1524319, 694374, 1079722, -549654, -211831, 111128]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-325, -90, -24, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-325, -90, -24, -5, -1], [-1088, -325, -90, -24, -5, -1]], ![[], [], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-325, -90, -24, -5, -1], [-1088, -325, -90, -24, -5, -1], [-3565, -1088, -325, -90, -24, -5, -1]], ![[], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-325, -90, -24, -5, -1], [-1088, -325, -90, -24, -5, -1], [-3565, -1088, -325, -90, -24, -5, -1], [-11348, -3565, -1088, -325, -90, -24, -5, -1]], ![[], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-325, -90, -24, -5, -1], [-1088, -325, -90, -24, -5, -1], [-3565, -1088, -325, -90, -24, -5, -1], [-11348, -3565, -1088, -325, -90, -24, -5, -1], [-35725, -11348, -3565, -1088, -325, -90, -24, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 19, -11, -41, 33, 24, -25, -1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], [-5, -11, 93, -36, -216, 124, 153, -101, -30, 24]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], [-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], [-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], [-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], [-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], [-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], [-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], [-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], [-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], [-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], [-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], [-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], [-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], [-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088], [-1088, -2501, 19932, -5997, -46526, 22034, 32976, -17450, -6477, 3565]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], [-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], [-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], [-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], [-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088], [-1088, -2501, 19932, -5997, -46526, 22034, 32976, -17450, -6477, 3565], [-3565, -8218, 65234, -19283, -152162, 71119, 107594, -56149, -21015, 11348]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], [-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], [-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], [-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], [-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088], [-1088, -2501, 19932, -5997, -46526, 22034, 32976, -17450, -6477, 3565], [-3565, -8218, 65234, -19283, -152162, 71119, 107594, -56149, -21015, 11348], [-11348, -26261, 207394, -59594, -484551, 222322, 343471, -176106, -67497, 35725]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 19, -11, -41, 33, 24, -25, -1, 5], [-5, -11, 93, -36, -216, 124, 153, -101, -30, 24], [-24, -53, 445, -171, -1020, 576, 700, -447, -125, 90], [-90, -204, 1657, -545, -3861, 1950, 2736, -1550, -537, 325], [-325, -740, 5971, -1918, -13870, 6864, 9750, -5389, -1875, 1088], [-1088, -2501, 19932, -5997, -46526, 22034, 32976, -17450, -6477, 3565], [-3565, -8218, 65234, -19283, -152162, 71119, 107594, -56149, -21015, 11348], [-11348, -26261, 207394, -59594, -484551, 222322, 343471, -176106, -67497, 35725], [-35725, -82798, 652514, -185581, -1524319, 694374, 1079722, -549654, -211831, 111128]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp509 : Fact (Nat.Prime 509) := fact_iff.2 (by norm_num)
instance hp2043289 : Fact (Nat.Prime 2043289) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [0, 4, 0, 1]
  k := [1]
  f := [0, 0, 4, -1, -7, 7, 7, -5, 1, 1]
  g := [1, 1, 0, 3, 0, 1]
  h := [1, 1, 0, 3, 0, 1]
  a := [2, 3, 0, 1, 2]
  b := [1, 4, 3, 4, 1, 2, 0, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD509 : CertificateDedekindCriterionLists l 509 where
  n := 2
  a' := [178, 236, 128, 230, 383, 440, 347, 119]
  b' := [252, 147, 105, 114, 12, 189, 114, 342, 213]
  k := [268, 305, 210, 412, 368, 53, 305, 398, 1]
  f := [48, 16, 25, 17, 7, 13, 46, 3, 47, 1]
  g := [461, 145, 237, 159, 65, 123, 439, 21, 451, 1]
  h := [53, 1]
  a := [422, 23, 406, 59, 256, 88, 453, 223, 457]
  b := [475, 167, 302, 453, 53, 216, 219, 147, 52]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2043289 : CertificateDedekindCriterionLists l 2043289 where
  n := 2
  a' := [246506, 408835, 58739, 1330511, 432983, 1178563, 898244, 2034432]
  b' := [1943426, 475815, 1953155, 554201, 300079, 1791947, 1586014, 531119, 1817241]
  k := [1752768, 628754, 704489, 424714, 446301, 1807564, 1643657, 870663, 1]
  f := [165086, 558796, 60503, 1097823, 508621, 1175139, 1106473, 396169, 342580, 1]
  g := [209781, 710083, 76883, 1395045, 646323, 1493293, 1406036, 503426, 435329, 1]
  h := [1607955, 1]
  a := [1828768, 1487299, 301586, 648462, 30873, 1780517, 380518, 1763841, 964284]
  b := [1795589, 1315268, 306900, 1400000, 872161, 963034, 355170, 1896634, 1079005]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 509, 2043289]
  exp := ![1, 1, 1]
  pdgood := [5, 509, 2043289]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp509.out
    exact hp2043289.out
  a := [39406981337, -594233366240, -476221820951, 1942824147906, 328246338330, -1774637454936, 229077278909, 426046673270, -115308607120]
  b := [-17103405416, -67255001121, 211071767482, 165404715131, -406729650056, -77787857228, 260978787016, -25243658687, -48370097683, 11530860712]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 509 T_ofList CD509
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2043289 T_ofList CD2043289

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

end VoightMaximalOrderD10R205

namespace VoightMaximalOrderD10R206

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3252762190625, [1, 10, 16, -33, -46, 29, 41, -6, -12, 0, 1], 1⟩
local notation "l" => [1, 10, 16, -33, -46, 29, 41, -6, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -10, -16, 33, 46, -29, -41, 6, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], ![0, -1, -10, -16, 33, 46, -29, -41, 6, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], ![0, -1, -10, -16, 33, 46, -29, -41, 6, 12], ![-12, -120, -193, 386, 536, -315, -446, 43, 103, 6]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], ![0, -1, -10, -16, 33, 46, -29, -41, 6, 12], ![-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], ![-6, -72, -216, 5, 662, 362, -561, -410, 115, 103]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], ![0, -1, -10, -16, 33, 46, -29, -41, 6, 12], ![-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], ![-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], ![-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], ![0, -1, -10, -16, 33, 46, -29, -41, 6, 12], ![-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], ![-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], ![-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115], ![-115, -1253, -2876, 2075, 8473, 1408, -7040, -3171, 1437, 826]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], ![0, -1, -10, -16, 33, 46, -29, -41, 6, 12], ![-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], ![-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], ![-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115], ![-115, -1253, -2876, 2075, 8473, 1408, -7040, -3171, 1437, 826], ![-826, -8375, -14469, 24382, 40071, -15481, -32458, -2084, 6741, 1437]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], ![0, -1, -10, -16, 33, 46, -29, -41, 6, 12], ![-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], ![-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], ![-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115], ![-115, -1253, -2876, 2075, 8473, 1408, -7040, -3171, 1437, 826], ![-826, -8375, -14469, 24382, 40071, -15481, -32458, -2084, 6741, 1437], ![-1437, -15196, -31367, 32952, 90484, -1602, -74398, -23836, 15160, 6741]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], ![0, -1, -10, -16, 33, 46, -29, -41, 6, 12], ![-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], ![-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], ![-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115], ![-115, -1253, -2876, 2075, 8473, 1408, -7040, -3171, 1437, 826], ![-826, -8375, -14469, 24382, 40071, -15481, -32458, -2084, 6741, 1437], ![-1437, -15196, -31367, 32952, 90484, -1602, -74398, -23836, 15160, 6741], ![-6741, -68847, -123052, 191086, 343038, -105005, -277983, -33952, 57056, 15160]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-103, -6, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-103, -6, -12, 0, -1], [-115, -103, -6, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-103, -6, -12, 0, -1], [-115, -103, -6, -12, 0, -1], [-826, -115, -103, -6, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-103, -6, -12, 0, -1], [-115, -103, -6, -12, 0, -1], [-826, -115, -103, -6, -12, 0, -1], [-1437, -826, -115, -103, -6, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-103, -6, -12, 0, -1], [-115, -103, -6, -12, 0, -1], [-826, -115, -103, -6, -12, 0, -1], [-1437, -826, -115, -103, -6, -12, 0, -1], [-6741, -1437, -826, -115, -103, -6, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -10, -16, 33, 46, -29, -41, 6, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], [0, -1, -10, -16, 33, 46, -29, -41, 6, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], [0, -1, -10, -16, 33, 46, -29, -41, 6, 12], [-12, -120, -193, 386, 536, -315, -446, 43, 103, 6]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], [0, -1, -10, -16, 33, 46, -29, -41, 6, 12], [-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], [-6, -72, -216, 5, 662, 362, -561, -410, 115, 103]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], [0, -1, -10, -16, 33, 46, -29, -41, 6, 12], [-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], [-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], [-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], [0, -1, -10, -16, 33, 46, -29, -41, 6, 12], [-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], [-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], [-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115], [-115, -1253, -2876, 2075, 8473, 1408, -7040, -3171, 1437, 826]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], [0, -1, -10, -16, 33, 46, -29, -41, 6, 12], [-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], [-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], [-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115], [-115, -1253, -2876, 2075, 8473, 1408, -7040, -3171, 1437, 826], [-826, -8375, -14469, 24382, 40071, -15481, -32458, -2084, 6741, 1437]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], [0, -1, -10, -16, 33, 46, -29, -41, 6, 12], [-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], [-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], [-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115], [-115, -1253, -2876, 2075, 8473, 1408, -7040, -3171, 1437, 826], [-826, -8375, -14469, 24382, 40071, -15481, -32458, -2084, 6741, 1437], [-1437, -15196, -31367, 32952, 90484, -1602, -74398, -23836, 15160, 6741]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -10, -16, 33, 46, -29, -41, 6, 12, 0], [0, -1, -10, -16, 33, 46, -29, -41, 6, 12], [-12, -120, -193, 386, 536, -315, -446, 43, 103, 6], [-6, -72, -216, 5, 662, 362, -561, -410, 115, 103], [-103, -1036, -1720, 3183, 4743, -2325, -3861, 57, 826, 115], [-115, -1253, -2876, 2075, 8473, 1408, -7040, -3171, 1437, 826], [-826, -8375, -14469, 24382, 40071, -15481, -32458, -2084, 6741, 1437], [-1437, -15196, -31367, 32952, 90484, -1602, -74398, -23836, 15160, 6741], [-6741, -68847, -123052, 191086, 343038, -105005, -277983, -33952, 57056, 15160]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1040883901 : Fact (Nat.Prime 1040883901) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 1]
  b' := [4, 1, 0, 4, 2]
  k := [1]
  f := [3, -2, 0, 13, 10, -1, -5, 2, 4]
  g := [4, 0, 2, 4, 0, 1]
  h := [4, 0, 2, 4, 0, 1]
  a := [2, 2, 4, 0, 4]
  b := [0, 2, 3, 2, 2, 3, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1040883901 : CertificateDedekindCriterionLists l 1040883901 where
  n := 2
  a' := [974891715, 199021517, 582048035, 570976564, 348327305, 836539254, 810859573, 648146868]
  b' := [299258183, 370426906, 824264357, 211287035, 866960775, 604922025, 985399537, 221233644, 621906282]
  k := [777369924, 419509735, 169363792, 531590179, 851627537, 598623251, 754023013, 1036654697, 1]
  f := [1311673, 964459, 1034023, 603484, 1646915, 1293923, 1915760, 1920346, 2110307, 1]
  g := [645653087, 474741441, 508983449, 297056501, 810671234, 636915509, 943006346, 945263597, 1038769299, 1]
  h := [2114602, 1]
  a := [679038672, 942941600, 343284300, 223267623, 965560071, 420066177, 957951311, 867293647, 48733201]
  b := [249745159, 590897023, 877404457, 660859379, 38210173, 467952775, 513386807, 955891652, 992150700]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1040883901]
  exp := ![1, 1]
  pdgood := [5, 1040883901]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1040883901.out
  a := [-73900370135, -71884072068, 730143232412, 311206952004, -1417267768580, -383840027082, 685236494676, 97348926140, -86431220460]
  b := [7910478964, 55775244657, 16943299884, -246611458336, -46410595213, 266316011900, 46190125299, -89267142378, -9734892614, 8643122046]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1040883901 T_ofList CD1040883901

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

end VoightMaximalOrderD10R206

namespace VoightMaximalOrderD10R207

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3256446753125, [1, -8, 11, 30, -32, -35, 27, 15, -9, -2, 1], 1⟩
local notation "l" => [1, -8, 11, 30, -32, -35, 27, 15, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -11, -30, 32, 35, -27, -15, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], ![-2, 15, -14, -71, 34, 102, -19, -57, 3, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], ![-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], ![-13, 102, -128, -404, 345, 489, -249, -214, 60, 29]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], ![-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], ![-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], ![-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], ![-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], ![-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], ![-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], ![-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], ![-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], ![-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], ![-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], ![-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283], ![-283, 2146, -2198, -9569, 5299, 12683, -2987, -6071, 483, 944]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], ![-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], ![-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], ![-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], ![-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283], ![-283, 2146, -2198, -9569, 5299, 12683, -2987, -6071, 483, 944], ![-944, 7269, -8238, -30518, 20639, 38339, -12805, -17147, 2425, 2371]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], ![-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], ![-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], ![-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], ![-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283], ![-283, 2146, -2198, -9569, 5299, 12683, -2987, -6071, 483, 944], ![-944, 7269, -8238, -30518, 20639, 38339, -12805, -17147, 2425, 2371], ![-2371, 18024, -18812, -79368, 45354, 103624, -25678, -48370, 4192, 7167]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], ![-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], ![-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], ![-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], ![-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283], ![-283, 2146, -2198, -9569, 5299, 12683, -2987, -6071, 483, 944], ![-944, 7269, -8238, -30518, 20639, 38339, -12805, -17147, 2425, 2371], ![-2371, 18024, -18812, -79368, 45354, 103624, -25678, -48370, 4192, 7167], ![-7167, 54965, -60813, -233822, 149976, 296199, -89885, -133183, 16133, 18526]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-118, -29, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-118, -29, -13, -2, -1], [-283, -118, -29, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-118, -29, -13, -2, -1], [-283, -118, -29, -13, -2, -1], [-944, -283, -118, -29, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-118, -29, -13, -2, -1], [-283, -118, -29, -13, -2, -1], [-944, -283, -118, -29, -13, -2, -1], [-2371, -944, -283, -118, -29, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-118, -29, -13, -2, -1], [-283, -118, -29, -13, -2, -1], [-944, -283, -118, -29, -13, -2, -1], [-2371, -944, -283, -118, -29, -13, -2, -1], [-7167, -2371, -944, -283, -118, -29, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -11, -30, 32, 35, -27, -15, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], [-2, 15, -14, -71, 34, 102, -19, -57, 3, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], [-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], [-13, 102, -128, -404, 345, 489, -249, -214, 60, 29]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], [-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], [-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], [-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], [-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], [-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], [-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], [-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], [-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], [-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], [-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], [-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283], [-283, 2146, -2198, -9569, 5299, 12683, -2987, -6071, 483, 944]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], [-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], [-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], [-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], [-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283], [-283, 2146, -2198, -9569, 5299, 12683, -2987, -6071, 483, 944], [-944, 7269, -8238, -30518, 20639, 38339, -12805, -17147, 2425, 2371]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], [-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], [-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], [-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], [-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283], [-283, 2146, -2198, -9569, 5299, 12683, -2987, -6071, 483, 944], [-944, 7269, -8238, -30518, 20639, 38339, -12805, -17147, 2425, 2371], [-2371, 18024, -18812, -79368, 45354, 103624, -25678, -48370, 4192, 7167]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -11, -30, 32, 35, -27, -15, 9, 2], [-2, 15, -14, -71, 34, 102, -19, -57, 3, 13], [-13, 102, -128, -404, 345, 489, -249, -214, 60, 29], [-29, 219, -217, -998, 524, 1360, -294, -684, 47, 118], [-118, 915, -1079, -3757, 2778, 4654, -1826, -2064, 378, 283], [-283, 2146, -2198, -9569, 5299, 12683, -2987, -6071, 483, 944], [-944, 7269, -8238, -30518, 20639, 38339, -12805, -17147, 2425, 2371], [-2371, 18024, -18812, -79368, 45354, 103624, -25678, -48370, 4192, 7167], [-7167, 54965, -60813, -233822, 149976, 296199, -89885, -133183, 16133, 18526]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp1699 : Fact (Nat.Prime 1699) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2]
  b' := [2, 4, 3, 3]
  k := [1]
  f := [0, 2, -2, -6, 8, 9, -5, -3, 5, 2]
  g := [1, 1, 0, 0, 4, 1]
  h := [1, 1, 0, 0, 4, 1]
  a := [2, 3, 0, 4, 4]
  b := [1, 0, 3, 0, 0, 2, 1, 4, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [5, 18, 3, 5, 2, 12, 13]
  b' := [17, 2, 6, 8, 2, 17, 1, 15]
  k := [4, 16, 13, 10, 12, 11, 1]
  f := [8, 5, 9, 7, 13, 11, 9, 9, 4, 1]
  g := [17, 4, 17, 12, 18, 12, 16, 14, 1]
  h := [9, 3, 1]
  a := [3, 2, 14, 12, 13, 5, 6, 11]
  b := [2, 10, 7, 14, 14, 1, 17, 9, 8]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1699 : CertificateDedekindCriterionLists l 1699 where
  n := 2
  a' := [1612, 1073, 265, 31, 921, 1633, 655]
  b' := [1597, 1408, 480, 182, 1019, 940, 40, 980]
  k := [185, 1187, 342, 663, 714, 1438, 1]
  f := [66, 484, 878, 499, 827, 445, 344, 231, 414, 1]
  g := [547, 1399, 593, 1297, 657, 544, 250, 718, 1]
  h := [205, 979, 1]
  a := [696, 1002, 314, 905, 1320, 1223, 820, 11]
  b := [882, 421, 951, 307, 1576, 1570, 1606, 825, 1688]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 19, 1699]
  exp := ![1, 1, 1]
  pdgood := [5, 19, 1699]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp1699.out
  a := [-168046035, -259494884, 777648035, 649626104, -893032881, -428612060, 370709954, 76891958, -49029360]
  b := [-21025930, 77787867, 103012512, -188610077, -137361446, 146861129, 62824437, -46123498, -8669783, 4902936]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1699 T_ofList CD1699

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

end VoightMaximalOrderD10R207

namespace VoightMaximalOrderD10R209

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3277687628125, [-1, -1, 14, -1, -36, 4, 32, -1, -10, 0, 1], 1⟩
local notation "l" => [-1, -1, 14, -1, -36, 4, 32, -1, -10, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -14, 1, 36, -4, -32, 1, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -14, 1, 36, -4, -32, 1, 10, 0], ![0, 1, 1, -14, 1, 36, -4, -32, 1, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -14, 1, 36, -4, -32, 1, 10, 0], ![0, 1, 1, -14, 1, 36, -4, -32, 1, 10], ![10, 10, -139, 11, 346, -39, -284, 6, 68, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -14, 1, 36, -4, -32, 1, 10, 0], ![0, 1, 1, -14, 1, 36, -4, -32, 1, 10], ![10, 10, -139, 11, 346, -39, -284, 6, 68, 1], ![1, 11, -4, -138, 47, 342, -71, -283, 16, 68]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -14, 1, 36, -4, -32, 1, 10, 0], ![0, 1, 1, -14, 1, 36, -4, -32, 1, 10], ![10, 10, -139, 11, 346, -39, -284, 6, 68, 1], ![1, 11, -4, -138, 47, 342, -71, -283, 16, 68], ![68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -14, 1, 36, -4, -32, 1, 10, 0], ![0, 1, 1, -14, 1, 36, -4, -32, 1, 10], ![10, 10, -139, 11, 346, -39, -284, 6, 68, 1], ![1, 11, -4, -138, 47, 342, -71, -283, 16, 68], ![68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16], ![16, 84, -155, -925, 640, 2246, -737, -1818, 157, 397]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -14, 1, 36, -4, -32, 1, 10, 0], ![0, 1, 1, -14, 1, 36, -4, -32, 1, 10], ![10, 10, -139, 11, 346, -39, -284, 6, 68, 1], ![1, 11, -4, -138, 47, 342, -71, -283, 16, 68], ![68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16], ![16, 84, -155, -925, 640, 2246, -737, -1818, 157, 397], ![397, 413, -5474, 242, 13367, -948, -10458, -340, 2152, 157]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -14, 1, 36, -4, -32, 1, 10, 0], ![0, 1, 1, -14, 1, 36, -4, -32, 1, 10], ![10, 10, -139, 11, 346, -39, -284, 6, 68, 1], ![1, 11, -4, -138, 47, 342, -71, -283, 16, 68], ![68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16], ![16, 84, -155, -925, 640, 2246, -737, -1818, 157, 397], ![397, 413, -5474, 242, 13367, -948, -10458, -340, 2152, 157], ![157, 554, -1785, -5317, 5894, 12739, -5972, -10301, 1230, 2152]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -14, 1, 36, -4, -32, 1, 10, 0], ![0, 1, 1, -14, 1, 36, -4, -32, 1, 10], ![10, 10, -139, 11, 346, -39, -284, 6, 68, 1], ![1, 11, -4, -138, 47, 342, -71, -283, 16, 68], ![68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16], ![16, 84, -155, -925, 640, 2246, -737, -1818, 157, 397], ![397, 413, -5474, 242, 13367, -948, -10458, -340, 2152, 157], ![157, 554, -1785, -5317, 5894, 12739, -5972, -10301, 1230, 2152], ![2152, 2309, -29574, 367, 72155, -2714, -56125, -3820, 11219, 1230]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1], [-16, -68, -1, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1], [-16, -68, -1, -10, 0, -1], [-397, -16, -68, -1, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1], [-16, -68, -1, -10, 0, -1], [-397, -16, -68, -1, -10, 0, -1], [-157, -397, -16, -68, -1, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1], [-16, -68, -1, -10, 0, -1], [-397, -16, -68, -1, -10, 0, -1], [-157, -397, -16, -68, -1, -10, 0, -1], [-2152, -157, -397, -16, -68, -1, -10, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -14, 1, 36, -4, -32, 1, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -14, 1, 36, -4, -32, 1, 10, 0], [0, 1, 1, -14, 1, 36, -4, -32, 1, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -14, 1, 36, -4, -32, 1, 10, 0], [0, 1, 1, -14, 1, 36, -4, -32, 1, 10], [10, 10, -139, 11, 346, -39, -284, 6, 68, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -14, 1, 36, -4, -32, 1, 10, 0], [0, 1, 1, -14, 1, 36, -4, -32, 1, 10], [10, 10, -139, 11, 346, -39, -284, 6, 68, 1], [1, 11, -4, -138, 47, 342, -71, -283, 16, 68]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -14, 1, 36, -4, -32, 1, 10, 0], [0, 1, 1, -14, 1, 36, -4, -32, 1, 10], [10, 10, -139, 11, 346, -39, -284, 6, 68, 1], [1, 11, -4, -138, 47, 342, -71, -283, 16, 68], [68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -14, 1, 36, -4, -32, 1, 10, 0], [0, 1, 1, -14, 1, 36, -4, -32, 1, 10], [10, 10, -139, 11, 346, -39, -284, 6, 68, 1], [1, 11, -4, -138, 47, 342, -71, -283, 16, 68], [68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16], [16, 84, -155, -925, 640, 2246, -737, -1818, 157, 397]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -14, 1, 36, -4, -32, 1, 10, 0], [0, 1, 1, -14, 1, 36, -4, -32, 1, 10], [10, 10, -139, 11, 346, -39, -284, 6, 68, 1], [1, 11, -4, -138, 47, 342, -71, -283, 16, 68], [68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16], [16, 84, -155, -925, 640, 2246, -737, -1818, 157, 397], [397, 413, -5474, 242, 13367, -948, -10458, -340, 2152, 157]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -14, 1, 36, -4, -32, 1, 10, 0], [0, 1, 1, -14, 1, 36, -4, -32, 1, 10], [10, 10, -139, 11, 346, -39, -284, 6, 68, 1], [1, 11, -4, -138, 47, 342, -71, -283, 16, 68], [68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16], [16, 84, -155, -925, 640, 2246, -737, -1818, 157, 397], [397, 413, -5474, 242, 13367, -948, -10458, -340, 2152, 157], [157, 554, -1785, -5317, 5894, 12739, -5972, -10301, 1230, 2152]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -14, 1, 36, -4, -32, 1, 10, 0], [0, 1, 1, -14, 1, 36, -4, -32, 1, 10], [10, 10, -139, 11, 346, -39, -284, 6, 68, 1], [1, 11, -4, -138, 47, 342, -71, -283, 16, 68], [68, 69, -941, 64, 2310, -225, -1834, -3, 397, 16], [16, 84, -155, -925, 640, 2246, -737, -1818, 157, 397], [397, 413, -5474, 242, 13367, -948, -10458, -340, 2152, 157], [157, 554, -1785, -5317, 5894, 12739, -5972, -10301, 1230, 2152], [2152, 2309, -29574, 367, 72155, -2714, -56125, -3820, 11219, 1230]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp22369 : Fact (Nat.Prime 22369) := fact_iff.2 (by norm_num)
instance hp46889 : Fact (Nat.Prime 46889) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [4, 3, 1, 1, 1]
  k := [1]
  f := [1, 1, -1, 1, 8, 0, -6, 1, 2]
  g := [2, 1, 2, 0, 0, 1]
  h := [2, 1, 2, 0, 0, 1]
  a := [4, 4, 4, 2]
  b := [1, 3, 3, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD22369 : CertificateDedekindCriterionLists l 22369 where
  n := 2
  a' := [13949, 10691, 10069, 9555, 14735, 15563, 8166, 7235]
  b' := [6482, 8114, 21154, 9978, 16250, 12916, 16263, 14018, 4167]
  k := [21730, 2094, 17011, 14379, 16990, 3315, 5556, 21435, 1]
  f := [308, 322, 110, 445, 162, 452, 67, 350, 458, 1]
  g := [14753, 15392, 5236, 21304, 7714, 21634, 3163, 16758, 21902, 1]
  h := [467, 1]
  a := [13838, 9555, 3285, 9639, 7504, 2361, 20979, 12968, 6163]
  b := [8481, 4319, 9651, 7276, 16469, 3089, 17377, 12721, 16206]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD46889 : CertificateDedekindCriterionLists l 46889 where
  n := 2
  a' := [3418, 39909, 36974, 26667, 12833, 41211, 14316, 37298]
  b' := [9806, 17306, 11881, 6416, 3530, 2380, 5097, 1415, 32325]
  k := [42214, 40682, 976, 24554, 5193, 32687, 16519, 14336, 1]
  f := [26815, 30776, 26410, 16274, 26258, 7718, 16282, 31140, 6073, 1]
  g := [31654, 36329, 31175, 19210, 30996, 9110, 19220, 36759, 7168, 1]
  h := [39721, 1]
  a := [9871, 6769, 12286, 33249, 20261, 27573, 42386, 37288, 17831]
  b := [4152, 14268, 45935, 22927, 9017, 4870, 29248, 28722, 29058]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 22369, 46889]
  exp := ![1, 1, 1]
  pdgood := [5, 22369, 46889]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp22369.out
    exact hp46889.out
  a := [-7890237251, 70375956300, 159967451879, -202045202952, -344625782750, 93110506404, 165883590100, -10197797420, -21914001620]
  b := [2645937046, 11600518239, -23930030139, -50625956709, 36595313813, 60320881854, -12008030173, -20971159334, 1019779742, 2191400162]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 22369 T_ofList CD22369
    exact satisfiesDedekindCriterion_of_certificate_lists T l 46889 T_ofList CD46889

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

end VoightMaximalOrderD10R209

end TraceEuclidean
