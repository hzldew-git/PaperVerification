import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk214
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

namespace VoightMaximalOrderD10R550

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6114952738933, [-1, -2, 9, 15, -24, -25, 26, 11, -10, -1, 1], 1⟩
local notation "l" => [-1, -2, 9, 15, -24, -25, 26, 11, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -9, -15, 24, 25, -26, -11, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -9, -15, 24, 25, -26, -11, 10, 1], ![1, 3, -7, -24, 9, 49, -1, -37, -1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -9, -15, 24, 25, -26, -11, 10, 1], ![1, 3, -7, -24, 9, 49, -1, -37, -1, 11], ![11, 23, -96, -172, 240, 284, -237, -122, 73, 10]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -9, -15, 24, 25, -26, -11, 10, 1], ![1, 3, -7, -24, 9, 49, -1, -37, -1, 11], ![11, 23, -96, -172, 240, 284, -237, -122, 73, 10], ![10, 31, -67, -246, 68, 490, 24, -347, -22, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -9, -15, 24, 25, -26, -11, 10, 1], ![1, 3, -7, -24, 9, 49, -1, -37, -1, 11], ![11, 23, -96, -172, 240, 284, -237, -122, 73, 10], ![10, 31, -67, -246, 68, 490, 24, -347, -22, 83], ![83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -9, -15, 24, 25, -26, -11, 10, 1], ![1, 3, -7, -24, 9, 49, -1, -37, -1, 11], ![11, 23, -96, -172, 240, 284, -237, -122, 73, 10], ![10, 31, -67, -246, 68, 490, 24, -347, -22, 83], ![83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61], ![61, 205, -373, -1631, 152, 3271, 557, -2339, -279, 544]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -9, -15, 24, 25, -26, -11, 10, 1], ![1, 3, -7, -24, 9, 49, -1, -37, -1, 11], ![11, 23, -96, -172, 240, 284, -237, -122, 73, 10], ![10, 31, -67, -246, 68, 490, 24, -347, -22, 83], ![83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61], ![61, 205, -373, -1631, 152, 3271, 557, -2339, -279, 544], ![544, 1149, -4691, -8533, 11425, 13752, -10873, -5427, 3101, 265]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -9, -15, 24, 25, -26, -11, 10, 1], ![1, 3, -7, -24, 9, 49, -1, -37, -1, 11], ![11, 23, -96, -172, 240, 284, -237, -122, 73, 10], ![10, 31, -67, -246, 68, 490, 24, -347, -22, 83], ![83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61], ![61, 205, -373, -1631, 152, 3271, 557, -2339, -279, 544], ![544, 1149, -4691, -8533, 11425, 13752, -10873, -5427, 3101, 265], ![265, 1074, -1236, -8666, -2173, 18050, 6862, -13788, -2777, 3366]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -9, -15, 24, 25, -26, -11, 10, 1], ![1, 3, -7, -24, 9, 49, -1, -37, -1, 11], ![11, 23, -96, -172, 240, 284, -237, -122, 73, 10], ![10, 31, -67, -246, 68, 490, 24, -347, -22, 83], ![83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61], ![61, 205, -373, -1631, 152, 3271, 557, -2339, -279, 544], ![544, 1149, -4691, -8533, 11425, 13752, -10873, -5427, 3101, 265], ![265, 1074, -1236, -8666, -2173, 18050, 6862, -13788, -2777, 3366], ![3366, 6997, -29220, -51726, 72118, 81977, -69466, -30164, 19872, 589]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-83, -10, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-83, -10, -11, -1, -1], [-61, -83, -10, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-83, -10, -11, -1, -1], [-61, -83, -10, -11, -1, -1], [-544, -61, -83, -10, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-83, -10, -11, -1, -1], [-61, -83, -10, -11, -1, -1], [-544, -61, -83, -10, -11, -1, -1], [-265, -544, -61, -83, -10, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-83, -10, -11, -1, -1], [-61, -83, -10, -11, -1, -1], [-544, -61, -83, -10, -11, -1, -1], [-265, -544, -61, -83, -10, -11, -1, -1], [-3366, -265, -544, -61, -83, -10, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -9, -15, 24, 25, -26, -11, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -9, -15, 24, 25, -26, -11, 10, 1], [1, 3, -7, -24, 9, 49, -1, -37, -1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -9, -15, 24, 25, -26, -11, 10, 1], [1, 3, -7, -24, 9, 49, -1, -37, -1, 11], [11, 23, -96, -172, 240, 284, -237, -122, 73, 10]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -9, -15, 24, 25, -26, -11, 10, 1], [1, 3, -7, -24, 9, 49, -1, -37, -1, 11], [11, 23, -96, -172, 240, 284, -237, -122, 73, 10], [10, 31, -67, -246, 68, 490, 24, -347, -22, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -9, -15, 24, 25, -26, -11, 10, 1], [1, 3, -7, -24, 9, 49, -1, -37, -1, 11], [11, 23, -96, -172, 240, 284, -237, -122, 73, 10], [10, 31, -67, -246, 68, 490, 24, -347, -22, 83], [83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -9, -15, 24, 25, -26, -11, 10, 1], [1, 3, -7, -24, 9, 49, -1, -37, -1, 11], [11, 23, -96, -172, 240, 284, -237, -122, 73, 10], [10, 31, -67, -246, 68, 490, 24, -347, -22, 83], [83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61], [61, 205, -373, -1631, 152, 3271, 557, -2339, -279, 544]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -9, -15, 24, 25, -26, -11, 10, 1], [1, 3, -7, -24, 9, 49, -1, -37, -1, 11], [11, 23, -96, -172, 240, 284, -237, -122, 73, 10], [10, 31, -67, -246, 68, 490, 24, -347, -22, 83], [83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61], [61, 205, -373, -1631, 152, 3271, 557, -2339, -279, 544], [544, 1149, -4691, -8533, 11425, 13752, -10873, -5427, 3101, 265]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -9, -15, 24, 25, -26, -11, 10, 1], [1, 3, -7, -24, 9, 49, -1, -37, -1, 11], [11, 23, -96, -172, 240, 284, -237, -122, 73, 10], [10, 31, -67, -246, 68, 490, 24, -347, -22, 83], [83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61], [61, 205, -373, -1631, 152, 3271, 557, -2339, -279, 544], [544, 1149, -4691, -8533, 11425, 13752, -10873, -5427, 3101, 265], [265, 1074, -1236, -8666, -2173, 18050, 6862, -13788, -2777, 3366]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -9, -15, 24, 25, -26, -11, 10, 1], [1, 3, -7, -24, 9, 49, -1, -37, -1, 11], [11, 23, -96, -172, 240, 284, -237, -122, 73, 10], [10, 31, -67, -246, 68, 490, 24, -347, -22, 83], [83, 176, -716, -1312, 1746, 2143, -1668, -889, 483, 61], [61, 205, -373, -1631, 152, 3271, 557, -2339, -279, 544], [544, 1149, -4691, -8533, 11425, 13752, -10873, -5427, 3101, 265], [265, 1074, -1236, -8666, -2173, 18050, 6862, -13788, -2777, 3366], [3366, 6997, -29220, -51726, 72118, 81977, -69466, -30164, 19872, 589]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp43 : Fact (Nat.Prime 43) := fact_iff.2 (by norm_num)
instance hp3307167517 : Fact (Nat.Prime 3307167517) := fact_iff.2 (by norm_num)

def CD43 : CertificateDedekindCriterionLists l 43 where
  n := 2
  a' := [10, 27, 28, 33, 23, 21, 39]
  b' := [39, 32, 39, 0, 1, 14, 15, 22]
  k := [27, 36, 30, 28, 30, 6, 1]
  f := [10, 22, 14, 13, 12, 11, 18, 15, 11, 1]
  g := [39, 22, 16, 24, 4, 32, 20, 24, 1]
  h := [11, 18, 1]
  a := [32, 5, 11, 7, 15, 25, 15, 36]
  b := [26, 9, 41, 15, 5, 31, 40, 23, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3307167517 : CertificateDedekindCriterionLists l 3307167517 where
  n := 2
  a' := [3251650903, 298465324, 180467131, 486558578, 2475319195, 1410871745, 2415540686, 1665793528]
  b' := [1735681302, 3272945986, 1432697899, 2521403060, 2275368833, 2234838198, 1284529872, 1877752090, 1284764060]
  k := [38386215, 2288771828, 1883869617, 956393434, 549198580, 578877719, 3124617300, 3130643069, 1]
  f := [63783003, 107348441, 544846876, 1348555074, 236824199, 334205720, 1485646042, 1434984859, 824436323, 1]
  g := [121102025, 203817835, 1034477163, 2560443105, 449647847, 634541924, 2820731788, 2724543593, 1565321534, 1]
  h := [1741845982, 1]
  a := [165494853, 2607589591, 119510737, 433219210, 3018161979, 2002091575, 495277372, 2689388413, 2769704326]
  b := [2580945520, 2500682411, 3164447961, 2547798063, 2809601419, 3263890521, 146624918, 218978288, 537463191]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![43, 3307167517]
  exp := ![1, 1]
  pdgood := [43, 3307167517]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp43.out
    exact hp3307167517.out
  a := [7188361019451, -83742967666254, 39479138611690, 259670872104820, -170877736646674, -163961257958210, 114087420906852, 19970388475428, -15292933374120]
  b := [-3665284611341, 1695561311607, 29142170997229, -15881891685774, -50453302241832, 30420656303624, 22657443772112, -14405261281122, -2149968181284, 1529293337412]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 43 T_ofList CD43
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3307167517 T_ofList CD3307167517

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

end VoightMaximalOrderD10R550

namespace VoightMaximalOrderD10R554

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6140781355508, [-1, -7, -1, 45, -9, -53, 15, 22, -7, -3, 1], 1⟩
local notation "l" => [-1, -7, -1, 45, -9, -53, 15, 22, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -45, 9, 53, -15, -22, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -45, 9, 53, -15, -22, 7, 3], ![3, 22, 10, -134, -18, 168, 8, -81, -1, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -45, 9, 53, -15, -22, 7, 3], ![3, 22, 10, -134, -18, 168, 8, -81, -1, 16], ![16, 115, 38, -710, 10, 830, -72, -344, 31, 47]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -45, 9, 53, -15, -22, 7, 3], ![3, 22, 10, -134, -18, 168, 8, -81, -1, 16], ![16, 115, 38, -710, 10, 830, -72, -344, 31, 47], ![47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -45, 9, 53, -15, -22, 7, 3], ![3, 22, 10, -134, -18, 168, 8, -81, -1, 16], ![16, 115, 38, -710, 10, 830, -72, -344, 31, 47], ![47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], ![172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -45, 9, 53, -15, -22, 7, 3], ![3, 22, 10, -134, -18, 168, 8, -81, -1, 16], ![16, 115, 38, -710, 10, 830, -72, -344, 31, 47], ![47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], ![172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501], ![501, 3679, 1752, -22028, -3069, 26024, 1314, -11101, -152, 1601]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -45, 9, 53, -15, -22, 7, 3], ![3, 22, 10, -134, -18, 168, 8, -81, -1, 16], ![16, 115, 38, -710, 10, 830, -72, -344, 31, 47], ![47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], ![172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501], ![501, 3679, 1752, -22028, -3069, 26024, 1314, -11101, -152, 1601], ![1601, 11708, 5280, -70293, -7619, 81784, 2009, -33908, 106, 4651]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -45, 9, 53, -15, -22, 7, 3], ![3, 22, 10, -134, -18, 168, 8, -81, -1, 16], ![16, 115, 38, -710, 10, 830, -72, -344, 31, 47], ![47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], ![172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501], ![501, 3679, 1752, -22028, -3069, 26024, 1314, -11101, -152, 1601], ![1601, 11708, 5280, -70293, -7619, 81784, 2009, -33908, 106, 4651], ![4651, 34158, 16359, -204015, -28434, 238884, 12019, -100313, -1351, 14059]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -45, 9, 53, -15, -22, 7, 3], ![3, 22, 10, -134, -18, 168, 8, -81, -1, 16], ![16, 115, 38, -710, 10, 830, -72, -344, 31, 47], ![47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], ![172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501], ![501, 3679, 1752, -22028, -3069, 26024, 1314, -11101, -152, 1601], ![1601, 11708, 5280, -70293, -7619, 81784, 2009, -33908, 106, 4651], ![4651, 34158, 16359, -204015, -28434, 238884, 12019, -100313, -1351, 14059], ![14059, 103064, 48217, -616296, -77484, 716693, 27999, -297279, -1900, 40826]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-172, -47, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-172, -47, -16, -3, -1], [-501, -172, -47, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-172, -47, -16, -3, -1], [-501, -172, -47, -16, -3, -1], [-1601, -501, -172, -47, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-172, -47, -16, -3, -1], [-501, -172, -47, -16, -3, -1], [-1601, -501, -172, -47, -16, -3, -1], [-4651, -1601, -501, -172, -47, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-172, -47, -16, -3, -1], [-501, -172, -47, -16, -3, -1], [-1601, -501, -172, -47, -16, -3, -1], [-4651, -1601, -501, -172, -47, -16, -3, -1], [-14059, -4651, -1601, -501, -172, -47, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -45, 9, 53, -15, -22, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -45, 9, 53, -15, -22, 7, 3], [3, 22, 10, -134, -18, 168, 8, -81, -1, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -45, 9, 53, -15, -22, 7, 3], [3, 22, 10, -134, -18, 168, 8, -81, -1, 16], [16, 115, 38, -710, 10, 830, -72, -344, 31, 47]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -45, 9, 53, -15, -22, 7, 3], [3, 22, 10, -134, -18, 168, 8, -81, -1, 16], [16, 115, 38, -710, 10, 830, -72, -344, 31, 47], [47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -45, 9, 53, -15, -22, 7, 3], [3, 22, 10, -134, -18, 168, 8, -81, -1, 16], [16, 115, 38, -710, 10, 830, -72, -344, 31, 47], [47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], [172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -45, 9, 53, -15, -22, 7, 3], [3, 22, 10, -134, -18, 168, 8, -81, -1, 16], [16, 115, 38, -710, 10, 830, -72, -344, 31, 47], [47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], [172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501], [501, 3679, 1752, -22028, -3069, 26024, 1314, -11101, -152, 1601]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -45, 9, 53, -15, -22, 7, 3], [3, 22, 10, -134, -18, 168, 8, -81, -1, 16], [16, 115, 38, -710, 10, 830, -72, -344, 31, 47], [47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], [172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501], [501, 3679, 1752, -22028, -3069, 26024, 1314, -11101, -152, 1601], [1601, 11708, 5280, -70293, -7619, 81784, 2009, -33908, 106, 4651]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -45, 9, 53, -15, -22, 7, 3], [3, 22, 10, -134, -18, 168, 8, -81, -1, 16], [16, 115, 38, -710, 10, 830, -72, -344, 31, 47], [47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], [172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501], [501, 3679, 1752, -22028, -3069, 26024, 1314, -11101, -152, 1601], [1601, 11708, 5280, -70293, -7619, 81784, 2009, -33908, 106, 4651], [4651, 34158, 16359, -204015, -28434, 238884, 12019, -100313, -1351, 14059]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -45, 9, 53, -15, -22, 7, 3], [3, 22, 10, -134, -18, 168, 8, -81, -1, 16], [16, 115, 38, -710, 10, 830, -72, -344, 31, 47], [47, 345, 162, -2077, -287, 2501, 125, -1106, -15, 172], [172, 1251, 517, -7578, -529, 8829, -79, -3659, 98, 501], [501, 3679, 1752, -22028, -3069, 26024, 1314, -11101, -152, 1601], [1601, 11708, 5280, -70293, -7619, 81784, 2009, -33908, 106, 4651], [4651, 34158, 16359, -204015, -28434, 238884, 12019, -100313, -1351, 14059], [14059, 103064, 48217, -616296, -77484, 716693, 27999, -297279, -1900, 40826]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp40519 : Fact (Nat.Prime 40519) := fact_iff.2 (by norm_num)
instance hp37888283 : Fact (Nat.Prime 37888283) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 3
  a' := [0, 0, 1, 0, 1]
  b' := [1, 0, 1, 1, 0, 1, 1]
  k := [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
  f := [1, 4, 1, -22, 5, 27, -7, -10, 4, 2]
  g := [1, 1, 0, 0, 1, 1, 0, 1, 1]
  h := [1, 0, 1]
  a := [1, 0, 0, 1, 1, 1, 0, 1]
  b := [0, 0, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD40519 : CertificateDedekindCriterionLists l 40519 where
  n := 2
  a' := [32548, 36143, 34670, 9226, 39729, 24664, 18753, 39184]
  b' := [39417, 34652, 28675, 26783, 9914, 7483, 31474, 6616, 27161]
  k := [2211, 19815, 34892, 25456, 9328, 10205, 7896, 11712, 1]
  f := [12585, 898, 6313, 12900, 2243, 6869, 11404, 1253, 9282, 1]
  g := [35407, 2524, 17761, 36292, 6308, 19325, 32083, 3523, 26114, 1]
  h := [14402, 1]
  a := [17685, 17725, 29493, 14943, 39710, 7858, 17444, 24476, 31784]
  b := [39765, 771, 19658, 37816, 12030, 8513, 18214, 31974, 8735]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD37888283 : CertificateDedekindCriterionLists l 37888283 where
  n := 2
  a' := [36777095, 29353255, 18938677, 10381161, 19955051, 31605026, 25079416, 13258254]
  b' := [26751807, 4386369, 27887002, 35011405, 11704419, 32029834, 27771869, 13411816, 23785716]
  k := [25856354, 3919976, 36032590, 16821639, 33273111, 33695109, 28674402, 20694350, 1]
  f := [2052437, 8500175, 6864511, 2326415, 697302, 1088810, 5739710, 6985101, 6646288, 1]
  g := [9045438, 37461712, 30253060, 10252902, 3073127, 4798570, 25295875, 30784522, 29291315, 1]
  h := [8596965, 1]
  a := [14129813, 6334719, 24555348, 34034653, 10774064, 1868320, 12242173, 14240023, 23153785]
  b := [14460222, 21486150, 25591098, 17632153, 5450730, 2056142, 36767944, 7069748, 14734498]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 40519, 37888283]
  exp := ![1, 1, 1]
  pdgood := [2, 40519, 37888283]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp40519.out
    exact hp37888283.out
  a := [81308680324577, -351446024955908, -43352961568568, 763650022627308, -187995268336927, -462246759061084, 155219655797197, 83135870444682, -30037585632560]
  b := [-12054153000333, -27658061616495, 121453132017626, 1051753380636, -153848727931773, 34174068509053, 66109357732570, -19666195891175, -9214714613445, 3003758563256]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 40519 T_ofList CD40519
    exact satisfiesDedekindCriterion_of_certificate_lists T l 37888283 T_ofList CD37888283

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

end VoightMaximalOrderD10R554

namespace VoightMaximalOrderD10R555

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6144743194925, [1, -4, -8, 27, 25, -40, -17, 24, 1, -5, 1], 1⟩
local notation "l" => [1, -4, -8, 27, 25, -40, -17, 24, 1, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 8, -27, -25, 40, 17, -24, -1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], ![-5, 19, 44, -127, -152, 175, 125, -103, -29, 24]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], ![-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], ![-24, 91, 211, -604, -727, 808, 583, -451, -127, 91]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], ![-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], ![-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], ![-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], ![-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], ![-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], ![-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], ![-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], ![-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], ![-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], ![-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], ![-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098], ![-1098, 4064, 10005, -26682, -35487, 33474, 28907, -17863, -6615, 3561]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], ![-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], ![-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], ![-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], ![-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098], ![-1098, 4064, 10005, -26682, -35487, 33474, 28907, -17863, -6615, 3561], ![-3561, 13146, 32552, -86142, -115707, 106953, 94011, -56557, -21424, 11190]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], ![-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], ![-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], ![-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], ![-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098], ![-1098, 4064, 10005, -26682, -35487, 33474, 28907, -17863, -6615, 3561], ![-3561, 13146, 32552, -86142, -115707, 106953, 94011, -56557, -21424, 11190], ![-11190, 41199, 102666, -269578, -365892, 331893, 297183, -174549, -67747, 34526]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], ![-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], ![-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], ![-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], ![-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098], ![-1098, 4064, 10005, -26682, -35487, 33474, 28907, -17863, -6615, 3561], ![-3561, 13146, 32552, -86142, -115707, 106953, 94011, -56557, -21424, 11190], ![-11190, 41199, 102666, -269578, -365892, 331893, 297183, -174549, -67747, 34526], ![-34526, 126914, 317407, -829536, -1132728, 1015148, 918835, -531441, -209075, 104883]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-328, -91, -24, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-328, -91, -24, -5, -1], [-1098, -328, -91, -24, -5, -1]], ![[], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-328, -91, -24, -5, -1], [-1098, -328, -91, -24, -5, -1], [-3561, -1098, -328, -91, -24, -5, -1]], ![[], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-328, -91, -24, -5, -1], [-1098, -328, -91, -24, -5, -1], [-3561, -1098, -328, -91, -24, -5, -1], [-11190, -3561, -1098, -328, -91, -24, -5, -1]], ![[], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-328, -91, -24, -5, -1], [-1098, -328, -91, -24, -5, -1], [-3561, -1098, -328, -91, -24, -5, -1], [-11190, -3561, -1098, -328, -91, -24, -5, -1], [-34526, -11190, -3561, -1098, -328, -91, -24, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 8, -27, -25, 40, 17, -24, -1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], [-5, 19, 44, -127, -152, 175, 125, -103, -29, 24]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], [-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], [-24, 91, 211, -604, -727, 808, 583, -451, -127, 91]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], [-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], [-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], [-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], [-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], [-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], [-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], [-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], [-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], [-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], [-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], [-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098], [-1098, 4064, 10005, -26682, -35487, 33474, 28907, -17863, -6615, 3561]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], [-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], [-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], [-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], [-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098], [-1098, 4064, 10005, -26682, -35487, 33474, 28907, -17863, -6615, 3561], [-3561, 13146, 32552, -86142, -115707, 106953, 94011, -56557, -21424, 11190]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], [-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], [-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], [-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], [-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098], [-1098, 4064, 10005, -26682, -35487, 33474, 28907, -17863, -6615, 3561], [-3561, 13146, 32552, -86142, -115707, 106953, 94011, -56557, -21424, 11190], [-11190, 41199, 102666, -269578, -365892, 331893, 297183, -174549, -67747, 34526]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 8, -27, -25, 40, 17, -24, -1, 5], [-5, 19, 44, -127, -152, 175, 125, -103, -29, 24], [-24, 91, 211, -604, -727, 808, 583, -451, -127, 91], [-91, 340, 819, -2246, -2879, 2913, 2355, -1601, -542, 328], [-328, 1221, 2964, -8037, -10446, 10241, 8489, -5517, -1929, 1098], [-1098, 4064, 10005, -26682, -35487, 33474, 28907, -17863, -6615, 3561], [-3561, 13146, 32552, -86142, -115707, 106953, 94011, -56557, -21424, 11190], [-11190, 41199, 102666, -269578, -365892, 331893, 297183, -174549, -67747, 34526], [-34526, 126914, 317407, -829536, -1132728, 1015148, 918835, -531441, -209075, 104883]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp139 : Fact (Nat.Prime 139) := fact_iff.2 (by norm_num)
instance hp3727 : Fact (Nat.Prime 3727) := fact_iff.2 (by norm_num)
instance hp24971 : Fact (Nat.Prime 24971) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 3
  a' := [0, 3, 3, 3, 0, 2, 2]
  b' := [2, 3, 1, 3, 4, 3, 0, 1]
  k := [1, 3, 3, 1, 4, 3, 0, 4, 4, 2, 3, 1, 3, 1, 1]
  f := [0, 2, 4, -3, -2, 11, 5, -2, 2, 2]
  g := [1, 3, 2, 3, 4, 0, 4, 2, 1]
  h := [1, 3, 1]
  a := [1, 4, 2, 0, 3, 2, 0, 2]
  b := [1, 0, 1, 2, 4, 3, 3, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [18, 5, 8, 8, 15, 3, 7, 8]
  b' := [12, 1, 16, 8, 16, 12, 13, 10, 16]
  k := [5, 13, 17, 15, 6, 4, 14, 10, 1]
  f := [1, 2, 2, 0, 0, 4, 3, 1, 2, 1]
  g := [10, 12, 9, 9, 8, 14, 13, 15, 12, 1]
  h := [2, 1]
  a := [16, 5, 5, 10, 15, 16, 0, 0, 14]
  b := [8, 0, 9, 17, 10, 5, 17, 7, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD139 : CertificateDedekindCriterionLists l 139 where
  n := 2
  a' := [2, 32, 62, 49, 64, 27, 19, 79]
  b' := [19, 18, 80, 97, 40, 91, 78, 116, 53]
  k := [66, 85, 24, 14, 60, 64, 113, 32, 1]
  f := [11, 34, 22, 16, 6, 47, 48, 29, 31, 1]
  g := [30, 92, 58, 43, 16, 127, 128, 77, 83, 1]
  h := [51, 1]
  a := [111, 32, 38, 121, 21, 53, 6, 72, 62]
  b := [52, 120, 30, 131, 134, 131, 25, 94, 77]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3727 : CertificateDedekindCriterionLists l 3727 where
  n := 2
  a' := [1127, 3088, 1642, 3406, 806, 391, 3049, 991]
  b' := [2055, 995, 2989, 87, 3502, 110, 3136, 3485, 304]
  k := [887, 244, 1214, 103, 3488, 1057, 3053, 967, 1]
  f := [1087, 1363, 2464, 2900, 627, 335, 561, 2342, 419, 1]
  g := [1250, 1567, 2833, 3334, 720, 385, 645, 2693, 481, 1]
  h := [3241, 1]
  a := [1982, 2740, 312, 811, 73, 1833, 295, 1365, 2534]
  b := [2239, 154, 2239, 168, 1558, 2084, 726, 2936, 1193]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD24971 : CertificateDedekindCriterionLists l 24971 where
  n := 2
  a' := [8231, 4248, 15606, 17905, 23293, 17692, 23713, 1551]
  b' := [15013, 11932, 2379, 24115, 9912, 7149, 19211, 4855, 16475]
  k := [10367, 2914, 12732, 15773, 17617, 18566, 13553, 24725, 1]
  f := [6643, 6013, 7012, 1564, 1818, 3751, 8129, 4484, 6240, 1]
  g := [13159, 11910, 13889, 3097, 3601, 7430, 16102, 8881, 12360, 1]
  h := [12606, 1]
  a := [10506, 9236, 20650, 17450, 1366, 15097, 1039, 10203, 8553]
  b := [12202, 7020, 8910, 6088, 6133, 21596, 11362, 19912, 16418]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![5, 19, 139, 3727, 24971]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [5, 19, 139, 3727, 24971]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp139.out
    exact hp3727.out
    exact hp24971.out
  a := [-3028637131807, -31130455802032, -26064116747094, 83985406667794, 36637887580977, -73611273356636, -2172639923985, 20264743035280, -4635124594700]
  b := [-1064396442698, -496391047909, 11103237105874, 7803301167306, -17319867353972, -6384377358305, 10653559915058, 280300602249, -2258230533263, 463512459470]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 139 T_ofList CD139
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3727 T_ofList CD3727
    exact satisfiesDedekindCriterion_of_certificate_lists T l 24971 T_ofList CD24971

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

end VoightMaximalOrderD10R555

namespace VoightMaximalOrderD10R557

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6156595900304, [11, -20, -63, 107, 28, -96, 12, 30, -8, -3, 1], 1⟩
local notation "l" => [11, -20, -63, 107, 28, -96, 12, 30, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 20, 63, -107, -28, 96, -12, -30, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], ![-33, 49, 209, -258, -191, 260, 60, -102, -6, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], ![-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], ![-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], ![-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], ![-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], ![-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], ![-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], ![-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], ![-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], ![-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], ![-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], ![-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], ![-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], ![-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417], ![-4587, 6481, 29156, -33259, -26617, 31605, 8350, -10952, -833, 1309]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], ![-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], ![-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], ![-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], ![-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417], ![-4587, 6481, 29156, -33259, -26617, 31605, 8350, -10952, -833, 1309], ![-14399, 21593, 88948, -110907, -69911, 99047, 15897, -30920, -480, 3094]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], ![-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], ![-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], ![-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], ![-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417], ![-4587, 6481, 29156, -33259, -26617, 31605, 8350, -10952, -833, 1309], ![-14399, 21593, 88948, -110907, -69911, 99047, 15897, -30920, -480, 3094], ![-34034, 47481, 216515, -242110, -197539, 227113, 61919, -76923, -6168, 8802]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], ![-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], ![-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], ![-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], ![-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417], ![-4587, 6481, 29156, -33259, -26617, 31605, 8350, -10952, -833, 1309], ![-14399, 21593, 88948, -110907, -69911, 99047, 15897, -30920, -480, 3094], ![-34034, 47481, 216515, -242110, -197539, 227113, 61919, -76923, -6168, 8802], ![-96822, 142006, 602007, -725299, -488566, 647453, 121489, -202141, -6507, 20238]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-169, -45, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-169, -45, -17, -3, -1], [-417, -169, -45, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-169, -45, -17, -3, -1], [-417, -169, -45, -17, -3, -1], [-1309, -417, -169, -45, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-169, -45, -17, -3, -1], [-417, -169, -45, -17, -3, -1], [-1309, -417, -169, -45, -17, -3, -1], [-3094, -1309, -417, -169, -45, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-169, -45, -17, -3, -1], [-417, -169, -45, -17, -3, -1], [-1309, -417, -169, -45, -17, -3, -1], [-3094, -1309, -417, -169, -45, -17, -3, -1], [-8802, -3094, -1309, -417, -169, -45, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 20, 63, -107, -28, 96, -12, -30, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], [-33, 49, 209, -258, -191, 260, 60, -102, -6, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], [-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], [-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], [-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], [-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], [-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], [-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], [-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], [-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], [-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], [-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], [-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], [-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], [-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417], [-4587, 6481, 29156, -33259, -26617, 31605, 8350, -10952, -833, 1309]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], [-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], [-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], [-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], [-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417], [-4587, 6481, 29156, -33259, -26617, 31605, 8350, -10952, -833, 1309], [-14399, 21593, 88948, -110907, -69911, 99047, 15897, -30920, -480, 3094]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], [-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], [-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], [-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], [-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417], [-4587, 6481, 29156, -33259, -26617, 31605, 8350, -10952, -833, 1309], [-14399, 21593, 88948, -110907, -69911, 99047, 15897, -30920, -480, 3094], [-34034, 47481, 216515, -242110, -197539, 227113, 61919, -76923, -6168, 8802]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 20, 63, -107, -28, 96, -12, -30, 8, 3], [-33, 49, 209, -258, -191, 260, 60, -102, -6, 17], [-187, 307, 1120, -1610, -734, 1441, 56, -450, 34, 45], [-495, 713, 3142, -3695, -2870, 3586, 901, -1294, -90, 169], [-1859, 2885, 11360, -14941, -8427, 13354, 1558, -4169, 58, 417], [-4587, 6481, 29156, -33259, -26617, 31605, 8350, -10952, -833, 1309], [-14399, 21593, 88948, -110907, -69911, 99047, 15897, -30920, -480, 3094], [-34034, 47481, 216515, -242110, -197539, 227113, 61919, -76923, -6168, 8802], [-96822, 142006, 602007, -725299, -488566, 647453, 121489, -202141, -6507, 20238]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp37 : Fact (Nat.Prime 37) := fact_iff.2 (by norm_num)
instance hp59 : Fact (Nat.Prime 59) := fact_iff.2 (by norm_num)
instance hp883 : Fact (Nat.Prime 883) := fact_iff.2 (by norm_num)
instance hp199621 : Fact (Nat.Prime 199621) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 3
  a' := [1]
  b' := [0, 1, 1]
  k := [1, 0, 1, 0, 0, 0, 0, 0, 1]
  f := [-5, 10, 32, -53, -13, 49, -5, -14, 5, 2]
  g := [1, 0, 0, 1, 1, 1, 1]
  h := [1, 0, 1, 0, 1]
  a := [1, 1, 0, 1]
  b := [0, 1, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD37 : CertificateDedekindCriterionLists l 37 where
  n := 2
  a' := [22, 17, 28, 18, 33, 17, 3, 2]
  b' := [3, 22, 32, 22, 12, 23, 5, 29, 8]
  k := [11, 32, 10, 18, 19, 33, 1, 32, 1]
  f := [0, 1, 2, -2, 0, 3, 1, 1, 2, 1]
  g := [11, 6, 5, 28, 0, 15, 34, 33, 33, 1]
  h := [1, 1]
  a := [32, 5, 9, 1, 35, 6, 16, 19, 14]
  b := [27, 16, 3, 24, 18, 32, 19, 8, 23]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD59 : CertificateDedekindCriterionLists l 59 where
  n := 2
  a' := [56, 31, 47, 19, 12, 54, 2, 31]
  b' := [24, 5, 47, 39, 14, 25, 5, 27, 49]
  k := [14, 29, 42, 32, 17, 17, 18, 13, 1]
  f := [5, 16, 42, 18, 12, 52, 44, 28, 5, 1]
  g := [6, 18, 47, 22, 14, 58, 50, 32, 5, 1]
  h := [51, 1]
  a := [10, 38, 57, 29, 1, 38, 47, 21, 7]
  b := [41, 35, 4, 55, 1, 7, 40, 38, 52]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD883 : CertificateDedekindCriterionLists l 883 where
  n := 2
  a' := [667, 549, 598, 326, 367, 449, 516, 439]
  b' := [536, 666, 18, 149, 672, 115, 392, 407, 638]
  k := [523, 416, 142, 187, 16, 842, 605, 423, 1]
  f := [563, 164, 146, 35, 236, 609, 10, 434, 160, 1]
  g := [742, 215, 192, 46, 311, 802, 12, 572, 210, 1]
  h := [670, 1]
  a := [858, 715, 354, 788, 613, 418, 731, 347, 283]
  b := [445, 655, 317, 759, 169, 865, 722, 558, 600]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD199621 : CertificateDedekindCriterionLists l 199621 where
  n := 2
  a' := [112115, 47803, 9205, 198837, 147863, 158264, 114910, 104273]
  b' := [119873, 46459, 172397, 28470, 41747, 185745, 66009, 42243, 165855]
  k := [132438, 169035, 105868, 38421, 90387, 63785, 168722, 47257, 1]
  f := [130567, 45825, 139797, 82826, 121939, 166635, 170294, 146074, 20831, 1]
  g := [148098, 51977, 158567, 93946, 138311, 189008, 193158, 165686, 23627, 1]
  h := [175991, 1]
  a := [24826, 128823, 118952, 188217, 197152, 146077, 125904, 4184, 38260]
  b := [145550, 138599, 8661, 178488, 86234, 21627, 93104, 173541, 161361]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![2, 37, 59, 883, 199621]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [2, 37, 59, 883, 199621]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp37.out
    exact hp59.out
    exact hp883.out
    exact hp199621.out
  a := [-18073147066982, -127168863885762, 200223693507921, 241781497013802, -262051048788488, -116424817788128, 107064024896699, 15819029461452, -13177477058260]
  b := [-9978709611217, 10996142480480, 64788321689055, -50912399370691, -60601928375441, 43949106352860, 19421858061362, -13407603576867, -1977227257893, 1317747705826]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 37 T_ofList CD37
    exact satisfiesDedekindCriterion_of_certificate_lists T l 59 T_ofList CD59
    exact satisfiesDedekindCriterion_of_certificate_lists T l 883 T_ofList CD883
    exact satisfiesDedekindCriterion_of_certificate_lists T l 199621 T_ofList CD199621

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

end VoightMaximalOrderD10R557

end TraceEuclidean
