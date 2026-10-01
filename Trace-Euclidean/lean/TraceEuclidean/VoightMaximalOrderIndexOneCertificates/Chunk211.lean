import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk207
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

namespace VoightMaximalOrderD10R480

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5534452170893, [-1, -3, 7, 23, -9, -39, 9, 23, -7, -3, 1], 1⟩
local notation "l" => [-1, -3, 7, 23, -9, -39, 9, 23, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -23, 9, 39, -9, -23, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -23, 9, 39, -9, -23, 7, 3], ![3, 10, -18, -76, 4, 126, 12, -78, -2, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -23, 9, 39, -9, -23, 7, 3], ![3, 10, -18, -76, 4, 126, 12, -78, -2, 16], ![16, 51, -102, -386, 68, 628, -18, -356, 34, 46]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -23, 9, 39, -9, -23, 7, 3], ![3, 10, -18, -76, 4, 126, 12, -78, -2, 16], ![16, 51, -102, -386, 68, 628, -18, -356, 34, 46], ![46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -23, 9, 39, -9, -23, 7, 3], ![3, 10, -18, -76, 4, 126, 12, -78, -2, 16], ![16, 51, -102, -386, 68, 628, -18, -356, 34, 46], ![46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], ![172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -23, 9, 39, -9, -23, 7, 3], ![3, 10, -18, -76, 4, 126, 12, -78, -2, 16], ![16, 51, -102, -386, 68, 628, -18, -356, 34, 46], ![46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], ![172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482], ![482, 1618, -2812, -12136, 111, 19186, 2398, -10772, -368, 1574]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -23, 9, 39, -9, -23, 7, 3], ![3, 10, -18, -76, 4, 126, 12, -78, -2, 16], ![16, 51, -102, -386, 68, 628, -18, -356, 34, 46], ![46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], ![172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482], ![482, 1618, -2812, -12136, 111, 19186, 2398, -10772, -368, 1574], ![1574, 5204, -9400, -39014, 2030, 61497, 5020, -33804, 246, 4354]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -23, 9, 39, -9, -23, 7, 3], ![3, 10, -18, -76, 4, 126, 12, -78, -2, 16], ![16, 51, -102, -386, 68, 628, -18, -356, 34, 46], ![46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], ![172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482], ![482, 1618, -2812, -12136, 111, 19186, 2398, -10772, -368, 1574], ![1574, 5204, -9400, -39014, 2030, 61497, 5020, -33804, 246, 4354], ![4354, 14636, -25274, -109542, 172, 171836, 22311, -95122, -3326, 13308]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -23, 9, 39, -9, -23, 7, 3], ![3, 10, -18, -76, 4, 126, 12, -78, -2, 16], ![16, 51, -102, -386, 68, 628, -18, -356, 34, 46], ![46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], ![172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482], ![482, 1618, -2812, -12136, 111, 19186, 2398, -10772, -368, 1574], ![1574, 5204, -9400, -39014, 2030, 61497, 5020, -33804, 246, 4354], ![4354, 14636, -25274, -109542, 172, 171836, 22311, -95122, -3326, 13308], ![13308, 44278, -78520, -331358, 10230, 519184, 52064, -283773, -1966, 36598]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-172, -46, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-172, -46, -16, -3, -1], [-482, -172, -46, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-172, -46, -16, -3, -1], [-482, -172, -46, -16, -3, -1], [-1574, -482, -172, -46, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-172, -46, -16, -3, -1], [-482, -172, -46, -16, -3, -1], [-1574, -482, -172, -46, -16, -3, -1], [-4354, -1574, -482, -172, -46, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-172, -46, -16, -3, -1], [-482, -172, -46, -16, -3, -1], [-1574, -482, -172, -46, -16, -3, -1], [-4354, -1574, -482, -172, -46, -16, -3, -1], [-13308, -4354, -1574, -482, -172, -46, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -23, 9, 39, -9, -23, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -23, 9, 39, -9, -23, 7, 3], [3, 10, -18, -76, 4, 126, 12, -78, -2, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -23, 9, 39, -9, -23, 7, 3], [3, 10, -18, -76, 4, 126, 12, -78, -2, 16], [16, 51, -102, -386, 68, 628, -18, -356, 34, 46]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -23, 9, 39, -9, -23, 7, 3], [3, 10, -18, -76, 4, 126, 12, -78, -2, 16], [16, 51, -102, -386, 68, 628, -18, -356, 34, 46], [46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -23, 9, 39, -9, -23, 7, 3], [3, 10, -18, -76, 4, 126, 12, -78, -2, 16], [16, 51, -102, -386, 68, 628, -18, -356, 34, 46], [46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], [172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -23, 9, 39, -9, -23, 7, 3], [3, 10, -18, -76, 4, 126, 12, -78, -2, 16], [16, 51, -102, -386, 68, 628, -18, -356, 34, 46], [46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], [172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482], [482, 1618, -2812, -12136, 111, 19186, 2398, -10772, -368, 1574]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -23, 9, 39, -9, -23, 7, 3], [3, 10, -18, -76, 4, 126, 12, -78, -2, 16], [16, 51, -102, -386, 68, 628, -18, -356, 34, 46], [46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], [172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482], [482, 1618, -2812, -12136, 111, 19186, 2398, -10772, -368, 1574], [1574, 5204, -9400, -39014, 2030, 61497, 5020, -33804, 246, 4354]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -23, 9, 39, -9, -23, 7, 3], [3, 10, -18, -76, 4, 126, 12, -78, -2, 16], [16, 51, -102, -386, 68, 628, -18, -356, 34, 46], [46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], [172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482], [482, 1618, -2812, -12136, 111, 19186, 2398, -10772, -368, 1574], [1574, 5204, -9400, -39014, 2030, 61497, 5020, -33804, 246, 4354], [4354, 14636, -25274, -109542, 172, 171836, 22311, -95122, -3326, 13308]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -23, 9, 39, -9, -23, 7, 3], [3, 10, -18, -76, 4, 126, 12, -78, -2, 16], [16, 51, -102, -386, 68, 628, -18, -356, 34, 46], [46, 154, -271, -1160, 28, 1862, 214, -1076, -34, 172], [172, 562, -1050, -4227, 388, 6736, 314, -3742, 128, 482], [482, 1618, -2812, -12136, 111, 19186, 2398, -10772, -368, 1574], [1574, 5204, -9400, -39014, 2030, 61497, 5020, -33804, 246, 4354], [4354, 14636, -25274, -109542, 172, 171836, 22311, -95122, -3326, 13308], [13308, 44278, -78520, -331358, 10230, 519184, 52064, -283773, -1966, 36598]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp9437 : Fact (Nat.Prime 9437) := fact_iff.2 (by norm_num)

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [2, 57, 15, 27, 22, 44, 28]
  b' := [4, 60, 47, 34, 37, 42, 43, 27]
  k := [60, 34, 50, 18, 11, 34, 1]
  f := [1, 15, 54, 16, 13, 57, 62, 56, 11, 1]
  g := [1, 15, 52, 6, 11, 55, 52, 46, 1]
  h := [60, 12, 1]
  a := [10, 45, 44, 47, 29, 13, 32, 51]
  b := [52, 1, 48, 11, 60, 40, 45, 45, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [76, 166, 302, 87, 258, 181, 69]
  b' := [141, 52, 264, 312, 179, 167, 16, 41]
  k := [396, 173, 327, 369, 70, 173, 1]
  f := [1, 312, 570, 265, 346, 651, 630, 341, 68, 1]
  g := [1, 312, 328, 9, 339, 388, 328, 85, 1]
  h := [396, 309, 1]
  a := [305, 110, 13, 173, 49, 58, 105, 369]
  b := [93, 372, 167, 50, 354, 169, 72, 213, 28]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9437 : CertificateDedekindCriterionLists l 9437 where
  n := 2
  a' := [4017, 7465, 7789, 3603, 6483, 4688, 5934, 2293]
  b' := [7324, 2029, 4110, 7303, 7039, 8683, 4963, 8475, 4988]
  k := [1, 1663, 4970, 3902, 8517, 5535, 4970, 7774, 1]
  f := [73, 219, 246, 593, 414, 594, 587, 219, 757, 1]
  g := [830, 2489, 2794, 6739, 4699, 6748, 6666, 2482, 8604, 1]
  h := [830, 1]
  a := [1607, 3738, 2147, 8465, 7702, 5432, 7543, 2167, 4362]
  b := [5771, 3976, 3712, 716, 2978, 534, 3670, 7885, 5075]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![61, 397, 9437]
  exp := ![1, 1, 1]
  pdgood := [61, 397, 9437]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp61.out
    exact hp397.out
    exact hp9437.out
  a := [11976884305, -85725863674, -74982603292, 318021951460, 44978122958, -314847723208, 73843485918, 55277218256, -17599140280]
  b := [-4068473378, -2387805511, 33948148071, 13097895352, -66100988232, -3988816758, 44601686354, -9615442046, -6055696034, 1759914028]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9437 T_ofList CD9437

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

end VoightMaximalOrderD10R480

namespace VoightMaximalOrderD10R481

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5545730083904, [-1, -3, 9, 19, -28, -25, 28, 10, -10, -1, 1], 1⟩
local notation "l" => [-1, -3, 9, 19, -28, -25, 28, 10, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 28, 25, -28, -10, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 28, 25, -28, -10, 10, 1], ![1, 4, -6, -28, 9, 53, -3, -38, 0, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 28, 25, -28, -10, 10, 1], ![1, 4, -6, -28, 9, 53, -3, -38, 0, 11], ![11, 34, -95, -215, 280, 284, -255, -113, 72, 11]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 28, 25, -28, -10, 10, 1], ![1, 4, -6, -28, 9, 53, -3, -38, 0, 11], ![11, 34, -95, -215, 280, 284, -255, -113, 72, 11], ![11, 44, -65, -304, 93, 555, -24, -365, -3, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 28, 25, -28, -10, 10, 1], ![1, 4, -6, -28, 9, 53, -3, -38, 0, 11], ![11, 34, -95, -215, 280, 284, -255, -113, 72, 11], ![11, 44, -65, -304, 93, 555, -24, -365, -3, 83], ![83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 28, 25, -28, -10, 10, 1], ![1, 4, -6, -28, 9, 53, -3, -38, 0, 11], ![11, 34, -95, -215, 280, 284, -255, -113, 72, 11], ![11, 44, -65, -304, 93, 555, -24, -365, -3, 83], ![83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80], ![80, 323, -460, -2223, 598, 4020, -72, -2569, -54, 545]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 28, 25, -28, -10, 10, 1], ![1, 4, -6, -28, 9, 53, -3, -38, 0, 11], ![11, 34, -95, -215, 280, 284, -255, -113, 72, 11], ![11, 44, -65, -304, 93, 555, -24, -365, -3, 83], ![83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80], ![80, 323, -460, -2223, 598, 4020, -72, -2569, -54, 545], ![545, 1715, -4582, -10815, 13037, 14223, -11240, -5522, 2881, 491]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 28, 25, -28, -10, 10, 1], ![1, 4, -6, -28, 9, 53, -3, -38, 0, 11], ![11, 34, -95, -215, 280, 284, -255, -113, 72, 11], ![11, 44, -65, -304, 93, 555, -24, -365, -3, 83], ![83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80], ![80, 323, -460, -2223, 598, 4020, -72, -2569, -54, 545], ![545, 1715, -4582, -10815, 13037, 14223, -11240, -5522, 2881, 491], ![491, 2018, -2704, -13911, 2933, 25312, 475, -16150, -612, 3372]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 28, 25, -28, -10, 10, 1], ![1, 4, -6, -28, 9, 53, -3, -38, 0, 11], ![11, 34, -95, -215, 280, 284, -255, -113, 72, 11], ![11, 44, -65, -304, 93, 555, -24, -365, -3, 83], ![83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80], ![80, 323, -460, -2223, 598, 4020, -72, -2569, -54, 545], ![545, 1715, -4582, -10815, 13037, 14223, -11240, -5522, 2881, 491], ![491, 2018, -2704, -13911, 2933, 25312, 475, -16150, -612, 3372], ![3372, 10607, -28330, -66772, 80505, 87233, -69104, -33245, 17570, 2760]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-83, -11, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-83, -11, -11, -1, -1], [-80, -83, -11, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-83, -11, -11, -1, -1], [-80, -83, -11, -11, -1, -1], [-545, -80, -83, -11, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-83, -11, -11, -1, -1], [-80, -83, -11, -11, -1, -1], [-545, -80, -83, -11, -11, -1, -1], [-491, -545, -80, -83, -11, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-83, -11, -11, -1, -1], [-80, -83, -11, -11, -1, -1], [-545, -80, -83, -11, -11, -1, -1], [-491, -545, -80, -83, -11, -11, -1, -1], [-3372, -491, -545, -80, -83, -11, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 28, 25, -28, -10, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 28, 25, -28, -10, 10, 1], [1, 4, -6, -28, 9, 53, -3, -38, 0, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 28, 25, -28, -10, 10, 1], [1, 4, -6, -28, 9, 53, -3, -38, 0, 11], [11, 34, -95, -215, 280, 284, -255, -113, 72, 11]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 28, 25, -28, -10, 10, 1], [1, 4, -6, -28, 9, 53, -3, -38, 0, 11], [11, 34, -95, -215, 280, 284, -255, -113, 72, 11], [11, 44, -65, -304, 93, 555, -24, -365, -3, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 28, 25, -28, -10, 10, 1], [1, 4, -6, -28, 9, 53, -3, -38, 0, 11], [11, 34, -95, -215, 280, 284, -255, -113, 72, 11], [11, 44, -65, -304, 93, 555, -24, -365, -3, 83], [83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 28, 25, -28, -10, 10, 1], [1, 4, -6, -28, 9, 53, -3, -38, 0, 11], [11, 34, -95, -215, 280, 284, -255, -113, 72, 11], [11, 44, -65, -304, 93, 555, -24, -365, -3, 83], [83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80], [80, 323, -460, -2223, 598, 4020, -72, -2569, -54, 545]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 28, 25, -28, -10, 10, 1], [1, 4, -6, -28, 9, 53, -3, -38, 0, 11], [11, 34, -95, -215, 280, 284, -255, -113, 72, 11], [11, 44, -65, -304, 93, 555, -24, -365, -3, 83], [83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80], [80, 323, -460, -2223, 598, 4020, -72, -2569, -54, 545], [545, 1715, -4582, -10815, 13037, 14223, -11240, -5522, 2881, 491]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 28, 25, -28, -10, 10, 1], [1, 4, -6, -28, 9, 53, -3, -38, 0, 11], [11, 34, -95, -215, 280, 284, -255, -113, 72, 11], [11, 44, -65, -304, 93, 555, -24, -365, -3, 83], [83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80], [80, 323, -460, -2223, 598, 4020, -72, -2569, -54, 545], [545, 1715, -4582, -10815, 13037, 14223, -11240, -5522, 2881, 491], [491, 2018, -2704, -13911, 2933, 25312, 475, -16150, -612, 3372]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 28, 25, -28, -10, 10, 1], [1, 4, -6, -28, 9, 53, -3, -38, 0, 11], [11, 34, -95, -215, 280, 284, -255, -113, 72, 11], [11, 44, -65, -304, 93, 555, -24, -365, -3, 83], [83, 260, -703, -1642, 2020, 2168, -1769, -854, 465, 80], [80, 323, -460, -2223, 598, 4020, -72, -2569, -54, 545], [545, 1715, -4582, -10815, 13037, 14223, -11240, -5522, 2881, 491], [491, 2018, -2704, -13911, 2933, 25312, 475, -16150, -612, 3372], [3372, 10607, -28330, -66772, 80505, 87233, -69104, -33245, 17570, 2760]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp4463 : Fact (Nat.Prime 4463) := fact_iff.2 (by norm_num)
instance hp19415647 : Fact (Nat.Prime 19415647) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 0, 1]
  k := [1, 1, 1, 1, 1]
  f := [1, 2, -4, -8, 15, 13, -13, -4, 5, 1]
  g := [1, 1, 0, 1, 1, 0, 0, 1]
  h := [1, 0, 1, 1]
  a := [1, 0, 0, 0, 0, 0, 1]
  b := [0, 0, 0, 0, 1, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4463 : CertificateDedekindCriterionLists l 4463 where
  n := 2
  a' := [3565, 1788, 3201, 1464, 2195, 2435, 1278, 2974]
  b' := [2605, 2757, 3950, 1740, 400, 2608, 3372, 1773, 2149]
  k := [4079, 2257, 4226, 131, 3931, 95, 1100, 2829, 1]
  f := [2279, 1004, 1972, 1260, 2136, 2320, 808, 940, 966, 1]
  g := [3337, 1469, 2887, 1844, 3127, 3396, 1182, 1376, 1414, 1]
  h := [3048, 1]
  a := [178, 1008, 2554, 4377, 1374, 1297, 3526, 2088, 536]
  b := [2893, 2941, 1756, 2303, 2991, 1915, 336, 1501, 3927]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19415647 : CertificateDedekindCriterionLists l 19415647 where
  n := 2
  a' := [17119336, 5952450, 9319941, 9209972, 8494231, 921488, 17911435, 15822776]
  b' := [2819520, 7441113, 15678300, 9110346, 9965235, 6685468, 8696469, 8400861, 2556502]
  k := [10495198, 16000823, 7115666, 7494877, 1342028, 14149162, 7073922, 3693001, 1]
  f := [3967837, 2406446, 4296338, 6950568, 8423456, 10291656, 2819089, 1576752, 1670891, 1]
  g := [4384853, 2659361, 4747879, 7681066, 9308753, 11373299, 3115372, 1742467, 1846500, 1]
  h := [17569146, 1]
  a := [13138535, 17718335, 5056299, 18087338, 5354217, 17609447, 15899403, 3382299, 7361485]
  b := [8680956, 5115675, 12245650, 6342320, 11961152, 8169108, 11651158, 7028512, 12054162]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 4463, 19415647]
  exp := ![1, 1, 1]
  pdgood := [2, 4463, 19415647]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp4463.out
    exact hp19415647.out
  a := [174289711262, -3615085450632, 8231462137539, 7694290038024, -19034161462187, -3695954753891, 10963982406140, 392409003709, -1483142380010]
  b := [-115864592128, 335551219514, 1206013938557, -2600478755897, -1565590189781, 3473117464910, 608561023148, -1402450907999, -54072324171, 148314238001]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4463 T_ofList CD4463
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19415647 T_ofList CD19415647

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

end VoightMaximalOrderD10R481

namespace VoightMaximalOrderD10R482

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5549501383744, [1, -11, 19, 29, -46, -26, 34, 9, -10, -1, 1], 1⟩
local notation "l" => [1, -11, 19, 29, -46, -26, 34, 9, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -19, -29, 46, 26, -34, -9, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], ![-1, 10, -8, -48, 17, 72, -8, -43, 1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], ![-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], ![-11, 120, -199, -327, 458, 303, -302, -107, 67, 12]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], ![-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], ![-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], ![-12, 121, -108, -547, 225, 770, -105, -410, 13, 79]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], ![-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], ![-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], ![-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], ![-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], ![-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], ![-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], ![-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], ![-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92], ![-92, 933, -891, -4048, 1833, 5479, -849, -2744, 104, 472]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], ![-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], ![-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], ![-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], ![-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92], ![-92, 933, -891, -4048, 1833, 5479, -849, -2744, 104, 472], ![-472, 5100, -8035, -14579, 17664, 14105, -10569, -5097, 1976, 576]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], ![-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], ![-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], ![-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], ![-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92], ![-92, 933, -891, -4048, 1833, 5479, -849, -2744, 104, 472], ![-472, 5100, -8035, -14579, 17664, 14105, -10569, -5097, 1976, 576], ![-576, 5864, -5844, -24739, 11917, 32640, -5479, -15753, 663, 2552]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], ![-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], ![-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], ![-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], ![-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92], ![-92, 933, -891, -4048, 1833, 5479, -849, -2744, 104, 472], ![-472, 5100, -8035, -14579, 17664, 14105, -10569, -5097, 1976, 576], ![-576, 5864, -5844, -24739, 11917, 32640, -5479, -15753, 663, 2552], ![-2552, 27496, -42624, -79852, 92653, 78269, -54128, -28447, 9767, 3215]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-79, -12, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-79, -12, -11, -1, -1], [-92, -79, -12, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-79, -12, -11, -1, -1], [-92, -79, -12, -11, -1, -1], [-472, -92, -79, -12, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-79, -12, -11, -1, -1], [-92, -79, -12, -11, -1, -1], [-472, -92, -79, -12, -11, -1, -1], [-576, -472, -92, -79, -12, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-79, -12, -11, -1, -1], [-92, -79, -12, -11, -1, -1], [-472, -92, -79, -12, -11, -1, -1], [-576, -472, -92, -79, -12, -11, -1, -1], [-2552, -576, -472, -92, -79, -12, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -19, -29, 46, 26, -34, -9, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], [-1, 10, -8, -48, 17, 72, -8, -43, 1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], [-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], [-11, 120, -199, -327, 458, 303, -302, -107, 67, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], [-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], [-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], [-12, 121, -108, -547, 225, 770, -105, -410, 13, 79]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], [-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], [-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], [-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], [-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], [-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], [-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], [-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], [-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92], [-92, 933, -891, -4048, 1833, 5479, -849, -2744, 104, 472]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], [-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], [-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], [-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], [-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92], [-92, 933, -891, -4048, 1833, 5479, -849, -2744, 104, 472], [-472, 5100, -8035, -14579, 17664, 14105, -10569, -5097, 1976, 576]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], [-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], [-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], [-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], [-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92], [-92, 933, -891, -4048, 1833, 5479, -849, -2744, 104, 472], [-472, 5100, -8035, -14579, 17664, 14105, -10569, -5097, 1976, 576], [-576, 5864, -5844, -24739, 11917, 32640, -5479, -15753, 663, 2552]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -19, -29, 46, 26, -34, -9, 10, 1], [-1, 10, -8, -48, 17, 72, -8, -43, 1, 11], [-11, 120, -199, -327, 458, 303, -302, -107, 67, 12], [-12, 121, -108, -547, 225, 770, -105, -410, 13, 79], [-79, 857, -1380, -2399, 3087, 2279, -1916, -816, 380, 92], [-92, 933, -891, -4048, 1833, 5479, -849, -2744, 104, 472], [-472, 5100, -8035, -14579, 17664, 14105, -10569, -5097, 1976, 576], [-576, 5864, -5844, -24739, 11917, 32640, -5479, -15753, 663, 2552], [-2552, 27496, -42624, -79852, 92653, 78269, -54128, -28447, 9767, 3215]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp80221 : Fact (Nat.Prime 80221) := fact_iff.2 (by norm_num)
instance hp1080901 : Fact (Nat.Prime 1080901) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [0, 1, 1, 0, 1, 0, 1]
  k := [1, 1, 0, 0, 1, 1, 1]
  f := [0, 6, -9, -14, 24, 14, -16, -4, 6, 1]
  g := [1, 0, 0, 1, 1, 0, 1, 0, 1]
  h := [1, 1, 1]
  a := [0, 1, 1, 0, 0, 0, 0, 1]
  b := [1, 0, 0, 0, 0, 0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD80221 : CertificateDedekindCriterionLists l 80221 where
  n := 2
  a' := [25679, 52286, 31687, 64538, 72645, 7271, 14973, 68411]
  b' := [74683, 8995, 15858, 32719, 46323, 31110, 19652, 15349, 36966]
  k := [57558, 1451, 79437, 18884, 56728, 57004, 37872, 73785, 1]
  f := [23115, 17944, 24847, 16846, 20767, 903, 29417, 14616, 19926, 1]
  g := [42797, 33222, 46003, 31189, 38449, 1671, 54465, 27060, 36892, 1]
  h := [43328, 1]
  a := [59558, 73301, 55549, 30583, 26453, 3135, 68023, 25280, 54374]
  b := [27035, 79694, 37963, 36343, 6627, 18080, 55690, 22725, 25847]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1080901 : CertificateDedekindCriterionLists l 1080901 where
  n := 2
  a' := [768149, 360069, 801660, 396737, 1038179, 791748, 584730, 1011047]
  b' := [743174, 682178, 834349, 870312, 473912, 292551, 193521, 633546, 488162]
  k := [567952, 228801, 539074, 742774, 6261, 79154, 542321, 128753, 1]
  f := [556951, 455082, 705623, 899641, 803561, 712308, 171572, 149820, 60542, 1]
  g := [592223, 483902, 750310, 956615, 854450, 757418, 182437, 159308, 64376, 1]
  h := [1016524, 1]
  a := [811014, 820452, 51356, 336369, 282452, 39728, 190732, 661052, 88856]
  b := [687832, 958831, 227632, 997757, 221137, 228584, 324397, 609938, 992045]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 80221, 1080901]
  exp := ![2, 1, 1]
  pdgood := [2, 80221, 1080901]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp80221.out
    exact hp1080901.out
  a := [-1214244680867, -1023630776595, 6076238930803, 2786200269588, -7203438226933, -1795425765767, 3036474549061, 292288227086, -400844885640]
  b := [-141917137941, 630928133744, 535818783480, -1577263061871, -654040870311, 1237332466388, 271757166811, -384501153734, -33237271565, 40084488564]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 80221 T_ofList CD80221
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1080901 T_ofList CD1080901

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

end VoightMaximalOrderD10R482

namespace VoightMaximalOrderD10R484

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5576307163633, [-1, -4, 14, 16, -36, -20, 32, 8, -10, -1, 1], 1⟩
local notation "l" => [-1, -4, 14, 16, -36, -20, 32, 8, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -14, -16, 36, 20, -32, -8, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -14, -16, 36, 20, -32, -8, 10, 1], ![1, 5, -10, -30, 20, 56, -12, -40, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -14, -16, 36, 20, -32, -8, 10, 1], ![1, 5, -10, -30, 20, 56, -12, -40, 2, 11], ![11, 45, -149, -186, 366, 240, -296, -100, 70, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -14, -16, 36, 20, -32, -8, 10, 1], ![1, 5, -10, -30, 20, 56, -12, -40, 2, 11], ![11, 45, -149, -186, 366, 240, -296, -100, 70, 13], ![13, 63, -137, -357, 282, 626, -176, -400, 30, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -14, -16, 36, 20, -32, -8, 10, 1], ![1, 5, -10, -30, 20, 56, -12, -40, 2, 11], ![11, 45, -149, -186, 366, 240, -296, -100, 70, 13], ![13, 63, -137, -357, 282, 626, -176, -400, 30, 83], ![83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -14, -16, 36, 20, -32, -8, 10, 1], ![1, 5, -10, -30, 20, 56, -12, -40, 2, 11], ![11, 45, -149, -186, 366, 240, -296, -100, 70, 13], ![13, 63, -137, -357, 282, 626, -176, -400, 30, 83], ![83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113], ![113, 535, -1237, -2907, 2603, 4891, -1674, -2934, 290, 543]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -14, -16, 36, 20, -32, -8, 10, 1], ![1, 5, -10, -30, 20, 56, -12, -40, 2, 11], ![11, 45, -149, -186, 366, 240, -296, -100, 70, 13], ![13, 63, -137, -357, 282, 626, -176, -400, 30, 83], ![83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113], ![113, 535, -1237, -2907, 2603, 4891, -1674, -2934, 290, 543], ![543, 2285, -7067, -9925, 16641, 13463, -12485, -6018, 2496, 833]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -14, -16, 36, 20, -32, -8, 10, 1], ![1, 5, -10, -30, 20, 56, -12, -40, 2, 11], ![11, 45, -149, -186, 366, 240, -296, -100, 70, 13], ![13, 63, -137, -357, 282, 626, -176, -400, 30, 83], ![83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113], ![113, 535, -1237, -2907, 2603, 4891, -1674, -2934, 290, 543], ![543, 2285, -7067, -9925, 16641, 13463, -12485, -6018, 2496, 833], ![833, 3875, -9377, -20395, 20063, 33301, -13193, -19149, 2312, 3329]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -14, -16, 36, 20, -32, -8, 10, 1], ![1, 5, -10, -30, 20, 56, -12, -40, 2, 11], ![11, 45, -149, -186, 366, 240, -296, -100, 70, 13], ![13, 63, -137, -357, 282, 626, -176, -400, 30, 83], ![83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113], ![113, 535, -1237, -2907, 2603, 4891, -1674, -2934, 290, 543], ![543, 2285, -7067, -9925, 16641, 13463, -12485, -6018, 2496, 833], ![833, 3875, -9377, -20395, 20063, 33301, -13193, -19149, 2312, 3329], ![3329, 14149, -42731, -62641, 99449, 86643, -73227, -39825, 14141, 5641]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-83, -13, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-83, -13, -11, -1, -1], [-113, -83, -13, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-83, -13, -11, -1, -1], [-113, -83, -13, -11, -1, -1], [-543, -113, -83, -13, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-83, -13, -11, -1, -1], [-113, -83, -13, -11, -1, -1], [-543, -113, -83, -13, -11, -1, -1], [-833, -543, -113, -83, -13, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-83, -13, -11, -1, -1], [-113, -83, -13, -11, -1, -1], [-543, -113, -83, -13, -11, -1, -1], [-833, -543, -113, -83, -13, -11, -1, -1], [-3329, -833, -543, -113, -83, -13, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -14, -16, 36, 20, -32, -8, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -14, -16, 36, 20, -32, -8, 10, 1], [1, 5, -10, -30, 20, 56, -12, -40, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -14, -16, 36, 20, -32, -8, 10, 1], [1, 5, -10, -30, 20, 56, -12, -40, 2, 11], [11, 45, -149, -186, 366, 240, -296, -100, 70, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -14, -16, 36, 20, -32, -8, 10, 1], [1, 5, -10, -30, 20, 56, -12, -40, 2, 11], [11, 45, -149, -186, 366, 240, -296, -100, 70, 13], [13, 63, -137, -357, 282, 626, -176, -400, 30, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -14, -16, 36, 20, -32, -8, 10, 1], [1, 5, -10, -30, 20, 56, -12, -40, 2, 11], [11, 45, -149, -186, 366, 240, -296, -100, 70, 13], [13, 63, -137, -357, 282, 626, -176, -400, 30, 83], [83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -14, -16, 36, 20, -32, -8, 10, 1], [1, 5, -10, -30, 20, 56, -12, -40, 2, 11], [11, 45, -149, -186, 366, 240, -296, -100, 70, 13], [13, 63, -137, -357, 282, 626, -176, -400, 30, 83], [83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113], [113, 535, -1237, -2907, 2603, 4891, -1674, -2934, 290, 543]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -14, -16, 36, 20, -32, -8, 10, 1], [1, 5, -10, -30, 20, 56, -12, -40, 2, 11], [11, 45, -149, -186, 366, 240, -296, -100, 70, 13], [13, 63, -137, -357, 282, 626, -176, -400, 30, 83], [83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113], [113, 535, -1237, -2907, 2603, 4891, -1674, -2934, 290, 543], [543, 2285, -7067, -9925, 16641, 13463, -12485, -6018, 2496, 833]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -14, -16, 36, 20, -32, -8, 10, 1], [1, 5, -10, -30, 20, 56, -12, -40, 2, 11], [11, 45, -149, -186, 366, 240, -296, -100, 70, 13], [13, 63, -137, -357, 282, 626, -176, -400, 30, 83], [83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113], [113, 535, -1237, -2907, 2603, 4891, -1674, -2934, 290, 543], [543, 2285, -7067, -9925, 16641, 13463, -12485, -6018, 2496, 833], [833, 3875, -9377, -20395, 20063, 33301, -13193, -19149, 2312, 3329]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -14, -16, 36, 20, -32, -8, 10, 1], [1, 5, -10, -30, 20, 56, -12, -40, 2, 11], [11, 45, -149, -186, 366, 240, -296, -100, 70, 13], [13, 63, -137, -357, 282, 626, -176, -400, 30, 83], [83, 345, -1099, -1465, 2631, 1942, -2030, -840, 430, 113], [113, 535, -1237, -2907, 2603, 4891, -1674, -2934, 290, 543], [543, 2285, -7067, -9925, 16641, 13463, -12485, -6018, 2496, 833], [833, 3875, -9377, -20395, 20063, 33301, -13193, -19149, 2312, 3329], [3329, 14149, -42731, -62641, 99449, 86643, -73227, -39825, 14141, 5641]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp19295180497 : Fact (Nat.Prime 19295180497) := fact_iff.2 (by norm_num)

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 3
  a' := [14, 9, 9, 15, 11, 13, 10]
  b' := [10, 11, 4, 10, 8, 1, 8, 3]
  k := [4, 10, 1, 3, 0, 16, 10, 9, 5, 5, 2, 3, 7, 10, 1]
  f := [1, 4, 5, 13, 15, 10, 6, 12, 4, 1]
  g := [4, 3, 14, 13, 9, 5, 15, 3, 1]
  h := [4, 13, 1]
  a := [7, 11, 1, 5, 16, 12, 3, 11]
  b := [7, 2, 5, 0, 7, 14, 0, 3, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19295180497 : CertificateDedekindCriterionLists l 19295180497 where
  n := 2
  a' := [13281984838, 2518901984, 6409002060, 16886494822, 1933937083, 4704358914, 14057219895, 15371383879]
  b' := [6722550817, 8470776254, 12245044160, 1799449346, 14698280663, 1197507404, 13090218738, 6224522493, 435977402]
  k := [16712623517, 5630012164, 10928634093, 15490863681, 8023504250, 14358184659, 2142795828, 8251298804, 1]
  f := [2097199189, 3605938236, 4443415917, 3315977978, 1193629403, 1361785308, 2238527784, 731170882, 3941658624, 1]
  g := [7328190942, 12600140251, 15526517672, 11586939335, 4170869520, 4758452516, 7822031934, 2554912218, 13773239650, 1]
  h := [5521940846, 1]
  a := [14733276523, 16893495802, 7158707352, 1988443960, 7347727335, 9115549160, 8848120736, 10834223530, 5865929014]
  b := [7175790227, 11120904063, 18685834507, 5545151051, 16270898994, 7223176391, 17803381196, 1238266496, 13429251483]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![17, 19295180497]
  exp := ![1, 1]
  pdgood := [17, 19295180497]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp17.out
    exact hp19295180497.out
  a := [718113948055, -8624360993208, 2215086693306, 42184941832500, -29538242657856, -26086699762832, 17974003618516, 4156154709912, -2667625081280]
  b := [-261533004126, -392754728635, 4696308988117, -2497835513704, -8459692651306, 5602525706160, 3582086082056, -2313372456740, -442291721804, 266762508128]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19295180497 T_ofList CD19295180497

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

end VoightMaximalOrderD10R484

end TraceEuclidean
