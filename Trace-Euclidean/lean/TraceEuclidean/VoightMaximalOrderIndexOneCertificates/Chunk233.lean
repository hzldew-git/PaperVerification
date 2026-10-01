import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk229
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

namespace VoightMaximalOrderD10R780

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7543057455181, [1, -7, -7, 32, 11, -46, -3, 24, -3, -4, 1], 1⟩
local notation "l" => [1, -7, -7, 32, 11, -46, -3, 24, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 7, -32, -11, 46, 3, -24, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], ![-4, 27, 35, -121, -76, 173, 58, -93, -12, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], ![-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], ![-19, 129, 160, -573, -330, 798, 230, -398, -36, 64]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], ![-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], ![-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], ![-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], ![-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], ![-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], ![-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], ![-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], ![-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], ![-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], ![-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], ![-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674], ![-674, 4498, 6194, -19599, -13877, 26696, 10865, -12902, -2268, 2050]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], ![-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], ![-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], ![-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], ![-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674], ![-674, 4498, 6194, -19599, -13877, 26696, 10865, -12902, -2268, 2050], ![-2050, 13676, 18848, -59406, -42149, 80423, 32846, -38335, -6752, 5932]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], ![-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], ![-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], ![-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], ![-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674], ![-674, 4498, 6194, -19599, -13877, 26696, 10865, -12902, -2268, 2050], ![-2050, 13676, 18848, -59406, -42149, 80423, 32846, -38335, -6752, 5932], ![-5932, 39474, 55200, -170976, -124658, 230723, 98219, -109522, -20539, 16976]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], ![-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], ![-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], ![-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], ![-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674], ![-674, 4498, 6194, -19599, -13877, 26696, 10865, -12902, -2268, 2050], ![-2050, 13676, 18848, -59406, -42149, 80423, 32846, -38335, -6752, 5932], ![-5932, 39474, 55200, -170976, -124658, 230723, 98219, -109522, -20539, 16976], ![-16976, 112900, 158306, -488032, -357712, 656238, 281651, -309205, -58594, 47365]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1], [-674, -220, -64, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1], [-674, -220, -64, -19, -4, -1], [-2050, -674, -220, -64, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1], [-674, -220, -64, -19, -4, -1], [-2050, -674, -220, -64, -19, -4, -1], [-5932, -2050, -674, -220, -64, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1], [-674, -220, -64, -19, -4, -1], [-2050, -674, -220, -64, -19, -4, -1], [-5932, -2050, -674, -220, -64, -19, -4, -1], [-16976, -5932, -2050, -674, -220, -64, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 7, -32, -11, 46, 3, -24, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], [-4, 27, 35, -121, -76, 173, 58, -93, -12, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], [-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], [-19, 129, 160, -573, -330, 798, 230, -398, -36, 64]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], [-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], [-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], [-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], [-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], [-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], [-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], [-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], [-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], [-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], [-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], [-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674], [-674, 4498, 6194, -19599, -13877, 26696, 10865, -12902, -2268, 2050]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], [-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], [-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], [-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], [-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674], [-674, 4498, 6194, -19599, -13877, 26696, 10865, -12902, -2268, 2050], [-2050, 13676, 18848, -59406, -42149, 80423, 32846, -38335, -6752, 5932]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], [-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], [-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], [-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], [-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674], [-674, 4498, 6194, -19599, -13877, 26696, 10865, -12902, -2268, 2050], [-2050, 13676, 18848, -59406, -42149, 80423, 32846, -38335, -6752, 5932], [-5932, 39474, 55200, -170976, -124658, 230723, 98219, -109522, -20539, 16976]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 7, -32, -11, 46, 3, -24, 3, 4], [-4, 27, 35, -121, -76, 173, 58, -93, -12, 19], [-19, 129, 160, -573, -330, 798, 230, -398, -36, 64], [-64, 429, 577, -1888, -1277, 2614, 990, -1306, -206, 220], [-220, 1476, 1969, -6463, -4308, 8843, 3274, -4290, -646, 674], [-674, 4498, 6194, -19599, -13877, 26696, 10865, -12902, -2268, 2050], [-2050, 13676, 18848, -59406, -42149, 80423, 32846, -38335, -6752, 5932], [-5932, 39474, 55200, -170976, -124658, 230723, 98219, -109522, -20539, 16976], [-16976, 112900, 158306, -488032, -357712, 656238, 281651, -309205, -58594, 47365]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp53 : Fact (Nat.Prime 53) := fact_iff.2 (by norm_num)
instance hp79 : Fact (Nat.Prime 79) := fact_iff.2 (by norm_num)
instance hp73867 : Fact (Nat.Prime 73867) := fact_iff.2 (by norm_num)

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 4
  a' := [21, 4, 12, 5, 5, 22]
  b' := [1, 25, 8, 19, 14, 26, 1]
  k := [16, 22, 28, 22, 13, 23, 26, 7, 26, 5, 23, 18, 14, 28, 3, 14, 7, 27, 1]
  f := [1, 6, 11, 11, 20, 30, 29, 19, 7, 1]
  g := [5, 12, 4, 21, 22, 25, 13, 1]
  h := [6, 19, 12, 1]
  a := [16, 20, 19, 4, 27, 26, 5]
  b := [26, 13, 1, 13, 16, 6, 1, 4, 24]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD53 : CertificateDedekindCriterionLists l 53 where
  n := 2
  a' := [6, 20, 45, 37, 16, 49, 42, 17]
  b' := [15, 48, 21, 24, 35, 29, 24, 27, 4]
  k := [36, 21, 29, 2, 12, 6, 9, 14, 1]
  f := [39, 6, 21, 9, 0, 10, 26, 35, 5, 1]
  g := [47, 6, 25, 11, 0, 11, 31, 42, 5, 1]
  h := [44, 1]
  a := [39, 7, 1, 42, 13, 31, 8, 12, 28]
  b := [6, 11, 27, 8, 25, 8, 29, 41, 25]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD79 : CertificateDedekindCriterionLists l 79 where
  n := 2
  a' := [26, 40, 17, 65, 55, 37, 7, 28]
  b' := [14, 70, 38, 68, 28, 3, 22, 17, 32]
  k := [40, 1, 25, 43, 64, 18, 10, 14, 1]
  f := [31, 28, 12, 29, 18, 54, 7, 37, 5, 1]
  g := [35, 31, 13, 33, 20, 60, 7, 42, 5, 1]
  h := [70, 1]
  a := [49, 32, 57, 78, 17, 15, 44, 34, 3]
  b := [74, 52, 48, 52, 64, 1, 50, 45, 76]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD73867 : CertificateDedekindCriterionLists l 73867 where
  n := 2
  a' := [71640, 53979, 32712, 55561, 15814, 51764, 58577, 22368]
  b' := [58433, 37939, 36650, 2594, 45578, 51713, 7085, 30262, 22137]
  k := [35469, 45649, 47322, 31250, 15151, 73813, 49748, 62806, 1]
  f := [5987, 22626, 16333, 21864, 37543, 6945, 14327, 13769, 18051, 1]
  g := [10415, 39360, 28412, 38034, 65309, 12080, 24923, 23952, 31401, 1]
  h := [42462, 1]
  a := [39868, 11693, 65262, 39481, 10538, 14176, 34137, 3177, 3398]
  b := [8785, 24088, 72499, 23420, 8121, 17518, 28741, 5785, 70469]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![29, 53, 79, 73867]
  exp := ![1, 1, 1, 1]
  pdgood := [29, 53, 79, 73867]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp29.out
    exact hp53.out
    exact hp79.out
    exact hp73867.out
  a := [-34143857500, -146659742208, 299919358160, 802023866768, -311034459496, -672915211936, 201831755036, 147910689904, -49763275140]
  b := [-6159001463, 25510468682, 88161979160, -59950809148, -178776990174, 45017167962, 100044706560, -24418456036, -16781599996, 4976327514]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 53 T_ofList CD53
    exact satisfiesDedekindCriterion_of_certificate_lists T l 79 T_ofList CD79
    exact satisfiesDedekindCriterion_of_certificate_lists T l 73867 T_ofList CD73867

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

end VoightMaximalOrderD10R780

namespace VoightMaximalOrderD10R785

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7567325739388, [-2, -12, 33, 37, -71, -47, 43, 18, -11, -2, 1], 1⟩
local notation "l" => [-2, -12, 33, 37, -71, -47, 43, 18, -11, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 12, -33, -37, 71, 47, -43, -18, 11, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 12, -33, -37, 71, 47, -43, -18, 11, 2], ![4, 26, -54, -107, 105, 165, -39, -79, 4, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 12, -33, -37, 71, 47, -43, -18, 11, 2], ![4, 26, -54, -107, 105, 165, -39, -79, 4, 15], ![30, 184, -469, -609, 958, 810, -480, -309, 86, 34]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 12, -33, -37, 71, 47, -43, -18, 11, 2], ![4, 26, -54, -107, 105, 165, -39, -79, 4, 15], ![30, 184, -469, -609, 958, 810, -480, -309, 86, 34], ![68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 12, -33, -37, 71, 47, -43, -18, 11, 2], ![4, 26, -54, -107, 105, 165, -39, -79, 4, 15], ![30, 184, -469, -609, 958, 810, -480, -309, 86, 34], ![68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], ![308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 12, -33, -37, 71, 47, -43, -18, 11, 2], ![4, 26, -54, -107, 105, 165, -39, -79, 4, 15], ![30, 184, -469, -609, 958, 810, -480, -309, 86, 34], ![68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], ![308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373], ![746, 4784, -10393, -18445, 19847, 26738, -6996, -10780, 679, 1348]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 12, -33, -37, 71, 47, -43, -18, 11, 2], ![4, 26, -54, -107, 105, 165, -39, -79, 4, 15], ![30, 184, -469, -609, 958, 810, -480, -309, 86, 34], ![68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], ![308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373], ![746, 4784, -10393, -18445, 19847, 26738, -6996, -10780, 679, 1348], ![2696, 16922, -39700, -60269, 77263, 83203, -31226, -31260, 4048, 3375]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 12, -33, -37, 71, 47, -43, -18, 11, 2], ![4, 26, -54, -107, 105, 165, -39, -79, 4, 15], ![30, 184, -469, -609, 958, 810, -480, -309, 86, 34], ![68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], ![308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373], ![746, 4784, -10393, -18445, 19847, 26738, -6996, -10780, 679, 1348], ![2696, 16922, -39700, -60269, 77263, 83203, -31226, -31260, 4048, 3375], ![6750, 43196, -94453, -164575, 179356, 235888, -61922, -91976, 5865, 10798]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 12, -33, -37, 71, 47, -43, -18, 11, 2], ![4, 26, -54, -107, 105, 165, -39, -79, 4, 15], ![30, 184, -469, -609, 958, 810, -480, -309, 86, 34], ![68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], ![308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373], ![746, 4784, -10393, -18445, 19847, 26738, -6996, -10780, 679, 1348], ![2696, 16922, -39700, -60269, 77263, 83203, -31226, -31260, 4048, 3375], ![6750, 43196, -94453, -164575, 179356, 235888, -61922, -91976, 5865, 10798], ![21596, 136326, -313138, -493979, 602083, 686862, -228426, -256286, 26802, 27461]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-154, -34, -15, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-154, -34, -15, -2, -1], [-373, -154, -34, -15, -2, -1]], ![[], [], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-154, -34, -15, -2, -1], [-373, -154, -34, -15, -2, -1], [-1348, -373, -154, -34, -15, -2, -1]], ![[], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-154, -34, -15, -2, -1], [-373, -154, -34, -15, -2, -1], [-1348, -373, -154, -34, -15, -2, -1], [-3375, -1348, -373, -154, -34, -15, -2, -1]], ![[], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-154, -34, -15, -2, -1], [-373, -154, -34, -15, -2, -1], [-1348, -373, -154, -34, -15, -2, -1], [-3375, -1348, -373, -154, -34, -15, -2, -1], [-10798, -3375, -1348, -373, -154, -34, -15, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 12, -33, -37, 71, 47, -43, -18, 11, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 12, -33, -37, 71, 47, -43, -18, 11, 2], [4, 26, -54, -107, 105, 165, -39, -79, 4, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 12, -33, -37, 71, 47, -43, -18, 11, 2], [4, 26, -54, -107, 105, 165, -39, -79, 4, 15], [30, 184, -469, -609, 958, 810, -480, -309, 86, 34]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 12, -33, -37, 71, 47, -43, -18, 11, 2], [4, 26, -54, -107, 105, 165, -39, -79, 4, 15], [30, 184, -469, -609, 958, 810, -480, -309, 86, 34], [68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 12, -33, -37, 71, 47, -43, -18, 11, 2], [4, 26, -54, -107, 105, 165, -39, -79, 4, 15], [30, 184, -469, -609, 958, 810, -480, -309, 86, 34], [68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], [308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 12, -33, -37, 71, 47, -43, -18, 11, 2], [4, 26, -54, -107, 105, 165, -39, -79, 4, 15], [30, 184, -469, -609, 958, 810, -480, -309, 86, 34], [68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], [308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373], [746, 4784, -10393, -18445, 19847, 26738, -6996, -10780, 679, 1348]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 12, -33, -37, 71, 47, -43, -18, 11, 2], [4, 26, -54, -107, 105, 165, -39, -79, 4, 15], [30, 184, -469, -609, 958, 810, -480, -309, 86, 34], [68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], [308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373], [746, 4784, -10393, -18445, 19847, 26738, -6996, -10780, 679, 1348], [2696, 16922, -39700, -60269, 77263, 83203, -31226, -31260, 4048, 3375]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 12, -33, -37, 71, 47, -43, -18, 11, 2], [4, 26, -54, -107, 105, 165, -39, -79, 4, 15], [30, 184, -469, -609, 958, 810, -480, -309, 86, 34], [68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], [308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373], [746, 4784, -10393, -18445, 19847, 26738, -6996, -10780, 679, 1348], [2696, 16922, -39700, -60269, 77263, 83203, -31226, -31260, 4048, 3375], [6750, 43196, -94453, -164575, 179356, 235888, -61922, -91976, 5865, 10798]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 12, -33, -37, 71, 47, -43, -18, 11, 2], [4, 26, -54, -107, 105, 165, -39, -79, 4, 15], [30, 184, -469, -609, 958, 810, -480, -309, 86, 34], [68, 438, -938, -1727, 1805, 2556, -652, -1092, 65, 154], [308, 1916, -4644, -6636, 9207, 9043, -4066, -3424, 602, 373], [746, 4784, -10393, -18445, 19847, 26738, -6996, -10780, 679, 1348], [2696, 16922, -39700, -60269, 77263, 83203, -31226, -31260, 4048, 3375], [6750, 43196, -94453, -164575, 179356, 235888, -61922, -91976, 5865, 10798], [21596, 136326, -313138, -493979, 602083, 686862, -228426, -256286, 26802, 27461]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp274517 : Fact (Nat.Prime 274517) := fact_iff.2 (by norm_num)
instance hp6891491 : Fact (Nat.Prime 6891491) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 0, 0, 1]
  b' := [1, 1, 0, 0, 0, 1]
  k := [1, 1, 1, 1, 1, 0, 1, 0, 1]
  f := [1, 6, -16, -18, 36, 24, -21, -9, 6, 1]
  g := [0, 1, 1, 1, 1, 1, 0, 1, 0, 1]
  h := [0, 1]
  a := [1, 1, 0, 1, 1, 1, 0, 1]
  b := [1, 1, 1, 0, 0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD274517 : CertificateDedekindCriterionLists l 274517 where
  n := 2
  a' := [136916, 152075, 153529, 6633, 120551, 212214, 99063, 252386]
  b' := [173945, 194486, 60430, 263980, 197904, 209876, 101013, 176127, 2459]
  k := [141491, 95849, 144267, 112931, 143917, 20775, 148839, 157218, 1]
  f := [194322, 85424, 80844, 173858, 137138, 87636, 178810, 193909, 56099, 1]
  g := [272296, 119700, 113283, 243620, 192165, 122800, 250559, 271716, 78608, 1]
  h := [195907, 1]
  a := [183243, 145306, 41588, 249902, 85492, 28220, 114516, 133024, 130908]
  b := [95542, 71564, 110078, 132613, 61561, 249902, 6364, 84187, 143609]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD6891491 : CertificateDedekindCriterionLists l 6891491 where
  n := 2
  a' := [3650732, 1499440, 908889, 6184270, 5951930, 6619791, 2368087, 6121576]
  b' := [540156, 6584433, 5676251, 5703376, 1530246, 6188613, 5568724, 5485635, 3148431]
  k := [2698035, 1870316, 3198171, 1285511, 6016160, 5676328, 5670937, 4590234, 1]
  f := [4060117, 4175720, 2826036, 1782644, 1625872, 2288779, 3899470, 1772383, 1530759, 1]
  g := [6087465, 6260791, 4237166, 2672775, 2437722, 3431640, 5846601, 2657390, 2295116, 1]
  h := [4596373, 1]
  a := [5066490, 5741083, 2764191, 2121139, 6570629, 334311, 2451137, 3629794, 6003286]
  b := [2196120, 1221829, 1153171, 6607064, 6781159, 4221435, 4789188, 5896886, 888205]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 274517, 6891491]
  exp := ![1, 1, 1]
  pdgood := [2, 274517, 6891491]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp274517.out
    exact hp6891491.out
  a := [251323801486595, -1587559838539773, -1122527581457619, 7003038449242109, -135943236453920, -5522591534980774, 1338015529898178, 935773377938556, -296939306948970]
  b := [-42202605486907, -218844825241288, 871767583289872, 133682076319074, -1644410633119594, 201138069350103, 789833723935651, -191102548009983, -99516123932835, 29693930694897]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 274517 T_ofList CD274517
    exact satisfiesDedekindCriterion_of_certificate_lists T l 6891491 T_ofList CD6891491

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

end VoightMaximalOrderD10R785

end TraceEuclidean
