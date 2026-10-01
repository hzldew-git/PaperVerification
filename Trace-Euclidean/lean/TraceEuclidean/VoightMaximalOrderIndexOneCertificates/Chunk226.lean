import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk222
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

namespace VoightMaximalOrderD10R651

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6726961924889, [-1, -7, -8, 26, 30, -46, -17, 31, -4, -4, 1], 1⟩
local notation "l" => [-1, -7, -8, 26, 30, -46, -17, 31, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 8, -26, -30, 46, 17, -31, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 8, -26, -30, 46, 17, -31, 4, 4], ![4, 29, 39, -96, -146, 154, 114, -107, -15, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 8, -26, -30, 46, 17, -31, 4, 4], ![4, 29, 39, -96, -146, 154, 114, -107, -15, 20], ![20, 144, 189, -481, -696, 774, 494, -506, -27, 65]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 8, -26, -30, 46, 17, -31, 4, 4], ![4, 29, 39, -96, -146, 154, 114, -107, -15, 20], ![20, 144, 189, -481, -696, 774, 494, -506, -27, 65], ![65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 8, -26, -30, 46, 17, -31, 4, 4], ![4, 29, 39, -96, -146, 154, 114, -107, -15, 20], ![20, 144, 189, -481, -696, 774, 494, -506, -27, 65], ![65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], ![233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 8, -26, -30, 46, 17, -31, 4, 4], ![4, 29, 39, -96, -146, 154, 114, -107, -15, 20], ![20, 144, 189, -481, -696, 774, 494, -506, -27, 65], ![65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], ![233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686], ![686, 5035, 7184, -15497, -25974, 23065, 19949, -15011, -2600, 2155]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 8, -26, -30, 46, 17, -31, 4, 4], ![4, 29, 39, -96, -146, 154, 114, -107, -15, 20], ![20, 144, 189, -481, -696, 774, 494, -506, -27, 65], ![65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], ![233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686], ![686, 5035, 7184, -15497, -25974, 23065, 19949, -15011, -2600, 2155], ![2155, 15771, 22275, -48846, -80147, 73156, 59700, -46856, -6391, 6020]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 8, -26, -30, 46, 17, -31, 4, 4], ![4, 29, 39, -96, -146, 154, 114, -107, -15, 20], ![20, 144, 189, -481, -696, 774, 494, -506, -27, 65], ![65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], ![233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686], ![686, 5035, 7184, -15497, -25974, 23065, 19949, -15011, -2600, 2155], ![2155, 15771, 22275, -48846, -80147, 73156, 59700, -46856, -6391, 6020], ![6020, 44295, 63931, -134245, -229446, 196773, 175496, -126920, -22776, 17689]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 8, -26, -30, 46, 17, -31, 4, 4], ![4, 29, 39, -96, -146, 154, 114, -107, -15, 20], ![20, 144, 189, -481, -696, 774, 494, -506, -27, 65], ![65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], ![233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686], ![686, 5035, 7184, -15497, -25974, 23065, 19949, -15011, -2600, 2155], ![2155, 15771, 22275, -48846, -80147, 73156, 59700, -46856, -6391, 6020], ![6020, 44295, 63931, -134245, -229446, 196773, 175496, -126920, -22776, 17689], ![17689, 129843, 185807, -395983, -664915, 584248, 497486, -372863, -56164, 47980]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-65, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-65, -20, -4, -1], [-233, -65, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-65, -20, -4, -1], [-233, -65, -20, -4, -1], [-686, -233, -65, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-65, -20, -4, -1], [-233, -65, -20, -4, -1], [-686, -233, -65, -20, -4, -1], [-2155, -686, -233, -65, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-65, -20, -4, -1], [-233, -65, -20, -4, -1], [-686, -233, -65, -20, -4, -1], [-2155, -686, -233, -65, -20, -4, -1], [-6020, -2155, -686, -233, -65, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-65, -20, -4, -1], [-233, -65, -20, -4, -1], [-686, -233, -65, -20, -4, -1], [-2155, -686, -233, -65, -20, -4, -1], [-6020, -2155, -686, -233, -65, -20, -4, -1], [-17689, -6020, -2155, -686, -233, -65, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 8, -26, -30, 46, 17, -31, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 8, -26, -30, 46, 17, -31, 4, 4], [4, 29, 39, -96, -146, 154, 114, -107, -15, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 8, -26, -30, 46, 17, -31, 4, 4], [4, 29, 39, -96, -146, 154, 114, -107, -15, 20], [20, 144, 189, -481, -696, 774, 494, -506, -27, 65]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 8, -26, -30, 46, 17, -31, 4, 4], [4, 29, 39, -96, -146, 154, 114, -107, -15, 20], [20, 144, 189, -481, -696, 774, 494, -506, -27, 65], [65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 8, -26, -30, 46, 17, -31, 4, 4], [4, 29, 39, -96, -146, 154, 114, -107, -15, 20], [20, 144, 189, -481, -696, 774, 494, -506, -27, 65], [65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], [233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 8, -26, -30, 46, 17, -31, 4, 4], [4, 29, 39, -96, -146, 154, 114, -107, -15, 20], [20, 144, 189, -481, -696, 774, 494, -506, -27, 65], [65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], [233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686], [686, 5035, 7184, -15497, -25974, 23065, 19949, -15011, -2600, 2155]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 8, -26, -30, 46, 17, -31, 4, 4], [4, 29, 39, -96, -146, 154, 114, -107, -15, 20], [20, 144, 189, -481, -696, 774, 494, -506, -27, 65], [65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], [233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686], [686, 5035, 7184, -15497, -25974, 23065, 19949, -15011, -2600, 2155], [2155, 15771, 22275, -48846, -80147, 73156, 59700, -46856, -6391, 6020]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 8, -26, -30, 46, 17, -31, 4, 4], [4, 29, 39, -96, -146, 154, 114, -107, -15, 20], [20, 144, 189, -481, -696, 774, 494, -506, -27, 65], [65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], [233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686], [686, 5035, 7184, -15497, -25974, 23065, 19949, -15011, -2600, 2155], [2155, 15771, 22275, -48846, -80147, 73156, 59700, -46856, -6391, 6020], [6020, 44295, 63931, -134245, -229446, 196773, 175496, -126920, -22776, 17689]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 8, -26, -30, 46, 17, -31, 4, 4], [4, 29, 39, -96, -146, 154, 114, -107, -15, 20], [20, 144, 189, -481, -696, 774, 494, -506, -27, 65], [65, 475, 664, -1501, -2431, 2294, 1879, -1521, -246, 233], [233, 1696, 2339, -5394, -8491, 8287, 6255, -5344, -589, 686], [686, 5035, 7184, -15497, -25974, 23065, 19949, -15011, -2600, 2155], [2155, 15771, 22275, -48846, -80147, 73156, 59700, -46856, -6391, 6020], [6020, 44295, 63931, -134245, -229446, 196773, 175496, -126920, -22776, 17689], [17689, 129843, 185807, -395983, -664915, 584248, 497486, -372863, -56164, 47980]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp97 : Fact (Nat.Prime 97) := fact_iff.2 (by norm_num)
instance hp1949 : Fact (Nat.Prime 1949) := fact_iff.2 (by norm_num)
instance hp366829 : Fact (Nat.Prime 366829) := fact_iff.2 (by norm_num)

def CD97 : CertificateDedekindCriterionLists l 97 where
  n := 3
  a' := [7, 8, 48, 42, 95, 25, 50]
  b' := [61, 13, 71, 82, 63, 34, 21, 18]
  k := [79, 2, 6, 53, 30, 31, 84, 81, 50, 28, 84, 19, 15, 20, 1]
  f := [5, 13, 7, 13, 24, 14, 19, 14, 17, 1]
  g := [44, 22, 11, 92, 21, 67, 24, 70, 1]
  h := [11, 23, 1]
  a := [33, 31, 83, 55, 73, 86, 76, 14]
  b := [58, 90, 82, 74, 85, 5, 60, 84, 83]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1949 : CertificateDedekindCriterionLists l 1949 where
  n := 2
  a' := [1061, 754, 1397, 1276, 1066, 1739, 134, 1156]
  b' := [925, 251, 867, 627, 574, 1705, 311, 1073, 1604]
  k := [1391, 1854, 253, 778, 570, 198, 1803, 1433, 1]
  f := [181, 61, 47, 82, 69, 77, 237, 39, 222, 1]
  g := [1378, 459, 356, 623, 523, 584, 1802, 290, 1689, 1]
  h := [256, 1]
  a := [1600, 158, 912, 394, 635, 1557, 331, 1937, 579]
  b := [1282, 33, 1755, 1196, 643, 1420, 1699, 1590, 1370]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD366829 : CertificateDedekindCriterionLists l 366829 where
  n := 2
  a' := [202197, 62236, 265700, 192702, 320826, 278345, 232746, 361679]
  b' := [303862, 174409, 305563, 127317, 275517, 46748, 328765, 49698, 41331]
  k := [46475, 79956, 12114, 287017, 127647, 7072, 258394, 256953, 1]
  f := [3109, 14803, 21993, 25028, 4885, 24430, 48653, 42181, 46709, 1]
  g := [20760, 98845, 146854, 167119, 32616, 163128, 324872, 281653, 311889, 1]
  h := [54936, 1]
  a := [72577, 349907, 67099, 2213, 136736, 79798, 362351, 123851, 275646]
  b := [154310, 192631, 73338, 68559, 88350, 66422, 91783, 235402, 91183]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![97, 1949, 366829]
  exp := ![1, 1, 1]
  pdgood := [97, 1949, 366829]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp97.out
    exact hp1949.out
    exact hp366829.out
  a := [10402890024782, -9626494126170, -83490371976201, 82104972363158, 83401002878798, -106649577131454, 9218663227484, 18776561982708, -4788593895080]
  b := [-1496034306817, -5608169591176, 5813249741175, 19977340619339, -17644487231320, -13066545716474, 15218584313233, -1243448875938, -2069199954074, 478859389508]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 97 T_ofList CD97
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1949 T_ofList CD1949
    exact satisfiesDedekindCriterion_of_certificate_lists T l 366829 T_ofList CD366829

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

end VoightMaximalOrderD10R651

namespace VoightMaximalOrderD10R654

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6740541378125, [1, 7, 10, -17, -37, 10, 36, -1, -11, 0, 1], 1⟩
local notation "l" => [1, 7, 10, -17, -37, 10, 36, -1, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -10, 17, 37, -10, -36, 1, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], ![0, -1, -7, -10, 17, 37, -10, -36, 1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], ![0, -1, -7, -10, 17, 37, -10, -36, 1, 11], ![-11, -77, -111, 180, 397, -93, -359, 1, 85, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], ![0, -1, -7, -10, 17, 37, -10, -36, 1, 11], ![-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], ![-1, -18, -87, -94, 217, 387, -129, -358, 12, 85]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], ![0, -1, -7, -10, 17, 37, -10, -36, 1, 11], ![-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], ![-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], ![-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], ![0, -1, -7, -10, 17, 37, -10, -36, 1, 11], ![-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], ![-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], ![-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12], ![-12, -169, -716, -664, 1802, 2931, -1065, -2661, 88, 577]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], ![0, -1, -7, -10, 17, 37, -10, -36, 1, 11], ![-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], ![-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], ![-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12], ![-12, -169, -716, -664, 1802, 2931, -1065, -2661, 88, 577], ![-577, -4051, -5939, 9093, 20685, -3968, -17841, -488, 3686, 88]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], ![0, -1, -7, -10, 17, 37, -10, -36, 1, 11], ![-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], ![-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], ![-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12], ![-12, -169, -716, -664, 1802, 2931, -1065, -2661, 88, 577], ![-577, -4051, -5939, 9093, 20685, -3968, -17841, -488, 3686, 88], ![-88, -1193, -4931, -4443, 12349, 19805, -7136, -17753, 480, 3686]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], ![0, -1, -7, -10, 17, 37, -10, -36, 1, 11], ![-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], ![-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], ![-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12], ![-12, -169, -716, -664, 1802, 2931, -1065, -2661, 88, 577], ![-577, -4051, -5939, 9093, 20685, -3968, -17841, -488, 3686, 88], ![-88, -1193, -4931, -4443, 12349, 19805, -7136, -17753, 480, 3686], ![-3686, -25890, -38053, 57731, 131939, -24511, -112891, -3450, 22793, 480]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-85, -1, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-85, -1, -11, 0, -1], [-12, -85, -1, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-85, -1, -11, 0, -1], [-12, -85, -1, -11, 0, -1], [-577, -12, -85, -1, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-85, -1, -11, 0, -1], [-12, -85, -1, -11, 0, -1], [-577, -12, -85, -1, -11, 0, -1], [-88, -577, -12, -85, -1, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-85, -1, -11, 0, -1], [-12, -85, -1, -11, 0, -1], [-577, -12, -85, -1, -11, 0, -1], [-88, -577, -12, -85, -1, -11, 0, -1], [-3686, -88, -577, -12, -85, -1, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -10, 17, 37, -10, -36, 1, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], [0, -1, -7, -10, 17, 37, -10, -36, 1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], [0, -1, -7, -10, 17, 37, -10, -36, 1, 11], [-11, -77, -111, 180, 397, -93, -359, 1, 85, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], [0, -1, -7, -10, 17, 37, -10, -36, 1, 11], [-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], [-1, -18, -87, -94, 217, 387, -129, -358, 12, 85]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], [0, -1, -7, -10, 17, 37, -10, -36, 1, 11], [-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], [-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], [-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], [0, -1, -7, -10, 17, 37, -10, -36, 1, 11], [-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], [-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], [-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12], [-12, -169, -716, -664, 1802, 2931, -1065, -2661, 88, 577]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], [0, -1, -7, -10, 17, 37, -10, -36, 1, 11], [-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], [-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], [-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12], [-12, -169, -716, -664, 1802, 2931, -1065, -2661, 88, 577], [-577, -4051, -5939, 9093, 20685, -3968, -17841, -488, 3686, 88]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], [0, -1, -7, -10, 17, 37, -10, -36, 1, 11], [-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], [-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], [-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12], [-12, -169, -716, -664, 1802, 2931, -1065, -2661, 88, 577], [-577, -4051, -5939, 9093, 20685, -3968, -17841, -488, 3686, 88], [-88, -1193, -4931, -4443, 12349, 19805, -7136, -17753, 480, 3686]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -10, 17, 37, -10, -36, 1, 11, 0], [0, -1, -7, -10, 17, 37, -10, -36, 1, 11], [-11, -77, -111, 180, 397, -93, -359, 1, 85, 1], [-1, -18, -87, -94, 217, 387, -129, -358, 12, 85], [-85, -596, -868, 1358, 3051, -633, -2673, -44, 577, 12], [-12, -169, -716, -664, 1802, 2931, -1065, -2661, 88, 577], [-577, -4051, -5939, 9093, 20685, -3968, -17841, -488, 3686, 88], [-88, -1193, -4931, -4443, 12349, 19805, -7136, -17753, 480, 3686], [-3686, -25890, -38053, 57731, 131939, -24511, -112891, -3450, 22793, 480]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp151 : Fact (Nat.Prime 151) := fact_iff.2 (by norm_num)
instance hp14284591 : Fact (Nat.Prime 14284591) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 2]
  b' := [1, 4, 1, 3, 3]
  k := [1]
  f := [0, -1, -1, 5, 9, 0, -6, 1, 3]
  g := [1, 1, 2, 2, 0, 1]
  h := [1, 1, 2, 2, 0, 1]
  a := [1, 1, 1, 2, 3]
  b := [1, 0, 0, 0, 4, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD151 : CertificateDedekindCriterionLists l 151 where
  n := 2
  a' := [132, 72, 31, 15, 26, 110, 78, 109]
  b' := [74, 123, 38, 106, 53, 65, 51, 73, 55]
  k := [17, 101, 5, 5, 89, 124, 78, 13, 1]
  f := [53, 19, 66, 23, 49, 18, 32, 32, 38, 1]
  g := [116, 40, 144, 48, 106, 38, 70, 69, 82, 1]
  h := [69, 1]
  a := [27, 26, 26, 149, 102, 109, 6, 52, 150]
  b := [84, 81, 68, 82, 73, 138, 115, 55, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD14284591 : CertificateDedekindCriterionLists l 14284591 where
  n := 2
  a' := [4264382, 9627872, 345261, 13938193, 13802482, 8369888, 7057133, 1992499]
  b' := [8832613, 1823055, 7318799, 3900033, 5185028, 8223129, 6273298, 6280146, 1365788]
  k := [5437941, 3996443, 13223488, 6742040, 11882762, 11944178, 11813755, 3691591, 1]
  f := [1892489, 638121, 533923, 2799000, 1781433, 4109390, 5287774, 1460116, 3332642, 1]
  g := [5104018, 1721003, 1439983, 7548866, 4804500, 11082970, 14261055, 3937911, 8988091, 1]
  h := [5296500, 1]
  a := [11283410, 13326457, 8135840, 1776535, 13635964, 1496034, 3039515, 11331984, 8076274]
  b := [9512201, 2745637, 2197872, 6949509, 7275460, 4271473, 13561492, 7516315, 6208317]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 151, 14284591]
  exp := ![1, 1, 1]
  pdgood := [5, 151, 14284591]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp151.out
    exact hp14284591.out
  a := [-1230697549969, -736081837860, 10048588085177, 4474444758480, -16703977241685, -3297725755648, 7325820079424, 462145739430, -863077155580]
  b := [177354630882, 829124581429, -18063596295, -2782927196611, -653172926193, 2867856244657, 405552323572, -922458982170, -46214573943, 86307715558]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 151 T_ofList CD151
    exact satisfiesDedekindCriterion_of_certificate_lists T l 14284591 T_ofList CD14284591

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

end VoightMaximalOrderD10R654

namespace VoightMaximalOrderD10R661

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6788771815625, [1, 1, -17, 6, 69, -80, -1, 32, -8, -3, 1], 1⟩
local notation "l" => [1, 1, -17, 6, 69, -80, -1, 32, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -6, -69, 80, 1, -32, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], ![-3, -4, 50, -1, -213, 171, 83, -95, -8, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], ![-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], ![-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], ![-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], ![-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], ![-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], ![-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], ![-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], ![-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], ![-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], ![-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], ![-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], ![-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], ![-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393], ![-393, -563, 6468, 472, -27426, 19737, 10974, -10140, -1106, 1351]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], ![-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], ![-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], ![-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], ![-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393], ![-393, -563, 6468, 472, -27426, 19737, 10974, -10140, -1106, 1351], ![-1351, -1744, 22404, -1638, -92747, 80654, 21088, -32258, 668, 2947]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], ![-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], ![-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], ![-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], ![-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393], ![-393, -563, 6468, 472, -27426, 19737, 10974, -10140, -1106, 1351], ![-1351, -1744, 22404, -1638, -92747, 80654, 21088, -32258, 668, 2947], ![-2947, -4298, 48355, 4722, -204981, 143013, 83601, -73216, -8682, 9509]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], ![-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], ![-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], ![-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], ![-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393], ![-393, -563, 6468, 472, -27426, 19737, 10974, -10140, -1106, 1351], ![-1351, -1744, 22404, -1638, -92747, 80654, 21088, -32258, 668, 2947], ![-2947, -4298, 48355, 4722, -204981, 143013, 83601, -73216, -8682, 9509], ![-9509, -12456, 157355, -8699, -651399, 555739, 152522, -220687, 2856, 19845]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-43, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-43, -17, -3, -1], [-170, -43, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-43, -17, -3, -1], [-170, -43, -17, -3, -1], [-393, -170, -43, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-43, -17, -3, -1], [-170, -43, -17, -3, -1], [-393, -170, -43, -17, -3, -1], [-1351, -393, -170, -43, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-43, -17, -3, -1], [-170, -43, -17, -3, -1], [-393, -170, -43, -17, -3, -1], [-1351, -393, -170, -43, -17, -3, -1], [-2947, -1351, -393, -170, -43, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-43, -17, -3, -1], [-170, -43, -17, -3, -1], [-393, -170, -43, -17, -3, -1], [-1351, -393, -170, -43, -17, -3, -1], [-2947, -1351, -393, -170, -43, -17, -3, -1], [-9509, -2947, -1351, -393, -170, -43, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -6, -69, 80, 1, -32, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], [-3, -4, 50, -1, -213, 171, 83, -95, -8, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], [-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], [-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], [-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], [-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], [-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], [-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], [-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], [-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], [-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], [-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], [-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], [-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], [-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393], [-393, -563, 6468, 472, -27426, 19737, 10974, -10140, -1106, 1351]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], [-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], [-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], [-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], [-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393], [-393, -563, 6468, 472, -27426, 19737, 10974, -10140, -1106, 1351], [-1351, -1744, 22404, -1638, -92747, 80654, 21088, -32258, 668, 2947]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], [-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], [-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], [-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], [-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393], [-393, -563, 6468, 472, -27426, 19737, 10974, -10140, -1106, 1351], [-1351, -1744, 22404, -1638, -92747, 80654, 21088, -32258, 668, 2947], [-2947, -4298, 48355, 4722, -204981, 143013, 83601, -73216, -8682, 9509]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -6, -69, 80, 1, -32, 8, 3], [-3, -4, 50, -1, -213, 171, 83, -95, -8, 17], [-17, -20, 285, -52, -1174, 1147, 188, -461, 41, 43], [-43, -60, 711, 27, -3019, 2266, 1190, -1188, -117, 170], [-170, -213, 2830, -309, -11703, 10581, 2436, -4250, 172, 393], [-393, -563, 6468, 472, -27426, 19737, 10974, -10140, -1106, 1351], [-1351, -1744, 22404, -1638, -92747, 80654, 21088, -32258, 668, 2947], [-2947, -4298, 48355, 4722, -204981, 143013, 83601, -73216, -8682, 9509], [-9509, -12456, 157355, -8699, -651399, 555739, 152522, -220687, 2856, 19845]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2172406981 : Fact (Nat.Prime 2172406981) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 4, 2]
  b' := [0, 3, 2, 4, 2]
  k := [1]
  f := [3, 3, 9, 6, -8, 22, 4, -4, 3, 1]
  g := [4, 2, 3, 3, 1, 1]
  h := [4, 2, 3, 3, 1, 1]
  a := [4, 3, 2, 2, 1]
  b := [1, 3, 0, 0, 3, 2, 3, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2172406981 : CertificateDedekindCriterionLists l 2172406981 where
  n := 2
  a' := [326676467, 724531041, 1965697481, 168854278, 707123034, 318538576, 541576387, 1660557503]
  b' := [1130024417, 2018275283, 1865015110, 1209696891, 1849182275, 1688289455, 841535750, 1519211346, 1022386378]
  k := [965824232, 1848208556, 1890070227, 858373997, 64769007, 1991057291, 380817712, 1562763143, 1]
  f := [104068595, 876661979, 111950590, 644274954, 1326853642, 726378064, 1331267012, 971975971, 500330568, 1]
  g := [162527112, 1369109861, 174836664, 1006183927, 2072187968, 1134406867, 2079080463, 1517964640, 781381570, 1]
  h := [1391025408, 1]
  a := [1261351357, 1700986204, 1933348273, 1269041298, 1334688939, 402231288, 1082737031, 998156056, 1442709524]
  b := [1885052502, 2082359273, 382734375, 1441359254, 1269147446, 959027634, 421272785, 849985945, 729697457]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 2172406981]
  exp := ![1, 1]
  pdgood := [5, 2172406981]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2172406981.out
  a := [1418226519595, -44844459447778, -70650193266887, 238794163235596, -54565815904953, -125019551410036, 49220580025944, 14752566680122, -6611604836860]
  b := [-1407364484690, -4424159551277, 14515639528782, 22590073977509, -49169260039427, 7912435087273, 18309482359055, -6072877767874, -1673604813118, 661160483686]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2172406981 T_ofList CD2172406981

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

end VoightMaximalOrderD10R661

namespace VoightMaximalOrderD10R664

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6791803690625, [-1, -8, -4, 42, 7, -57, 0, 27, -4, -4, 1], 1⟩
local notation "l" => [-1, -8, -4, 42, 7, -57, 0, 27, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 4, -42, -7, 57, 0, -27, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 4, -42, -7, 57, 0, -27, 4, 4], ![4, 33, 24, -164, -70, 221, 57, -108, -11, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 4, -42, -7, 57, 0, -27, 4, 4], ![4, 33, 24, -164, -70, 221, 57, -108, -11, 20], ![20, 164, 113, -816, -304, 1070, 221, -483, -28, 69]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 4, -42, -7, 57, 0, -27, 4, 4], ![4, 33, 24, -164, -70, 221, 57, -108, -11, 20], ![20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], ![69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 4, -42, -7, 57, 0, -27, 4, 4], ![4, 33, 24, -164, -70, 221, 57, -108, -11, 20], ![20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], ![69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], ![248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 4, -42, -7, 57, 0, -27, 4, 4], ![4, 33, 24, -164, -70, 221, 57, -108, -11, 20], ![20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], ![69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], ![248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785], ![785, 6528, 5193, -31406, -15471, 40224, 12837, -17566, -2486, 2490]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 4, -42, -7, 57, 0, -27, 4, 4], ![4, 33, 24, -164, -70, 221, 57, -108, -11, 20], ![20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], ![69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], ![248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785], ![785, 6528, 5193, -31406, -15471, 40224, 12837, -17566, -2486, 2490], ![2490, 20705, 16488, -99387, -48836, 126459, 40224, -54393, -7606, 7474]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 4, -42, -7, 57, 0, -27, 4, 4], ![4, 33, 24, -164, -70, 221, 57, -108, -11, 20], ![20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], ![69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], ![248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785], ![785, 6528, 5193, -31406, -15471, 40224, 12837, -17566, -2486, 2490], ![2490, 20705, 16488, -99387, -48836, 126459, 40224, -54393, -7606, 7474], ![7474, 62282, 50601, -297420, -151705, 377182, 126459, -161574, -24497, 22290]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 4, -42, -7, 57, 0, -27, 4, 4], ![4, 33, 24, -164, -70, 221, 57, -108, -11, 20], ![20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], ![69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], ![248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785], ![785, 6528, 5193, -31406, -15471, 40224, 12837, -17566, -2486, 2490], ![2490, 20705, 16488, -99387, -48836, 126459, 40224, -54393, -7606, 7474], ![7474, 62282, 50601, -297420, -151705, 377182, 126459, -161574, -24497, 22290], ![22290, 185794, 151442, -885579, -453450, 1118825, 377182, -475371, -72414, 64663]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-248, -69, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-248, -69, -20, -4, -1], [-785, -248, -69, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-248, -69, -20, -4, -1], [-785, -248, -69, -20, -4, -1], [-2490, -785, -248, -69, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-248, -69, -20, -4, -1], [-785, -248, -69, -20, -4, -1], [-2490, -785, -248, -69, -20, -4, -1], [-7474, -2490, -785, -248, -69, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-248, -69, -20, -4, -1], [-785, -248, -69, -20, -4, -1], [-2490, -785, -248, -69, -20, -4, -1], [-7474, -2490, -785, -248, -69, -20, -4, -1], [-22290, -7474, -2490, -785, -248, -69, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 4, -42, -7, 57, 0, -27, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 4, -42, -7, 57, 0, -27, 4, 4], [4, 33, 24, -164, -70, 221, 57, -108, -11, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 4, -42, -7, 57, 0, -27, 4, 4], [4, 33, 24, -164, -70, 221, 57, -108, -11, 20], [20, 164, 113, -816, -304, 1070, 221, -483, -28, 69]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 4, -42, -7, 57, 0, -27, 4, 4], [4, 33, 24, -164, -70, 221, 57, -108, -11, 20], [20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], [69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 4, -42, -7, 57, 0, -27, 4, 4], [4, 33, 24, -164, -70, 221, 57, -108, -11, 20], [20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], [69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], [248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 4, -42, -7, 57, 0, -27, 4, 4], [4, 33, 24, -164, -70, 221, 57, -108, -11, 20], [20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], [69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], [248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785], [785, 6528, 5193, -31406, -15471, 40224, 12837, -17566, -2486, 2490]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 4, -42, -7, 57, 0, -27, 4, 4], [4, 33, 24, -164, -70, 221, 57, -108, -11, 20], [20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], [69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], [248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785], [785, 6528, 5193, -31406, -15471, 40224, 12837, -17566, -2486, 2490], [2490, 20705, 16488, -99387, -48836, 126459, 40224, -54393, -7606, 7474]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 4, -42, -7, 57, 0, -27, 4, 4], [4, 33, 24, -164, -70, 221, 57, -108, -11, 20], [20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], [69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], [248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785], [785, 6528, 5193, -31406, -15471, 40224, 12837, -17566, -2486, 2490], [2490, 20705, 16488, -99387, -48836, 126459, 40224, -54393, -7606, 7474], [7474, 62282, 50601, -297420, -151705, 377182, 126459, -161574, -24497, 22290]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 4, -42, -7, 57, 0, -27, 4, 4], [4, 33, 24, -164, -70, 221, 57, -108, -11, 20], [20, 164, 113, -816, -304, 1070, 221, -483, -28, 69], [69, 572, 440, -2785, -1299, 3629, 1070, -1642, -207, 248], [248, 2053, 1564, -9976, -4521, 12837, 3629, -5626, -650, 785], [785, 6528, 5193, -31406, -15471, 40224, 12837, -17566, -2486, 2490], [2490, 20705, 16488, -99387, -48836, 126459, 40224, -54393, -7606, 7474], [7474, 62282, 50601, -297420, -151705, 377182, 126459, -161574, -24497, 22290], [22290, 185794, 151442, -885579, -453450, 1118825, 377182, -475371, -72414, 64663]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1901 : Fact (Nat.Prime 1901) := fact_iff.2 (by norm_num)
instance hp1143281 : Fact (Nat.Prime 1143281) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 2, 1]
  b' := [4, 2, 4, 2, 2]
  k := [1]
  f := [1, 4, 5, -4, 4, 17, 5, -3, 3, 2]
  g := [2, 3, 3, 1, 3, 1]
  h := [2, 3, 3, 1, 3, 1]
  a := [3, 1, 3, 2, 2]
  b := [4, 0, 3, 0, 3, 4, 2, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1901 : CertificateDedekindCriterionLists l 1901 where
  n := 2
  a' := [170, 1624, 1441, 1345, 738, 1751, 429, 933]
  b' := [711, 983, 124, 426, 765, 1565, 671, 883, 530]
  k := [330, 1420, 1337, 1622, 282, 1219, 1165, 961, 1]
  f := [113, 355, 421, 9, 130, 117, 210, 93, 352, 1]
  g := [459, 1441, 1707, 33, 528, 474, 852, 376, 1429, 1]
  h := [468, 1]
  a := [1080, 96, 329, 1850, 1657, 1216, 1070, 177, 960]
  b := [608, 119, 96, 1487, 756, 105, 24, 1500, 941]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1143281 : CertificateDedekindCriterionLists l 1143281 where
  n := 2
  a' := [390377, 793477, 811224, 641441, 1003284, 65522, 819962, 9493]
  b' := [300835, 81183, 1028395, 410788, 494799, 873230, 139309, 9474, 1015195]
  k := [31942, 161785, 210186, 1052722, 585338, 1037963, 274654, 1064009, 1]
  f := [13075, 24225, 25250, 31101, 30541, 18397, 12235, 5006, 38260, 1]
  g := [377161, 698784, 728343, 897120, 880962, 530657, 352917, 144394, 1103643, 1]
  h := [39634, 1]
  a := [260511, 890306, 886639, 128882, 1040615, 331654, 140741, 519742, 871441]
  b := [242253, 1015021, 631946, 498675, 87831, 566357, 39766, 565177, 271840]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 1901, 1143281]
  exp := ![1, 1, 1]
  pdgood := [5, 1901, 1143281]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1901.out
    exact hp1143281.out
  a := [57466857063, -146298250152, -412517849870, 689320424592, 583467172438, -842197573840, -9341179364, 211905401052, -49352621520]
  b := [-8541717871, -30637857923, 65235354309, 123525292308, -172779475097, -87933467742, 125173453928, -1644653242, -23164644966, 4935262152]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1901 T_ofList CD1901
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1143281 T_ofList CD1143281

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

end VoightMaximalOrderD10R664

end TraceEuclidean
