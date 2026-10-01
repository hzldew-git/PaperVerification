import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk194
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

namespace VoightMaximalOrderD10R321

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4315461526453, [9, -23, -24, 77, 4, -71, 13, 25, -7, -3, 1], 1⟩
local notation "l" => [9, -23, -24, 77, 4, -71, 13, 25, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-9, 23, 24, -77, -4, 71, -13, -25, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], ![-27, 60, 95, -207, -89, 209, 32, -88, -4, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], ![-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], ![-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], ![-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], ![-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], ![-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], ![-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], ![-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], ![-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], ![-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], ![-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], ![-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], ![-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], ![-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408], ![-3672, 7980, 12984, -26804, -12247, 25400, 4459, -9375, -569, 1217]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], ![-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], ![-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], ![-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], ![-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408], ![-3672, 7980, 12984, -26804, -12247, 25400, 4459, -9375, -569, 1217], ![-10953, 24319, 37188, -80725, -31672, 74160, 9579, -25966, -856, 3082]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], ![-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], ![-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], ![-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], ![-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408], ![-3672, 7980, 12984, -26804, -12247, 25400, 4459, -9375, -569, 1217], ![-10953, 24319, 37188, -80725, -31672, 74160, 9579, -25966, -856, 3082], ![-27738, 59933, 98287, -200126, -93053, 187150, 34094, -67471, -4392, 8390]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], ![-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], ![-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], ![-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], ![-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408], ![-3672, 7980, 12984, -26804, -12247, 25400, 4459, -9375, -569, 1217], ![-10953, 24319, 37188, -80725, -31672, 74160, 9579, -25966, -856, 3082], ![-27738, 59933, 98287, -200126, -93053, 187150, 34094, -67471, -4392, 8390], ![-75510, 165232, 261293, -547743, -233686, 502637, 78080, -175656, -8741, 20778]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-156, -44, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-156, -44, -16, -3, -1], [-408, -156, -44, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-156, -44, -16, -3, -1], [-408, -156, -44, -16, -3, -1], [-1217, -408, -156, -44, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-156, -44, -16, -3, -1], [-408, -156, -44, -16, -3, -1], [-1217, -408, -156, -44, -16, -3, -1], [-3082, -1217, -408, -156, -44, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-156, -44, -16, -3, -1], [-408, -156, -44, -16, -3, -1], [-1217, -408, -156, -44, -16, -3, -1], [-3082, -1217, -408, -156, -44, -16, -3, -1], [-8390, -3082, -1217, -408, -156, -44, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-9, 23, 24, -77, -4, 71, -13, -25, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], [-27, 60, 95, -207, -89, 209, 32, -88, -4, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], [-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], [-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], [-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], [-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], [-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], [-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], [-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], [-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], [-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], [-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], [-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], [-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], [-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408], [-3672, 7980, 12984, -26804, -12247, 25400, 4459, -9375, -569, 1217]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], [-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], [-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], [-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], [-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408], [-3672, 7980, 12984, -26804, -12247, 25400, 4459, -9375, -569, 1217], [-10953, 24319, 37188, -80725, -31672, 74160, 9579, -25966, -856, 3082]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], [-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], [-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], [-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], [-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408], [-3672, 7980, 12984, -26804, -12247, 25400, 4459, -9375, -569, 1217], [-10953, 24319, 37188, -80725, -31672, 74160, 9579, -25966, -856, 3082], [-27738, 59933, 98287, -200126, -93053, 187150, 34094, -67471, -4392, 8390]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-9, 23, 24, -77, -4, 71, -13, -25, 7, 3], [-27, 60, 95, -207, -89, 209, 32, -88, -4, 16], [-144, 341, 444, -1137, -271, 1047, 1, -368, 24, 44], [-396, 868, 1397, -2944, -1313, 2853, 475, -1099, -60, 156], [-1404, 3192, 4612, -10615, -3568, 9763, 825, -3425, -7, 408], [-3672, 7980, 12984, -26804, -12247, 25400, 4459, -9375, -569, 1217], [-10953, 24319, 37188, -80725, -31672, 74160, 9579, -25966, -856, 3082], [-27738, 59933, 98287, -200126, -93053, 187150, 34094, -67471, -4392, 8390], [-75510, 165232, 261293, -547743, -233686, 502637, 78080, -175656, -8741, 20778]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp277 : Fact (Nat.Prime 277) := fact_iff.2 (by norm_num)
instance hp1621 : Fact (Nat.Prime 1621) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [0, 1, 4, 0, 1, 5, 4]
  b' := [3, 4, 2, 1, 4, 2, 1, 3]
  k := [4, 2, 3, 0, 6, 0, 1]
  f := [-1, 5, 5, -10, 0, 12, 0, -2, 2, 1]
  g := [1, 5, 0, 1, 1, 5, 1, 2, 1]
  h := [2, 2, 1]
  a := [1, 5, 0, 5, 1, 2, 6, 2]
  b := [2, 4, 6, 0, 6, 1, 4, 1, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [1, 5, 2, 2, 2, 4, 9]
  b' := [9, 6, 1, 8, 8, 2, 4, 3]
  k := [4, 5, 3, 10, 3, 5, 1]
  f := [3, 11, 11, 2, 9, 11, 0, -1, 2, 1]
  g := [6, 8, 5, 8, 6, 0, 1, 1, 1]
  h := [7, 7, 1]
  a := [1, 7, 2, 10, 10, 5, 0, 3]
  b := [7, 0, 6, 3, 10, 1, 4, 8, 8]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD277 : CertificateDedekindCriterionLists l 277 where
  n := 2
  a' := [262, 113, 132, 242, 203, 58, 199, 276]
  b' := [137, 55, 2, 198, 241, 257, 234, 240, 154]
  k := [222, 51, 57, 160, 50, 220, 215, 84, 1]
  f := [13, 28, 70, 8, 69, 61, 51, 56, 62, 1]
  g := [38, 81, 203, 22, 201, 175, 147, 162, 179, 1]
  h := [95, 1]
  a := [275, 3, 139, 60, 186, 98, 264, 191, 276]
  b := [8, 49, 40, 67, 196, 116, 262, 246, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1621 : CertificateDedekindCriterionLists l 1621 where
  n := 2
  a' := [1177, 1314, 995, 916, 246, 833, 934]
  b' := [701, 878, 721, 1299, 204, 1345, 1313, 1099]
  k := [1485, 489, 200, 1370, 1277, 444, 1]
  f := [45, 467, 493, 512, 625, 540, 351, 398, 374, 1]
  g := [1158, 1226, 1243, 1574, 1396, 861, 987, 1031, 1]
  h := [63, 587, 1]
  a := [389, 98, 138, 22, 1297, 824, 636, 471]
  b := [668, 1474, 75, 447, 537, 109, 1159, 821, 1150]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![7, 11, 277, 1621]
  exp := ![1, 1, 1, 1]
  pdgood := [7, 11, 277, 1621]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp11.out
    exact hp277.out
    exact hp1621.out
  a := [-82228131, -285827676, 477027630, 592623410, -600666500, -347871550, 259198089, 59717332, -36842860]
  b := [-33679456, 40670079, 135158358, -119191778, -142301280, 99232898, 55219038, -32270561, -7077019, 3684286]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 277 T_ofList CD277
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1621 T_ofList CD1621

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

end VoightMaximalOrderD10R321

namespace VoightMaximalOrderD10R324

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4356892278125, [1, 5, -109, 105, 88, -117, -8, 39, -6, -4, 1], 1⟩
local notation "l" => [1, 5, -109, 105, 88, -117, -8, 39, -6, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -5, 109, -105, -88, 117, 8, -39, 6, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], ![-4, -21, 431, -311, -457, 380, 149, -148, -15, 22]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], ![-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], ![-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], ![-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], ![-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], ![-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], ![-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], ![-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], ![-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], ![-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], ![-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], ![-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], ![-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], ![-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833], ![-833, -4441, 89344, -57768, -94441, 67885, 30653, -23985, -3065, 2697]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], ![-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], ![-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], ![-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], ![-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833], ![-833, -4441, 89344, -57768, -94441, 67885, 30653, -23985, -3065, 2697], ![-2697, -14318, 289532, -193841, -295104, 221108, 89461, -74530, -7803, 7723]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], ![-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], ![-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], ![-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], ![-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833], ![-833, -4441, 89344, -57768, -94441, 67885, 30653, -23985, -3065, 2697], ![-2697, -14318, 289532, -193841, -295104, 221108, 89461, -74530, -7803, 7723], ![-7723, -41312, 827489, -521383, -873465, 608487, 282892, -211736, -28192, 23089]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], ![-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], ![-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], ![-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], ![-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833], ![-833, -4441, 89344, -57768, -94441, 67885, 30653, -23985, -3065, 2697], ![-2697, -14318, 289532, -193841, -295104, 221108, 89461, -74530, -7803, 7723], ![-7723, -41312, 827489, -521383, -873465, 608487, 282892, -211736, -28192, 23089], ![-23089, -123168, 2475389, -1596856, -2553215, 1827948, 793199, -617579, -73202, 64164]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-22, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-22, -4, -1], [-73, -22, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-22, -4, -1], [-73, -22, -4, -1], [-276, -73, -22, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-22, -4, -1], [-73, -22, -4, -1], [-276, -73, -22, -4, -1], [-833, -276, -73, -22, -4, -1]], ![[], [], [], [-1], [-4, -1], [-22, -4, -1], [-73, -22, -4, -1], [-276, -73, -22, -4, -1], [-833, -276, -73, -22, -4, -1], [-2697, -833, -276, -73, -22, -4, -1]], ![[], [], [-1], [-4, -1], [-22, -4, -1], [-73, -22, -4, -1], [-276, -73, -22, -4, -1], [-833, -276, -73, -22, -4, -1], [-2697, -833, -276, -73, -22, -4, -1], [-7723, -2697, -833, -276, -73, -22, -4, -1]], ![[], [-1], [-4, -1], [-22, -4, -1], [-73, -22, -4, -1], [-276, -73, -22, -4, -1], [-833, -276, -73, -22, -4, -1], [-2697, -833, -276, -73, -22, -4, -1], [-7723, -2697, -833, -276, -73, -22, -4, -1], [-23089, -7723, -2697, -833, -276, -73, -22, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -5, 109, -105, -88, 117, 8, -39, 6, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], [-4, -21, 431, -311, -457, 380, 149, -148, -15, 22]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], [-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], [-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], [-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], [-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], [-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], [-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], [-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], [-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], [-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], [-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], [-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], [-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], [-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833], [-833, -4441, 89344, -57768, -94441, 67885, 30653, -23985, -3065, 2697]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], [-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], [-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], [-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], [-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833], [-833, -4441, 89344, -57768, -94441, 67885, 30653, -23985, -3065, 2697], [-2697, -14318, 289532, -193841, -295104, 221108, 89461, -74530, -7803, 7723]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], [-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], [-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], [-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], [-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833], [-833, -4441, 89344, -57768, -94441, 67885, 30653, -23985, -3065, 2697], [-2697, -14318, 289532, -193841, -295104, 221108, 89461, -74530, -7803, 7723], [-7723, -41312, 827489, -521383, -873465, 608487, 282892, -211736, -28192, 23089]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -5, 109, -105, -88, 117, 8, -39, 6, 4], [-4, -21, 431, -311, -457, 380, 149, -148, -15, 22], [-22, -114, 2377, -1879, -2247, 2117, 556, -709, -16, 73], [-73, -387, 7843, -5288, -8303, 6294, 2701, -2291, -271, 276], [-276, -1453, 29697, -21137, -29576, 23989, 8502, -8063, -635, 833], [-833, -4441, 89344, -57768, -94441, 67885, 30653, -23985, -3065, 2697], [-2697, -14318, 289532, -193841, -295104, 221108, 89461, -74530, -7803, 7723], [-7723, -41312, 827489, -521383, -873465, 608487, 282892, -211736, -28192, 23089], [-23089, -123168, 2475389, -1596856, -2553215, 1827948, 793199, -617579, -73202, 64164]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp739 : Fact (Nat.Prime 739) := fact_iff.2 (by norm_num)
instance hp1886611 : Fact (Nat.Prime 1886611) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 1, 1]
  b' := [4, 2, 0, 3, 2]
  k := [1]
  f := [3, -1, 25, -21, -12, 25, 4, -7, 3, 2]
  g := [4, 0, 2, 0, 3, 1]
  h := [4, 0, 2, 0, 3, 1]
  a := [4, 2, 3, 2]
  b := [1, 2, 4, 3, 4, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD739 : CertificateDedekindCriterionLists l 739 where
  n := 2
  a' := [606, 656, 72, 289, 689, 515, 447, 167]
  b' := [123, 1, 50, 682, 713, 622, 498, 89, 392]
  k := [333, 687, 314, 714, 260, 424, 461, 312, 1]
  f := [467, 331, 463, 448, 220, 407, 7, 533, 122, 1]
  g := [594, 420, 588, 569, 279, 517, 8, 678, 154, 1]
  h := [581, 1]
  a := [557, 610, 26, 490, 599, 0, 630, 588, 557]
  b := [637, 530, 717, 157, 475, 82, 414, 239, 182]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1886611 : CertificateDedekindCriterionLists l 1886611 where
  n := 2
  a' := [353562, 11649, 1027324, 784451, 623539, 220723, 1595197, 1862019]
  b' := [1567588, 607892, 70193, 972467, 117177, 616264, 1649642, 344704, 1679720]
  k := [704112, 1769287, 1303649, 1592049, 1518431, 1769628, 297466, 446710, 1]
  f := [1265627, 717622, 259831, 102504, 1485891, 818145, 1265862, 1488116, 196911, 1]
  g := [1435587, 813990, 294723, 116269, 1685430, 928012, 1435853, 1687953, 223353, 1]
  h := [1663254, 1]
  a := [1147632, 666194, 547431, 401068, 1460774, 1412629, 90917, 1022548, 1850555]
  b := [903485, 220794, 399014, 1430208, 1066491, 1829233, 1472797, 209866, 36056]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 739, 1886611]
  exp := ![1, 1, 1]
  pdgood := [5, 739, 1886611]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp739.out
    exact hp1886611.out
  a := [2023455594185, -86594951737534, 69503109608864, 188167825292664, -110922627933154, -93049948523798, 48287759205712, 12715976562492, -6071976112820]
  b := [-403296913308, -2288210666907, 42447382230253, -14143950072468, -44891353774567, 17363741305048, 14761109573820, -5923138551856, -1514476700762, 607197611282]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 739 T_ofList CD739
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1886611 T_ofList CD1886611

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

end VoightMaximalOrderD10R324

namespace VoightMaximalOrderD10R330

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4387790403125, [-1, 1, 15, 8, -35, -21, 29, 13, -9, -2, 1], 1⟩
local notation "l" => [-1, 1, 15, 8, -35, -21, 29, 13, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -15, -8, 35, 21, -29, -13, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -15, -8, 35, 21, -29, -13, 9, 2], ![2, -1, -31, -31, 62, 77, -37, -55, 5, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -15, -8, 35, 21, -29, -13, 9, 2], ![2, -1, -31, -31, 62, 77, -37, -55, 5, 13], ![13, -11, -196, -135, 424, 335, -300, -206, 62, 31]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -15, -8, 35, 21, -29, -13, 9, 2], ![2, -1, -31, -31, 62, 77, -37, -55, 5, 13], ![13, -11, -196, -135, 424, 335, -300, -206, 62, 31], ![31, -18, -476, -444, 950, 1075, -564, -703, 73, 124]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -15, -8, 35, 21, -29, -13, 9, 2], ![2, -1, -31, -31, 62, 77, -37, -55, 5, 13], ![13, -11, -196, -135, 424, 335, -300, -206, 62, 31], ![31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], ![124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -15, -8, 35, 21, -29, -13, 9, 2], ![2, -1, -31, -31, 62, 77, -37, -55, 5, 13], ![13, -11, -196, -135, 424, 335, -300, -206, 62, 31], ![31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], ![124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321], ![321, -197, -4908, -4446, 9767, 10637, -5755, -6694, 713, 1055]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -15, -8, 35, 21, -29, -13, 9, 2], ![2, -1, -31, -31, 62, 77, -37, -55, 5, 13], ![13, -11, -196, -135, 424, 335, -300, -206, 62, 31], ![31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], ![124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321], ![321, -197, -4908, -4446, 9767, 10637, -5755, -6694, 713, 1055], ![1055, -734, -16022, -13348, 32479, 31922, -19958, -19470, 2801, 2823]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -15, -8, 35, 21, -29, -13, 9, 2], ![2, -1, -31, -31, 62, 77, -37, -55, 5, 13], ![13, -11, -196, -135, 424, 335, -300, -206, 62, 31], ![31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], ![124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321], ![321, -197, -4908, -4446, 9767, 10637, -5755, -6694, 713, 1055], ![1055, -734, -16022, -13348, 32479, 31922, -19958, -19470, 2801, 2823], ![2823, -1768, -43079, -38606, 85457, 91762, -49945, -56657, 5937, 8447]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -15, -8, 35, 21, -29, -13, 9, 2], ![2, -1, -31, -31, 62, 77, -37, -55, 5, 13], ![13, -11, -196, -135, 424, 335, -300, -206, 62, 31], ![31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], ![124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321], ![321, -197, -4908, -4446, 9767, 10637, -5755, -6694, 713, 1055], ![1055, -734, -16022, -13348, 32479, 31922, -19958, -19470, 2801, 2823], ![2823, -1768, -43079, -38606, 85457, 91762, -49945, -56657, 5937, 8447], ![8447, -5624, -128473, -110655, 257039, 262844, -153201, -159756, 19366, 22831]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-124, -31, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-124, -31, -13, -2, -1], [-321, -124, -31, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-124, -31, -13, -2, -1], [-321, -124, -31, -13, -2, -1], [-1055, -321, -124, -31, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-124, -31, -13, -2, -1], [-321, -124, -31, -13, -2, -1], [-1055, -321, -124, -31, -13, -2, -1], [-2823, -1055, -321, -124, -31, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-124, -31, -13, -2, -1], [-321, -124, -31, -13, -2, -1], [-1055, -321, -124, -31, -13, -2, -1], [-2823, -1055, -321, -124, -31, -13, -2, -1], [-8447, -2823, -1055, -321, -124, -31, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -15, -8, 35, 21, -29, -13, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -15, -8, 35, 21, -29, -13, 9, 2], [2, -1, -31, -31, 62, 77, -37, -55, 5, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -15, -8, 35, 21, -29, -13, 9, 2], [2, -1, -31, -31, 62, 77, -37, -55, 5, 13], [13, -11, -196, -135, 424, 335, -300, -206, 62, 31]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -15, -8, 35, 21, -29, -13, 9, 2], [2, -1, -31, -31, 62, 77, -37, -55, 5, 13], [13, -11, -196, -135, 424, 335, -300, -206, 62, 31], [31, -18, -476, -444, 950, 1075, -564, -703, 73, 124]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -15, -8, 35, 21, -29, -13, 9, 2], [2, -1, -31, -31, 62, 77, -37, -55, 5, 13], [13, -11, -196, -135, 424, 335, -300, -206, 62, 31], [31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], [124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -15, -8, 35, 21, -29, -13, 9, 2], [2, -1, -31, -31, 62, 77, -37, -55, 5, 13], [13, -11, -196, -135, 424, 335, -300, -206, 62, 31], [31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], [124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321], [321, -197, -4908, -4446, 9767, 10637, -5755, -6694, 713, 1055]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -15, -8, 35, 21, -29, -13, 9, 2], [2, -1, -31, -31, 62, 77, -37, -55, 5, 13], [13, -11, -196, -135, 424, 335, -300, -206, 62, 31], [31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], [124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321], [321, -197, -4908, -4446, 9767, 10637, -5755, -6694, 713, 1055], [1055, -734, -16022, -13348, 32479, 31922, -19958, -19470, 2801, 2823]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -15, -8, 35, 21, -29, -13, 9, 2], [2, -1, -31, -31, 62, 77, -37, -55, 5, 13], [13, -11, -196, -135, 424, 335, -300, -206, 62, 31], [31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], [124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321], [321, -197, -4908, -4446, 9767, 10637, -5755, -6694, 713, 1055], [1055, -734, -16022, -13348, 32479, 31922, -19958, -19470, 2801, 2823], [2823, -1768, -43079, -38606, 85457, 91762, -49945, -56657, 5937, 8447]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -15, -8, 35, 21, -29, -13, 9, 2], [2, -1, -31, -31, 62, 77, -37, -55, 5, 13], [13, -11, -196, -135, 424, 335, -300, -206, 62, 31], [31, -18, -476, -444, 950, 1075, -564, -703, 73, 124], [124, -93, -1878, -1468, 3896, 3554, -2521, -2176, 413, 321], [321, -197, -4908, -4446, 9767, 10637, -5755, -6694, 713, 1055], [1055, -734, -16022, -13348, 32479, 31922, -19958, -19470, 2801, 2823], [2823, -1768, -43079, -38606, 85457, 91762, -49945, -56657, 5937, 8447], [8447, -5624, -128473, -110655, 257039, 262844, -153201, -159756, 19366, 22831]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp34246169 : Fact (Nat.Prime 34246169) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 4, 4]
  b' := [4, 2, 2, 0, 1]
  k := [1]
  f := [2, 1, 2, 0, 15, 7, 1, -1, 5, 2]
  g := [3, 1, 4, 0, 4, 1]
  h := [3, 1, 4, 0, 4, 1]
  a := [2, 2, 2, 4, 4]
  b := [4, 0, 3, 1, 0, 2, 4, 4, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [23, 23, 10, 3, 30, 11, 17, 30]
  b' := [3, 31, 8, 15, 36, 8, 9, 33, 24]
  k := [10, 21, 11, 37, 13, 34, 11, 35, 1]
  f := [1, 1, 0, 0, 2, 3, 1, 2, 3, 1]
  g := [20, 11, 2, 3, 22, 40, 15, 40, 37, 1]
  h := [2, 1]
  a := [3, 15, 2, 22, 29, 18, 24, 27, 34]
  b := [4, 1, 31, 20, 40, 1, 4, 22, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD34246169 : CertificateDedekindCriterionLists l 34246169 where
  n := 2
  a' := [19334963, 15835099, 25801709, 17875455, 14349746, 9608156, 15366563, 14061378]
  b' := [6945019, 28684047, 11322010, 4066206, 15016000, 15434829, 10096062, 22807730, 21268404]
  k := [2886528, 14458429, 17933533, 7710448, 23325896, 2172529, 23068580, 2537112, 1]
  f := [11626809, 18571199, 1403106, 25245471, 9775929, 6649722, 23486861, 6590306, 1221565, 1]
  g := [12074060, 19285581, 1457079, 26216594, 10151981, 6905518, 24390335, 6843816, 1268555, 1]
  h := [32977612, 1]
  a := [15559074, 31842171, 15654416, 20877635, 25274466, 8609517, 18069326, 27160717, 32526343]
  b := [15786778, 20097577, 29709146, 33746239, 1462565, 28966322, 29890883, 13420552, 1719826]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 41, 34246169]
  exp := ![1, 1, 1]
  pdgood := [5, 41, 34246169]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp41.out
    exact hp34246169.out
  a := [-37545636222, -867077877078, 743699648043, 3088043521072, -1827744607932, -2407604535024, 1090818262212, 463800237984, -191918016780]
  b := [-30525171577, 86222906454, 319878992679, -288366437071, -608795924986, 346222260504, 335351777355, -141260113086, -50218384134, 19191801678]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 34246169 T_ofList CD34246169

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

end VoightMaximalOrderD10R330

namespace VoightMaximalOrderD10R335

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4410183278125, [-1, -4, 22, 0, -48, 5, 37, -2, -11, 0, 1], 1⟩
local notation "l" => [-1, -4, 22, 0, -48, 5, 37, -2, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -22, 0, 48, -5, -37, 2, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -22, 0, 48, -5, -37, 2, 11, 0], ![0, 1, 4, -22, 0, 48, -5, -37, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -22, 0, 48, -5, -37, 2, 11, 0], ![0, 1, 4, -22, 0, 48, -5, -37, 2, 11], ![11, 44, -241, 4, 506, -55, -359, 17, 84, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -22, 0, 48, -5, -37, 2, 11, 0], ![0, 1, 4, -22, 0, 48, -5, -37, 2, 11], ![11, 44, -241, 4, 506, -55, -359, 17, 84, 2], ![2, 19, 0, -241, 100, 496, -129, -355, 39, 84]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -22, 0, 48, -5, -37, 2, 11, 0], ![0, 1, 4, -22, 0, 48, -5, -37, 2, 11], ![11, 44, -241, 4, 506, -55, -359, 17, 84, 2], ![2, 19, 0, -241, 100, 496, -129, -355, 39, 84], ![84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -22, 0, 48, -5, -37, 2, 11, 0], ![0, 1, 4, -22, 0, 48, -5, -37, 2, 11], ![11, 44, -241, 4, 506, -55, -359, 17, 84, 2], ![2, 19, 0, -241, 100, 496, -129, -355, 39, 84], ![84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39], ![39, 240, -520, -1829, 1872, 3596, -1763, -2534, 468, 569]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -22, 0, 48, -5, -37, 2, 11, 0], ![0, 1, 4, -22, 0, 48, -5, -37, 2, 11], ![11, 44, -241, 4, 506, -55, -359, 17, 84, 2], ![2, 19, 0, -241, 100, 496, -129, -355, 39, 84], ![84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39], ![39, 240, -520, -1829, 1872, 3596, -1763, -2534, 468, 569], ![569, 2315, -12278, -520, 25483, -973, -17457, -625, 3725, 468]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -22, 0, 48, -5, -37, 2, 11, 0], ![0, 1, 4, -22, 0, 48, -5, -37, 2, 11], ![11, 44, -241, 4, 506, -55, -359, 17, 84, 2], ![2, 19, 0, -241, 100, 496, -129, -355, 39, 84], ![84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39], ![39, 240, -520, -1829, 1872, 3596, -1763, -2534, 468, 569], ![569, 2315, -12278, -520, 25483, -973, -17457, -625, 3725, 468], ![468, 2441, -7981, -12278, 21944, 23143, -18289, -16521, 4523, 3725]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -22, 0, 48, -5, -37, 2, 11, 0], ![0, 1, 4, -22, 0, 48, -5, -37, 2, 11], ![11, 44, -241, 4, 506, -55, -359, 17, 84, 2], ![2, 19, 0, -241, 100, 496, -129, -355, 39, 84], ![84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39], ![39, 240, -520, -1829, 1872, 3596, -1763, -2534, 468, 569], ![569, 2315, -12278, -520, 25483, -973, -17457, -625, 3725, 468], ![468, 2441, -7981, -12278, 21944, 23143, -18289, -16521, 4523, 3725], ![3725, 15368, -79509, -7981, 166522, 3319, -114682, -10839, 24454, 4523]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1], [-39, -84, -2, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1], [-39, -84, -2, -11, 0, -1], [-569, -39, -84, -2, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1], [-39, -84, -2, -11, 0, -1], [-569, -39, -84, -2, -11, 0, -1], [-468, -569, -39, -84, -2, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1], [-39, -84, -2, -11, 0, -1], [-569, -39, -84, -2, -11, 0, -1], [-468, -569, -39, -84, -2, -11, 0, -1], [-3725, -468, -569, -39, -84, -2, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -22, 0, 48, -5, -37, 2, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -22, 0, 48, -5, -37, 2, 11, 0], [0, 1, 4, -22, 0, 48, -5, -37, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -22, 0, 48, -5, -37, 2, 11, 0], [0, 1, 4, -22, 0, 48, -5, -37, 2, 11], [11, 44, -241, 4, 506, -55, -359, 17, 84, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -22, 0, 48, -5, -37, 2, 11, 0], [0, 1, 4, -22, 0, 48, -5, -37, 2, 11], [11, 44, -241, 4, 506, -55, -359, 17, 84, 2], [2, 19, 0, -241, 100, 496, -129, -355, 39, 84]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -22, 0, 48, -5, -37, 2, 11, 0], [0, 1, 4, -22, 0, 48, -5, -37, 2, 11], [11, 44, -241, 4, 506, -55, -359, 17, 84, 2], [2, 19, 0, -241, 100, 496, -129, -355, 39, 84], [84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -22, 0, 48, -5, -37, 2, 11, 0], [0, 1, 4, -22, 0, 48, -5, -37, 2, 11], [11, 44, -241, 4, 506, -55, -359, 17, 84, 2], [2, 19, 0, -241, 100, 496, -129, -355, 39, 84], [84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39], [39, 240, -520, -1829, 1872, 3596, -1763, -2534, 468, 569]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -22, 0, 48, -5, -37, 2, 11, 0], [0, 1, 4, -22, 0, 48, -5, -37, 2, 11], [11, 44, -241, 4, 506, -55, -359, 17, 84, 2], [2, 19, 0, -241, 100, 496, -129, -355, 39, 84], [84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39], [39, 240, -520, -1829, 1872, 3596, -1763, -2534, 468, 569], [569, 2315, -12278, -520, 25483, -973, -17457, -625, 3725, 468]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -22, 0, 48, -5, -37, 2, 11, 0], [0, 1, 4, -22, 0, 48, -5, -37, 2, 11], [11, 44, -241, 4, 506, -55, -359, 17, 84, 2], [2, 19, 0, -241, 100, 496, -129, -355, 39, 84], [84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39], [39, 240, -520, -1829, 1872, 3596, -1763, -2534, 468, 569], [569, 2315, -12278, -520, 25483, -973, -17457, -625, 3725, 468], [468, 2441, -7981, -12278, 21944, 23143, -18289, -16521, 4523, 3725]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -22, 0, 48, -5, -37, 2, 11, 0], [0, 1, 4, -22, 0, 48, -5, -37, 2, 11], [11, 44, -241, 4, 506, -55, -359, 17, 84, 2], [2, 19, 0, -241, 100, 496, -129, -355, 39, 84], [84, 338, -1829, 0, 3791, -320, -2612, 39, 569, 39], [39, 240, -520, -1829, 1872, 3596, -1763, -2534, 468, 569], [569, 2315, -12278, -520, 25483, -973, -17457, -625, 3725, 468], [468, 2441, -7981, -12278, 21944, 23143, -18289, -16521, 4523, 3725], [3725, 15368, -79509, -7981, 166522, 3319, -114682, -10839, 24454, 4523]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp74276771 : Fact (Nat.Prime 74276771) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 2]
  b' := [3, 1, 2, 4, 3]
  k := [1]
  f := [1, 4, 2, 8, 16, 3, -5, 2, 3]
  g := [2, 4, 4, 2, 0, 1]
  h := [2, 4, 4, 2, 0, 1]
  a := [1, 0, 1, 1, 2]
  b := [0, 3, 0, 0, 0, 2, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [2, 18, 6, 15, 18, 2, 10, 11]
  b' := [0, 13, 17, 17, 15, 11, 4, 8, 3]
  k := [14, 13, 15, 7, 15, 5, 1, 4, 1]
  f := [9, 7, 1, 1, 16, 5, 1, 11, 3, 1]
  g := [10, 7, 2, 1, 15, 5, 3, 12, 2, 1]
  h := [17, 1]
  a := [9, 2, 16, 7, 12, 8, 12, 1, 14]
  b := [11, 7, 18, 10, 3, 0, 10, 4, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD74276771 : CertificateDedekindCriterionLists l 74276771 where
  n := 2
  a' := [44786740, 29220796, 14136434, 11653549, 27746300, 24020707, 3556859, 51972622]
  b' := [26684628, 34892891, 14742718, 8108252, 39009404, 21017688, 33974601, 16034386, 35490137]
  k := [21428028, 54261302, 58198939, 14380303, 72144153, 69548974, 21102277, 36391258, 1]
  f := [876503, 43408364, 40037201, 32841621, 838284, 27121299, 21689305, 5310941, 13738234, 1]
  g := [1160886, 57492287, 53027343, 43497144, 1110266, 35920854, 28726439, 7034085, 18195629, 1]
  h := [56081142, 1]
  a := [39690254, 58869775, 14096279, 37329893, 50154339, 25243372, 26341225, 74255065, 23483157]
  b := [27412047, 40921585, 30442674, 20226625, 59092174, 70643413, 57542467, 58407223, 50793614]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 19, 74276771]
  exp := ![1, 1, 1]
  pdgood := [5, 19, 74276771]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp74276771.out
  a := [-1909731549, -71558942968, 280561315530, 322862811660, -725455173936, -181354042810, 371396010796, 34289206560, -48127806720]
  b := [-1286640424, 5646422627, 53025739463, -109809330324, -62467426483, 134363712298, 22791361321, -47727718558, -3428920656, 4812780672]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 74276771 T_ofList CD74276771

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

end VoightMaximalOrderD10R335

end TraceEuclidean
