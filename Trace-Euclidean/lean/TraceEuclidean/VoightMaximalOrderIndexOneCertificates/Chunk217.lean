import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk213
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

namespace VoightMaximalOrderD10R536

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5957133878125, [-1, -8, 0, 40, 1, -58, 12, 24, -7, -3, 1], 1⟩
local notation "l" => [-1, -8, 0, 40, 1, -58, 12, 24, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 0, -40, -1, 58, -12, -24, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 0, -40, -1, 58, -12, -24, 7, 3], ![3, 25, 8, -120, -43, 173, 22, -84, -3, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 0, -40, -1, 58, -12, -24, 7, 3], ![3, 25, 8, -120, -43, 173, 22, -84, -3, 16], ![16, 131, 25, -632, -136, 885, -19, -362, 28, 45]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 0, -40, -1, 58, -12, -24, 7, 3], ![3, 25, 8, -120, -43, 173, 22, -84, -3, 16], ![16, 131, 25, -632, -136, 885, -19, -362, 28, 45], ![45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 0, -40, -1, 58, -12, -24, 7, 3], ![3, 25, 8, -120, -43, 173, 22, -84, -3, 16], ![16, 131, 25, -632, -136, 885, -19, -362, 28, 45], ![45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], ![163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 0, -40, -1, 58, -12, -24, 7, 3], ![3, 25, 8, -120, -43, 173, 22, -84, -3, 16], ![16, 131, 25, -632, -136, 885, -19, -362, 28, 45], ![45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], ![163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442], ![442, 3699, 1349, -17304, -6831, 23698, 3473, -10090, -473, 1368]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 0, -40, -1, 58, -12, -24, 7, 3], ![3, 25, 8, -120, -43, 173, 22, -84, -3, 16], ![16, 131, 25, -632, -136, 885, -19, -362, 28, 45], ![45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], ![163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442], ![442, 3699, 1349, -17304, -6831, 23698, 3473, -10090, -473, 1368], ![1368, 11386, 3699, -53371, -18672, 72513, 7282, -29359, -514, 3631]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 0, -40, -1, 58, -12, -24, 7, 3], ![3, 25, 8, -120, -43, 173, 22, -84, -3, 16], ![16, 131, 25, -632, -136, 885, -19, -362, 28, 45], ![45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], ![163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442], ![442, 3699, 1349, -17304, -6831, 23698, 3473, -10090, -473, 1368], ![1368, 11386, 3699, -53371, -18672, 72513, 7282, -29359, -514, 3631], ![3631, 30416, 11386, -141541, -57002, 191926, 28941, -79862, -3942, 10379]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, 0, -40, -1, 58, -12, -24, 7, 3], ![3, 25, 8, -120, -43, 173, 22, -84, -3, 16], ![16, 131, 25, -632, -136, 885, -19, -362, 28, 45], ![45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], ![163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442], ![442, 3699, 1349, -17304, -6831, 23698, 3473, -10090, -473, 1368], ![1368, 11386, 3699, -53371, -18672, 72513, 7282, -29359, -514, 3631], ![3631, 30416, 11386, -141541, -57002, 191926, 28941, -79862, -3942, 10379], ![10379, 86663, 30416, -403774, -151920, 544980, 67378, -220155, -7209, 27195]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-442, -163, -45, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-442, -163, -45, -16, -3, -1], [-1368, -442, -163, -45, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-442, -163, -45, -16, -3, -1], [-1368, -442, -163, -45, -16, -3, -1], [-3631, -1368, -442, -163, -45, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-442, -163, -45, -16, -3, -1], [-1368, -442, -163, -45, -16, -3, -1], [-3631, -1368, -442, -163, -45, -16, -3, -1], [-10379, -3631, -1368, -442, -163, -45, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 0, -40, -1, 58, -12, -24, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 0, -40, -1, 58, -12, -24, 7, 3], [3, 25, 8, -120, -43, 173, 22, -84, -3, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 0, -40, -1, 58, -12, -24, 7, 3], [3, 25, 8, -120, -43, 173, 22, -84, -3, 16], [16, 131, 25, -632, -136, 885, -19, -362, 28, 45]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 0, -40, -1, 58, -12, -24, 7, 3], [3, 25, 8, -120, -43, 173, 22, -84, -3, 16], [16, 131, 25, -632, -136, 885, -19, -362, 28, 45], [45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 0, -40, -1, 58, -12, -24, 7, 3], [3, 25, 8, -120, -43, 173, 22, -84, -3, 16], [16, 131, 25, -632, -136, 885, -19, -362, 28, 45], [45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], [163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 0, -40, -1, 58, -12, -24, 7, 3], [3, 25, 8, -120, -43, 173, 22, -84, -3, 16], [16, 131, 25, -632, -136, 885, -19, -362, 28, 45], [45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], [163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442], [442, 3699, 1349, -17304, -6831, 23698, 3473, -10090, -473, 1368]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 0, -40, -1, 58, -12, -24, 7, 3], [3, 25, 8, -120, -43, 173, 22, -84, -3, 16], [16, 131, 25, -632, -136, 885, -19, -362, 28, 45], [45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], [163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442], [442, 3699, 1349, -17304, -6831, 23698, 3473, -10090, -473, 1368], [1368, 11386, 3699, -53371, -18672, 72513, 7282, -29359, -514, 3631]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 0, -40, -1, 58, -12, -24, 7, 3], [3, 25, 8, -120, -43, 173, 22, -84, -3, 16], [16, 131, 25, -632, -136, 885, -19, -362, 28, 45], [45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], [163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442], [442, 3699, 1349, -17304, -6831, 23698, 3473, -10090, -473, 1368], [1368, 11386, 3699, -53371, -18672, 72513, 7282, -29359, -514, 3631], [3631, 30416, 11386, -141541, -57002, 191926, 28941, -79862, -3942, 10379]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, 0, -40, -1, 58, -12, -24, 7, 3], [3, 25, 8, -120, -43, 173, 22, -84, -3, 16], [16, 131, 25, -632, -136, 885, -19, -362, 28, 45], [45, 376, 131, -1775, -677, 2474, 345, -1099, -47, 163], [163, 1349, 376, -6389, -1938, 8777, 518, -3567, 42, 442], [442, 3699, 1349, -17304, -6831, 23698, 3473, -10090, -473, 1368], [1368, 11386, 3699, -53371, -18672, 72513, 7282, -29359, -514, 3631], [3631, 30416, 11386, -141541, -57002, 191926, 28941, -79862, -3942, 10379], [10379, 86663, 30416, -403774, -151920, 544980, 67378, -220155, -7209, 27195]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1906282841 : Fact (Nat.Prime 1906282841) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2]
  b' := [2, 1, 2, 2]
  k := [1]
  f := [2, 4, 2, -6, 2, 14, -1, -4, 2, 1]
  g := [3, 2, 1, 1, 1, 1]
  h := [3, 2, 1, 1, 1, 1]
  a := [4, 3, 4]
  b := [1, 2, 4, 2, 2, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1906282841 : CertificateDedekindCriterionLists l 1906282841 where
  n := 2
  a' := [1425950471, 416971718, 1370188844, 933585026, 1736285077, 407579782, 1116567112, 971184597]
  b' := [1740103416, 463299018, 174563520, 1283258043, 123438455, 123575406, 1295332128, 1288435633, 527518214]
  k := [475550503, 1577298360, 1626205831, 491936636, 1514811585, 1434145012, 1177222956, 1052899612, 1]
  f := [343916803, 84740201, 251078253, 156335219, 205003869, 304287727, 385245333, 325573103, 331183366, 1]
  g := [1536478994, 378584403, 1121714490, 698441533, 915873069, 1359432560, 1721117885, 1454526874, 1479591225, 1]
  h := [426691613, 1]
  a := [1227275144, 995464793, 1563248399, 799366734, 857781160, 1061819441, 634641502, 782863263, 1763882898]
  b := [1365713685, 1398285116, 174214809, 309987127, 1704975022, 1012674518, 277597966, 304695058, 142399943]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1906282841]
  exp := ![1, 1]
  pdgood := [5, 1906282841]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1906282841.out
  a := [14971030307, -64937426656, -81150251032, 284411079760, -27706668961, -189190304836, 53627668862, 32773898336, -11450046280]
  b := [-3062805564, -6853851975, 29139124575, 16114835190, -59076856299, 6126028003, 27259075013, -6910010164, -3620891222, 1145004628]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1906282841 T_ofList CD1906282841

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

end VoightMaximalOrderD10R536

namespace VoightMaximalOrderD10R538

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5978042831872, [-1, -2, 12, 26, -17, -44, 12, 24, -5, -4, 1], 1⟩
local notation "l" => [-1, -2, 12, 26, -17, -44, 12, 24, -5, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -26, 17, 44, -12, -24, 5, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -26, 17, 44, -12, -24, 5, 4], ![4, 9, -46, -116, 42, 193, -4, -108, -4, 21]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -26, 17, 44, -12, -24, 5, 4], ![4, 9, -46, -116, 42, 193, -4, -108, -4, 21], ![21, 46, -243, -592, 241, 966, -59, -508, -3, 80]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -26, 17, 44, -12, -24, 5, 4], ![4, 9, -46, -116, 42, 193, -4, -108, -4, 21], ![21, 46, -243, -592, 241, 966, -59, -508, -3, 80], ![80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -26, 17, 44, -12, -24, 5, 4], ![4, 9, -46, -116, 42, 193, -4, -108, -4, 21], ![21, 46, -243, -592, 241, 966, -59, -508, -3, 80], ![80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], ![317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -26, 17, 44, -12, -24, 5, 4], ![4, 9, -46, -116, 42, 193, -4, -108, -4, 21], ![21, 46, -243, -592, 241, 966, -59, -508, -3, 80], ![80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], ![317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160], ![1160, 2637, -13206, -33783, 10564, 54106, 796, -27883, -1802, 4246]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -26, 17, 44, -12, -24, 5, 4], ![4, 9, -46, -116, 42, 193, -4, -108, -4, 21], ![21, 46, -243, -592, 241, 966, -59, -508, -3, 80], ![80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], ![317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160], ![1160, 2637, -13206, -33783, 10564, 54106, 796, -27883, -1802, 4246], ![4246, 9652, -48315, -123602, 38399, 197388, 3154, -101108, -6653, 15182]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -26, 17, 44, -12, -24, 5, 4], ![4, 9, -46, -116, 42, 193, -4, -108, -4, 21], ![21, 46, -243, -592, 241, 966, -59, -508, -3, 80], ![80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], ![317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160], ![1160, 2637, -13206, -33783, 10564, 54106, 796, -27883, -1802, 4246], ![4246, 9652, -48315, -123602, 38399, 197388, 3154, -101108, -6653, 15182], ![15182, 34610, -172532, -443047, 134492, 706407, 15204, -361214, -25198, 54075]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -26, 17, 44, -12, -24, 5, 4], ![4, 9, -46, -116, 42, 193, -4, -108, -4, 21], ![21, 46, -243, -592, 241, 966, -59, -508, -3, 80], ![80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], ![317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160], ![1160, 2637, -13206, -33783, 10564, 54106, 796, -27883, -1802, 4246], ![4246, 9652, -48315, -123602, 38399, 197388, 3154, -101108, -6653, 15182], ![15182, 34610, -172532, -443047, 134492, 706407, 15204, -361214, -25198, 54075], ![54075, 123332, -614290, -1578482, 476228, 2513792, 57507, -1282596, -90839, 191102]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-21, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-21, -4, -1], [-80, -21, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-21, -4, -1], [-80, -21, -4, -1], [-317, -80, -21, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-21, -4, -1], [-80, -21, -4, -1], [-317, -80, -21, -4, -1], [-1160, -317, -80, -21, -4, -1]], ![[], [], [], [-1], [-4, -1], [-21, -4, -1], [-80, -21, -4, -1], [-317, -80, -21, -4, -1], [-1160, -317, -80, -21, -4, -1], [-4246, -1160, -317, -80, -21, -4, -1]], ![[], [], [-1], [-4, -1], [-21, -4, -1], [-80, -21, -4, -1], [-317, -80, -21, -4, -1], [-1160, -317, -80, -21, -4, -1], [-4246, -1160, -317, -80, -21, -4, -1], [-15182, -4246, -1160, -317, -80, -21, -4, -1]], ![[], [-1], [-4, -1], [-21, -4, -1], [-80, -21, -4, -1], [-317, -80, -21, -4, -1], [-1160, -317, -80, -21, -4, -1], [-4246, -1160, -317, -80, -21, -4, -1], [-15182, -4246, -1160, -317, -80, -21, -4, -1], [-54075, -15182, -4246, -1160, -317, -80, -21, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -26, 17, 44, -12, -24, 5, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -26, 17, 44, -12, -24, 5, 4], [4, 9, -46, -116, 42, 193, -4, -108, -4, 21]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -26, 17, 44, -12, -24, 5, 4], [4, 9, -46, -116, 42, 193, -4, -108, -4, 21], [21, 46, -243, -592, 241, 966, -59, -508, -3, 80]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -26, 17, 44, -12, -24, 5, 4], [4, 9, -46, -116, 42, 193, -4, -108, -4, 21], [21, 46, -243, -592, 241, 966, -59, -508, -3, 80], [80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -26, 17, 44, -12, -24, 5, 4], [4, 9, -46, -116, 42, 193, -4, -108, -4, 21], [21, 46, -243, -592, 241, 966, -59, -508, -3, 80], [80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], [317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -26, 17, 44, -12, -24, 5, 4], [4, 9, -46, -116, 42, 193, -4, -108, -4, 21], [21, 46, -243, -592, 241, 966, -59, -508, -3, 80], [80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], [317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160], [1160, 2637, -13206, -33783, 10564, 54106, 796, -27883, -1802, 4246]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -26, 17, 44, -12, -24, 5, 4], [4, 9, -46, -116, 42, 193, -4, -108, -4, 21], [21, 46, -243, -592, 241, 966, -59, -508, -3, 80], [80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], [317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160], [1160, 2637, -13206, -33783, 10564, 54106, 796, -27883, -1802, 4246], [4246, 9652, -48315, -123602, 38399, 197388, 3154, -101108, -6653, 15182]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -26, 17, 44, -12, -24, 5, 4], [4, 9, -46, -116, 42, 193, -4, -108, -4, 21], [21, 46, -243, -592, 241, 966, -59, -508, -3, 80], [80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], [317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160], [1160, 2637, -13206, -33783, 10564, 54106, 796, -27883, -1802, 4246], [4246, 9652, -48315, -123602, 38399, 197388, 3154, -101108, -6653, 15182], [15182, 34610, -172532, -443047, 134492, 706407, 15204, -361214, -25198, 54075]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -26, 17, 44, -12, -24, 5, 4], [4, 9, -46, -116, 42, 193, -4, -108, -4, 21], [21, 46, -243, -592, 241, 966, -59, -508, -3, 80], [80, 181, -914, -2323, 768, 3761, 6, -1979, -108, 317], [317, 714, -3623, -9156, 3066, 14716, -43, -7602, -394, 1160], [1160, 2637, -13206, -33783, 10564, 54106, 796, -27883, -1802, 4246], [4246, 9652, -48315, -123602, 38399, 197388, 3154, -101108, -6653, 15182], [15182, 34610, -172532, -443047, 134492, 706407, 15204, -361214, -25198, 54075], [54075, 123332, -614290, -1578482, 476228, 2513792, 57507, -1282596, -90839, 191102]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp43 : Fact (Nat.Prime 43) := fact_iff.2 (by norm_num)
instance hp3677 : Fact (Nat.Prime 3677) := fact_iff.2 (by norm_num)
instance hp36923 : Fact (Nat.Prime 36923) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1]
  k := [1]
  f := [1, 1, -5, -13, 10, 23, -5, -11, 3, 3]
  g := [1, 0, 1, 0, 1, 1]
  h := [1, 0, 1, 0, 1, 1]
  a := [1]
  b := [0, 1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD43 : CertificateDedekindCriterionLists l 43 where
  n := 2
  a' := [15, 38, 16, 10, 23, 9, 24, 23]
  b' := [3, 26, 19, 7, 8, 33, 41, 36, 7]
  k := [33, 24, 37, 12, 35, 17, 22, 42, 1]
  f := [7, 19, 16, 9, 12, 16, 13, 1, 9, 1]
  g := [15, 40, 33, 19, 24, 31, 27, 2, 19, 1]
  h := [20, 1]
  a := [15, 10, 3, 31, 5, 5, 30, 14, 9]
  b := [16, 34, 39, 21, 22, 29, 0, 33, 34]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3677 : CertificateDedekindCriterionLists l 3677 where
  n := 2
  a' := [941, 3423, 18, 1226, 2936, 1349, 2838, 2548]
  b' := [605, 3309, 1549, 3320, 2209, 547, 3424, 1796, 534]
  k := [1438, 2742, 428, 3100, 1925, 3491, 904, 447, 1]
  f := [1309, 375, 803, 4, 465, 1501, 823, 537, 904, 1]
  g := [2984, 853, 1830, 8, 1060, 3421, 1874, 1223, 2060, 1]
  h := [1613, 1]
  a := [2746, 1927, 2469, 3584, 115, 367, 869, 298, 1781]
  b := [714, 2715, 230, 3049, 1706, 2664, 3057, 3095, 1896]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD36923 : CertificateDedekindCriterionLists l 36923 where
  n := 2
  a' := [3335, 13313, 16400, 28157, 33140, 25951, 36751, 14436]
  b' := [32546, 17650, 30529, 5637, 29425, 12557, 33050, 755, 35319]
  k := [15155, 1107, 16223, 14159, 31972, 34991, 3212, 15787, 1]
  f := [8471, 2040, 4796, 2353, 6234, 10554, 1095, 7859, 7542, 1]
  g := [29602, 7126, 16759, 8221, 21784, 36879, 3823, 27463, 26353, 1]
  h := [10566, 1]
  a := [19583, 26796, 2053, 7888, 9036, 35362, 13305, 15412, 7007]
  b := [34834, 451, 31799, 16171, 6222, 15522, 9455, 15078, 29916]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 43, 3677, 36923]
  exp := ![1, 1, 1, 1]
  pdgood := [2, 43, 3677, 36923]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp43.out
    exact hp3677.out
    exact hp36923.out
  a := [87969382338, -1385895340266, -1064298734156, 5573770492272, 456820358866, -4959044617512, 559051925850, 1172406117466, -288270097060]
  b := [-49822623622, 7106804331, 588060332086, 133501973907, -1177118360568, -14032221850, 712548432543, -79346851569, -128771415629, 28827009706]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 43 T_ofList CD43
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3677 T_ofList CD3677
    exact satisfiesDedekindCriterion_of_certificate_lists T l 36923 T_ofList CD36923

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

end VoightMaximalOrderD10R538

namespace VoightMaximalOrderD10R542

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6041922243584, [1, -6, 4, 24, -25, -30, 30, 14, -10, -2, 1], 1⟩
local notation "l" => [1, -6, 4, 24, -25, -30, 30, 14, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 25, 30, -30, -14, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], ![-2, 11, -2, -52, 26, 85, -30, -58, 6, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], ![-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], ![-14, 82, -45, -338, 298, 446, -335, -226, 82, 34]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], ![-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], ![-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], ![-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], ![-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], ![-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], ![-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], ![-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], ![-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], ![-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], ![-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], ![-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414], ![-414, 2334, -790, -10346, 6696, 15309, -7408, -8978, 1466, 1517]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], ![-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], ![-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], ![-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], ![-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414], ![-414, 2334, -790, -10346, 6696, 15309, -7408, -8978, 1466, 1517], ![-1517, 8688, -3734, -37198, 27579, 52206, -30201, -28646, 6192, 4500]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], ![-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], ![-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], ![-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], ![-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414], ![-414, 2334, -790, -10346, 6696, 15309, -7408, -8978, 1466, 1517], ![-1517, 8688, -3734, -37198, 27579, 52206, -30201, -28646, 6192, 4500], ![-4500, 25483, -9312, -111734, 75302, 162579, -82794, -93201, 16354, 15192]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], ![-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], ![-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], ![-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], ![-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414], ![-414, 2334, -790, -10346, 6696, 15309, -7408, -8978, 1466, 1517], ![-1517, 8688, -3734, -37198, 27579, 52206, -30201, -28646, 6192, 4500], ![-4500, 25483, -9312, -111734, 75302, 162579, -82794, -93201, 16354, 15192], ![-15192, 86652, -35285, -373920, 268066, 531062, -293181, -295482, 58719, 46738]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-150, -34, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-150, -34, -14, -2, -1], [-414, -150, -34, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-150, -34, -14, -2, -1], [-414, -150, -34, -14, -2, -1], [-1517, -414, -150, -34, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-150, -34, -14, -2, -1], [-414, -150, -34, -14, -2, -1], [-1517, -414, -150, -34, -14, -2, -1], [-4500, -1517, -414, -150, -34, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-150, -34, -14, -2, -1], [-414, -150, -34, -14, -2, -1], [-1517, -414, -150, -34, -14, -2, -1], [-4500, -1517, -414, -150, -34, -14, -2, -1], [-15192, -4500, -1517, -414, -150, -34, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 25, 30, -30, -14, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], [-2, 11, -2, -52, 26, 85, -30, -58, 6, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], [-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], [-14, 82, -45, -338, 298, 446, -335, -226, 82, 34]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], [-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], [-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], [-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], [-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], [-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], [-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], [-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], [-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], [-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], [-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], [-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414], [-414, 2334, -790, -10346, 6696, 15309, -7408, -8978, 1466, 1517]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], [-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], [-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], [-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], [-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414], [-414, 2334, -790, -10346, 6696, 15309, -7408, -8978, 1466, 1517], [-1517, 8688, -3734, -37198, 27579, 52206, -30201, -28646, 6192, 4500]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], [-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], [-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], [-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], [-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414], [-414, 2334, -790, -10346, 6696, 15309, -7408, -8978, 1466, 1517], [-1517, 8688, -3734, -37198, 27579, 52206, -30201, -28646, 6192, 4500], [-4500, 25483, -9312, -111734, 75302, 162579, -82794, -93201, 16354, 15192]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 25, 30, -30, -14, 10, 2], [-2, 11, -2, -52, 26, 85, -30, -58, 6, 14], [-14, 82, -45, -338, 298, 446, -335, -226, 82, 34], [-34, 190, -54, -861, 512, 1318, -574, -811, 114, 150], [-150, 866, -410, -3654, 2889, 5012, -3182, -2674, 689, 414], [-414, 2334, -790, -10346, 6696, 15309, -7408, -8978, 1466, 1517], [-1517, 8688, -3734, -37198, 27579, 52206, -30201, -28646, 6192, 4500], [-4500, 25483, -9312, -111734, 75302, 162579, -82794, -93201, 16354, 15192], [-15192, 86652, -35285, -373920, 268066, 531062, -293181, -295482, 58719, 46738]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5900314691 : Fact (Nat.Prime 5900314691) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [1, 1, 0, 1]
  k := [1]
  f := [0, 3, -1, -12, 13, 16, -15, -6, 5, 1]
  g := [1, 0, 1, 0, 0, 1]
  h := [1, 0, 1, 0, 0, 1]
  a := [0, 0, 0, 0, 1]
  b := [1, 0, 1, 0, 1, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5900314691 : CertificateDedekindCriterionLists l 5900314691 where
  n := 2
  a' := [4099005033, 1400102393, 2521708644, 1738190986, 3378727917, 1156321481, 2268831539, 2577665329]
  b' := [946067819, 4670686689, 4629744154, 3641676320, 3607183517, 4127403002, 3203816610, 5866238312, 4958316911]
  k := [5770918951, 5798095093, 3058856771, 4331765048, 5129154607, 1912351508, 4464788766, 3760144093, 1]
  f := [988750919, 511473579, 683615180, 976549014, 659867947, 998183927, 516445636, 399293386, 876013862, 1]
  g := [5451847235, 2820200476, 3769367446, 5384567474, 3638428211, 5503859642, 2847615768, 2201653114, 4830229391, 1]
  h := [1070085298, 1]
  a := [4511899190, 2077694604, 1817659451, 1482954274, 1565467783, 5835539020, 4157045927, 3131658235, 1791007672]
  b := [1337989809, 1242888570, 91710433, 4079803003, 516121693, 4731292031, 1445289532, 3302043007, 4109307019]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 5900314691]
  exp := ![1, 1]
  pdgood := [2, 5900314691]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5900314691.out
  a := [-580510920716, -596683826138, 5362261336096, 1980429178910, -9494589531730, -2447496576370, 4011067397356, 594619708428, -464871295110]
  b := [-98718591683, 349438827449, 384682104746, -1400537442801, -563173343894, 1578498157195, 388690467339, -498923971213, -68759396745, 46487129511]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5900314691 T_ofList CD5900314691

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

end VoightMaximalOrderD10R542

namespace VoightMaximalOrderD10R548

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6087516278125, [1, -5, -1, 28, -8, -46, 12, 23, -7, -3, 1], 1⟩
local notation "l" => [1, -5, -1, 28, -8, -46, 12, 23, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 1, -28, 8, 46, -12, -23, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], ![-3, 14, 8, -83, -4, 146, 10, -81, -2, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], ![-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], ![-16, 77, 30, -440, 45, 732, -46, -358, 31, 46]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], ![-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], ![-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], ![-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], ![-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], ![-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], ![-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], ![-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], ![-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], ![-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], ![-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], ![-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471], ![-471, 2186, 1270, -12805, -841, 21760, 2050, -10700, -410, 1492]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], ![-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], ![-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], ![-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], ![-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471], ![-471, 2186, 1270, -12805, -841, 21760, 2050, -10700, -410, 1492], ![-1492, 6989, 3678, -40506, -869, 67791, 3856, -32266, -256, 4066]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], ![-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], ![-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], ![-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], ![-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471], ![-471, 2186, 1270, -12805, -841, 21760, 2050, -10700, -410, 1492], ![-1492, 6989, 3678, -40506, -869, 67791, 3856, -32266, -256, 4066], ![-4066, 18838, 11055, -110170, -7978, 186167, 18999, -89662, -3804, 11942]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], ![-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], ![-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], ![-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], ![-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471], ![-471, 2186, 1270, -12805, -841, 21760, 2050, -10700, -410, 1492], ![-1492, 6989, 3678, -40506, -869, 67791, 3856, -32266, -256, 4066], ![-4066, 18838, 11055, -110170, -7978, 186167, 18999, -89662, -3804, 11942], ![-11942, 55644, 30780, -323321, -14634, 541354, 42863, -255667, -6068, 32022]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-169, -46, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-169, -46, -16, -3, -1], [-471, -169, -46, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-169, -46, -16, -3, -1], [-471, -169, -46, -16, -3, -1], [-1492, -471, -169, -46, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-169, -46, -16, -3, -1], [-471, -169, -46, -16, -3, -1], [-1492, -471, -169, -46, -16, -3, -1], [-4066, -1492, -471, -169, -46, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-169, -46, -16, -3, -1], [-471, -169, -46, -16, -3, -1], [-1492, -471, -169, -46, -16, -3, -1], [-4066, -1492, -471, -169, -46, -16, -3, -1], [-11942, -4066, -1492, -471, -169, -46, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 1, -28, 8, 46, -12, -23, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], [-3, 14, 8, -83, -4, 146, 10, -81, -2, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], [-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], [-16, 77, 30, -440, 45, 732, -46, -358, 31, 46]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], [-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], [-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], [-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], [-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], [-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], [-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], [-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], [-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], [-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], [-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], [-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471], [-471, 2186, 1270, -12805, -841, 21760, 2050, -10700, -410, 1492]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], [-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], [-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], [-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], [-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471], [-471, 2186, 1270, -12805, -841, 21760, 2050, -10700, -410, 1492], [-1492, 6989, 3678, -40506, -869, 67791, 3856, -32266, -256, 4066]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], [-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], [-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], [-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], [-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471], [-471, 2186, 1270, -12805, -841, 21760, 2050, -10700, -410, 1492], [-1492, 6989, 3678, -40506, -869, 67791, 3856, -32266, -256, 4066], [-4066, 18838, 11055, -110170, -7978, 186167, 18999, -89662, -3804, 11942]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 1, -28, 8, 46, -12, -23, 7, 3], [-3, 14, 8, -83, -4, 146, 10, -81, -2, 16], [-16, 77, 30, -440, 45, 732, -46, -358, 31, 46], [-46, 214, 123, -1258, -72, 2161, 180, -1104, -36, 169], [-169, 799, 383, -4609, 94, 7702, 133, -3707, 79, 471], [-471, 2186, 1270, -12805, -841, 21760, 2050, -10700, -410, 1492], [-1492, 6989, 3678, -40506, -869, 67791, 3856, -32266, -256, 4066], [-4066, 18838, 11055, -110170, -7978, 186167, 18999, -89662, -3804, 11942], [-11942, 55644, 30780, -323321, -14634, 541354, 42863, -255667, -6068, 32022]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp541 : Fact (Nat.Prime 541) := fact_iff.2 (by norm_num)
instance hp3600749 : Fact (Nat.Prime 3600749) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 0, 4]
  b' := [0, 2, 0, 1, 4]
  k := [1]
  f := [3, 1, 5, -4, 5, 12, -1, -3, 2, 1]
  g := [4, 0, 3, 1, 1, 1]
  h := [4, 0, 3, 1, 1, 1]
  a := [4, 4, 3, 2, 3]
  b := [1, 1, 1, 2, 0, 3, 0, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD541 : CertificateDedekindCriterionLists l 541 where
  n := 2
  a' := [217, 426, 247, 406, 60, 155, 136, 496]
  b' := [171, 164, 412, 518, 185, 514, 515, 213, 5]
  k := [343, 402, 107, 138, 507, 166, 500, 175, 1]
  f := [259, 227, 64, 224, 384, 285, 24, 61, 72, 1]
  g := [310, 271, 76, 268, 459, 340, 28, 73, 86, 1]
  h := [452, 1]
  a := [306, 339, 325, 23, 493, 170, 312, 346, 436]
  b := [500, 265, 349, 501, 80, 510, 393, 348, 105]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3600749 : CertificateDedekindCriterionLists l 3600749 where
  n := 2
  a' := [3481976, 513349, 810373, 230103, 2999638, 2801165, 1337933, 438849]
  b' := [2939985, 221100, 2081381, 1879790, 257712, 2589889, 1071519, 3132058, 3551988]
  k := [414415, 1000057, 1233182, 1015393, 1895759, 218300, 2669179, 3096879, 1]
  f := [1769475, 1177963, 588341, 1672264, 608546, 648955, 1907979, 992758, 882559, 1]
  g := [3104522, 2066720, 1032236, 2933966, 1067685, 1138583, 3347525, 1741780, 1548438, 1]
  h := [2052308, 1]
  a := [2594258, 2506637, 1925094, 971095, 1657968, 310355, 3385834, 176750, 1520321]
  b := [401551, 2410750, 3311949, 2188388, 1563428, 802815, 730902, 2669808, 2080428]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 541, 3600749]
  exp := ![1, 1, 1]
  pdgood := [5, 541, 3600749]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp541.out
    exact hp3600749.out
  a := [-2405026121725, -8347098048518, 14948666901432, 30293615720152, -18642796216112, -22213184169356, 10102643210960, 3763395062848, -1585624340640]
  b := [-482953229554, 928787803843, 3332707275105, -3327217565692, -6315639757672, 2956476840144, 3237661883908, -1247785448492, -423908236504, 158562434064]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 541 T_ofList CD541
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3600749 T_ofList CD3600749

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

end VoightMaximalOrderD10R548

end TraceEuclidean
