import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk166
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

namespace VoightMaximalOrderD10R24

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1102817328125, [1, -7, -2, 32, -5, -47, 15, 23, -10, -2, 1], 1⟩
local notation "l" => [1, -7, -2, 32, -5, -47, 15, 23, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -32, 5, 47, -15, -23, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], ![-2, 13, 11, -62, -22, 99, 17, -61, -3, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], ![-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], ![-14, 96, 41, -437, 8, 636, -111, -305, 79, 25]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], ![-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], ![-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], ![-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], ![-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], ![-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], ![-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], ![-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], ![-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], ![-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], ![-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], ![-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203], ![-203, 1292, 1284, -6077, -2967, 9427, 2706, -5421, -676, 1010]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], ![-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], ![-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], ![-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], ![-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203], ![-203, 1292, 1284, -6077, -2967, 9427, 2706, -5421, -676, 1010], ![-1010, 6867, 3312, -31036, -1027, 44503, -5723, -20524, 4679, 1344]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], ![-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], ![-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], ![-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], ![-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203], ![-203, 1292, 1284, -6077, -2967, 9427, 2706, -5421, -676, 1010], ![-1010, 6867, 3312, -31036, -1027, 44503, -5723, -20524, 4679, 1344], ![-1344, 8398, 9555, -39696, -24316, 62141, 24343, -36635, -7084, 7367]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], ![-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], ![-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], ![-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], ![-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203], ![-203, 1292, 1284, -6077, -2967, 9427, 2706, -5421, -676, 1010], ![-1010, 6867, 3312, -31036, -1027, 44503, -5723, -20524, 4679, 1344], ![-1344, 8398, 9555, -39696, -24316, 62141, 24343, -36635, -7084, 7367], ![-7367, 50225, 23132, -226189, -2861, 321933, -48364, -145098, 37035, 7650]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-25, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-25, -14, -2, -1], [-129, -25, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-25, -14, -2, -1], [-129, -25, -14, -2, -1], [-203, -129, -25, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-25, -14, -2, -1], [-129, -25, -14, -2, -1], [-203, -129, -25, -14, -2, -1], [-1010, -203, -129, -25, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-25, -14, -2, -1], [-129, -25, -14, -2, -1], [-203, -129, -25, -14, -2, -1], [-1010, -203, -129, -25, -14, -2, -1], [-1344, -1010, -203, -129, -25, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-25, -14, -2, -1], [-129, -25, -14, -2, -1], [-203, -129, -25, -14, -2, -1], [-1010, -203, -129, -25, -14, -2, -1], [-1344, -1010, -203, -129, -25, -14, -2, -1], [-7367, -1344, -1010, -203, -129, -25, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -32, 5, 47, -15, -23, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], [-2, 13, 11, -62, -22, 99, 17, -61, -3, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], [-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], [-14, 96, 41, -437, 8, 636, -111, -305, 79, 25]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], [-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], [-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], [-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], [-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], [-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], [-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], [-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], [-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], [-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], [-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], [-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203], [-203, 1292, 1284, -6077, -2967, 9427, 2706, -5421, -676, 1010]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], [-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], [-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], [-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], [-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203], [-203, 1292, 1284, -6077, -2967, 9427, 2706, -5421, -676, 1010], [-1010, 6867, 3312, -31036, -1027, 44503, -5723, -20524, 4679, 1344]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], [-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], [-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], [-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], [-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203], [-203, 1292, 1284, -6077, -2967, 9427, 2706, -5421, -676, 1010], [-1010, 6867, 3312, -31036, -1027, 44503, -5723, -20524, 4679, 1344], [-1344, 8398, 9555, -39696, -24316, 62141, 24343, -36635, -7084, 7367]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -32, 5, 47, -15, -23, 10, 2], [-2, 13, 11, -62, -22, 99, 17, -61, -3, 14], [-14, 96, 41, -437, 8, 636, -111, -305, 79, 25], [-25, 161, 146, -759, -312, 1183, 261, -686, -55, 129], [-129, 878, 419, -3982, -114, 5751, -752, -2706, 604, 203], [-203, 1292, 1284, -6077, -2967, 9427, 2706, -5421, -676, 1010], [-1010, 6867, 3312, -31036, -1027, 44503, -5723, -20524, 4679, 1344], [-1344, 8398, 9555, -39696, -24316, 62141, 24343, -36635, -7084, 7367], [-7367, 50225, 23132, -226189, -2861, 321933, -48364, -145098, 37035, 7650]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1039 : Fact (Nat.Prime 1039) := fact_iff.2 (by norm_num)
instance hp67931 : Fact (Nat.Prime 67931) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [1, 3]
  b' := [1, 3, 3]
  k := [1, 0, 4, 3, 4, 1, 1]
  f := [1, 5, 6, -1, 7, 16, 3, -1, 4, 1]
  g := [2, 4, 4, 1, 1]
  h := [3, 3, 2, 2, 4, 2, 1]
  a := [4, 0, 0, 4]
  b := [1, 3, 0, 1, 2, 1, 2, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1039 : CertificateDedekindCriterionLists l 1039 where
  n := 2
  a' := [589, 452, 354, 135, 20, 284, 957, 163]
  b' := [118, 959, 97, 65, 437, 446, 351, 790, 790]
  k := [491, 265, 217, 245, 95, 138, 377, 488, 1]
  f := [175, 782, 69, 347, 663, 438, 187, 231, 186, 1]
  g := [229, 1023, 89, 454, 867, 572, 244, 302, 243, 1]
  h := [794, 1]
  a := [810, 755, 223, 1010, 1034, 699, 606, 89, 302]
  b := [969, 427, 77, 597, 160, 654, 985, 501, 737]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD67931 : CertificateDedekindCriterionLists l 67931 where
  n := 2
  a' := [64807, 19776, 21351, 40782, 49835, 45705, 10916, 1831]
  b' := [29512, 50930, 49456, 49847, 33305, 7098, 19567, 54096, 37536]
  k := [65999, 67346, 23953, 10178, 18951, 61990, 22463, 11915, 1]
  f := [12980, 21965, 13384, 16790, 10692, 24867, 2602, 20118, 16460, 1]
  g := [31483, 53275, 32461, 40723, 25932, 60314, 6309, 48796, 39922, 1]
  h := [28007, 1]
  a := [27838, 99, 2868, 2450, 5308, 11191, 30451, 18970, 37503]
  b := [33731, 58524, 27097, 41460, 39874, 59093, 2812, 34104, 30428]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 1039, 67931]
  exp := ![1, 1, 1]
  pdgood := [5, 1039, 67931]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1039.out
    exact hp67931.out
  a := [56984604092, -55096894326, -729299210480, 1251744119122, 346195456003, -1358877703218, 423881336810, 166904117626, -67740748320]
  b := [8090243221, -69478585122, 85283933046, 159664991966, -281210920818, -31929592127, 190881095541, -55036867932, -18045226729, 6774074832]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1039 T_ofList CD1039
    exact satisfiesDedekindCriterion_of_certificate_lists T l 67931 T_ofList CD67931

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

end VoightMaximalOrderD10R24

namespace VoightMaximalOrderD10R26

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1129529628125, [1, 11, 25, -8, -53, -7, 36, 6, -10, -1, 1], 1⟩
local notation "l" => [1, 11, 25, -8, -53, -7, 36, 6, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -25, 8, 53, 7, -36, -6, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], ![-1, -12, -36, -17, 61, 60, -29, -42, 4, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], ![-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], ![-11, -122, -287, 52, 566, 138, -336, -95, 68, 15]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], ![-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], ![-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], ![-15, -176, -497, -167, 847, 671, -402, -426, 55, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], ![-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], ![-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], ![-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], ![-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], ![-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], ![-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], ![-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], ![-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138], ![-138, -1601, -4378, -1147, 7481, 5198, -3540, -3145, 480, 542]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], ![-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], ![-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], ![-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], ![-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138], ![-138, -1601, -4378, -1147, 7481, 5198, -3540, -3145, 480, 542], ![-542, -6100, -15151, -42, 27579, 11275, -14314, -6792, 2275, 1022]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], ![-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], ![-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], ![-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], ![-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138], ![-138, -1601, -4378, -1147, 7481, 5198, -3540, -3145, 480, 542], ![-542, -6100, -15151, -42, 27579, 11275, -14314, -6792, 2275, 1022], ![-1022, -11784, -31650, -6975, 54124, 34733, -25517, -20446, 3428, 3297]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], ![-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], ![-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], ![-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], ![-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138], ![-138, -1601, -4378, -1147, 7481, 5198, -3540, -3145, 480, 542], ![-542, -6100, -15151, -42, 27579, 11275, -14314, -6792, 2275, 1022], ![-1022, -11784, -31650, -6975, 54124, 34733, -25517, -20446, 3428, 3297], ![-3297, -37289, -94209, -5274, 167766, 77203, -83959, -45299, 12524, 6725]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-83, -15, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-83, -15, -11, -1, -1], [-138, -83, -15, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-83, -15, -11, -1, -1], [-138, -83, -15, -11, -1, -1], [-542, -138, -83, -15, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-83, -15, -11, -1, -1], [-138, -83, -15, -11, -1, -1], [-542, -138, -83, -15, -11, -1, -1], [-1022, -542, -138, -83, -15, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-83, -15, -11, -1, -1], [-138, -83, -15, -11, -1, -1], [-542, -138, -83, -15, -11, -1, -1], [-1022, -542, -138, -83, -15, -11, -1, -1], [-3297, -1022, -542, -138, -83, -15, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -25, 8, 53, 7, -36, -6, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], [-1, -12, -36, -17, 61, 60, -29, -42, 4, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], [-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], [-11, -122, -287, 52, 566, 138, -336, -95, 68, 15]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], [-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], [-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], [-15, -176, -497, -167, 847, 671, -402, -426, 55, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], [-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], [-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], [-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], [-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], [-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], [-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], [-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], [-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138], [-138, -1601, -4378, -1147, 7481, 5198, -3540, -3145, 480, 542]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], [-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], [-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], [-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], [-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138], [-138, -1601, -4378, -1147, 7481, 5198, -3540, -3145, 480, 542], [-542, -6100, -15151, -42, 27579, 11275, -14314, -6792, 2275, 1022]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], [-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], [-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], [-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], [-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138], [-138, -1601, -4378, -1147, 7481, 5198, -3540, -3145, 480, 542], [-542, -6100, -15151, -42, 27579, 11275, -14314, -6792, 2275, 1022], [-1022, -11784, -31650, -6975, 54124, 34733, -25517, -20446, 3428, 3297]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -25, 8, 53, 7, -36, -6, 10, 1], [-1, -12, -36, -17, 61, 60, -29, -42, 4, 11], [-11, -122, -287, 52, 566, 138, -336, -95, 68, 15], [-15, -176, -497, -167, 847, 671, -402, -426, 55, 83], [-83, -928, -2251, 167, 4232, 1428, -2317, -900, 404, 138], [-138, -1601, -4378, -1147, 7481, 5198, -3540, -3145, 480, 542], [-542, -6100, -15151, -42, 27579, 11275, -14314, -6792, 2275, 1022], [-1022, -11784, -31650, -6975, 54124, 34733, -25517, -20446, 3428, 3297], [-3297, -37289, -94209, -5274, 167766, 77203, -83959, -45299, 12524, 6725]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp521 : Fact (Nat.Prime 521) := fact_iff.2 (by norm_num)
instance hp16921 : Fact (Nat.Prime 16921) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 1]
  b' := [4, 3, 3, 3]
  k := [1]
  f := [3, 1, -1, 8, 17, 7, -3, 2, 4, 1]
  g := [4, 2, 2, 3, 2, 1]
  h := [4, 2, 2, 3, 2, 1]
  a := [0, 1, 4, 2, 4]
  b := [4, 1, 3, 4, 3, 0, 2, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [4, 26, 28, 4, 28, 28, 21, 18]
  b' := [11, 14, 4, 17, 27, 11, 18, 21, 39]
  k := [5, 21, 31, 5, 38, 26, 10, 37, 1]
  f := [15, 9, 3, 10, 13, 20, 0, 2, 10, 1]
  g := [28, 16, 6, 18, 21, 36, 0, 4, 18, 1]
  h := [22, 1]
  a := [28, 14, 3, 22, 24, 29, 14, 32, 2]
  b := [7, 0, 26, 34, 34, 13, 40, 25, 39]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD521 : CertificateDedekindCriterionLists l 521 where
  n := 2
  a' := [179, 158, 183, 493, 326, 148, 122, 456]
  b' := [469, 164, 356, 68, 179, 309, 276, 81, 123]
  k := [160, 415, 359, 207, 249, 88, 478, 413, 1]
  f := [135, 133, 51, 140, 147, 162, 80, 260, 125, 1]
  g := [224, 220, 84, 232, 243, 268, 132, 431, 206, 1]
  h := [314, 1]
  a := [20, 458, 317, 303, 269, 157, 70, 233, 287]
  b := [181, 367, 502, 341, 1, 105, 300, 90, 234]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD16921 : CertificateDedekindCriterionLists l 16921 where
  n := 2
  a' := [1939, 165, 10427, 16848, 9463, 9367, 12928, 957]
  b' := [10117, 8303, 1972, 2796, 5672, 10664, 4302, 10425, 5534]
  k := [3377, 5577, 6016, 6900, 7434, 15299, 11592, 12368, 1]
  f := [527, 791, 1198, 1040, 765, 611, 260, 621, 1970, 1]
  g := [3918, 5879, 8904, 7728, 5684, 4540, 1931, 4616, 14644, 1]
  h := [2276, 1]
  a := [13022, 15230, 13490, 4195, 2425, 9959, 8299, 14766, 11400]
  b := [5802, 7148, 8920, 4944, 10639, 99, 7180, 14257, 5521]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 41, 521, 16921]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 41, 521, 16921]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp41.out
    exact hp521.out
    exact hp16921.out
  a := [-21388143847, -35312083006, 120258501245, 98108677998, -142075972472, -66190110316, 60032371925, 12168832978, -8439262920]
  b := [2108671932, 15013460793, 9346644974, -33566000673, -18215780528, 24891926950, 9019121780, -7645354813, -1301275927, 843926292]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 521 T_ofList CD521
    exact satisfiesDedekindCriterion_of_certificate_lists T l 16921 T_ofList CD16921

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

end VoightMaximalOrderD10R26

namespace VoightMaximalOrderD10R29

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1142405128125, [1, -3, -9, 27, 15, -49, 4, 23, -6, -3, 1], 1⟩
local notation "l" => [1, -3, -9, 27, 15, -49, 4, 23, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -27, -15, 49, -4, -23, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], ![-3, 8, 30, -72, -72, 132, 37, -73, -5, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], ![-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], ![-15, 42, 143, -375, -297, 663, 72, -308, 17, 40]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], ![-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], ![-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], ![-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], ![-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], ![-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], ![-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], ![-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], ![-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], ![-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], ![-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], ![-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343], ![-343, 892, 3458, -7923, -8442, 13815, 4366, -6774, -590, 1003]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], ![-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], ![-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], ![-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], ![-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343], ![-343, 892, 3458, -7923, -8442, 13815, 4366, -6774, -590, 1003], ![-1003, 2666, 9919, -23623, -22968, 40705, 9803, -18703, -756, 2419]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], ![-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], ![-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], ![-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], ![-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343], ![-343, 892, 3458, -7923, -8442, 13815, 4366, -6774, -590, 1003], ![-1003, 2666, 9919, -23623, -22968, 40705, 9803, -18703, -756, 2419], ![-2419, 6254, 24437, -55394, -59908, 95563, 31029, -45834, -4189, 6501]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], ![-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], ![-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], ![-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], ![-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343], ![-343, 892, 3458, -7923, -8442, 13815, 4366, -6774, -590, 1003], ![-1003, 2666, 9919, -23623, -22968, 40705, 9803, -18703, -756, 2419], ![-2419, 6254, 24437, -55394, -59908, 95563, 31029, -45834, -4189, 6501], ![-6501, 17084, 64763, -151090, -152909, 258641, 69559, -118494, -6828, 15314]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-40, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-40, -15, -3, -1], [-137, -40, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-40, -15, -3, -1], [-137, -40, -15, -3, -1], [-343, -137, -40, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-40, -15, -3, -1], [-137, -40, -15, -3, -1], [-343, -137, -40, -15, -3, -1], [-1003, -343, -137, -40, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-40, -15, -3, -1], [-137, -40, -15, -3, -1], [-343, -137, -40, -15, -3, -1], [-1003, -343, -137, -40, -15, -3, -1], [-2419, -1003, -343, -137, -40, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-40, -15, -3, -1], [-137, -40, -15, -3, -1], [-343, -137, -40, -15, -3, -1], [-1003, -343, -137, -40, -15, -3, -1], [-2419, -1003, -343, -137, -40, -15, -3, -1], [-6501, -2419, -1003, -343, -137, -40, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -27, -15, 49, -4, -23, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], [-3, 8, 30, -72, -72, 132, 37, -73, -5, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], [-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], [-15, 42, 143, -375, -297, 663, 72, -308, 17, 40]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], [-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], [-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], [-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], [-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], [-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], [-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], [-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], [-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], [-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], [-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], [-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343], [-343, 892, 3458, -7923, -8442, 13815, 4366, -6774, -590, 1003]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], [-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], [-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], [-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], [-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343], [-343, 892, 3458, -7923, -8442, 13815, 4366, -6774, -590, 1003], [-1003, 2666, 9919, -23623, -22968, 40705, 9803, -18703, -756, 2419]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], [-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], [-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], [-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], [-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343], [-343, 892, 3458, -7923, -8442, 13815, 4366, -6774, -590, 1003], [-1003, 2666, 9919, -23623, -22968, 40705, 9803, -18703, -756, 2419], [-2419, 6254, 24437, -55394, -59908, 95563, 31029, -45834, -4189, 6501]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -27, -15, 49, -4, -23, 6, 3], [-3, 8, 30, -72, -72, 132, 37, -73, -5, 15], [-15, 42, 143, -375, -297, 663, 72, -308, 17, 40], [-40, 105, 402, -937, -975, 1663, 503, -848, -68, 137], [-137, 371, 1338, -3297, -2992, 5738, 1115, -2648, -26, 343], [-343, 892, 3458, -7923, -8442, 13815, 4366, -6774, -590, 1003], [-1003, 2666, 9919, -23623, -22968, 40705, 9803, -18703, -756, 2419], [-2419, 6254, 24437, -55394, -59908, 95563, 31029, -45834, -4189, 6501], [-6501, 17084, 64763, -151090, -152909, 258641, 69559, -118494, -6828, 15314]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp151 : Fact (Nat.Prime 151) := fact_iff.2 (by norm_num)
instance hp268999 : Fact (Nat.Prime 268999) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [2, 0, 0, 1]
  b' := [0, 1, 1, 1, 1]
  k := [1, 2, 2, 1, 2, 1, 1]
  f := [1, 3, 5, -8, -4, 18, 1, -5, 4, 2]
  g := [2, 2, 1, 0, 1, 2, 2, 2, 1]
  h := [2, 1, 1]
  a := [2, 0, 0, 2]
  b := [1, 2, 0, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2, 3]
  b' := [0, 4, 0, 1, 3]
  k := [1]
  f := [3, 7, 5, 1, 5, 13, 4, -3, 3, 1]
  g := [4, 4, 0, 4, 1, 1]
  h := [4, 4, 0, 4, 1, 1]
  a := [1, 4, 2, 3, 3]
  b := [2, 2, 2, 0, 4, 4, 4, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD151 : CertificateDedekindCriterionLists l 151 where
  n := 2
  a' := [16, 29, 69, 1, 31, 114, 123, 65]
  b' := [38, 24, 26, 94, 75, 0, 33, 62, 127]
  k := [17, 118, 56, 120, 114, 19, 122, 135, 1]
  f := [19, 16, 16, 44, 58, 7, 31, 10, 36, 1]
  g := [35, 29, 29, 81, 106, 11, 57, 18, 66, 1]
  h := [82, 1]
  a := [2, 126, 69, 83, 115, 60, 94, 67, 142]
  b := [137, 7, 22, 96, 118, 78, 34, 116, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD268999 : CertificateDedekindCriterionLists l 268999 where
  n := 2
  a' := [106432, 243738, 81608, 159733, 191154, 71367, 126992, 121696]
  b' := [123446, 142421, 134836, 217470, 149363, 85756, 127224, 229980, 16367]
  k := [263649, 123087, 52857, 168597, 88559, 65061, 82358, 227245, 1]
  f := [126876, 88588, 138621, 87285, 107651, 131702, 90616, 2017, 65628, 1]
  g := [219659, 153370, 239992, 151114, 186374, 228013, 156881, 3491, 113621, 1]
  h := [155375, 1]
  a := [38774, 226099, 60434, 197142, 30611, 178265, 251504, 144033, 172215]
  b := [163401, 49505, 236198, 53410, 160083, 257574, 19416, 245186, 96784]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![3, 5, 151, 268999]
  exp := ![1, 1, 1, 1]
  pdgood := [3, 5, 151, 268999]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp151.out
    exact hp268999.out
  a := [-30462430527, -273591681774, 62464720272, 803977739346, -271845642787, -519134551912, 207647765264, 86400254368, -36902066640]
  b := [-10357237754, 1408629793, 97703348663, -3190812558, -165475434673, 41516320069, 75631116097, -25590084290, -9747087436, 3690206664]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 151 T_ofList CD151
    exact satisfiesDedekindCriterion_of_certificate_lists T l 268999 T_ofList CD268999

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

end VoightMaximalOrderD10R29

namespace VoightMaximalOrderD10R32

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1175858493445, [-1, -9, -13, 43, 33, -55, -17, 28, 0, -5, 1], 1⟩
local notation "l" => [-1, -9, -13, 43, 33, -55, -17, 28, 0, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 9, 13, -43, -33, 55, 17, -28, 0, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 9, 13, -43, -33, 55, 17, -28, 0, 5], ![5, 46, 74, -202, -208, 242, 140, -123, -28, 25]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 9, 13, -43, -33, 55, 17, -28, 0, 5], ![5, 46, 74, -202, -208, 242, 140, -123, -28, 25], ![25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 9, 13, -43, -33, 55, 17, -28, 0, 5], ![5, 46, 74, -202, -208, 242, 140, -123, -28, 25], ![25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], ![97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 9, 13, -43, -33, 55, 17, -28, 0, 5], ![5, 46, 74, -202, -208, 242, 140, -123, -28, 25], ![25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], ![97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], ![362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 9, 13, -43, -33, 55, 17, -28, 0, 5], ![5, 46, 74, -202, -208, 242, 140, -123, -28, 25], ![25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], ![97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], ![362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250], ![1250, 11612, 19605, -48146, -55325, 53004, 36958, -24538, -7320, 4201]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 9, 13, -43, -33, 55, 17, -28, 0, 5], ![5, 46, 74, -202, -208, 242, 140, -123, -28, 25], ![25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], ![97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], ![362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250], ![1250, 11612, 19605, -48146, -55325, 53004, 36958, -24538, -7320, 4201], ![4201, 39059, 66225, -161038, -186779, 175730, 124421, -80670, -24538, 13685]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 9, 13, -43, -33, 55, 17, -28, 0, 5], ![5, 46, 74, -202, -208, 242, 140, -123, -28, 25], ![25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], ![97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], ![362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250], ![1250, 11612, 19605, -48146, -55325, 53004, 36958, -24538, -7320, 4201], ![4201, 39059, 66225, -161038, -186779, 175730, 124421, -80670, -24538, 13685], ![13685, 127366, 216964, -522230, -612643, 565896, 408375, -258759, -80670, 43887]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 9, 13, -43, -33, 55, 17, -28, 0, 5], ![5, 46, 74, -202, -208, 242, 140, -123, -28, 25], ![25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], ![97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], ![362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250], ![1250, 11612, 19605, -48146, -55325, 53004, 36958, -24538, -7320, 4201], ![4201, 39059, 66225, -161038, -186779, 175730, 124421, -80670, -24538, 13685], ![13685, 127366, 216964, -522230, -612643, 565896, 408375, -258759, -80670, 43887], ![43887, 408668, 697897, -1670177, -1970501, 1801142, 1311975, -820461, -258759, 138765]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-97, -25, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-97, -25, -5, -1], [-362, -97, -25, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-97, -25, -5, -1], [-362, -97, -25, -5, -1], [-1250, -362, -97, -25, -5, -1]], ![[], [], [], [-1], [-5, -1], [-25, -5, -1], [-97, -25, -5, -1], [-362, -97, -25, -5, -1], [-1250, -362, -97, -25, -5, -1], [-4201, -1250, -362, -97, -25, -5, -1]], ![[], [], [-1], [-5, -1], [-25, -5, -1], [-97, -25, -5, -1], [-362, -97, -25, -5, -1], [-1250, -362, -97, -25, -5, -1], [-4201, -1250, -362, -97, -25, -5, -1], [-13685, -4201, -1250, -362, -97, -25, -5, -1]], ![[], [-1], [-5, -1], [-25, -5, -1], [-97, -25, -5, -1], [-362, -97, -25, -5, -1], [-1250, -362, -97, -25, -5, -1], [-4201, -1250, -362, -97, -25, -5, -1], [-13685, -4201, -1250, -362, -97, -25, -5, -1], [-43887, -13685, -4201, -1250, -362, -97, -25, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 9, 13, -43, -33, 55, 17, -28, 0, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 9, 13, -43, -33, 55, 17, -28, 0, 5], [5, 46, 74, -202, -208, 242, 140, -123, -28, 25]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 9, 13, -43, -33, 55, 17, -28, 0, 5], [5, 46, 74, -202, -208, 242, 140, -123, -28, 25], [25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 9, 13, -43, -33, 55, 17, -28, 0, 5], [5, 46, 74, -202, -208, 242, 140, -123, -28, 25], [25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], [97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 9, 13, -43, -33, 55, 17, -28, 0, 5], [5, 46, 74, -202, -208, 242, 140, -123, -28, 25], [25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], [97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], [362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 9, 13, -43, -33, 55, 17, -28, 0, 5], [5, 46, 74, -202, -208, 242, 140, -123, -28, 25], [25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], [97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], [362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250], [1250, 11612, 19605, -48146, -55325, 53004, 36958, -24538, -7320, 4201]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 9, 13, -43, -33, 55, 17, -28, 0, 5], [5, 46, 74, -202, -208, 242, 140, -123, -28, 25], [25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], [97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], [362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250], [1250, 11612, 19605, -48146, -55325, 53004, 36958, -24538, -7320, 4201], [4201, 39059, 66225, -161038, -186779, 175730, 124421, -80670, -24538, 13685]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 9, 13, -43, -33, 55, 17, -28, 0, 5], [5, 46, 74, -202, -208, 242, 140, -123, -28, 25], [25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], [97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], [362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250], [1250, 11612, 19605, -48146, -55325, 53004, 36958, -24538, -7320, 4201], [4201, 39059, 66225, -161038, -186779, 175730, 124421, -80670, -24538, 13685], [13685, 127366, 216964, -522230, -612643, 565896, 408375, -258759, -80670, 43887]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 9, 13, -43, -33, 55, 17, -28, 0, 5], [5, 46, 74, -202, -208, 242, 140, -123, -28, 25], [25, 230, 371, -1001, -1027, 1167, 667, -560, -123, 97], [97, 898, 1491, -3800, -4202, 4308, 2816, -2049, -560, 362], [362, 3355, 5604, -14075, -15746, 15708, 10462, -7320, -2049, 1250], [1250, 11612, 19605, -48146, -55325, 53004, 36958, -24538, -7320, 4201], [4201, 39059, 66225, -161038, -186779, 175730, 124421, -80670, -24538, 13685], [13685, 127366, 216964, -522230, -612643, 565896, 408375, -258759, -80670, 43887], [43887, 408668, 697897, -1670177, -1970501, 1801142, 1311975, -820461, -258759, 138765]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp401 : Fact (Nat.Prime 401) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 2, 3, 1, 1, 0, 4, 3]
  b' := [3, 4, 4, 1, 2, 4, 1, 1, 3]
  k := [4, 4, 1, 1, 4, 2, 3, 2, 1]
  f := [1, 2, 5, -8, -5, 13, 7, -4, 1, 2]
  g := [1, 0, 3, 0, 2, 2, 4, 1, 1, 1]
  h := [4, 1]
  a := [3, 0, 1, 0, 3, 4, 3, 1, 4]
  b := [3, 4, 0, 0, 1, 0, 0, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [10, 39, 21, 43, 43, 32, 3]
  b' := [33, 44, 42, 52, 5, 40, 18, 53]
  k := [45, 19, 11, 42, 30, 22, 1]
  f := [43, 56, 31, 8, 24, 39, 29, 36, 12, 1]
  g := [57, 53, 20, 3, 31, 39, 23, 39, 1]
  h := [46, 17, 1]
  a := [17, 5, 55, 21, 15, 30, 2, 34]
  b := [30, 3, 22, 25, 53, 56, 14, 1, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [267, 5, 187, 125, 138, 159, 202]
  b' := [176, 313, 365, 211, 195, 382, 173, 74]
  k := [69, 29, 310, 156, 256, 154, 1]
  f := [37, 129, 119, 32, 104, 120, 79, 167, 83, 1]
  g := [204, 374, 35, 114, 385, 23, 392, 273, 1]
  h := [72, 119, 1]
  a := [340, 72, 232, 130, 2, 275, 325, 277]
  b := [131, 65, 201, 311, 379, 225, 170, 298, 120]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD401 : CertificateDedekindCriterionLists l 401 where
  n := 2
  a' := [104, 76, 387, 214, 313, 234, 264, 236]
  b' := [115, 2, 260, 152, 375, 276, 140, 208, 152]
  k := [43, 232, 33, 44, 317, 298, 232, 12, 1]
  f := [113, 37, 73, 29, 171, 92, 159, 63, 98, 1]
  g := [236, 76, 152, 60, 357, 190, 331, 130, 204, 1]
  h := [192, 1]
  a := [72, 58, 156, 195, 54, 134, 127, 109, 356]
  b := [25, 133, 253, 71, 333, 114, 245, 334, 45]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 61, 397, 401]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 61, 397, 401]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp61.out
    exact hp397.out
    exact hp401.out
  a := [7947528647, -16499341360, -32401184042, 44150452842, 25172497332, -34817657742, -1665011080, 8445432820, -1799965720]
  b := [-888453748, -3547624335, 6133898121, 7699398660, -9043061396, -4033156626, 4988243518, 183780462, -934541568, 179996572]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 401 T_ofList CD401

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

end VoightMaximalOrderD10R32

end TraceEuclidean
