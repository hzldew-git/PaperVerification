import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk190
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

namespace VoightMaximalOrderD10R275

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3931632878125, [-1, -4, 7, 21, -17, -35, 17, 20, -7, -3, 1], 1⟩
local notation "l" => [-1, -4, 7, 21, -17, -35, 17, 20, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -21, 17, 35, -17, -20, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -21, 17, 35, -17, -20, 7, 3], ![3, 13, -17, -70, 30, 122, -16, -77, 1, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -21, 17, 35, -17, -20, 7, 3], ![3, 13, -17, -70, 30, 122, -16, -77, 1, 16], ![16, 67, -99, -353, 202, 590, -150, -336, 35, 49]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -21, 17, 35, -17, -20, 7, 3], ![3, 13, -17, -70, 30, 122, -16, -77, 1, 16], ![16, 67, -99, -353, 202, 590, -150, -336, 35, 49], ![49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -21, 17, 35, -17, -20, 7, 3], ![3, 13, -17, -70, 30, 122, -16, -77, 1, 16], ![16, 67, -99, -353, 202, 590, -150, -336, 35, 49], ![49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], ![182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -21, 17, 35, -17, -20, 7, 3], ![3, 13, -17, -70, 30, 122, -16, -77, 1, 16], ![16, 67, -99, -353, 202, 590, -150, -336, 35, 49], ![49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], ![182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553], ![553, 2394, -3094, -12675, 5303, 21321, -2551, -12237, -12, 1803]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -21, 17, 35, -17, -20, 7, 3], ![3, 13, -17, -70, 30, 122, -16, -77, 1, 16], ![16, 67, -99, -353, 202, 590, -150, -336, 35, 49], ![49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], ![182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553], ![553, 2394, -3094, -12675, 5303, 21321, -2551, -12237, -12, 1803], ![1803, 7765, -10227, -40957, 17976, 68408, -9330, -38611, 384, 5397]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -21, 17, 35, -17, -20, 7, 3], ![3, 13, -17, -70, 30, 122, -16, -77, 1, 16], ![16, 67, -99, -353, 202, 590, -150, -336, 35, 49], ![49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], ![182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553], ![553, 2394, -3094, -12675, 5303, 21321, -2551, -12237, -12, 1803], ![1803, 7765, -10227, -40957, 17976, 68408, -9330, -38611, 384, 5397], ![5397, 23391, -30014, -123564, 50792, 206871, -23341, -117270, -832, 16575]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -21, 17, 35, -17, -20, 7, 3], ![3, 13, -17, -70, 30, 122, -16, -77, 1, 16], ![16, 67, -99, -353, 202, 590, -150, -336, 35, 49], ![49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], ![182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553], ![553, 2394, -3094, -12675, 5303, 21321, -2551, -12237, -12, 1803], ![1803, 7765, -10227, -40957, 17976, 68408, -9330, -38611, 384, 5397], ![5397, 23391, -30014, -123564, 50792, 206871, -23341, -117270, -832, 16575], ![16575, 71697, -92634, -378089, 158211, 630917, -74904, -354841, -1245, 48893]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-182, -49, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-182, -49, -16, -3, -1], [-553, -182, -49, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-182, -49, -16, -3, -1], [-553, -182, -49, -16, -3, -1], [-1803, -553, -182, -49, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-182, -49, -16, -3, -1], [-553, -182, -49, -16, -3, -1], [-1803, -553, -182, -49, -16, -3, -1], [-5397, -1803, -553, -182, -49, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-182, -49, -16, -3, -1], [-553, -182, -49, -16, -3, -1], [-1803, -553, -182, -49, -16, -3, -1], [-5397, -1803, -553, -182, -49, -16, -3, -1], [-16575, -5397, -1803, -553, -182, -49, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -21, 17, 35, -17, -20, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -21, 17, 35, -17, -20, 7, 3], [3, 13, -17, -70, 30, 122, -16, -77, 1, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -21, 17, 35, -17, -20, 7, 3], [3, 13, -17, -70, 30, 122, -16, -77, 1, 16], [16, 67, -99, -353, 202, 590, -150, -336, 35, 49]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -21, 17, 35, -17, -20, 7, 3], [3, 13, -17, -70, 30, 122, -16, -77, 1, 16], [16, 67, -99, -353, 202, 590, -150, -336, 35, 49], [49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -21, 17, 35, -17, -20, 7, 3], [3, 13, -17, -70, 30, 122, -16, -77, 1, 16], [16, 67, -99, -353, 202, 590, -150, -336, 35, 49], [49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], [182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -21, 17, 35, -17, -20, 7, 3], [3, 13, -17, -70, 30, 122, -16, -77, 1, 16], [16, 67, -99, -353, 202, 590, -150, -336, 35, 49], [49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], [182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553], [553, 2394, -3094, -12675, 5303, 21321, -2551, -12237, -12, 1803]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -21, 17, 35, -17, -20, 7, 3], [3, 13, -17, -70, 30, 122, -16, -77, 1, 16], [16, 67, -99, -353, 202, 590, -150, -336, 35, 49], [49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], [182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553], [553, 2394, -3094, -12675, 5303, 21321, -2551, -12237, -12, 1803], [1803, 7765, -10227, -40957, 17976, 68408, -9330, -38611, 384, 5397]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -21, 17, 35, -17, -20, 7, 3], [3, 13, -17, -70, 30, 122, -16, -77, 1, 16], [16, 67, -99, -353, 202, 590, -150, -336, 35, 49], [49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], [182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553], [553, 2394, -3094, -12675, 5303, 21321, -2551, -12237, -12, 1803], [1803, 7765, -10227, -40957, 17976, 68408, -9330, -38611, 384, 5397], [5397, 23391, -30014, -123564, 50792, 206871, -23341, -117270, -832, 16575]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -21, 17, 35, -17, -20, 7, 3], [3, 13, -17, -70, 30, 122, -16, -77, 1, 16], [16, 67, -99, -353, 202, 590, -150, -336, 35, 49], [49, 212, -276, -1128, 480, 1917, -243, -1130, 7, 182], [182, 777, -1062, -4098, 1966, 6850, -1177, -3883, 144, 553], [553, 2394, -3094, -12675, 5303, 21321, -2551, -12237, -12, 1803], [1803, 7765, -10227, -40957, 17976, 68408, -9330, -38611, 384, 5397], [5397, 23391, -30014, -123564, 50792, 206871, -23341, -117270, -832, 16575], [16575, 71697, -92634, -378089, 158211, 630917, -74904, -354841, -1245, 48893]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1258122521 : Fact (Nat.Prime 1258122521) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 4, 4]
  b' := [1, 0, 1, 0, 4]
  k := [1]
  f := [1, 4, 5, 3, 9, 11, 0, -2, 2, 1]
  g := [2, 4, 4, 1, 1, 1]
  h := [2, 4, 4, 1, 1, 1]
  a := [2, 0, 2, 2, 2]
  b := [2, 2, 1, 0, 2, 3, 4, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1258122521 : CertificateDedekindCriterionLists l 1258122521 where
  n := 2
  a' := [508299706, 407435931, 45462041, 940147232, 112049678, 548473535, 1233328212, 442586504]
  b' := [36916165, 521981666, 188350211, 940058948, 63249978, 167242344, 147196024, 250785428, 90615113]
  k := [509715950, 146097515, 35863952, 239686633, 660435435, 34758866, 123736558, 1085528247, 1]
  f := [454467117, 97331267, 132025601, 149852534, 505460972, 385133514, 411530909, 191746130, 308611336, 1]
  g := [799285111, 171179452, 232197431, 263550199, 888969551, 677345998, 723771898, 337229737, 542764122, 1]
  h := [715358396, 1]
  a := [1129244343, 97624465, 716455806, 419893473, 275530724, 1114673218, 902788286, 1145247986, 820769220]
  b := [157734812, 720570577, 1123573492, 839582451, 850768229, 308975574, 153427239, 676576545, 437353301]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1258122521]
  exp := ![1, 1]
  pdgood := [5, 1258122521]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1258122521.out
  a := [-15399108929, -71471823794, 571359597374, 1138440378432, -1085591652438, -1293184126006, 606353049755, 274556667010, -108313711800]
  b := [2277124081, 41236999161, 81877685164, -164547180016, -263938784892, 185917157272, 190346759169, -76335935273, -30705078055, 10831371180]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1258122521 T_ofList CD1258122521

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

end VoightMaximalOrderD10R275

namespace VoightMaximalOrderD10R276

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3946990075853, [1, -7, -41, 62, 48, -92, 3, 39, -13, -2, 1], 1⟩
local notation "l" => [1, -7, -41, 62, 48, -92, 3, 39, -13, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 41, -62, -48, 92, -3, -39, 13, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], ![-2, 13, 89, -83, -158, 136, 86, -81, -13, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], ![-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], ![-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], ![-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], ![-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], ![-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], ![-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], ![-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], ![-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], ![-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], ![-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], ![-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], ![-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], ![-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60], ![-60, 238, 3713, 3872, -13186, -3808, 14591, -1853, -4975, 1752]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], ![-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], ![-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], ![-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], ![-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60], ![-60, 238, 3713, 3872, -13186, -3808, 14591, -1853, -4975, 1752], ![-1752, 12204, 72070, -104911, -80224, 147998, -9064, -53737, 20923, -1471]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], ![-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], ![-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], ![-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], ![-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60], ![-60, 238, 3713, 3872, -13186, -3808, 14591, -1853, -4975, 1752], ![-1752, 12204, 72070, -104911, -80224, 147998, -9064, -53737, 20923, -1471], ![1471, -12049, -48107, 163272, -34303, -215556, 152411, 48305, -72860, 17981]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], ![-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], ![-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], ![-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], ![-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60], ![-60, 238, 3713, 3872, -13186, -3808, 14591, -1853, -4975, 1752], ![-1752, 12204, 72070, -104911, -80224, 147998, -9064, -53737, 20923, -1471], ![1471, -12049, -48107, 163272, -34303, -215556, 152411, 48305, -72860, 17981], ![-17981, 127338, 725172, -1162929, -699816, 1619949, -269499, -548848, 282058, -36898]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-17, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-17, -2, -1], [-21, -17, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-17, -2, -1], [-21, -17, -2, -1], [-182, -21, -17, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-17, -2, -1], [-21, -17, -2, -1], [-182, -21, -17, -2, -1], [-60, -182, -21, -17, -2, -1]], ![[], [], [], [-1], [-2, -1], [-17, -2, -1], [-21, -17, -2, -1], [-182, -21, -17, -2, -1], [-60, -182, -21, -17, -2, -1], [-1752, -60, -182, -21, -17, -2, -1]], ![[], [], [-1], [-2, -1], [-17, -2, -1], [-21, -17, -2, -1], [-182, -21, -17, -2, -1], [-60, -182, -21, -17, -2, -1], [-1752, -60, -182, -21, -17, -2, -1], [1471, -1752, -60, -182, -21, -17, -2, -1]], ![[], [-1], [-2, -1], [-17, -2, -1], [-21, -17, -2, -1], [-182, -21, -17, -2, -1], [-60, -182, -21, -17, -2, -1], [-1752, -60, -182, -21, -17, -2, -1], [1471, -1752, -60, -182, -21, -17, -2, -1], [-17981, 1471, -1752, -60, -182, -21, -17, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 41, -62, -48, 92, -3, -39, 13, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], [-2, 13, 89, -83, -158, 136, 86, -81, -13, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], [-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], [-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], [-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], [-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], [-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], [-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], [-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], [-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], [-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], [-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], [-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], [-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], [-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60], [-60, 238, 3713, 3872, -13186, -3808, 14591, -1853, -4975, 1752]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], [-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], [-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], [-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], [-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60], [-60, 238, 3713, 3872, -13186, -3808, 14591, -1853, -4975, 1752], [-1752, 12204, 72070, -104911, -80224, 147998, -9064, -53737, 20923, -1471]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], [-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], [-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], [-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], [-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60], [-60, 238, 3713, 3872, -13186, -3808, 14591, -1853, -4975, 1752], [-1752, 12204, 72070, -104911, -80224, 147998, -9064, -53737, 20923, -1471], [1471, -12049, -48107, 163272, -34303, -215556, 152411, 48305, -72860, 17981]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 41, -62, -48, 92, -3, -39, 13, 2], [-2, 13, 89, -83, -158, 136, 86, -81, -13, 17], [-17, 117, 710, -965, -899, 1406, 85, -577, 140, 21], [-21, 130, 978, -592, -1973, 1033, 1343, -734, -304, 182], [-182, 1253, 7592, -10306, -9328, 14771, 487, -5755, 1632, 60], [-60, 238, 3713, 3872, -13186, -3808, 14591, -1853, -4975, 1752], [-1752, 12204, 72070, -104911, -80224, 147998, -9064, -53737, 20923, -1471], [1471, -12049, -48107, 163272, -34303, -215556, 152411, 48305, -72860, 17981], [-17981, 127338, 725172, -1162929, -699816, 1619949, -269499, -548848, 282058, -36898]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp18413 : Fact (Nat.Prime 18413) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 5
  a' := [1]
  b' := [10, 5]
  k := [1]
  f := [4, 8, 11, 0, -1, 10, 3, 1, 4, 1]
  g := [5, 4, 1]
  h := [9, 9, 7, 5, 2, 1, 6, 5, 1]
  a := [4, 8]
  b := [8, 5, 8, 8, 6, 7, 10, 7, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD18413 : CertificateDedekindCriterionLists l 18413 where
  n := 2
  a' := [1715, 3282, 1006, 13236, 1280, 1838, 8712, 7872]
  b' := [18229, 3034, 4222, 7070, 5646, 3364, 7332, 12563, 5263]
  k := [12093, 10300, 13358, 16326, 380, 7478, 6850, 6867, 1]
  f := [4867, 2545, 5469, 2915, 40, 1042, 4065, 5768, 3963, 1]
  g := [15526, 8116, 17445, 9296, 126, 3324, 12967, 18398, 12639, 1]
  h := [5772, 1]
  a := [7000, 2558, 5612, 3246, 9086, 10411, 1492, 15959, 11432]
  b := [11348, 3620, 4344, 12451, 1909, 11527, 1949, 14068, 6981]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![11, 18413]
  exp := ![1, 1]
  pdgood := [11, 18413]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp18413.out
  a := [-46615858, -579847792, 847294681, 1860231500, -1806208180, -1109460230, 1068465708, 32377876, -98176320]
  b := [-6688343, 42129620, 302688395, -207965131, -462332551, 299807422, 184036465, -135259204, -5201314, 9817632]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 18413 T_ofList CD18413

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

end VoightMaximalOrderD10R276

namespace VoightMaximalOrderD10R278

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3959351078125, [-5, 35, -80, 40, 86, -95, -11, 38, -6, -4, 1], 1⟩
local notation "l" => [-5, 35, -80, 40, 86, -95, -11, 38, -6, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -35, 80, -40, -86, 95, 11, -38, 6, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -35, 80, -40, -86, 95, 11, -38, 6, 4], ![20, -135, 285, -80, -384, 294, 139, -141, -14, 22]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -35, 80, -40, -86, 95, 11, -38, 6, 4], ![20, -135, 285, -80, -384, 294, 139, -141, -14, 22], ![110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -35, 80, -40, -86, 95, 11, -38, 6, 4], ![20, -135, 285, -80, -384, 294, 139, -141, -14, 22], ![110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], ![370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -35, 80, -40, -86, 95, 11, -38, 6, 4], ![20, -135, 285, -80, -384, 294, 139, -141, -14, 22], ![110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], ![370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], ![1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -35, 80, -40, -86, 95, 11, -38, 6, 4], ![20, -135, 285, -80, -384, 294, 139, -141, -14, 22], ![110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], ![370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], ![1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895], ![4475, -29890, 61925, -15320, -83280, 59008, 30151, -25795, -3016, 3026]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -35, 80, -40, -86, 95, 11, -38, 6, 4], ![20, -135, 285, -80, -384, 294, 139, -141, -14, 22], ![110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], ![370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], ![1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895], ![4475, -29890, 61925, -15320, -83280, 59008, 30151, -25795, -3016, 3026], ![15130, -101435, 212190, -59115, -275556, 204190, 92294, -84837, -7639, 9088]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -35, 80, -40, -86, 95, 11, -38, 6, 4], ![20, -135, 285, -80, -384, 294, 139, -141, -14, 22], ![110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], ![370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], ![1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895], ![4475, -29890, 61925, -15320, -83280, 59008, 30151, -25795, -3016, 3026], ![15130, -101435, 212190, -59115, -275556, 204190, 92294, -84837, -7639, 9088], ![45440, -302950, 625605, -151330, -840683, 587804, 304158, -253050, -30309, 28713]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -35, 80, -40, -86, 95, 11, -38, 6, 4], ![20, -135, 285, -80, -384, 294, 139, -141, -14, 22], ![110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], ![370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], ![1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895], ![4475, -29890, 61925, -15320, -83280, 59008, 30151, -25795, -3016, 3026], ![15130, -101435, 212190, -59115, -275556, 204190, 92294, -84837, -7639, 9088], ![45440, -302950, 625605, -151330, -840683, 587804, 304158, -253050, -30309, 28713], ![143565, -959515, 1994090, -522915, -2620648, 1887052, 903647, -786936, -80772, 84543]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-22, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-22, -4, -1], [-74, -22, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-22, -4, -1], [-74, -22, -4, -1], [-287, -74, -22, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-22, -4, -1], [-74, -22, -4, -1], [-287, -74, -22, -4, -1], [-895, -287, -74, -22, -4, -1]], ![[], [], [], [-1], [-4, -1], [-22, -4, -1], [-74, -22, -4, -1], [-287, -74, -22, -4, -1], [-895, -287, -74, -22, -4, -1], [-3026, -895, -287, -74, -22, -4, -1]], ![[], [], [-1], [-4, -1], [-22, -4, -1], [-74, -22, -4, -1], [-287, -74, -22, -4, -1], [-895, -287, -74, -22, -4, -1], [-3026, -895, -287, -74, -22, -4, -1], [-9088, -3026, -895, -287, -74, -22, -4, -1]], ![[], [-1], [-4, -1], [-22, -4, -1], [-74, -22, -4, -1], [-287, -74, -22, -4, -1], [-895, -287, -74, -22, -4, -1], [-3026, -895, -287, -74, -22, -4, -1], [-9088, -3026, -895, -287, -74, -22, -4, -1], [-28713, -9088, -3026, -895, -287, -74, -22, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -35, 80, -40, -86, 95, 11, -38, 6, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -35, 80, -40, -86, 95, 11, -38, 6, 4], [20, -135, 285, -80, -384, 294, 139, -141, -14, 22]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -35, 80, -40, -86, 95, 11, -38, 6, 4], [20, -135, 285, -80, -384, 294, 139, -141, -14, 22], [110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -35, 80, -40, -86, 95, 11, -38, 6, 4], [20, -135, 285, -80, -384, 294, 139, -141, -14, 22], [110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], [370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -35, 80, -40, -86, 95, 11, -38, 6, 4], [20, -135, 285, -80, -384, 294, 139, -141, -14, 22], [110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], [370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], [1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -35, 80, -40, -86, 95, 11, -38, 6, 4], [20, -135, 285, -80, -384, 294, 139, -141, -14, 22], [110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], [370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], [1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895], [4475, -29890, 61925, -15320, -83280, 59008, 30151, -25795, -3016, 3026]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -35, 80, -40, -86, 95, 11, -38, 6, 4], [20, -135, 285, -80, -384, 294, 139, -141, -14, 22], [110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], [370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], [1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895], [4475, -29890, 61925, -15320, -83280, 59008, 30151, -25795, -3016, 3026], [15130, -101435, 212190, -59115, -275556, 204190, 92294, -84837, -7639, 9088]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -35, 80, -40, -86, 95, 11, -38, 6, 4], [20, -135, 285, -80, -384, 294, 139, -141, -14, 22], [110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], [370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], [1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895], [4475, -29890, 61925, -15320, -83280, 59008, 30151, -25795, -3016, 3026], [15130, -101435, 212190, -59115, -275556, 204190, 92294, -84837, -7639, 9088], [45440, -302950, 625605, -151330, -840683, 587804, 304158, -253050, -30309, 28713]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -35, 80, -40, -86, 95, 11, -38, 6, 4], [20, -135, 285, -80, -384, 294, 139, -141, -14, 22], [110, -750, 1625, -595, -1972, 1706, 536, -697, -9, 74], [370, -2480, 5170, -1335, -6959, 5058, 2520, -2276, -253, 287], [1435, -9675, 20480, -6310, -26017, 20306, 8215, -8386, -554, 895], [4475, -29890, 61925, -15320, -83280, 59008, 30151, -25795, -3016, 3026], [15130, -101435, 212190, -59115, -275556, 204190, 92294, -84837, -7639, 9088], [45440, -302950, 625605, -151330, -840683, 587804, 304158, -253050, -30309, 28713], [143565, -959515, 1994090, -522915, -2620648, 1887052, 903647, -786936, -80772, 84543]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp253398469 : Fact (Nat.Prime 253398469) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [4, 2, 1]
  b' := [4, 1, 4, 1]
  k := [1, 0, 4, 3, 4, 1, 1]
  f := [1, -7, 16, -8, -14, 19, 7, -6, 3, 2]
  g := [0, 4, 0, 3, 1]
  h := [0, 0, 0, 4, 0, 3, 1]
  a := [1, 2, 1, 4]
  b := [0, 3, 1, 2, 3, 1, 2, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD253398469 : CertificateDedekindCriterionLists l 253398469 where
  n := 2
  a' := [226352361, 4960518, 167893426, 39834414, 8587934, 48346582, 208207822, 56086930]
  b' := [166456950, 142319614, 99280359, 70608977, 121122603, 34206342, 9758714, 82357859, 190855817]
  k := [104676297, 200855227, 121219257, 124544240, 232959412, 111018856, 187961530, 17501578, 1]
  f := [95335307, 210182128, 69586716, 232031633, 24546763, 42050047, 40754568, 49225378, 8448590, 1]
  g := [98745351, 217700122, 72075759, 240331161, 25424774, 43554133, 42212316, 50986118, 8750787, 1]
  h := [244647678, 1]
  a := [195236565, 229606197, 94683359, 69843674, 227892011, 86917850, 21079147, 44618032, 218067048]
  b := [113329749, 175940369, 198892780, 40602490, 121369909, 87378853, 233023238, 103839815, 35331421]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 253398469]
  exp := ![1, 1]
  pdgood := [5, 253398469]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp253398469.out
  a := [81185187633401, -215665717287266, -134287928497702, 540625099935296, -67431800840804, -281865953484766, 77720377733980, 37307431403216, -12125549195760]
  b := [11597920147410, -58975512286279, 72681231135544, 46254629546006, -110908226832628, 8172341514064, 41115471030215, -9480885504950, -4215765108152, 1212554919576]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 253398469 T_ofList CD253398469

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

end VoightMaximalOrderD10R278

namespace VoightMaximalOrderD10R283

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3994414465625, [1, -3, -8, 20, 23, -35, -18, 24, 1, -5, 1], 1⟩
local notation "l" => [1, -3, -8, 20, 23, -35, -18, 24, 1, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -20, -23, 35, 18, -24, -1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], ![-5, 14, 43, -92, -135, 152, 125, -102, -29, 24]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], ![-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], ![-24, 67, 206, -437, -644, 705, 584, -451, -126, 91]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], ![-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], ![-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], ![-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], ![-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], ![-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], ![-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], ![-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], ![-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], ![-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], ![-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], ![-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103], ![-1103, 2980, 9720, -19179, -31154, 29424, 28839, -18009, -6656, 3586]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], ![-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], ![-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], ![-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], ![-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103], ![-1103, 2980, 9720, -19179, -31154, 29424, 28839, -18009, -6656, 3586], ![-3586, 9655, 31668, -62000, -101657, 94356, 93972, -57225, -21595, 11274]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], ![-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], ![-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], ![-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], ![-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103], ![-1103, 2980, 9720, -19179, -31154, 29424, 28839, -18009, -6656, 3586], ![-3586, 9655, 31668, -62000, -101657, 94356, 93972, -57225, -21595, 11274], ![-11274, 30236, 99847, -193812, -321302, 292933, 297288, -176604, -68499, 34775]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], ![-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], ![-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], ![-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], ![-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103], ![-1103, 2980, 9720, -19179, -31154, 29424, 28839, -18009, -6656, 3586], ![-3586, 9655, 31668, -62000, -101657, 94356, 93972, -57225, -21595, 11274], ![-11274, 30236, 99847, -193812, -321302, 292933, 297288, -176604, -68499, 34775], ![-34775, 93051, 308436, -595653, -993637, 895823, 918883, -537312, -211379, 105376]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1], [-1103, -329, -91, -24, -5, -1]], ![[], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1], [-1103, -329, -91, -24, -5, -1], [-3586, -1103, -329, -91, -24, -5, -1]], ![[], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1], [-1103, -329, -91, -24, -5, -1], [-3586, -1103, -329, -91, -24, -5, -1], [-11274, -3586, -1103, -329, -91, -24, -5, -1]], ![[], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1], [-1103, -329, -91, -24, -5, -1], [-3586, -1103, -329, -91, -24, -5, -1], [-11274, -3586, -1103, -329, -91, -24, -5, -1], [-34775, -11274, -3586, -1103, -329, -91, -24, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -20, -23, 35, 18, -24, -1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], [-5, 14, 43, -92, -135, 152, 125, -102, -29, 24]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], [-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], [-24, 67, 206, -437, -644, 705, 584, -451, -126, 91]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], [-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], [-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], [-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], [-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], [-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], [-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], [-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], [-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], [-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], [-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], [-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103], [-1103, 2980, 9720, -19179, -31154, 29424, 28839, -18009, -6656, 3586]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], [-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], [-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], [-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], [-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103], [-1103, 2980, 9720, -19179, -31154, 29424, 28839, -18009, -6656, 3586], [-3586, 9655, 31668, -62000, -101657, 94356, 93972, -57225, -21595, 11274]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], [-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], [-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], [-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], [-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103], [-1103, 2980, 9720, -19179, -31154, 29424, 28839, -18009, -6656, 3586], [-3586, 9655, 31668, -62000, -101657, 94356, 93972, -57225, -21595, 11274], [-11274, 30236, 99847, -193812, -321302, 292933, 297288, -176604, -68499, 34775]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -20, -23, 35, 18, -24, -1, 5], [-5, 14, 43, -92, -135, 152, 125, -102, -29, 24], [-24, 67, 206, -437, -644, 705, 584, -451, -126, 91], [-91, 249, 795, -1614, -2530, 2541, 2343, -1600, -542, 329], [-329, 896, 2881, -5785, -9181, 8985, 8463, -5553, -1929, 1103], [-1103, 2980, 9720, -19179, -31154, 29424, 28839, -18009, -6656, 3586], [-3586, 9655, 31668, -62000, -101657, 94356, 93972, -57225, -21595, 11274], [-11274, 30236, 99847, -193812, -321302, 292933, 297288, -176604, -68499, 34775], [-34775, 93051, 308436, -595653, -993637, 895823, 918883, -537312, -211379, 105376]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1889 : Fact (Nat.Prime 1889) := fact_iff.2 (by norm_num)
instance hp676661 : Fact (Nat.Prime 676661) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3]
  b' := [3, 3, 3, 3, 3]
  k := [1]
  f := [3, 7, 8, 4, 1, 11, 7, -4, 1, 1]
  g := [4, 4, 2, 3, 0, 1]
  h := [4, 4, 2, 3, 0, 1]
  a := [1, 2, 2, 1, 4]
  b := [2, 1, 1, 4, 0, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1889 : CertificateDedekindCriterionLists l 1889 where
  n := 2
  a' := [111, 534, 451, 1433, 333, 1466, 198, 685]
  b' := [1400, 251, 482, 1528, 582, 130, 890, 751, 1603]
  k := [1222, 841, 404, 746, 163, 175, 546, 564, 1]
  f := [631, 321, 396, 568, 229, 152, 568, 229, 428, 1]
  g := [1806, 916, 1132, 1624, 653, 434, 1625, 653, 1224, 1]
  h := [660, 1]
  a := [1484, 294, 197, 630, 1793, 1796, 1032, 172, 1446]
  b := [39, 1873, 1695, 1585, 1881, 104, 2, 443, 443]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD676661 : CertificateDedekindCriterionLists l 676661 where
  n := 2
  a' := [175328, 166311, 140790, 471574, 276159, 299939, 510344, 583954]
  b' := [220044, 166446, 18076, 328169, 207596, 580178, 384292, 545135, 311039]
  k := [545043, 651300, 582595, 421141, 147271, 472095, 417049, 446393, 1]
  f := [298435, 99823, 436216, 12526, 347987, 13141, 283344, 146177, 149573, 1]
  g := [445328, 148956, 650926, 18690, 519270, 19608, 422809, 218126, 223194, 1]
  h := [453462, 1]
  a := [53920, 655674, 556217, 512607, 440005, 181525, 44272, 293610, 570085]
  b := [633408, 567524, 91974, 574125, 82172, 31658, 355847, 35650, 106576]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 1889, 676661]
  exp := ![1, 1, 1]
  pdgood := [5, 1889, 676661]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1889.out
    exact hp676661.out
  a := [-52562401216, -515330165838, -459463556747, 1649780952428, 870428707998, -1670469004948, -47090273012, 459192719910, -104955715740]
  b := [-19651154787, -14408161866, 186162484377, 149523074219, -342654389623, -152542453894, 241771590618, 6152741570, -51167057778, 10495571574]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1889 T_ofList CD1889
    exact satisfiesDedekindCriterion_of_certificate_lists T l 676661 T_ofList CD676661

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

end VoightMaximalOrderD10R283

end TraceEuclidean
