import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk212
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

namespace VoightMaximalOrderD10R526

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5863765633525, [-1, -1, 22, 15, -48, -21, 38, 8, -11, -1, 1], 1⟩
local notation "l" => [-1, -1, 22, 15, -48, -21, 38, 8, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -22, -15, 48, 21, -38, -8, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -22, -15, 48, 21, -38, -8, 11, 1], ![1, 2, -21, -37, 33, 69, -17, -46, 3, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -22, -15, 48, 21, -38, -8, 11, 1], ![1, 2, -21, -37, 33, 69, -17, -46, 3, 12], ![12, 13, -262, -201, 539, 285, -387, -113, 86, 15]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -22, -15, 48, 21, -38, -8, 11, 1], ![1, 2, -21, -37, 33, 69, -17, -46, 3, 12], ![12, 13, -262, -201, 539, 285, -387, -113, 86, 15], ![15, 27, -317, -487, 519, 854, -285, -507, 52, 101]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -22, -15, 48, 21, -38, -8, 11, 1], ![1, 2, -21, -37, 33, 69, -17, -46, 3, 12], ![12, 13, -262, -201, 539, 285, -387, -113, 86, 15], ![15, 27, -317, -487, 519, 854, -285, -507, 52, 101], ![101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -22, -15, 48, 21, -38, -8, 11, 1], ![1, 2, -21, -37, 33, 69, -17, -46, 3, 12], ![12, 13, -262, -201, 539, 285, -387, -113, 86, 15], ![15, 27, -317, -487, 519, 854, -285, -507, 52, 101], ![101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153], ![153, 254, -3250, -4490, 5512, 7574, -3174, -4208, 590, 757]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -22, -15, 48, 21, -38, -8, 11, 1], ![1, 2, -21, -37, 33, 69, -17, -46, 3, 12], ![12, 13, -262, -201, 539, 285, -387, -113, 86, 15], ![15, 27, -317, -487, 519, 854, -285, -507, 52, 101], ![101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153], ![153, 254, -3250, -4490, 5512, 7574, -3174, -4208, 590, 757], ![757, 910, -16400, -14605, 31846, 21409, -21192, -9230, 4119, 1347]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -22, -15, 48, 21, -38, -8, 11, 1], ![1, 2, -21, -37, 33, 69, -17, -46, 3, 12], ![12, 13, -262, -201, 539, 285, -387, -113, 86, 15], ![15, 27, -317, -487, 519, 854, -285, -507, 52, 101], ![101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153], ![153, 254, -3250, -4490, 5512, 7574, -3174, -4208, 590, 757], ![757, 910, -16400, -14605, 31846, 21409, -21192, -9230, 4119, 1347], ![1347, 2104, -28724, -36605, 50051, 60133, -29777, -31968, 5587, 5466]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -22, -15, 48, 21, -38, -8, 11, 1], ![1, 2, -21, -37, 33, 69, -17, -46, 3, 12], ![12, 13, -262, -201, 539, 285, -387, -113, 86, 15], ![15, 27, -317, -487, 519, 854, -285, -507, 52, 101], ![101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153], ![153, 254, -3250, -4490, 5512, 7574, -3174, -4208, 590, 757], ![757, 910, -16400, -14605, 31846, 21409, -21192, -9230, 4119, 1347], ![1347, 2104, -28724, -36605, 50051, 60133, -29777, -31968, 5587, 5466], ![5466, 6813, -118148, -110714, 225763, 164837, -147575, -73505, 28158, 11053]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-101, -15, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-101, -15, -12, -1, -1], [-153, -101, -15, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-101, -15, -12, -1, -1], [-153, -101, -15, -12, -1, -1], [-757, -153, -101, -15, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-101, -15, -12, -1, -1], [-153, -101, -15, -12, -1, -1], [-757, -153, -101, -15, -12, -1, -1], [-1347, -757, -153, -101, -15, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-101, -15, -12, -1, -1], [-153, -101, -15, -12, -1, -1], [-757, -153, -101, -15, -12, -1, -1], [-1347, -757, -153, -101, -15, -12, -1, -1], [-5466, -1347, -757, -153, -101, -15, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -22, -15, 48, 21, -38, -8, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -22, -15, 48, 21, -38, -8, 11, 1], [1, 2, -21, -37, 33, 69, -17, -46, 3, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -22, -15, 48, 21, -38, -8, 11, 1], [1, 2, -21, -37, 33, 69, -17, -46, 3, 12], [12, 13, -262, -201, 539, 285, -387, -113, 86, 15]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -22, -15, 48, 21, -38, -8, 11, 1], [1, 2, -21, -37, 33, 69, -17, -46, 3, 12], [12, 13, -262, -201, 539, 285, -387, -113, 86, 15], [15, 27, -317, -487, 519, 854, -285, -507, 52, 101]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -22, -15, 48, 21, -38, -8, 11, 1], [1, 2, -21, -37, 33, 69, -17, -46, 3, 12], [12, 13, -262, -201, 539, 285, -387, -113, 86, 15], [15, 27, -317, -487, 519, 854, -285, -507, 52, 101], [101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -22, -15, 48, 21, -38, -8, 11, 1], [1, 2, -21, -37, 33, 69, -17, -46, 3, 12], [12, 13, -262, -201, 539, 285, -387, -113, 86, 15], [15, 27, -317, -487, 519, 854, -285, -507, 52, 101], [101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153], [153, 254, -3250, -4490, 5512, 7574, -3174, -4208, 590, 757]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -22, -15, 48, 21, -38, -8, 11, 1], [1, 2, -21, -37, 33, 69, -17, -46, 3, 12], [12, 13, -262, -201, 539, 285, -387, -113, 86, 15], [15, 27, -317, -487, 519, 854, -285, -507, 52, 101], [101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153], [153, 254, -3250, -4490, 5512, 7574, -3174, -4208, 590, 757], [757, 910, -16400, -14605, 31846, 21409, -21192, -9230, 4119, 1347]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -22, -15, 48, 21, -38, -8, 11, 1], [1, 2, -21, -37, 33, 69, -17, -46, 3, 12], [12, 13, -262, -201, 539, 285, -387, -113, 86, 15], [15, 27, -317, -487, 519, 854, -285, -507, 52, 101], [101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153], [153, 254, -3250, -4490, 5512, 7574, -3174, -4208, 590, 757], [757, 910, -16400, -14605, 31846, 21409, -21192, -9230, 4119, 1347], [1347, 2104, -28724, -36605, 50051, 60133, -29777, -31968, 5587, 5466]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -22, -15, 48, 21, -38, -8, 11, 1], [1, 2, -21, -37, 33, 69, -17, -46, 3, 12], [12, 13, -262, -201, 539, 285, -387, -113, 86, 15], [15, 27, -317, -487, 519, 854, -285, -507, 52, 101], [101, 116, -2195, -1832, 4361, 2640, -2984, -1093, 604, 153], [153, 254, -3250, -4490, 5512, 7574, -3174, -4208, 590, 757], [757, 910, -16400, -14605, 31846, 21409, -21192, -9230, 4119, 1347], [1347, 2104, -28724, -36605, 50051, 60133, -29777, -31968, 5587, 5466], [5466, 6813, -118148, -110714, 225763, 164837, -147575, -73505, 28158, 11053]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp53 : Fact (Nat.Prime 53) := fact_iff.2 (by norm_num)
instance hp36677 : Fact (Nat.Prime 36677) := fact_iff.2 (by norm_num)
instance hp120661 : Fact (Nat.Prime 120661) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 3, 3, 2, 4, 4, 3]
  b' := [1, 0, 3, 2, 4, 0, 1, 4]
  k := [1, 0, 3, 4, 0, 2, 1]
  f := [1, 1, -3, -2, 11, 6, -5, 1, 4, 1]
  g := [2, 1, 2, 1, 2, 3, 4, 3, 1]
  h := [2, 1, 1]
  a := [0, 4, 4, 1, 1, 2, 2]
  b := [3, 4, 1, 0, 3, 4, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD53 : CertificateDedekindCriterionLists l 53 where
  n := 2
  a' := [52, 6, 24, 10, 0, 43, 47, 3]
  b' := [48, 8, 25, 35, 13, 35, 24, 48, 35]
  k := [36, 11, 12, 42, 2, 20, 21, 42, 1]
  f := [2, 4, 2, 1, 6, 6, 2, 2, 5, 1]
  g := [21, 38, 18, 10, 52, 49, 19, 19, 47, 1]
  h := [5, 1]
  a := [10, 7, 18, 47, 37, 42, 33, 49, 2]
  b := [42, 35, 38, 11, 24, 26, 19, 35, 51]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD36677 : CertificateDedekindCriterionLists l 36677 where
  n := 2
  a' := [30290, 27375, 10641, 24344, 5485, 20480, 36326, 30244]
  b' := [2620, 25730, 16477, 15555, 1971, 33059, 15584, 7327, 4790]
  k := [31800, 6006, 26201, 8036, 9817, 23259, 33637, 3765, 1]
  f := [13415, 18042, 84, 5063, 7431, 5178, 24634, 21633, 1786, 1]
  g := [14141, 19018, 88, 5337, 7833, 5458, 25967, 22803, 1882, 1]
  h := [34794, 1]
  a := [5765, 5510, 7417, 1252, 32724, 32136, 16445, 26073, 20976]
  b := [5082, 8265, 1213, 9762, 16313, 17970, 19395, 7065, 15701]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD120661 : CertificateDedekindCriterionLists l 120661 where
  n := 2
  a' := [111323, 81661, 31103, 96719, 31889, 59287, 49848, 101153]
  b' := [109811, 15230, 51770, 21313, 11203, 82197, 14090, 12295, 96015]
  k := [95228, 90224, 29613, 27920, 37853, 56723, 34852, 92420, 1]
  f := [10981, 13958, 1728, 7083, 12254, 2212, 13037, 6617, 12468, 1]
  g := [93837, 119270, 14758, 60526, 104711, 18895, 111405, 56537, 106540, 1]
  h := [14120, 1]
  a := [61870, 88830, 106389, 117888, 17502, 73123, 3541, 115961, 9174]
  b := [21113, 71427, 100279, 30856, 56989, 25234, 22523, 53756, 111487]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 53, 36677, 120661]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 53, 36677, 120661]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp53.out
    exact hp36677.out
    exact hp120661.out
  a := [732067047933, -85653372686866, 23866534719579, 343744125041662, -216844189201563, -191184462221006, 123045900549474, 28488634309800, -16749652129400]
  b := [-1904820174638, 1109217954861, 40980995176987, -22199783866629, -67385416776718, 41319332862523, 25966646304339, -15855374049482, -3016359952274, 1674965212940]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 53 T_ofList CD53
    exact satisfiesDedekindCriterion_of_certificate_lists T l 36677 T_ofList CD36677
    exact satisfiesDedekindCriterion_of_certificate_lists T l 120661 T_ofList CD120661

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

end VoightMaximalOrderD10R526

namespace VoightMaximalOrderD10R527

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5873821065625, [1, -6, 0, 38, -12, -51, 19, 22, -8, -3, 1], 1⟩
local notation "l" => [1, -6, 0, 38, -12, -51, 19, 22, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 0, -38, 12, 51, -19, -22, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], ![-3, 17, 6, -114, -2, 165, -6, -85, 2, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], ![-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], ![-17, 99, 17, -640, 90, 865, -158, -380, 51, 53]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], ![-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], ![-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], ![-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], ![-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], ![-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], ![-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], ![-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], ![-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], ![-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], ![-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], ![-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674], ![-674, 3834, 1207, -25311, 207, 34897, -2100, -16025, 630, 2378]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], ![-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], ![-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], ![-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], ![-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674], ![-674, 3834, 1207, -25311, 207, 34897, -2100, -16025, 630, 2378], ![-2378, 13594, 3834, -89157, 3225, 121485, -10285, -54416, 2999, 7764]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], ![-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], ![-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], ![-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], ![-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674], ![-674, 3834, 1207, -25311, 207, 34897, -2100, -16025, 630, 2378], ![-2378, 13594, 3834, -89157, 3225, 121485, -10285, -54416, 2999, 7764], ![-7764, 44206, 13594, -291198, 4011, 399189, -26031, -181093, 7696, 26291]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], ![-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], ![-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], ![-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], ![-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674], ![-674, 3834, 1207, -25311, 207, 34897, -2100, -16025, 630, 2378], ![-2378, 13594, 3834, -89157, 3225, 121485, -10285, -54416, 2999, 7764], ![-7764, 44206, 13594, -291198, 4011, 399189, -26031, -181093, 7696, 26291], ![-26291, 149982, 44206, -985464, 24294, 1344852, -100340, -604433, 29235, 86569]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-53, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-53, -17, -3, -1], [-210, -53, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-53, -17, -3, -1], [-210, -53, -17, -3, -1], [-674, -210, -53, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-53, -17, -3, -1], [-210, -53, -17, -3, -1], [-674, -210, -53, -17, -3, -1], [-2378, -674, -210, -53, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-53, -17, -3, -1], [-210, -53, -17, -3, -1], [-674, -210, -53, -17, -3, -1], [-2378, -674, -210, -53, -17, -3, -1], [-7764, -2378, -674, -210, -53, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-53, -17, -3, -1], [-210, -53, -17, -3, -1], [-674, -210, -53, -17, -3, -1], [-2378, -674, -210, -53, -17, -3, -1], [-7764, -2378, -674, -210, -53, -17, -3, -1], [-26291, -7764, -2378, -674, -210, -53, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 0, -38, 12, 51, -19, -22, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], [-3, 17, 6, -114, -2, 165, -6, -85, 2, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], [-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], [-17, 99, 17, -640, 90, 865, -158, -380, 51, 53]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], [-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], [-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], [-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], [-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], [-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], [-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], [-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], [-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], [-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], [-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], [-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674], [-674, 3834, 1207, -25311, 207, 34897, -2100, -16025, 630, 2378]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], [-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], [-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], [-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], [-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674], [-674, 3834, 1207, -25311, 207, 34897, -2100, -16025, 630, 2378], [-2378, 13594, 3834, -89157, 3225, 121485, -10285, -54416, 2999, 7764]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], [-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], [-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], [-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], [-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674], [-674, 3834, 1207, -25311, 207, 34897, -2100, -16025, 630, 2378], [-2378, 13594, 3834, -89157, 3225, 121485, -10285, -54416, 2999, 7764], [-7764, 44206, 13594, -291198, 4011, 399189, -26031, -181093, 7696, 26291]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 0, -38, 12, 51, -19, -22, 8, 3], [-3, 17, 6, -114, -2, 165, -6, -85, 2, 17], [-17, 99, 17, -640, 90, 865, -158, -380, 51, 53], [-53, 301, 99, -1997, -4, 2793, -142, -1324, 44, 210], [-210, 1207, 301, -7881, 523, 10706, -1197, -4762, 356, 674], [-674, 3834, 1207, -25311, 207, 34897, -2100, -16025, 630, 2378], [-2378, 13594, 3834, -89157, 3225, 121485, -10285, -54416, 2999, 7764], [-7764, 44206, 13594, -291198, 4011, 399189, -26031, -181093, 7696, 26291], [-26291, 149982, 44206, -985464, 24294, 1344852, -100340, -604433, 29235, 86569]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp112559 : Fact (Nat.Prime 112559) := fact_iff.2 (by norm_num)
instance hp16699 : Fact (Nat.Prime 16699) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 3]
  b' := [3, 2, 0, 3]
  k := [1]
  f := [0, 2, 2, -4, 7, 15, 0, -2, 3, 1]
  g := [1, 2, 3, 3, 1, 1]
  h := [1, 2, 3, 3, 1, 1]
  a := [4, 4, 0, 0, 3]
  b := [1, 0, 1, 3, 3, 2, 1, 4, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD112559 : CertificateDedekindCriterionLists l 112559 where
  n := 2
  a' := [50014, 73384, 94989, 109612, 36591, 42745, 58659, 95331]
  b' := [44100, 473, 13498, 88665, 76033, 15698, 8729, 74812, 64447]
  k := [86525, 42049, 51268, 30691, 92212, 17495, 90089, 87232, 1]
  f := [4815, 12025, 7843, 12042, 5010, 11001, 5795, 9023, 11238, 1]
  g := [42803, 106893, 69712, 107042, 44528, 97790, 51507, 80206, 99894, 1]
  h := [12662, 1]
  a := [60671, 25004, 103730, 44653, 32240, 101605, 100414, 19548, 60017]
  b := [20253, 3790, 11482, 832, 42095, 50302, 34512, 71115, 52542]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD16699 : CertificateDedekindCriterionLists l 16699 where
  n := 2
  a' := [16488, 2307, 2964, 15586, 9486, 14780, 13416, 3785]
  b' := [10260, 6342, 16648, 13780, 11283, 6770, 9863, 270, 14423]
  k := [6732, 15773, 9903, 2693, 4678, 8809, 3272, 10525, 1]
  f := [10086, 3485, 2712, 7808, 5976, 4948, 1144, 4762, 3603, 1]
  g := [14729, 5088, 3960, 11402, 8726, 7225, 1670, 6954, 5261, 1]
  h := [11435, 1]
  a := [10894, 11493, 14907, 2187, 5137, 3869, 10252, 1454, 6166]
  b := [4432, 13474, 11569, 9405, 14126, 8782, 6081, 1986, 10533]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 112559, 16699]
  exp := ![1, 1, 1]
  pdgood := [5, 112559, 16699]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp112559.out
    exact hp16699.out
  a := [-19469961717083, -73891068384240, 89670216925770, 184411138420480, -128100954462252, -115886534501508, 60265430337510, 20848511569668, -8557724251440]
  b := [-3246559971798, 7154783653043, 27151465074373, -20331415548348, -38179774506718, 20703156540144, 16857611427828, -7463499231258, -2341582884510, 855772425144]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 112559 T_ofList CD112559
    exact satisfiesDedekindCriterion_of_certificate_lists T l 16699 T_ofList CD16699

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

end VoightMaximalOrderD10R527

namespace VoightMaximalOrderD10R531

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5906673101808, [1, -7, 10, 19, -38, -18, 36, 7, -11, -1, 1], 1⟩
local notation "l" => [1, -7, 10, 19, -38, -18, 36, 7, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -10, -19, 38, 18, -36, -7, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], ![-1, 6, -3, -29, 19, 56, -18, -43, 4, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], ![-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], ![-12, 83, -114, -231, 427, 235, -376, -102, 89, 16]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], ![-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], ![-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], ![-16, 100, -77, -418, 377, 715, -341, -488, 74, 105]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], ![-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], ![-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], ![-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], ![-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], ![-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], ![-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], ![-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], ![-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179], ![-179, 1148, -1071, -4351, 4730, 6794, -4177, -4318, 893, 846]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], ![-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], ![-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], ![-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], ![-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179], ![-179, 1148, -1071, -4351, 4730, 6794, -4177, -4318, 893, 846], ![-846, 5743, -7312, -17145, 27797, 19958, -23662, -10099, 4988, 1739]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], ![-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], ![-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], ![-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], ![-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179], ![-179, 1148, -1071, -4351, 4730, 6794, -4177, -4318, 893, 846], ![-846, 5743, -7312, -17145, 27797, 19958, -23662, -10099, 4988, 1739], ![-1739, 11327, -11647, -40353, 48937, 59099, -42646, -35835, 9030, 6727]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], ![-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], ![-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], ![-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], ![-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179], ![-179, 1148, -1071, -4351, 4730, 6794, -4177, -4318, 893, 846], ![-846, 5743, -7312, -17145, 27797, 19958, -23662, -10099, 4988, 1739], ![-1739, 11327, -11647, -40353, 48937, 59099, -42646, -35835, 9030, 6727], ![-6727, 45350, -55943, -139460, 215273, 170023, -183073, -89735, 38162, 15757]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-105, -16, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-105, -16, -12, -1, -1], [-179, -105, -16, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-105, -16, -12, -1, -1], [-179, -105, -16, -12, -1, -1], [-846, -179, -105, -16, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-105, -16, -12, -1, -1], [-179, -105, -16, -12, -1, -1], [-846, -179, -105, -16, -12, -1, -1], [-1739, -846, -179, -105, -16, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-105, -16, -12, -1, -1], [-179, -105, -16, -12, -1, -1], [-846, -179, -105, -16, -12, -1, -1], [-1739, -846, -179, -105, -16, -12, -1, -1], [-6727, -1739, -846, -179, -105, -16, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -10, -19, 38, 18, -36, -7, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], [-1, 6, -3, -29, 19, 56, -18, -43, 4, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], [-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], [-12, 83, -114, -231, 427, 235, -376, -102, 89, 16]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], [-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], [-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], [-16, 100, -77, -418, 377, 715, -341, -488, 74, 105]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], [-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], [-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], [-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], [-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], [-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], [-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], [-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], [-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179], [-179, 1148, -1071, -4351, 4730, 6794, -4177, -4318, 893, 846]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], [-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], [-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], [-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], [-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179], [-179, 1148, -1071, -4351, 4730, 6794, -4177, -4318, 893, 846], [-846, 5743, -7312, -17145, 27797, 19958, -23662, -10099, 4988, 1739]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], [-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], [-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], [-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], [-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179], [-179, 1148, -1071, -4351, 4730, 6794, -4177, -4318, 893, 846], [-846, 5743, -7312, -17145, 27797, 19958, -23662, -10099, 4988, 1739], [-1739, 11327, -11647, -40353, 48937, 59099, -42646, -35835, 9030, 6727]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -10, -19, 38, 18, -36, -7, 11, 1], [-1, 6, -3, -29, 19, 56, -18, -43, 4, 12], [-12, 83, -114, -231, 427, 235, -376, -102, 89, 16], [-16, 100, -77, -418, 377, 715, -341, -488, 74, 105], [-105, 719, -950, -2072, 3572, 2267, -3065, -1076, 667, 179], [-179, 1148, -1071, -4351, 4730, 6794, -4177, -4318, 893, 846], [-846, 5743, -7312, -17145, 27797, 19958, -23662, -10099, 4988, 1739], [-1739, 11327, -11647, -40353, 48937, 59099, -42646, -35835, 9030, 6727], [-6727, 45350, -55943, -139460, 215273, 170023, -183073, -89735, 38162, 15757]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp14437 : Fact (Nat.Prime 14437) := fact_iff.2 (by norm_num)
instance hp2841211 : Fact (Nat.Prime 2841211) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1, 1, 0, 1]
  k := [1, 1, 1, 0, 0, 1, 1]
  f := [0, 4, -4, -9, 20, 10, -17, -3, 6, 1]
  g := [1, 0, 1, 0, 1, 1, 0, 0, 1]
  h := [1, 1, 1]
  a := [1, 1, 0, 0, 1, 0, 1, 1]
  b := [1, 0, 1, 1, 1, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [0, 1, 0, 1, 1]
  b' := [2, 1, 0, 2, 1, 1]
  k := [1, 0, 2, 2, 1, 1, 1]
  f := [1, 5, 0, -3, 16, 8, -10, -1, 5, 1]
  g := [2, 2, 2, 2, 2, 0, 2, 0, 1]
  h := [2, 2, 1]
  a := [1, 0, 1, 0, 0, 0, 1, 2]
  b := [0, 2, 2, 1, 2, 1, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD14437 : CertificateDedekindCriterionLists l 14437 where
  n := 2
  a' := [374, 1294, 2779, 5729, 5762, 1116, 4181, 2136]
  b' := [8677, 2586, 8268, 10851, 5412, 3329, 814, 11628, 4575]
  k := [327, 9346, 11620, 284, 13722, 7637, 12191, 4883, 1]
  f := [8257, 1905, 1671, 9196, 11528, 1941, 5242, 10691, 2029, 1]
  g := [9938, 2292, 2011, 11068, 13874, 2335, 6309, 12867, 2441, 1]
  h := [11995, 1]
  a := [6392, 12939, 12224, 13269, 1106, 13283, 7683, 13702, 2325]
  b := [8134, 5282, 6094, 2048, 6358, 13431, 10418, 5793, 12112]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2841211 : CertificateDedekindCriterionLists l 2841211 where
  n := 2
  a' := [2691622, 505532, 278597, 489388, 895907, 2612566, 977623, 170747]
  b' := [243711, 2261485, 520079, 2723868, 582584, 672789, 396031, 442254, 2506549]
  k := [1453402, 2086226, 1090464, 854047, 2757361, 2772559, 2200148, 1777700, 1]
  f := [331334, 67422, 347883, 803, 60175, 110803, 526433, 170432, 432233, 1]
  g := [1770345, 360238, 1858767, 4287, 321520, 592029, 2812774, 910627, 2309455, 1]
  h := [531755, 1]
  a := [808472, 1108926, 685773, 764515, 1131415, 2684718, 956290, 1158983, 1061318]
  b := [599989, 2183739, 1063444, 1361283, 614934, 231125, 2395398, 156138, 1779893]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 3, 14437, 2841211]
  exp := ![1, 1, 1, 1]
  pdgood := [2, 3, 14437, 2841211]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp14437.out
    exact hp2841211.out
  a := [-58251457933682, -2591196006544, 455910989452666, 26745827259021, -655018085234200, -47628996796790, 266032960085862, 15811328851989, -29596098558610]
  b := [-8356795616132, 34004728172370, 13613142212790, -116650782283155, -13211417206791, 109463203410125, 8554991698864, -33222689289988, -1877093870785, 2959609855861]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 14437 T_ofList CD14437
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2841211 T_ofList CD2841211

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

end VoightMaximalOrderD10R531

namespace VoightMaximalOrderD10R535

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5948409528125, [1, -5, 1, 25, -25, -27, 33, 9, -11, -1, 1], 1⟩
local notation "l" => [1, -5, 1, 25, -25, -27, 33, 9, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, -1, -25, 25, 27, -33, -9, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], ![-1, 4, 4, -26, 0, 52, -6, -42, 2, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], ![-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], ![-12, 59, -8, -296, 274, 324, -344, -114, 90, 14]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], ![-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], ![-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], ![-14, 58, 45, -358, 54, 652, -138, -470, 40, 104]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], ![-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], ![-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], ![-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], ![-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], ![-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], ![-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], ![-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], ![-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144], ![-144, 616, 362, -3646, 1045, 6130, -1890, -4076, 510, 818]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], ![-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], ![-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], ![-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], ![-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144], ![-144, 616, 362, -3646, 1045, 6130, -1890, -4076, 510, 818], ![-818, 3946, -202, -20088, 16804, 23131, -20864, -9252, 4922, 1328]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], ![-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], ![-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], ![-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], ![-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144], ![-144, 616, 362, -3646, 1045, 6130, -1890, -4076, 510, 818], ![-818, 3946, -202, -20088, 16804, 23131, -20864, -9252, 4922, 1328], ![-1328, 5822, 2618, -33402, 13112, 52660, -20693, -32816, 5356, 6250]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], ![-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], ![-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], ![-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], ![-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144], ![-144, 616, 362, -3646, 1045, 6130, -1890, -4076, 510, 818], ![-818, 3946, -202, -20088, 16804, 23131, -20864, -9252, 4922, 1328], ![-1328, 5822, 2618, -33402, 13112, 52660, -20693, -32816, 5356, 6250], ![-6250, 29922, -428, -153632, 122848, 181862, -153590, -76943, 35934, 11606]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-14, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-14, -12, -1, -1], [-104, -14, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-14, -12, -1, -1], [-104, -14, -12, -1, -1], [-144, -104, -14, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-14, -12, -1, -1], [-104, -14, -12, -1, -1], [-144, -104, -14, -12, -1, -1], [-818, -144, -104, -14, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-14, -12, -1, -1], [-104, -14, -12, -1, -1], [-144, -104, -14, -12, -1, -1], [-818, -144, -104, -14, -12, -1, -1], [-1328, -818, -144, -104, -14, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-14, -12, -1, -1], [-104, -14, -12, -1, -1], [-144, -104, -14, -12, -1, -1], [-818, -144, -104, -14, -12, -1, -1], [-1328, -818, -144, -104, -14, -12, -1, -1], [-6250, -1328, -818, -144, -104, -14, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, -1, -25, 25, 27, -33, -9, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], [-1, 4, 4, -26, 0, 52, -6, -42, 2, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], [-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], [-12, 59, -8, -296, 274, 324, -344, -114, 90, 14]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], [-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], [-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], [-14, 58, 45, -358, 54, 652, -138, -470, 40, 104]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], [-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], [-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], [-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], [-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], [-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], [-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], [-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], [-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144], [-144, 616, 362, -3646, 1045, 6130, -1890, -4076, 510, 818]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], [-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], [-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], [-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], [-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144], [-144, 616, 362, -3646, 1045, 6130, -1890, -4076, 510, 818], [-818, 3946, -202, -20088, 16804, 23131, -20864, -9252, 4922, 1328]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], [-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], [-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], [-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], [-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144], [-144, 616, 362, -3646, 1045, 6130, -1890, -4076, 510, 818], [-818, 3946, -202, -20088, 16804, 23131, -20864, -9252, 4922, 1328], [-1328, 5822, 2618, -33402, 13112, 52660, -20693, -32816, 5356, 6250]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, -1, -25, 25, 27, -33, -9, 11, 1], [-1, 4, 4, -26, 0, 52, -6, -42, 2, 12], [-12, 59, -8, -296, 274, 324, -344, -114, 90, 14], [-14, 58, 45, -358, 54, 652, -138, -470, 40, 104], [-104, 506, -46, -2555, 2242, 2862, -2780, -1074, 674, 144], [-144, 616, 362, -3646, 1045, 6130, -1890, -4076, 510, 818], [-818, 3946, -202, -20088, 16804, 23131, -20864, -9252, 4922, 1328], [-1328, 5822, 2618, -33402, 13112, 52660, -20693, -32816, 5356, 6250], [-6250, 29922, -428, -153632, 122848, 181862, -153590, -76943, 35934, 11606]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp449 : Fact (Nat.Prime 449) := fact_iff.2 (by norm_num)
instance hp4239401 : Fact (Nat.Prime 4239401) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 4]
  b' := [1, 3, 1, 2]
  k := [1]
  f := [3, 1, 3, -5, 9, 7, -5, -1, 3, 1]
  g := [4, 0, 2, 0, 2, 1]
  h := [4, 0, 2, 0, 2, 1]
  a := [4, 1, 2, 2, 1]
  b := [1, 2, 1, 0, 1, 4, 4, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD449 : CertificateDedekindCriterionLists l 449 where
  n := 2
  a' := [211, 432, 149, 347, 231, 224, 180, 402]
  b' := [100, 195, 274, 325, 313, 19, 382, 58, 105]
  k := [360, 305, 128, 275, 65, 237, 436, 117, 1]
  f := [271, 283, 336, 59, 28, 1, 92, 233, 51, 1]
  g := [312, 325, 386, 67, 32, 1, 106, 268, 58, 1]
  h := [390, 1]
  a := [411, 113, 306, 285, 174, 307, 299, 312, 4]
  b := [305, 82, 46, 245, 308, 129, 401, 165, 445]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4239401 : CertificateDedekindCriterionLists l 4239401 where
  n := 2
  a' := [3952859, 685663, 657812, 919387, 3848603, 3029758, 1839661, 2301628]
  b' := [1273145, 1584973, 2996073, 3970596, 642266, 3216305, 1890608, 3719776, 3512620]
  k := [1238580, 3442621, 2330199, 2801898, 3670988, 753012, 753541, 250273, 1]
  f := [305799, 1383249, 3697480, 853907, 3522367, 3080672, 1833570, 2946121, 121443, 1]
  g := [315100, 1425321, 3809940, 879878, 3629501, 3174371, 1889338, 3035728, 125136, 1]
  h := [4114264, 1]
  a := [1996569, 719161, 3241479, 4064882, 2144976, 2842333, 1333843, 4238289, 4075072]
  b := [612329, 339521, 2886818, 1933490, 1147242, 1002447, 2665983, 3607859, 164329]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 449, 4239401]
  exp := ![1, 1, 1]
  pdgood := [5, 449, 4239401]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp449.out
    exact hp4239401.out
  a := [-3869837487565, -5440225490166, 47193023549846, 3659078503656, -93004131625918, -2715923013492, 41606105173080, 1211913063524, -4650349555560]
  b := [-775870988562, 2471443994107, 3455375471835, -12927210513394, -2493855450674, 15789442051038, 853108020338, -5213421434896, -167694801908, 465034955556]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 449 T_ofList CD449
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4239401 T_ofList CD4239401

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

end VoightMaximalOrderD10R535

end TraceEuclidean
