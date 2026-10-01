import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk203
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

namespace VoightMaximalOrderD10R426

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5143161503125, [-1, -4, 9, 21, -25, -29, 24, 14, -9, -2, 1], 1⟩
local notation "l" => [-1, -4, 9, 21, -25, -29, 24, 14, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -9, -21, 25, 29, -24, -14, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -9, -21, 25, 29, -24, -14, 9, 2], ![2, 9, -14, -51, 29, 83, -19, -52, 4, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -9, -21, 25, 29, -24, -14, 9, 2], ![2, 9, -14, -51, 29, 83, -19, -52, 4, 13], ![13, 54, -108, -287, 274, 406, -229, -201, 65, 30]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -9, -21, 25, 29, -24, -14, 9, 2], ![2, 9, -14, -51, 29, 83, -19, -52, 4, 13], ![13, 54, -108, -287, 274, 406, -229, -201, 65, 30], ![30, 133, -216, -738, 463, 1144, -314, -649, 69, 125]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -9, -21, 25, 29, -24, -14, 9, 2], ![2, 9, -14, -51, 29, 83, -19, -52, 4, 13], ![13, 54, -108, -287, 274, 406, -229, -201, 65, 30], ![30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], ![125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -9, -21, 25, 29, -24, -14, 9, 2], ![2, 9, -14, -51, 29, 83, -19, -52, 4, 13], ![13, 54, -108, -287, 274, 406, -229, -201, 65, 30], ![30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], ![125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319], ![319, 1401, -2341, -7691, 5134, 11638, -3568, -6322, 807, 1114]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -9, -21, 25, 29, -24, -14, 9, 2], ![2, 9, -14, -51, 29, 83, -19, -52, 4, 13], ![13, 54, -108, -287, 274, 406, -229, -201, 65, 30], ![30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], ![125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319], ![319, 1401, -2341, -7691, 5134, 11638, -3568, -6322, 807, 1114], ![1114, 4775, -8625, -25735, 20159, 37440, -15098, -19164, 3704, 3035]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -9, -21, 25, 29, -24, -14, 9, 2], ![2, 9, -14, -51, 29, 83, -19, -52, 4, 13], ![13, 54, -108, -287, 274, 406, -229, -201, 65, 30], ![30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], ![125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319], ![319, 1401, -2341, -7691, 5134, 11638, -3568, -6322, 807, 1114], ![1114, 4775, -8625, -25735, 20159, 37440, -15098, -19164, 3704, 3035], ![3035, 13254, -22540, -72360, 50140, 108174, -35400, -57588, 8151, 9774]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -9, -21, 25, 29, -24, -14, 9, 2], ![2, 9, -14, -51, 29, 83, -19, -52, 4, 13], ![13, 54, -108, -287, 274, 406, -229, -201, 65, 30], ![30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], ![125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319], ![319, 1401, -2341, -7691, 5134, 11638, -3568, -6322, 807, 1114], ![1114, 4775, -8625, -25735, 20159, 37440, -15098, -19164, 3704, 3035], ![3035, 13254, -22540, -72360, 50140, 108174, -35400, -57588, 8151, 9774], ![9774, 42131, -74712, -227794, 171990, 333586, -126402, -172236, 30378, 27699]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-125, -30, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-125, -30, -13, -2, -1], [-319, -125, -30, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-125, -30, -13, -2, -1], [-319, -125, -30, -13, -2, -1], [-1114, -319, -125, -30, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-125, -30, -13, -2, -1], [-319, -125, -30, -13, -2, -1], [-1114, -319, -125, -30, -13, -2, -1], [-3035, -1114, -319, -125, -30, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-125, -30, -13, -2, -1], [-319, -125, -30, -13, -2, -1], [-1114, -319, -125, -30, -13, -2, -1], [-3035, -1114, -319, -125, -30, -13, -2, -1], [-9774, -3035, -1114, -319, -125, -30, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -9, -21, 25, 29, -24, -14, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -9, -21, 25, 29, -24, -14, 9, 2], [2, 9, -14, -51, 29, 83, -19, -52, 4, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -9, -21, 25, 29, -24, -14, 9, 2], [2, 9, -14, -51, 29, 83, -19, -52, 4, 13], [13, 54, -108, -287, 274, 406, -229, -201, 65, 30]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -9, -21, 25, 29, -24, -14, 9, 2], [2, 9, -14, -51, 29, 83, -19, -52, 4, 13], [13, 54, -108, -287, 274, 406, -229, -201, 65, 30], [30, 133, -216, -738, 463, 1144, -314, -649, 69, 125]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -9, -21, 25, 29, -24, -14, 9, 2], [2, 9, -14, -51, 29, 83, -19, -52, 4, 13], [13, 54, -108, -287, 274, 406, -229, -201, 65, 30], [30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], [125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -9, -21, 25, 29, -24, -14, 9, 2], [2, 9, -14, -51, 29, 83, -19, -52, 4, 13], [13, 54, -108, -287, 274, 406, -229, -201, 65, 30], [30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], [125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319], [319, 1401, -2341, -7691, 5134, 11638, -3568, -6322, 807, 1114]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -9, -21, 25, 29, -24, -14, 9, 2], [2, 9, -14, -51, 29, 83, -19, -52, 4, 13], [13, 54, -108, -287, 274, 406, -229, -201, 65, 30], [30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], [125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319], [319, 1401, -2341, -7691, 5134, 11638, -3568, -6322, 807, 1114], [1114, 4775, -8625, -25735, 20159, 37440, -15098, -19164, 3704, 3035]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -9, -21, 25, 29, -24, -14, 9, 2], [2, 9, -14, -51, 29, 83, -19, -52, 4, 13], [13, 54, -108, -287, 274, 406, -229, -201, 65, 30], [30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], [125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319], [319, 1401, -2341, -7691, 5134, 11638, -3568, -6322, 807, 1114], [1114, 4775, -8625, -25735, 20159, 37440, -15098, -19164, 3704, 3035], [3035, 13254, -22540, -72360, 50140, 108174, -35400, -57588, 8151, 9774]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -9, -21, 25, 29, -24, -14, 9, 2], [2, 9, -14, -51, 29, 83, -19, -52, 4, 13], [13, 54, -108, -287, 274, 406, -229, -201, 65, 30], [30, 133, -216, -738, 463, 1144, -314, -649, 69, 125], [125, 530, -992, -2841, 2387, 4088, -1856, -2064, 476, 319], [319, 1401, -2341, -7691, 5134, 11638, -3568, -6322, 807, 1114], [1114, 4775, -8625, -25735, 20159, 37440, -15098, -19164, 3704, 3035], [3035, 13254, -22540, -72360, 50140, 108174, -35400, -57588, 8151, 9774], [9774, 42131, -74712, -227794, 171990, 333586, -126402, -172236, 30378, 27699]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp52081 : Fact (Nat.Prime 52081) := fact_iff.2 (by norm_num)
instance hp31601 : Fact (Nat.Prime 31601) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 2, 1]
  b' := [1, 2, 0, 4, 4]
  k := [1]
  f := [1, 4, 3, -1, 9, 13, 0, -2, 5, 2]
  g := [2, 4, 2, 0, 4, 1]
  h := [2, 4, 2, 0, 4, 1]
  a := [0, 4, 4, 3, 4]
  b := [3, 2, 3, 4, 1, 0, 1, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD52081 : CertificateDedekindCriterionLists l 52081 where
  n := 2
  a' := [41653, 47634, 38403, 32496, 42968, 16000, 24266, 12600]
  b' := [10596, 41437, 48849, 9605, 12140, 39448, 15948, 22338, 50681]
  k := [14078, 49068, 39090, 40688, 28137, 10878, 1569, 34500, 1]
  f := [30901, 9700, 124, 17414, 29574, 13110, 17508, 15875, 11536, 1]
  g := [46206, 14503, 185, 26039, 44221, 19602, 26179, 23737, 17249, 1]
  h := [34830, 1]
  a := [20387, 31345, 1886, 1477, 33945, 51386, 40909, 24493, 36124]
  b := [8999, 6372, 31088, 37701, 41231, 44448, 41049, 6997, 15957]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31601 : CertificateDedekindCriterionLists l 31601 where
  n := 2
  a' := [1215, 23767, 650, 65, 30175, 17348, 26717, 23718]
  b' := [9282, 421, 9878, 6064, 2263, 31419, 31561, 10179, 18432]
  k := [11546, 17381, 13989, 13820, 25536, 7943, 10003, 12551, 1]
  f := [7301, 6677, 5667, 5276, 5241, 6593, 9374, 9267, 6654, 1]
  g := [24225, 22152, 18801, 17504, 17388, 21874, 31101, 30745, 22075, 1]
  h := [9524, 1]
  a := [30483, 14160, 12296, 6914, 23895, 30408, 19643, 628, 7076]
  b := [19488, 10343, 13054, 20727, 26889, 3341, 3152, 115, 24525]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 52081, 31601]
  exp := ![1, 1, 1]
  pdgood := [5, 52081, 31601]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp52081.out
    exact hp31601.out
  a := [-2677106705, -47500975490, 135457209546, 217430043730, -289933736742, -214494560042, 191646497356, 48060203556, -29342499720]
  b := [-1387987925, 8306404915, 23131195316, -41130771074, -50933796682, 53849089832, 32353555951, -24541425604, -5392870350, 2934249972]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 52081 T_ofList CD52081
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31601 T_ofList CD31601

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

end VoightMaximalOrderD10R426

namespace VoightMaximalOrderD10R431

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5172046653125, [1, -6, -10, 39, 14, -55, -2, 27, -4, -4, 1], 1⟩
local notation "l" => [1, -6, -10, 39, 14, -55, -2, 27, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 10, -39, -14, 55, 2, -27, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], ![-4, 23, 46, -146, -95, 206, 63, -106, -11, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], ![-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], ![-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], ![-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], ![-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], ![-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], ![-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], ![-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], ![-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], ![-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], ![-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], ![-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], ![-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], ![-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799], ![-799, 4544, 9421, -28267, -20130, 37977, 13648, -17704, -2411, 2579]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], ![-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], ![-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], ![-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], ![-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799], ![-799, 4544, 9421, -28267, -20130, 37977, 13648, -17704, -2411, 2579], ![-2579, 14675, 30334, -91160, -64373, 121715, 43135, -55985, -7388, 7905]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], ![-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], ![-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], ![-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], ![-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799], ![-799, 4544, 9421, -28267, -20130, 37977, 13648, -17704, -2411, 2579], ![-2579, 14675, 30334, -91160, -64373, 121715, 43135, -55985, -7388, 7905], ![-7905, 44851, 93725, -277961, -201830, 370402, 137525, -170300, -24365, 24232]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], ![-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], ![-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], ![-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], ![-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799], ![-799, 4544, 9421, -28267, -20130, 37977, 13648, -17704, -2411, 2579], ![-2579, 14675, 30334, -91160, -64373, 121715, 43135, -55985, -7388, 7905], ![-7905, 44851, 93725, -277961, -201830, 370402, 137525, -170300, -24365, 24232], ![-24232, 137487, 287171, -851323, -617209, 1130930, 418866, -516739, -73372, 72563]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-250, -69, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-250, -69, -20, -4, -1], [-799, -250, -69, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-250, -69, -20, -4, -1], [-799, -250, -69, -20, -4, -1], [-2579, -799, -250, -69, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-250, -69, -20, -4, -1], [-799, -250, -69, -20, -4, -1], [-2579, -799, -250, -69, -20, -4, -1], [-7905, -2579, -799, -250, -69, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-250, -69, -20, -4, -1], [-799, -250, -69, -20, -4, -1], [-2579, -799, -250, -69, -20, -4, -1], [-7905, -2579, -799, -250, -69, -20, -4, -1], [-24232, -7905, -2579, -799, -250, -69, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 10, -39, -14, 55, 2, -27, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], [-4, 23, 46, -146, -95, 206, 63, -106, -11, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], [-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], [-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], [-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], [-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], [-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], [-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], [-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], [-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], [-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], [-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], [-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], [-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], [-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799], [-799, 4544, 9421, -28267, -20130, 37977, 13648, -17704, -2411, 2579]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], [-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], [-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], [-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], [-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799], [-799, 4544, 9421, -28267, -20130, 37977, 13648, -17704, -2411, 2579], [-2579, 14675, 30334, -91160, -64373, 121715, 43135, -55985, -7388, 7905]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], [-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], [-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], [-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], [-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799], [-799, 4544, 9421, -28267, -20130, 37977, 13648, -17704, -2411, 2579], [-2579, 14675, 30334, -91160, -64373, 121715, 43135, -55985, -7388, 7905], [-7905, 44851, 93725, -277961, -201830, 370402, 137525, -170300, -24365, 24232]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 10, -39, -14, 55, 2, -27, 4, 4], [-4, 23, 46, -146, -95, 206, 63, -106, -11, 20], [-20, 116, 223, -734, -426, 1005, 246, -477, -26, 69], [-69, 394, 806, -2468, -1700, 3369, 1143, -1617, -201, 250], [-250, 1431, 2894, -8944, -5968, 12050, 3869, -5607, -617, 799], [-799, 4544, 9421, -28267, -20130, 37977, 13648, -17704, -2411, 2579], [-2579, 14675, 30334, -91160, -64373, 121715, 43135, -55985, -7388, 7905], [-7905, 44851, 93725, -277961, -201830, 370402, 137525, -170300, -24365, 24232], [-24232, 137487, 287171, -851323, -617209, 1130930, 418866, -516739, -73372, 72563]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp150459539 : Fact (Nat.Prime 150459539) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 2, 3]
  b' := [4, 4, 4, 3, 1]
  k := [1]
  f := [0, 2, 4, -5, 1, 15, 5, -3, 3, 2]
  g := [1, 2, 3, 1, 3, 1]
  h := [1, 2, 3, 1, 3, 1]
  a := [4, 1, 0, 1]
  b := [1, 0, 4, 2, 0, 4, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [3, 4, 0, 4, 2, 9, 7, 10]
  b' := [0, 4, 7, 0, 8, 1, 0, 10, 5]
  k := [5, 7, 1, 9, 4, 0, 3, 1, 1]
  f := [1, 2, 4, -1, 2, 7, 3, 0, 2, 1]
  g := [4, 4, 10, 6, 10, 4, 9, 6, 4, 1]
  h := [3, 1]
  a := [6, 6, 8, 7, 7, 8, 8, 4, 8]
  b := [7, 5, 5, 3, 8, 5, 6, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD150459539 : CertificateDedekindCriterionLists l 150459539 where
  n := 2
  a' := [68843089, 20113822, 72472251, 15312968, 77852135, 30497918, 92972089, 22058479]
  b' := [46236007, 13310853, 108934079, 4826252, 51873842, 77651496, 28429210, 19580234, 30984511]
  k := [139628585, 40172174, 26712635, 113452679, 149052654, 47812555, 79562331, 78328760, 1]
  f := [37553545, 5280718, 30752447, 87792518, 79329709, 102393879, 39523116, 18089238, 28969952, 1]
  g := [50768508, 7138984, 41574127, 118686402, 107245559, 138425931, 53431163, 24454778, 39164378, 1]
  h := [111295157, 1]
  a := [143468813, 20392217, 81290944, 87008536, 98728174, 117279850, 49721248, 45153835, 83210734]
  b := [18712437, 57027022, 28335299, 12279075, 7653444, 37452988, 58557087, 10216714, 67248805]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 150459539]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 150459539]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp150459539.out
  a := [1112997246899, 2676738135816, -24154198319753, 11279500397140, 41107599566386, -34555021298738, -4330989827224, 9844186106612, -2086902140120]
  b := [184120328709, -1280608653293, -698391346471, 7881925748067, -4458358057224, -6258229639972, 5227749598435, 359400347600, -1067894696266, 208690214012]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 150459539 T_ofList CD150459539

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

end VoightMaximalOrderD10R431

namespace VoightMaximalOrderD10R436

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5238865440625, [1, -8, -14, 45, 40, -57, -22, 30, 0, -5, 1], 1⟩
local notation "l" => [1, -8, -14, 45, 40, -57, -22, 30, 0, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, 14, -45, -40, 57, 22, -30, 0, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], ![-5, 39, 78, -211, -245, 245, 167, -128, -30, 25]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], ![-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], ![-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], ![-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], ![-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], ![-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], ![-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], ![-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], ![-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], ![-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], ![-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], ![-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], ![-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], ![-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152], ![-1152, 8869, 18809, -46247, -60170, 47898, 40276, -22722, -7140, 3705]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], ![-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], ![-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], ![-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], ![-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152], ![-1152, 8869, 18809, -46247, -60170, 47898, 40276, -22722, -7140, 3705], ![-3705, 28488, 60739, -147916, -194447, 151015, 129408, -70874, -22722, 11385]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], ![-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], ![-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], ![-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], ![-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152], ![-1152, 8869, 18809, -46247, -60170, 47898, 40276, -22722, -7140, 3705], ![-3705, 28488, 60739, -147916, -194447, 151015, 129408, -70874, -22722, 11385], ![-11385, 87375, 187878, -451586, -603316, 454498, 401485, -212142, -70874, 34203]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], ![-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], ![-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], ![-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], ![-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152], ![-1152, 8869, 18809, -46247, -60170, 47898, 40276, -22722, -7140, 3705], ![-3705, 28488, 60739, -147916, -194447, 151015, 129408, -70874, -22722, 11385], ![-11385, 87375, 187878, -451586, -603316, 454498, 401485, -212142, -70874, 34203], ![-34203, 262239, 566217, -1351257, -1819706, 1346255, 1206964, -624605, -212142, 100141]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1], [-1152, -347, -95, -25, -5, -1]], ![[], [], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1], [-1152, -347, -95, -25, -5, -1], [-3705, -1152, -347, -95, -25, -5, -1]], ![[], [], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1], [-1152, -347, -95, -25, -5, -1], [-3705, -1152, -347, -95, -25, -5, -1], [-11385, -3705, -1152, -347, -95, -25, -5, -1]], ![[], [-1], [-5, -1], [-25, -5, -1], [-95, -25, -5, -1], [-347, -95, -25, -5, -1], [-1152, -347, -95, -25, -5, -1], [-3705, -1152, -347, -95, -25, -5, -1], [-11385, -3705, -1152, -347, -95, -25, -5, -1], [-34203, -11385, -3705, -1152, -347, -95, -25, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, 14, -45, -40, 57, 22, -30, 0, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], [-5, 39, 78, -211, -245, 245, 167, -128, -30, 25]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], [-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], [-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], [-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], [-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], [-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], [-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], [-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], [-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], [-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], [-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], [-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], [-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], [-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152], [-1152, 8869, 18809, -46247, -60170, 47898, 40276, -22722, -7140, 3705]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], [-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], [-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], [-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], [-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152], [-1152, 8869, 18809, -46247, -60170, 47898, 40276, -22722, -7140, 3705], [-3705, 28488, 60739, -147916, -194447, 151015, 129408, -70874, -22722, 11385]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], [-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], [-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], [-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], [-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152], [-1152, 8869, 18809, -46247, -60170, 47898, 40276, -22722, -7140, 3705], [-3705, 28488, 60739, -147916, -194447, 151015, 129408, -70874, -22722, 11385], [-11385, 87375, 187878, -451586, -603316, 454498, 401485, -212142, -70874, 34203]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, 14, -45, -40, 57, 22, -30, 0, 5], [-5, 39, 78, -211, -245, 245, 167, -128, -30, 25], [-25, 195, 389, -1047, -1211, 1180, 795, -583, -128, 95], [-95, 735, 1525, -3886, -4847, 4204, 3270, -2055, -583, 347], [-347, 2681, 5593, -14090, -17766, 14932, 11838, -7140, -2055, 1152], [-1152, 8869, 18809, -46247, -60170, 47898, 40276, -22722, -7140, 3705], [-3705, 28488, 60739, -147916, -194447, 151015, 129408, -70874, -22722, 11385], [-11385, 87375, 187878, -451586, -603316, 454498, 401485, -212142, -70874, 34203], [-34203, 262239, 566217, -1351257, -1819706, 1346255, 1206964, -624605, -212142, 100141]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp54078611 : Fact (Nat.Prime 54078611) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := []
  b' := [4]
  k := [1]
  f := [3, 8, 6, -9, -8, 13, 6, -6, 0, 1]
  g := [4, 4, 0, 0, 0, 1]
  h := [4, 4, 0, 0, 0, 1]
  a := [1, 0, 4, 1, 1]
  b := [2, 1, 2, 4, 3, 0, 2, 4, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [15, 16, 10, 24, 6, 21, 16, 27]
  b' := [1, 20, 20, 19, 13, 7, 27, 17, 28]
  k := [9, 13, 26, 10, 0, 17, 28, 6, 1]
  f := [9, 6, 9, 0, 2, 7, 7, 8, 6, 1]
  g := [28, 15, 25, 2, 10, 15, 18, 26, 16, 1]
  h := [10, 1]
  a := [21, 18, 14, 3, 12, 7, 19, 13]
  b := [11, 27, 6, 2, 6, 11, 18, 18]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD54078611 : CertificateDedekindCriterionLists l 54078611 where
  n := 2
  a' := [49848612, 1003759, 50777887, 31701140, 43406095, 19582723, 29537534, 8562320]
  b' := [48488509, 31695041, 41875568, 50092558, 32558108, 36390715, 48148419, 33622056, 41109773]
  k := [19305759, 51919548, 31202502, 40416364, 20763717, 47794256, 3155868, 359590, 1]
  f := [21674789, 5029552, 17468736, 14538046, 5861526, 20176390, 11624257, 13803400, 13519053, 1]
  g := [43639760, 10126438, 35171343, 29270726, 11801525, 40622901, 23404138, 27791599, 27219098, 1]
  h := [26859508, 1]
  a := [37355179, 43622751, 26937896, 45195248, 25014754, 9856644, 1772552, 36265858, 52640425]
  b := [19299922, 30664875, 52407925, 23568941, 48959539, 49524030, 21389102, 22340567, 1438186]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 31, 54078611]
  exp := ![1, 1, 1]
  pdgood := [5, 31, 54078611]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp31.out
    exact hp54078611.out
  a := [-18122001911, -105125870340, 262107518851, 650686146914, -380942536106, -644130709310, 236359832760, 144731973620, -52258305720]
  b := [-3313023327, 16576849763, 55676570727, -80131862475, -169368051169, 57779172250, 102916697240, -28157503382, -17086112648, 5225830572]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 54078611 T_ofList CD54078611

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

end VoightMaximalOrderD10R436

namespace VoightMaximalOrderD10R440

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5247386378125, [1, -5, -5, 26, 10, -42, -6, 25, -1, -5, 1], 1⟩
local notation "l" => [1, -5, -5, 26, 10, -42, -6, 25, -1, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -26, -10, 42, 6, -25, 1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], ![-5, 24, 30, -125, -76, 200, 72, -119, -20, 26]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], ![-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], ![-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], ![-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], ![-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], ![-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], ![-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], ![-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], ![-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], ![-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], ![-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], ![-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], ![-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], ![-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817], ![-1817, 8628, 11260, -44433, -29377, 69038, 28350, -38448, -7932, 7148]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], ![-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], ![-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], ![-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], ![-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817], ![-1817, 8628, 11260, -44433, -29377, 69038, 28350, -38448, -7932, 7148], ![-7148, 33923, 44368, -174588, -115913, 270839, 111926, -150350, -31300, 27808]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], ![-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], ![-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], ![-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], ![-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817], ![-1817, 8628, 11260, -44433, -29377, 69038, 28350, -38448, -7932, 7148], ![-7148, 33923, 44368, -174588, -115913, 270839, 111926, -150350, -31300, 27808], ![-27808, 131892, 172963, -678640, -452668, 1052023, 437687, -583274, -122542, 107740]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], ![-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], ![-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], ![-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], ![-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817], ![-1817, 8628, 11260, -44433, -29377, 69038, 28350, -38448, -7932, 7148], ![-7148, 33923, 44368, -174588, -115913, 270839, 111926, -150350, -31300, 27808], ![-27808, 131892, 172963, -678640, -452668, 1052023, 437687, -583274, -122542, 107740], ![-107740, 510892, 670592, -2628277, -1756040, 4072412, 1698463, -2255813, -475534, 416158]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-26, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-26, -5, -1], [-110, -26, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-26, -5, -1], [-110, -26, -5, -1], [-457, -110, -26, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-26, -5, -1], [-110, -26, -5, -1], [-457, -110, -26, -5, -1], [-1817, -457, -110, -26, -5, -1]], ![[], [], [], [-1], [-5, -1], [-26, -5, -1], [-110, -26, -5, -1], [-457, -110, -26, -5, -1], [-1817, -457, -110, -26, -5, -1], [-7148, -1817, -457, -110, -26, -5, -1]], ![[], [], [-1], [-5, -1], [-26, -5, -1], [-110, -26, -5, -1], [-457, -110, -26, -5, -1], [-1817, -457, -110, -26, -5, -1], [-7148, -1817, -457, -110, -26, -5, -1], [-27808, -7148, -1817, -457, -110, -26, -5, -1]], ![[], [-1], [-5, -1], [-26, -5, -1], [-110, -26, -5, -1], [-457, -110, -26, -5, -1], [-1817, -457, -110, -26, -5, -1], [-7148, -1817, -457, -110, -26, -5, -1], [-27808, -7148, -1817, -457, -110, -26, -5, -1], [-107740, -27808, -7148, -1817, -457, -110, -26, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -26, -10, 42, 6, -25, 1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], [-5, 24, 30, -125, -76, 200, 72, -119, -20, 26]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], [-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], [-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], [-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], [-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], [-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], [-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], [-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], [-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], [-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], [-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], [-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], [-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], [-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817], [-1817, 8628, 11260, -44433, -29377, 69038, 28350, -38448, -7932, 7148]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], [-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], [-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], [-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], [-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817], [-1817, 8628, 11260, -44433, -29377, 69038, 28350, -38448, -7932, 7148], [-7148, 33923, 44368, -174588, -115913, 270839, 111926, -150350, -31300, 27808]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], [-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], [-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], [-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], [-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817], [-1817, 8628, 11260, -44433, -29377, 69038, 28350, -38448, -7932, 7148], [-7148, 33923, 44368, -174588, -115913, 270839, 111926, -150350, -31300, 27808], [-27808, 131892, 172963, -678640, -452668, 1052023, 437687, -583274, -122542, 107740]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 5, -26, -10, 42, 6, -25, 1, 5], [-5, 24, 30, -125, -76, 200, 72, -119, -20, 26], [-26, 125, 154, -646, -385, 1016, 356, -578, -93, 110], [-110, 524, 675, -2706, -1746, 4235, 1676, -2394, -468, 457], [-457, 2175, 2809, -11207, -7276, 17448, 6977, -9749, -1937, 1817], [-1817, 8628, 11260, -44433, -29377, 69038, 28350, -38448, -7932, 7148], [-7148, 33923, 44368, -174588, -115913, 270839, 111926, -150350, -31300, 27808], [-27808, 131892, 172963, -678640, -452668, 1052023, 437687, -583274, -122542, 107740], [-107740, 510892, 670592, -2628277, -1756040, 4072412, 1698463, -2255813, -475534, 416158]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1679163641 : Fact (Nat.Prime 1679163641) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4]
  b' := [0, 2, 0, 1]
  k := [1]
  f := [3, 1, 1, -2, -2, 10, 2, -5, 1, 1]
  g := [4, 0, 0, 2, 0, 1]
  h := [4, 0, 0, 2, 0, 1]
  a := [0, 4, 2, 1, 3]
  b := [4, 2, 0, 2, 3, 1, 3, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1679163641 : CertificateDedekindCriterionLists l 1679163641 where
  n := 2
  a' := [419109228, 120389692, 752927462, 83174775, 721188181, 1274006514, 1152865656, 1063036142]
  b' := [237898728, 753130936, 698528657, 444015595, 435825486, 1380179808, 585925242, 1351558896, 68458611]
  k := [1008097013, 1237975191, 824442909, 40055964, 666450968, 1329596995, 1276192439, 470862149, 1]
  f := [952202383, 147163935, 1204870806, 146521928, 1156848291, 1381467428, 568321489, 990872153, 202421907, 1]
  g := [1107479086, 171162121, 1401350430, 170415421, 1345496830, 1606744859, 660998306, 1152454778, 235431072, 1]
  h := [1443732564, 1]
  a := [645231386, 414871187, 1310318108, 422107533, 1401241992, 388058850, 261958864, 748738055, 1459600414]
  b := [1565112725, 1402744099, 1365081022, 1496469733, 1008236098, 35257345, 827745178, 1533079767, 219563227]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1679163641]
  exp := ![1, 1]
  pdgood := [5, 1679163641]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1679163641.out
  a := [653973690025, 304418666250, -10921232305862, 10434206900444, 13787780537824, -14945001461720, -2716861194004, 5022208689040, -967613947920]
  b := [129115574364, -851321105503, 574206353637, 2708220849622, -2556739592286, -2104707821328, 2209309740728, 285731136612, -550601566300, 96761394792]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1679163641 T_ofList CD1679163641

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

end VoightMaximalOrderD10R440

end TraceEuclidean
