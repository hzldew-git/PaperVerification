import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk189
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

namespace VoightMaximalOrderD10R268

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3864244215625, [1, -2, -13, 31, 10, -49, 7, 22, -6, -3, 1], 1⟩
local notation "l" => [1, -2, -13, 31, 10, -49, 7, 22, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 13, -31, -10, 49, -7, -22, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], ![-3, 5, 41, -80, -61, 137, 28, -73, -4, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], ![-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], ![-15, 27, 200, -424, -230, 674, 32, -302, 17, 41]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], ![-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], ![-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], ![-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], ![-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], ![-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], ![-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], ![-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], ![-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], ![-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], ![-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], ![-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364], ![-364, 588, 4971, -9397, -7420, 15365, 3478, -7209, -509, 1062]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], ![-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], ![-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], ![-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], ![-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364], ![-364, 588, 4971, -9397, -7420, 15365, 3478, -7209, -509, 1062], ![-1062, 1760, 14394, -27951, -20017, 44618, 7931, -19886, -837, 2677]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], ![-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], ![-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], ![-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], ![-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364], ![-364, 588, 4971, -9397, -7420, 15365, 3478, -7209, -509, 1062], ![-1062, 1760, 14394, -27951, -20017, 44618, 7931, -19886, -837, 2677], ![-2677, 4292, 36561, -68593, -54721, 111156, 25879, -50963, -3824, 7194]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], ![-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], ![-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], ![-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], ![-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364], ![-364, 588, 4971, -9397, -7420, 15365, 3478, -7209, -509, 1062], ![-1062, 1760, 14394, -27951, -20017, 44618, 7931, -19886, -837, 2677], ![-2677, 4292, 36561, -68593, -54721, 111156, 25879, -50963, -3824, 7194], ![-7194, 11711, 97814, -186453, -140533, 297785, 60798, -132389, -7799, 17758]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-140, -41, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-140, -41, -15, -3, -1], [-364, -140, -41, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-140, -41, -15, -3, -1], [-364, -140, -41, -15, -3, -1], [-1062, -364, -140, -41, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-140, -41, -15, -3, -1], [-364, -140, -41, -15, -3, -1], [-1062, -364, -140, -41, -15, -3, -1], [-2677, -1062, -364, -140, -41, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-140, -41, -15, -3, -1], [-364, -140, -41, -15, -3, -1], [-1062, -364, -140, -41, -15, -3, -1], [-2677, -1062, -364, -140, -41, -15, -3, -1], [-7194, -2677, -1062, -364, -140, -41, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 13, -31, -10, 49, -7, -22, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], [-3, 5, 41, -80, -61, 137, 28, -73, -4, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], [-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], [-15, 27, 200, -424, -230, 674, 32, -302, 17, 41]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], [-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], [-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], [-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], [-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], [-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], [-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], [-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], [-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], [-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], [-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], [-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364], [-364, 588, 4971, -9397, -7420, 15365, 3478, -7209, -509, 1062]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], [-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], [-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], [-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], [-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364], [-364, 588, 4971, -9397, -7420, 15365, 3478, -7209, -509, 1062], [-1062, 1760, 14394, -27951, -20017, 44618, 7931, -19886, -837, 2677]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], [-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], [-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], [-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], [-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364], [-364, 588, 4971, -9397, -7420, 15365, 3478, -7209, -509, 1062], [-1062, 1760, 14394, -27951, -20017, 44618, 7931, -19886, -837, 2677], [-2677, 4292, 36561, -68593, -54721, 111156, 25879, -50963, -3824, 7194]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 13, -31, -10, 49, -7, -22, 6, 3], [-3, 5, 41, -80, -61, 137, 28, -73, -4, 15], [-15, 27, 200, -424, -230, 674, 32, -302, 17, 41], [-41, 67, 560, -1071, -834, 1779, 387, -870, -56, 140], [-140, 239, 1887, -3780, -2471, 6026, 799, -2693, -30, 364], [-364, 588, 4971, -9397, -7420, 15365, 3478, -7209, -509, 1062], [-1062, 1760, 14394, -27951, -20017, 44618, 7931, -19886, -837, 2677], [-2677, 4292, 36561, -68593, -54721, 111156, 25879, -50963, -3824, 7194], [-7194, 11711, 97814, -186453, -140533, 297785, 60798, -132389, -7799, 17758]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1236558149 : Fact (Nat.Prime 1236558149) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 3]
  b' := [0, 4, 3, 3]
  k := [1]
  f := [3, 2, 6, 1, 2, 15, 3, -2, 3, 1]
  g := [4, 1, 2, 4, 1, 1]
  h := [4, 1, 2, 4, 1, 1]
  a := [4, 0, 2, 3, 1]
  b := [1, 4, 1, 0, 3, 4, 0, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1236558149 : CertificateDedekindCriterionLists l 1236558149 where
  n := 2
  a' := [738848422, 1053873311, 992671679, 610204773, 139091468, 135779097, 956646857, 150548213]
  b' := [255985000, 50165238, 208349175, 269593505, 731220415, 788027921, 563055786, 996227152, 945039870]
  k := [726383684, 1200688858, 1070552298, 621605131, 1009215287, 1001173948, 1191556511, 1203504183, 1]
  f := [150924723, 594862482, 7100951, 563664659, 603397146, 498417343, 13745763, 318186645, 308918648, 1]
  g := [293990888, 1158750838, 13832158, 1097979644, 1175375770, 970882398, 26775791, 619805506, 601752090, 1]
  h := [634806056, 1]
  a := [1134337922, 372046122, 255475387, 1061741777, 642442815, 230180731, 206092029, 1030131356, 1133286214]
  b := [192320835, 909493868, 730257861, 823757139, 163099942, 266076380, 989023914, 325205853, 103271935]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1236558149]
  exp := ![1, 1]
  pdgood := [5, 1236558149]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1236558149.out
  a := [-19096098507, -381141401736, 275357026569, 1114944923008, -567546411341, -719251873644, 332384515829, 127214143012, -57138362460]
  b := [-12639444626, -7161822223, 148314069106, -50351504907, -235441721375, 88533458519, 105941171307, -40906838147, -14435565175, 5713836246]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1236558149 T_ofList CD1236558149

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

end VoightMaximalOrderD10R268

namespace VoightMaximalOrderD10R269

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3870088137728, [1, -6, 3, 24, -19, -30, 21, 14, -8, -2, 1], 1⟩
local notation "l" => [1, -6, 3, 24, -19, -30, 21, 14, -8, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -24, 19, 30, -21, -14, 8, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], ![-2, 11, 0, -51, 14, 79, -12, -49, 2, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], ![-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], ![-12, 70, -25, -288, 177, 374, -173, -180, 47, 26]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], ![-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], ![-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], ![-26, 144, -8, -649, 206, 957, -172, -537, 28, 99]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], ![-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], ![-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], ![-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], ![-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], ![-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], ![-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], ![-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], ![-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226], ![-226, 1257, -110, -5577, 1910, 8012, -1570, -4286, 250, 707]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], ![-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], ![-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], ![-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], ![-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226], ![-226, 1257, -110, -5577, 1910, 8012, -1570, -4286, 250, 707], ![-707, 4016, -864, -17078, 7856, 23120, -6835, -11468, 1370, 1664]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], ![-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], ![-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], ![-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], ![-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226], ![-226, 1257, -110, -5577, 1910, 8012, -1570, -4286, 250, 707], ![-707, 4016, -864, -17078, 7856, 23120, -6835, -11468, 1370, 1664], ![-1664, 9277, -976, -40800, 14538, 57776, -11824, -30131, 1844, 4698]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], ![-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], ![-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], ![-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], ![-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226], ![-226, 1257, -110, -5577, 1910, 8012, -1570, -4286, 250, 707], ![-707, 4016, -864, -17078, 7856, 23120, -6835, -11468, 1370, 1664], ![-1664, 9277, -976, -40800, 14538, 57776, -11824, -30131, 1844, 4698], ![-4698, 26524, -4817, -113728, 48462, 155478, -40882, -77596, 7453, 11240]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-99, -26, -12, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-99, -26, -12, -2, -1], [-226, -99, -26, -12, -2, -1]], ![[], [], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-99, -26, -12, -2, -1], [-226, -99, -26, -12, -2, -1], [-707, -226, -99, -26, -12, -2, -1]], ![[], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-99, -26, -12, -2, -1], [-226, -99, -26, -12, -2, -1], [-707, -226, -99, -26, -12, -2, -1], [-1664, -707, -226, -99, -26, -12, -2, -1]], ![[], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-99, -26, -12, -2, -1], [-226, -99, -26, -12, -2, -1], [-707, -226, -99, -26, -12, -2, -1], [-1664, -707, -226, -99, -26, -12, -2, -1], [-4698, -1664, -707, -226, -99, -26, -12, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -24, 19, 30, -21, -14, 8, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], [-2, 11, 0, -51, 14, 79, -12, -49, 2, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], [-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], [-12, 70, -25, -288, 177, 374, -173, -180, 47, 26]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], [-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], [-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], [-26, 144, -8, -649, 206, 957, -172, -537, 28, 99]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], [-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], [-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], [-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], [-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], [-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], [-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], [-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], [-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226], [-226, 1257, -110, -5577, 1910, 8012, -1570, -4286, 250, 707]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], [-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], [-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], [-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], [-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226], [-226, 1257, -110, -5577, 1910, 8012, -1570, -4286, 250, 707], [-707, 4016, -864, -17078, 7856, 23120, -6835, -11468, 1370, 1664]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], [-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], [-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], [-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], [-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226], [-226, 1257, -110, -5577, 1910, 8012, -1570, -4286, 250, 707], [-707, 4016, -864, -17078, 7856, 23120, -6835, -11468, 1370, 1664], [-1664, 9277, -976, -40800, 14538, 57776, -11824, -30131, 1844, 4698]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -24, 19, 30, -21, -14, 8, 2], [-2, 11, 0, -51, 14, 79, -12, -49, 2, 12], [-12, 70, -25, -288, 177, 374, -173, -180, 47, 26], [-26, 144, -8, -649, 206, 957, -172, -537, 28, 99], [-99, 568, -153, -2384, 1232, 3176, -1122, -1558, 255, 226], [-226, 1257, -110, -5577, 1910, 8012, -1570, -4286, 250, 707], [-707, 4016, -864, -17078, 7856, 23120, -6835, -11468, 1370, 1664], [-1664, 9277, -976, -40800, 14538, 57776, -11824, -30131, 1844, 4698], [-4698, 26524, -4817, -113728, 48462, 155478, -40882, -77596, 7453, 11240]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3779382947 : Fact (Nat.Prime 3779382947) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 0, 1]
  k := [1]
  f := [0, 4, 0, -10, 11, 17, -9, -6, 5, 1]
  g := [1, 1, 1, 1, 0, 1]
  h := [1, 1, 1, 1, 0, 1]
  a := [1, 1]
  b := [1, 1, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3779382947 : CertificateDedekindCriterionLists l 3779382947 where
  n := 2
  a' := [3044479092, 1559713457, 354928635, 498609815, 229499355, 372504492, 584949766, 1328327807]
  b' := [2992251765, 326791590, 3559213919, 2963764392, 2628126673, 3005403905, 202135072, 2458327234, 272339460]
  k := [3422447946, 1076491782, 2108947384, 559066677, 237214367, 519241436, 203414820, 798317617, 1]
  f := [878879805, 829621705, 511520908, 803573498, 739852623, 1163169656, 1042141922, 915481490, 902688655, 1]
  g := [2228480749, 2103582295, 1297008406, 2037534666, 1875964514, 2949323867, 2642446892, 2321287693, 2288850281, 1]
  h := [1490532664, 1]
  a := [2370925248, 3604878401, 2557192641, 3321535138, 2016014463, 3067550968, 761866839, 370166247, 2855811918]
  b := [201013757, 998656878, 656773662, 1477017503, 237157128, 990299823, 175210750, 15964258, 923571029]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 3779382947]
  exp := ![1, 1]
  pdgood := [2, 3779382947]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3779382947.out
  a := [-135205358150, -208706659416, 1092067022616, 783769923826, -1579162032386, -672348209556, 719393281852, 138401941224, -103305132180]
  b := [-23794020674, 76626894240, 114213796929, -271486007940, -184283676420, 260017605783, 102468515036, -89419095268, -15906296766, 10330513218]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3779382947 T_ofList CD3779382947

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

end VoightMaximalOrderD10R269

namespace VoightMaximalOrderD10R271

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3890908535237, [1, -5, -4, 28, 4, -42, 5, 22, -6, -3, 1], 1⟩
local notation "l" => [1, -5, -4, 28, 4, -42, 5, 22, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -28, -4, 42, -5, -22, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], ![-3, 14, 17, -80, -40, 122, 27, -71, -4, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], ![-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], ![-15, 72, 74, -403, -140, 590, 47, -303, 19, 41]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], ![-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], ![-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], ![-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], ![-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], ![-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], ![-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], ![-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], ![-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], ![-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], ![-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], ![-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369], ![-369, 1703, 2145, -9574, -5216, 13856, 3552, -7246, -525, 1104]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], ![-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], ![-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], ![-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], ![-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369], ![-369, 1703, 2145, -9574, -5216, 13856, 3552, -7246, -525, 1104], ![-1104, 5151, 6119, -28767, -13990, 41152, 8336, -20736, -622, 2787]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], ![-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], ![-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], ![-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], ![-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369], ![-369, 1703, 2145, -9574, -5216, 13856, 3552, -7246, -525, 1104], ![-1104, 5151, 6119, -28767, -13990, 41152, 8336, -20736, -622, 2787], ![-2787, 12831, 16299, -71917, -39915, 103064, 27217, -52978, -4014, 7739]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], ![-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], ![-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], ![-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], ![-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369], ![-369, 1703, 2145, -9574, -5216, 13856, 3552, -7246, -525, 1104], ![-1104, 5151, 6119, -28767, -13990, 41152, 8336, -20736, -622, 2787], ![-2787, 12831, 16299, -71917, -39915, 103064, 27217, -52978, -4014, 7739], ![-7739, 35908, 43787, -200393, -102873, 285123, 64369, -143041, -6544, 19203]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-142, -41, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-142, -41, -15, -3, -1], [-369, -142, -41, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-142, -41, -15, -3, -1], [-369, -142, -41, -15, -3, -1], [-1104, -369, -142, -41, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-142, -41, -15, -3, -1], [-369, -142, -41, -15, -3, -1], [-1104, -369, -142, -41, -15, -3, -1], [-2787, -1104, -369, -142, -41, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-41, -15, -3, -1], [-142, -41, -15, -3, -1], [-369, -142, -41, -15, -3, -1], [-1104, -369, -142, -41, -15, -3, -1], [-2787, -1104, -369, -142, -41, -15, -3, -1], [-7739, -2787, -1104, -369, -142, -41, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -28, -4, 42, -5, -22, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], [-3, 14, 17, -80, -40, 122, 27, -71, -4, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], [-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], [-15, 72, 74, -403, -140, 590, 47, -303, 19, 41]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], [-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], [-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], [-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], [-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], [-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], [-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], [-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], [-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], [-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], [-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], [-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369], [-369, 1703, 2145, -9574, -5216, 13856, 3552, -7246, -525, 1104]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], [-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], [-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], [-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], [-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369], [-369, 1703, 2145, -9574, -5216, 13856, 3552, -7246, -525, 1104], [-1104, 5151, 6119, -28767, -13990, 41152, 8336, -20736, -622, 2787]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], [-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], [-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], [-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], [-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369], [-369, 1703, 2145, -9574, -5216, 13856, 3552, -7246, -525, 1104], [-1104, 5151, 6119, -28767, -13990, 41152, 8336, -20736, -622, 2787], [-2787, 12831, 16299, -71917, -39915, 103064, 27217, -52978, -4014, 7739]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -28, -4, 42, -5, -22, 6, 3], [-3, 14, 17, -80, -40, 122, 27, -71, -4, 15], [-15, 72, 74, -403, -140, 590, 47, -303, 19, 41], [-41, 190, 236, -1074, -567, 1582, 385, -855, -57, 142], [-142, 669, 758, -3740, -1642, 5397, 872, -2739, -3, 369], [-369, 1703, 2145, -9574, -5216, 13856, 3552, -7246, -525, 1104], [-1104, 5151, 6119, -28767, -13990, 41152, 8336, -20736, -622, 2787], [-2787, 12831, 16299, -71917, -39915, 103064, 27217, -52978, -4014, 7739], [-7739, 35908, 43787, -200393, -102873, 285123, 64369, -143041, -6544, 19203]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp16253 : Fact (Nat.Prime 16253) := fact_iff.2 (by norm_num)
instance hp828361 : Fact (Nat.Prime 828361) := fact_iff.2 (by norm_num)

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 3
  a' := [11, 3, 4, 1, 0, 2, 1]
  b' := [8, 13, 5, 6, 2, 15, 2, 2]
  k := [15, 1, 16, 3, 16, 5, 8, 13, 9, 10, 7, 1, 10, 13, 1]
  f := [1, 4, 4, 2, 5, 7, 6, 5, 4, 1]
  g := [9, 9, 5, 14, 7, 14, 15, 9, 1]
  h := [2, 5, 1]
  a := [10, 7, 11, 13, 11, 14, 13, 10]
  b := [16, 9, 13, 4, 0, 10, 7, 3, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD16253 : CertificateDedekindCriterionLists l 16253 where
  n := 2
  a' := [15346, 9824, 9412, 7658, 12267, 15225, 9363, 9941]
  b' := [4088, 14060, 12, 11657, 7637, 1790, 1007, 9296, 6119]
  k := [8654, 12855, 3495, 2869, 10061, 5370, 7764, 1736, 1]
  f := [217, 2308, 2294, 1668, 3157, 2437, 7064, 4395, 4016, 1]
  g := [486, 5169, 5137, 3735, 7070, 5457, 15820, 9841, 8993, 1]
  h := [7257, 1]
  a := [853, 1118, 6663, 4929, 482, 3705, 6223, 12312, 2504]
  b := [7244, 2679, 5227, 11567, 11880, 14535, 9012, 298, 13749]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD828361 : CertificateDedekindCriterionLists l 828361 where
  n := 2
  a' := [683869, 161834, 497523, 197115, 105286, 314123, 171847, 19659]
  b' := [20169, 38826, 77386, 347654, 190905, 128429, 275234, 666642, 273936]
  k := [59631, 432572, 185171, 141965, 206592, 249841, 439816, 396587, 1]
  f := [246539, 612147, 537890, 194506, 437036, 456512, 72750, 380725, 150825, 1]
  g := [324130, 804802, 707174, 255720, 574580, 600185, 95645, 500547, 198292, 1]
  h := [630066, 1]
  a := [503620, 11413, 787465, 244890, 226123, 790798, 385042, 255915, 295433]
  b := [433668, 29400, 375775, 569058, 473956, 244099, 4812, 567288, 532928]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![17, 16253, 828361]
  exp := ![1, 1, 1]
  pdgood := [17, 16253, 828361]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp17.out
    exact hp16253.out
    exact hp828361.out
  a := [-797161836049, -4113223118866, 4695737421001, 15062462562930, -10373251064776, -13603467350126, 7436964825125, 2568625898778, -1285594569840]
  b := [-205207761742, 302849631063, 1758050264939, -1238444154815, -3460881735930, 1710676779034, 2065424110406, -925042214087, -295430426973, 128559456984]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 16253 T_ofList CD16253
    exact satisfiesDedekindCriterion_of_certificate_lists T l 828361 T_ofList CD828361

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

end VoightMaximalOrderD10R271

namespace VoightMaximalOrderD10R273

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3914017628125, [-1, 0, 11, 2, -31, -7, 30, 5, -10, -1, 1], 1⟩
local notation "l" => [-1, 0, 11, 2, -31, -7, 30, 5, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -11, -2, 31, 7, -30, -5, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -11, -2, 31, 7, -30, -5, 10, 1], ![1, 1, -11, -13, 29, 38, -23, -35, 5, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -11, -2, 31, 7, -30, -5, 10, 1], ![1, 1, -11, -13, 29, 38, -23, -35, 5, 11], ![11, 1, -120, -33, 328, 106, -292, -78, 75, 16]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -11, -2, 31, 7, -30, -5, 10, 1], ![1, 1, -11, -13, 29, 38, -23, -35, 5, 11], ![11, 1, -120, -33, 328, 106, -292, -78, 75, 16], ![16, 11, -175, -152, 463, 440, -374, -372, 82, 91]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -11, -2, 31, 7, -30, -5, 10, 1], ![1, 1, -11, -13, 29, 38, -23, -35, 5, 11], ![11, 1, -120, -33, 328, 106, -292, -78, 75, 16], ![16, 11, -175, -152, 463, 440, -374, -372, 82, 91], ![91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -11, -2, 31, 7, -30, -5, 10, 1], ![1, 1, -11, -13, 29, 38, -23, -35, 5, 11], ![11, 1, -120, -33, 328, 106, -292, -78, 75, 16], ![16, 11, -175, -152, 463, 440, -374, -372, 82, 91], ![91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173], ![173, 91, -1887, -1336, 5006, 3880, -4090, -3155, 901, 711]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -11, -2, 31, 7, -30, -5, 10, 1], ![1, 1, -11, -13, 29, 38, -23, -35, 5, 11], ![11, 1, -120, -33, 328, 106, -292, -78, 75, 16], ![16, 11, -175, -152, 463, 440, -374, -372, 82, 91], ![91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173], ![173, 91, -1887, -1336, 5006, 3880, -4090, -3155, 901, 711], ![711, 173, -7730, -3309, 20705, 9983, -17450, -7645, 3955, 1612]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -11, -2, 31, 7, -30, -5, 10, 1], ![1, 1, -11, -13, 29, 38, -23, -35, 5, 11], ![11, 1, -120, -33, 328, 106, -292, -78, 75, 16], ![16, 11, -175, -152, 463, 440, -374, -372, 82, 91], ![91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173], ![173, 91, -1887, -1336, 5006, 3880, -4090, -3155, 901, 711], ![711, 173, -7730, -3309, 20705, 9983, -17450, -7645, 3955, 1612], ![1612, 711, -17559, -10954, 46663, 31989, -38377, -25510, 8475, 5567]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -11, -2, 31, 7, -30, -5, 10, 1], ![1, 1, -11, -13, 29, 38, -23, -35, 5, 11], ![11, 1, -120, -33, 328, 106, -292, -78, 75, 16], ![16, 11, -175, -152, 463, 440, -374, -372, 82, 91], ![91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173], ![173, 91, -1887, -1336, 5006, 3880, -4090, -3155, 901, 711], ![711, 173, -7730, -3309, 20705, 9983, -17450, -7645, 3955, 1612], ![1612, 711, -17559, -10954, 46663, 31989, -38377, -25510, 8475, 5567], ![5567, 1612, -60526, -28693, 161623, 85632, -135021, -66212, 30160, 14042]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-91, -16, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-91, -16, -11, -1, -1], [-173, -91, -16, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-91, -16, -11, -1, -1], [-173, -91, -16, -11, -1, -1], [-711, -173, -91, -16, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-91, -16, -11, -1, -1], [-173, -91, -16, -11, -1, -1], [-711, -173, -91, -16, -11, -1, -1], [-1612, -711, -173, -91, -16, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-91, -16, -11, -1, -1], [-173, -91, -16, -11, -1, -1], [-711, -173, -91, -16, -11, -1, -1], [-1612, -711, -173, -91, -16, -11, -1, -1], [-5567, -1612, -711, -173, -91, -16, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -11, -2, 31, 7, -30, -5, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -11, -2, 31, 7, -30, -5, 10, 1], [1, 1, -11, -13, 29, 38, -23, -35, 5, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -11, -2, 31, 7, -30, -5, 10, 1], [1, 1, -11, -13, 29, 38, -23, -35, 5, 11], [11, 1, -120, -33, 328, 106, -292, -78, 75, 16]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -11, -2, 31, 7, -30, -5, 10, 1], [1, 1, -11, -13, 29, 38, -23, -35, 5, 11], [11, 1, -120, -33, 328, 106, -292, -78, 75, 16], [16, 11, -175, -152, 463, 440, -374, -372, 82, 91]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -11, -2, 31, 7, -30, -5, 10, 1], [1, 1, -11, -13, 29, 38, -23, -35, 5, 11], [11, 1, -120, -33, 328, 106, -292, -78, 75, 16], [16, 11, -175, -152, 463, 440, -374, -372, 82, 91], [91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -11, -2, 31, 7, -30, -5, 10, 1], [1, 1, -11, -13, 29, 38, -23, -35, 5, 11], [11, 1, -120, -33, 328, 106, -292, -78, 75, 16], [16, 11, -175, -152, 463, 440, -374, -372, 82, 91], [91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173], [173, 91, -1887, -1336, 5006, 3880, -4090, -3155, 901, 711]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -11, -2, 31, 7, -30, -5, 10, 1], [1, 1, -11, -13, 29, 38, -23, -35, 5, 11], [11, 1, -120, -33, 328, 106, -292, -78, 75, 16], [16, 11, -175, -152, 463, 440, -374, -372, 82, 91], [91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173], [173, 91, -1887, -1336, 5006, 3880, -4090, -3155, 901, 711], [711, 173, -7730, -3309, 20705, 9983, -17450, -7645, 3955, 1612]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -11, -2, 31, 7, -30, -5, 10, 1], [1, 1, -11, -13, 29, 38, -23, -35, 5, 11], [11, 1, -120, -33, 328, 106, -292, -78, 75, 16], [16, 11, -175, -152, 463, 440, -374, -372, 82, 91], [91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173], [173, 91, -1887, -1336, 5006, 3880, -4090, -3155, 901, 711], [711, 173, -7730, -3309, 20705, 9983, -17450, -7645, 3955, 1612], [1612, 711, -17559, -10954, 46663, 31989, -38377, -25510, 8475, 5567]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -11, -2, 31, 7, -30, -5, 10, 1], [1, 1, -11, -13, 29, 38, -23, -35, 5, 11], [11, 1, -120, -33, 328, 106, -292, -78, 75, 16], [16, 11, -175, -152, 463, 440, -374, -372, 82, 91], [91, 16, -990, -357, 2669, 1100, -2290, -829, 538, 173], [173, 91, -1887, -1336, 5006, 3880, -4090, -3155, 901, 711], [711, 173, -7730, -3309, 20705, 9983, -17450, -7645, 3955, 1612], [1612, 711, -17559, -10954, 46663, 31989, -38377, -25510, 8475, 5567], [5567, 1612, -60526, -28693, 161623, 85632, -135021, -66212, 30160, 14042]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp941011 : Fact (Nat.Prime 941011) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3]
  b' := [0, 1, 4]
  k := [1]
  f := [1, 0, 1, 2, 11, 7, -1, 3, 4, 1]
  g := [2, 0, 4, 3, 2, 1]
  h := [2, 0, 4, 3, 2, 1]
  a := [1, 0, 3, 2]
  b := [0, 0, 3, 3, 2, 2, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [2, 5, 5, 7, 4, 8]
  b' := [9, 4, 3, 8, 7, 8, 2]
  k := [2, 1, 8, 6, 1]
  f := [3, 8, 3, 6, 13, 9, 9, 9, 4, 1]
  g := [8, 2, 2, 9, 4, 8, 8, 1]
  h := [4, 10, 2, 1]
  a := [8, 5, 9, 8, 1, 5, 2]
  b := [4, 7, 1, 8, 2, 10, 8, 3, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD941011 : CertificateDedekindCriterionLists l 941011 where
  n := 2
  a' := [152388, 232731, 603128, 665323, 532513, 499034, 65499, 794078]
  b' := [337423, 44732, 619307, 200849, 419762, 828, 260755, 819443, 434553]
  k := [573355, 767728, 170427, 343551, 630439, 561005, 589128, 248159, 1]
  f := [369153, 319178, 507655, 139465, 673548, 465969, 203368, 679191, 107719, 1]
  g := [425222, 367656, 584760, 160647, 775850, 536742, 234256, 782350, 124079, 1]
  h := [816931, 1]
  a := [310526, 605425, 480776, 47268, 481609, 267013, 629082, 175177, 345942]
  b := [581873, 739179, 569834, 190818, 72169, 903977, 480508, 195789, 595069]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 941011]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 941011]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp941011.out
  a := [-51755605, -5159117612, 6683212691, 22085584108, -22616877028, -15894668726, 13131849091, 3105687036, -1932205140]
  b := [-234505346, 393616201, 2159046770, -2716907453, -4203940045, 4164331384, 2141680527, -1685958913, -329890755, 193220514]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 941011 T_ofList CD941011

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

end VoightMaximalOrderD10R273

end TraceEuclidean
