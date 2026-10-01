import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk228
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

namespace VoightMaximalOrderD10R761

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7437873086464, [-1, 8, 10, -58, -70, 30, 49, -4, -12, 0, 1], 1⟩
local notation "l" => [-1, 8, 10, -58, -70, 30, 49, -4, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, -10, 58, 70, -30, -49, 4, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, -10, 58, 70, -30, -49, 4, 12, 0], ![0, 1, -8, -10, 58, 70, -30, -49, 4, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, -10, 58, 70, -30, -49, 4, 12, 0], ![0, 1, -8, -10, 58, 70, -30, -49, 4, 12], ![12, -96, -119, 688, 830, -302, -518, 18, 95, 4]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, -10, 58, 70, -30, -49, 4, 12, 0], ![0, 1, -8, -10, 58, 70, -30, -49, 4, 12], ![12, -96, -119, 688, 830, -302, -518, 18, 95, 4], ![4, -20, -136, 113, 968, 710, -498, -502, 66, 95]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, -10, 58, 70, -30, -49, 4, 12, 0], ![0, 1, -8, -10, 58, 70, -30, -49, 4, 12], ![12, -96, -119, 688, 830, -302, -518, 18, 95, 4], ![4, -20, -136, 113, 968, 710, -498, -502, 66, 95], ![95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, -10, 58, 70, -30, -49, 4, 12, 0], ![0, 1, -8, -10, 58, 70, -30, -49, 4, 12], ![12, -96, -119, 688, 830, -302, -518, 18, 95, 4], ![4, -20, -136, 113, 968, 710, -498, -502, 66, 95], ![95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66], ![66, -433, -1416, 2858, 9994, 4783, -5116, -3681, 674, 638]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, -10, 58, 70, -30, -49, 4, 12, 0], ![0, 1, -8, -10, 58, 70, -30, -49, 4, 12], ![12, -96, -119, 688, 830, -302, -518, 18, 95, 4], ![4, -20, -136, 113, 968, 710, -498, -502, 66, 95], ![95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66], ![66, -433, -1416, 2858, 9994, 4783, -5116, -3681, 674, 638], ![638, -5038, -6813, 35588, 47518, -9146, -26479, -2564, 3975, 674]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, -10, 58, 70, -30, -49, 4, 12, 0], ![0, 1, -8, -10, 58, 70, -30, -49, 4, 12], ![12, -96, -119, 688, 830, -302, -518, 18, 95, 4], ![4, -20, -136, 113, 968, 710, -498, -502, 66, 95], ![95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66], ![66, -433, -1416, 2858, 9994, 4783, -5116, -3681, 674, 638], ![638, -5038, -6813, 35588, 47518, -9146, -26479, -2564, 3975, 674], ![674, -4754, -11778, 32279, 82768, 27298, -42172, -23783, 5524, 3975]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, -10, 58, 70, -30, -49, 4, 12, 0], ![0, 1, -8, -10, 58, 70, -30, -49, 4, 12], ![12, -96, -119, 688, 830, -302, -518, 18, 95, 4], ![4, -20, -136, 113, 968, 710, -498, -502, 66, 95], ![95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66], ![66, -433, -1416, 2858, 9994, 4783, -5116, -3681, 674, 638], ![638, -5038, -6813, 35588, 47518, -9146, -26479, -2564, 3975, 674], ![674, -4754, -11778, 32279, 82768, 27298, -42172, -23783, 5524, 3975], ![3975, -31126, -44504, 218772, 310529, -36482, -167477, -26272, 23917, 5524]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-95, -4, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-95, -4, -12, 0, -1], [-66, -95, -4, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-95, -4, -12, 0, -1], [-66, -95, -4, -12, 0, -1], [-638, -66, -95, -4, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-95, -4, -12, 0, -1], [-66, -95, -4, -12, 0, -1], [-638, -66, -95, -4, -12, 0, -1], [-674, -638, -66, -95, -4, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-95, -4, -12, 0, -1], [-66, -95, -4, -12, 0, -1], [-638, -66, -95, -4, -12, 0, -1], [-674, -638, -66, -95, -4, -12, 0, -1], [-3975, -674, -638, -66, -95, -4, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -8, -10, 58, 70, -30, -49, 4, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -8, -10, 58, 70, -30, -49, 4, 12, 0], [0, 1, -8, -10, 58, 70, -30, -49, 4, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -8, -10, 58, 70, -30, -49, 4, 12, 0], [0, 1, -8, -10, 58, 70, -30, -49, 4, 12], [12, -96, -119, 688, 830, -302, -518, 18, 95, 4]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -8, -10, 58, 70, -30, -49, 4, 12, 0], [0, 1, -8, -10, 58, 70, -30, -49, 4, 12], [12, -96, -119, 688, 830, -302, -518, 18, 95, 4], [4, -20, -136, 113, 968, 710, -498, -502, 66, 95]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -8, -10, 58, 70, -30, -49, 4, 12, 0], [0, 1, -8, -10, 58, 70, -30, -49, 4, 12], [12, -96, -119, 688, 830, -302, -518, 18, 95, 4], [4, -20, -136, 113, 968, 710, -498, -502, 66, 95], [95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -8, -10, 58, 70, -30, -49, 4, 12, 0], [0, 1, -8, -10, 58, 70, -30, -49, 4, 12], [12, -96, -119, 688, 830, -302, -518, 18, 95, 4], [4, -20, -136, 113, 968, 710, -498, -502, 66, 95], [95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66], [66, -433, -1416, 2858, 9994, 4783, -5116, -3681, 674, 638]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -8, -10, 58, 70, -30, -49, 4, 12, 0], [0, 1, -8, -10, 58, 70, -30, -49, 4, 12], [12, -96, -119, 688, 830, -302, -518, 18, 95, 4], [4, -20, -136, 113, 968, 710, -498, -502, 66, 95], [95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66], [66, -433, -1416, 2858, 9994, 4783, -5116, -3681, 674, 638], [638, -5038, -6813, 35588, 47518, -9146, -26479, -2564, 3975, 674]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -8, -10, 58, 70, -30, -49, 4, 12, 0], [0, 1, -8, -10, 58, 70, -30, -49, 4, 12], [12, -96, -119, 688, 830, -302, -518, 18, 95, 4], [4, -20, -136, 113, 968, 710, -498, -502, 66, 95], [95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66], [66, -433, -1416, 2858, 9994, 4783, -5116, -3681, 674, 638], [638, -5038, -6813, 35588, 47518, -9146, -26479, -2564, 3975, 674], [674, -4754, -11778, 32279, 82768, 27298, -42172, -23783, 5524, 3975]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -8, -10, 58, 70, -30, -49, 4, 12, 0], [0, 1, -8, -10, 58, 70, -30, -49, 4, 12], [12, -96, -119, 688, 830, -302, -518, 18, 95, 4], [4, -20, -136, 113, 968, 710, -498, -502, 66, 95], [95, -756, -970, 5374, 6763, -1882, -3945, -118, 638, 66], [66, -433, -1416, 2858, 9994, 4783, -5116, -3681, 674, 638], [638, -5038, -6813, 35588, 47518, -9146, -26479, -2564, 3975, 674], [674, -4754, -11778, 32279, 82768, 27298, -42172, -23783, 5524, 3975], [3975, -31126, -44504, 218772, 310529, -36482, -167477, -26272, 23917, 5524]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp9868951 : Fact (Nat.Prime 9868951) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [0, 1]
  k := [1]
  f := [1, -4, -5, 30, 35, -14, -24, 2, 7]
  g := [1, 0, 0, 1, 0, 1]
  h := [1, 0, 0, 1, 0, 1]
  a := [1, 1, 1, 1, 1]
  b := [0, 1, 0, 0, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [0, 21, 20, 9, 13, 20, 22, 2]
  b' := [16, 17, 12, 22, 22, 10, 5, 12, 10]
  k := [20, 20, 12, 12, 0, 8, 12, 3, 1]
  f := [7, 6, 1, 10, 9, 4, 4, 9, 7, 1]
  g := [16, 13, 2, 17, 12, 11, 13, 19, 13, 1]
  h := [10, 1]
  a := [11, 0, 1, 15, 12, 7, 9, 16, 18]
  b := [1, 8, 21, 3, 16, 9, 13, 0, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9868951 : CertificateDedekindCriterionLists l 9868951 where
  n := 2
  a' := [8494179, 1264902, 791050, 438341, 1223642, 292026, 9407770, 4914155]
  b' := [294854, 3600220, 5948580, 6668377, 7125513, 8889435, 3061602, 7022813, 1647083]
  k := [524549, 2241170, 6307059, 103872, 1357064, 7288440, 2697751, 9685583, 1]
  f := [12563, 77991, 66821, 57319, 30606, 74487, 22039, 69477, 90833, 1]
  g := [1352293, 8395009, 7192583, 6169792, 3294391, 8017814, 2372211, 7478543, 9777267, 1]
  h := [91684, 1]
  a := [4629229, 9423771, 896431, 8713755, 8978004, 489583, 6587347, 3795838, 7461033]
  b := [9760402, 4317216, 1921833, 801308, 3785822, 543815, 3705341, 7916787, 2407918]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 23, 9868951]
  exp := ![2, 1, 1]
  pdgood := [2, 23, 9868951]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp23.out
    exact hp9868951.out
  a := [-800471804, 3465537020, 31279905846, 15506596286, -40863929536, -15788858614, 17029274388, 3214755980, -2322661530]
  b := [13433961, 1200079029, -1262967955, -9747595761, -2943139048, 7760193958, 2071707913, -2260366206, -321475598, 232266153]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9868951 T_ofList CD9868951

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

end VoightMaximalOrderD10R761

namespace VoightMaximalOrderD10R762

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7439310496661, [1, 9, 12, -36, -42, 35, 43, -6, -12, 0, 1], 1⟩
local notation "l" => [1, 9, 12, -36, -42, 35, 43, -6, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -12, 36, 42, -35, -43, 6, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], ![0, -1, -9, -12, 36, 42, -35, -43, 6, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], ![0, -1, -9, -12, 36, 42, -35, -43, 6, 12], ![-12, -108, -145, 423, 492, -384, -474, 37, 101, 6]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], ![0, -1, -9, -12, 36, 42, -35, -43, 6, 12], ![-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], ![-6, -66, -180, 71, 675, 282, -642, -438, 109, 101]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], ![0, -1, -9, -12, 36, 42, -35, -43, 6, 12], ![-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], ![-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], ![-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], ![0, -1, -9, -12, 36, 42, -35, -43, 6, 12], ![-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], ![-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], ![-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109], ![-109, -1082, -2223, 2646, 8034, 498, -7547, -3407, 1272, 774]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], ![0, -1, -9, -12, 36, 42, -35, -43, 6, 12], ![-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], ![-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], ![-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109], ![-109, -1082, -2223, 2646, 8034, 498, -7547, -3407, 1272, 774], ![-774, -7075, -10370, 25641, 35154, -19056, -32784, -2903, 5881, 1272]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], ![0, -1, -9, -12, 36, 42, -35, -43, 6, 12], ![-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], ![-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], ![-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109], ![-109, -1082, -2223, 2646, 8034, 498, -7547, -3407, 1272, 774], ![-774, -7075, -10370, 25641, 35154, -19056, -32784, -2903, 5881, 1272], ![-1272, -12222, -22339, 35422, 79065, -9366, -73752, -25152, 12361, 5881]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], ![0, -1, -9, -12, 36, 42, -35, -43, 6, 12], ![-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], ![-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], ![-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109], ![-109, -1082, -2223, 2646, 8034, 498, -7547, -3407, 1272, 774], ![-774, -7075, -10370, 25641, 35154, -19056, -32784, -2903, 5881, 1272], ![-1272, -12222, -22339, 35422, 79065, -9366, -73752, -25152, 12361, 5881], ![-5881, -54201, -82794, 189377, 282424, -126770, -262249, -38466, 45420, 12361]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-101, -6, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-101, -6, -12, 0, -1], [-109, -101, -6, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-101, -6, -12, 0, -1], [-109, -101, -6, -12, 0, -1], [-774, -109, -101, -6, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-101, -6, -12, 0, -1], [-109, -101, -6, -12, 0, -1], [-774, -109, -101, -6, -12, 0, -1], [-1272, -774, -109, -101, -6, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-6, -12, 0, -1], [-101, -6, -12, 0, -1], [-109, -101, -6, -12, 0, -1], [-774, -109, -101, -6, -12, 0, -1], [-1272, -774, -109, -101, -6, -12, 0, -1], [-5881, -1272, -774, -109, -101, -6, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -12, 36, 42, -35, -43, 6, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], [0, -1, -9, -12, 36, 42, -35, -43, 6, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], [0, -1, -9, -12, 36, 42, -35, -43, 6, 12], [-12, -108, -145, 423, 492, -384, -474, 37, 101, 6]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], [0, -1, -9, -12, 36, 42, -35, -43, 6, 12], [-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], [-6, -66, -180, 71, 675, 282, -642, -438, 109, 101]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], [0, -1, -9, -12, 36, 42, -35, -43, 6, 12], [-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], [-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], [-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], [0, -1, -9, -12, 36, 42, -35, -43, 6, 12], [-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], [-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], [-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109], [-109, -1082, -2223, 2646, 8034, 498, -7547, -3407, 1272, 774]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], [0, -1, -9, -12, 36, 42, -35, -43, 6, 12], [-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], [-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], [-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109], [-109, -1082, -2223, 2646, 8034, 498, -7547, -3407, 1272, 774], [-774, -7075, -10370, 25641, 35154, -19056, -32784, -2903, 5881, 1272]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], [0, -1, -9, -12, 36, 42, -35, -43, 6, 12], [-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], [-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], [-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109], [-109, -1082, -2223, 2646, 8034, 498, -7547, -3407, 1272, 774], [-774, -7075, -10370, 25641, 35154, -19056, -32784, -2903, 5881, 1272], [-1272, -12222, -22339, 35422, 79065, -9366, -73752, -25152, 12361, 5881]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -9, -12, 36, 42, -35, -43, 6, 12, 0], [0, -1, -9, -12, 36, 42, -35, -43, 6, 12], [-12, -108, -145, 423, 492, -384, -474, 37, 101, 6], [-6, -66, -180, 71, 675, 282, -642, -438, 109, 101], [-101, -915, -1278, 3456, 4313, -2860, -4061, -36, 774, 109], [-109, -1082, -2223, 2646, 8034, 498, -7547, -3407, 1272, 774], [-774, -7075, -10370, 25641, 35154, -19056, -32784, -2903, 5881, 1272], [-1272, -12222, -22339, 35422, 79065, -9366, -73752, -25152, 12361, 5881], [-5881, -54201, -82794, 189377, 282424, -126770, -262249, -38466, 45420, 12361]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp1997 : Fact (Nat.Prime 1997) := fact_iff.2 (by norm_num)
instance hp10319233 : Fact (Nat.Prime 10319233) := fact_iff.2 (by norm_num)

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 3
  a' := [4, 10, 10, 13, 8, 18, 4]
  b' := [17, 17, 9, 4, 13, 1, 16, 9]
  k := [7, 0, 18, 1, 17, 0, 1, 0, 9, 14, 18, 10, 10, 17, 1]
  f := [8, 10, 18, 22, 14, 11, 3, 12, 6, 1]
  g := [9, 8, 17, 15, 6, 11, 1, 12, 1]
  h := [17, 7, 1]
  a := [0, 9, 9, 14, 3, 5, 8, 17]
  b := [17, 17, 15, 4, 18, 8, 0, 18, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1997 : CertificateDedekindCriterionLists l 1997 where
  n := 2
  a' := [1266, 1829, 612, 88, 1373, 1507, 1883, 47]
  b' := [205, 163, 479, 1932, 1269, 616, 1723, 180, 1548]
  k := [1638, 1473, 1307, 1942, 347, 1509, 255, 358, 1]
  f := [325, 1434, 1065, 1063, 1581, 1665, 1635, 71, 163, 1]
  g := [357, 1575, 1169, 1167, 1736, 1828, 1795, 77, 179, 1]
  h := [1818, 1]
  a := [1163, 1136, 829, 1809, 1663, 937, 328, 1029, 1957]
  b := [983, 955, 14, 391, 1307, 1938, 651, 328, 40]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD10319233 : CertificateDedekindCriterionLists l 10319233 where
  n := 2
  a' := [1538896, 3576292, 1933879, 6801608, 4838357, 10034743, 1127831, 2642876]
  b' := [9220321, 5377923, 6635526, 5938031, 9756997, 9898095, 7169987, 9250523, 1999510]
  k := [9383233, 2894866, 8077296, 1729644, 9424778, 847239, 4527783, 3936536, 1]
  f := [5001653, 4017522, 3800341, 2153664, 4708600, 3290077, 5228526, 1221382, 1592845, 1]
  g := [6180510, 4964425, 4696056, 2661268, 5818386, 4065526, 6460855, 1509253, 1968268, 1]
  h := [8350965, 1]
  a := [5361876, 7772163, 8252556, 4931256, 3721380, 2948460, 5705652, 6934646, 8201358]
  b := [10313738, 8144563, 6800924, 1288121, 2203057, 4371191, 1990049, 1301112, 2117875]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![19, 1997, 10319233]
  exp := ![1, 1, 1]
  pdgood := [19, 1997, 10319233]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp19.out
    exact hp1997.out
    exact hp10319233.out
  a := [-5009656762021, 485004665334, 45637699246176, 9445167341424, -83924237776876, -21649414571062, 36829910939868, 5412733753980, -4641769212480]
  b := [600133268860, 3355411971135, -622483817810, -14245074032808, -926740193202, 15495101258884, 2628479099815, -4797015704982, -541273375398, 464176921248]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1997 T_ofList CD1997
    exact satisfiesDedekindCriterion_of_certificate_lists T l 10319233 T_ofList CD10319233

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

end VoightMaximalOrderD10R762

namespace VoightMaximalOrderD10R764

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7457817050000, [1, -5, -6, 28, 10, -42, -2, 23, -3, -4, 1], 1⟩
local notation "l" => [1, -5, -6, 28, 10, -42, -2, 23, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -28, -10, 42, 2, -23, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], ![-4, 19, 29, -106, -68, 158, 50, -90, -11, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], ![-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], ![-19, 91, 133, -503, -296, 730, 196, -387, -33, 65]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], ![-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], ![-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], ![-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], ![-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], ![-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], ![-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], ![-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], ![-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], ![-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], ![-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], ![-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716], ![-716, 3353, 5366, -18380, -13035, 26115, 9813, -13580, -2213, 2246]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], ![-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], ![-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], ![-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], ![-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716], ![-716, 3353, 5366, -18380, -13035, 26115, 9813, -13580, -2213, 2246], ![-2246, 10514, 16829, -57522, -40840, 81297, 30607, -41845, -6842, 6771]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], ![-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], ![-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], ![-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], ![-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716], ![-716, 3353, 5366, -18380, -13035, 26115, 9813, -13580, -2213, 2246], ![-2246, 10514, 16829, -57522, -40840, 81297, 30607, -41845, -6842, 6771], ![-6771, 31609, 51140, -172759, -125232, 243542, 94839, -125126, -21532, 20242]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], ![-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], ![-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], ![-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], ![-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716], ![-716, 3353, 5366, -18380, -13035, 26115, 9813, -13580, -2213, 2246], ![-2246, 10514, 16829, -57522, -40840, 81297, 30607, -41845, -6842, 6771], ![-6771, 31609, 51140, -172759, -125232, 243542, 94839, -125126, -21532, 20242], ![-20242, 94439, 153061, -515636, -375179, 724932, 284026, -370727, -64400, 59436]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1], [-716, -227, -65, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1], [-716, -227, -65, -19, -4, -1], [-2246, -716, -227, -65, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1], [-716, -227, -65, -19, -4, -1], [-2246, -716, -227, -65, -19, -4, -1], [-6771, -2246, -716, -227, -65, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1], [-716, -227, -65, -19, -4, -1], [-2246, -716, -227, -65, -19, -4, -1], [-6771, -2246, -716, -227, -65, -19, -4, -1], [-20242, -6771, -2246, -716, -227, -65, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -28, -10, 42, 2, -23, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], [-4, 19, 29, -106, -68, 158, 50, -90, -11, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], [-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], [-19, 91, 133, -503, -296, 730, 196, -387, -33, 65]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], [-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], [-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], [-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], [-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], [-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], [-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], [-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], [-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], [-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], [-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], [-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716], [-716, 3353, 5366, -18380, -13035, 26115, 9813, -13580, -2213, 2246]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], [-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], [-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], [-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], [-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716], [-716, 3353, 5366, -18380, -13035, 26115, 9813, -13580, -2213, 2246], [-2246, 10514, 16829, -57522, -40840, 81297, 30607, -41845, -6842, 6771]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], [-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], [-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], [-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], [-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716], [-716, 3353, 5366, -18380, -13035, 26115, 9813, -13580, -2213, 2246], [-2246, 10514, 16829, -57522, -40840, 81297, 30607, -41845, -6842, 6771], [-6771, 31609, 51140, -172759, -125232, 243542, 94839, -125126, -21532, 20242]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -28, -10, 42, 2, -23, 3, 4], [-4, 19, 29, -106, -68, 158, 50, -90, -11, 19], [-19, 91, 133, -503, -296, 730, 196, -387, -33, 65], [-65, 306, 481, -1687, -1153, 2434, 860, -1299, -192, 227], [-227, 1070, 1668, -5875, -3957, 8381, 2888, -4361, -618, 716], [-716, 3353, 5366, -18380, -13035, 26115, 9813, -13580, -2213, 2246], [-2246, 10514, 16829, -57522, -40840, 81297, 30607, -41845, -6842, 6771], [-6771, 31609, 51140, -172759, -125232, 243542, 94839, -125126, -21532, 20242], [-20242, 94439, 153061, -515636, -375179, 724932, 284026, -370727, -64400, 59436]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp149156341 : Fact (Nat.Prime 149156341) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 3
  a' := [1]
  b' := [0, 1, 1, 0, 1]
  k := [1, 0, 0, 0, 0, 0, 1, 0, 1]
  f := [0, 3, 4, -13, -4, 22, 2, -11, 2, 2]
  g := [1, 1, 1, 1, 0, 0, 1]
  h := [1, 0, 1, 0, 1]
  a := [0, 1, 0, 0, 0, 1]
  b := [1, 1, 1, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 1]
  b' := [1, 4, 1, 2]
  k := [1]
  f := [0, 1, 2, -4, 0, 12, 6, 1, 4, 2]
  g := [1, 0, 2, 4, 3, 1]
  h := [1, 0, 2, 4, 3, 1]
  a := [2, 3, 3, 4, 3]
  b := [1, 3, 1, 4, 0, 0, 0, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD149156341 : CertificateDedekindCriterionLists l 149156341 where
  n := 2
  a' := [140802149, 112050698, 51505579, 103703819, 104153975, 88451531, 60036863, 55258971]
  b' := [92289231, 32962816, 116971338, 81286992, 107502670, 63715694, 57404416, 145140353, 93297675]
  k := [53365946, 94117849, 78265619, 43640496, 125688070, 20879701, 43467668, 62793572, 1]
  f := [97848985, 57420204, 11002454, 4551644, 59714346, 96835349, 26785114, 17641958, 24787892, 1]
  g := [123937262, 72729449, 13935903, 5765193, 75635251, 122653372, 33926500, 22345617, 31396784, 1]
  h := [117759553, 1]
  a := [56541685, 12990261, 15474669, 148956515, 118138062, 125930127, 52978552, 125044977, 19921139]
  b := [23649044, 30561210, 50866319, 46300181, 122137736, 120101932, 86426004, 106987177, 129235202]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 5, 149156341]
  exp := ![1, 1, 1]
  pdgood := [2, 5, 149156341]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp149156341.out
  a := [-4596808500, -23834458644, 46338092319, 109007425252, -90194424087, -116856906192, 51551750668, 28607365602, -10967984820]
  b := [-1217674382, 2752335288, 11555712999, -12913257911, -27029802541, 14150557251, 18043758160, -6248349346, -3299455953, 1096798482]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 149156341 T_ofList CD149156341

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

end VoightMaximalOrderD10R764

namespace VoightMaximalOrderD10R775

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7517433528125, [-31, -45, 102, 138, -87, -104, 40, 30, -10, -3, 1], 1⟩
local notation "l" => [-31, -45, 102, 138, -87, -104, 40, 30, -10, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![31, 45, -102, -138, 87, 104, -40, -30, 10, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![31, 45, -102, -138, 87, 104, -40, -30, 10, 3], ![93, 166, -261, -516, 123, 399, -16, -130, 0, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![31, 45, -102, -138, 87, 104, -40, -30, 10, 3], ![93, 166, -261, -516, 123, 399, -16, -130, 0, 19], ![589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![31, 45, -102, -138, 87, 104, -40, -30, 10, 3], ![93, 166, -261, -516, 123, 399, -16, -130, 0, 19], ![589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], ![1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![31, 45, -102, -138, 87, 104, -40, -30, 10, 3], ![93, 166, -261, -516, 123, 399, -16, -130, 0, 19], ![589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], ![1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], ![7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![31, 45, -102, -138, 87, 104, -40, -30, 10, 3], ![93, 166, -261, -516, 123, 399, -16, -130, 0, 19], ![589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], ![1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], ![7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677], ![20987, 37626, -56892, -113834, 22155, 80867, -980, -22485, -341, 2270]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![31, 45, -102, -138, 87, 104, -40, -30, 10, 3], ![93, 166, -261, -516, 123, 399, -16, -130, 0, 19], ![589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], ![1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], ![7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677], ![20987, 37626, -56892, -113834, 22155, 80867, -980, -22485, -341, 2270], ![70370, 123137, -193914, -370152, 83656, 258235, -9933, -69080, 215, 6469]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![31, 45, -102, -138, 87, 104, -40, -30, 10, 3], ![93, 166, -261, -516, 123, 399, -16, -130, 0, 19], ![589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], ![1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], ![7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677], ![20987, 37626, -56892, -113834, 22155, 80867, -980, -22485, -341, 2270], ![70370, 123137, -193914, -370152, 83656, 258235, -9933, -69080, 215, 6469], ![200539, 361475, -536701, -1086636, 192651, 756432, -525, -204003, -4390, 19622]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![31, 45, -102, -138, 87, 104, -40, -30, 10, 3], ![93, 166, -261, -516, 123, 399, -16, -130, 0, 19], ![589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], ![1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], ![7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677], ![20987, 37626, -56892, -113834, 22155, 80867, -980, -22485, -341, 2270], ![70370, 123137, -193914, -370152, 83656, 258235, -9933, -69080, 215, 6469], ![200539, 361475, -536701, -1086636, 192651, 756432, -525, -204003, -4390, 19622], ![608282, 1083529, -1639969, -3244537, 620478, 2233339, -28448, -589185, -7783, 54476]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-19, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-19, -3, -1], [-57, -19, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-19, -3, -1], [-57, -19, -3, -1], [-231, -57, -19, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-19, -3, -1], [-57, -19, -3, -1], [-231, -57, -19, -3, -1], [-677, -231, -57, -19, -3, -1]], ![[], [], [], [-1], [-3, -1], [-19, -3, -1], [-57, -19, -3, -1], [-231, -57, -19, -3, -1], [-677, -231, -57, -19, -3, -1], [-2270, -677, -231, -57, -19, -3, -1]], ![[], [], [-1], [-3, -1], [-19, -3, -1], [-57, -19, -3, -1], [-231, -57, -19, -3, -1], [-677, -231, -57, -19, -3, -1], [-2270, -677, -231, -57, -19, -3, -1], [-6469, -2270, -677, -231, -57, -19, -3, -1]], ![[], [-1], [-3, -1], [-19, -3, -1], [-57, -19, -3, -1], [-231, -57, -19, -3, -1], [-677, -231, -57, -19, -3, -1], [-2270, -677, -231, -57, -19, -3, -1], [-6469, -2270, -677, -231, -57, -19, -3, -1], [-19622, -6469, -2270, -677, -231, -57, -19, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [31, 45, -102, -138, 87, 104, -40, -30, 10, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [31, 45, -102, -138, 87, 104, -40, -30, 10, 3], [93, 166, -261, -516, 123, 399, -16, -130, 0, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [31, 45, -102, -138, 87, 104, -40, -30, 10, 3], [93, 166, -261, -516, 123, 399, -16, -130, 0, 19], [589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [31, 45, -102, -138, 87, 104, -40, -30, 10, 3], [93, 166, -261, -516, 123, 399, -16, -130, 0, 19], [589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], [1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [31, 45, -102, -138, 87, 104, -40, -30, 10, 3], [93, 166, -261, -516, 123, 399, -16, -130, 0, 19], [589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], [1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], [7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [31, 45, -102, -138, 87, 104, -40, -30, 10, 3], [93, 166, -261, -516, 123, 399, -16, -130, 0, 19], [589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], [1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], [7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677], [20987, 37626, -56892, -113834, 22155, 80867, -980, -22485, -341, 2270]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [31, 45, -102, -138, 87, 104, -40, -30, 10, 3], [93, 166, -261, -516, 123, 399, -16, -130, 0, 19], [589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], [1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], [7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677], [20987, 37626, -56892, -113834, 22155, 80867, -980, -22485, -341, 2270], [70370, 123137, -193914, -370152, 83656, 258235, -9933, -69080, 215, 6469]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [31, 45, -102, -138, 87, 104, -40, -30, 10, 3], [93, 166, -261, -516, 123, 399, -16, -130, 0, 19], [589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], [1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], [7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677], [20987, 37626, -56892, -113834, 22155, 80867, -980, -22485, -341, 2270], [70370, 123137, -193914, -370152, 83656, 258235, -9933, -69080, 215, 6469], [200539, 361475, -536701, -1086636, 192651, 756432, -525, -204003, -4390, 19622]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [31, 45, -102, -138, 87, 104, -40, -30, 10, 3], [93, 166, -261, -516, 123, 399, -16, -130, 0, 19], [589, 948, -1772, -2883, 1137, 2099, -361, -586, 60, 57], [1767, 3154, -4866, -9638, 2076, 7065, -181, -2071, -16, 231], [7161, 12162, -20408, -36744, 10459, 26100, -2175, -7111, 239, 677], [20987, 37626, -56892, -113834, 22155, 80867, -980, -22485, -341, 2270], [70370, 123137, -193914, -370152, 83656, 258235, -9933, -69080, 215, 6469], [200539, 361475, -536701, -1086636, 192651, 756432, -525, -204003, -4390, 19622], [608282, 1083529, -1639969, -3244537, 620478, 2233339, -28448, -589185, -7783, 54476]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp251 : Fact (Nat.Prime 251) := fact_iff.2 (by norm_num)
instance hp9583979 : Fact (Nat.Prime 9583979) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3]
  b' := [0, 1, 3]
  k := [1]
  f := [7, 9, -18, -26, 20, 24, -6, -4, 3, 1]
  g := [2, 0, 3, 2, 1, 1]
  h := [2, 0, 3, 2, 1, 1]
  a := [1, 2, 0, 1, 2]
  b := [2, 1, 2, 4, 2, 1, 4, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD251 : CertificateDedekindCriterionLists l 251 where
  n := 2
  a' := [153, 241, 250, 121, 132, 177, 161, 48]
  b' := [37, 185, 41, 149, 36, 171, 171, 240, 162]
  k := [248, 197, 242, 234, 35, 4, 10, 168, 1]
  f := [21, 16, 14, 10, 21, 32, 25, 33, 34, 1]
  g := [131, 96, 88, 64, 128, 195, 153, 204, 208, 1]
  h := [40, 1]
  a := [152, 224, 202, 16, 161, 34, 225, 194, 191]
  b := [150, 146, 247, 152, 98, 27, 47, 159, 60]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9583979 : CertificateDedekindCriterionLists l 9583979 where
  n := 2
  a' := [7389438, 3717012, 6980614, 9094451, 184884, 883722, 1362385, 7145740]
  b' := [4992923, 6662294, 8272430, 9071895, 791582, 1176823, 1900649, 5837835, 1335802]
  k := [896897, 3718089, 8977348, 4413730, 4207411, 9086513, 7539543, 1356346, 1]
  f := [3832534, 3718633, 3563813, 3325194, 929886, 3141362, 3416141, 102018, 2348005, 1]
  g := [8928677, 8663319, 8302634, 7746722, 2166359, 7318449, 7958602, 237670, 5470161, 1]
  h := [4113815, 1]
  a := [1048398, 5731333, 1329727, 1503060, 8404716, 7356592, 6728663, 5874511, 7472050]
  b := [6567492, 2332726, 4999965, 8441258, 9249102, 1414895, 9147393, 9462544, 2111929]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 251, 9583979]
  exp := ![1, 1, 1]
  pdgood := [5, 251, 9583979]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp251.out
    exact hp9583979.out
  a := [-8372418755, 19956579882, 155860912956, 40261378590, -202238567401, -50835922028, 77695406345, 10707744000, -9603424500]
  b := [5500379728, 19559607381, -7031199916, -58499687378, -14976415282, 38855964359, 9475472459, -10146870599, -1358877135, 960342450]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 251 T_ofList CD251
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9583979 T_ofList CD9583979

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

end VoightMaximalOrderD10R775

end TraceEuclidean
