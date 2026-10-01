import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk225
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

namespace VoightMaximalOrderD10R698

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7019580190625, [1, -14, 3, 50, -14, -57, 16, 23, -7, -3, 1], 1⟩
local notation "l" => [1, -14, 3, 50, -14, -57, 16, 23, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -3, -50, 14, 57, -16, -23, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], ![-3, 41, 5, -153, -8, 185, 9, -85, -2, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], ![-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], ![-16, 221, -7, -795, 71, 904, -71, -359, 27, 46]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], ![-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], ![-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], ![-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], ![-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], ![-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], ![-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], ![-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], ![-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], ![-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], ![-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], ![-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458], ![-458, 6247, 890, -22767, -1755, 26109, 1926, -10481, -421, 1400]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], ![-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], ![-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], ![-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], ![-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458], ![-458, 6247, 890, -22767, -1755, 26109, 1926, -10481, -421, 1400], ![-1400, 19142, 2047, -69110, -3167, 78045, 3709, -30274, -681, 3779]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], ![-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], ![-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], ![-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], ![-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458], ![-458, 6247, 890, -22767, -1755, 26109, 1926, -10481, -421, 1400], ![-1400, 19142, 2047, -69110, -3167, 78045, 3709, -30274, -681, 3779], ![-3779, 51506, 7805, -186903, -16204, 212236, 17581, -83208, -3821, 10656]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], ![-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], ![-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], ![-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], ![-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458], ![-458, 6247, 890, -22767, -1755, 26109, 1926, -10481, -421, 1400], ![-1400, 19142, 2047, -69110, -3167, 78045, 3709, -30274, -681, 3779], ![-3779, 51506, 7805, -186903, -16204, 212236, 17581, -83208, -3821, 10656], ![-10656, 145405, 19538, -524995, -37719, 591188, 41740, -227507, -8616, 28147]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1], [-458, -165, -46, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1], [-458, -165, -46, -16, -3, -1], [-1400, -458, -165, -46, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1], [-458, -165, -46, -16, -3, -1], [-1400, -458, -165, -46, -16, -3, -1], [-3779, -1400, -458, -165, -46, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1], [-458, -165, -46, -16, -3, -1], [-1400, -458, -165, -46, -16, -3, -1], [-3779, -1400, -458, -165, -46, -16, -3, -1], [-10656, -3779, -1400, -458, -165, -46, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -3, -50, 14, 57, -16, -23, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], [-3, 41, 5, -153, -8, 185, 9, -85, -2, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], [-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], [-16, 221, -7, -795, 71, 904, -71, -359, 27, 46]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], [-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], [-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], [-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], [-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], [-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], [-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], [-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], [-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], [-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], [-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], [-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458], [-458, 6247, 890, -22767, -1755, 26109, 1926, -10481, -421, 1400]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], [-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], [-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], [-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], [-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458], [-458, 6247, 890, -22767, -1755, 26109, 1926, -10481, -421, 1400], [-1400, 19142, 2047, -69110, -3167, 78045, 3709, -30274, -681, 3779]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], [-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], [-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], [-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], [-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458], [-458, 6247, 890, -22767, -1755, 26109, 1926, -10481, -421, 1400], [-1400, 19142, 2047, -69110, -3167, 78045, 3709, -30274, -681, 3779], [-3779, 51506, 7805, -186903, -16204, 212236, 17581, -83208, -3821, 10656]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -3, -50, 14, 57, -16, -23, 7, 3], [-3, 41, 5, -153, -8, 185, 9, -85, -2, 16], [-16, 221, -7, -795, 71, 904, -71, -359, 27, 46], [-46, 628, 83, -2307, -151, 2693, 168, -1129, -37, 165], [-165, 2264, 133, -8167, 3, 9254, 53, -3627, 26, 458], [-458, 6247, 890, -22767, -1755, 26109, 1926, -10481, -421, 1400], [-1400, 19142, 2047, -69110, -3167, 78045, 3709, -30274, -681, 3779], [-3779, 51506, 7805, -186903, -16204, 212236, 17581, -83208, -3821, 10656], [-10656, 145405, 19538, -524995, -37719, 591188, 41740, -227507, -8616, 28147]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2246265661 : Fact (Nat.Prime 2246265661) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 2]
  b' := [1, 2, 4, 2]
  k := [1]
  f := [3, 6, 5, -6, 7, 15, -1, -3, 2, 1]
  g := [4, 2, 3, 1, 1, 1]
  h := [4, 2, 3, 1, 1, 1]
  a := [4, 0, 3, 4, 3]
  b := [1, 1, 4, 3, 1, 2, 3, 3, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2246265661 : CertificateDedekindCriterionLists l 2246265661 where
  n := 2
  a' := [2241269593, 1138142393, 740956034, 1293529079, 601703751, 125800115, 969564391, 1702161761]
  b' := [141935488, 673573036, 1539916158, 604344658, 277376576, 945682683, 751685079, 1802376658, 1807551503]
  k := [1103949903, 2168232904, 1895055916, 819253560, 1270867342, 220096885, 1463985362, 994717185, 1]
  f := [458696070, 1463272347, 1301917072, 273344827, 1457790909, 1573480457, 882291544, 1741616811, 387235567, 1]
  g := [589141213, 1879401420, 1672159525, 351079316, 1872361157, 2020950789, 1133199833, 2236902183, 497358591, 1]
  h := [1748907067, 1]
  a := [1897182197, 2083744376, 337488277, 1371245991, 659750668, 1610594960, 1710596757, 1061943503, 909104888]
  b := [1501260674, 550134162, 481262116, 1427693454, 1315063360, 1697886718, 885621395, 2114492704, 1337160773]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 2246265661]
  exp := ![1, 1]
  pdgood := [5, 2246265661]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2246265661.out
  a := [86024457191, -174489855094, -771391586323, 1462274060084, 275027615390, -1144357752058, 187976291422, 222215625748, -64880537440]
  b := [5342366349, -96198432691, 153836008055, 159542013715, -324473430597, -24212291640, 164338141092, -26469759144, -24167978698, 6488053744]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2246265661 T_ofList CD2246265661

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

end VoightMaximalOrderD10R698

namespace VoightMaximalOrderD10R704

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7060253378125, [5, -30, 31, 55, -65, -36, 42, 10, -11, -1, 1], 1⟩
local notation "l" => [5, -30, 31, 55, -65, -36, 42, 10, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 30, -31, -55, 65, 36, -42, -10, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], ![-5, 25, -1, -86, 10, 101, -6, -52, 1, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], ![-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], ![-60, 355, -347, -661, 694, 442, -403, -126, 80, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], ![-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], ![-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], ![-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], ![-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], ![-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], ![-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], ![-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], ![-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], ![-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], ![-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], ![-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110], ![-550, 2835, -685, -8603, 1987, 8943, -1088, -3844, 176, 600]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], ![-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], ![-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], ![-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], ![-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110], ![-550, 2835, -685, -8603, 1987, 8943, -1088, -3844, 176, 600], ![-3000, 17450, -15765, -33685, 30397, 23587, -16257, -7088, 2756, 776]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], ![-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], ![-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], ![-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], ![-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110], ![-550, 2835, -685, -8603, 1987, 8943, -1088, -3844, 176, 600], ![-3000, 17450, -15765, -33685, 30397, 23587, -16257, -7088, 2756, 776], ![-3880, 20280, -6606, -58445, 16755, 58333, -9005, -24017, 1448, 3532]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], ![-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], ![-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], ![-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], ![-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110], ![-550, 2835, -685, -8603, 1987, 8943, -1088, -3844, 176, 600], ![-3000, 17450, -15765, -33685, 30397, 23587, -16257, -7088, 2756, 776], ![-3880, 20280, -6606, -58445, 16755, 58333, -9005, -24017, 1448, 3532], ![-17660, 102080, -89212, -200866, 171135, 143907, -90011, -44325, 14835, 4980]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-93, -13, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-93, -13, -12, -1, -1], [-110, -93, -13, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-93, -13, -12, -1, -1], [-110, -93, -13, -12, -1, -1], [-600, -110, -93, -13, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-93, -13, -12, -1, -1], [-110, -93, -13, -12, -1, -1], [-600, -110, -93, -13, -12, -1, -1], [-776, -600, -110, -93, -13, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-93, -13, -12, -1, -1], [-110, -93, -13, -12, -1, -1], [-600, -110, -93, -13, -12, -1, -1], [-776, -600, -110, -93, -13, -12, -1, -1], [-3532, -776, -600, -110, -93, -13, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 30, -31, -55, 65, 36, -42, -10, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], [-5, 25, -1, -86, 10, 101, -6, -52, 1, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], [-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], [-60, 355, -347, -661, 694, 442, -403, -126, 80, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], [-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], [-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], [-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], [-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], [-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], [-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], [-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], [-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], [-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], [-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], [-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110], [-550, 2835, -685, -8603, 1987, 8943, -1088, -3844, 176, 600]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], [-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], [-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], [-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], [-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110], [-550, 2835, -685, -8603, 1987, 8943, -1088, -3844, 176, 600], [-3000, 17450, -15765, -33685, 30397, 23587, -16257, -7088, 2756, 776]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], [-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], [-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], [-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], [-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110], [-550, 2835, -685, -8603, 1987, 8943, -1088, -3844, 176, 600], [-3000, 17450, -15765, -33685, 30397, 23587, -16257, -7088, 2756, 776], [-3880, 20280, -6606, -58445, 16755, 58333, -9005, -24017, 1448, 3532]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 30, -31, -55, 65, 36, -42, -10, 11, 1], [-5, 25, -1, -86, 10, 101, -6, -52, 1, 12], [-60, 355, -347, -661, 694, 442, -403, -126, 80, 13], [-65, 330, -48, -1062, 184, 1162, -104, -533, 17, 93], [-465, 2725, -2553, -5163, 4983, 3532, -2744, -1034, 490, 110], [-550, 2835, -685, -8603, 1987, 8943, -1088, -3844, 176, 600], [-3000, 17450, -15765, -33685, 30397, 23587, -16257, -7088, 2756, 776], [-3880, 20280, -6606, -58445, 16755, 58333, -9005, -24017, 1448, 3532], [-17660, 102080, -89212, -200866, 171135, 143907, -90011, -44325, 14835, 4980]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp23189 : Fact (Nat.Prime 23189) := fact_iff.2 (by norm_num)
instance hp97429 : Fact (Nat.Prime 97429) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 1, 2]
  b' := [1, 4, 4, 0, 1]
  k := [1]
  f := [-1, 6, -6, -11, 13, 8, -8, -2, 3, 1]
  g := [0, 1, 0, 0, 2, 1]
  h := [0, 1, 0, 0, 2, 1]
  a := [4, 4, 2, 2, 4]
  b := [0, 2, 3, 1, 2, 2, 2, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23189 : CertificateDedekindCriterionLists l 23189 where
  n := 2
  a' := [13030, 7022, 2181, 18391, 10644, 9000, 15298, 19287]
  b' := [11252, 3888, 3511, 13660, 3991, 9785, 5692, 1662, 21046]
  k := [2064, 20537, 15326, 16404, 17113, 21899, 12697, 200, 1]
  f := [629, 6697, 5328, 6515, 466, 3779, 4784, 7825, 5797, 1]
  g := [1269, 13511, 10748, 13143, 939, 7624, 9651, 15786, 11694, 1]
  h := [11494, 1]
  a := [18412, 11466, 9811, 6904, 12978, 14992, 22099, 1029, 20589]
  b := [2916, 8782, 1749, 10795, 18687, 8290, 21919, 17889, 2600]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD97429 : CertificateDedekindCriterionLists l 97429 where
  n := 2
  a' := [75929, 83994, 26989, 4517, 43802, 46598, 46363, 40769]
  b' := [65450, 19170, 42453, 51759, 94984, 73135, 95720, 13740, 17121]
  k := [46460, 51182, 57385, 38953, 57503, 89066, 77115, 56927, 1]
  f := [45165, 40949, 29537, 29173, 57167, 58673, 46469, 34463, 20148, 1]
  g := [63806, 57849, 41727, 41213, 80761, 82888, 65647, 48686, 28463, 1]
  h := [68965, 1]
  a := [79167, 35574, 19398, 53884, 55677, 86586, 428, 52796, 30182]
  b := [20957, 13074, 5899, 17497, 55972, 3327, 82145, 30859, 67247]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 23189, 97429]
  exp := ![1, 1, 1]
  pdgood := [5, 23189, 97429]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp23189.out
    exact hp97429.out
  a := [-68637693769, 23483985978, 353809327146, -105988570894, -442557327410, 66611303578, 190778609884, -8112883412, -24294044120]
  b := [-11816162475, 48131622317, -958255839, -107892806568, 15108339250, 82344234326, -6467859700, -24722325926, 568347900, 2429404412]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23189 T_ofList CD23189
    exact satisfiesDedekindCriterion_of_certificate_lists T l 97429 T_ofList CD97429

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

end VoightMaximalOrderD10R704

namespace VoightMaximalOrderD10R716

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7140386403125, [1, -5, -3, 32, -1, -45, 9, 21, -6, -3, 1], 1⟩
local notation "l" => [1, -5, -3, 32, -1, -45, 9, 21, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -32, 1, 45, -9, -21, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], ![-3, 14, 14, -93, -29, 136, 18, -72, -3, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], ![-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], ![-15, 72, 59, -466, -78, 646, 1, -297, 18, 42]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], ![-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], ![-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], ![-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], ![-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], ![-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], ![-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], ![-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], ![-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], ![-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], ![-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], ![-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387], ![-387, 1791, 1839, -11757, -4023, 16274, 2573, -7611, -434, 1144]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], ![-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], ![-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], ![-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], ![-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387], ![-387, 1791, 1839, -11757, -4023, 16274, 2573, -7611, -434, 1144], ![-1144, 5333, 5223, -34769, -10613, 47457, 5978, -21451, -747, 2998]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], ![-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], ![-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], ![-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], ![-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387], ![-387, 1791, 1839, -11757, -4023, 16274, 2573, -7611, -434, 1144], ![-1144, 5333, 5223, -34769, -10613, 47457, 5978, -21451, -747, 2998], ![-2998, 13846, 14327, -90713, -31771, 124297, 20475, -56980, -3463, 8247]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], ![-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], ![-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], ![-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], ![-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387], ![-387, 1791, 1839, -11757, -4023, 16274, 2573, -7611, -434, 1144], ![-1144, 5333, 5223, -34769, -10613, 47457, 5978, -21451, -747, 2998], ![-2998, 13846, 14327, -90713, -31771, 124297, 20475, -56980, -3463, 8247], ![-8247, 38237, 38587, -249577, -82466, 339344, 50074, -152712, -7498, 21278]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1], [-387, -144, -42, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1], [-387, -144, -42, -15, -3, -1], [-1144, -387, -144, -42, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1], [-387, -144, -42, -15, -3, -1], [-1144, -387, -144, -42, -15, -3, -1], [-2998, -1144, -387, -144, -42, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1], [-387, -144, -42, -15, -3, -1], [-1144, -387, -144, -42, -15, -3, -1], [-2998, -1144, -387, -144, -42, -15, -3, -1], [-8247, -2998, -1144, -387, -144, -42, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -32, 1, 45, -9, -21, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], [-3, 14, 14, -93, -29, 136, 18, -72, -3, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], [-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], [-15, 72, 59, -466, -78, 646, 1, -297, 18, 42]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], [-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], [-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], [-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], [-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], [-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], [-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], [-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], [-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], [-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], [-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], [-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387], [-387, 1791, 1839, -11757, -4023, 16274, 2573, -7611, -434, 1144]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], [-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], [-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], [-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], [-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387], [-387, 1791, 1839, -11757, -4023, 16274, 2573, -7611, -434, 1144], [-1144, 5333, 5223, -34769, -10613, 47457, 5978, -21451, -747, 2998]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], [-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], [-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], [-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], [-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387], [-387, 1791, 1839, -11757, -4023, 16274, 2573, -7611, -434, 1144], [-1144, 5333, 5223, -34769, -10613, 47457, 5978, -21451, -747, 2998], [-2998, 13846, 14327, -90713, -31771, 124297, 20475, -56980, -3463, 8247]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -32, 1, 45, -9, -21, 6, 3], [-3, 14, 14, -93, -29, 136, 18, -72, -3, 15], [-15, 72, 59, -466, -78, 646, 1, -297, 18, 42], [-42, 195, 198, -1285, -424, 1812, 268, -881, -45, 144], [-144, 678, 627, -4410, -1141, 6056, 516, -2756, -17, 387], [-387, 1791, 1839, -11757, -4023, 16274, 2573, -7611, -434, 1144], [-1144, 5333, 5223, -34769, -10613, 47457, 5978, -21451, -747, 2998], [-2998, 13846, 14327, -90713, -31771, 124297, 20475, -56980, -3463, 8247], [-8247, 38237, 38587, -249577, -82466, 339344, 50074, -152712, -7498, 21278]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp3049 : Fact (Nat.Prime 3049) := fact_iff.2 (by norm_num)
instance hp749401 : Fact (Nat.Prime 749401) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2, 2]
  b' := [4, 1, 1, 3, 2]
  k := [1]
  f := [3, 1, 7, 0, 5, 17, 3, -1, 3, 1]
  g := [4, 0, 4, 4, 1, 1]
  h := [4, 0, 4, 4, 1, 1]
  a := [4, 0, 3]
  b := [1, 4, 1, 3, 2, 4, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3049 : CertificateDedekindCriterionLists l 3049 where
  n := 2
  a' := [2645, 788, 1788, 1556, 1433, 1693, 1982, 397]
  b' := [1358, 1793, 1669, 573, 2779, 2879, 1235, 287, 1311]
  k := [2401, 2715, 1995, 280, 633, 2214, 1391, 1117, 1]
  f := [40, 329, 1183, 567, 2068, 1418, 612, 748, 455, 1]
  g := [49, 403, 1449, 694, 2533, 1736, 749, 916, 557, 1]
  h := [2489, 1]
  a := [30, 1702, 2786, 908, 210, 2977, 1801, 1323, 1802]
  b := [660, 1568, 1509, 2655, 1132, 1013, 368, 2590, 1247]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD749401 : CertificateDedekindCriterionLists l 749401 where
  n := 2
  a' := [165082, 305327, 328368, 133634, 677723, 523105, 722571, 713085]
  b' := [675557, 266892, 272085, 346581, 208825, 349041, 443038, 138478, 420369]
  k := [290781, 208658, 329453, 507504, 83901, 242082, 652726, 226443, 1]
  f := [286059, 231391, 624645, 233569, 332484, 148722, 275559, 512702, 96115, 1]
  g := [336970, 272572, 735815, 275137, 391657, 175190, 324601, 603949, 113220, 1]
  h := [636178, 1]
  a := [111959, 509023, 747281, 221250, 565733, 322755, 422076, 80578, 33126]
  b := [413727, 519573, 643168, 418910, 717898, 125704, 728225, 741897, 716275]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 3049, 749401]
  exp := ![1, 1, 1]
  pdgood := [5, 3049, 749401]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp3049.out
    exact hp749401.out
  a := [-486187943895, -2264189633868, 1810898999268, 5802703674818, -2717740659255, -3850048498344, 1625359063589, 709533871896, -295505368980]
  b := [-99522512428, 152777032035, 823917522999, -379211327496, -1195805805998, 429557656917, 559626775572, -200646469367, -79818548259, 29550536898]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3049 T_ofList CD3049
    exact satisfiesDedekindCriterion_of_certificate_lists T l 749401 T_ofList CD749401

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

end VoightMaximalOrderD10R716

namespace VoightMaximalOrderD10R721

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7167043667825, [1, -3, -18, 27, 33, -49, -10, 26, -3, -4, 1], 1⟩
local notation "l" => [1, -3, -18, 27, 33, -49, -10, 26, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 18, -27, -33, 49, 10, -26, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], ![-4, 11, 75, -90, -159, 163, 89, -94, -14, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], ![-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], ![-19, 53, 353, -438, -717, 772, 353, -405, -37, 62]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], ![-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], ![-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], ![-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], ![-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], ![-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], ![-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], ![-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], ![-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], ![-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], ![-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], ![-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625], ![-625, 1664, 11821, -12910, -25153, 22341, 14105, -11819, -2219, 1874]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], ![-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], ![-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], ![-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], ![-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625], ![-625, 1664, 11821, -12910, -25153, 22341, 14105, -11819, -2219, 1874], ![-1874, 4997, 35396, -38777, -74752, 66673, 41081, -34619, -6197, 5277]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], ![-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], ![-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], ![-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], ![-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625], ![-625, 1664, 11821, -12910, -25153, 22341, 14105, -11819, -2219, 1874], ![-1874, 4997, 35396, -38777, -74752, 66673, 41081, -34619, -6197, 5277], ![-5277, 13957, 99983, -107083, -212918, 183821, 119443, -96121, -18788, 14911]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], ![-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], ![-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], ![-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], ![-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625], ![-625, 1664, 11821, -12910, -25153, 22341, 14105, -11819, -2219, 1874], ![-1874, 4997, 35396, -38777, -74752, 66673, 41081, -34619, -6197, 5277], ![-5277, 13957, 99983, -107083, -212918, 183821, 119443, -96121, -18788, 14911], ![-14911, 39456, 282355, -302614, -599146, 517721, 332931, -268243, -51388, 40856]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-211, -62, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-211, -62, -19, -4, -1], [-625, -211, -62, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-211, -62, -19, -4, -1], [-625, -211, -62, -19, -4, -1], [-1874, -625, -211, -62, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-211, -62, -19, -4, -1], [-625, -211, -62, -19, -4, -1], [-1874, -625, -211, -62, -19, -4, -1], [-5277, -1874, -625, -211, -62, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-211, -62, -19, -4, -1], [-625, -211, -62, -19, -4, -1], [-1874, -625, -211, -62, -19, -4, -1], [-5277, -1874, -625, -211, -62, -19, -4, -1], [-14911, -5277, -1874, -625, -211, -62, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 18, -27, -33, 49, 10, -26, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], [-4, 11, 75, -90, -159, 163, 89, -94, -14, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], [-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], [-19, 53, 353, -438, -717, 772, 353, -405, -37, 62]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], [-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], [-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], [-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], [-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], [-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], [-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], [-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], [-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], [-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], [-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], [-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625], [-625, 1664, 11821, -12910, -25153, 22341, 14105, -11819, -2219, 1874]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], [-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], [-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], [-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], [-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625], [-625, 1664, 11821, -12910, -25153, 22341, 14105, -11819, -2219, 1874], [-1874, 4997, 35396, -38777, -74752, 66673, 41081, -34619, -6197, 5277]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], [-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], [-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], [-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], [-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625], [-625, 1664, 11821, -12910, -25153, 22341, 14105, -11819, -2219, 1874], [-1874, 4997, 35396, -38777, -74752, 66673, 41081, -34619, -6197, 5277], [-5277, 13957, 99983, -107083, -212918, 183821, 119443, -96121, -18788, 14911]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 18, -27, -33, 49, 10, -26, 3, 4], [-4, 11, 75, -90, -159, 163, 89, -94, -14, 19], [-19, 53, 353, -438, -717, 772, 353, -405, -37, 62], [-62, 167, 1169, -1321, -2484, 2321, 1392, -1259, -219, 211], [-211, 571, 3965, -4528, -8284, 7855, 4431, -4094, -626, 625], [-625, 1664, 11821, -12910, -25153, 22341, 14105, -11819, -2219, 1874], [-1874, 4997, 35396, -38777, -74752, 66673, 41081, -34619, -6197, 5277], [-5277, 13957, 99983, -107083, -212918, 183821, 119443, -96121, -18788, 14911], [-14911, 39456, 282355, -302614, -599146, 517721, 332931, -268243, -51388, 40856]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp39558679 : Fact (Nat.Prime 39558679) := fact_iff.2 (by norm_num)
instance hp7247 : Fact (Nat.Prime 7247) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 3
  a' := [0, 3, 4, 4, 0, 2, 2]
  b' := [3, 2, 3, 3, 2, 2, 1, 1]
  k := [4, 3, 1, 1, 0, 0, 3, 2, 4, 3, 0, 2, 3, 4, 1]
  f := [3, 3, 8, -1, -5, 13, 5, -4, 2, 1]
  g := [4, 2, 4, 4, 0, 3, 3, 0, 1]
  h := [4, 1, 1]
  a := [1, 0, 2, 1, 3, 4, 3, 2]
  b := [2, 2, 1, 1, 2, 3, 4, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD39558679 : CertificateDedekindCriterionLists l 39558679 where
  n := 2
  a' := [28096890, 4023234, 22552110, 3951815, 39150185, 19796273, 6895532, 5117410]
  b' := [21629010, 31176547, 5206766, 11568914, 858409, 17611966, 1979750, 11523263, 17013034]
  k := [11727867, 38880977, 5163354, 33076452, 38329890, 35586608, 9151809, 5489057, 1]
  f := [1760273, 6703721, 1588620, 4092679, 2447466, 11400885, 10369160, 16772659, 9699257, 1]
  g := [4087752, 15567556, 3689134, 9504126, 5683569, 26475433, 24079533, 38949906, 22523866, 1]
  h := [17034809, 1]
  a := [4873229, 28764384, 33976660, 14688095, 16624045, 22107710, 1564291, 23266002, 2384309]
  b := [33375346, 15411218, 13667818, 38954557, 39365726, 9281027, 30349977, 16611512, 37174370]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7247 : CertificateDedekindCriterionLists l 7247 where
  n := 2
  a' := [6814, 7116, 2004, 7066, 2649, 6876, 2745, 3158]
  b' := [2494, 4764, 1789, 4105, 6455, 851, 3369, 447, 2870]
  k := [201, 2407, 7097, 488, 6630, 1840, 2494, 6781, 1]
  f := [94, 174, 128, 124, 93, 131, 174, 114, 224, 1]
  g := [2949, 5446, 3992, 3873, 2901, 4097, 5441, 3553, 7012, 1]
  h := [231, 1]
  a := [1896, 5647, 1555, 3587, 986, 1595, 6180, 1725, 4941]
  b := [694, 6944, 6896, 1464, 6318, 2303, 2255, 5914, 2306]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 39558679, 7247]
  exp := ![1, 1, 1]
  pdgood := [5, 39558679, 7247]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp39558679.out
    exact hp7247.out
  a := [-3076201452362, -55846565886654, 72597190510587, 239429873215662, -195458754547094, -207292279531762, 132273716459672, 45580697900766, -23876071215860]
  b := [-1503203395309, 2499120233852, 27926903624788, -19181197100415, -59699579436771, 32344842135522, 34115284994040, -16274862257972, -5513112638711, 2387607121586]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 39558679 T_ofList CD39558679
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7247 T_ofList CD7247

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

end VoightMaximalOrderD10R721

end TraceEuclidean
