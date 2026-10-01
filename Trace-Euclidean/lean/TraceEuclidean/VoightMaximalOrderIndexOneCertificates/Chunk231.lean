import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk227
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

namespace VoightMaximalOrderD10R740

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7274581690625, [-1, 2, 16, -5, -48, 4, 38, -1, -11, 0, 1], 1⟩
local notation "l" => [-1, 2, 16, -5, -48, 4, 38, -1, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -16, 5, 48, -4, -38, 1, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -16, 5, 48, -4, -38, 1, 11, 0], ![0, 1, -2, -16, 5, 48, -4, -38, 1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -16, 5, 48, -4, -38, 1, 11, 0], ![0, 1, -2, -16, 5, 48, -4, -38, 1, 11], ![11, -22, -175, 53, 512, -39, -370, 7, 83, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -16, 5, 48, -4, -38, 1, 11, 0], ![0, 1, -2, -16, 5, 48, -4, -38, 1, 11], ![11, -22, -175, 53, 512, -39, -370, 7, 83, 1], ![1, 9, -38, -170, 101, 508, -77, -369, 18, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -16, 5, 48, -4, -38, 1, 11, 0], ![0, 1, -2, -16, 5, 48, -4, -38, 1, 11], ![11, -22, -175, 53, 512, -39, -370, 7, 83, 1], ![1, 9, -38, -170, 101, 508, -77, -369, 18, 83], ![83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -16, 5, 48, -4, -38, 1, 11, 0], ![0, 1, -2, -16, 5, 48, -4, -38, 1, 11], ![11, -22, -175, 53, 512, -39, -370, 7, 83, 1], ![1, 9, -38, -170, 101, 508, -77, -369, 18, 83], ![83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18], ![18, 47, -453, -1229, 1241, 3742, -915, -2628, 204, 544]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -16, 5, 48, -4, -38, 1, 11, 0], ![0, 1, -2, -16, 5, 48, -4, -38, 1, 11], ![11, -22, -175, 53, 512, -39, -370, 7, 83, 1], ![1, 9, -38, -170, 101, 508, -77, -369, 18, 83], ![83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18], ![18, 47, -453, -1229, 1241, 3742, -915, -2628, 204, 544], ![544, -1070, -8657, 2267, 24883, -935, -16930, -371, 3356, 204]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -16, 5, 48, -4, -38, 1, 11, 0], ![0, 1, -2, -16, 5, 48, -4, -38, 1, 11], ![11, -22, -175, 53, 512, -39, -370, 7, 83, 1], ![1, 9, -38, -170, 101, 508, -77, -369, 18, 83], ![83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18], ![18, 47, -453, -1229, 1241, 3742, -915, -2628, 204, 544], ![544, -1070, -8657, 2267, 24883, -935, -16930, -371, 3356, 204], ![204, 136, -4334, -7637, 12059, 24067, -8687, -16726, 1873, 3356]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -16, 5, 48, -4, -38, 1, 11, 0], ![0, 1, -2, -16, 5, 48, -4, -38, 1, 11], ![11, -22, -175, 53, 512, -39, -370, 7, 83, 1], ![1, 9, -38, -170, 101, 508, -77, -369, 18, 83], ![83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18], ![18, 47, -453, -1229, 1241, 3742, -915, -2628, 204, 544], ![544, -1070, -8657, 2267, 24883, -935, -16930, -371, 3356, 204], ![204, 136, -4334, -7637, 12059, 24067, -8687, -16726, 1873, 3356], ![3356, -6508, -53560, 12446, 153451, -1365, -103461, -5331, 20190, 1873]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-83, -1, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-83, -1, -11, 0, -1], [-18, -83, -1, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-83, -1, -11, 0, -1], [-18, -83, -1, -11, 0, -1], [-544, -18, -83, -1, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-83, -1, -11, 0, -1], [-18, -83, -1, -11, 0, -1], [-544, -18, -83, -1, -11, 0, -1], [-204, -544, -18, -83, -1, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-83, -1, -11, 0, -1], [-18, -83, -1, -11, 0, -1], [-544, -18, -83, -1, -11, 0, -1], [-204, -544, -18, -83, -1, -11, 0, -1], [-3356, -204, -544, -18, -83, -1, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -16, 5, 48, -4, -38, 1, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -16, 5, 48, -4, -38, 1, 11, 0], [0, 1, -2, -16, 5, 48, -4, -38, 1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -16, 5, 48, -4, -38, 1, 11, 0], [0, 1, -2, -16, 5, 48, -4, -38, 1, 11], [11, -22, -175, 53, 512, -39, -370, 7, 83, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -16, 5, 48, -4, -38, 1, 11, 0], [0, 1, -2, -16, 5, 48, -4, -38, 1, 11], [11, -22, -175, 53, 512, -39, -370, 7, 83, 1], [1, 9, -38, -170, 101, 508, -77, -369, 18, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -16, 5, 48, -4, -38, 1, 11, 0], [0, 1, -2, -16, 5, 48, -4, -38, 1, 11], [11, -22, -175, 53, 512, -39, -370, 7, 83, 1], [1, 9, -38, -170, 101, 508, -77, -369, 18, 83], [83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -16, 5, 48, -4, -38, 1, 11, 0], [0, 1, -2, -16, 5, 48, -4, -38, 1, 11], [11, -22, -175, 53, 512, -39, -370, 7, 83, 1], [1, 9, -38, -170, 101, 508, -77, -369, 18, 83], [83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18], [18, 47, -453, -1229, 1241, 3742, -915, -2628, 204, 544]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -16, 5, 48, -4, -38, 1, 11, 0], [0, 1, -2, -16, 5, 48, -4, -38, 1, 11], [11, -22, -175, 53, 512, -39, -370, 7, 83, 1], [1, 9, -38, -170, 101, 508, -77, -369, 18, 83], [83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18], [18, 47, -453, -1229, 1241, 3742, -915, -2628, 204, 544], [544, -1070, -8657, 2267, 24883, -935, -16930, -371, 3356, 204]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -16, 5, 48, -4, -38, 1, 11, 0], [0, 1, -2, -16, 5, 48, -4, -38, 1, 11], [11, -22, -175, 53, 512, -39, -370, 7, 83, 1], [1, 9, -38, -170, 101, 508, -77, -369, 18, 83], [83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18], [18, 47, -453, -1229, 1241, 3742, -915, -2628, 204, 544], [544, -1070, -8657, 2267, 24883, -935, -16930, -371, 3356, 204], [204, 136, -4334, -7637, 12059, 24067, -8687, -16726, 1873, 3356]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -16, 5, 48, -4, -38, 1, 11, 0], [0, 1, -2, -16, 5, 48, -4, -38, 1, 11], [11, -22, -175, 53, 512, -39, -370, 7, 83, 1], [1, 9, -38, -170, 101, 508, -77, -369, 18, 83], [83, -165, -1319, 377, 3814, -231, -2646, 6, 544, 18], [18, 47, -453, -1229, 1241, 3742, -915, -2628, 204, 544], [544, -1070, -8657, 2267, 24883, -935, -16930, -371, 3356, 204], [204, 136, -4334, -7637, 12059, 24067, -8687, -16726, 1873, 3356], [3356, -6508, -53560, 12446, 153451, -1365, -103461, -5331, 20190, 1873]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2327866141 : Fact (Nat.Prime 2327866141) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 1]
  b' := [1, 1, 1, 1, 4]
  k := [1]
  f := [2, 2, 0, 5, 12, 2, -6, 1, 3]
  g := [3, 2, 2, 2, 0, 1]
  h := [3, 2, 2, 2, 0, 1]
  a := [0, 3, 1, 2]
  b := [2, 0, 1, 1, 4, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2327866141 : CertificateDedekindCriterionLists l 2327866141 where
  n := 2
  a' := [17698991, 1871502877, 1357842143, 917675065, 1057268332, 2026170496, 1418242755, 2068194962]
  b' := [279966411, 2189016310, 610881031, 1445261814, 1486188907, 1210721466, 989501064, 2190170543, 1063459527]
  k := [1933307968, 216202522, 1304054100, 591309954, 1649845161, 930539002, 1959778964, 895306273, 1]
  f := [64149187, 709386351, 251505536, 27048249, 617783172, 543139854, 30280150, 678526693, 495881977, 1]
  g := [208480949, 2305462416, 817377664, 87905160, 2007757666, 1765171428, 98408640, 2205170408, 1611586207, 1]
  h := [716279934, 1]
  a := [1617229351, 136839214, 2246404561, 1401259148, 1841625230, 136740578, 1567240300, 1473601369, 635377486]
  b := [2125602827, 2261772114, 952502018, 1481131907, 1875650834, 1248798341, 506337901, 1502118910, 1692488655]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 2327866141]
  exp := ![1, 1]
  pdgood := [5, 2327866141]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2327866141.out
  a := [-23245092571, -151538825956, 742709868469, -88248362352, -1221711245641, 206440803558, 614011436032, -29028582450, -79245534040]
  b := [-5802880933, 40321774521, 20184501425, -210251456885, 43310739379, 223416640857, -29407734516, -78835161092, 2902858245, 7924553404]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2327866141 T_ofList CD2327866141

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

end VoightMaximalOrderD10R740

namespace VoightMaximalOrderD10R742

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7282727340625, [-29, -28, 87, 69, -95, -56, 47, 18, -11, -2, 1], 1⟩
local notation "l" => [-29, -28, 87, 69, -95, -56, 47, 18, -11, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![29, 28, -87, -69, 95, 56, -47, -18, 11, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![29, 28, -87, -69, 95, 56, -47, -18, 11, 2], ![58, 85, -146, -225, 121, 207, -38, -83, 4, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![29, 28, -87, -69, 95, 56, -47, -18, 11, 2], ![58, 85, -146, -225, 121, 207, -38, -83, 4, 15], ![435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![29, 28, -87, -69, 95, 56, -47, -18, 11, 2], ![58, 85, -146, -225, 121, 207, -38, -83, 4, 15], ![435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], ![986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![29, 28, -87, -69, 95, 56, -47, -18, 11, 2], ![58, 85, -146, -225, 121, 207, -38, -83, 4, 15], ![435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], ![986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], ![4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![29, 28, -87, -69, 95, 56, -47, -18, 11, 2], ![58, 85, -146, -225, 121, 207, -38, -83, 4, 15], ![435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], ![986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], ![4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366], ![10614, 14598, -26656, -36917, 21940, 31180, -6753, -10534, 689, 1272]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![29, 28, -87, -69, 95, 56, -47, -18, 11, 2], ![58, 85, -146, -225, 121, 207, -38, -83, 4, 15], ![435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], ![986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], ![4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366], ![10614, 14598, -26656, -36917, 21940, 31180, -6753, -10534, 689, 1272], ![36888, 46230, -96066, -114424, 83923, 93172, -28604, -29649, 3458, 3233]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![29, 28, -87, -69, 95, 56, -47, -18, 11, 2], ![58, 85, -146, -225, 121, 207, -38, -83, 4, 15], ![435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], ![986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], ![4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366], ![10614, 14598, -26656, -36917, 21940, 31180, -6753, -10534, 689, 1272], ![36888, 46230, -96066, -114424, 83923, 93172, -28604, -29649, 3458, 3233], ![93757, 127412, -235041, -319143, 192711, 264971, -58779, -86798, 5914, 9924]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![29, 28, -87, -69, 95, 56, -47, -18, 11, 2], ![58, 85, -146, -225, 121, 207, -38, -83, 4, 15], ![435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], ![986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], ![4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366], ![10614, 14598, -26656, -36917, 21940, 31180, -6753, -10534, 689, 1272], ![36888, 46230, -96066, -114424, 83923, 93172, -28604, -29649, 3458, 3233], ![93757, 127412, -235041, -319143, 192711, 264971, -58779, -86798, 5914, 9924], ![287796, 371629, -735976, -919797, 623637, 748455, -201457, -237411, 22366, 25762]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-150, -34, -15, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-150, -34, -15, -2, -1], [-366, -150, -34, -15, -2, -1]], ![[], [], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-150, -34, -15, -2, -1], [-366, -150, -34, -15, -2, -1], [-1272, -366, -150, -34, -15, -2, -1]], ![[], [], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-150, -34, -15, -2, -1], [-366, -150, -34, -15, -2, -1], [-1272, -366, -150, -34, -15, -2, -1], [-3233, -1272, -366, -150, -34, -15, -2, -1]], ![[], [-1], [-2, -1], [-15, -2, -1], [-34, -15, -2, -1], [-150, -34, -15, -2, -1], [-366, -150, -34, -15, -2, -1], [-1272, -366, -150, -34, -15, -2, -1], [-3233, -1272, -366, -150, -34, -15, -2, -1], [-9924, -3233, -1272, -366, -150, -34, -15, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [29, 28, -87, -69, 95, 56, -47, -18, 11, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [29, 28, -87, -69, 95, 56, -47, -18, 11, 2], [58, 85, -146, -225, 121, 207, -38, -83, 4, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [29, 28, -87, -69, 95, 56, -47, -18, 11, 2], [58, 85, -146, -225, 121, 207, -38, -83, 4, 15], [435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [29, 28, -87, -69, 95, 56, -47, -18, 11, 2], [58, 85, -146, -225, 121, 207, -38, -83, 4, 15], [435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], [986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [29, 28, -87, -69, 95, 56, -47, -18, 11, 2], [58, 85, -146, -225, 121, 207, -38, -83, 4, 15], [435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], [986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], [4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [29, 28, -87, -69, 95, 56, -47, -18, 11, 2], [58, 85, -146, -225, 121, 207, -38, -83, 4, 15], [435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], [986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], [4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366], [10614, 14598, -26656, -36917, 21940, 31180, -6753, -10534, 689, 1272]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [29, 28, -87, -69, 95, 56, -47, -18, 11, 2], [58, 85, -146, -225, 121, 207, -38, -83, 4, 15], [435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], [986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], [4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366], [10614, 14598, -26656, -36917, 21940, 31180, -6753, -10534, 689, 1272], [36888, 46230, -96066, -114424, 83923, 93172, -28604, -29649, 3458, 3233]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [29, 28, -87, -69, 95, 56, -47, -18, 11, 2], [58, 85, -146, -225, 121, 207, -38, -83, 4, 15], [435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], [986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], [4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366], [10614, 14598, -26656, -36917, 21940, 31180, -6753, -10534, 689, 1272], [36888, 46230, -96066, -114424, 83923, 93172, -28604, -29649, 3458, 3233], [93757, 127412, -235041, -319143, 192711, 264971, -58779, -86798, 5914, 9924]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [29, 28, -87, -69, 95, 56, -47, -18, 11, 2], [58, 85, -146, -225, 121, 207, -38, -83, 4, 15], [435, 478, -1220, -1181, 1200, 961, -498, -308, 82, 34], [986, 1387, -2480, -3566, 2049, 3104, -637, -1110, 66, 150], [4350, 5186, -11663, -12830, 10684, 10449, -3946, -3337, 540, 366], [10614, 14598, -26656, -36917, 21940, 31180, -6753, -10534, 689, 1272], [36888, 46230, -96066, -114424, 83923, 93172, -28604, -29649, 3458, 3233], [93757, 127412, -235041, -319143, 192711, 264971, -58779, -86798, 5914, 9924], [287796, 371629, -735976, -919797, 623637, 748455, -201457, -237411, 22366, 25762]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp139 : Fact (Nat.Prime 139) := fact_iff.2 (by norm_num)
instance hp1524181 : Fact (Nat.Prime 1524181) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3]
  b' := [0, 1, 3, 2]
  k := [1]
  f := [6, 6, -16, -11, 24, 18, -1, 4, 7, 2]
  g := [1, 1, 3, 4, 4, 1]
  h := [1, 1, 3, 4, 4, 1]
  a := [1, 1, 3, 2, 4]
  b := [0, 3, 4, 4, 1, 3, 1, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [1, 4, 1, 9, 8, 7, 5, 1]
  b' := [6, 10, 3, 8, 9, 10, 4, 2, 6]
  k := [3, 8, 1, 5, 2, 2, 10, 6, 1]
  f := [9, 6, -5, -4, 14, 9, 0, 4, 3, 1]
  g := [10, 4, 4, 3, 8, 5, 6, 8, 2, 1]
  h := [7, 1]
  a := [3, 2, 2, 5, 9, 9, 1, 3, 7]
  b := [4, 8, 8, 1, 7, 0, 5, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD139 : CertificateDedekindCriterionLists l 139 where
  n := 2
  a' := [14, 124, 85, 91, 38, 136, 15, 96]
  b' := [69, 85, 96, 119, 66, 75, 24, 129, 82]
  k := [59, 73, 0, 104, 55, 32, 53, 129, 1]
  f := [3, 3, 2, 4, 3, 2, 3, 1, 4, 1]
  g := [97, 73, 73, 138, 46, 44, 105, 13, 133, 1]
  h := [4, 1]
  a := [130, 129, 58, 125, 44, 114, 67, 26, 35]
  b := [92, 3, 92, 82, 49, 39, 78, 41, 104]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1524181 : CertificateDedekindCriterionLists l 1524181 where
  n := 2
  a' := [1060588, 567841, 587932, 512251, 853467, 827323, 579066, 1477637]
  b' := [250964, 317855, 1164269, 654311, 1101099, 982437, 1197024, 1165545, 174525]
  k := [524206, 1435993, 1173680, 14003, 907840, 408216, 271856, 17971, 1]
  f := [230377, 223112, 737793, 533956, 321532, 582264, 314456, 543881, 380992, 1]
  g := [466252, 451548, 1493193, 1080653, 650736, 1178423, 636415, 1100741, 771075, 1]
  h := [753104, 1]
  a := [568435, 1200064, 1277383, 778484, 1299638, 889324, 978923, 370748, 737192]
  b := [1404562, 1495996, 149887, 788604, 1357313, 150515, 920615, 1515280, 786989]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 11, 139, 1524181]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 11, 139, 1524181]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp139.out
    exact hp1524181.out
  a := [16971147927, -133790356534, 57938195196, 240417089014, -112018715258, -130287067184, 58343140218, 21884596646, -9404109020]
  b := [-17993416201, 9781206377, 54275176711, -27036722652, -51229873965, 22875814708, 18887708511, -7804073998, -2376541845, 940410902]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 139 T_ofList CD139
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1524181 T_ofList CD1524181

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

end VoightMaximalOrderD10R742

namespace VoightMaximalOrderD10R747

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7322530253125, [1, -6, 3, 28, -30, -30, 33, 11, -11, -1, 1], 1⟩
local notation "l" => [1, -6, 3, 28, -30, -30, 33, 11, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 30, 30, -33, -11, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], ![-1, 5, 3, -31, 2, 60, -3, -44, 0, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], ![-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], ![-12, 71, -31, -333, 329, 362, -336, -135, 88, 12]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], ![-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], ![-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], ![-12, 60, 35, -367, 27, 689, -34, -468, -3, 100]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], ![-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], ![-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], ![-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], ![-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], ![-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], ![-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], ![-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], ![-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97], ![-97, 482, 297, -2956, 145, 5543, -174, -3678, -67, 729]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], ![-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], ![-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], ![-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], ![-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97], ![-97, 482, 297, -2956, 145, 5543, -174, -3678, -67, 729], ![-729, 4277, -1705, -20115, 18914, 22015, -18514, -8193, 4341, 662]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], ![-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], ![-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], ![-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], ![-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97], ![-97, 482, 297, -2956, 145, 5543, -174, -3678, -67, 729], ![-729, 4277, -1705, -20115, 18914, 22015, -18514, -8193, 4341, 662], ![-662, 3243, 2291, -20241, -255, 38774, 169, -25796, -911, 5003]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], ![-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], ![-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], ![-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], ![-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97], ![-97, 482, 297, -2956, 145, 5543, -174, -3678, -67, 729], ![-729, 4277, -1705, -20115, 18914, 22015, -18514, -8193, 4341, 662], ![-662, 3243, 2291, -20241, -255, 38774, 169, -25796, -911, 5003], ![-5003, 29356, -11766, -137793, 129849, 149835, -126325, -54864, 29237, 4092]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-100, -12, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-100, -12, -12, -1, -1], [-97, -100, -12, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-100, -12, -12, -1, -1], [-97, -100, -12, -12, -1, -1], [-729, -97, -100, -12, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-100, -12, -12, -1, -1], [-97, -100, -12, -12, -1, -1], [-729, -97, -100, -12, -12, -1, -1], [-662, -729, -97, -100, -12, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-100, -12, -12, -1, -1], [-97, -100, -12, -12, -1, -1], [-729, -97, -100, -12, -12, -1, -1], [-662, -729, -97, -100, -12, -12, -1, -1], [-5003, -662, -729, -97, -100, -12, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 30, 30, -33, -11, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], [-1, 5, 3, -31, 2, 60, -3, -44, 0, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], [-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], [-12, 71, -31, -333, 329, 362, -336, -135, 88, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], [-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], [-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], [-12, 60, 35, -367, 27, 689, -34, -468, -3, 100]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], [-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], [-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], [-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], [-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], [-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], [-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], [-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], [-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97], [-97, 482, 297, -2956, 145, 5543, -174, -3678, -67, 729]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], [-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], [-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], [-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], [-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97], [-97, 482, 297, -2956, 145, 5543, -174, -3678, -67, 729], [-729, 4277, -1705, -20115, 18914, 22015, -18514, -8193, 4341, 662]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], [-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], [-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], [-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], [-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97], [-97, 482, 297, -2956, 145, 5543, -174, -3678, -67, 729], [-729, 4277, -1705, -20115, 18914, 22015, -18514, -8193, 4341, 662], [-662, 3243, 2291, -20241, -255, 38774, 169, -25796, -911, 5003]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 30, 30, -33, -11, 11, 1], [-1, 5, 3, -31, 2, 60, -3, -44, 0, 12], [-12, 71, -31, -333, 329, 362, -336, -135, 88, 12], [-12, 60, 35, -367, 27, 689, -34, -468, -3, 100], [-100, 588, -240, -2765, 2633, 3027, -2611, -1134, 632, 97], [-97, 482, 297, -2956, 145, 5543, -174, -3678, -67, 729], [-729, 4277, -1705, -20115, 18914, 22015, -18514, -8193, 4341, 662], [-662, 3243, 2291, -20241, -255, 38774, 169, -25796, -911, 5003], [-5003, 29356, -11766, -137793, 129849, 149835, -126325, -54864, 29237, 4092]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp18439 : Fact (Nat.Prime 18439) := fact_iff.2 (by norm_num)
instance hp127079 : Fact (Nat.Prime 127079) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 3]
  b' := [2, 2, 3, 4]
  k := [1]
  f := [3, 6, 6, -2, 11, 10, -3, -1, 3, 1]
  g := [4, 3, 3, 0, 2, 1]
  h := [4, 3, 3, 0, 2, 1]
  a := [4, 3, 3, 4, 1]
  b := [1, 1, 2, 4, 3, 1, 1, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD18439 : CertificateDedekindCriterionLists l 18439 where
  n := 2
  a' := [11267, 7120, 763, 8181, 13186, 5935, 18139, 3600]
  b' := [16120, 9769, 3, 5339, 16922, 9207, 2440, 2235, 18039]
  k := [1685, 600, 13408, 1550, 14510, 17296, 3198, 16958, 1]
  f := [461, 127, 94, 690, 300, 678, 209, 546, 711, 1]
  g := [11487, 3149, 2338, 17190, 7452, 16884, 5185, 13598, 17698, 1]
  h := [740, 1]
  a := [5699, 14859, 37, 8251, 8514, 16965, 8207, 8397, 8249]
  b := [15162, 6403, 14151, 8005, 8596, 12819, 16469, 17844, 10190]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD127079 : CertificateDedekindCriterionLists l 127079 where
  n := 2
  a' := [111193, 47120, 108289, 35522, 13983, 102662, 40996, 54725]
  b' := [49472, 87127, 20015, 5530, 125669, 31572, 106321, 28609, 50399]
  k := [16604, 45530, 116757, 15566, 19004, 59053, 18915, 64305, 1]
  f := [87805, 30324, 93767, 45015, 76839, 76427, 63608, 91625, 24018, 1]
  g := [117546, 40594, 125527, 60261, 102865, 102313, 85152, 122659, 32152, 1]
  h := [94926, 1]
  a := [37068, 74291, 2053, 95586, 54246, 96774, 112283, 105075, 101617]
  b := [7106, 25947, 126318, 5502, 41049, 84731, 35893, 52866, 25462]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 18439, 127079]
  exp := ![1, 1, 1]
  pdgood := [5, 18439, 127079]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp18439.out
    exact hp127079.out
  a := [-84356298360311, -74935190186736, 1039309860929403, 274264959569744, -1590903335673471, -218405883007290, 670242037145658, 27561220995132, -74504414854880]
  b := [-14061335734786, 57805764261069, 66922415135546, -267299525623033, -82644253030953, 265750861790579, 37529236773361, -83810102506382, -3501166248062, 7450441485488]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 18439 T_ofList CD18439
    exact satisfiesDedekindCriterion_of_certificate_lists T l 127079 T_ofList CD127079

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

end VoightMaximalOrderD10R747

namespace VoightMaximalOrderD10R754

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7376833717588, [-2, -2, 22, 17, -55, -44, 30, 21, -8, -3, 1], 1⟩
local notation "l" => [-2, -2, 22, 17, -55, -44, 30, 21, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -22, -17, 55, 44, -30, -21, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -22, -17, 55, 44, -30, -21, 8, 3], ![6, 8, -64, -73, 148, 187, -46, -93, 3, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -22, -17, 55, 44, -30, -21, 8, 3], ![6, 8, -64, -73, 148, 187, -46, -93, 3, 17], ![34, 40, -366, -353, 862, 896, -323, -403, 43, 54]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -22, -17, 55, 44, -30, -21, 8, 3], ![6, 8, -64, -73, 148, 187, -46, -93, 3, 17], ![34, 40, -366, -353, 862, 896, -323, -403, 43, 54], ![108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -22, -17, 55, 44, -30, -21, 8, 3], ![6, 8, -64, -73, 148, 187, -46, -93, 3, 17], ![34, 40, -366, -353, 862, 896, -323, -403, 43, 54], ![108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], ![410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -22, -17, 55, 44, -30, -21, 8, 3], ![6, 8, -64, -73, 148, 187, -46, -93, 3, 17], ![34, 40, -366, -353, 862, 896, -323, -403, 43, 54], ![108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], ![410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644], ![1288, 1698, -13650, -15316, 30787, 38327, -7683, -16436, 123, 2115]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -22, -17, 55, 44, -30, -21, 8, 3], ![6, 8, -64, -73, 148, 187, -46, -93, 3, 17], ![34, 40, -366, -353, 862, 896, -323, -403, 43, 54], ![108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], ![410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644], ![1288, 1698, -13650, -15316, 30787, 38327, -7683, -16436, 123, 2115], ![4230, 5518, -44832, -49605, 101009, 123847, -25123, -52098, 484, 6468]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -22, -17, 55, 44, -30, -21, 8, 3], ![6, 8, -64, -73, 148, 187, -46, -93, 3, 17], ![34, 40, -366, -353, 862, 896, -323, -403, 43, 54], ![108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], ![410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644], ![1288, 1698, -13650, -15316, 30787, 38327, -7683, -16436, 123, 2115], ![4230, 5518, -44832, -49605, 101009, 123847, -25123, -52098, 484, 6468], ![12936, 17166, -136778, -154788, 306135, 385601, -70193, -160951, -354, 19888]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -22, -17, 55, 44, -30, -21, 8, 3], ![6, 8, -64, -73, 148, 187, -46, -93, 3, 17], ![34, 40, -366, -353, 862, 896, -323, -403, 43, 54], ![108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], ![410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644], ![1288, 1698, -13650, -15316, 30787, 38327, -7683, -16436, 123, 2115], ![4230, 5518, -44832, -49605, 101009, 123847, -25123, -52098, 484, 6468], ![12936, 17166, -136778, -154788, 306135, 385601, -70193, -160951, -354, 19888], ![39776, 52712, -420370, -474874, 939052, 1181207, -211039, -487841, -1847, 59310]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-54, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-54, -17, -3, -1], [-205, -54, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-54, -17, -3, -1], [-205, -54, -17, -3, -1], [-644, -205, -54, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-54, -17, -3, -1], [-205, -54, -17, -3, -1], [-644, -205, -54, -17, -3, -1], [-2115, -644, -205, -54, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-54, -17, -3, -1], [-205, -54, -17, -3, -1], [-644, -205, -54, -17, -3, -1], [-2115, -644, -205, -54, -17, -3, -1], [-6468, -2115, -644, -205, -54, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-54, -17, -3, -1], [-205, -54, -17, -3, -1], [-644, -205, -54, -17, -3, -1], [-2115, -644, -205, -54, -17, -3, -1], [-6468, -2115, -644, -205, -54, -17, -3, -1], [-19888, -6468, -2115, -644, -205, -54, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -22, -17, 55, 44, -30, -21, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -22, -17, 55, 44, -30, -21, 8, 3], [6, 8, -64, -73, 148, 187, -46, -93, 3, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -22, -17, 55, 44, -30, -21, 8, 3], [6, 8, -64, -73, 148, 187, -46, -93, 3, 17], [34, 40, -366, -353, 862, 896, -323, -403, 43, 54]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -22, -17, 55, 44, -30, -21, 8, 3], [6, 8, -64, -73, 148, 187, -46, -93, 3, 17], [34, 40, -366, -353, 862, 896, -323, -403, 43, 54], [108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -22, -17, 55, 44, -30, -21, 8, 3], [6, 8, -64, -73, 148, 187, -46, -93, 3, 17], [34, 40, -366, -353, 862, 896, -323, -403, 43, 54], [108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], [410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -22, -17, 55, 44, -30, -21, 8, 3], [6, 8, -64, -73, 148, 187, -46, -93, 3, 17], [34, 40, -366, -353, 862, 896, -323, -403, 43, 54], [108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], [410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644], [1288, 1698, -13650, -15316, 30787, 38327, -7683, -16436, 123, 2115]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -22, -17, 55, 44, -30, -21, 8, 3], [6, 8, -64, -73, 148, 187, -46, -93, 3, 17], [34, 40, -366, -353, 862, 896, -323, -403, 43, 54], [108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], [410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644], [1288, 1698, -13650, -15316, 30787, 38327, -7683, -16436, 123, 2115], [4230, 5518, -44832, -49605, 101009, 123847, -25123, -52098, 484, 6468]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -22, -17, 55, 44, -30, -21, 8, 3], [6, 8, -64, -73, 148, 187, -46, -93, 3, 17], [34, 40, -366, -353, 862, 896, -323, -403, 43, 54], [108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], [410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644], [1288, 1698, -13650, -15316, 30787, 38327, -7683, -16436, 123, 2115], [4230, 5518, -44832, -49605, 101009, 123847, -25123, -52098, 484, 6468], [12936, 17166, -136778, -154788, 306135, 385601, -70193, -160951, -354, 19888]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -22, -17, 55, 44, -30, -21, 8, 3], [6, 8, -64, -73, 148, 187, -46, -93, 3, 17], [34, 40, -366, -353, 862, 896, -323, -403, 43, 54], [108, 142, -1148, -1284, 2617, 3238, -724, -1457, 29, 205], [410, 518, -4368, -4633, 9991, 11637, -2912, -5029, 183, 644], [1288, 1698, -13650, -15316, 30787, 38327, -7683, -16436, 123, 2115], [4230, 5518, -44832, -49605, 101009, 123847, -25123, -52098, 484, 6468], [12936, 17166, -136778, -154788, 306135, 385601, -70193, -160951, -354, 19888], [39776, 52712, -420370, -474874, 939052, 1181207, -211039, -487841, -1847, 59310]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp2517701 : Fact (Nat.Prime 2517701) := fact_iff.2 (by norm_num)
instance hp732497 : Fact (Nat.Prime 732497) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 3
  a' := [1, 0, 1, 0, 1]
  b' := [1, 1, 1, 1, 0, 1, 1]
  k := [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1]
  f := [1, 1, -11, -8, 28, 22, -15, -10, 4, 2]
  g := [0, 1, 1, 0, 0, 1, 0, 1, 1]
  h := [0, 0, 1]
  a := [1, 1, 0, 1, 1, 0, 1, 1]
  b := [0, 0, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2517701 : CertificateDedekindCriterionLists l 2517701 where
  n := 2
  a' := [172959, 2476352, 2500529, 1720433, 2041754, 92126, 722917, 1402272]
  b' := [1508563, 390898, 1389430, 1195750, 1722136, 1836124, 614102, 1798440, 2361893]
  k := [1785173, 1331341, 565892, 1808702, 1209788, 1691865, 140411, 1954152, 1]
  f := [231549, 31759, 96296, 94829, 84859, 160879, 5524, 130697, 250238, 1]
  g := [2068939, 283766, 860424, 847314, 758230, 1437485, 49353, 1167805, 2235925, 1]
  h := [281773, 1]
  a := [368701, 366757, 570170, 1341877, 1023880, 16537, 1241308, 88781, 1481491]
  b := [2270829, 1918644, 1581078, 2076681, 1371609, 492550, 951170, 2327199, 1036210]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD732497 : CertificateDedekindCriterionLists l 732497 where
  n := 2
  a' := [726789, 291955, 421728, 168196, 414281, 399844, 577355, 485116]
  b' := [63505, 581423, 583344, 598158, 651958, 348427, 452740, 136681, 353041]
  k := [39614, 718169, 584665, 30649, 718715, 109614, 47570, 721356, 1]
  f := [979, 678, 273, 4540, 1452, 1951, 4528, 2020, 5527, 1]
  g := [128769, 89155, 35892, 597145, 190876, 256583, 595527, 265586, 726925, 1]
  h := [5569, 1]
  a := [422228, 482011, 664155, 149356, 612698, 368703, 152778, 701400, 247507]
  b := [624807, 498726, 212087, 341880, 557257, 478438, 101037, 547151, 484990]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 2517701, 732497]
  exp := ![1, 1, 1]
  pdgood := [2, 2517701, 732497]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp2517701.out
    exact hp732497.out
  a := [-200073157661, -38756044933310, 37247896018238, 210286741593928, -18628676783295, -177501981895262, 26558114341047, 41619446714736, -11247059801180]
  b := [-1644135271736, 2785142112779, 18655021232671, -13265282833108, -47499512117468, 6440656217065, 26184978658298, -4117769444747, -4499356465509, 1124705980118]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2517701 T_ofList CD2517701
    exact satisfiesDedekindCriterion_of_certificate_lists T l 732497 T_ofList CD732497

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

end VoightMaximalOrderD10R754

end TraceEuclidean
