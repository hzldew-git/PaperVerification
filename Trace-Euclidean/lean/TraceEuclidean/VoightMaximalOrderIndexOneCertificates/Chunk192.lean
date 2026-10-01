import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk188
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

namespace VoightMaximalOrderD10R262

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3744566823265, [-1, -2, 8, 14, -19, -25, 19, 14, -8, -2, 1], 1⟩
local notation "l" => [-1, -2, 8, 14, -19, -25, 19, 14, -8, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -8, -14, 19, 25, -19, -14, 8, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -8, -14, 19, 25, -19, -14, 8, 2], ![2, 5, -14, -36, 24, 69, -13, -47, 2, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -8, -14, 19, 25, -19, -14, 8, 2], ![2, 5, -14, -36, 24, 69, -13, -47, 2, 12], ![12, 26, -91, -182, 192, 324, -159, -181, 49, 26]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -8, -14, 19, 25, -19, -14, 8, 2], ![2, 5, -14, -36, 24, 69, -13, -47, 2, 12], ![12, 26, -91, -182, 192, 324, -159, -181, 49, 26], ![26, 64, -182, -455, 312, 842, -170, -523, 27, 101]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -8, -14, 19, 25, -19, -14, 8, 2], ![2, 5, -14, -36, 24, 69, -13, -47, 2, 12], ![12, 26, -91, -182, 192, 324, -159, -181, 49, 26], ![26, 64, -182, -455, 312, 842, -170, -523, 27, 101], ![101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -8, -14, 19, 25, -19, -14, 8, 2], ![2, 5, -14, -36, 24, 69, -13, -47, 2, 12], ![12, 26, -91, -182, 192, 324, -159, -181, 49, 26], ![26, 64, -182, -455, 312, 842, -170, -523, 27, 101], ![101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229], ![229, 559, -1604, -3950, 2755, 7189, -1514, -4283, 248, 743]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -8, -14, 19, 25, -19, -14, 8, 2], ![2, 5, -14, -36, 24, 69, -13, -47, 2, 12], ![12, 26, -91, -182, 192, 324, -159, -181, 49, 26], ![26, 64, -182, -455, 312, 842, -170, -523, 27, 101], ![101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229], ![229, 559, -1604, -3950, 2755, 7189, -1514, -4283, 248, 743], ![743, 1715, -5385, -12006, 10167, 21330, -6928, -11916, 1661, 1734]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -8, -14, 19, 25, -19, -14, 8, 2], ![2, 5, -14, -36, 24, 69, -13, -47, 2, 12], ![12, 26, -91, -182, 192, 324, -159, -181, 49, 26], ![26, 64, -182, -455, 312, 842, -170, -523, 27, 101], ![101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229], ![229, 559, -1604, -3950, 2755, 7189, -1514, -4283, 248, 743], ![743, 1715, -5385, -12006, 10167, 21330, -6928, -11916, 1661, 1734], ![1734, 4211, -12157, -29661, 20940, 53517, -11616, -31204, 1956, 5129]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -8, -14, 19, 25, -19, -14, 8, 2], ![2, 5, -14, -36, 24, 69, -13, -47, 2, 12], ![12, 26, -91, -182, 192, 324, -159, -181, 49, 26], ![26, 64, -182, -455, 312, 842, -170, -523, 27, 101], ![101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229], ![229, 559, -1604, -3950, 2755, 7189, -1514, -4283, 248, 743], ![743, 1715, -5385, -12006, 10167, 21330, -6928, -11916, 1661, 1734], ![1734, 4211, -12157, -29661, 20940, 53517, -11616, -31204, 1956, 5129], ![5129, 11992, -36821, -83963, 67790, 149165, -43934, -83422, 9828, 12214]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-101, -26, -12, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-101, -26, -12, -2, -1], [-229, -101, -26, -12, -2, -1]], ![[], [], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-101, -26, -12, -2, -1], [-229, -101, -26, -12, -2, -1], [-743, -229, -101, -26, -12, -2, -1]], ![[], [], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-101, -26, -12, -2, -1], [-229, -101, -26, -12, -2, -1], [-743, -229, -101, -26, -12, -2, -1], [-1734, -743, -229, -101, -26, -12, -2, -1]], ![[], [-1], [-2, -1], [-12, -2, -1], [-26, -12, -2, -1], [-101, -26, -12, -2, -1], [-229, -101, -26, -12, -2, -1], [-743, -229, -101, -26, -12, -2, -1], [-1734, -743, -229, -101, -26, -12, -2, -1], [-5129, -1734, -743, -229, -101, -26, -12, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -8, -14, 19, 25, -19, -14, 8, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -8, -14, 19, 25, -19, -14, 8, 2], [2, 5, -14, -36, 24, 69, -13, -47, 2, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -8, -14, 19, 25, -19, -14, 8, 2], [2, 5, -14, -36, 24, 69, -13, -47, 2, 12], [12, 26, -91, -182, 192, 324, -159, -181, 49, 26]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -8, -14, 19, 25, -19, -14, 8, 2], [2, 5, -14, -36, 24, 69, -13, -47, 2, 12], [12, 26, -91, -182, 192, 324, -159, -181, 49, 26], [26, 64, -182, -455, 312, 842, -170, -523, 27, 101]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -8, -14, 19, 25, -19, -14, 8, 2], [2, 5, -14, -36, 24, 69, -13, -47, 2, 12], [12, 26, -91, -182, 192, 324, -159, -181, 49, 26], [26, 64, -182, -455, 312, 842, -170, -523, 27, 101], [101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -8, -14, 19, 25, -19, -14, 8, 2], [2, 5, -14, -36, 24, 69, -13, -47, 2, 12], [12, 26, -91, -182, 192, 324, -159, -181, 49, 26], [26, 64, -182, -455, 312, 842, -170, -523, 27, 101], [101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229], [229, 559, -1604, -3950, 2755, 7189, -1514, -4283, 248, 743]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -8, -14, 19, 25, -19, -14, 8, 2], [2, 5, -14, -36, 24, 69, -13, -47, 2, 12], [12, 26, -91, -182, 192, 324, -159, -181, 49, 26], [26, 64, -182, -455, 312, 842, -170, -523, 27, 101], [101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229], [229, 559, -1604, -3950, 2755, 7189, -1514, -4283, 248, 743], [743, 1715, -5385, -12006, 10167, 21330, -6928, -11916, 1661, 1734]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -8, -14, 19, 25, -19, -14, 8, 2], [2, 5, -14, -36, 24, 69, -13, -47, 2, 12], [12, 26, -91, -182, 192, 324, -159, -181, 49, 26], [26, 64, -182, -455, 312, 842, -170, -523, 27, 101], [101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229], [229, 559, -1604, -3950, 2755, 7189, -1514, -4283, 248, 743], [743, 1715, -5385, -12006, 10167, 21330, -6928, -11916, 1661, 1734], [1734, 4211, -12157, -29661, 20940, 53517, -11616, -31204, 1956, 5129]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -8, -14, 19, 25, -19, -14, 8, 2], [2, 5, -14, -36, 24, 69, -13, -47, 2, 12], [12, 26, -91, -182, 192, 324, -159, -181, 49, 26], [26, 64, -182, -455, 312, 842, -170, -523, 27, 101], [101, 228, -744, -1596, 1464, 2837, -1077, -1584, 285, 229], [229, 559, -1604, -3950, 2755, 7189, -1514, -4283, 248, 743], [743, 1715, -5385, -12006, 10167, 21330, -6928, -11916, 1661, 1734], [1734, 4211, -12157, -29661, 20940, 53517, -11616, -31204, 1956, 5129], [5129, 11992, -36821, -83963, 67790, 149165, -43934, -83422, 9828, 12214]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp1277 : Fact (Nat.Prime 1277) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 3, 4, 2, 3, 1, 3]
  b' := [3, 1, 3, 0, 1, 1, 1, 3]
  k := [1, 3, 1, 0, 0, 0, 1, 2, 1]
  f := [2, 1, -1, -2, 4, 5, -2, -1, 2, 1]
  g := [3, 0, 1, 1, 0, 0, 3, 2, 0, 1]
  h := [3, 1]
  a := [0, 0, 1, 2, 3, 3, 0, 4]
  b := [2, 0, 2, 1, 2, 4, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [10, 58, 55, 45, 26, 48, 6]
  b' := [10, 45, 51, 34, 3, 21, 41, 45]
  k := [60, 16, 43, 32, 18, 16, 1]
  f := [1, 54, 101, 72, 63, 73, 87, 55, 8, 1]
  g := [1, 54, 56, 24, 42, 37, 56, 7, 1]
  h := [60, 52, 1]
  a := [43, 31, 44, 1, 2, 42, 40, 15]
  b := [19, 37, 27, 37, 3, 14, 38, 6, 46]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [259, 76, 264, 105, 339, 29, 202]
  b' := [346, 340, 184, 145, 184, 360, 151, 74]
  k := [396, 132, 305, 338, 92, 132, 1]
  f := [1, 332, 653, 318, 199, 556, 705, 380, 56, 1]
  g := [1, 332, 378, 3, 196, 394, 378, 65, 1]
  h := [396, 330, 1]
  a := [226, 278, 98, 64, 12, 350, 147, 284]
  b := [172, 184, 355, 88, 151, 64, 211, 27, 113]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1277 : CertificateDedekindCriterionLists l 1277 where
  n := 2
  a' := [566, 1220, 1244, 272, 140, 153, 795, 785]
  b' := [516, 663, 576, 1238, 1180, 1064, 1060, 1105, 906]
  k := [1, 228, 441, 274, 1088, 1003, 441, 1049, 1]
  f := [10, 20, 23, 67, 56, 69, 92, 20, 103, 1]
  g := [113, 225, 258, 755, 626, 774, 1033, 217, 1162, 1]
  h := [113, 1]
  a := [384, 631, 693, 49, 326, 1137, 688, 649, 33]
  b := [904, 698, 13, 220, 249, 805, 1156, 1096, 1244]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 61, 397, 1277]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 61, 397, 1277]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp61.out
    exact hp397.out
    exact hp1277.out
  a := [2690757629, -28954328760, 4617437536, 101388579900, -39275700650, -83423437598, 36735978600, 15456873628, -6866635360]
  b := [-1422691587, 404874055, 10771109621, -3560226694, -20278979640, 7598642470, 11689119133, -4710320918, -1683020070, 686663536]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1277 T_ofList CD1277

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

end VoightMaximalOrderD10R262

namespace VoightMaximalOrderD10R264

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3768792878125, [1, 6, 6, -20, -32, 16, 35, -3, -11, 0, 1], 1⟩
local notation "l" => [1, 6, 6, -20, -32, 16, 35, -3, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 32, -16, -35, 3, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], ![0, -1, -6, -6, 20, 32, -16, -35, 3, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], ![0, -1, -6, -6, 20, 32, -16, -35, 3, 11], ![-11, -66, -67, 214, 346, -156, -353, 17, 86, 3]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], ![0, -1, -6, -6, 20, 32, -16, -35, 3, 11], ![-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], ![-3, -29, -84, -7, 310, 298, -261, -344, 50, 86]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], ![0, -1, -6, -6, 20, 32, -16, -35, 3, 11], ![-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], ![-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], ![-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], ![0, -1, -6, -6, 20, 32, -16, -35, 3, 11], ![-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], ![-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], ![-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50], ![-50, -386, -819, 455, 3236, 1945, -2816, -2562, 547, 602]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], ![0, -1, -6, -6, 20, 32, -16, -35, 3, 11], ![-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], ![-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], ![-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50], ![-50, -386, -819, 455, 3236, 1945, -2816, -2562, 547, 602], ![-602, -3662, -3998, 11221, 19719, -6396, -19125, -1010, 4060, 547]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], ![0, -1, -6, -6, 20, 32, -16, -35, 3, 11], ![-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], ![-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], ![-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50], ![-50, -386, -819, 455, 3236, 1945, -2816, -2562, 547, 602], ![-602, -3662, -3998, 11221, 19719, -6396, -19125, -1010, 4060, 547], ![-547, -3884, -6944, 6942, 28725, 10967, -25541, -17484, 5007, 4060]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], ![0, -1, -6, -6, 20, 32, -16, -35, 3, 11], ![-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], ![-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], ![-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50], ![-50, -386, -819, 455, 3236, 1945, -2816, -2562, 547, 602], ![-602, -3662, -3998, 11221, 19719, -6396, -19125, -1010, 4060, 547], ![-547, -3884, -6944, 6942, 28725, 10967, -25541, -17484, 5007, 4060], ![-4060, -24907, -28244, 74256, 136862, -36235, -131133, -13361, 27176, 5007]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-86, -3, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-86, -3, -11, 0, -1], [-50, -86, -3, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-86, -3, -11, 0, -1], [-50, -86, -3, -11, 0, -1], [-602, -50, -86, -3, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-86, -3, -11, 0, -1], [-50, -86, -3, -11, 0, -1], [-602, -50, -86, -3, -11, 0, -1], [-547, -602, -50, -86, -3, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-86, -3, -11, 0, -1], [-50, -86, -3, -11, 0, -1], [-602, -50, -86, -3, -11, 0, -1], [-547, -602, -50, -86, -3, -11, 0, -1], [-4060, -547, -602, -50, -86, -3, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 32, -16, -35, 3, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], [0, -1, -6, -6, 20, 32, -16, -35, 3, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], [0, -1, -6, -6, 20, 32, -16, -35, 3, 11], [-11, -66, -67, 214, 346, -156, -353, 17, 86, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], [0, -1, -6, -6, 20, 32, -16, -35, 3, 11], [-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], [-3, -29, -84, -7, 310, 298, -261, -344, 50, 86]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], [0, -1, -6, -6, 20, 32, -16, -35, 3, 11], [-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], [-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], [-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], [0, -1, -6, -6, 20, 32, -16, -35, 3, 11], [-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], [-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], [-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50], [-50, -386, -819, 455, 3236, 1945, -2816, -2562, 547, 602]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], [0, -1, -6, -6, 20, 32, -16, -35, 3, 11], [-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], [-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], [-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50], [-50, -386, -819, 455, 3236, 1945, -2816, -2562, 547, 602], [-602, -3662, -3998, 11221, 19719, -6396, -19125, -1010, 4060, 547]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], [0, -1, -6, -6, 20, 32, -16, -35, 3, 11], [-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], [-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], [-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50], [-50, -386, -819, 455, 3236, 1945, -2816, -2562, 547, 602], [-602, -3662, -3998, 11221, 19719, -6396, -19125, -1010, 4060, 547], [-547, -3884, -6944, 6942, 28725, 10967, -25541, -17484, 5007, 4060]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 32, -16, -35, 3, 11, 0], [0, -1, -6, -6, 20, 32, -16, -35, 3, 11], [-11, -66, -67, 214, 346, -156, -353, 17, 86, 3], [-3, -29, -84, -7, 310, 298, -261, -344, 50, 86], [-86, -519, -545, 1636, 2745, -1066, -2712, -3, 602, 50], [-50, -386, -819, 455, 3236, 1945, -2816, -2562, 547, 602], [-602, -3662, -3998, 11221, 19719, -6396, -19125, -1010, 4060, 547], [-547, -3884, -6944, 6942, 28725, 10967, -25541, -17484, 5007, 4060], [-4060, -24907, -28244, 74256, 136862, -36235, -131133, -13361, 27176, 5007]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp109637611 : Fact (Nat.Prime 109637611) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 2]
  b' := [0, 0, 1, 3, 3]
  k := [1]
  f := [0, 0, 1, 6, 9, -2, -5, 1, 3]
  g := [1, 3, 1, 2, 0, 1]
  h := [1, 3, 1, 2, 0, 1]
  a := [4, 4, 0, 1]
  b := [1, 2, 4, 1, 4, 4, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [2, 3, 1, 2, 9, 8, 1, 1]
  b' := [8, 2, 10, 7, 2, 3, 3, 7, 6]
  k := [9, 0, 6, 4, 8, 5, 4, 3, 1]
  f := [1, 3, 1, 2, 4, 1, 1, 3, 4, 1]
  g := [3, 9, 2, 0, 3, 6, 10, 5, 7, 1]
  h := [4, 1]
  a := [1, 4, 9, 8, 10, 9, 8, 5, 7]
  b := [0, 5, 7, 6, 3, 6, 6, 5, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD109637611 : CertificateDedekindCriterionLists l 109637611 where
  n := 2
  a' := [11775510, 91022571, 68480474, 25702324, 34839941, 5667790, 68815283, 6012122]
  b' := [19657452, 20303322, 6545446, 60441322, 30381671, 29477905, 39284160, 52408483, 23695900]
  k := [100790789, 13899802, 96685812, 28583737, 99200735, 66360296, 47987442, 87735212, 1]
  f := [27241859, 37218224, 43663239, 8806948, 29824856, 23160311, 46084200, 31518987, 26315538, 1]
  g := [45411770, 62042220, 72785963, 14681049, 49717587, 38607890, 76821669, 52541677, 43867606, 1]
  h := [65770005, 1]
  a := [59978880, 67360037, 88835829, 36841724, 404356, 104910791, 2021412, 74189366, 4549340]
  b := [10593768, 62839026, 36684877, 91629090, 84703376, 103375230, 37859027, 82378344, 105088271]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 109637611]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 109637611]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp109637611.out
  a := [-2112283562909, 1109540568876, 17815070616540, 1397433868524, -29634752905790, -2604068404210, 12678873307220, 669434794900, -1478627777900]
  b := [353052271919, 1221255590925, -878423904717, -4697276520244, 115980200771, 5020532060754, 274605995288, -1593185441860, -66943479490, 147862777790]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 109637611 T_ofList CD109637611

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

end VoightMaximalOrderD10R264

namespace VoightMaximalOrderD10R265

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3773288593664, [-1, -5, 3, 28, -6, -42, 9, 21, -6, -3, 1], 1⟩
local notation "l" => [-1, -5, 3, 28, -6, -42, 9, 21, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -28, 6, 42, -9, -21, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -28, 6, 42, -9, -21, 6, 3], ![3, 16, -4, -87, -10, 132, 15, -72, -3, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -28, 6, 42, -9, -21, 6, 3], ![3, 16, -4, -87, -10, 132, 15, -72, -3, 15], ![15, 78, -29, -424, 3, 620, -3, -300, 18, 42]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -28, 6, 42, -9, -21, 6, 3], ![3, 16, -4, -87, -10, 132, 15, -72, -3, 15], ![15, 78, -29, -424, 3, 620, -3, -300, 18, 42], ![42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -28, 6, 42, -9, -21, 6, 3], ![3, 16, -4, -87, -10, 132, 15, -72, -3, 15], ![15, 78, -29, -424, 3, 620, -3, -300, 18, 42], ![42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], ![144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -28, 6, 42, -9, -21, 6, 3], ![3, 16, -4, -87, -10, 132, 15, -72, -3, 15], ![15, 78, -29, -424, 3, 620, -3, -300, 18, 42], ![42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], ![144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384], ![384, 2064, -390, -10959, -1776, 15787, 2420, -7593, -478, 1131]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -28, 6, 42, -9, -21, 6, 3], ![3, 16, -4, -87, -10, 132, 15, -72, -3, 15], ![15, 78, -29, -424, 3, 620, -3, -300, 18, 42], ![42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], ![144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384], ![384, 2064, -390, -10959, -1776, 15787, 2420, -7593, -478, 1131], ![1131, 6039, -1329, -32058, -4173, 45726, 5608, -21331, -807, 2915]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -28, 6, 42, -9, -21, 6, 3], ![3, 16, -4, -87, -10, 132, 15, -72, -3, 15], ![15, 78, -29, -424, 3, 620, -3, -300, 18, 42], ![42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], ![144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384], ![384, 2064, -390, -10959, -1776, 15787, 2420, -7593, -478, 1131], ![1131, 6039, -1329, -32058, -4173, 45726, 5608, -21331, -807, 2915], ![2915, 15706, -2706, -82949, -14568, 118257, 19491, -55607, -3841, 7938]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -28, 6, 42, -9, -21, 6, 3], ![3, 16, -4, -87, -10, 132, 15, -72, -3, 15], ![15, 78, -29, -424, 3, 620, -3, -300, 18, 42], ![42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], ![144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384], ![384, 2064, -390, -10959, -1776, 15787, 2420, -7593, -478, 1131], ![1131, 6039, -1329, -32058, -4173, 45726, 5608, -21331, -807, 2915], ![2915, 15706, -2706, -82949, -14568, 118257, 19491, -55607, -3841, 7938], ![7938, 42605, -8108, -224970, -35321, 318828, 46815, -147207, -7979, 19973]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1], [-384, -144, -42, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1], [-384, -144, -42, -15, -3, -1], [-1131, -384, -144, -42, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1], [-384, -144, -42, -15, -3, -1], [-1131, -384, -144, -42, -15, -3, -1], [-2915, -1131, -384, -144, -42, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-144, -42, -15, -3, -1], [-384, -144, -42, -15, -3, -1], [-1131, -384, -144, -42, -15, -3, -1], [-2915, -1131, -384, -144, -42, -15, -3, -1], [-7938, -2915, -1131, -384, -144, -42, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -28, 6, 42, -9, -21, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -28, 6, 42, -9, -21, 6, 3], [3, 16, -4, -87, -10, 132, 15, -72, -3, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -28, 6, 42, -9, -21, 6, 3], [3, 16, -4, -87, -10, 132, 15, -72, -3, 15], [15, 78, -29, -424, 3, 620, -3, -300, 18, 42]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -28, 6, 42, -9, -21, 6, 3], [3, 16, -4, -87, -10, 132, 15, -72, -3, 15], [15, 78, -29, -424, 3, 620, -3, -300, 18, 42], [42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -28, 6, 42, -9, -21, 6, 3], [3, 16, -4, -87, -10, 132, 15, -72, -3, 15], [15, 78, -29, -424, 3, 620, -3, -300, 18, 42], [42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], [144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -28, 6, 42, -9, -21, 6, 3], [3, 16, -4, -87, -10, 132, 15, -72, -3, 15], [15, 78, -29, -424, 3, 620, -3, -300, 18, 42], [42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], [144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384], [384, 2064, -390, -10959, -1776, 15787, 2420, -7593, -478, 1131]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -28, 6, 42, -9, -21, 6, 3], [3, 16, -4, -87, -10, 132, 15, -72, -3, 15], [15, 78, -29, -424, 3, 620, -3, -300, 18, 42], [42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], [144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384], [384, 2064, -390, -10959, -1776, 15787, 2420, -7593, -478, 1131], [1131, 6039, -1329, -32058, -4173, 45726, 5608, -21331, -807, 2915]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -28, 6, 42, -9, -21, 6, 3], [3, 16, -4, -87, -10, 132, 15, -72, -3, 15], [15, 78, -29, -424, 3, 620, -3, -300, 18, 42], [42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], [144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384], [384, 2064, -390, -10959, -1776, 15787, 2420, -7593, -478, 1131], [1131, 6039, -1329, -32058, -4173, 45726, 5608, -21331, -807, 2915], [2915, 15706, -2706, -82949, -14568, 118257, 19491, -55607, -3841, 7938]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -28, 6, 42, -9, -21, 6, 3], [3, 16, -4, -87, -10, 132, 15, -72, -3, 15], [15, 78, -29, -424, 3, 620, -3, -300, 18, 42], [42, 225, -48, -1205, -172, 1767, 242, -885, -48, 144], [144, 762, -207, -4080, -341, 5876, 471, -2782, -21, 384], [384, 2064, -390, -10959, -1776, 15787, 2420, -7593, -478, 1131], [1131, 6039, -1329, -32058, -4173, 45726, 5608, -21331, -807, 2915], [2915, 15706, -2706, -82949, -14568, 118257, 19491, -55607, -3841, 7938], [7938, 42605, -8108, -224970, -35321, 318828, 46815, -147207, -7979, 19973]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp317 : Fact (Nat.Prime 317) := fact_iff.2 (by norm_num)
instance hp46496557 : Fact (Nat.Prime 46496557) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [0, 1, 1, 0, 1]
  k := [1, 1, 1]
  f := [1, 3, -1, -13, 4, 22, -3, -10, 3, 2]
  g := [1, 1, 1, 1, 0, 0, 1]
  h := [1, 0, 0, 1, 1]
  a := [0, 1, 1, 1, 1]
  b := [1, 0, 1, 1, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD317 : CertificateDedekindCriterionLists l 317 where
  n := 2
  a' := [316, 213, 220, 155, 130, 105, 55, 274]
  b' := [109, 246, 51, 97, 7, 309, 280, 79, 40]
  k := [9, 229, 16, 58, 151, 7, 294, 73, 1]
  f := [257, 162, 225, 28, 23, 178, 218, 50, 31, 1]
  g := [292, 183, 255, 31, 26, 202, 247, 56, 35, 1]
  h := [279, 1]
  a := [18, 83, 259, 198, 267, 191, 135, 154, 289]
  b := [185, 29, 98, 195, 235, 307, 112, 51, 28]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD46496557 : CertificateDedekindCriterionLists l 46496557 where
  n := 2
  a' := [15266428, 22486615, 35973822, 44849234, 22437595, 15827495, 25752188, 41555673]
  b' := [28841742, 17592591, 907735, 9770743, 21436215, 2638531, 39345085, 3963544, 41879260]
  k := [17570299, 3808533, 44955303, 16002270, 42747556, 37483292, 42584566, 7794441, 1]
  f := [28118933, 39298394, 1452547, 33690045, 41754861, 27464546, 36013207, 37834066, 3570565, 1]
  g := [30691408, 42893627, 1585433, 36772196, 45574825, 29977153, 39307893, 41295334, 3897219, 1]
  h := [42599335, 1]
  a := [22127554, 31032683, 32517492, 23519693, 11067342, 39156635, 22871182, 39565832, 34773694]
  b := [20217339, 4236745, 338687, 22787181, 7842261, 13084811, 30949733, 3785172, 11722863]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 317, 46496557]
  exp := ![1, 1, 1]
  pdgood := [2, 317, 46496557]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp317.out
    exact hp46496557.out
  a := [224093000077, -1102431523623, -533870634495, 3495586728748, -212387115468, -2687286007275, 700185584773, 513022262067, -175148017710]
  b := [-50714363443, -64463931484, 414303426945, 85814182932, -713255090809, 54943140795, 382920750342, -89832642175, -56556666738, 17514801771]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 317 T_ofList CD317
    exact satisfiesDedekindCriterion_of_certificate_lists T l 46496557 T_ofList CD46496557

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

end VoightMaximalOrderD10R265

namespace VoightMaximalOrderD10R266

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3784829003125, [1, -14, -7, 49, 7, -58, 6, 26, -7, -3, 1], 1⟩
local notation "l" => [1, -14, -7, 49, 7, -58, 6, 26, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, 7, -49, -7, 58, -6, -26, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], ![-3, 41, 35, -140, -70, 167, 40, -84, -5, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], ![-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], ![-16, 221, 153, -749, -252, 858, 71, -376, 28, 43]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], ![-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], ![-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], ![-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], ![-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], ![-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], ![-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], ![-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], ![-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], ![-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], ![-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], ![-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396], ![-396, 5387, 4927, -17719, -9943, 19915, 5680, -8996, -710, 1240]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], ![-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], ![-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], ![-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], ![-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396], ![-396, 5387, 4927, -17719, -9943, 19915, 5680, -8996, -710, 1240], ![-1240, 16964, 14067, -55833, -26399, 61977, 12475, -26560, -316, 3010]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], ![-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], ![-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], ![-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], ![-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396], ![-396, 5387, 4927, -17719, -9943, 19915, 5680, -8996, -710, 1240], ![-1240, 16964, 14067, -55833, -26399, 61977, 12475, -26560, -316, 3010], ![-3010, 40900, 38034, -133423, -76903, 148181, 43917, -65785, -5490, 8714]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], ![-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], ![-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], ![-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], ![-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396], ![-396, 5387, 4927, -17719, -9943, 19915, 5680, -8996, -710, 1240], ![-1240, 16964, 14067, -55833, -26399, 61977, 12475, -26560, -316, 3010], ![-3010, 40900, 38034, -133423, -76903, 148181, 43917, -65785, -5490, 8714], ![-8714, 118986, 101898, -388952, -194421, 428509, 95897, -182647, -4787, 20652]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1], [-396, -157, -43, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1], [-396, -157, -43, -16, -3, -1], [-1240, -396, -157, -43, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1], [-396, -157, -43, -16, -3, -1], [-1240, -396, -157, -43, -16, -3, -1], [-3010, -1240, -396, -157, -43, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-157, -43, -16, -3, -1], [-396, -157, -43, -16, -3, -1], [-1240, -396, -157, -43, -16, -3, -1], [-3010, -1240, -396, -157, -43, -16, -3, -1], [-8714, -3010, -1240, -396, -157, -43, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, 7, -49, -7, 58, -6, -26, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], [-3, 41, 35, -140, -70, 167, 40, -84, -5, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], [-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], [-16, 221, 153, -749, -252, 858, 71, -376, 28, 43]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], [-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], [-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], [-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], [-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], [-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], [-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], [-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], [-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], [-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], [-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], [-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396], [-396, 5387, 4927, -17719, -9943, 19915, 5680, -8996, -710, 1240]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], [-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], [-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], [-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], [-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396], [-396, 5387, 4927, -17719, -9943, 19915, 5680, -8996, -710, 1240], [-1240, 16964, 14067, -55833, -26399, 61977, 12475, -26560, -316, 3010]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], [-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], [-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], [-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], [-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396], [-396, 5387, 4927, -17719, -9943, 19915, 5680, -8996, -710, 1240], [-1240, 16964, 14067, -55833, -26399, 61977, 12475, -26560, -316, 3010], [-3010, 40900, 38034, -133423, -76903, 148181, 43917, -65785, -5490, 8714]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, 7, -49, -7, 58, -6, -26, 7, 3], [-3, 41, 35, -140, -70, 167, 40, -84, -5, 16], [-16, 221, 153, -749, -252, 858, 71, -376, 28, 43], [-43, 586, 522, -1954, -1050, 2242, 600, -1047, -75, 157], [-157, 2155, 1685, -7171, -3053, 8056, 1300, -3482, 52, 396], [-396, 5387, 4927, -17719, -9943, 19915, 5680, -8996, -710, 1240], [-1240, 16964, 14067, -55833, -26399, 61977, 12475, -26560, -316, 3010], [-3010, 40900, 38034, -133423, -76903, 148181, 43917, -65785, -5490, 8714], [-8714, 118986, 101898, -388952, -194421, 428509, 95897, -182647, -4787, 20652]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp491 : Fact (Nat.Prime 491) := fact_iff.2 (by norm_num)
instance hp2466691 : Fact (Nat.Prime 2466691) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 3, 2]
  b' := [3, 3, 3, 1, 2]
  k := [1]
  f := [0, 4, 4, -7, 1, 14, 1, -4, 2, 1]
  g := [1, 3, 2, 1, 1, 1]
  h := [1, 3, 2, 1, 1, 1]
  a := [2, 2, 3, 2, 4]
  b := [1, 4, 0, 0, 2, 1, 4, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD491 : CertificateDedekindCriterionLists l 491 where
  n := 2
  a' := [310, 247, 57, 78, 279, 359, 343, 169]
  b' := [249, 430, 142, 247, 302, 20, 186, 255, 254]
  k := [305, 261, 412, 321, 378, 386, 341, 306, 1]
  f := [48, 91, 82, 31, 65, 29, 90, 38, 74, 1]
  g := [259, 488, 437, 163, 349, 152, 484, 200, 397, 1]
  h := [91, 1]
  a := [469, 413, 161, 106, 392, 2, 183, 209, 416]
  b := [442, 342, 167, 186, 392, 160, 290, 116, 75]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2466691 : CertificateDedekindCriterionLists l 2466691 where
  n := 2
  a' := [652546, 1710209, 409206, 545004, 1230363, 44458, 588456, 2122783]
  b' := [2125827, 1632975, 678938, 683195, 439950, 1095619, 1782361, 942330, 38212]
  k := [1895880, 2161992, 1689844, 1516555, 367215, 1383275, 738638, 2242525, 1]
  f := [1333441, 479147, 5746, 548499, 846464, 1204355, 1066294, 868139, 611579, 1]
  g := [2444716, 878461, 10534, 1005612, 1551897, 2208050, 1954930, 1591635, 1121261, 1]
  h := [1345427, 1]
  a := [2037956, 993349, 792383, 305977, 1847754, 1647693, 2353883, 974632, 2274143]
  b := [194296, 285, 2353089, 2443590, 120778, 1115395, 171006, 543758, 192548]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 491, 2466691]
  exp := ![1, 1, 1]
  pdgood := [5, 491, 2466691]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp491.out
    exact hp2466691.out
  a := [-6223635697, -92123242358, 23165158464, 799973516986, -365380415420, -794477500886, 390865874294, 134281144600, -66346896600]
  b := [-877097293, 520501393, 87159691413, -25193918098, -203617738774, 69809105016, 121864966792, -49720817240, -15418521358, 6634689660]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 491 T_ofList CD491
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2466691 T_ofList CD2466691

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

end VoightMaximalOrderD10R266

end TraceEuclidean
