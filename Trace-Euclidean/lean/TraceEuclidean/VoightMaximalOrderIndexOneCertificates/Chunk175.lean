import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk171
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

namespace VoightMaximalOrderD10R84

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1958895690625, [-1, -3, 15, 13, -35, -16, 28, 7, -9, -1, 1], 1⟩
local notation "l" => [-1, -3, 15, 13, -35, -16, 28, 7, -9, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -15, -13, 35, 16, -28, -7, 9, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -15, -13, 35, 16, -28, -7, 9, 1], ![1, 4, -12, -28, 22, 51, -12, -35, 2, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -15, -13, 35, 16, -28, -7, 9, 1], ![1, 4, -12, -28, 22, 51, -12, -35, 2, 10], ![10, 31, -146, -142, 322, 182, -229, -82, 55, 12]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -15, -13, 35, 16, -28, -7, 9, 1], ![1, 4, -12, -28, 22, 51, -12, -35, 2, 10], ![10, 31, -146, -142, 322, 182, -229, -82, 55, 12], ![12, 46, -149, -302, 278, 514, -154, -313, 26, 67]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -15, -13, 35, 16, -28, -7, 9, 1], ![1, 4, -12, -28, 22, 51, -12, -35, 2, 10], ![10, 31, -146, -142, 322, 182, -229, -82, 55, 12], ![12, 46, -149, -302, 278, 514, -154, -313, 26, 67], ![67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -15, -13, 35, 16, -28, -7, 9, 1], ![1, 4, -12, -28, 22, 51, -12, -35, 2, 10], ![10, 31, -146, -142, 322, 182, -229, -82, 55, 12], ![12, 46, -149, -302, 278, 514, -154, -313, 26, 67], ![67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93], ![93, 346, -1182, -2168, 2235, 3531, -1254, -2013, 214, 383]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -15, -13, 35, 16, -28, -7, 9, 1], ![1, 4, -12, -28, 22, 51, -12, -35, 2, 10], ![10, 31, -146, -142, 322, 182, -229, -82, 55, 12], ![12, 46, -149, -302, 278, 514, -154, -313, 26, 67], ![67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93], ![93, 346, -1182, -2168, 2235, 3531, -1254, -2013, 214, 383], ![383, 1242, -5399, -6161, 11237, 8363, -7193, -3935, 1434, 597]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -15, -13, 35, 16, -28, -7, 9, 1], ![1, 4, -12, -28, 22, 51, -12, -35, 2, 10], ![10, 31, -146, -142, 322, 182, -229, -82, 55, 12], ![12, 46, -149, -302, 278, 514, -154, -313, 26, 67], ![67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93], ![93, 346, -1182, -2168, 2235, 3531, -1254, -2013, 214, 383], ![383, 1242, -5399, -6161, 11237, 8363, -7193, -3935, 1434, 597], ![597, 2174, -7713, -13160, 14734, 20789, -8353, -11372, 1438, 2031]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -15, -13, 35, 16, -28, -7, 9, 1], ![1, 4, -12, -28, 22, 51, -12, -35, 2, 10], ![10, 31, -146, -142, 322, 182, -229, -82, 55, 12], ![12, 46, -149, -302, 278, 514, -154, -313, 26, 67], ![67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93], ![93, 346, -1182, -2168, 2235, 3531, -1254, -2013, 214, 383], ![383, 1242, -5399, -6161, 11237, 8363, -7193, -3935, 1434, 597], ![597, 2174, -7713, -13160, 14734, 20789, -8353, -11372, 1438, 2031], ![2031, 6690, -28291, -34116, 57925, 47230, -36079, -22570, 6907, 3469]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-10, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-67, -12, -10, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-67, -12, -10, -1, -1], [-93, -67, -12, -10, -1, -1]], ![[], [], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-67, -12, -10, -1, -1], [-93, -67, -12, -10, -1, -1], [-383, -93, -67, -12, -10, -1, -1]], ![[], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-67, -12, -10, -1, -1], [-93, -67, -12, -10, -1, -1], [-383, -93, -67, -12, -10, -1, -1], [-597, -383, -93, -67, -12, -10, -1, -1]], ![[], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-67, -12, -10, -1, -1], [-93, -67, -12, -10, -1, -1], [-383, -93, -67, -12, -10, -1, -1], [-597, -383, -93, -67, -12, -10, -1, -1], [-2031, -597, -383, -93, -67, -12, -10, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -15, -13, 35, 16, -28, -7, 9, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -15, -13, 35, 16, -28, -7, 9, 1], [1, 4, -12, -28, 22, 51, -12, -35, 2, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -15, -13, 35, 16, -28, -7, 9, 1], [1, 4, -12, -28, 22, 51, -12, -35, 2, 10], [10, 31, -146, -142, 322, 182, -229, -82, 55, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -15, -13, 35, 16, -28, -7, 9, 1], [1, 4, -12, -28, 22, 51, -12, -35, 2, 10], [10, 31, -146, -142, 322, 182, -229, -82, 55, 12], [12, 46, -149, -302, 278, 514, -154, -313, 26, 67]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -15, -13, 35, 16, -28, -7, 9, 1], [1, 4, -12, -28, 22, 51, -12, -35, 2, 10], [10, 31, -146, -142, 322, 182, -229, -82, 55, 12], [12, 46, -149, -302, 278, 514, -154, -313, 26, 67], [67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -15, -13, 35, 16, -28, -7, 9, 1], [1, 4, -12, -28, 22, 51, -12, -35, 2, 10], [10, 31, -146, -142, 322, 182, -229, -82, 55, 12], [12, 46, -149, -302, 278, 514, -154, -313, 26, 67], [67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93], [93, 346, -1182, -2168, 2235, 3531, -1254, -2013, 214, 383]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -15, -13, 35, 16, -28, -7, 9, 1], [1, 4, -12, -28, 22, 51, -12, -35, 2, 10], [10, 31, -146, -142, 322, 182, -229, -82, 55, 12], [12, 46, -149, -302, 278, 514, -154, -313, 26, 67], [67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93], [93, 346, -1182, -2168, 2235, 3531, -1254, -2013, 214, 383], [383, 1242, -5399, -6161, 11237, 8363, -7193, -3935, 1434, 597]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -15, -13, 35, 16, -28, -7, 9, 1], [1, 4, -12, -28, 22, 51, -12, -35, 2, 10], [10, 31, -146, -142, 322, 182, -229, -82, 55, 12], [12, 46, -149, -302, 278, 514, -154, -313, 26, 67], [67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93], [93, 346, -1182, -2168, 2235, 3531, -1254, -2013, 214, 383], [383, 1242, -5399, -6161, 11237, 8363, -7193, -3935, 1434, 597], [597, 2174, -7713, -13160, 14734, 20789, -8353, -11372, 1438, 2031]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -15, -13, 35, 16, -28, -7, 9, 1], [1, 4, -12, -28, 22, 51, -12, -35, 2, 10], [10, 31, -146, -142, 322, 182, -229, -82, 55, 12], [12, 46, -149, -302, 278, 514, -154, -313, 26, 67], [67, 213, -959, -1020, 2043, 1350, -1362, -623, 290, 93], [93, 346, -1182, -2168, 2235, 3531, -1254, -2013, 214, 383], [383, 1242, -5399, -6161, 11237, 8363, -7193, -3935, 1434, 597], [597, 2174, -7713, -13160, 14734, 20789, -8353, -11372, 1438, 2031], [2031, 6690, -28291, -34116, 57925, 47230, -36079, -22570, 6907, 3469]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp59 : Fact (Nat.Prime 59) := fact_iff.2 (by norm_num)
instance hp181 : Fact (Nat.Prime 181) := fact_iff.2 (by norm_num)
instance hp58699 : Fact (Nat.Prime 58699) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 3]
  b' := [2, 1, 4, 4]
  k := [1]
  f := [1, 3, 2, 3, 13, 8, -1, 1, 3, 1]
  g := [2, 3, 4, 1, 2, 1]
  h := [2, 3, 4, 1, 2, 1]
  a := [0, 3]
  b := [3, 4, 1, 1, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD59 : CertificateDedekindCriterionLists l 59 where
  n := 2
  a' := [48, 39, 45, 34, 1, 32, 57, 36]
  b' := [1, 58, 19, 23, 16, 37, 38, 49, 55]
  k := [38, 9, 34, 18, 57, 43, 19, 47, 1]
  f := [19, 35, 12, 9, 5, 17, 0, 7, 14, 1]
  g := [32, 58, 19, 15, 7, 28, 0, 12, 23, 1]
  h := [35, 1]
  a := [37, 18, 24, 0, 28, 51, 38, 54, 36]
  b := [26, 40, 56, 57, 33, 0, 20, 34, 23]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD181 : CertificateDedekindCriterionLists l 181 where
  n := 2
  a' := [150, 100, 95, 129, 164, 150, 21, 77]
  b' := [146, 170, 82, 155, 14, 117, 142, 78, 92]
  k := [172, 100, 92, 131, 5, 155, 51, 60, 1]
  f := [1, 6, 3, 56, 24, 25, 46, 11, 40, 1]
  g := [3, 18, 9, 169, 69, 74, 138, 31, 120, 1]
  h := [60, 1]
  a := [48, 118, 43, 109, 134, 5, 116, 60, 107]
  b := [105, 19, 57, 31, 83, 118, 102, 174, 74]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD58699 : CertificateDedekindCriterionLists l 58699 where
  n := 2
  a' := [16615, 2588, 662, 25287, 14155, 57471, 36245, 43756]
  b' := [43441, 48932, 46783, 4614, 21821, 8589, 12514, 26213, 40793]
  k := [19226, 38006, 29068, 33014, 20026, 5320, 41027, 14270, 1]
  f := [19353, 6356, 2596, 6342, 4109, 14161, 6973, 571, 13807, 1]
  g := [51139, 16793, 6859, 16758, 10857, 37419, 18424, 1508, 36484, 1]
  h := [22214, 1]
  a := [45020, 39098, 1076, 4003, 46391, 49390, 7602, 20983, 58177]
  b := [22688, 2439, 32791, 19751, 36490, 52496, 45827, 57520, 522]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 59, 181, 58699]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 59, 181, 58699]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp59.out
    exact hp181.out
    exact hp58699.out
  a := [-2534783935, -4958546598, 27605509398, 18761267452, -44800699994, -14370972686, 22478507418, 3017170264, -3433847560]
  b := [-199816390, 2189468901, 2379866397, -8049537374, -4118598706, 7923833522, 2121901016, -2866676228, -336055502, 343384756]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 59 T_ofList CD59
    exact satisfiesDedekindCriterion_of_certificate_lists T l 181 T_ofList CD181
    exact satisfiesDedekindCriterion_of_certificate_lists T l 58699 T_ofList CD58699

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

end VoightMaximalOrderD10R84

namespace VoightMaximalOrderD10R88

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1989143628125, [-1, -1, 12, 13, -30, -22, 26, 12, -9, -2, 1], 1⟩
local notation "l" => [-1, -1, 12, 13, -30, -22, 26, 12, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -13, 30, 22, -26, -12, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -13, 30, 22, -26, -12, 9, 2], ![2, 3, -23, -38, 47, 74, -30, -50, 6, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -13, 30, 22, -26, -12, 9, 2], ![2, 3, -23, -38, 47, 74, -30, -50, 6, 13], ![13, 15, -153, -192, 352, 333, -264, -186, 67, 32]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -13, 30, 22, -26, -12, 9, 2], ![2, 3, -23, -38, 47, 74, -30, -50, 6, 13], ![13, 15, -153, -192, 352, 333, -264, -186, 67, 32], ![32, 45, -369, -569, 768, 1056, -499, -648, 102, 131]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -13, 30, 22, -26, -12, 9, 2], ![2, 3, -23, -38, 47, 74, -30, -50, 6, 13], ![13, 15, -153, -192, 352, 333, -264, -186, 67, 32], ![32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], ![131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -13, 30, 22, -26, -12, 9, 2], ![2, 3, -23, -38, 47, 74, -30, -50, 6, 13], ![13, 15, -153, -192, 352, 333, -264, -186, 67, 32], ![32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], ![131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364], ![364, 495, -4205, -6259, 8848, 11369, -5814, -6718, 1205, 1259]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -13, 30, 22, -26, -12, 9, 2], ![2, 3, -23, -38, 47, 74, -30, -50, 6, 13], ![13, 15, -153, -192, 352, 333, -264, -186, 67, 32], ![32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], ![131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364], ![364, 495, -4205, -6259, 8848, 11369, -5814, -6718, 1205, 1259], ![1259, 1623, -14613, -20572, 31511, 36546, -21365, -20922, 4613, 3723]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -13, 30, 22, -26, -12, 9, 2], ![2, 3, -23, -38, 47, 74, -30, -50, 6, 13], ![13, 15, -153, -192, 352, 333, -264, -186, 67, 32], ![32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], ![131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364], ![364, 495, -4205, -6259, 8848, 11369, -5814, -6718, 1205, 1259], ![1259, 1623, -14613, -20572, 31511, 36546, -21365, -20922, 4613, 3723], ![3723, 4982, -43053, -63012, 91118, 113417, -60252, -66041, 12585, 12059]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -13, 30, 22, -26, -12, 9, 2], ![2, 3, -23, -38, 47, 74, -30, -50, 6, 13], ![13, 15, -153, -192, 352, 333, -264, -186, 67, 32], ![32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], ![131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364], ![364, 495, -4205, -6259, 8848, 11369, -5814, -6718, 1205, 1259], ![1259, 1623, -14613, -20572, 31511, 36546, -21365, -20922, 4613, 3723], ![3723, 4982, -43053, -63012, 91118, 113417, -60252, -66041, 12585, 12059], ![12059, 15782, -139726, -199820, 298758, 356416, -200117, -204960, 42490, 36703]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-32, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-32, -13, -2, -1], [-131, -32, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-32, -13, -2, -1], [-131, -32, -13, -2, -1], [-364, -131, -32, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-32, -13, -2, -1], [-131, -32, -13, -2, -1], [-364, -131, -32, -13, -2, -1], [-1259, -364, -131, -32, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-32, -13, -2, -1], [-131, -32, -13, -2, -1], [-364, -131, -32, -13, -2, -1], [-1259, -364, -131, -32, -13, -2, -1], [-3723, -1259, -364, -131, -32, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-32, -13, -2, -1], [-131, -32, -13, -2, -1], [-364, -131, -32, -13, -2, -1], [-1259, -364, -131, -32, -13, -2, -1], [-3723, -1259, -364, -131, -32, -13, -2, -1], [-12059, -3723, -1259, -364, -131, -32, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -13, 30, 22, -26, -12, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -13, 30, 22, -26, -12, 9, 2], [2, 3, -23, -38, 47, 74, -30, -50, 6, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -13, 30, 22, -26, -12, 9, 2], [2, 3, -23, -38, 47, 74, -30, -50, 6, 13], [13, 15, -153, -192, 352, 333, -264, -186, 67, 32]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -13, 30, 22, -26, -12, 9, 2], [2, 3, -23, -38, 47, 74, -30, -50, 6, 13], [13, 15, -153, -192, 352, 333, -264, -186, 67, 32], [32, 45, -369, -569, 768, 1056, -499, -648, 102, 131]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -13, 30, 22, -26, -12, 9, 2], [2, 3, -23, -38, 47, 74, -30, -50, 6, 13], [13, 15, -153, -192, 352, 333, -264, -186, 67, 32], [32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], [131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -13, 30, 22, -26, -12, 9, 2], [2, 3, -23, -38, 47, 74, -30, -50, 6, 13], [13, 15, -153, -192, 352, 333, -264, -186, 67, 32], [32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], [131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364], [364, 495, -4205, -6259, 8848, 11369, -5814, -6718, 1205, 1259]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -13, 30, 22, -26, -12, 9, 2], [2, 3, -23, -38, 47, 74, -30, -50, 6, 13], [13, 15, -153, -192, 352, 333, -264, -186, 67, 32], [32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], [131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364], [364, 495, -4205, -6259, 8848, 11369, -5814, -6718, 1205, 1259], [1259, 1623, -14613, -20572, 31511, 36546, -21365, -20922, 4613, 3723]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -13, 30, 22, -26, -12, 9, 2], [2, 3, -23, -38, 47, 74, -30, -50, 6, 13], [13, 15, -153, -192, 352, 333, -264, -186, 67, 32], [32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], [131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364], [364, 495, -4205, -6259, 8848, 11369, -5814, -6718, 1205, 1259], [1259, 1623, -14613, -20572, 31511, 36546, -21365, -20922, 4613, 3723], [3723, 4982, -43053, -63012, 91118, 113417, -60252, -66041, 12585, 12059]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -13, 30, 22, -26, -12, 9, 2], [2, 3, -23, -38, 47, 74, -30, -50, 6, 13], [13, 15, -153, -192, 352, 333, -264, -186, 67, 32], [32, 45, -369, -569, 768, 1056, -499, -648, 102, 131], [131, 163, -1527, -2072, 3361, 3650, -2350, -2071, 531, 364], [364, 495, -4205, -6259, 8848, 11369, -5814, -6718, 1205, 1259], [1259, 1623, -14613, -20572, 31511, 36546, -21365, -20922, 4613, 3723], [3723, 4982, -43053, -63012, 91118, 113417, -60252, -66041, 12585, 12059], [12059, 15782, -139726, -199820, 298758, 356416, -200117, -204960, 42490, 36703]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp636525961 : Fact (Nat.Prime 636525961) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 1, 3]
  b' := [2, 1, 1, 2, 2]
  k := [1]
  f := [2, 5, 2, -1, 11, 12, -2, -2, 5, 2]
  g := [3, 4, 1, 0, 4, 1]
  h := [3, 4, 1, 0, 4, 1]
  a := [1, 2, 2, 3, 2]
  b := [3, 3, 3, 2, 0, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD636525961 : CertificateDedekindCriterionLists l 636525961 where
  n := 2
  a' := [140312850, 294230987, 84317641, 503320219, 22404065, 219866929, 571240966, 367026590]
  b' := [500903307, 570304085, 146389698, 607142554, 98497915, 454034712, 476495698, 102804453, 525020122]
  k := [572652971, 53383428, 183028521, 304554437, 349362345, 157876932, 486836532, 322310555, 1]
  f := [8085217, 23850385, 61379618, 115473523, 66551311, 41408183, 111511058, 65905365, 118330289, 1]
  g := [32757468, 96630458, 248681126, 467843995, 269634373, 167766334, 451789965, 267017306, 479418257, 1]
  h := [157107702, 1]
  a := [133076896, 64192492, 418006622, 163783221, 622391749, 207666254, 80575475, 542608547, 502033490]
  b := [28951167, 54257466, 196227845, 336692734, 573370793, 511677142, 86949258, 280219754, 134492471]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 636525961]
  exp := ![1, 1]
  pdgood := [5, 636525961]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp636525961.out
  a := [6067600067, -242044511262, 207117562432, 664278858654, -435294372318, -507927884086, 271256566642, 106304496050, -46057840800]
  b := [-9250229872, 13971394267, 82292647034, -67116265490, -132599549122, 80014601734, 71220895998, -34948060356, -11551606421, 4605784080]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 636525961 T_ofList CD636525961

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

end VoightMaximalOrderD10R88

namespace VoightMaximalOrderD10R91

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1994625941504, [1, 8, 14, -16, -39, 10, 32, -2, -10, 0, 1], 1⟩
local notation "l" => [1, 8, 14, -16, -39, 10, 32, -2, -10, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 16, 39, -10, -32, 2, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], ![0, -1, -8, -14, 16, 39, -10, -32, 2, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], ![0, -1, -8, -14, 16, 39, -10, -32, 2, 10], ![-10, -80, -141, 152, 376, -84, -281, 10, 68, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], ![0, -1, -8, -14, 16, 39, -10, -32, 2, 10], ![-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], ![-2, -26, -108, -109, 230, 356, -148, -277, 30, 68]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], ![0, -1, -8, -14, 16, 39, -10, -32, 2, 10], ![-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], ![-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], ![-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], ![0, -1, -8, -14, 16, 39, -10, -32, 2, 10], ![-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], ![-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], ![-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30], ![-30, -308, -966, -498, 2150, 2243, -1410, -1760, 288, 403]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], ![0, -1, -8, -14, 16, 39, -10, -32, 2, 10], ![-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], ![-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], ![-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30], ![-30, -308, -966, -498, 2150, 2243, -1410, -1760, 288, 403], ![-403, -3254, -5950, 5482, 15219, -1880, -10653, -604, 2270, 288]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], ![0, -1, -8, -14, 16, 39, -10, -32, 2, 10], ![-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], ![-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], ![-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30], ![-30, -308, -966, -498, 2150, 2243, -1410, -1760, 288, 403], ![-403, -3254, -5950, 5482, 15219, -1880, -10653, -604, 2270, 288], ![-288, -2707, -7286, -1342, 16714, 12339, -11096, -10077, 2276, 2270]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], ![0, -1, -8, -14, 16, 39, -10, -32, 2, 10], ![-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], ![-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], ![-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30], ![-30, -308, -966, -498, 2150, 2243, -1410, -1760, 288, 403], ![-403, -3254, -5950, 5482, 15219, -1880, -10653, -604, 2270, 288], ![-288, -2707, -7286, -1342, 16714, 12339, -11096, -10077, 2276, 2270], ![-2270, -18448, -34487, 29034, 87188, -5986, -60301, -6556, 12623, 2276]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-2, -10, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-2, -10, 0, -1], [-68, -2, -10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [-2, -10, 0, -1], [-68, -2, -10, 0, -1], [-30, -68, -2, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [-2, -10, 0, -1], [-68, -2, -10, 0, -1], [-30, -68, -2, -10, 0, -1], [-403, -30, -68, -2, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [-2, -10, 0, -1], [-68, -2, -10, 0, -1], [-30, -68, -2, -10, 0, -1], [-403, -30, -68, -2, -10, 0, -1], [-288, -403, -30, -68, -2, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [-2, -10, 0, -1], [-68, -2, -10, 0, -1], [-30, -68, -2, -10, 0, -1], [-403, -30, -68, -2, -10, 0, -1], [-288, -403, -30, -68, -2, -10, 0, -1], [-2270, -288, -403, -30, -68, -2, -10, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 16, 39, -10, -32, 2, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], [0, -1, -8, -14, 16, 39, -10, -32, 2, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], [0, -1, -8, -14, 16, 39, -10, -32, 2, 10], [-10, -80, -141, 152, 376, -84, -281, 10, 68, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], [0, -1, -8, -14, 16, 39, -10, -32, 2, 10], [-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], [-2, -26, -108, -109, 230, 356, -148, -277, 30, 68]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], [0, -1, -8, -14, 16, 39, -10, -32, 2, 10], [-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], [-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], [-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], [0, -1, -8, -14, 16, 39, -10, -32, 2, 10], [-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], [-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], [-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30], [-30, -308, -966, -498, 2150, 2243, -1410, -1760, 288, 403]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], [0, -1, -8, -14, 16, 39, -10, -32, 2, 10], [-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], [-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], [-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30], [-30, -308, -966, -498, 2150, 2243, -1410, -1760, 288, 403], [-403, -3254, -5950, 5482, 15219, -1880, -10653, -604, 2270, 288]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], [0, -1, -8, -14, 16, 39, -10, -32, 2, 10], [-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], [-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], [-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30], [-30, -308, -966, -498, 2150, 2243, -1410, -1760, 288, 403], [-403, -3254, -5950, 5482, 15219, -1880, -10653, -604, 2270, 288], [-288, -2707, -7286, -1342, 16714, 12339, -11096, -10077, 2276, 2270]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 16, 39, -10, -32, 2, 10, 0], [0, -1, -8, -14, 16, 39, -10, -32, 2, 10], [-10, -80, -141, 152, 376, -84, -281, 10, 68, 2], [-2, -26, -108, -109, 230, 356, -148, -277, 30, 68], [-68, -546, -978, 980, 2543, -450, -1820, -12, 403, 30], [-30, -308, -966, -498, 2150, 2243, -1410, -1760, 288, 403], [-403, -3254, -5950, 5482, 15219, -1880, -10653, -604, 2270, 288], [-288, -2707, -7286, -1342, 16714, 12339, -11096, -10077, 2276, 2270], [-2270, -18448, -34487, 29034, 87188, -5986, -60301, -6556, 12623, 2276]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp8695879 : Fact (Nat.Prime 8695879) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [1, 1, 0, 1]
  k := [1]
  f := [0, -4, -6, 8, 20, -4, -16, 2, 5]
  g := [1, 0, 1, 0, 0, 1]
  h := [1, 0, 1, 0, 0, 1]
  a := [1, 1, 1, 1]
  b := [1, 0, 1, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [0, 0, 0, 1, 4, 6, 1, 1]
  b' := [4, 4, 0, 1, 5, 4, 1, 0, 3]
  k := [2, 0, 3, 0, 0, 6, 2, 3, 1]
  f := [1, 0, 0, 4, 6, 0, -3, 1, 3, 1]
  g := [4, 2, 6, 3, 0, 5, 3, 1, 5, 1]
  h := [2, 1]
  a := [2, 2, 2, 6, 0, 1, 3, 5, 3]
  b := [5, 4, 4, 4, 5, 5, 5, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD8695879 : CertificateDedekindCriterionLists l 8695879 where
  n := 2
  a' := [7458281, 984956, 4086509, 7955289, 5139850, 3943535, 3343294, 1832181]
  b' := [7393071, 6036425, 1260146, 4161265, 810717, 5273183, 764650, 4434356, 5593677]
  k := [6329296, 330430, 1897667, 7291681, 3236727, 8015847, 7367017, 1599136, 1]
  f := [3063755, 2970088, 3960603, 2414333, 4092532, 7116105, 163532, 4861976, 726050, 1]
  g := [3373986, 3270834, 4361647, 2658804, 4506935, 7836670, 180090, 5354292, 799568, 1]
  h := [7896311, 1]
  a := [6338302, 5777821, 8391753, 6198277, 3473305, 2174113, 3600749, 4252504, 7440381]
  b := [7609724, 8429412, 3774935, 4982885, 7409168, 1824586, 8227548, 801117, 1255498]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 7, 8695879]
  exp := ![2, 1, 1]
  pdgood := [2, 7, 8695879]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp7.out
    exact hp8695879.out
  a := [-11001944652, 792710992, 60996189964, 3196745748, -76100305336, -4286004598, 32160081370, 1281354300, -4091056180]
  b := [1405678658, 5982980475, -1670191311, -15632630453, 99088157, 12809790088, 439407949, -4034219373, -128135430, 409105618]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 8695879 T_ofList CD8695879

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

end VoightMaximalOrderD10R91

namespace VoightMaximalOrderD10R92

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2008019565625, [1, -8, 10, 34, -35, -36, 35, 11, -11, -1, 1], 1⟩
local notation "l" => [1, -8, 10, 34, -35, -36, 35, 11, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -10, -34, 35, 36, -35, -11, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], ![-1, 7, -2, -44, 1, 71, 1, -46, 0, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], ![-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], ![-12, 95, -113, -410, 376, 433, -349, -131, 86, 12]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], ![-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], ![-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], ![-12, 84, -25, -521, 10, 808, 13, -481, 1, 98]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], ![-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], ![-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], ![-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], ![-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], ![-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], ![-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], ![-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], ![-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99], ![-99, 694, -218, -4262, 108, 6473, 73, -3711, 24, 696]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], ![-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], ![-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], ![-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], ![-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99], ![-99, 694, -218, -4262, 108, 6473, 73, -3711, 24, 696], ![-696, 5469, -6266, -23882, 20098, 25164, -17887, -7583, 3945, 720]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], ![-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], ![-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], ![-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], ![-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99], ![-99, 694, -218, -4262, 108, 6473, 73, -3711, 24, 696], ![-696, 5469, -6266, -23882, 20098, 25164, -17887, -7583, 3945, 720], ![-720, 5064, -1731, -30746, 1318, 46018, -36, -25807, 337, 4665]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], ![-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], ![-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], ![-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], ![-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99], ![-99, 694, -218, -4262, 108, 6473, 73, -3711, 24, 696], ![-696, 5469, -6266, -23882, 20098, 25164, -17887, -7583, 3945, 720], ![-720, 5064, -1731, -30746, 1318, 46018, -36, -25807, 337, 4665], ![-4665, 36600, -41586, -160341, 132529, 169258, -117257, -51351, 25508, 5002]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-98, -12, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-98, -12, -12, -1, -1], [-99, -98, -12, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-98, -12, -12, -1, -1], [-99, -98, -12, -12, -1, -1], [-696, -99, -98, -12, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-98, -12, -12, -1, -1], [-99, -98, -12, -12, -1, -1], [-696, -99, -98, -12, -12, -1, -1], [-720, -696, -99, -98, -12, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-98, -12, -12, -1, -1], [-99, -98, -12, -12, -1, -1], [-696, -99, -98, -12, -12, -1, -1], [-720, -696, -99, -98, -12, -12, -1, -1], [-4665, -720, -696, -99, -98, -12, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -10, -34, 35, 36, -35, -11, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], [-1, 7, -2, -44, 1, 71, 1, -46, 0, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], [-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], [-12, 95, -113, -410, 376, 433, -349, -131, 86, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], [-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], [-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], [-12, 84, -25, -521, 10, 808, 13, -481, 1, 98]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], [-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], [-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], [-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], [-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], [-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], [-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], [-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], [-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99], [-99, 694, -218, -4262, 108, 6473, 73, -3711, 24, 696]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], [-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], [-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], [-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], [-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99], [-99, 694, -218, -4262, 108, 6473, 73, -3711, 24, 696], [-696, 5469, -6266, -23882, 20098, 25164, -17887, -7583, 3945, 720]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], [-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], [-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], [-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], [-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99], [-99, 694, -218, -4262, 108, 6473, 73, -3711, 24, 696], [-696, 5469, -6266, -23882, 20098, 25164, -17887, -7583, 3945, 720], [-720, 5064, -1731, -30746, 1318, 46018, -36, -25807, 337, 4665]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 8, -10, -34, 35, 36, -35, -11, 11, 1], [-1, 7, -2, -44, 1, 71, 1, -46, 0, 12], [-12, 95, -113, -410, 376, 433, -349, -131, 86, 12], [-12, 84, -25, -521, 10, 808, 13, -481, 1, 98], [-98, 772, -896, -3357, 2909, 3538, -2622, -1065, 597, 99], [-99, 694, -218, -4262, 108, 6473, 73, -3711, 24, 696], [-696, 5469, -6266, -23882, 20098, 25164, -17887, -7583, 3945, 720], [-720, 5064, -1731, -30746, 1318, 46018, -36, -25807, 337, 4665], [-4665, 36600, -41586, -160341, 132529, 169258, -117257, -51351, 25508, 5002]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp642566261 : Fact (Nat.Prime 642566261) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 4, 2]
  b' := [3, 3, 0, 4, 1]
  k := [1]
  f := [3, 8, 6, -2, 12, 12, -3, -1, 3, 1]
  g := [4, 4, 3, 0, 2, 1]
  h := [4, 4, 3, 0, 2, 1]
  a := [1, 4, 3, 1, 1]
  b := [2, 3, 0, 3, 4, 1, 4, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD642566261 : CertificateDedekindCriterionLists l 642566261 where
  n := 2
  a' := [22520194, 508520929, 131200774, 461473463, 397611601, 150420096, 146538918, 547988637]
  b' := [378333196, 278157335, 95150757, 586893160, 293116239, 38070221, 320051025, 538534948, 367489881]
  k := [124617242, 571930075, 256043556, 309872432, 276464111, 477908423, 46981528, 515442998, 1]
  f := [4890192, 12113156, 38141655, 49505047, 61344740, 23982144, 41763092, 24832128, 57274216, 1]
  g := [49436623, 122456035, 385587030, 500463441, 620154944, 242443684, 422197373, 251036466, 579004629, 1]
  h := [63561631, 1]
  a := [614226219, 14000171, 601152323, 22343221, 64622719, 507469392, 301111094, 194400174, 524587923]
  b := [202636744, 567780303, 319834844, 148917647, 559709337, 47750264, 366108842, 630637573, 117978338]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 642566261]
  exp := ![1, 1]
  pdgood := [5, 642566261]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp642566261.out
  a := [-263507317303, -319924592192, 1717073028458, 517819155388, -2676306211185, -130913162736, 1184438347209, 12663455254, -138043196160]
  b := [-33340018576, 140166696839, 130506079374, -475316564600, -139956826033, 467268580453, 32791381741, -149929092089, -2646777487, 13804319616]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 642566261 T_ofList CD642566261

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

end VoightMaximalOrderD10R92

end TraceEuclidean
