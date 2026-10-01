import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk217
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

namespace VoightMaximalOrderD10R585

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6300093693232, [1, -5, -2, 25, -1, -39, 5, 22, -4, -4, 1], 1⟩
local notation "l" => [1, -5, -2, 25, -1, -39, 5, 22, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -25, 1, 39, -5, -22, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], ![-4, 19, 13, -98, -21, 157, 19, -93, -6, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], ![-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], ![-20, 96, 59, -487, -78, 759, 57, -421, -13, 74]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], ![-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], ![-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], ![-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], ![-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], ![-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], ![-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], ![-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], ![-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], ![-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], ![-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], ![-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007], ![-1007, 4752, 3355, -24259, -5824, 37765, 5589, -20761, -1809, 3589]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], ![-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], ![-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], ![-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], ![-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007], ![-1007, 4752, 3355, -24259, -5824, 37765, 5589, -20761, -1809, 3589], ![-3589, 16938, 11930, -86370, -20670, 134147, 19820, -73369, -6405, 12547]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], ![-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], ![-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], ![-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], ![-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007], ![-1007, 4752, 3355, -24259, -5824, 37765, 5589, -20761, -1809, 3589], ![-3589, 16938, 11930, -86370, -20670, 134147, 19820, -73369, -6405, 12547], ![-12547, 59146, 42032, -301745, -73823, 468663, 71412, -256214, -23181, 43783]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], ![-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], ![-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], ![-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], ![-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007], ![-1007, 4752, 3355, -24259, -5824, 37765, 5589, -20761, -1809, 3589], ![-3589, 16938, 11930, -86370, -20670, 134147, 19820, -73369, -6405, 12547], ![-12547, 59146, 42032, -301745, -73823, 468663, 71412, -256214, -23181, 43783], ![-43783, 206368, 146712, -1052543, -257962, 1633714, 249748, -891814, -81082, 151951]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-74, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-74, -20, -4, -1], [-283, -74, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-74, -20, -4, -1], [-283, -74, -20, -4, -1], [-1007, -283, -74, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-74, -20, -4, -1], [-283, -74, -20, -4, -1], [-1007, -283, -74, -20, -4, -1], [-3589, -1007, -283, -74, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-74, -20, -4, -1], [-283, -74, -20, -4, -1], [-1007, -283, -74, -20, -4, -1], [-3589, -1007, -283, -74, -20, -4, -1], [-12547, -3589, -1007, -283, -74, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-74, -20, -4, -1], [-283, -74, -20, -4, -1], [-1007, -283, -74, -20, -4, -1], [-3589, -1007, -283, -74, -20, -4, -1], [-12547, -3589, -1007, -283, -74, -20, -4, -1], [-43783, -12547, -3589, -1007, -283, -74, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -25, 1, 39, -5, -22, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], [-4, 19, 13, -98, -21, 157, 19, -93, -6, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], [-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], [-20, 96, 59, -487, -78, 759, 57, -421, -13, 74]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], [-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], [-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], [-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], [-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], [-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], [-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], [-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], [-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], [-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], [-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], [-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007], [-1007, 4752, 3355, -24259, -5824, 37765, 5589, -20761, -1809, 3589]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], [-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], [-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], [-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], [-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007], [-1007, 4752, 3355, -24259, -5824, 37765, 5589, -20761, -1809, 3589], [-3589, 16938, 11930, -86370, -20670, 134147, 19820, -73369, -6405, 12547]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], [-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], [-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], [-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], [-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007], [-1007, 4752, 3355, -24259, -5824, 37765, 5589, -20761, -1809, 3589], [-3589, 16938, 11930, -86370, -20670, 134147, 19820, -73369, -6405, 12547], [-12547, 59146, 42032, -301745, -73823, 468663, 71412, -256214, -23181, 43783]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -25, 1, 39, -5, -22, 4, 4], [-4, 19, 13, -98, -21, 157, 19, -93, -6, 20], [-20, 96, 59, -487, -78, 759, 57, -421, -13, 74], [-74, 350, 244, -1791, -413, 2808, 389, -1571, -125, 283], [-283, 1341, 916, -6831, -1508, 10624, 1393, -5837, -439, 1007], [-1007, 4752, 3355, -24259, -5824, 37765, 5589, -20761, -1809, 3589], [-3589, 16938, 11930, -86370, -20670, 134147, 19820, -73369, -6405, 12547], [-12547, 59146, 42032, -301745, -73823, 468663, 71412, -256214, -23181, 43783], [-43783, 206368, 146712, -1052543, -257962, 1633714, 249748, -891814, -81082, 151951]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp1734401 : Fact (Nat.Prime 1734401) := fact_iff.2 (by norm_num)
instance hp227027 : Fact (Nat.Prime 227027) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1, 0, 1]
  b' := [0, 1, 1, 1, 0, 1, 1]
  k := [1, 1, 1, 0, 1, 0, 1]
  f := [0, 3, 2, -12, 1, 20, -2, -10, 3, 3]
  g := [1, 0, 1, 0, 0, 1, 0, 1, 1]
  h := [1, 1, 1]
  a := [1, 0, 1, 0, 1, 0, 1, 1]
  b := [1, 1, 1, 0, 0, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1734401 : CertificateDedekindCriterionLists l 1734401 where
  n := 2
  a' := [413210, 466116, 515335, 372652, 926414, 1115389, 1139296, 314538]
  b' := [1367922, 1398531, 366584, 907820, 1018031, 646720, 696503, 1034846, 543185]
  k := [807922, 27432, 1162168, 1616730, 220050, 581618, 5901, 421170, 1]
  f := [1462561, 1120254, 361207, 20697, 1470130, 610179, 1294370, 770912, 185015, 1]
  g := [1664683, 1275069, 411124, 23557, 1673298, 694503, 1473248, 877449, 210583, 1]
  h := [1523814, 1]
  a := [1041287, 1002151, 1100004, 1078012, 709338, 595867, 1092453, 39050, 1278871]
  b := [413703, 1521477, 899116, 1357115, 843111, 1237234, 1574729, 1207026, 455530]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD227027 : CertificateDedekindCriterionLists l 227027 where
  n := 2
  a' := [105128, 224373, 174535, 153181, 119172, 87685, 73636, 82372]
  b' := [13039, 212840, 141037, 104775, 204185, 84163, 66352, 26972, 41298]
  k := [95839, 65991, 200408, 106286, 84810, 152346, 182409, 225672, 1]
  f := [75478, 31162, 67149, 14608, 92868, 76102, 104357, 31035, 56753, 1]
  g := [150063, 61954, 133503, 29042, 184637, 151302, 207478, 61701, 112834, 1]
  h := [114189, 1]
  a := [147465, 134167, 30821, 179898, 217213, 98864, 167918, 78775, 37982]
  b := [41048, 112093, 201393, 136503, 155017, 87722, 224238, 22453, 189045]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 1734401, 227027]
  exp := ![1, 1, 1]
  pdgood := [2, 1734401, 227027]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp1734401.out
    exact hp227027.out
  a := [-3378755565231, -20477976457633, 3657434571967, 100475835349977, -13431552799174, -97436234409146, 18757080540628, 25147988685742, -6918914948870]
  b := [-833253455377, -50236961994, 10102353337059, -433689080329, -21919925264271, 2399475459856, 14228505866176, -2419625455180, -2791555466529, 691891494887]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1734401 T_ofList CD1734401
    exact satisfiesDedekindCriterion_of_certificate_lists T l 227027 T_ofList CD227027

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

end VoightMaximalOrderD10R585

namespace VoightMaximalOrderD10R586

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6307277778125, [1, -4, -7, 32, -3, -53, 20, 26, -9, -3, 1], 1⟩
local notation "l" => [1, -4, -7, 32, -3, -53, 20, 26, -9, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, 3, 53, -20, -26, 9, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], ![-3, 11, 25, -89, -23, 162, -7, -98, 1, 18]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], ![-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], ![-18, 69, 137, -551, -35, 931, -198, -475, 64, 55]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], ![-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], ![-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], ![-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], ![-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], ![-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], ![-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], ![-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], ![-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], ![-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], ![-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], ![-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707], ![-707, 2599, 5810, -20819, -4753, 36535, -2389, -20082, 240, 2554]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], ![-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], ![-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], ![-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], ![-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707], ![-707, 2599, 5810, -20819, -4753, 36535, -2389, -20082, 240, 2554], ![-2554, 9509, 20477, -75918, -13157, 130609, -14545, -68793, 2904, 7902]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], ![-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], ![-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], ![-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], ![-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707], ![-707, 2599, 5810, -20819, -4753, 36535, -2389, -20082, 240, 2554], ![-2554, 9509, 20477, -75918, -13157, 130609, -14545, -68793, 2904, 7902], ![-7902, 29054, 64823, -232387, -52212, 405649, -27431, -219997, 2325, 26610]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], ![-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], ![-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], ![-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], ![-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707], ![-707, 2599, 5810, -20819, -4753, 36535, -2389, -20082, 240, 2554], ![-2554, 9509, 20477, -75918, -13157, 130609, -14545, -68793, 2904, 7902], ![-7902, 29054, 64823, -232387, -52212, 405649, -27431, -219997, 2325, 26610], ![-26610, 98538, 215324, -786697, -152557, 1358118, -126551, -719291, 19493, 82155]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-18, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-55, -18, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-55, -18, -3, -1], [-229, -55, -18, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-55, -18, -3, -1], [-229, -55, -18, -3, -1], [-707, -229, -55, -18, -3, -1]], ![[], [], [], [-1], [-3, -1], [-18, -3, -1], [-55, -18, -3, -1], [-229, -55, -18, -3, -1], [-707, -229, -55, -18, -3, -1], [-2554, -707, -229, -55, -18, -3, -1]], ![[], [], [-1], [-3, -1], [-18, -3, -1], [-55, -18, -3, -1], [-229, -55, -18, -3, -1], [-707, -229, -55, -18, -3, -1], [-2554, -707, -229, -55, -18, -3, -1], [-7902, -2554, -707, -229, -55, -18, -3, -1]], ![[], [-1], [-3, -1], [-18, -3, -1], [-55, -18, -3, -1], [-229, -55, -18, -3, -1], [-707, -229, -55, -18, -3, -1], [-2554, -707, -229, -55, -18, -3, -1], [-7902, -2554, -707, -229, -55, -18, -3, -1], [-26610, -7902, -2554, -707, -229, -55, -18, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, 3, 53, -20, -26, 9, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], [-3, 11, 25, -89, -23, 162, -7, -98, 1, 18]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], [-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], [-18, 69, 137, -551, -35, 931, -198, -475, 64, 55]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], [-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], [-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], [-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], [-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], [-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], [-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], [-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], [-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], [-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], [-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], [-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707], [-707, 2599, 5810, -20819, -4753, 36535, -2389, -20082, 240, 2554]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], [-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], [-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], [-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], [-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707], [-707, 2599, 5810, -20819, -4753, 36535, -2389, -20082, 240, 2554], [-2554, 9509, 20477, -75918, -13157, 130609, -14545, -68793, 2904, 7902]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], [-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], [-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], [-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], [-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707], [-707, 2599, 5810, -20819, -4753, 36535, -2389, -20082, 240, 2554], [-2554, 9509, 20477, -75918, -13157, 130609, -14545, -68793, 2904, 7902], [-7902, 29054, 64823, -232387, -52212, 405649, -27431, -219997, 2325, 26610]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, 3, 53, -20, -26, 9, 3], [-3, 11, 25, -89, -23, 162, -7, -98, 1, 18], [-18, 69, 137, -551, -35, 931, -198, -475, 64, 55], [-55, 202, 454, -1623, -386, 2880, -169, -1628, 20, 229], [-229, 861, 1805, -6874, -936, 11751, -1700, -6123, 433, 707], [-707, 2599, 5810, -20819, -4753, 36535, -2389, -20082, 240, 2554], [-2554, 9509, 20477, -75918, -13157, 130609, -14545, -68793, 2904, 7902], [-7902, 29054, 64823, -232387, -52212, 405649, -27431, -219997, 2325, 26610], [-26610, 98538, 215324, -786697, -152557, 1358118, -126551, -719291, 19493, 82155]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2018328889 : Fact (Nat.Prime 2018328889) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 4, 1]
  b' := [2, 3, 3, 0, 1]
  k := [1]
  f := [3, 4, 7, -4, 4, 13, -2, -4, 2, 1]
  g := [4, 2, 3, 0, 1, 1]
  h := [4, 2, 3, 0, 1, 1]
  a := [4, 0, 0, 4, 4]
  b := [1, 3, 2, 4, 4, 0, 1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2018328889 : CertificateDedekindCriterionLists l 2018328889 where
  n := 2
  a' := [959524994, 2001796765, 1670235652, 703763541, 58470113, 650504772, 417276583, 1525237850]
  b' := [1543758313, 2009381147, 692457755, 1200147921, 455071471, 1845637606, 329966288, 24205523, 951822955]
  k := [1772145344, 25933381, 507846426, 1967828131, 271457370, 45304854, 107545009, 853868532, 1]
  f := [44422024, 475558995, 416616751, 274638191, 459542515, 99095045, 129906668, 566451429, 414273418, 1]
  g := [153991081, 1648548110, 1444221986, 952046485, 1593026211, 343517733, 450327707, 1963631100, 1436098709, 1]
  h := [582230177, 1]
  a := [761499198, 314799685, 1053501656, 861184964, 932534911, 1123917023, 1725606839, 1079343129, 1427171716]
  b := [355260980, 231359661, 377132321, 1006437459, 1620256358, 1431361943, 527878574, 559213070, 591157173]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 2018328889]
  exp := ![1, 1]
  pdgood := [5, 2018328889]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2018328889.out
  a := [-22068352272859, -108702726228644, 374945265491925, 467137811818752, -797288801246146, -471258567969392, 333957664323759, 77470498940804, -38811592920020]
  b := [-5519610979326, 14211309143339, 58848413573618, -92817054949531, -115422854325144, 128215695295664, 71903595826355, -41201477216277, -8911397681681, 3881159292002]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2018328889 T_ofList CD2018328889

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

end VoightMaximalOrderD10R586

namespace VoightMaximalOrderD10R589

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6328946403125, [1, -4, -12, 57, -27, -51, 34, 14, -11, -1, 1], 1⟩
local notation "l" => [1, -4, -12, 57, -27, -51, 34, 14, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -57, 27, 51, -34, -14, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], ![-1, 3, 16, -45, -30, 78, 17, -48, -3, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], ![-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], ![-12, 47, 147, -668, 279, 582, -330, -151, 84, 9]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], ![-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], ![-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], ![-9, 24, 155, -366, -425, 738, 276, -456, -52, 93]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], ![-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], ![-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], ![-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], ![-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], ![-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], ![-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], ![-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], ![-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41], ![-41, 71, 855, -1197, -4039, 4236, 2924, -2998, -575, 608]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], ![-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], ![-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], ![-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], ![-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41], ![-41, 71, 855, -1197, -4039, 4236, 2924, -2998, -575, 608], ![-608, 2391, 7367, -33801, 15219, 26969, -16436, -5588, 3690, 33]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], ![-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], ![-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], ![-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], ![-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41], ![-41, 71, 855, -1197, -4039, 4236, 2924, -2998, -575, 608], ![-608, 2391, 7367, -33801, 15219, 26969, -16436, -5588, 3690, 33], ![-33, -476, 2787, 5486, -32910, 16902, 25847, -16898, -5225, 3723]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], ![-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], ![-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], ![-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], ![-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41], ![-41, 71, 855, -1197, -4039, 4236, 2924, -2998, -575, 608], ![-608, 2391, 7367, -33801, 15219, 26969, -16436, -5588, 3690, 33], ![-33, -476, 2787, 5486, -32910, 16902, 25847, -16898, -5225, 3723], ![-3723, 14859, 44200, -209424, 106007, 156963, -109680, -26275, 24055, -1502]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-93, -9, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-93, -9, -12, -1, -1], [-41, -93, -9, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-93, -9, -12, -1, -1], [-41, -93, -9, -12, -1, -1], [-608, -41, -93, -9, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-93, -9, -12, -1, -1], [-41, -93, -9, -12, -1, -1], [-608, -41, -93, -9, -12, -1, -1], [-33, -608, -41, -93, -9, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-93, -9, -12, -1, -1], [-41, -93, -9, -12, -1, -1], [-608, -41, -93, -9, -12, -1, -1], [-33, -608, -41, -93, -9, -12, -1, -1], [-3723, -33, -608, -41, -93, -9, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -57, 27, 51, -34, -14, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], [-1, 3, 16, -45, -30, 78, 17, -48, -3, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], [-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], [-12, 47, 147, -668, 279, 582, -330, -151, 84, 9]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], [-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], [-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], [-9, 24, 155, -366, -425, 738, 276, -456, -52, 93]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], [-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], [-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], [-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], [-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], [-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], [-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], [-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], [-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41], [-41, 71, 855, -1197, -4039, 4236, 2924, -2998, -575, 608]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], [-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], [-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], [-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], [-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41], [-41, 71, 855, -1197, -4039, 4236, 2924, -2998, -575, 608], [-608, 2391, 7367, -33801, 15219, 26969, -16436, -5588, 3690, 33]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], [-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], [-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], [-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], [-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41], [-41, 71, 855, -1197, -4039, 4236, 2924, -2998, -575, 608], [-608, 2391, 7367, -33801, 15219, 26969, -16436, -5588, 3690, 33], [-33, -476, 2787, 5486, -32910, 16902, 25847, -16898, -5225, 3723]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -57, 27, 51, -34, -14, 11, 1], [-1, 3, 16, -45, -30, 78, 17, -48, -3, 12], [-12, 47, 147, -668, 279, 582, -330, -151, 84, 9], [-9, 24, 155, -366, -425, 738, 276, -456, -52, 93], [-93, 363, 1140, -5146, 2145, 4318, -2424, -1026, 567, 41], [-41, 71, 855, -1197, -4039, 4236, 2924, -2998, -575, 608], [-608, 2391, 7367, -33801, 15219, 26969, -16436, -5588, 3690, 33], [-33, -476, 2787, 5486, -32910, 16902, 25847, -16898, -5225, 3723], [-3723, 14859, 44200, -209424, 106007, 156963, -109680, -26275, 24055, -1502]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp34781 : Fact (Nat.Prime 34781) := fact_iff.2 (by norm_num)
instance hp58229 : Fact (Nat.Prime 58229) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4]
  b' := [4, 4, 2]
  k := [1]
  f := [0, 2, 5, -9, 7, 13, -4, -2, 3, 1]
  g := [1, 3, 2, 0, 2, 1]
  h := [1, 3, 2, 0, 2, 1]
  a := [1, 0, 2, 1]
  b := [1, 0, 3, 1, 0, 2, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD34781 : CertificateDedekindCriterionLists l 34781 where
  n := 2
  a' := [27479, 9867, 8375, 27805, 19828, 18093, 29053, 12245]
  b' := [31395, 25826, 9998, 602, 17061, 8182, 6714, 14957, 2504]
  k := [25358, 7555, 16046, 22178, 15451, 3077, 21439, 28301, 1]
  f := [17379, 18594, 15279, 2451, 5008, 11054, 8572, 1437, 8393, 1]
  g := [29300, 31347, 25758, 4131, 8443, 18636, 14451, 2422, 14150, 1]
  h := [20630, 1]
  a := [7734, 3456, 21890, 479, 14361, 25338, 10927, 7346, 14411]
  b := [1805, 25245, 32992, 8972, 18770, 22367, 26522, 4096, 20370]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD58229 : CertificateDedekindCriterionLists l 58229 where
  n := 2
  a' := [42042, 54843, 1716, 5441, 35222, 24449, 16088, 10423]
  b' := [48778, 45559, 2665, 29948, 21513, 35870, 26174, 2417, 50601]
  k := [39636, 47437, 21939, 41136, 16669, 52950, 21815, 15701, 1]
  f := [44789, 38443, 39565, 1071, 11576, 2639, 30172, 20814, 6792, 1]
  g := [51769, 44433, 45730, 1237, 13380, 3050, 34874, 24057, 7850, 1]
  h := [50378, 1]
  a := [8742, 23493, 19083, 2312, 43597, 32453, 50484, 20342, 53792]
  b := [12360, 14121, 56334, 13125, 49623, 14156, 22299, 1861, 4437]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 34781, 58229]
  exp := ![1, 1, 1]
  pdgood := [5, 34781, 58229]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp34781.out
    exact hp58229.out
  a := [-72100189439, -735370203688, 1103166211955, 1107012158266, -1556287152091, -402077795326, 630644595946, 29179505632, -71559204680]
  b := [-20556625921, 11597394043, 279082202613, -271405981303, -241376393168, 260587434603, 62205636151, -79159722410, -3633542610, 7155920468]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 34781 T_ofList CD34781
    exact satisfiesDedekindCriterion_of_certificate_lists T l 58229 T_ofList CD58229

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

end VoightMaximalOrderD10R589

namespace VoightMaximalOrderD10R591

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6351072926605, [1, 4, -34, 32, 44, -56, -11, 27, -3, -4, 1], 1⟩
local notation "l" => [1, 4, -34, 32, 44, -56, -11, 27, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 34, -32, -44, 56, 11, -27, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], ![-4, -17, 132, -94, -208, 180, 100, -97, -15, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], ![-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], ![-19, -80, 629, -476, -930, 856, 389, -413, -40, 61]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], ![-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], ![-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], ![-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], ![-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], ![-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], ![-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], ![-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], ![-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], ![-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], ![-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], ![-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586], ![-586, -2548, 19047, -12079, -30318, 22517, 14710, -11092, -2223, 1698]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], ![-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], ![-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], ![-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], ![-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586], ![-586, -2548, 19047, -12079, -30318, 22517, 14710, -11092, -2223, 1698], ![-1698, -7378, 55184, -35289, -86791, 64770, 41195, -31136, -5998, 4569]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], ![-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], ![-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], ![-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], ![-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586], ![-586, -2548, 19047, -12079, -30318, 22517, 14710, -11092, -2223, 1698], ![-1698, -7378, 55184, -35289, -86791, 64770, 41195, -31136, -5998, 4569], ![-4569, -19974, 147968, -91024, -236325, 169073, 115029, -82168, -17429, 12278]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], ![-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], ![-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], ![-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], ![-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586], ![-586, -2548, 19047, -12079, -30318, 22517, 14710, -11092, -2223, 1698], ![-1698, -7378, 55184, -35289, -86791, 64770, 41195, -31136, -5998, 4569], ![-4569, -19974, 147968, -91024, -236325, 169073, 115029, -82168, -17429, 12278], ![-12278, -53681, 397478, -244928, -631256, 451243, 304131, -216477, -45334, 31683]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1], [-586, -204, -61, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1], [-586, -204, -61, -19, -4, -1], [-1698, -586, -204, -61, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1], [-586, -204, -61, -19, -4, -1], [-1698, -586, -204, -61, -19, -4, -1], [-4569, -1698, -586, -204, -61, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1], [-586, -204, -61, -19, -4, -1], [-1698, -586, -204, -61, -19, -4, -1], [-4569, -1698, -586, -204, -61, -19, -4, -1], [-12278, -4569, -1698, -586, -204, -61, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 34, -32, -44, 56, 11, -27, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], [-4, -17, 132, -94, -208, 180, 100, -97, -15, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], [-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], [-19, -80, 629, -476, -930, 856, 389, -413, -40, 61]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], [-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], [-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], [-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], [-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], [-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], [-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], [-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], [-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], [-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], [-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], [-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586], [-586, -2548, 19047, -12079, -30318, 22517, 14710, -11092, -2223, 1698]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], [-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], [-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], [-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], [-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586], [-586, -2548, 19047, -12079, -30318, 22517, 14710, -11092, -2223, 1698], [-1698, -7378, 55184, -35289, -86791, 64770, 41195, -31136, -5998, 4569]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], [-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], [-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], [-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], [-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586], [-586, -2548, 19047, -12079, -30318, 22517, 14710, -11092, -2223, 1698], [-1698, -7378, 55184, -35289, -86791, 64770, 41195, -31136, -5998, 4569], [-4569, -19974, 147968, -91024, -236325, 169073, 115029, -82168, -17429, 12278]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -4, 34, -32, -44, 56, 11, -27, 3, 4], [-4, -17, 132, -94, -208, 180, 100, -97, -15, 19], [-19, -80, 629, -476, -930, 856, 389, -413, -40, 61], [-61, -263, 1994, -1323, -3160, 2486, 1527, -1258, -230, 204], [-204, -877, 6673, -4534, -10299, 8264, 4730, -3981, -646, 586], [-586, -2548, 19047, -12079, -30318, 22517, 14710, -11092, -2223, 1698], [-1698, -7378, 55184, -35289, -86791, 64770, 41195, -31136, -5998, 4569], [-4569, -19974, 147968, -91024, -236325, 169073, 115029, -82168, -17429, 12278], [-12278, -53681, 397478, -244928, -631256, 451243, 304131, -216477, -45334, 31683]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp443 : Fact (Nat.Prime 443) := fact_iff.2 (by norm_num)
instance hp23696707 : Fact (Nat.Prime 23696707) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 0, 4, 2, 4, 3, 1]
  b' := [4, 3, 1, 1, 0, 0, 3, 1]
  k := [1, 2, 1, 3, 2, 2, 3, 4, 1]
  f := [0, 0, 8, -5, -8, 12, 3, -5, 1, 1]
  g := [1, 3, 3, 4, 0, 4, 0, 2, 0, 1]
  h := [1, 1]
  a := [2, 0, 4, 4, 2, 3, 4, 0, 1]
  b := [1, 2, 0, 0, 1, 2, 3, 4, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 3
  a' := [1, 10, 9, 4, 9, 6, 5]
  b' := [7, 5, 10, 5, 7, 1, 1, 9]
  k := [3, 1, 7, 8, 0, 7, 9, 0, 5, 2, 7, 4, 0, 5, 1]
  f := [4, 3, 9, 0, 1, 8, 3, 0, 2, 1]
  g := [9, 2, 10, 0, 9, 1, 2, 4, 1]
  h := [5, 3, 1]
  a := [4, 4, 3, 2, 8, 1, 5, 5]
  b := [2, 5, 1, 3, 2, 10, 1, 5, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD443 : CertificateDedekindCriterionLists l 443 where
  n := 2
  a' := [131, 152, 111, 270, 440, 220, 259, 391]
  b' := [144, 341, 297, 344, 67, 389, 90, 64, 55]
  k := [201, 193, 289, 153, 177, 338, 87, 276, 1]
  f := [145, 140, 32, 91, 124, 177, 82, 295, 94, 1]
  g := [212, 204, 46, 133, 181, 258, 119, 431, 136, 1]
  h := [303, 1]
  a := [266, 311, 304, 78, 153, 27, 243, 169, 321]
  b := [376, 280, 349, 181, 434, 369, 34, 23, 122]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23696707 : CertificateDedekindCriterionLists l 23696707 where
  n := 2
  a' := [21026928, 15111406, 22575377, 17684150, 14428489, 2457982, 17818183, 12973571]
  b' := [21112421, 22301013, 12423412, 21465341, 8924184, 21161323, 1606739, 8349153, 3824427]
  k := [21075087, 8124212, 1336450, 22067368, 7442873, 19220080, 11699394, 6013474, 1]
  f := [6188021, 6351094, 18228201, 10771553, 11169772, 16413734, 19162706, 6801322, 2625228, 1]
  g := [7087286, 7274057, 20877187, 12336912, 12793002, 18799035, 21947497, 7789713, 3006735, 1]
  h := [20689968, 1]
  a := [3821522, 18166322, 11990548, 8578951, 6174299, 8102935, 14462898, 8282044, 14411212]
  b := [21264169, 8399513, 17215183, 5086757, 18082864, 1783627, 11374451, 2196542, 9285495]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 11, 443, 23696707]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 11, 443, 23696707]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp443.out
    exact hp23696707.out
  a := [991852576539, -7280999465092, -1666634819762, 19180254836068, -3413931642508, -12631420665198, 3798871582252, 2376002489784, -862424887540]
  b := [-103620577621, -933152529823, 2751705926527, 782221927186, -4093449110355, 446523146996, 1882207970020, -460781735692, -272097244480, 86242488754]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 443 T_ofList CD443
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23696707 T_ofList CD23696707

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

end VoightMaximalOrderD10R591

end TraceEuclidean
