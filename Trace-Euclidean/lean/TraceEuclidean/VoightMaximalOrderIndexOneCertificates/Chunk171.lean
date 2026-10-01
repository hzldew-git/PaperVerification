import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk167
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

namespace VoightMaximalOrderD10R33

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1185241902869, [-1, 0, 26, 47, -30, -60, 20, 25, -8, -3, 1], 1⟩
local notation "l" => [-1, 0, 26, 47, -30, -60, 20, 25, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -26, -47, 30, 60, -20, -25, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -26, -47, 30, 60, -20, -25, 8, 3], ![3, 1, -78, -167, 43, 210, 0, -95, -1, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -26, -47, 30, 60, -20, -25, 8, 3], ![3, 1, -78, -167, 43, 210, 0, -95, -1, 17], ![17, 3, -441, -877, 343, 1063, -130, -425, 41, 50]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -26, -47, 30, 60, -20, -25, 8, 3], ![3, 1, -78, -167, 43, 210, 0, -95, -1, 17], ![17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], ![50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -26, -47, 30, 60, -20, -25, 8, 3], ![3, 1, -78, -167, 43, 210, 0, -95, -1, 17], ![17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], ![50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], ![191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -26, -47, 30, 60, -20, -25, 8, 3], ![3, 1, -78, -167, 43, 210, 0, -95, -1, 17], ![17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], ![50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], ![191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548], ![548, 191, -14198, -30705, 6166, 35819, 1123, -14177, -328, 1792]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -26, -47, 30, 60, -20, -25, 8, 3], ![3, 1, -78, -167, 43, 210, 0, -95, -1, 17], ![17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], ![50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], ![191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548], ![548, 191, -14198, -30705, 6166, 35819, 1123, -14177, -328, 1792], ![1792, 548, -46401, -98422, 23055, 113686, -21, -43677, 159, 5048]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -26, -47, 30, 60, -20, -25, 8, 3], ![3, 1, -78, -167, 43, 210, 0, -95, -1, 17], ![17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], ![50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], ![191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548], ![548, 191, -14198, -30705, 6166, 35819, 1123, -14177, -328, 1792], ![1792, 548, -46401, -98422, 23055, 113686, -21, -43677, 159, 5048], ![5048, 1792, -130700, -283657, 53018, 325935, 12726, -126221, -3293, 15303]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -26, -47, 30, 60, -20, -25, 8, 3], ![3, 1, -78, -167, 43, 210, 0, -95, -1, 17], ![17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], ![50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], ![191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548], ![548, 191, -14198, -30705, 6166, 35819, 1123, -14177, -328, 1792], ![1792, 548, -46401, -98422, 23055, 113686, -21, -43677, 159, 5048], ![5048, 1792, -130700, -283657, 53018, 325935, 12726, -126221, -3293, 15303], ![15303, 5048, -396086, -849941, 175433, 971198, 19875, -369849, -3797, 42616]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-50, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-50, -17, -3, -1], [-191, -50, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-50, -17, -3, -1], [-191, -50, -17, -3, -1], [-548, -191, -50, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-50, -17, -3, -1], [-191, -50, -17, -3, -1], [-548, -191, -50, -17, -3, -1], [-1792, -548, -191, -50, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-50, -17, -3, -1], [-191, -50, -17, -3, -1], [-548, -191, -50, -17, -3, -1], [-1792, -548, -191, -50, -17, -3, -1], [-5048, -1792, -548, -191, -50, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-50, -17, -3, -1], [-191, -50, -17, -3, -1], [-548, -191, -50, -17, -3, -1], [-1792, -548, -191, -50, -17, -3, -1], [-5048, -1792, -548, -191, -50, -17, -3, -1], [-15303, -5048, -1792, -548, -191, -50, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -26, -47, 30, 60, -20, -25, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -26, -47, 30, 60, -20, -25, 8, 3], [3, 1, -78, -167, 43, 210, 0, -95, -1, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -26, -47, 30, 60, -20, -25, 8, 3], [3, 1, -78, -167, 43, 210, 0, -95, -1, 17], [17, 3, -441, -877, 343, 1063, -130, -425, 41, 50]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -26, -47, 30, 60, -20, -25, 8, 3], [3, 1, -78, -167, 43, 210, 0, -95, -1, 17], [17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], [50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -26, -47, 30, 60, -20, -25, 8, 3], [3, 1, -78, -167, 43, 210, 0, -95, -1, 17], [17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], [50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], [191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -26, -47, 30, 60, -20, -25, 8, 3], [3, 1, -78, -167, 43, 210, 0, -95, -1, 17], [17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], [50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], [191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548], [548, 191, -14198, -30705, 6166, 35819, 1123, -14177, -328, 1792]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -26, -47, 30, 60, -20, -25, 8, 3], [3, 1, -78, -167, 43, 210, 0, -95, -1, 17], [17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], [50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], [191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548], [548, 191, -14198, -30705, 6166, 35819, 1123, -14177, -328, 1792], [1792, 548, -46401, -98422, 23055, 113686, -21, -43677, 159, 5048]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -26, -47, 30, 60, -20, -25, 8, 3], [3, 1, -78, -167, 43, 210, 0, -95, -1, 17], [17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], [50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], [191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548], [548, 191, -14198, -30705, 6166, 35819, 1123, -14177, -328, 1792], [1792, 548, -46401, -98422, 23055, 113686, -21, -43677, 159, 5048], [5048, 1792, -130700, -283657, 53018, 325935, 12726, -126221, -3293, 15303]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -26, -47, 30, 60, -20, -25, 8, 3], [3, 1, -78, -167, 43, 210, 0, -95, -1, 17], [17, 3, -441, -877, 343, 1063, -130, -425, 41, 50], [50, 17, -1297, -2791, 623, 3343, 63, -1380, -25, 191], [191, 50, -4949, -10274, 2939, 12083, -477, -4712, 148, 548], [548, 191, -14198, -30705, 6166, 35819, 1123, -14177, -328, 1792], [1792, 548, -46401, -98422, 23055, 113686, -21, -43677, 159, 5048], [5048, 1792, -130700, -283657, 53018, 325935, 12726, -126221, -3293, 15303], [15303, 5048, -396086, -849941, 175433, 971198, 19875, -369849, -3797, 42616]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp43 : Fact (Nat.Prime 43) := fact_iff.2 (by norm_num)
instance hp47 : Fact (Nat.Prime 47) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)

def CD43 : CertificateDedekindCriterionLists l 43 where
  n := 2
  a' := [26, 27, 32, 36, 19, 16, 7, 4]
  b' := [18, 40, 3, 5, 15, 37, 37, 13, 33]
  k := [28, 16, 16, 38, 32, 41, 40, 4, 1]
  f := [13, 7, 1, 4, 6, 18, 13, 11, 10, 1]
  g := [31, 15, 3, 12, 12, 39, 30, 26, 22, 1]
  h := [18, 1]
  a := [20, 31, 21, 23, 40, 28, 37, 36, 2]
  b := [18, 14, 0, 7, 30, 12, 26, 31, 41]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD47 : CertificateDedekindCriterionLists l 47 where
  n := 2
  a' := [33, 26, 28, 7, 9, 31, 44, 24]
  b' := [45, 17, 19, 19, 5, 16, 44, 12, 13]
  k := [23, 27, 24, 30, 45, 16, 40, 30, 1]
  f := [3, 4, 1, 6, 4, 4, 2, 2, 6, 1]
  g := [20, 24, 7, 46, 16, 16, 14, 15, 37, 1]
  h := [7, 1]
  a := [15, 8, 7, 9, 16, 8, 37, 42, 27]
  b := [26, 21, 14, 40, 2, 8, 22, 43, 20]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [15, 21, 8, 40, 18, 30, 7]
  b' := [41, 28, 9, 24, 56, 28, 14, 22]
  k := [47, 36, 29, 40, 31, 27, 1]
  f := [10, 32, 46, 46, 34, 44, 50, 22, 10, 1]
  g := [21, 34, 43, 29, 23, 53, 21, 12, 1]
  h := [29, 46, 1]
  a := [40, 26, 15, 28, 57, 43, 53, 16]
  b := [42, 1, 22, 46, 27, 13, 29, 40, 45]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [246, 69, 283, 258, 246, 137, 361]
  b' := [341, 18, 8, 38, 184, 305, 164, 203]
  k := [363, 253, 121, 98, 164, 250, 1]
  f := [331, 126, 171, 100, 26, 213, 284, 343, 60, 1]
  g := [362, 66, 173, 75, 13, 230, 265, 322, 1]
  h := [363, 72, 1]
  a := [383, 48, 347, 17, 332, 339, 193, 341]
  b := [378, 311, 22, 182, 134, 26, 290, 221, 56]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![43, 47, 61, 397]
  exp := ![1, 1, 1, 1]
  pdgood := [43, 47, 61, 397]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp43.out
    exact hp47.out
    exact hp61.out
    exact hp397.out
  a := [-48942557, -7404392476, -7267851765, 23444646878, 8305944472, -22414169178, 3098934533, 4194288896, -1144165380]
  b := [-142392163, 270806725, 3134391224, 1762274145, -5566902178, -902480426, 3239144447, -459808643, -453753851, 114416538]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 43 T_ofList CD43
    exact satisfiesDedekindCriterion_of_certificate_lists T l 47 T_ofList CD47
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397

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

end VoightMaximalOrderD10R33

namespace VoightMaximalOrderD10R35

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1253482128125, [1, -7, 8, 24, -31, -26, 31, 9, -10, -1, 1], 1⟩
local notation "l" => [1, -7, 8, 24, -31, -26, 31, 9, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -8, -24, 31, 26, -31, -9, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], ![-1, 6, -1, -32, 7, 57, -5, -40, 1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], ![-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], ![-11, 76, -82, -265, 309, 293, -284, -104, 70, 12]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], ![-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], ![-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], ![-12, 73, -20, -370, 107, 621, -79, -392, 16, 82]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], ![-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], ![-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], ![-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], ![-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], ![-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], ![-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], ![-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], ![-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98], ![-98, 604, -222, -2935, 1050, 4720, -799, -2803, 163, 526]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], ![-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], ![-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], ![-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], ![-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98], ![-98, 604, -222, -2935, 1050, 4720, -799, -2803, 163, 526], ![-526, 3584, -3604, -12846, 13371, 14726, -11586, -5533, 2457, 689]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], ![-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], ![-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], ![-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], ![-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98], ![-98, 604, -222, -2935, 1050, 4720, -799, -2803, 163, 526], ![-526, 3584, -3604, -12846, 13371, 14726, -11586, -5533, 2457, 689], ![-689, 4297, -1928, -20140, 8513, 31285, -6633, -17787, 1357, 3146]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], ![-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], ![-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], ![-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], ![-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98], ![-98, 604, -222, -2935, 1050, 4720, -799, -2803, 163, 526], ![-526, 3584, -3604, -12846, 13371, 14726, -11586, -5533, 2457, 689], ![-689, 4297, -1928, -20140, 8513, 31285, -6633, -17787, 1357, 3146], ![-3146, 21333, -20871, -77432, 77386, 90309, -66241, -34947, 13673, 4503]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-82, -12, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-82, -12, -11, -1, -1], [-98, -82, -12, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-82, -12, -11, -1, -1], [-98, -82, -12, -11, -1, -1], [-526, -98, -82, -12, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-82, -12, -11, -1, -1], [-98, -82, -12, -11, -1, -1], [-526, -98, -82, -12, -11, -1, -1], [-689, -526, -98, -82, -12, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-82, -12, -11, -1, -1], [-98, -82, -12, -11, -1, -1], [-526, -98, -82, -12, -11, -1, -1], [-689, -526, -98, -82, -12, -11, -1, -1], [-3146, -689, -526, -98, -82, -12, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -8, -24, 31, 26, -31, -9, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], [-1, 6, -1, -32, 7, 57, -5, -40, 1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], [-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], [-11, 76, -82, -265, 309, 293, -284, -104, 70, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], [-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], [-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], [-12, 73, -20, -370, 107, 621, -79, -392, 16, 82]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], [-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], [-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], [-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], [-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], [-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], [-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], [-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], [-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98], [-98, 604, -222, -2935, 1050, 4720, -799, -2803, 163, 526]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], [-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], [-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], [-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], [-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98], [-98, 604, -222, -2935, 1050, 4720, -799, -2803, 163, 526], [-526, 3584, -3604, -12846, 13371, 14726, -11586, -5533, 2457, 689]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], [-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], [-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], [-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], [-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98], [-98, 604, -222, -2935, 1050, 4720, -799, -2803, 163, 526], [-526, 3584, -3604, -12846, 13371, 14726, -11586, -5533, 2457, 689], [-689, 4297, -1928, -20140, 8513, 31285, -6633, -17787, 1357, 3146]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -8, -24, 31, 26, -31, -9, 10, 1], [-1, 6, -1, -32, 7, 57, -5, -40, 1, 11], [-11, 76, -82, -265, 309, 293, -284, -104, 70, 12], [-12, 73, -20, -370, 107, 621, -79, -392, 16, 82], [-82, 562, -583, -1988, 2172, 2239, -1921, -817, 428, 98], [-98, 604, -222, -2935, 1050, 4720, -799, -2803, 163, 526], [-526, 3584, -3604, -12846, 13371, 14726, -11586, -5533, 2457, 689], [-689, 4297, -1928, -20140, 8513, 31285, -6633, -17787, 1357, 3146], [-3146, 21333, -20871, -77432, 77386, 90309, -66241, -34947, 13673, 4503]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp181 : Fact (Nat.Prime 181) := fact_iff.2 (by norm_num)
instance hp2216101 : Fact (Nat.Prime 2216101) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 2, 1]
  b' := [4, 0, 0, 3, 3]
  k := [1]
  f := [0, 3, 2, -2, 12, 10, -2, 1, 4, 1]
  g := [1, 4, 1, 3, 2, 1]
  h := [1, 4, 1, 3, 2, 1]
  a := [2, 3, 0, 2, 2]
  b := [1, 0, 1, 1, 4, 3, 3, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD181 : CertificateDedekindCriterionLists l 181 where
  n := 2
  a' := [39, 19, 86, 52, 7, 1, 27, 27]
  b' := [55, 133, 73, 11, 78, 49, 140, 180, 178]
  k := [29, 75, 85, 116, 101, 77, 75, 170, 1]
  f := [4, 2, 4, 4, 3, 4, 3, 1, 5, 1]
  g := [145, 42, 138, 122, 78, 124, 90, 20, 175, 1]
  h := [5, 1]
  a := [22, 61, 122, 155, 74, 110, 179, 169, 133]
  b := [108, 134, 97, 111, 62, 0, 37, 178, 48]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2216101 : CertificateDedekindCriterionLists l 2216101 where
  n := 2
  a' := [282429, 458097, 982320, 500492, 1924396, 223594, 249087, 834957]
  b' := [254240, 954894, 1367034, 2164661, 848969, 1309648, 1967307, 1378931, 2123328]
  k := [1306938, 1406087, 114407, 1558254, 1393361, 555080, 1281825, 78628, 1]
  f := [435859, 593648, 544503, 16189, 462867, 312142, 719005, 734103, 553328, 1]
  g := [903785, 1230971, 1129065, 33568, 959788, 647248, 1490908, 1522214, 1147364, 1]
  h := [1068736, 1]
  a := [958233, 1499395, 293661, 1489293, 2104787, 1706658, 1253606, 799875, 126758]
  b := [36357, 1776224, 325494, 1349915, 1300799, 946867, 1184163, 1551736, 2089343]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 181, 2216101]
  exp := ![1, 1, 1]
  pdgood := [5, 181, 2216101]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp181.out
    exact hp2216101.out
  a := [-92439530934, -115001752556, 561792746500, 298030043490, -789087229229, -163265920456, 331365393334, 25451696672, -40805473480]
  b := [-13492157477, 45171492050, 54085328768, -140334532834, -67695080041, 131495630347, 25037180983, -41410366324, -2953224402, 4080547348]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 181 T_ofList CD181
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2216101 T_ofList CD2216101

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

end VoightMaximalOrderD10R35

namespace VoightMaximalOrderD10R41

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1355940128125, [1, -6, 4, 24, -21, -30, 25, 12, -10, -1, 1], 1⟩
local notation "l" => [1, -6, 4, 24, -21, -30, 25, 12, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 21, 30, -25, -12, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], ![-1, 5, 2, -28, -3, 51, 5, -37, -2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], ![-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], ![-11, 65, -39, -262, 203, 327, -224, -127, 73, 9]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], ![-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], ![-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], ![-9, 43, 29, -255, -73, 473, 102, -332, -37, 82]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], ![-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], ![-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], ![-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], ![-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], ![-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], ![-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], ![-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], ![-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45], ![-45, 188, 303, -1365, -994, 2817, 1262, -2117, -432, 533]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], ![-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], ![-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], ![-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], ![-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45], ![-45, 188, 303, -1365, -994, 2817, 1262, -2117, -432, 533], ![-533, 3153, -1944, -12489, 9828, 14996, -10508, -5134, 3213, 101]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], ![-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], ![-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], ![-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], ![-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45], ![-45, 188, 303, -1365, -994, 2817, 1262, -2117, -432, 533], ![-533, 3153, -1944, -12489, 9828, 14996, -10508, -5134, 3213, 101], ![-101, 73, 2749, -4368, -10368, 12858, 12471, -11720, -4124, 3314]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], ![-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], ![-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], ![-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], ![-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45], ![-45, 188, 303, -1365, -994, 2817, 1262, -2117, -432, 533], ![-533, 3153, -1944, -12489, 9828, 14996, -10508, -5134, 3213, 101], ![-101, 73, 2749, -4368, -10368, 12858, 12471, -11720, -4124, 3314], ![-3314, 19783, -13183, -76787, 65226, 89052, -69992, -27297, 21420, -810]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-9, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-9, -11, -1, -1], [-82, -9, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-9, -11, -1, -1], [-82, -9, -11, -1, -1], [-45, -82, -9, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-9, -11, -1, -1], [-82, -9, -11, -1, -1], [-45, -82, -9, -11, -1, -1], [-533, -45, -82, -9, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-9, -11, -1, -1], [-82, -9, -11, -1, -1], [-45, -82, -9, -11, -1, -1], [-533, -45, -82, -9, -11, -1, -1], [-101, -533, -45, -82, -9, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-9, -11, -1, -1], [-82, -9, -11, -1, -1], [-45, -82, -9, -11, -1, -1], [-533, -45, -82, -9, -11, -1, -1], [-101, -533, -45, -82, -9, -11, -1, -1], [-3314, -101, -533, -45, -82, -9, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 21, 30, -25, -12, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], [-1, 5, 2, -28, -3, 51, 5, -37, -2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], [-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], [-11, 65, -39, -262, 203, 327, -224, -127, 73, 9]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], [-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], [-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], [-9, 43, 29, -255, -73, 473, 102, -332, -37, 82]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], [-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], [-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], [-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], [-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], [-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], [-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], [-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], [-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45], [-45, 188, 303, -1365, -994, 2817, 1262, -2117, -432, 533]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], [-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], [-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], [-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], [-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45], [-45, 188, 303, -1365, -994, 2817, 1262, -2117, -432, 533], [-533, 3153, -1944, -12489, 9828, 14996, -10508, -5134, 3213, 101]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], [-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], [-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], [-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], [-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45], [-45, 188, 303, -1365, -994, 2817, 1262, -2117, -432, 533], [-533, 3153, -1944, -12489, 9828, 14996, -10508, -5134, 3213, 101], [-101, 73, 2749, -4368, -10368, 12858, 12471, -11720, -4124, 3314]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -4, -24, 21, 30, -25, -12, 10, 1], [-1, 5, 2, -28, -3, 51, 5, -37, -2, 11], [-11, 65, -39, -262, 203, 327, -224, -127, 73, 9], [-9, 43, 29, -255, -73, 473, 102, -332, -37, 82], [-82, 483, -285, -1939, 1467, 2387, -1577, -882, 488, 45], [-45, 188, 303, -1365, -994, 2817, 1262, -2117, -432, 533], [-533, 3153, -1944, -12489, 9828, 14996, -10508, -5134, 3213, 101], [-101, 73, 2749, -4368, -10368, 12858, 12471, -11720, -4124, 3314], [-3314, 19783, -13183, -76787, 65226, 89052, -69992, -27297, 21420, -810]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp39445531 : Fact (Nat.Prime 39445531) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 3, 2]
  b' := [1, 4, 3, 3, 1]
  k := [1]
  f := [3, 6, 1, 0, 11, 10, -2, 0, 4, 1]
  g := [4, 3, 0, 3, 2, 1]
  h := [4, 3, 0, 3, 2, 1]
  a := [0, 2, 4, 3, 1]
  b := [4, 3, 3, 1, 0, 0, 2, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [9, 9, 5, 4, 6, 0, 8, 7]
  b' := [3, 0, 8, 9, 2, 5, 8, 5, 9]
  k := [3, 7, 10, 6, 1, 3, 9, 3, 1]
  f := [4, 1, 7, 6, 6, 8, 4, 2, 2, 1]
  g := [5, 0, 9, 9, 4, 6, 7, 3, 1, 1]
  h := [9, 1]
  a := [1, 1, 5, 4, 7, 7, 5, 10, 4]
  b := [6, 10, 10, 4, 5, 2, 4, 8, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD39445531 : CertificateDedekindCriterionLists l 39445531 where
  n := 2
  a' := [3755058, 10258701, 14628838, 14988134, 433642, 4748256, 10477436, 35374615]
  b' := [32544190, 33407407, 32243524, 23749577, 23141387, 4553082, 8305411, 17087987, 452324]
  k := [29186370, 218361, 23764623, 15862242, 2178726, 12821783, 28879849, 30892535, 1]
  f := [21421643, 21707551, 6896498, 16641094, 13149990, 11834071, 3929389, 10724149, 9397745, 1]
  g := [35208918, 35678839, 11335181, 27351539, 21613510, 19450647, 6458399, 17626364, 15446267, 1]
  h := [23999263, 1]
  a := [31406935, 4339223, 4983189, 14285110, 11663498, 9711304, 9980347, 21143288, 6933897]
  b := [13557543, 13311493, 35991690, 21824987, 29775122, 37548076, 24838172, 17145223, 32511634]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 39445531]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 39445531]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp39445531.out
  a := [-146042762645, -279275707116, 884250974502, 791517088340, -1337808317249, -484270337734, 662838269301, 49189799186, -81538741640]
  b := [-24702044475, 66560752159, 121612163615, -215979115058, -173863259135, 221750073323, 72829494853, -82833525941, -5734367335, 8153874164]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 39445531 T_ofList CD39445531

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

end VoightMaximalOrderD10R41

namespace VoightMaximalOrderD10R44

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1406641653125, [-19, -25, 57, 64, -66, -54, 37, 18, -10, -2, 1], 1⟩
local notation "l" => [-19, -25, 57, 64, -66, -54, 37, 18, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 25, -57, -64, 66, 54, -37, -18, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 25, -57, -64, 66, 54, -37, -18, 10, 2], ![38, 69, -89, -185, 68, 174, -20, -73, 2, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 25, -57, -64, 66, 54, -37, -18, 10, 2], ![38, 69, -89, -185, 68, 174, -20, -73, 2, 14], ![266, 388, -729, -985, 739, 824, -344, -272, 67, 30]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 25, -57, -64, 66, 54, -37, -18, 10, 2], ![38, 69, -89, -185, 68, 174, -20, -73, 2, 14], ![266, 388, -729, -985, 739, 824, -344, -272, 67, 30], ![570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 25, -57, -64, 66, 54, -37, -18, 10, 2], ![38, 69, -89, -185, 68, 174, -20, -73, 2, 14], ![266, 388, -729, -985, 739, 824, -344, -272, 67, 30], ![570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], ![2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 25, -57, -64, 66, 54, -37, -18, 10, 2], ![38, 69, -89, -185, 68, 174, -20, -73, 2, 14], ![266, 388, -729, -985, 739, 824, -344, -272, 67, 30], ![570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], ![2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282], ![5358, 9463, -12329, -24271, 9162, 20961, -2581, -7416, 248, 950]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 25, -57, -64, 66, 54, -37, -18, 10, 2], ![38, 69, -89, -185, 68, 174, -20, -73, 2, 14], ![266, 388, -729, -985, 739, 824, -344, -272, 67, 30], ![570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], ![2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282], ![5358, 9463, -12329, -24271, 9162, 20961, -2581, -7416, 248, 950], ![18050, 29108, -44687, -73129, 38429, 60462, -14189, -19681, 2084, 2148]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 25, -57, -64, 66, 54, -37, -18, 10, 2], ![38, 69, -89, -185, 68, 174, -20, -73, 2, 14], ![266, 388, -729, -985, 739, 824, -344, -272, 67, 30], ![570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], ![2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282], ![5358, 9463, -12329, -24271, 9162, 20961, -2581, -7416, 248, 950], ![18050, 29108, -44687, -73129, 38429, 60462, -14189, -19681, 2084, 2148], ![40812, 71750, -93328, -182159, 68639, 154421, -19014, -52853, 1799, 6380]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 25, -57, -64, 66, 54, -37, -18, 10, 2], ![38, 69, -89, -185, 68, 174, -20, -73, 2, 14], ![266, 388, -729, -985, 739, 824, -344, -272, 67, 30], ![570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], ![2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282], ![5358, 9463, -12329, -24271, 9162, 20961, -2581, -7416, 248, 950], ![18050, 29108, -44687, -73129, 38429, 60462, -14189, -19681, 2084, 2148], ![40812, 71750, -93328, -182159, 68639, 154421, -19014, -52853, 1799, 6380], ![121220, 200312, -291910, -501648, 238921, 413159, -81639, -133854, 10947, 14559]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1], [-282, -127, -30, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1], [-282, -127, -30, -14, -2, -1], [-950, -282, -127, -30, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1], [-282, -127, -30, -14, -2, -1], [-950, -282, -127, -30, -14, -2, -1], [-2148, -950, -282, -127, -30, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-30, -14, -2, -1], [-127, -30, -14, -2, -1], [-282, -127, -30, -14, -2, -1], [-950, -282, -127, -30, -14, -2, -1], [-2148, -950, -282, -127, -30, -14, -2, -1], [-6380, -2148, -950, -282, -127, -30, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 25, -57, -64, 66, 54, -37, -18, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 25, -57, -64, 66, 54, -37, -18, 10, 2], [38, 69, -89, -185, 68, 174, -20, -73, 2, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 25, -57, -64, 66, 54, -37, -18, 10, 2], [38, 69, -89, -185, 68, 174, -20, -73, 2, 14], [266, 388, -729, -985, 739, 824, -344, -272, 67, 30]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 25, -57, -64, 66, 54, -37, -18, 10, 2], [38, 69, -89, -185, 68, 174, -20, -73, 2, 14], [266, 388, -729, -985, 739, 824, -344, -272, 67, 30], [570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 25, -57, -64, 66, 54, -37, -18, 10, 2], [38, 69, -89, -185, 68, 174, -20, -73, 2, 14], [266, 388, -729, -985, 739, 824, -344, -272, 67, 30], [570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], [2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 25, -57, -64, 66, 54, -37, -18, 10, 2], [38, 69, -89, -185, 68, 174, -20, -73, 2, 14], [266, 388, -729, -985, 739, 824, -344, -272, 67, 30], [570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], [2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282], [5358, 9463, -12329, -24271, 9162, 20961, -2581, -7416, 248, 950]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 25, -57, -64, 66, 54, -37, -18, 10, 2], [38, 69, -89, -185, 68, 174, -20, -73, 2, 14], [266, 388, -729, -985, 739, 824, -344, -272, 67, 30], [570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], [2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282], [5358, 9463, -12329, -24271, 9162, 20961, -2581, -7416, 248, 950], [18050, 29108, -44687, -73129, 38429, 60462, -14189, -19681, 2084, 2148]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 25, -57, -64, 66, 54, -37, -18, 10, 2], [38, 69, -89, -185, 68, 174, -20, -73, 2, 14], [266, 388, -729, -985, 739, 824, -344, -272, 67, 30], [570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], [2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282], [5358, 9463, -12329, -24271, 9162, 20961, -2581, -7416, 248, 950], [18050, 29108, -44687, -73129, 38429, 60462, -14189, -19681, 2084, 2148], [40812, 71750, -93328, -182159, 68639, 154421, -19014, -52853, 1799, 6380]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 25, -57, -64, 66, 54, -37, -18, 10, 2], [38, 69, -89, -185, 68, 174, -20, -73, 2, 14], [266, 388, -729, -985, 739, 824, -344, -272, 67, 30], [570, 1016, -1322, -2649, 995, 2359, -286, -884, 28, 127], [2413, 3745, -6223, -9450, 5733, 7853, -2340, -2572, 386, 282], [5358, 9463, -12329, -24271, 9162, 20961, -2581, -7416, 248, 950], [18050, 29108, -44687, -73129, 38429, 60462, -14189, -19681, 2084, 2148], [40812, 71750, -93328, -182159, 68639, 154421, -19014, -52853, 1799, 6380], [121220, 200312, -291910, -501648, 238921, 413159, -81639, -133854, 10947, 14559]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp359 : Fact (Nat.Prime 359) := fact_iff.2 (by norm_num)
instance hp1253831 : Fact (Nat.Prime 1253831) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 4, 2, 2, 4]
  k := [1]
  f := [4, 5, -11, -12, 15, 12, -5, 0, 6, 2]
  g := [1, 0, 1, 2, 4, 1]
  h := [1, 0, 1, 2, 4, 1]
  a := [2, 0, 0, 2]
  b := [3, 0, 4, 0, 4, 2, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD359 : CertificateDedekindCriterionLists l 359 where
  n := 2
  a' := [80, 214, 186, 13, 75, 229, 137, 167]
  b' := [87, 77, 136, 61, 188, 149, 79, 15, 141]
  k := [151, 272, 48, 17, 312, 237, 292, 207, 1]
  f := [41, 19, 59, 52, 18, 29, 50, 5, 59, 1]
  g := [196, 88, 282, 246, 82, 137, 238, 21, 282, 1]
  h := [75, 1]
  a := [342, 73, 70, 62, 39, 149, 16, 117, 131]
  b := [249, 142, 338, 47, 214, 84, 76, 17, 228]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1253831 : CertificateDedekindCriterionLists l 1253831 where
  n := 2
  a' := [1216125, 1078858, 28481, 263375, 99665, 840973, 264081, 666230]
  b' := [556788, 430496, 583408, 1030252, 924910, 833132, 712160, 304670, 65289]
  k := [311711, 17205, 967736, 639120, 902477, 1008393, 1252359, 651063, 1]
  f := [266483, 243986, 132651, 260398, 195576, 258494, 295365, 249099, 228940, 1]
  g := [1108638, 1015041, 551859, 1083321, 813643, 1075399, 1228791, 1036312, 952446, 1]
  h := [301383, 1]
  a := [825671, 72086, 350566, 743778, 911032, 535320, 873643, 600835, 508281]
  b := [943467, 797235, 16485, 690319, 218907, 522664, 1194742, 135375, 745550]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 359, 1253831]
  exp := ![1, 1, 1]
  pdgood := [5, 359, 1253831]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp359.out
    exact hp1253831.out
  a := [5903841420, -40505530720, 27611257312, 79325107568, -59209461524, -45326397104, 31937900156, 7414615344, -4799126980]
  b := [-4576944545, 4009494802, 16114095792, -12531383784, -16948668526, 11748272006, 6706246046, -4178091676, -837444074, 479912698]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 359 T_ofList CD359
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1253831 T_ofList CD1253831

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

end VoightMaximalOrderD10R44

end TraceEuclidean
