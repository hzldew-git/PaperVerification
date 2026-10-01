import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk211
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

namespace VoightMaximalOrderD10R517

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5809061065625, [-19, -54, 56, 116, -62, -87, 33, 27, -9, -3, 1], 1⟩
local notation "l" => [-19, -54, 56, 116, -62, -87, 33, 27, -9, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 54, -56, -116, 62, 87, -33, -27, 9, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 54, -56, -116, 62, 87, -33, -27, 9, 3], ![57, 181, -114, -404, 70, 323, -12, -114, 0, 18]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 54, -56, -116, 62, 87, -33, -27, 9, 3], ![57, 181, -114, -404, 70, 323, -12, -114, 0, 18], ![342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 54, -56, -116, 62, 87, -33, -27, 9, 3], ![57, 181, -114, -404, 70, 323, -12, -114, 0, 18], ![342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], ![1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 54, -56, -116, 62, 87, -33, -27, 9, 3], ![57, 181, -114, -404, 70, 323, -12, -114, 0, 18], ![342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], ![1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], ![3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 54, -56, -116, 62, 87, -33, -27, 9, 3], ![57, 181, -114, -404, 70, 323, -12, -114, 0, 18], ![342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], ![1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], ![3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618], ![11742, 37362, -22242, -80190, 11961, 59695, -978, -18206, -254, 2015]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 54, -56, -116, 62, 87, -33, -27, 9, 3], ![57, 181, -114, -404, 70, 323, -12, -114, 0, 18], ![342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], ![1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], ![3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618], ![11742, 37362, -22242, -80190, 11961, 59695, -978, -18206, -254, 2015], ![38285, 120552, -75478, -255982, 44740, 187266, -6800, -55383, -71, 5791]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 54, -56, -116, 62, 87, -33, -27, 9, 3], ![57, 181, -114, -404, 70, 323, -12, -114, 0, 18], ![342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], ![1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], ![3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618], ![11742, 37362, -22242, -80190, 11961, 59695, -978, -18206, -254, 2015], ![38285, 120552, -75478, -255982, 44740, 187266, -6800, -55383, -71, 5791], ![110029, 350999, -203744, -747234, 103060, 548557, -3837, -163157, -3264, 17302]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![19, 54, -56, -116, 62, 87, -33, -27, 9, 3], ![57, 181, -114, -404, 70, 323, -12, -114, 0, 18], ![342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], ![1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], ![3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618], ![11742, 37362, -22242, -80190, 11961, 59695, -978, -18206, -254, 2015], ![38285, 120552, -75478, -255982, 44740, 187266, -6800, -55383, -71, 5791], ![110029, 350999, -203744, -747234, 103060, 548557, -3837, -163157, -3264, 17302], ![328738, 1044337, -617913, -2210776, 325490, 1608334, -22409, -470991, -7439, 48642]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-18, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-54, -18, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-54, -18, -3, -1], [-210, -54, -18, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-54, -18, -3, -1], [-210, -54, -18, -3, -1], [-618, -210, -54, -18, -3, -1]], ![[], [], [], [-1], [-3, -1], [-18, -3, -1], [-54, -18, -3, -1], [-210, -54, -18, -3, -1], [-618, -210, -54, -18, -3, -1], [-2015, -618, -210, -54, -18, -3, -1]], ![[], [], [-1], [-3, -1], [-18, -3, -1], [-54, -18, -3, -1], [-210, -54, -18, -3, -1], [-618, -210, -54, -18, -3, -1], [-2015, -618, -210, -54, -18, -3, -1], [-5791, -2015, -618, -210, -54, -18, -3, -1]], ![[], [-1], [-3, -1], [-18, -3, -1], [-54, -18, -3, -1], [-210, -54, -18, -3, -1], [-618, -210, -54, -18, -3, -1], [-2015, -618, -210, -54, -18, -3, -1], [-5791, -2015, -618, -210, -54, -18, -3, -1], [-17302, -5791, -2015, -618, -210, -54, -18, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 54, -56, -116, 62, 87, -33, -27, 9, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 54, -56, -116, 62, 87, -33, -27, 9, 3], [57, 181, -114, -404, 70, 323, -12, -114, 0, 18]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 54, -56, -116, 62, 87, -33, -27, 9, 3], [57, 181, -114, -404, 70, 323, -12, -114, 0, 18], [342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 54, -56, -116, 62, 87, -33, -27, 9, 3], [57, 181, -114, -404, 70, 323, -12, -114, 0, 18], [342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], [1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 54, -56, -116, 62, 87, -33, -27, 9, 3], [57, 181, -114, -404, 70, 323, -12, -114, 0, 18], [342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], [1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], [3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 54, -56, -116, 62, 87, -33, -27, 9, 3], [57, 181, -114, -404, 70, 323, -12, -114, 0, 18], [342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], [1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], [3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618], [11742, 37362, -22242, -80190, 11961, 59695, -978, -18206, -254, 2015]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 54, -56, -116, 62, 87, -33, -27, 9, 3], [57, 181, -114, -404, 70, 323, -12, -114, 0, 18], [342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], [1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], [3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618], [11742, 37362, -22242, -80190, 11961, 59695, -978, -18206, -254, 2015], [38285, 120552, -75478, -255982, 44740, 187266, -6800, -55383, -71, 5791]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 54, -56, -116, 62, 87, -33, -27, 9, 3], [57, 181, -114, -404, 70, 323, -12, -114, 0, 18], [342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], [1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], [3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618], [11742, 37362, -22242, -80190, 11961, 59695, -978, -18206, -254, 2015], [38285, 120552, -75478, -255982, 44740, 187266, -6800, -55383, -71, 5791], [110029, 350999, -203744, -747234, 103060, 548557, -3837, -163157, -3264, 17302]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [19, 54, -56, -116, 62, 87, -33, -27, 9, 3], [57, 181, -114, -404, 70, 323, -12, -114, 0, 18], [342, 1029, -827, -2202, 712, 1636, -271, -498, 48, 54], [1026, 3258, -1995, -7091, 1146, 5410, -146, -1729, -12, 210], [3990, 12366, -8502, -26355, 5929, 19416, -1520, -5816, 161, 618], [11742, 37362, -22242, -80190, 11961, 59695, -978, -18206, -254, 2015], [38285, 120552, -75478, -255982, 44740, 187266, -6800, -55383, -71, 5791], [110029, 350999, -203744, -747234, 103060, 548557, -3837, -163157, -3264, 17302], [328738, 1044337, -617913, -2210776, 325490, 1608334, -22409, -470991, -7439, 48642]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1019 : Fact (Nat.Prime 1019) := fact_iff.2 (by norm_num)
instance hp1824239 : Fact (Nat.Prime 1824239) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3, 1]
  b' := [0, 3, 1, 4, 1]
  k := [1]
  f := [4, 12, -9, -22, 13, 19, -5, -5, 2, 1]
  g := [1, 3, 1, 0, 1, 1]
  h := [1, 3, 1, 0, 1, 1]
  a := [2, 1, 3, 1, 1]
  b := [3, 3, 2, 4, 0, 2, 2, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1019 : CertificateDedekindCriterionLists l 1019 where
  n := 2
  a' := [613, 304, 793, 628, 163, 816, 581, 315]
  b' := [927, 499, 722, 717, 418, 305, 545, 181, 984]
  k := [30, 190, 372, 772, 395, 894, 743, 459, 1]
  f := [157, 755, 676, 283, 169, 571, 351, 534, 177, 1]
  g := [203, 976, 873, 365, 218, 738, 453, 690, 228, 1]
  h := [788, 1]
  a := [443, 663, 709, 642, 170, 959, 845, 377, 979]
  b := [832, 89, 1007, 81, 1004, 572, 370, 640, 40]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1824239 : CertificateDedekindCriterionLists l 1824239 where
  n := 2
  a' := [614703, 210927, 1175301, 1452057, 1042660, 1168354, 665944, 1094851]
  b' := [922380, 986597, 1621789, 26657, 69378, 296493, 1418958, 951283, 891816]
  k := [1212400, 832638, 289287, 410291, 375857, 1786900, 1448566, 1158544, 1]
  f := [138115, 223881, 8449, 269295, 45099, 142202, 213395, 259779, 272116, 1]
  g := [756971, 1227029, 46303, 1475933, 247171, 779370, 1169558, 1423775, 1491390, 1]
  h := [332846, 1]
  a := [1313724, 293613, 1538693, 915262, 404707, 401947, 1178381, 877341, 788180]
  b := [556929, 339770, 1214883, 288033, 484924, 1309204, 699422, 1047257, 1036059]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 1019, 1824239]
  exp := ![1, 1, 1]
  pdgood := [5, 1019, 1824239]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1019.out
    exact hp1824239.out
  a := [37095355501, -123459983764, -133885223858, 414954972996, 73068005750, -311349324454, 33435938756, 66454336548, -17404672440]
  b := [-13224189856, -21083680915, 80085332449, 30499909424, -104587821162, -5630331338, 47555895208, -5892583286, -7167573828, 1740467244]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1019 T_ofList CD1019
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1824239 T_ofList CD1824239

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

end VoightMaximalOrderD10R517

namespace VoightMaximalOrderD10R520

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5844427806016, [-1, -1, 13, 1, -40, -1, 42, 6, -12, -1, 1], 1⟩
local notation "l" => [-1, -1, 13, 1, -40, -1, 42, 6, -12, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -13, -1, 40, 1, -42, -6, 12, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -13, -1, 40, 1, -42, -6, 12, 1], ![1, 2, -12, -14, 39, 41, -41, -48, 6, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -13, -1, 40, 1, -42, -6, 12, 1], ![1, 2, -12, -14, 39, 41, -41, -48, 6, 13], ![13, 14, -167, -25, 506, 52, -505, -119, 108, 19]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -13, -1, 40, 1, -42, -6, 12, 1], ![1, 2, -12, -14, 39, 41, -41, -48, 6, 13], ![13, 14, -167, -25, 506, 52, -505, -119, 108, 19], ![19, 32, -233, -186, 735, 525, -746, -619, 109, 127]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -13, -1, 40, 1, -42, -6, 12, 1], ![1, 2, -12, -14, 39, 41, -41, -48, 6, 13], ![13, 14, -167, -25, 506, 52, -505, -119, 108, 19], ![19, 32, -233, -186, 735, 525, -746, -619, 109, 127], ![127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -13, -1, 40, 1, -42, -6, 12, 1], ![1, 2, -12, -14, 39, 41, -41, -48, 6, 13], ![13, 14, -167, -25, 506, 52, -505, -119, 108, 19], ![19, 32, -233, -186, 735, 525, -746, -619, 109, 127], ![127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236], ![236, 363, -2922, -1855, 9080, 5130, -9050, -6225, 1324, 1141]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -13, -1, 40, 1, -42, -6, 12, 1], ![1, 2, -12, -14, 39, 41, -41, -48, 6, 13], ![13, 14, -167, -25, 506, 52, -505, -119, 108, 19], ![19, 32, -233, -186, 735, 525, -746, -619, 109, 127], ![127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236], ![236, 363, -2922, -1855, 9080, 5130, -9050, -6225, 1324, 1141], ![1141, 1377, -14470, -4063, 43785, 10221, -42792, -15896, 7467, 2465]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -13, -1, 40, 1, -42, -6, 12, 1], ![1, 2, -12, -14, 39, 41, -41, -48, 6, 13], ![13, 14, -167, -25, 506, 52, -505, -119, 108, 19], ![19, 32, -233, -186, 735, 525, -746, -619, 109, 127], ![127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236], ![236, 363, -2922, -1855, 9080, 5130, -9050, -6225, 1324, 1141], ![1141, 1377, -14470, -4063, 43785, 10221, -42792, -15896, 7467, 2465], ![2465, 3606, -30668, -16935, 94537, 46250, -93309, -57582, 13684, 9932]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -13, -1, 40, 1, -42, -6, 12, 1], ![1, 2, -12, -14, 39, 41, -41, -48, 6, 13], ![13, 14, -167, -25, 506, 52, -505, -119, 108, 19], ![19, 32, -233, -186, 735, 525, -746, -619, 109, 127], ![127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236], ![236, 363, -2922, -1855, 9080, 5130, -9050, -6225, 1324, 1141], ![1141, 1377, -14470, -4063, 43785, 10221, -42792, -15896, 7467, 2465], ![2465, 3606, -30668, -16935, 94537, 46250, -93309, -57582, 13684, 9932], ![9932, 12397, -125510, -40600, 380345, 104469, -370894, -152901, 61602, 23616]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-19, -13, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-19, -13, -1, -1], [-127, -19, -13, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-19, -13, -1, -1], [-127, -19, -13, -1, -1], [-236, -127, -19, -13, -1, -1]], ![[], [], [], [-1], [-1, -1], [-13, -1, -1], [-19, -13, -1, -1], [-127, -19, -13, -1, -1], [-236, -127, -19, -13, -1, -1], [-1141, -236, -127, -19, -13, -1, -1]], ![[], [], [-1], [-1, -1], [-13, -1, -1], [-19, -13, -1, -1], [-127, -19, -13, -1, -1], [-236, -127, -19, -13, -1, -1], [-1141, -236, -127, -19, -13, -1, -1], [-2465, -1141, -236, -127, -19, -13, -1, -1]], ![[], [-1], [-1, -1], [-13, -1, -1], [-19, -13, -1, -1], [-127, -19, -13, -1, -1], [-236, -127, -19, -13, -1, -1], [-1141, -236, -127, -19, -13, -1, -1], [-2465, -1141, -236, -127, -19, -13, -1, -1], [-9932, -2465, -1141, -236, -127, -19, -13, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -13, -1, 40, 1, -42, -6, 12, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -13, -1, 40, 1, -42, -6, 12, 1], [1, 2, -12, -14, 39, 41, -41, -48, 6, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -13, -1, 40, 1, -42, -6, 12, 1], [1, 2, -12, -14, 39, 41, -41, -48, 6, 13], [13, 14, -167, -25, 506, 52, -505, -119, 108, 19]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -13, -1, 40, 1, -42, -6, 12, 1], [1, 2, -12, -14, 39, 41, -41, -48, 6, 13], [13, 14, -167, -25, 506, 52, -505, -119, 108, 19], [19, 32, -233, -186, 735, 525, -746, -619, 109, 127]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -13, -1, 40, 1, -42, -6, 12, 1], [1, 2, -12, -14, 39, 41, -41, -48, 6, 13], [13, 14, -167, -25, 506, 52, -505, -119, 108, 19], [19, 32, -233, -186, 735, 525, -746, -619, 109, 127], [127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -13, -1, 40, 1, -42, -6, 12, 1], [1, 2, -12, -14, 39, 41, -41, -48, 6, 13], [13, 14, -167, -25, 506, 52, -505, -119, 108, 19], [19, 32, -233, -186, 735, 525, -746, -619, 109, 127], [127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236], [236, 363, -2922, -1855, 9080, 5130, -9050, -6225, 1324, 1141]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -13, -1, 40, 1, -42, -6, 12, 1], [1, 2, -12, -14, 39, 41, -41, -48, 6, 13], [13, 14, -167, -25, 506, 52, -505, -119, 108, 19], [19, 32, -233, -186, 735, 525, -746, -619, 109, 127], [127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236], [236, 363, -2922, -1855, 9080, 5130, -9050, -6225, 1324, 1141], [1141, 1377, -14470, -4063, 43785, 10221, -42792, -15896, 7467, 2465]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -13, -1, 40, 1, -42, -6, 12, 1], [1, 2, -12, -14, 39, 41, -41, -48, 6, 13], [13, 14, -167, -25, 506, 52, -505, -119, 108, 19], [19, 32, -233, -186, 735, 525, -746, -619, 109, 127], [127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236], [236, 363, -2922, -1855, 9080, 5130, -9050, -6225, 1324, 1141], [1141, 1377, -14470, -4063, 43785, 10221, -42792, -15896, 7467, 2465], [2465, 3606, -30668, -16935, 94537, 46250, -93309, -57582, 13684, 9932]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -13, -1, 40, 1, -42, -6, 12, 1], [1, 2, -12, -14, 39, 41, -41, -48, 6, 13], [13, 14, -167, -25, 506, 52, -505, -119, 108, 19], [19, 32, -233, -186, 735, 525, -746, -619, 109, 127], [127, 146, -1619, -360, 4894, 862, -4809, -1508, 905, 236], [236, 363, -2922, -1855, 9080, 5130, -9050, -6225, 1324, 1141], [1141, 1377, -14470, -4063, 43785, 10221, -42792, -15896, 7467, 2465], [2465, 3606, -30668, -16935, 94537, 46250, -93309, -57582, 13684, 9932], [9932, 12397, -125510, -40600, 380345, 104469, -370894, -152901, 61602, 23616]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp607 : Fact (Nat.Prime 607) := fact_iff.2 (by norm_num)
instance hp150443467 : Fact (Nat.Prime 150443467) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 0, 1]
  k := [1, 1, 1, 1, 1]
  f := [1, 1, -6, 1, 21, 1, -20, -2, 6, 1]
  g := [1, 1, 0, 1, 1, 0, 0, 1]
  h := [1, 0, 1, 1]
  a := [0, 1, 1, 1, 1, 0, 1]
  b := [1, 0, 0, 1, 1, 0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD607 : CertificateDedekindCriterionLists l 607 where
  n := 2
  a' := [292, 478, 525, 329, 375, 40, 558, 58]
  b' := [526, 344, 235, 236, 386, 178, 571, 180, 61]
  k := [179, 269, 581, 206, 324, 77, 407, 560, 1]
  f := [18, 12, 11, 18, 15, 11, 13, 21, 23, 1]
  g := [475, 296, 278, 463, 374, 274, 333, 540, 583, 1]
  h := [23, 1]
  a := [472, 451, 202, 462, 392, 580, 479, 230, 93]
  b := [538, 198, 287, 588, 249, 246, 58, 255, 514]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD150443467 : CertificateDedekindCriterionLists l 150443467 where
  n := 2
  a' := [63230299, 132737134, 110050584, 129166833, 77441251, 131562573, 104298947, 132964543]
  b' := [41718541, 80680660, 1719585, 30961196, 48399257, 82613562, 5151412, 49052414, 52089925]
  k := [114873342, 29898807, 8664509, 118327526, 114168625, 83688280, 76081928, 46832693, 1]
  f := [91436163, 121469841, 83995374, 17701570, 110589900, 44388887, 102099130, 57165116, 19771620, 1]
  g := [108291626, 143861751, 99479191, 20964700, 130976188, 52571592, 120920218, 67703008, 23416346, 1]
  h := [127027120, 1]
  a := [139001750, 147555393, 103486825, 131203503, 36563927, 80359611, 49874264, 122543871, 87862027]
  b := [75030251, 16166211, 122012785, 42201854, 59378772, 5654675, 48829221, 131367267, 62581440]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 607, 150443467]
  exp := ![1, 1, 1]
  pdgood := [2, 607, 150443467]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp607.out
    exact hp150443467.out
  a := [-98259037326033, 2358456733043269, 4902360125009759, -6125104132561526, -12454362883224497, 410257626721955, 4924898285585353, 195067675448554, -502631161775760]
  b := [98076398957095, 289788677167234, -709449540072088, -1484123343719555, 1026840968529870, 2103832087311541, -13623554394436, -615694311086214, -24533079162613, 50263116177576]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 607 T_ofList CD607
    exact satisfiesDedekindCriterion_of_certificate_lists T l 150443467 T_ofList CD150443467

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

end VoightMaximalOrderD10R520

namespace VoightMaximalOrderD10R521

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5849557465797, [-1, 10, 16, -35, -48, 32, 45, -5, -12, 0, 1], 1⟩
local notation "l" => [-1, 10, 16, -35, -48, 32, 45, -5, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, -16, 35, 48, -32, -45, 5, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, -16, 35, 48, -32, -45, 5, 12, 0], ![0, 1, -10, -16, 35, 48, -32, -45, 5, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, -16, 35, 48, -32, -45, 5, 12, 0], ![0, 1, -10, -16, 35, 48, -32, -45, 5, 12], ![12, -120, -191, 410, 560, -349, -492, 28, 99, 5]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, -16, 35, 48, -32, -45, 5, 12, 0], ![0, 1, -10, -16, 35, 48, -32, -45, 5, 12], ![12, -120, -191, 410, 560, -349, -492, 28, 99, 5], ![5, -38, -200, -16, 650, 400, -574, -467, 88, 99]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, -16, 35, 48, -32, -45, 5, 12, 0], ![0, 1, -10, -16, 35, 48, -32, -45, 5, 12], ![12, -120, -191, 410, 560, -349, -492, 28, 99, 5], ![5, -38, -200, -16, 650, 400, -574, -467, 88, 99], ![99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, -16, 35, 48, -32, -45, 5, 12, 0], ![0, 1, -10, -16, 35, 48, -32, -45, 5, 12], ![12, -120, -191, 410, 560, -349, -492, 28, 99, 5], ![5, -38, -200, -16, 650, 400, -574, -467, 88, 99], ![99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88], ![88, -781, -2393, 1458, 7489, 1920, -6478, -3615, 977, 721]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, -16, 35, 48, -32, -45, 5, 12, 0], ![0, 1, -10, -16, 35, 48, -32, -45, 5, 12], ![12, -120, -191, 410, 560, -349, -492, 28, 99, 5], ![5, -38, -200, -16, 650, 400, -574, -467, 88, 99], ![99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88], ![88, -781, -2393, 1458, 7489, 1920, -6478, -3615, 977, 721], ![721, -7122, -12317, 22842, 36066, -15583, -30525, -2873, 5037, 977]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, -16, 35, 48, -32, -45, 5, 12, 0], ![0, 1, -10, -16, 35, 48, -32, -45, 5, 12], ![12, -120, -191, 410, 560, -349, -492, 28, 99, 5], ![5, -38, -200, -16, 650, 400, -574, -467, 88, 99], ![99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88], ![88, -781, -2393, 1458, 7489, 1920, -6478, -3615, 977, 721], ![721, -7122, -12317, 22842, 36066, -15583, -30525, -2873, 5037, 977], ![977, -9049, -22754, 21878, 69738, 4802, -59548, -25640, 8851, 5037]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, -16, 35, 48, -32, -45, 5, 12, 0], ![0, 1, -10, -16, 35, 48, -32, -45, 5, 12], ![12, -120, -191, 410, 560, -349, -492, 28, 99, 5], ![5, -38, -200, -16, 650, 400, -574, -467, 88, 99], ![99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88], ![88, -781, -2393, 1458, 7489, 1920, -6478, -3615, 977, 721], ![721, -7122, -12317, 22842, 36066, -15583, -30525, -2873, 5037, 977], ![977, -9049, -22754, 21878, 69738, 4802, -59548, -25640, 8851, 5037], ![5037, -49393, -89641, 153541, 263654, -91446, -221863, -34363, 34804, 8851]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-5, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-5, -12, 0, -1], [-99, -5, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-5, -12, 0, -1], [-99, -5, -12, 0, -1], [-88, -99, -5, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-5, -12, 0, -1], [-99, -5, -12, 0, -1], [-88, -99, -5, -12, 0, -1], [-721, -88, -99, -5, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-5, -12, 0, -1], [-99, -5, -12, 0, -1], [-88, -99, -5, -12, 0, -1], [-721, -88, -99, -5, -12, 0, -1], [-977, -721, -88, -99, -5, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-5, -12, 0, -1], [-99, -5, -12, 0, -1], [-88, -99, -5, -12, 0, -1], [-721, -88, -99, -5, -12, 0, -1], [-977, -721, -88, -99, -5, -12, 0, -1], [-5037, -977, -721, -88, -99, -5, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, -16, 35, 48, -32, -45, 5, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, -16, 35, 48, -32, -45, 5, 12, 0], [0, 1, -10, -16, 35, 48, -32, -45, 5, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, -16, 35, 48, -32, -45, 5, 12, 0], [0, 1, -10, -16, 35, 48, -32, -45, 5, 12], [12, -120, -191, 410, 560, -349, -492, 28, 99, 5]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, -16, 35, 48, -32, -45, 5, 12, 0], [0, 1, -10, -16, 35, 48, -32, -45, 5, 12], [12, -120, -191, 410, 560, -349, -492, 28, 99, 5], [5, -38, -200, -16, 650, 400, -574, -467, 88, 99]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, -16, 35, 48, -32, -45, 5, 12, 0], [0, 1, -10, -16, 35, 48, -32, -45, 5, 12], [12, -120, -191, 410, 560, -349, -492, 28, 99, 5], [5, -38, -200, -16, 650, 400, -574, -467, 88, 99], [99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, -16, 35, 48, -32, -45, 5, 12, 0], [0, 1, -10, -16, 35, 48, -32, -45, 5, 12], [12, -120, -191, 410, 560, -349, -492, 28, 99, 5], [5, -38, -200, -16, 650, 400, -574, -467, 88, 99], [99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88], [88, -781, -2393, 1458, 7489, 1920, -6478, -3615, 977, 721]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, -16, 35, 48, -32, -45, 5, 12, 0], [0, 1, -10, -16, 35, 48, -32, -45, 5, 12], [12, -120, -191, 410, 560, -349, -492, 28, 99, 5], [5, -38, -200, -16, 650, 400, -574, -467, 88, 99], [99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88], [88, -781, -2393, 1458, 7489, 1920, -6478, -3615, 977, 721], [721, -7122, -12317, 22842, 36066, -15583, -30525, -2873, 5037, 977]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, -16, 35, 48, -32, -45, 5, 12, 0], [0, 1, -10, -16, 35, 48, -32, -45, 5, 12], [12, -120, -191, 410, 560, -349, -492, 28, 99, 5], [5, -38, -200, -16, 650, 400, -574, -467, 88, 99], [99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88], [88, -781, -2393, 1458, 7489, 1920, -6478, -3615, 977, 721], [721, -7122, -12317, 22842, 36066, -15583, -30525, -2873, 5037, 977], [977, -9049, -22754, 21878, 69738, 4802, -59548, -25640, 8851, 5037]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, -16, 35, 48, -32, -45, 5, 12, 0], [0, 1, -10, -16, 35, 48, -32, -45, 5, 12], [12, -120, -191, 410, 560, -349, -492, 28, 99, 5], [5, -38, -200, -16, 650, 400, -574, -467, 88, 99], [99, -985, -1622, 3265, 4736, -2518, -4055, -79, 721, 88], [88, -781, -2393, 1458, 7489, 1920, -6478, -3615, 977, 721], [721, -7122, -12317, 22842, 36066, -15583, -30525, -2873, 5037, 977], [977, -9049, -22754, 21878, 69738, 4802, -59548, -25640, 8851, 5037], [5037, -49393, -89641, 153541, 263654, -91446, -221863, -34363, 34804, 8851]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp73 : Fact (Nat.Prime 73) := fact_iff.2 (by norm_num)
instance hp1871 : Fact (Nat.Prime 1871) := fact_iff.2 (by norm_num)
instance hp7243 : Fact (Nat.Prime 7243) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [1, 2, 2, 2, 0, 0, 2]
  b' := [1, 0, 2, 2, 1, 1, 2, 2]
  k := [1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 1, 0, 0, 1]
  f := [1, -2, -4, 13, 17, -9, -14, 3, 5, 1]
  g := [2, 2, 0, 2, 1, 2, 0, 2, 1]
  h := [1, 1, 1]
  a := [1, 1, 1, 2, 0, 1, 1, 1]
  b := [0, 2, 2, 1, 1, 1, 2, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD73 : CertificateDedekindCriterionLists l 73 where
  n := 3
  a' := [38, 40, 35, 66, 71, 60, 50]
  b' := [2, 7, 28, 34, 8, 5, 62, 12]
  k := [24, 64, 70, 55, 33, 48, 4, 23, 66, 65, 39, 15, 35, 66, 1]
  f := [25, 56, 37, 8, 14, 24, 51, 56, 17, 1]
  g := [38, 45, 8, 2, 18, 18, 59, 22, 1]
  h := [48, 51, 1]
  a := [7, 60, 4, 54, 7, 51, 58, 38]
  b := [30, 53, 29, 61, 5, 1, 42, 59, 35]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1871 : CertificateDedekindCriterionLists l 1871 where
  n := 2
  a' := [785, 140, 1520, 1834, 836, 538, 1283, 802]
  b' := [1800, 345, 205, 381, 1365, 1848, 1335, 299, 1574]
  k := [1777, 1471, 1493, 1374, 50, 81, 1242, 704, 1]
  f := [1040, 310, 1369, 458, 498, 1197, 578, 330, 286, 1]
  g := [1281, 381, 1686, 563, 613, 1474, 711, 406, 352, 1]
  h := [1519, 1]
  a := [1514, 962, 1819, 255, 553, 1859, 1059, 1486, 616]
  b := [1562, 1464, 355, 1472, 482, 105, 133, 1750, 1255]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7243 : CertificateDedekindCriterionLists l 7243 where
  n := 2
  a' := [1109, 3857, 4825, 892, 3939, 745, 6006, 522]
  b' := [6360, 1, 5254, 2943, 6900, 5479, 3102, 7156, 7185]
  k := [6322, 1742, 70, 1309, 2882, 5432, 3291, 2817, 1]
  f := [1330, 260, 1390, 2118, 1631, 159, 598, 333, 1537, 1]
  g := [4353, 849, 4549, 6930, 5335, 518, 1957, 1089, 5030, 1]
  h := [2213, 1]
  a := [3012, 3344, 2667, 4412, 6094, 6656, 771, 3438, 6100]
  b := [1529, 11, 2229, 3302, 960, 3038, 6556, 2199, 1143]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![3, 73, 1871, 7243]
  exp := ![2, 1, 1, 1]
  pdgood := [3, 73, 1871, 7243]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp73.out
    exact hp1871.out
    exact hp7243.out
  a := [-186831711721, -328586052180, 2418408186378, 286056364380, -3421454778694, -441153238864, 1261540109788, 103373411140, -139715359880]
  b := [-17792827570, 210910154727, 7620424960, -669426882058, 11842357199, 590004574510, 47967638578, -159685697350, -10337341114, 13971535988]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 73 T_ofList CD73
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1871 T_ofList CD1871
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7243 T_ofList CD7243

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

end VoightMaximalOrderD10R521

namespace VoightMaximalOrderD10R522

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5852238614648, [1, -15, 52, 18, -94, -2, 55, -1, -13, 0, 1], 1⟩
local notation "l" => [1, -15, 52, 18, -94, -2, 55, -1, -13, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 15, -52, -18, 94, 2, -55, 1, 13, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], ![0, -1, 15, -52, -18, 94, 2, -55, 1, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], ![0, -1, 15, -52, -18, 94, 2, -55, 1, 13], ![-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], ![0, -1, 15, -52, -18, 94, 2, -55, 1, 13], ![-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], ![-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], ![0, -1, 15, -52, -18, 94, 2, -55, 1, 13], ![-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], ![-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], ![-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], ![0, -1, 15, -52, -18, 94, 2, -55, 1, 13], ![-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], ![-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], ![-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28], ![-28, 306, 253, -6430, 723, 10077, -1437, -5070, 431, 862]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], ![0, -1, 15, -52, -18, 94, 2, -55, 1, 13], ![-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], ![-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], ![-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28], ![-28, 306, 253, -6430, 723, 10077, -1437, -5070, 431, 862], ![-862, 12902, -44518, -15263, 74598, 2447, -37333, -575, 6136, 431]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], ![0, -1, 15, -52, -18, 94, 2, -55, 1, 13], ![-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], ![-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], ![-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28], ![-28, 306, 253, -6430, 723, 10077, -1437, -5070, 431, 862], ![-862, 12902, -44518, -15263, 74598, 2447, -37333, -575, 6136, 431], ![-431, 5603, -9510, -52276, 25251, 75460, -21258, -36902, 5028, 6136]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], ![0, -1, 15, -52, -18, 94, 2, -55, 1, 13], ![-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], ![-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], ![-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28], ![-28, 306, 253, -6430, 723, 10077, -1437, -5070, 431, 862], ![-862, 12902, -44518, -15263, 74598, 2447, -37333, -575, 6136, 431], ![-431, 5603, -9510, -52276, 25251, 75460, -21258, -36902, 5028, 6136], ![-6136, 91609, -313469, -119958, 524508, 37523, -262020, -15122, 42866, 5028]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-13, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-13, 0, -1], [-1, -13, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-13, 0, -1], [-1, -13, 0, -1], [-114, -1, -13, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-13, 0, -1], [-1, -13, 0, -1], [-114, -1, -13, 0, -1], [-28, -114, -1, -13, 0, -1]], ![[], [], [], [-1], [0, -1], [-13, 0, -1], [-1, -13, 0, -1], [-114, -1, -13, 0, -1], [-28, -114, -1, -13, 0, -1], [-862, -28, -114, -1, -13, 0, -1]], ![[], [], [-1], [0, -1], [-13, 0, -1], [-1, -13, 0, -1], [-114, -1, -13, 0, -1], [-28, -114, -1, -13, 0, -1], [-862, -28, -114, -1, -13, 0, -1], [-431, -862, -28, -114, -1, -13, 0, -1]], ![[], [-1], [0, -1], [-13, 0, -1], [-1, -13, 0, -1], [-114, -1, -13, 0, -1], [-28, -114, -1, -13, 0, -1], [-862, -28, -114, -1, -13, 0, -1], [-431, -862, -28, -114, -1, -13, 0, -1], [-6136, -431, -862, -28, -114, -1, -13, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 15, -52, -18, 94, 2, -55, 1, 13, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], [0, -1, 15, -52, -18, 94, 2, -55, 1, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], [0, -1, 15, -52, -18, 94, 2, -55, 1, 13], [-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], [0, -1, 15, -52, -18, 94, 2, -55, 1, 13], [-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], [-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], [0, -1, 15, -52, -18, 94, 2, -55, 1, 13], [-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], [-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], [-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], [0, -1, 15, -52, -18, 94, 2, -55, 1, 13], [-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], [-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], [-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28], [-28, 306, 253, -6430, 723, 10077, -1437, -5070, 431, 862]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], [0, -1, 15, -52, -18, 94, 2, -55, 1, 13], [-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], [-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], [-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28], [-28, 306, 253, -6430, 723, 10077, -1437, -5070, 431, 862], [-862, 12902, -44518, -15263, 74598, 2447, -37333, -575, 6136, 431]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], [0, -1, 15, -52, -18, 94, 2, -55, 1, 13], [-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], [-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], [-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28], [-28, 306, 253, -6430, 723, 10077, -1437, -5070, 431, 862], [-862, 12902, -44518, -15263, 74598, 2447, -37333, -575, 6136, 431], [-431, 5603, -9510, -52276, 25251, 75460, -21258, -36902, 5028, 6136]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 15, -52, -18, 94, 2, -55, 1, 13, 0], [0, -1, 15, -52, -18, 94, 2, -55, 1, 13], [-13, 195, -677, -219, 1170, 8, -621, 15, 114, 1], [-1, 2, 143, -695, -125, 1172, -47, -620, 28, 114], [-114, 1709, -5926, -1909, 10021, 103, -5098, 67, 862, 28], [-28, 306, 253, -6430, 723, 10077, -1437, -5070, 431, 862], [-862, 12902, -44518, -15263, 74598, 2447, -37333, -575, 6136, 431], [-431, 5603, -9510, -52276, 25251, 75460, -21258, -36902, 5028, 6136], [-6136, 91609, -313469, -119958, 524508, 37523, -262020, -15122, 42866, 5028]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp731529826831 : Fact (Nat.Prime 731529826831) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 0, 0, 0, 0, 1]
  b' := [1, 1, 0, 0, 1, 0, 1, 1]
  k := [1, 1, 1, 1, 1, 1, 0, 0, 1]
  f := [0, 8, -26, -9, 47, 1, -27, 1, 7, 1]
  g := [1, 0, 0, 0, 0, 0, 1, 0, 1, 1]
  h := [1, 1]
  a := [0, 0, 1, 0, 0, 1, 1, 1, 1]
  b := [1, 0, 0, 0, 0, 1, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD731529826831 : CertificateDedekindCriterionLists l 731529826831 where
  n := 2
  a' := [425203750297, 542735041019, 536383524054, 372371666014, 34361314117, 558284434278, 583613394664, 335505377275]
  b' := [223547351159, 382226658919, 379656952901, 97837001493, 150669740889, 406742891922, 648626726641, 259712878291, 531689267838]
  k := [216847232200, 514091313205, 677405595652, 613474997147, 302094615327, 283038269606, 702248928151, 667875743263, 1]
  f := [28163072393, 13698015802, 12270487635, 22786114045, 3420504174, 29007497759, 4122462043, 20793381518, 30442326423, 1]
  g := [647315185951, 314842554169, 282031479877, 523728286604, 78618705519, 666723912212, 94752882289, 477926251652, 699702785047, 1]
  h := [31827041784, 1]
  a := [374913574806, 729111102256, 164676296625, 657230324563, 256245545200, 722305172374, 588276365321, 23899973581, 298455171357]
  b := [640593818537, 244564060548, 401042703471, 517508965605, 720280310489, 595903332098, 454731504299, 352269071651, 433074655474]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 731529826831]
  exp := ![2, 1]
  pdgood := [2, 731529826831]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp731529826831.out
  a := [-58471810241861, 74396010491261, 269468502486327, -240515556321499, -334214816102161, 134183806524627, 140745071688806, -13950492891410, -15344756911590]
  b := [-4093195303279, 35052056838544, -30841628175190, -82807997288654, 47015863456462, 61862927979122, -17505851511577, -18064143965894, 1395049289141, 1534475691159]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 731529826831 T_ofList CD731529826831

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

end VoightMaximalOrderD10R522

end TraceEuclidean
