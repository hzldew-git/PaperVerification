import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk181
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

namespace VoightMaximalOrderD10R183

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2963583578125, [11, -27, -32, 76, 27, -73, -3, 29, -4, -4, 1], 1⟩
local notation "l" => [11, -27, -32, 76, 27, -73, -3, 29, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 27, 32, -76, -27, 73, 3, -29, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], ![-44, 97, 155, -272, -184, 265, 85, -113, -13, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], ![-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], ![-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], ![-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], ![-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], ![-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], ![-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], ![-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], ![-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], ![-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], ![-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], ![-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], ![-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], ![-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713], ![-7843, 16666, 28424, -45079, -34471, 41349, 16120, -15893, -2486, 2174]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], ![-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], ![-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], ![-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], ![-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713], ![-7843, 16666, 28424, -45079, -34471, 41349, 16120, -15893, -2486, 2174], ![-23914, 50855, 86234, -136800, -103777, 124231, 47871, -46926, -7197, 6210]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], ![-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], ![-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], ![-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], ![-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713], ![-7843, 16666, 28424, -45079, -34471, 41349, 16120, -15893, -2486, 2174], ![-23914, 50855, 86234, -136800, -103777, 124231, 47871, -46926, -7197, 6210], ![-68310, 143756, 249575, -385726, -304470, 349553, 142861, -132219, -22086, 17643]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], ![-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], ![-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], ![-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], ![-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713], ![-7843, 16666, 28424, -45079, -34471, 41349, 16120, -15893, -2486, 2174], ![-23914, 50855, 86234, -136800, -103777, 124231, 47871, -46926, -7197, 6210], ![-68310, 143756, 249575, -385726, -304470, 349553, 142861, -132219, -22086, 17643], ![-194073, 408051, 708332, -1091293, -862087, 983469, 402482, -368786, -61647, 48486]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-235, -67, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-235, -67, -20, -4, -1], [-713, -235, -67, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-235, -67, -20, -4, -1], [-713, -235, -67, -20, -4, -1], [-2174, -713, -235, -67, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-235, -67, -20, -4, -1], [-713, -235, -67, -20, -4, -1], [-2174, -713, -235, -67, -20, -4, -1], [-6210, -2174, -713, -235, -67, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-235, -67, -20, -4, -1], [-713, -235, -67, -20, -4, -1], [-2174, -713, -235, -67, -20, -4, -1], [-6210, -2174, -713, -235, -67, -20, -4, -1], [-17643, -6210, -2174, -713, -235, -67, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 27, 32, -76, -27, 73, 3, -29, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], [-44, 97, 155, -272, -184, 265, 85, -113, -13, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], [-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], [-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], [-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], [-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], [-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], [-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], [-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], [-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], [-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], [-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], [-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], [-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], [-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713], [-7843, 16666, 28424, -45079, -34471, 41349, 16120, -15893, -2486, 2174]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], [-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], [-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], [-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], [-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713], [-7843, 16666, 28424, -45079, -34471, 41349, 16120, -15893, -2486, 2174], [-23914, 50855, 86234, -136800, -103777, 124231, 47871, -46926, -7197, 6210]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], [-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], [-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], [-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], [-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713], [-7843, 16666, 28424, -45079, -34471, 41349, 16120, -15893, -2486, 2174], [-23914, 50855, 86234, -136800, -103777, 124231, 47871, -46926, -7197, 6210], [-68310, 143756, 249575, -385726, -304470, 349553, 142861, -132219, -22086, 17643]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 27, 32, -76, -27, 73, 3, -29, 4, 4], [-44, 97, 155, -272, -184, 265, 85, -113, -13, 20], [-220, 496, 737, -1365, -812, 1276, 325, -495, -33, 67], [-737, 1589, 2640, -4355, -3174, 4079, 1477, -1618, -227, 235], [-2585, 5608, 9109, -15220, -10700, 13981, 4784, -5338, -678, 713], [-7843, 16666, 28424, -45079, -34471, 41349, 16120, -15893, -2486, 2174], [-23914, 50855, 86234, -136800, -103777, 124231, 47871, -46926, -7197, 6210], [-68310, 143756, 249575, -385726, -304470, 349553, 142861, -132219, -22086, 17643], [-194073, 408051, 708332, -1091293, -862087, 983469, 402482, -368786, -61647, 48486]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp189669349 : Fact (Nat.Prime 189669349) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [3, 2, 3]
  b' := [2, 2, 2, 3]
  k := [1, 0, 4, 2, 4, 4, 1]
  f := [-1, 7, 9, -13, -4, 16, 2, -5, 1, 1]
  g := [3, 1, 1, 0, 1]
  h := [2, 2, 3, 2, 0, 1, 1]
  a := [4, 0, 4, 3]
  b := [0, 4, 3, 0, 2, 0, 4, 3, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD189669349 : CertificateDedekindCriterionLists l 189669349 where
  n := 2
  a' := [36659546, 138954373, 87982173, 103207160, 128318161, 11065411, 109631945, 153550463]
  b' := [72736434, 169542105, 89521619, 33610300, 176878589, 17287768, 111686995, 49183249, 88310698]
  k := [184904166, 147841165, 20304855, 148089332, 174603503, 177118277, 58346801, 51103756, 1]
  f := [6565237, 47687634, 135675206, 140282493, 129797578, 89510063, 27719120, 42055191, 22109578, 1]
  g := [7587396, 55112247, 156798835, 162123442, 150006103, 103446119, 32034782, 48602874, 25551876, 1]
  h := [164117469, 1]
  a := [47121277, 68134791, 70017583, 23307794, 90481499, 160291586, 55233852, 158296273, 74240421]
  b := [108956532, 111008059, 9466285, 62003266, 77545180, 103551467, 85645767, 48298169, 115428928]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 189669349]
  exp := ![1, 1]
  pdgood := [5, 189669349]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp189669349.out
  a := [-10555736492, -33151889014, 65683644180, 92960893122, -84231742435, -68961300986, 38975340824, 13758762518, -6395352680]
  b := [-4335609191, 7326410902, 18444276438, -17426736758, -24020830840, 13639959543, 11125245823, -4779742582, -1631690359, 639535268]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 189669349 T_ofList CD189669349

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

end VoightMaximalOrderD10R183

namespace VoightMaximalOrderD10R184

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2972305937408, [1, 6, 6, -20, -31, 18, 33, -4, -11, 0, 1], 1⟩
local notation "l" => [1, 6, 6, -20, -31, 18, 33, -4, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 31, -18, -33, 4, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], ![0, -1, -6, -6, 20, 31, -18, -33, 4, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], ![0, -1, -6, -6, 20, 31, -18, -33, 4, 11], ![-11, -66, -67, 214, 335, -178, -332, 26, 88, 4]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], ![0, -1, -6, -6, 20, 31, -18, -33, 4, 11], ![-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], ![-4, -35, -90, 13, 338, 263, -310, -316, 70, 88]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], ![0, -1, -6, -6, 20, 31, -18, -33, 4, 11], ![-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], ![-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], ![-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], ![0, -1, -6, -6, 20, 31, -18, -33, 4, 11], ![-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], ![-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], ![-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70], ![-70, -508, -952, 837, 3840, 1481, -3556, -2361, 812, 652]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], ![0, -1, -6, -6, 20, 31, -18, -33, 4, 11], ![-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], ![-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], ![-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70], ![-70, -508, -952, 837, 3840, 1481, -3556, -2361, 812, 652], ![-652, -3982, -4420, 12088, 21049, -7896, -20035, -948, 4811, 812]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], ![0, -1, -6, -6, 20, 31, -18, -33, 4, 11], ![-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], ![-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], ![-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70], ![-70, -508, -952, 837, 3840, 1481, -3556, -2361, 812, 652], ![-652, -3982, -4420, 12088, 21049, -7896, -20035, -948, 4811, 812], ![-812, -5524, -8854, 11820, 37260, 6433, -34692, -16787, 7984, 4811]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], ![0, -1, -6, -6, 20, 31, -18, -33, 4, 11], ![-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], ![-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], ![-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70], ![-70, -508, -952, 837, 3840, 1481, -3556, -2361, 812, 652], ![-652, -3982, -4420, 12088, 21049, -7896, -20035, -948, 4811, 812], ![-812, -5524, -8854, 11820, 37260, 6433, -34692, -16787, 7984, 4811], ![-4811, -29678, -34390, 87366, 160961, -49338, -152330, -15448, 36134, 7984]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1], [-70, -88, -4, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1], [-70, -88, -4, -11, 0, -1], [-652, -70, -88, -4, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1], [-70, -88, -4, -11, 0, -1], [-652, -70, -88, -4, -11, 0, -1], [-812, -652, -70, -88, -4, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-88, -4, -11, 0, -1], [-70, -88, -4, -11, 0, -1], [-652, -70, -88, -4, -11, 0, -1], [-812, -652, -70, -88, -4, -11, 0, -1], [-4811, -812, -652, -70, -88, -4, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 31, -18, -33, 4, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], [0, -1, -6, -6, 20, 31, -18, -33, 4, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], [0, -1, -6, -6, 20, 31, -18, -33, 4, 11], [-11, -66, -67, 214, 335, -178, -332, 26, 88, 4]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], [0, -1, -6, -6, 20, 31, -18, -33, 4, 11], [-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], [-4, -35, -90, 13, 338, 263, -310, -316, 70, 88]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], [0, -1, -6, -6, 20, 31, -18, -33, 4, 11], [-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], [-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], [-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], [0, -1, -6, -6, 20, 31, -18, -33, 4, 11], [-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], [-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], [-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70], [-70, -508, -952, 837, 3840, 1481, -3556, -2361, 812, 652]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], [0, -1, -6, -6, 20, 31, -18, -33, 4, 11], [-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], [-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], [-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70], [-70, -508, -952, 837, 3840, 1481, -3556, -2361, 812, 652], [-652, -3982, -4420, 12088, 21049, -7896, -20035, -948, 4811, 812]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], [0, -1, -6, -6, 20, 31, -18, -33, 4, 11], [-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], [-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], [-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70], [-70, -508, -952, 837, 3840, 1481, -3556, -2361, 812, 652], [-652, -3982, -4420, 12088, 21049, -7896, -20035, -948, 4811, 812], [-812, -5524, -8854, 11820, 37260, 6433, -34692, -16787, 7984, 4811]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -6, 20, 31, -18, -33, 4, 11, 0], [0, -1, -6, -6, 20, 31, -18, -33, 4, 11], [-11, -66, -67, 214, 335, -178, -332, 26, 88, 4], [-4, -35, -90, 13, 338, 263, -310, -316, 70, 88], [-88, -532, -563, 1670, 2741, -1246, -2641, 42, 652, 70], [-70, -508, -952, 837, 3840, 1481, -3556, -2361, 812, 652], [-652, -3982, -4420, 12088, 21049, -7896, -20035, -948, 4811, 812], [-812, -5524, -8854, 11820, 37260, 6433, -34692, -16787, 7984, 4811], [-4811, -29678, -34390, 87366, 160961, -49338, -152330, -15448, 36134, 7984]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp317 : Fact (Nat.Prime 317) := fact_iff.2 (by norm_num)
instance hp1223 : Fact (Nat.Prime 1223) := fact_iff.2 (by norm_num)
instance hp7487 : Fact (Nat.Prime 7487) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [1, 1]
  k := [1]
  f := [0, -3, -2, 11, 17, -7, -15, 4, 7, 1]
  g := [1, 0, 1, 1, 1, 1]
  h := [1, 0, 1, 1, 1, 1]
  a := [0, 0, 0, 1]
  b := [1, 0, 1, 1, 1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD317 : CertificateDedekindCriterionLists l 317 where
  n := 2
  a' := [56, 124, 107, 166, 220, 54, 315, 144]
  b' := [82, 195, 112, 29, 67, 118, 91, 187, 301]
  k := [273, 279, 243, 78, 301, 215, 97, 305, 1]
  f := [1, 1, 3, 2, 6, 1, 3, 1, 6, 1]
  g := [53, 45, 152, 77, 299, 6, 163, 25, 311, 1]
  h := [6, 1]
  a := [202, 116, 100, 222, 79, 285, 270, 96, 173]
  b := [62, 55, 71, 192, 146, 67, 101, 47, 144]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1223 : CertificateDedekindCriterionLists l 1223 where
  n := 2
  a' := [1201, 237, 352, 1146, 1115, 626, 513, 928]
  b' := [743, 59, 165, 723, 873, 936, 875, 643, 984]
  k := [727, 778, 559, 518, 1206, 555, 672, 1027, 1]
  f := [25, 92, 43, 95, 7, 45, 30, 83, 91, 1]
  g := [312, 1145, 525, 1180, 75, 561, 369, 1032, 1125, 1]
  h := [98, 1]
  a := [635, 821, 690, 156, 37, 596, 304, 1138, 390]
  b := [4, 89, 395, 654, 611, 285, 84, 978, 833]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7487 : CertificateDedekindCriterionLists l 7487 where
  n := 2
  a' := [7426, 3021, 889, 4346, 3022, 2747, 7172, 659]
  b' := [522, 3689, 2043, 4618, 5638, 6743, 6244, 4024, 5750]
  k := [1860, 5933, 4077, 1541, 6749, 7036, 3334, 4575, 1]
  f := [1041, 61, 944, 326, 1000, 285, 443, 215, 1173, 1]
  g := [5353, 310, 4854, 1673, 5141, 1462, 2277, 1104, 6031, 1]
  h := [1456, 1]
  a := [355, 5617, 279, 499, 469, 6632, 2529, 6118, 1035]
  b := [5092, 199, 2964, 2431, 4451, 861, 2645, 5622, 6452]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 317, 1223, 7487]
  exp := ![1, 1, 1, 1]
  pdgood := [2, 317, 1223, 7487]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp317.out
    exact hp1223.out
    exact hp7487.out
  a := [-3993632047256, 1864118467422, 34922130395274, -2293989143338, -53459320508118, -2281604870042, 23726921620418, 1160300938950, -2753079352360]
  b := [666572888715, 2349799858589, -1724712316073, -8992761244847, 1164044555746, 9009194038924, 153057171290, -2978369619561, -116030093895, 275307935236]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 317 T_ofList CD317
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1223 T_ofList CD1223
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7487 T_ofList CD7487

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

end VoightMaximalOrderD10R184

namespace VoightMaximalOrderD10R188

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3027840775444, [-2, -4, 16, 25, -36, -30, 32, 10, -10, -1, 1], 1⟩
local notation "l" => [-2, -4, 16, 25, -36, -30, 32, 10, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 4, -16, -25, 36, 30, -32, -10, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 4, -16, -25, 36, 30, -32, -10, 10, 1], ![2, 6, -12, -41, 11, 66, -2, -42, 0, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 4, -16, -25, 36, 30, -32, -10, 10, 1], ![2, 6, -12, -41, 11, 66, -2, -42, 0, 11], ![22, 46, -170, -287, 355, 341, -286, -112, 68, 11]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 4, -16, -25, 36, 30, -32, -10, 10, 1], ![2, 6, -12, -41, 11, 66, -2, -42, 0, 11], ![22, 46, -170, -287, 355, 341, -286, -112, 68, 11], ![22, 66, -130, -445, 109, 685, -11, -396, -2, 79]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 4, -16, -25, 36, 30, -32, -10, 10, 1], ![2, 6, -12, -41, 11, 66, -2, -42, 0, 11], ![22, 46, -170, -287, 355, 341, -286, -112, 68, 11], ![22, 66, -130, -445, 109, 685, -11, -396, -2, 79], ![158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 4, -16, -25, 36, 30, -32, -10, 10, 1], ![2, 6, -12, -41, 11, 66, -2, -42, 0, 11], ![22, 46, -170, -287, 355, 341, -286, -112, 68, 11], ![22, 66, -130, -445, 109, 685, -11, -396, -2, 79], ![158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77], ![154, 466, -894, -3123, 667, 4709, 15, -2613, -31, 471]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 4, -16, -25, 36, 30, -32, -10, 10, 1], ![2, 6, -12, -41, 11, 66, -2, -42, 0, 11], ![22, 46, -170, -287, 355, 341, -286, -112, 68, 11], ![22, 66, -130, -445, 109, 685, -11, -396, -2, 79], ![158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77], ![154, 466, -894, -3123, 667, 4709, 15, -2613, -31, 471], ![942, 2038, -7070, -12669, 13833, 14797, -10363, -4695, 2097, 440]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 4, -16, -25, 36, 30, -32, -10, 10, 1], ![2, 6, -12, -41, 11, 66, -2, -42, 0, 11], ![22, 46, -170, -287, 355, 341, -286, -112, 68, 11], ![22, 66, -130, -445, 109, 685, -11, -396, -2, 79], ![158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77], ![154, 466, -894, -3123, 667, 4709, 15, -2613, -31, 471], ![942, 2038, -7070, -12669, 13833, 14797, -10363, -4695, 2097, 440], ![880, 2702, -5002, -18070, 3171, 27033, 717, -14763, -295, 2537]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 4, -16, -25, 36, 30, -32, -10, 10, 1], ![2, 6, -12, -41, 11, 66, -2, -42, 0, 11], ![22, 46, -170, -287, 355, 341, -286, -112, 68, 11], ![22, 66, -130, -445, 109, 685, -11, -396, -2, 79], ![158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77], ![154, 466, -894, -3123, 667, 4709, 15, -2613, -31, 471], ![942, 2038, -7070, -12669, 13833, 14797, -10363, -4695, 2097, 440], ![880, 2702, -5002, -18070, 3171, 27033, 717, -14763, -295, 2537], ![5074, 11028, -37890, -68427, 73262, 79281, -54151, -24653, 10607, 2242]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-79, -11, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-79, -11, -11, -1, -1], [-77, -79, -11, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-79, -11, -11, -1, -1], [-77, -79, -11, -11, -1, -1], [-471, -77, -79, -11, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-79, -11, -11, -1, -1], [-77, -79, -11, -11, -1, -1], [-471, -77, -79, -11, -11, -1, -1], [-440, -471, -77, -79, -11, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-79, -11, -11, -1, -1], [-77, -79, -11, -11, -1, -1], [-471, -77, -79, -11, -11, -1, -1], [-440, -471, -77, -79, -11, -11, -1, -1], [-2537, -440, -471, -77, -79, -11, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 4, -16, -25, 36, 30, -32, -10, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 4, -16, -25, 36, 30, -32, -10, 10, 1], [2, 6, -12, -41, 11, 66, -2, -42, 0, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 4, -16, -25, 36, 30, -32, -10, 10, 1], [2, 6, -12, -41, 11, 66, -2, -42, 0, 11], [22, 46, -170, -287, 355, 341, -286, -112, 68, 11]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 4, -16, -25, 36, 30, -32, -10, 10, 1], [2, 6, -12, -41, 11, 66, -2, -42, 0, 11], [22, 46, -170, -287, 355, 341, -286, -112, 68, 11], [22, 66, -130, -445, 109, 685, -11, -396, -2, 79]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 4, -16, -25, 36, 30, -32, -10, 10, 1], [2, 6, -12, -41, 11, 66, -2, -42, 0, 11], [22, 46, -170, -287, 355, 341, -286, -112, 68, 11], [22, 66, -130, -445, 109, 685, -11, -396, -2, 79], [158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 4, -16, -25, 36, 30, -32, -10, 10, 1], [2, 6, -12, -41, 11, 66, -2, -42, 0, 11], [22, 46, -170, -287, 355, 341, -286, -112, 68, 11], [22, 66, -130, -445, 109, 685, -11, -396, -2, 79], [158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77], [154, 466, -894, -3123, 667, 4709, 15, -2613, -31, 471]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 4, -16, -25, 36, 30, -32, -10, 10, 1], [2, 6, -12, -41, 11, 66, -2, -42, 0, 11], [22, 46, -170, -287, 355, 341, -286, -112, 68, 11], [22, 66, -130, -445, 109, 685, -11, -396, -2, 79], [158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77], [154, 466, -894, -3123, 667, 4709, 15, -2613, -31, 471], [942, 2038, -7070, -12669, 13833, 14797, -10363, -4695, 2097, 440]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 4, -16, -25, 36, 30, -32, -10, 10, 1], [2, 6, -12, -41, 11, 66, -2, -42, 0, 11], [22, 46, -170, -287, 355, 341, -286, -112, 68, 11], [22, 66, -130, -445, 109, 685, -11, -396, -2, 79], [158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77], [154, 466, -894, -3123, 667, 4709, 15, -2613, -31, 471], [942, 2038, -7070, -12669, 13833, 14797, -10363, -4695, 2097, 440], [880, 2702, -5002, -18070, 3171, 27033, 717, -14763, -295, 2537]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 4, -16, -25, 36, 30, -32, -10, 10, 1], [2, 6, -12, -41, 11, 66, -2, -42, 0, 11], [22, 46, -170, -287, 355, 341, -286, -112, 68, 11], [22, 66, -130, -445, 109, 685, -11, -396, -2, 79], [158, 338, -1198, -2105, 2399, 2479, -1843, -801, 394, 77], [154, 466, -894, -3123, 667, 4709, 15, -2613, -31, 471], [942, 2038, -7070, -12669, 13833, 14797, -10363, -4695, 2097, 440], [880, 2702, -5002, -18070, 3171, 27033, 717, -14763, -295, 2537], [5074, 11028, -37890, -68427, 73262, 79281, -54151, -24653, 10607, 2242]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp619 : Fact (Nat.Prime 619) := fact_iff.2 (by norm_num)
instance hp719 : Fact (Nat.Prime 719) := fact_iff.2 (by norm_num)
instance hp1700801 : Fact (Nat.Prime 1700801) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 3
  a' := [0, 0, 0, 0, 1]
  b' := [1, 0, 0, 0, 0, 1, 1]
  k := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]
  f := [1, 2, -8, -12, 18, 15, -16, -5, 5, 1]
  g := [0, 1, 0, 0, 0, 0, 0, 1, 1]
  h := [0, 0, 1]
  a := [1, 1, 0, 1, 1]
  b := [1, 0, 1, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD619 : CertificateDedekindCriterionLists l 619 where
  n := 2
  a' := [193, 248, 300, 551, 476, 476, 54, 149]
  b' := [526, 58, 190, 467, 220, 542, 375, 423, 121]
  k := [331, 559, 244, 145, 300, 570, 467, 515, 1]
  f := [14, 196, 74, 346, 71, 328, 100, 37, 150, 1]
  g := [24, 336, 126, 593, 120, 562, 170, 63, 257, 1]
  h := [361, 1]
  a := [596, 370, 227, 601, 546, 406, 540, 275, 609]
  b := [194, 351, 63, 507, 571, 110, 305, 512, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD719 : CertificateDedekindCriterionLists l 719 where
  n := 2
  a' := [224, 128, 621, 104, 541, 586, 448, 112]
  b' := [126, 605, 167, 693, 424, 624, 257, 396, 387]
  k := [419, 517, 492, 237, 424, 150, 678, 332, 1]
  f := [91, 70, 152, 59, 28, 165, 40, 12, 141, 1]
  g := [339, 259, 565, 217, 103, 614, 146, 44, 525, 1]
  h := [193, 1]
  a := [230, 525, 390, 420, 703, 690, 502, 631, 704]
  b := [337, 394, 240, 658, 409, 363, 343, 80, 15]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1700801 : CertificateDedekindCriterionLists l 1700801 where
  n := 2
  a' := [1662796, 1151438, 989148, 869298, 9218, 1255669, 1379665, 1614004]
  b' := [1113559, 565989, 969222, 1615105, 715752, 293989, 188552, 494753, 198622]
  k := [1378962, 800317, 569969, 782333, 1054550, 1078958, 818647, 1539842, 1]
  f := [10294, 35817, 34661, 80255, 77730, 5697, 49331, 14182, 76671, 1]
  g := [217548, 756935, 732498, 1696058, 1642684, 120377, 1042534, 299702, 1620321, 1]
  h := [80479, 1]
  a := [646311, 664739, 1666102, 211351, 1388703, 610828, 495405, 184970, 590559]
  b := [1189135, 774363, 7139, 1234674, 28230, 1214871, 1250258, 485788, 1110242]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 619, 719, 1700801]
  exp := ![1, 1, 1, 1]
  pdgood := [2, 619, 719, 1700801]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp619.out
    exact hp719.out
    exact hp1700801.out
  a := [4484618119835, -54421105840388, 37665799208304, 121131777511792, -97883181336314, -57846186132920, 48484287523739, 7519486467506, -6512279958240]
  b := [-2620789156848, 1759621545575, 18463854389276, -12835099336516, -23570771743462, 17193214157498, 8048775890906, -6134300398971, -817071446333, 651227995824]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 619 T_ofList CD619
    exact satisfiesDedekindCriterion_of_certificate_lists T l 719 T_ofList CD719
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1700801 T_ofList CD1700801

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

end VoightMaximalOrderD10R188

namespace VoightMaximalOrderD10R193

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3162795438977, [1, 11, 32, 0, -64, -22, 39, 13, -10, -2, 1], 1⟩
local notation "l" => [1, 11, 32, 0, -64, -22, 39, 13, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, 0, 64, 22, -39, -13, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], ![-2, -23, -75, -32, 128, 108, -56, -65, 7, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], ![-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], ![-14, -156, -471, -75, 864, 436, -438, -238, 75, 35]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], ![-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], ![-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], ![-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], ![-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], ![-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], ![-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], ![-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], ![-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], ![-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], ![-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], ![-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402], ![-402, -4567, -14494, -5039, 24452, 17653, -10323, -9247, 1206, 1361]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], ![-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], ![-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], ![-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], ![-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402], ![-402, -4567, -14494, -5039, 24452, 17653, -10323, -9247, 1206, 1361], ![-1361, -15373, -48119, -14494, 82065, 54394, -35426, -28016, 4363, 3928]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], ![-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], ![-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], ![-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], ![-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402], ![-402, -4567, -14494, -5039, 24452, 17653, -10323, -9247, 1206, 1361], ![-1361, -15373, -48119, -14494, 82065, 54394, -35426, -28016, 4363, 3928], ![-3928, -44569, -141069, -48119, 236898, 168481, -98798, -86490, 11264, 12219]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], ![-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], ![-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], ![-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], ![-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402], ![-402, -4567, -14494, -5039, 24452, 17653, -10323, -9247, 1206, 1361], ![-1361, -15373, -48119, -14494, 82065, 54394, -35426, -28016, 4363, 3928], ![-3928, -44569, -141069, -48119, 236898, 168481, -98798, -86490, 11264, 12219], ![-12219, -138337, -435577, -141069, 733897, 505716, -308060, -257645, 35700, 35702]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-35, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-35, -14, -2, -1], [-145, -35, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-35, -14, -2, -1], [-145, -35, -14, -2, -1], [-402, -145, -35, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-35, -14, -2, -1], [-145, -35, -14, -2, -1], [-402, -145, -35, -14, -2, -1], [-1361, -402, -145, -35, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-35, -14, -2, -1], [-145, -35, -14, -2, -1], [-402, -145, -35, -14, -2, -1], [-1361, -402, -145, -35, -14, -2, -1], [-3928, -1361, -402, -145, -35, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-35, -14, -2, -1], [-145, -35, -14, -2, -1], [-402, -145, -35, -14, -2, -1], [-1361, -402, -145, -35, -14, -2, -1], [-3928, -1361, -402, -145, -35, -14, -2, -1], [-12219, -3928, -1361, -402, -145, -35, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, 0, 64, 22, -39, -13, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], [-2, -23, -75, -32, 128, 108, -56, -65, 7, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], [-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], [-14, -156, -471, -75, 864, 436, -438, -238, 75, 35]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], [-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], [-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], [-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], [-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], [-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], [-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], [-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], [-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], [-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], [-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], [-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402], [-402, -4567, -14494, -5039, 24452, 17653, -10323, -9247, 1206, 1361]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], [-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], [-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], [-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], [-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402], [-402, -4567, -14494, -5039, 24452, 17653, -10323, -9247, 1206, 1361], [-1361, -15373, -48119, -14494, 82065, 54394, -35426, -28016, 4363, 3928]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], [-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], [-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], [-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], [-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402], [-402, -4567, -14494, -5039, 24452, 17653, -10323, -9247, 1206, 1361], [-1361, -15373, -48119, -14494, 82065, 54394, -35426, -28016, 4363, 3928], [-3928, -44569, -141069, -48119, 236898, 168481, -98798, -86490, 11264, 12219]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, 0, 64, 22, -39, -13, 10, 2], [-2, -23, -75, -32, 128, 108, -56, -65, 7, 14], [-14, -156, -471, -75, 864, 436, -438, -238, 75, 35], [-35, -399, -1276, -471, 2165, 1634, -929, -893, 112, 145], [-145, -1630, -5039, -1276, 8809, 5355, -4021, -2814, 557, 402], [-402, -4567, -14494, -5039, 24452, 17653, -10323, -9247, 1206, 1361], [-1361, -15373, -48119, -14494, 82065, 54394, -35426, -28016, 4363, 3928], [-3928, -44569, -141069, -48119, 236898, 168481, -98798, -86490, 11264, 12219], [-12219, -138337, -435577, -141069, 733897, 505716, -308060, -257645, 35700, 35702]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp5393 : Fact (Nat.Prime 5393) := fact_iff.2 (by norm_num)

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [59, 35, 27, 48, 48, 3, 53]
  b' := [37, 42, 9, 42, 50, 25, 31, 1]
  k := [13, 39, 16, 27, 49, 16, 1]
  f := [10, 45, 32, 46, 13, 46, 41, 36, 7, 1]
  g := [47, 24, 53, 2, 44, 38, 40, 7, 1]
  h := [13, 52, 1]
  a := [6, 38, 1, 38, 16, 2, 30, 54]
  b := [26, 30, 25, 40, 58, 16, 31, 31, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [376, 240, 174, 320, 166, 3, 279]
  b' := [75, 348, 288, 223, 271, 121, 380, 114]
  k := [305, 131, 271, 142, 236, 132, 1]
  f := [48, 84, 83, 89, 277, 539, 348, 97, 55, 1]
  g := [59, 43, 58, 50, 289, 367, 52, 65, 1]
  h := [323, 330, 1]
  a := [341, 266, 102, 136, 280, 314, 143, 65]
  b := [308, 305, 209, 87, 33, 98, 8, 110, 332]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5393 : CertificateDedekindCriterionLists l 5393 where
  n := 2
  a' := [4416, 517, 4892, 2015, 481, 3795, 2235, 1269]
  b' := [202, 316, 1799, 1517, 621, 5219, 3307, 79, 5252]
  k := [4974, 3537, 4258, 4429, 5191, 640, 4967, 4550, 1]
  f := [2587, 647, 2052, 1949, 222, 2694, 2815, 2155, 1315, 1]
  g := [4476, 1118, 3550, 3371, 383, 4661, 4869, 3727, 2274, 1]
  h := [3117, 1]
  a := [446, 2544, 622, 1237, 4772, 5389, 3626, 5296, 4860]
  b := [5228, 786, 1268, 1766, 2807, 3192, 4238, 1285, 533]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![61, 397, 5393]
  exp := ![1, 1, 1]
  pdgood := [61, 397, 5393]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp61.out
    exact hp397.out
    exact hp5393.out
  a := [-14811519452, -14163460974, 61049917245, 48697249502, -58281607832, -35090616410, 21873961792, 6884624540, -3144238600]
  b := [1358374703, 8195835814, 4016662167, -16030731159, -9581886688, 10068173640, 4958814589, -2791743998, -751347226, 314423860]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5393 T_ofList CD5393

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

end VoightMaximalOrderD10R193

end TraceEuclidean
