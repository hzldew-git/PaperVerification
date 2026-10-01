import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk215
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

namespace VoightMaximalOrderD10R560

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6169740672697, [1, 3, -54, 46, 66, -74, -14, 32, -4, -4, 1], 1⟩
local notation "l" => [1, 3, -54, 46, 66, -74, -14, 32, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 54, -46, -66, 74, 14, -32, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], ![-4, -13, 213, -130, -310, 230, 130, -114, -16, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], ![-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], ![-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], ![-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], ![-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], ![-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], ![-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], ![-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], ![-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], ![-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], ![-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], ![-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], ![-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], ![-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634], ![-634, -2124, 33506, -17388, -48664, 30387, 20373, -13894, -2502, 1886]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], ![-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], ![-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], ![-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], ![-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634], ![-634, -2124, 33506, -17388, -48664, 30387, 20373, -13894, -2502, 1886], ![-1886, -6292, 99720, -53250, -141864, 90900, 56791, -39979, -6350, 5042]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], ![-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], ![-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], ![-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], ![-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634], ![-634, -2124, 33506, -17388, -48664, 30387, 20373, -13894, -2502, 1886], ![-1886, -6292, 99720, -53250, -141864, 90900, 56791, -39979, -6350, 5042], ![-5042, -17012, 265976, -132212, -386022, 231244, 161488, -104553, -19811, 13818]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], ![-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], ![-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], ![-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], ![-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634], ![-634, -2124, 33506, -17388, -48664, 30387, 20373, -13894, -2502, 1886], ![-1886, -6292, 99720, -53250, -141864, 90900, 56791, -39979, -6350, 5042], ![-5042, -17012, 265976, -132212, -386022, 231244, 161488, -104553, -19811, 13818], ![-13818, -46496, 729160, -369652, -1044200, 636510, 424696, -280688, -49281, 35461]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-222, -64, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-222, -64, -20, -4, -1], [-634, -222, -64, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-222, -64, -20, -4, -1], [-634, -222, -64, -20, -4, -1], [-1886, -634, -222, -64, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-222, -64, -20, -4, -1], [-634, -222, -64, -20, -4, -1], [-1886, -634, -222, -64, -20, -4, -1], [-5042, -1886, -634, -222, -64, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-64, -20, -4, -1], [-222, -64, -20, -4, -1], [-634, -222, -64, -20, -4, -1], [-1886, -634, -222, -64, -20, -4, -1], [-5042, -1886, -634, -222, -64, -20, -4, -1], [-13818, -5042, -1886, -634, -222, -64, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 54, -46, -66, 74, 14, -32, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], [-4, -13, 213, -130, -310, 230, 130, -114, -16, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], [-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], [-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], [-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], [-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], [-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], [-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], [-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], [-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], [-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], [-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], [-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], [-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], [-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634], [-634, -2124, 33506, -17388, -48664, 30387, 20373, -13894, -2502, 1886]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], [-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], [-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], [-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], [-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634], [-634, -2124, 33506, -17388, -48664, 30387, 20373, -13894, -2502, 1886], [-1886, -6292, 99720, -53250, -141864, 90900, 56791, -39979, -6350, 5042]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], [-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], [-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], [-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], [-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634], [-634, -2124, 33506, -17388, -48664, 30387, 20373, -13894, -2502, 1886], [-1886, -6292, 99720, -53250, -141864, 90900, 56791, -39979, -6350, 5042], [-5042, -17012, 265976, -132212, -386022, 231244, 161488, -104553, -19811, 13818]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 54, -46, -66, 74, 14, -32, 4, 4], [-4, -13, 213, -130, -310, 230, 130, -114, -16, 20], [-20, -64, 1067, -707, -1450, 1170, 510, -510, -34, 64], [-64, -212, 3392, -1877, -4931, 3286, 2066, -1538, -254, 222], [-222, -730, 11776, -6820, -16529, 11497, 6394, -5038, -650, 634], [-634, -2124, 33506, -17388, -48664, 30387, 20373, -13894, -2502, 1886], [-1886, -6292, 99720, -53250, -141864, 90900, 56791, -39979, -6350, 5042], [-5042, -17012, 265976, -132212, -386022, 231244, 161488, -104553, -19811, 13818], [-13818, -46496, 729160, -369652, -1044200, 636510, 424696, -280688, -49281, 35461]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp17203 : Fact (Nat.Prime 17203) := fact_iff.2 (by norm_num)
instance hp7319251 : Fact (Nat.Prime 7319251) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [4, 0, 0, 5, 0, 1]
  b' := [0, 0, 3, 1, 5, 2, 6]
  k := [4, 2, 0, 5, 5, 0, 1]
  f := [1, 1, 8, -6, -7, 14, 5, 0, 5, 2]
  g := [2, 0, 0, 1, 3, 2, 2, 5, 1]
  h := [4, 5, 1]
  a := [6, 3, 5, 1, 1, 1, 0, 6]
  b := [1, 6, 0, 6, 1, 0, 5, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17203 : CertificateDedekindCriterionLists l 17203 where
  n := 2
  a' := [5339, 8717, 14877, 3028, 10130, 14104, 16753, 2084]
  b' := [15575, 12383, 14181, 9963, 5933, 11116, 15796, 770, 15060]
  k := [9227, 8610, 11874, 10902, 9315, 11656, 15589, 10217, 1]
  f := [1510, 2658, 308, 105, 3226, 3109, 521, 835, 2782, 1]
  g := [7441, 13096, 1514, 517, 15897, 15316, 2563, 4114, 13708, 1]
  h := [3491, 1]
  a := [8121, 12686, 7319, 2061, 1482, 6045, 7306, 10291, 6061]
  b := [15088, 13048, 13708, 12446, 2819, 12793, 7152, 15051, 11142]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7319251 : CertificateDedekindCriterionLists l 7319251 where
  n := 2
  a' := [4069553, 3961363, 1768578, 7274940, 947694, 2446038, 2703726, 6997491]
  b' := [208295, 4892778, 4857282, 4691147, 5109750, 7106711, 1049347, 118774, 6541752]
  k := [3084896, 3920605, 1804952, 4766220, 2032041, 7273965, 7176644, 1429307, 1]
  f := [410259, 2934510, 227658, 88969, 1778682, 77693, 2108486, 579132, 1760032, 1]
  g := [1019633, 7293254, 565805, 221118, 4420629, 193092, 5240304, 1439338, 4374277, 1]
  h := [2944970, 1]
  a := [6277138, 190286, 6596815, 7115313, 1364806, 7269945, 2817947, 553126, 5428004]
  b := [1232141, 6489360, 5037714, 827400, 4846502, 4907605, 5284201, 7080114, 1891247]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![7, 17203, 7319251]
  exp := ![1, 1, 1]
  pdgood := [7, 17203, 7319251]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp17203.out
    exact hp7319251.out
  a := [6477701706472, -199391698995864, 139633506135336, 577193498526128, -355349015244472, -363931677464928, 207624287870816, 60343054499728, -32361890089980]
  b := [-1865436727267, -7169524222796, 97153045100874, -28940510522592, -140561620824790, 56599756758148, 59043447855568, -25597769987248, -7328781053572, 3236189008998]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17203 T_ofList CD17203
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7319251 T_ofList CD7319251

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

end VoightMaximalOrderD10R560

namespace VoightMaximalOrderD10R561

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6175137950000, [1, 3, -25, 21, 44, -48, -22, 29, 0, -5, 1], 1⟩
local notation "l" => [1, 3, -25, 21, 44, -48, -22, 29, 0, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 25, -21, -44, 48, 22, -29, 0, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], ![-5, -16, 122, -80, -241, 196, 158, -123, -29, 25]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], ![-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], ![-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], ![-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], ![-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], ![-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], ![-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], ![-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], ![-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], ![-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], ![-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], ![-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], ![-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], ![-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218], ![-1218, -4011, 29283, -16966, -58769, 41349, 39305, -24040, -7282, 4052]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], ![-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], ![-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], ![-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], ![-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218], ![-1218, -4011, 29283, -16966, -58769, 41349, 39305, -24040, -7282, 4052], ![-4052, -13374, 97289, -55809, -195254, 135727, 130493, -78203, -24040, 12978]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], ![-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], ![-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], ![-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], ![-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218], ![-1218, -4011, 29283, -16966, -58769, 41349, 39305, -24040, -7282, 4052], ![-4052, -13374, 97289, -55809, -195254, 135727, 130493, -78203, -24040, 12978], ![-12978, -42986, 311076, -175249, -626841, 427690, 421243, -245869, -78203, 40850]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], ![-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], ![-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], ![-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], ![-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218], ![-1218, -4011, 29283, -16966, -58769, 41349, 39305, -24040, -7282, 4052], ![-4052, -13374, 97289, -55809, -195254, 135727, 130493, -78203, -24040, 12978], ![-12978, -42986, 311076, -175249, -626841, 427690, 421243, -245869, -78203, 40850], ![-40850, -135528, 978264, -546774, -1972649, 1333959, 1326390, -763407, -245869, 126047]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-357, -96, -25, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-357, -96, -25, -5, -1], [-1218, -357, -96, -25, -5, -1]], ![[], [], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-357, -96, -25, -5, -1], [-1218, -357, -96, -25, -5, -1], [-4052, -1218, -357, -96, -25, -5, -1]], ![[], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-357, -96, -25, -5, -1], [-1218, -357, -96, -25, -5, -1], [-4052, -1218, -357, -96, -25, -5, -1], [-12978, -4052, -1218, -357, -96, -25, -5, -1]], ![[], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-357, -96, -25, -5, -1], [-1218, -357, -96, -25, -5, -1], [-4052, -1218, -357, -96, -25, -5, -1], [-12978, -4052, -1218, -357, -96, -25, -5, -1], [-40850, -12978, -4052, -1218, -357, -96, -25, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 25, -21, -44, 48, 22, -29, 0, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], [-5, -16, 122, -80, -241, 196, 158, -123, -29, 25]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], [-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], [-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], [-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], [-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], [-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], [-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], [-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], [-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], [-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], [-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], [-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], [-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], [-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218], [-1218, -4011, 29283, -16966, -58769, 41349, 39305, -24040, -7282, 4052]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], [-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], [-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], [-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], [-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218], [-1218, -4011, 29283, -16966, -58769, 41349, 39305, -24040, -7282, 4052], [-4052, -13374, 97289, -55809, -195254, 135727, 130493, -78203, -24040, 12978]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], [-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], [-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], [-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], [-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218], [-1218, -4011, 29283, -16966, -58769, 41349, 39305, -24040, -7282, 4052], [-4052, -13374, 97289, -55809, -195254, 135727, 130493, -78203, -24040, 12978], [-12978, -42986, 311076, -175249, -626841, 427690, 421243, -245869, -78203, 40850]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 25, -21, -44, 48, 22, -29, 0, 5], [-5, -16, 122, -80, -241, 196, 158, -123, -29, 25], [-25, -80, 609, -403, -1180, 959, 746, -567, -123, 96], [-96, -313, 2320, -1407, -4627, 3428, 3071, -2038, -567, 357], [-357, -1167, 8612, -5177, -17115, 12509, 11282, -7282, -2038, 1218], [-1218, -4011, 29283, -16966, -58769, 41349, 39305, -24040, -7282, 4052], [-4052, -13374, 97289, -55809, -195254, 135727, 130493, -78203, -24040, 12978], [-12978, -42986, 311076, -175249, -626841, 427690, 421243, -245869, -78203, 40850], [-40850, -135528, 978264, -546774, -1972649, 1333959, 1326390, -763407, -245869, 126047]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp123502759 : Fact (Nat.Prime 123502759) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [0, 1, 1, 0, 1, 0, 1]
  k := [1, 1, 0, 0, 1, 1, 1]
  f := [0, -1, 13, -10, -21, 25, 12, -14, 1, 3]
  g := [1, 0, 0, 1, 1, 0, 1, 0, 1]
  h := [1, 1, 1]
  a := [0, 1, 0, 0, 1, 0, 1, 1]
  b := [1, 0, 1, 0, 1, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2]
  b' := [1, 2, 2, 3, 2]
  k := [1]
  f := [0, 1, 9, -1, -8, 10, 6, -5, 0, 1]
  g := [1, 4, 2, 0, 0, 1]
  h := [1, 4, 2, 0, 0, 1]
  a := [0, 1, 0, 0, 3]
  b := [1, 1, 3, 2, 2, 2, 0, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD123502759 : CertificateDedekindCriterionLists l 123502759 where
  n := 2
  a' := [118628663, 30702809, 122657958, 29124029, 22756695, 6208092, 9676875, 25059657]
  b' := [18126230, 117034948, 16262258, 1755370, 40856373, 120517454, 83594996, 101823693, 38383180]
  k := [83807241, 40686925, 89316218, 77707651, 102192416, 81723075, 67027326, 26230162, 1]
  f := [33251977, 18115727, 35272931, 46007160, 30203117, 28793039, 12004677, 24508739, 29482963, 1]
  g := [84437164, 46001492, 89568997, 116826559, 76695153, 73114525, 30483626, 62235349, 74866458, 1]
  h := [48636296, 1]
  a := [46355283, 36761104, 88875059, 52467642, 43604706, 118515731, 37424640, 42481275, 105000520]
  b := [84637514, 101759312, 56481668, 114754049, 30740618, 67735818, 61878295, 56339251, 18502239]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 5, 123502759]
  exp := ![1, 1, 1]
  pdgood := [2, 5, 123502759]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp123502759.out
  a := [91704740107, -1335174321430, -670463848321, 4039376759925, 511125816541, -3033619130088, 324892990285, 629095933625, -157993096510]
  b := [-30156570839, -149256146947, 468553976931, 268416592972, -817922051920, -120030449911, 438639131336, -36582949062, -70809248188, 15799309651]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 123502759 T_ofList CD123502759

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

end VoightMaximalOrderD10R561

namespace VoightMaximalOrderD10R564

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6183045726272, [-23, -31, 71, 67, -88, -47, 50, 12, -12, -1, 1], 1⟩
local notation "l" => [-23, -31, 71, 67, -88, -47, 50, 12, -12, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![23, 31, -71, -67, 88, 47, -50, -12, 12, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![23, 31, -71, -67, 88, 47, -50, -12, 12, 1], ![23, 54, -40, -138, 21, 135, -3, -62, 0, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![23, 31, -71, -67, 88, 47, -50, -12, 12, 1], ![23, 54, -40, -138, 21, 135, -3, -62, 0, 13], ![299, 426, -869, -911, 1006, 632, -515, -159, 94, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![23, 31, -71, -67, 88, 47, -50, -12, 12, 1], ![23, 54, -40, -138, 21, 135, -3, -62, 0, 13], ![299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], ![299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![23, 31, -71, -67, 88, 47, -50, -12, 12, 1], ![23, 54, -40, -138, 21, 135, -3, -62, 0, 13], ![299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], ![299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], ![2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![23, 31, -71, -67, 88, 47, -50, -12, 12, 1], ![23, 54, -40, -138, 21, 135, -3, -62, 0, 13], ![299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], ![299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], ![2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104], ![2392, 5685, -3768, -13863, 1486, 12564, 62, -4981, -54, 717]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![23, 31, -71, -67, 88, 47, -50, -12, 12, 1], ![23, 54, -40, -138, 21, 135, -3, -62, 0, 13], ![299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], ![299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], ![2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104], ![2392, 5685, -3768, -13863, 1486, 12564, 62, -4981, -54, 717], ![16491, 24619, -45222, -51807, 49233, 35185, -23286, -8542, 3623, 663]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![23, 31, -71, -67, 88, 47, -50, -12, 12, 1], ![23, 54, -40, -138, 21, 135, -3, -62, 0, 13], ![299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], ![299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], ![2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104], ![2392, 5685, -3768, -13863, 1486, 12564, 62, -4981, -54, 717], ![16491, 24619, -45222, -51807, 49233, 35185, -23286, -8542, 3623, 663], ![15249, 37044, -22454, -89643, 6537, 80394, 2035, -31242, -586, 4286]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![23, 31, -71, -67, 88, 47, -50, -12, 12, 1], ![23, 54, -40, -138, 21, 135, -3, -62, 0, 13], ![299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], ![299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], ![2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104], ![2392, 5685, -3768, -13863, 1486, 12564, 62, -4981, -54, 717], ![16491, 24619, -45222, -51807, 49233, 35185, -23286, -8542, 3623, 663], ![15249, 37044, -22454, -89643, 6537, 80394, 2035, -31242, -586, 4286], ![98578, 148115, -267262, -309616, 287525, 207979, -133906, -49397, 20190, 3700]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-13, -13, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-13, -13, -1, -1], [-107, -13, -13, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-13, -13, -1, -1], [-107, -13, -13, -1, -1], [-104, -107, -13, -13, -1, -1]], ![[], [], [], [-1], [-1, -1], [-13, -1, -1], [-13, -13, -1, -1], [-107, -13, -13, -1, -1], [-104, -107, -13, -13, -1, -1], [-717, -104, -107, -13, -13, -1, -1]], ![[], [], [-1], [-1, -1], [-13, -1, -1], [-13, -13, -1, -1], [-107, -13, -13, -1, -1], [-104, -107, -13, -13, -1, -1], [-717, -104, -107, -13, -13, -1, -1], [-663, -717, -104, -107, -13, -13, -1, -1]], ![[], [-1], [-1, -1], [-13, -1, -1], [-13, -13, -1, -1], [-107, -13, -13, -1, -1], [-104, -107, -13, -13, -1, -1], [-717, -104, -107, -13, -13, -1, -1], [-663, -717, -104, -107, -13, -13, -1, -1], [-4286, -663, -717, -104, -107, -13, -13, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [23, 31, -71, -67, 88, 47, -50, -12, 12, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [23, 31, -71, -67, 88, 47, -50, -12, 12, 1], [23, 54, -40, -138, 21, 135, -3, -62, 0, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [23, 31, -71, -67, 88, 47, -50, -12, 12, 1], [23, 54, -40, -138, 21, 135, -3, -62, 0, 13], [299, 426, -869, -911, 1006, 632, -515, -159, 94, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [23, 31, -71, -67, 88, 47, -50, -12, 12, 1], [23, 54, -40, -138, 21, 135, -3, -62, 0, 13], [299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], [299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [23, 31, -71, -67, 88, 47, -50, -12, 12, 1], [23, 54, -40, -138, 21, 135, -3, -62, 0, 13], [299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], [299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], [2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [23, 31, -71, -67, 88, 47, -50, -12, 12, 1], [23, 54, -40, -138, 21, 135, -3, -62, 0, 13], [299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], [299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], [2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104], [2392, 5685, -3768, -13863, 1486, 12564, 62, -4981, -54, 717]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [23, 31, -71, -67, 88, 47, -50, -12, 12, 1], [23, 54, -40, -138, 21, 135, -3, -62, 0, 13], [299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], [299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], [2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104], [2392, 5685, -3768, -13863, 1486, 12564, 62, -4981, -54, 717], [16491, 24619, -45222, -51807, 49233, 35185, -23286, -8542, 3623, 663]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [23, 31, -71, -67, 88, 47, -50, -12, 12, 1], [23, 54, -40, -138, 21, 135, -3, -62, 0, 13], [299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], [299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], [2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104], [2392, 5685, -3768, -13863, 1486, 12564, 62, -4981, -54, 717], [16491, 24619, -45222, -51807, 49233, 35185, -23286, -8542, 3623, 663], [15249, 37044, -22454, -89643, 6537, 80394, 2035, -31242, -586, 4286]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [23, 31, -71, -67, 88, 47, -50, -12, 12, 1], [23, 54, -40, -138, 21, 135, -3, -62, 0, 13], [299, 426, -869, -911, 1006, 632, -515, -159, 94, 13], [299, 702, -497, -1740, 233, 1617, -18, -671, -3, 107], [2461, 3616, -6895, -7666, 7676, 5262, -3733, -1302, 613, 104], [2392, 5685, -3768, -13863, 1486, 12564, 62, -4981, -54, 717], [16491, 24619, -45222, -51807, 49233, 35185, -23286, -8542, 3623, 663], [15249, 37044, -22454, -89643, 6537, 80394, 2035, -31242, -586, 4286], [98578, 148115, -267262, -309616, 287525, 207979, -133906, -49397, 20190, 3700]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp96610089473 : Fact (Nat.Prime 96610089473) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 0, 1]
  k := [1, 1, 1, 1, 1]
  f := [12, 16, -35, -32, 45, 24, -24, -5, 6, 1]
  g := [1, 1, 0, 1, 1, 0, 0, 1]
  h := [1, 0, 1, 1]
  a := [1, 0, 1, 0, 1]
  b := [1, 1, 1, 1, 0, 0, 1]
  c := [0, 0, 1, 1]
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD96610089473 : CertificateDedekindCriterionLists l 96610089473 where
  n := 2
  a' := [17793972732, 56162673155, 63923718398, 38075652643, 35869270171, 50595005537, 14805666717, 37532940241]
  b' := [51227868022, 6751841553, 54785879339, 66946729365, 93619803383, 52193662180, 44009005734, 10723661787, 49501945236]
  k := [84979142134, 27463461523, 15404398016, 64037600649, 25666036111, 88850692016, 18975913394, 33256149286, 1]
  f := [11999502382, 25495890284, 24379614942, 6807136945, 21035283352, 25270983699, 18019181240, 26654081876, 21290576294, 1]
  g := [36596713491, 77758707170, 74354231919, 20760764281, 64154513539, 77072775237, 54955846681, 81291020803, 64933119379, 1]
  h := [31676970093, 1]
  a := [80605876411, 1890021135, 95667623899, 94489509250, 88547494941, 16114273957, 32156347305, 18619400481, 10111612622]
  b := [16731551402, 74925276777, 73473011699, 91210590809, 28778508629, 53967311401, 30418138265, 78111461766, 86498476851]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 96610089473]
  exp := ![1, 1]
  pdgood := [2, 96610089473]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp96610089473.out
  a := [-2343473168645, 8733041139543, 22820652749530, -8941373647118, -26090657437604, 3124511516334, 9327729442921, -373786149237, -1032680025970]
  b := [1732472990319, 3799964085284, -2392384270141, -7242312921084, 1125072925649, 4698499937341, -271042675328, -1193648132251, 27051814664, 103268002597]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 96610089473 T_ofList CD96610089473

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

end VoightMaximalOrderD10R564

namespace VoightMaximalOrderD10R566

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6203166128125, [-1, 3, 27, 0, -57, -5, 42, 4, -12, -1, 1], 1⟩
local notation "l" => [-1, 3, 27, 0, -57, -5, 42, 4, -12, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -27, 0, 57, 5, -42, -4, 12, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -27, 0, 57, 5, -42, -4, 12, 1], ![1, -2, -30, -27, 57, 62, -37, -46, 8, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -27, 0, 57, 5, -42, -4, 12, 1], ![1, -2, -30, -27, 57, 62, -37, -46, 8, 13], ![13, -38, -353, -30, 714, 122, -484, -89, 110, 21]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -27, 0, 57, 5, -42, -4, 12, 1], ![1, -2, -30, -27, 57, 62, -37, -46, 8, 13], ![13, -38, -353, -30, 714, 122, -484, -89, 110, 21], ![21, -50, -605, -353, 1167, 819, -760, -568, 163, 131]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -27, 0, 57, 5, -42, -4, 12, 1], ![1, -2, -30, -27, 57, 62, -37, -46, 8, 13], ![13, -38, -353, -30, 714, 122, -484, -89, 110, 21], ![21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], ![131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -27, 0, 57, 5, -42, -4, 12, 1], ![1, -2, -30, -27, 57, 62, -37, -46, 8, 13], ![13, -38, -353, -30, 714, 122, -484, -89, 110, 21], ![21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], ![131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294], ![294, -751, -8310, -3587, 16153, 8584, -10526, -5859, 2244, 1298]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -27, 0, 57, 5, -42, -4, 12, 1], ![1, -2, -30, -27, 57, 62, -37, -46, 8, 13], ![13, -38, -353, -30, 714, 122, -484, -89, 110, 21], ![21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], ![131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294], ![294, -751, -8310, -3587, 16153, 8584, -10526, -5859, 2244, 1298], ![1298, -3600, -35797, -8310, 70399, 22643, -45932, -15718, 9717, 3542]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -27, 0, 57, 5, -42, -4, 12, 1], ![1, -2, -30, -27, 57, 62, -37, -46, 8, 13], ![13, -38, -353, -30, 714, 122, -484, -89, 110, 21], ![21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], ![131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294], ![294, -751, -8310, -3587, 16153, 8584, -10526, -5859, 2244, 1298], ![1298, -3600, -35797, -8310, 70399, 22643, -45932, -15718, 9717, 3542], ![3542, -9328, -99234, -35797, 193584, 88109, -126121, -60100, 26786, 13259]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -27, 0, 57, 5, -42, -4, 12, 1], ![1, -2, -30, -27, 57, 62, -37, -46, 8, 13], ![13, -38, -353, -30, 714, 122, -484, -89, 110, 21], ![21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], ![131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294], ![294, -751, -8310, -3587, 16153, 8584, -10526, -5859, 2244, 1298], ![1298, -3600, -35797, -8310, 70399, 22643, -45932, -15718, 9717, 3542], ![3542, -9328, -99234, -35797, 193584, 88109, -126121, -60100, 26786, 13259], ![13259, -36235, -367321, -99234, 719966, 259879, -468769, -179157, 99008, 40045]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-21, -13, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-21, -13, -1, -1], [-131, -21, -13, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-21, -13, -1, -1], [-131, -21, -13, -1, -1], [-294, -131, -21, -13, -1, -1]], ![[], [], [], [-1], [-1, -1], [-13, -1, -1], [-21, -13, -1, -1], [-131, -21, -13, -1, -1], [-294, -131, -21, -13, -1, -1], [-1298, -294, -131, -21, -13, -1, -1]], ![[], [], [-1], [-1, -1], [-13, -1, -1], [-21, -13, -1, -1], [-131, -21, -13, -1, -1], [-294, -131, -21, -13, -1, -1], [-1298, -294, -131, -21, -13, -1, -1], [-3542, -1298, -294, -131, -21, -13, -1, -1]], ![[], [-1], [-1, -1], [-13, -1, -1], [-21, -13, -1, -1], [-131, -21, -13, -1, -1], [-294, -131, -21, -13, -1, -1], [-1298, -294, -131, -21, -13, -1, -1], [-3542, -1298, -294, -131, -21, -13, -1, -1], [-13259, -3542, -1298, -294, -131, -21, -13, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -27, 0, 57, 5, -42, -4, 12, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -27, 0, 57, 5, -42, -4, 12, 1], [1, -2, -30, -27, 57, 62, -37, -46, 8, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -27, 0, 57, 5, -42, -4, 12, 1], [1, -2, -30, -27, 57, 62, -37, -46, 8, 13], [13, -38, -353, -30, 714, 122, -484, -89, 110, 21]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -27, 0, 57, 5, -42, -4, 12, 1], [1, -2, -30, -27, 57, 62, -37, -46, 8, 13], [13, -38, -353, -30, 714, 122, -484, -89, 110, 21], [21, -50, -605, -353, 1167, 819, -760, -568, 163, 131]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -27, 0, 57, 5, -42, -4, 12, 1], [1, -2, -30, -27, 57, 62, -37, -46, 8, 13], [13, -38, -353, -30, 714, 122, -484, -89, 110, 21], [21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], [131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -27, 0, 57, 5, -42, -4, 12, 1], [1, -2, -30, -27, 57, 62, -37, -46, 8, 13], [13, -38, -353, -30, 714, 122, -484, -89, 110, 21], [21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], [131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294], [294, -751, -8310, -3587, 16153, 8584, -10526, -5859, 2244, 1298]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -27, 0, 57, 5, -42, -4, 12, 1], [1, -2, -30, -27, 57, 62, -37, -46, 8, 13], [13, -38, -353, -30, 714, 122, -484, -89, 110, 21], [21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], [131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294], [294, -751, -8310, -3587, 16153, 8584, -10526, -5859, 2244, 1298], [1298, -3600, -35797, -8310, 70399, 22643, -45932, -15718, 9717, 3542]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -27, 0, 57, 5, -42, -4, 12, 1], [1, -2, -30, -27, 57, 62, -37, -46, 8, 13], [13, -38, -353, -30, 714, 122, -484, -89, 110, 21], [21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], [131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294], [294, -751, -8310, -3587, 16153, 8584, -10526, -5859, 2244, 1298], [1298, -3600, -35797, -8310, 70399, 22643, -45932, -15718, 9717, 3542], [3542, -9328, -99234, -35797, 193584, 88109, -126121, -60100, 26786, 13259]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -27, 0, 57, 5, -42, -4, 12, 1], [1, -2, -30, -27, 57, 62, -37, -46, 8, 13], [13, -38, -353, -30, 714, 122, -484, -89, 110, 21], [21, -50, -605, -353, 1167, 819, -760, -568, 163, 131], [131, -372, -3587, -605, 7114, 1822, -4683, -1284, 1004, 294], [294, -751, -8310, -3587, 16153, 8584, -10526, -5859, 2244, 1298], [1298, -3600, -35797, -8310, 70399, 22643, -45932, -15718, 9717, 3542], [3542, -9328, -99234, -35797, 193584, 88109, -126121, -60100, 26786, 13259], [13259, -36235, -367321, -99234, 719966, 259879, -468769, -179157, 99008, 40045]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp179 : Fact (Nat.Prime 179) := fact_iff.2 (by norm_num)
instance hp11089459 : Fact (Nat.Prime 11089459) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 1, 2]
  b' := [0, 2, 1, 3, 1]
  k := [1]
  f := [2, 3, 0, 6, 18, 7, -4, 2, 4, 1]
  g := [3, 3, 3, 2, 2, 1]
  h := [3, 3, 3, 2, 2, 1]
  a := [3, 1, 3, 2, 4]
  b := [0, 3, 4, 1, 0, 3, 4, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD179 : CertificateDedekindCriterionLists l 179 where
  n := 2
  a' := [151, 131, 128, 124, 29, 19, 0, 47]
  b' := [35, 61, 1, 83, 118, 81, 38, 142, 134]
  k := [118, 177, 168, 162, 71, 67, 54, 159, 1]
  f := [26, 55, 90, 54, 18, 45, 24, 24, 44, 1]
  g := [47, 99, 162, 96, 31, 81, 43, 43, 79, 1]
  h := [99, 1]
  a := [140, 62, 51, 168, 2, 90, 101, 117, 134]
  b := [113, 78, 79, 90, 19, 84, 116, 98, 45]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11089459 : CertificateDedekindCriterionLists l 11089459 where
  n := 2
  a' := [7150297, 10721184, 5471146, 5249729, 9509418, 834396, 4841015, 2376997]
  b' := [5169459, 8180180, 717322, 1843183, 9037123, 619613, 3466880, 1646141, 8361024]
  k := [9432237, 2297156, 581525, 7665223, 2671480, 10523723, 7523249, 4483153, 1]
  f := [8357545, 2793250, 1491451, 7420342, 7643684, 6696640, 6791111, 7303268, 1788474, 1]
  g := [10474897, 3500908, 1869304, 9300257, 9580181, 8393207, 8511612, 9153522, 2241576, 1]
  h := [8847882, 1]
  a := [10285765, 10584591, 5423844, 2948168, 313371, 30548, 2571398, 2538039, 9458015]
  b := [10501008, 1554968, 7299078, 2314755, 8423951, 4569478, 10896246, 10259613, 1631444]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 179, 11089459]
  exp := ![1, 1, 1]
  pdgood := [5, 179, 11089459]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp179.out
    exact hp11089459.out
  a := [475621034555, 9144342050934, 7880555117079, -30222057511926, -29953706201942, 15321402817392, 17665987906607, -511528379086, -1903907084560]
  b := [161848700120, -340783619737, -4663974500970, -4001610519547, 5827465800280, 5802957987096, -1863822776686, -2245786938507, 32113767063, 190390708456]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 179 T_ofList CD179
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11089459 T_ofList CD11089459

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

end VoightMaximalOrderD10R566

end TraceEuclidean
