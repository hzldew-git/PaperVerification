import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk196
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

namespace VoightMaximalOrderD10R350

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4584873528125, [1, -6, 1, 34, -16, -42, 22, 17, -9, -2, 1], 1⟩
local notation "l" => [1, -6, 1, 34, -16, -42, 22, 17, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -1, -34, 16, 42, -22, -17, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], ![-2, 11, 4, -69, -2, 100, -2, -56, 1, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], ![-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], ![-13, 76, -2, -438, 139, 544, -186, -223, 61, 27]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], ![-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], ![-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], ![-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], ![-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], ![-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], ![-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], ![-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], ![-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], ![-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], ![-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], ![-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250], ![-250, 1385, 413, -8466, 139, 11420, -676, -5507, 245, 890]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], ![-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], ![-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], ![-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], ![-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250], ![-250, 1385, 413, -8466, 139, 11420, -676, -5507, 245, 890], ![-890, 5090, 495, -29847, 5774, 37519, -8160, -15806, 2503, 2025]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], ![-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], ![-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], ![-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], ![-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250], ![-250, 1385, 413, -8466, 139, 11420, -676, -5507, 245, 890], ![-890, 5090, 495, -29847, 5774, 37519, -8160, -15806, 2503, 2025], ![-2025, 11260, 3065, -68355, 2553, 90824, -7031, -42585, 2419, 6553]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], ![-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], ![-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], ![-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], ![-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250], ![-250, 1385, 413, -8466, 139, 11420, -676, -5507, 245, 890], ![-890, 5090, 495, -29847, 5774, 37519, -8160, -15806, 2503, 2025], ![-2025, 11260, 3065, -68355, 2553, 90824, -7031, -42585, 2419, 6553], ![-6553, 37293, 4707, -219737, 36493, 277779, -53342, -118432, 16392, 15525]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-115, -27, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-115, -27, -13, -2, -1], [-250, -115, -27, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-115, -27, -13, -2, -1], [-250, -115, -27, -13, -2, -1], [-890, -250, -115, -27, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-115, -27, -13, -2, -1], [-250, -115, -27, -13, -2, -1], [-890, -250, -115, -27, -13, -2, -1], [-2025, -890, -250, -115, -27, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-115, -27, -13, -2, -1], [-250, -115, -27, -13, -2, -1], [-890, -250, -115, -27, -13, -2, -1], [-2025, -890, -250, -115, -27, -13, -2, -1], [-6553, -2025, -890, -250, -115, -27, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -1, -34, 16, 42, -22, -17, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], [-2, 11, 4, -69, -2, 100, -2, -56, 1, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], [-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], [-13, 76, -2, -438, 139, 544, -186, -223, 61, 27]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], [-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], [-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], [-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], [-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], [-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], [-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], [-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], [-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], [-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], [-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], [-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250], [-250, 1385, 413, -8466, 139, 11420, -676, -5507, 245, 890]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], [-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], [-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], [-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], [-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250], [-250, 1385, 413, -8466, 139, 11420, -676, -5507, 245, 890], [-890, 5090, 495, -29847, 5774, 37519, -8160, -15806, 2503, 2025]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], [-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], [-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], [-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], [-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250], [-250, 1385, 413, -8466, 139, 11420, -676, -5507, 245, 890], [-890, 5090, 495, -29847, 5774, 37519, -8160, -15806, 2503, 2025], [-2025, 11260, 3065, -68355, 2553, 90824, -7031, -42585, 2419, 6553]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -1, -34, 16, 42, -22, -17, 9, 2], [-2, 11, 4, -69, -2, 100, -2, -56, 1, 13], [-13, 76, -2, -438, 139, 544, -186, -223, 61, 27], [-27, 149, 49, -920, -6, 1273, -50, -645, 20, 115], [-115, 663, 34, -3861, 920, 4824, -1257, -2005, 390, 250], [-250, 1385, 413, -8466, 139, 11420, -676, -5507, 245, 890], [-890, 5090, 495, -29847, 5774, 37519, -8160, -15806, 2503, 2025], [-2025, 11260, 3065, -68355, 2553, 90824, -7031, -42585, 2419, 6553], [-6553, 37293, 4707, -219737, 36493, 277779, -53342, -118432, 16392, 15525]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp133378139 : Fact (Nat.Prime 133378139) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 1, 2]
  b' := [0, 1, 4, 1, 3]
  k := [1]
  f := [0, 2, 1, -6, 5, 12, -2, -3, 5, 2]
  g := [1, 2, 1, 0, 4, 1]
  h := [1, 2, 1, 0, 4, 1]
  a := [4, 0, 4, 0, 1]
  b := [1, 0, 0, 1, 0, 2, 3, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [9, 5, 2, 1, 0, 10, 5, 6]
  b' := [3, 7, 0, 4, 0, 5, 10, 8, 3]
  k := [3, 7, 1, 5, 9, 0, 6, 2, 1]
  f := [4, 1, 4, -1, 9, 12, 7, 1, 1, 1]
  g := [5, 0, 5, 2, 9, 9, 10, 2, 0, 1]
  h := [9, 1]
  a := [7, 1, 3, 2, 0, 5, 4, 0, 6]
  b := [10, 0, 6, 1, 7, 10, 2, 5, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD133378139 : CertificateDedekindCriterionLists l 133378139 where
  n := 2
  a' := [47157849, 1541663, 72380443, 130502138, 119458120, 113291296, 87215198, 36990788]
  b' := [72769802, 89004178, 73989622, 60954787, 3986252, 97594277, 36380156, 5307347, 99628465]
  k := [72045184, 91161615, 8685445, 65395816, 72299754, 102288482, 89276993, 118291090, 1]
  f := [57181852, 62207165, 40756472, 54415298, 6173226, 17538813, 52387016, 44105722, 32917892, 1]
  g := [102742053, 111771332, 73229589, 97771219, 11091803, 31513034, 94126884, 79247387, 59145544, 1]
  h := [74232593, 1]
  a := [110684827, 53221626, 20048968, 116968534, 53531510, 58969202, 10278523, 73902908, 14801536]
  b := [123807402, 24072541, 30570124, 67141872, 113019879, 125082460, 67682467, 117022276, 118576603]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 133378139]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 133378139]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp133378139.out
  a := [-413237016649, -1279920973574, 2488161517355, 3016830992192, -3917311975641, -1862134054120, 1912406656582, 306655585650, -248931149300]
  b := [-70095469049, 176551698037, 492969315871, -626965966821, -664329855908, 655511268815, 285023514840, -238876682194, -35644181551, 24893114930]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 133378139 T_ofList CD133378139

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

end VoightMaximalOrderD10R350

namespace VoightMaximalOrderD10R351

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4593477753125, [1, -3, -8, 31, -5, -51, 31, 14, -11, -1, 1], 1⟩
local notation "l" => [1, -3, -8, 31, -5, -51, 31, 14, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -31, 5, 51, -31, -14, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], ![-1, 2, 11, -23, -26, 56, 20, -45, -3, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], ![-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], ![-12, 35, 98, -361, 37, 586, -316, -148, 87, 9]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], ![-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], ![-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], ![-9, 15, 107, -181, -316, 496, 307, -442, -49, 96]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], ![-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], ![-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], ![-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], ![-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], ![-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], ![-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], ![-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], ![-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47], ![-47, 45, 655, -674, -2634, 2696, 3123, -3138, -520, 661]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], ![-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], ![-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], ![-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], ![-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47], ![-47, 45, 655, -674, -2634, 2696, 3123, -3138, -520, 661], ![-661, 1936, 5333, -19836, 2631, 31077, -17795, -6131, 4133, 141]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], ![-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], ![-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], ![-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], ![-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47], ![-47, 45, 655, -674, -2634, 2696, 3123, -3138, -520, 661], ![-661, 1936, 5333, -19836, 2631, 31077, -17795, -6131, 4133, 141], ![-141, -238, 3064, 962, -19131, 9822, 26706, -19769, -4580, 4274]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], ![-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], ![-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], ![-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], ![-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47], ![-47, 45, 655, -674, -2634, 2696, 3123, -3138, -520, 661], ![-661, 1936, 5333, -19836, 2631, 31077, -17795, -6131, 4133, 141], ![-141, -238, 3064, 962, -19131, 9822, 26706, -19769, -4580, 4274], ![-4274, 12681, 33954, -129430, 22332, 198843, -122672, -33130, 27245, -306]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-96, -9, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-96, -9, -12, -1, -1], [-47, -96, -9, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-96, -9, -12, -1, -1], [-47, -96, -9, -12, -1, -1], [-661, -47, -96, -9, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-96, -9, -12, -1, -1], [-47, -96, -9, -12, -1, -1], [-661, -47, -96, -9, -12, -1, -1], [-141, -661, -47, -96, -9, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-96, -9, -12, -1, -1], [-47, -96, -9, -12, -1, -1], [-661, -47, -96, -9, -12, -1, -1], [-141, -661, -47, -96, -9, -12, -1, -1], [-4274, -141, -661, -47, -96, -9, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -31, 5, 51, -31, -14, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], [-1, 2, 11, -23, -26, 56, 20, -45, -3, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], [-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], [-12, 35, 98, -361, 37, 586, -316, -148, 87, 9]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], [-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], [-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], [-9, 15, 107, -181, -316, 496, 307, -442, -49, 96]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], [-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], [-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], [-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], [-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], [-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], [-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], [-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], [-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47], [-47, 45, 655, -674, -2634, 2696, 3123, -3138, -520, 661]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], [-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], [-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], [-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], [-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47], [-47, 45, 655, -674, -2634, 2696, 3123, -3138, -520, 661], [-661, 1936, 5333, -19836, 2631, 31077, -17795, -6131, 4133, 141]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], [-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], [-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], [-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], [-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47], [-47, 45, 655, -674, -2634, 2696, 3123, -3138, -520, 661], [-661, 1936, 5333, -19836, 2631, 31077, -17795, -6131, 4133, 141], [-141, -238, 3064, 962, -19131, 9822, 26706, -19769, -4580, 4274]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 8, -31, 5, 51, -31, -14, 11, 1], [-1, 2, 11, -23, -26, 56, 20, -45, -3, 12], [-12, 35, 98, -361, 37, 586, -316, -148, 87, 9], [-9, 15, 107, -181, -316, 496, 307, -442, -49, 96], [-96, 279, 783, -2869, 299, 4580, -2480, -1037, 614, 47], [-47, 45, 655, -674, -2634, 2696, 3123, -3138, -520, 661], [-661, 1936, 5333, -19836, 2631, 31077, -17795, -6131, 4133, 141], [-141, -238, 3064, 962, -19131, 9822, 26706, -19769, -4580, 4274], [-4274, 12681, 33954, -129430, 22332, 198843, -122672, -33130, 27245, -306]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2399 : Fact (Nat.Prime 2399) := fact_iff.2 (by norm_num)
instance hp612719 : Fact (Nat.Prime 612719) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 4, 4]
  b' := [2, 2, 4, 1, 2]
  k := [1]
  f := [3, 7, 8, -3, 5, 15, -3, -2, 3, 1]
  g := [4, 4, 2, 0, 2, 1]
  h := [4, 4, 2, 0, 2, 1]
  a := [1, 2, 0, 2]
  b := [2, 1, 0, 1, 1, 1, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2399 : CertificateDedekindCriterionLists l 2399 where
  n := 2
  a' := [507, 284, 1369, 459, 1226, 2375, 1876, 372]
  b' := [1055, 1006, 2096, 51, 793, 54, 1935, 175, 1558]
  k := [960, 2099, 126, 531, 565, 416, 1864, 1730, 1]
  f := [219, 212, 140, 328, 296, 52, 230, 213, 288, 1]
  g := [1573, 1518, 1001, 2353, 2119, 367, 1651, 1525, 2064, 1]
  h := [334, 1]
  a := [442, 906, 1485, 1889, 1469, 1028, 2391, 1897, 2376]
  b := [1125, 57, 1722, 438, 1947, 1471, 1711, 437, 23]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD612719 : CertificateDedekindCriterionLists l 612719 where
  n := 2
  a' := [6064, 379232, 284655, 141125, 571194, 535536, 26513, 178665]
  b' := [130120, 575067, 69594, 225938, 319365, 62621, 349345, 602032, 184388]
  k := [144113, 220967, 64127, 323945, 199028, 494185, 89004, 70740, 1]
  f := [73795, 256856, 269350, 52704, 58673, 257614, 233709, 143399, 151138, 1]
  g := [166854, 580763, 609011, 119164, 132662, 582477, 528425, 324230, 341729, 1]
  h := [270989, 1]
  a := [608086, 586348, 385766, 161517, 88203, 190833, 320939, 259051, 611054]
  b := [412269, 390937, 591591, 305525, 526084, 494916, 358996, 408095, 1665]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 2399, 612719]
  exp := ![1, 1, 1]
  pdgood := [5, 2399, 612719]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2399.out
    exact hp612719.out
  a := [-1176422474344, -9091480569560, 15219294734087, 27605794308634, -35714342888991, -9958084789142, 15218387036193, 786039210314, -1691659409960]
  b := [-394590679583, 250412575600, 3733860608900, -3450309553917, -6057835900064, 5903991911035, 1540975248152, -1901368316397, -95520515131, 169165940996]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2399 T_ofList CD2399
    exact satisfiesDedekindCriterion_of_certificate_lists T l 612719 T_ofList CD612719

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

end VoightMaximalOrderD10R351

namespace VoightMaximalOrderD10R352

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4595608917524, [1, -4, -7, 32, 9, -50, 5, 25, -7, -3, 1], 1⟩
local notation "l" => [1, -4, -7, 32, 9, -50, 5, 25, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, -9, 50, -5, -25, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], ![-3, 11, 25, -89, -59, 141, 35, -80, -4, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], ![-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], ![-16, 61, 123, -487, -233, 741, 61, -365, 32, 44]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], ![-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], ![-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], ![-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], ![-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], ![-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], ![-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], ![-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], ![-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], ![-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], ![-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], ![-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435], ![-435, 1576, 3657, -12612, -8794, 18989, 5142, -9728, -534, 1414]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], ![-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], ![-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], ![-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], ![-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435], ![-435, 1576, 3657, -12612, -8794, 18989, 5142, -9728, -534, 1414], ![-1414, 5221, 11474, -41591, -25338, 61906, 11919, -30208, 170, 3708]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], ![-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], ![-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], ![-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], ![-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435], ![-435, 1576, 3657, -12612, -8794, 18989, 5142, -9728, -534, 1414], ![-1414, 5221, 11474, -41591, -25338, 61906, 11919, -30208, 170, 3708], ![-3708, 13418, 31177, -107182, -74963, 160062, 43366, -80781, -4252, 11294]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], ![-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], ![-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], ![-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], ![-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435], ![-435, 1576, 3657, -12612, -8794, 18989, 5142, -9728, -534, 1414], ![-1414, 5221, 11474, -41591, -25338, 61906, 11919, -30208, 170, 3708], ![-3708, 13418, 31177, -107182, -74963, 160062, 43366, -80781, -4252, 11294], ![-11294, 41468, 92476, -330231, -208828, 489737, 103592, -238984, -1723, 29630]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-164, -44, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-164, -44, -16, -3, -1], [-435, -164, -44, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-164, -44, -16, -3, -1], [-435, -164, -44, -16, -3, -1], [-1414, -435, -164, -44, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-164, -44, -16, -3, -1], [-435, -164, -44, -16, -3, -1], [-1414, -435, -164, -44, -16, -3, -1], [-3708, -1414, -435, -164, -44, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-44, -16, -3, -1], [-164, -44, -16, -3, -1], [-435, -164, -44, -16, -3, -1], [-1414, -435, -164, -44, -16, -3, -1], [-3708, -1414, -435, -164, -44, -16, -3, -1], [-11294, -3708, -1414, -435, -164, -44, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, -9, 50, -5, -25, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], [-3, 11, 25, -89, -59, 141, 35, -80, -4, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], [-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], [-16, 61, 123, -487, -233, 741, 61, -365, 32, 44]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], [-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], [-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], [-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], [-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], [-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], [-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], [-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], [-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], [-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], [-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], [-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435], [-435, 1576, 3657, -12612, -8794, 18989, 5142, -9728, -534, 1414]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], [-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], [-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], [-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], [-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435], [-435, 1576, 3657, -12612, -8794, 18989, 5142, -9728, -534, 1414], [-1414, 5221, 11474, -41591, -25338, 61906, 11919, -30208, 170, 3708]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], [-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], [-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], [-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], [-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435], [-435, 1576, 3657, -12612, -8794, 18989, 5142, -9728, -534, 1414], [-1414, 5221, 11474, -41591, -25338, 61906, 11919, -30208, 170, 3708], [-3708, 13418, 31177, -107182, -74963, 160062, 43366, -80781, -4252, 11294]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 7, -32, -9, 50, -5, -25, 7, 3], [-3, 11, 25, -89, -59, 141, 35, -80, -4, 16], [-16, 61, 123, -487, -233, 741, 61, -365, 32, 44], [-44, 160, 369, -1285, -883, 1967, 521, -1039, -57, 164], [-164, 612, 1308, -4879, -2761, 7317, 1147, -3579, 109, 435], [-435, 1576, 3657, -12612, -8794, 18989, 5142, -9728, -534, 1414], [-1414, 5221, 11474, -41591, -25338, 61906, 11919, -30208, 170, 3708], [-3708, 13418, 31177, -107182, -74963, 160062, 43366, -80781, -4252, 11294], [-11294, 41468, 92476, -330231, -208828, 489737, 103592, -238984, -1723, 29630]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp1148902229381 : Fact (Nat.Prime 1148902229381) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 3
  a' := [1, 0, 0, 0, 1]
  b' := [0, 1, 0, 0, 0, 1, 1]
  k := [1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]
  f := [0, 2, 4, -16, -4, 25, -2, -12, 4, 2]
  g := [1, 0, 0, 0, 1, 0, 0, 1, 1]
  h := [1, 0, 1]
  a := [0, 0, 1, 0, 0, 0, 1, 1]
  b := [1, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1148902229381 : CertificateDedekindCriterionLists l 1148902229381 where
  n := 2
  a' := [438660207926, 531972296665, 265164347776, 833847588229, 713802449939, 1022470089761, 1081433338602, 10095021858]
  b' := [948553811653, 968539063698, 71309654447, 772563765858, 116474132224, 664738194098, 435043849025, 306713534665, 764813150492]
  k := [1004799770368, 246796296658, 125038855346, 1096876304447, 252209982716, 866282175009, 261722370917, 54511760330, 1]
  f := [245051207083, 182818268314, 277385584186, 100907402975, 133729937687, 232451075520, 280675349421, 302167025633, 286578954888, 1]
  g := [514514492026, 383848949671, 582404406987, 211867232980, 280782093574, 488058999854, 589311664898, 634436024825, 601706994854, 1]
  h := [547195234524, 1]
  a := [253671432288, 70710163935, 494463663698, 156872662873, 832137688892, 640874939243, 525792614162, 915706380134, 39361388975]
  b := [944442414492, 154244302598, 801241766897, 455303044013, 113843602004, 747540623885, 41637164662, 519200101513, 1109540840406]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 1148902229381]
  exp := ![1, 1]
  pdgood := [2, 1148902229381]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp1148902229381.out
  a := [-110569647775770, -739816321559318, 386533399135498, 2025402465444978, -875603840328862, -1435481037305272, 660841454156485, 224390373641046, -101467991124280]
  b := [-28216863058633, 24374588091156, 267430783224552, -75030796877492, -424177333538905, 137800695956806, 211472040460366, -81776860244883, -25483077097833, 10146799112428]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1148902229381 T_ofList CD1148902229381

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

end VoightMaximalOrderD10R352

namespace VoightMaximalOrderD10R355

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4634584028125, [1, 0, -17, 28, 19, -55, 8, 24, -7, -3, 1], 1⟩
local notation "l" => [1, 0, -17, 28, 19, -55, 8, 24, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -28, -19, 55, -8, -24, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], ![-3, -1, 51, -67, -85, 146, 31, -80, -3, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], ![-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], ![-16, -3, 271, -397, -371, 795, 18, -353, 32, 45]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], ![-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], ![-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], ![-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], ![-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], ![-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], ![-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], ![-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], ![-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], ![-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], ![-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], ![-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463], ![-463, -167, 7826, -10141, -12711, 21303, 4229, -10344, -332, 1496]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], ![-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], ![-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], ![-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], ![-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463], ![-463, -167, 7826, -10141, -12711, 21303, 4229, -10344, -332, 1496], ![-1496, -463, 25265, -34062, -38565, 69569, 9335, -31675, 128, 4156]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], ![-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], ![-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], ![-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], ![-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463], ![-463, -167, 7826, -10141, -12711, 21303, 4229, -10344, -332, 1496], ![-1496, -463, 25265, -34062, -38565, 69569, 9335, -31675, 128, 4156], ![-4156, -1496, 70189, -91103, -113026, 190015, 36321, -90409, -2583, 12596]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], ![-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], ![-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], ![-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], ![-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463], ![-463, -167, 7826, -10141, -12711, 21303, 4229, -10344, -332, 1496], ![-1496, -463, 25265, -34062, -38565, 69569, 9335, -31675, 128, 4156], ![-4156, -1496, 70189, -91103, -113026, 190015, 36321, -90409, -2583, 12596], ![-12596, -4156, 212636, -282499, -330427, 579754, 89247, -265983, -2237, 35205]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-167, -45, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-167, -45, -16, -3, -1], [-463, -167, -45, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-167, -45, -16, -3, -1], [-463, -167, -45, -16, -3, -1], [-1496, -463, -167, -45, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-167, -45, -16, -3, -1], [-463, -167, -45, -16, -3, -1], [-1496, -463, -167, -45, -16, -3, -1], [-4156, -1496, -463, -167, -45, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-167, -45, -16, -3, -1], [-463, -167, -45, -16, -3, -1], [-1496, -463, -167, -45, -16, -3, -1], [-4156, -1496, -463, -167, -45, -16, -3, -1], [-12596, -4156, -1496, -463, -167, -45, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -28, -19, 55, -8, -24, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], [-3, -1, 51, -67, -85, 146, 31, -80, -3, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], [-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], [-16, -3, 271, -397, -371, 795, 18, -353, 32, 45]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], [-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], [-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], [-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], [-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], [-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], [-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], [-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], [-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], [-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], [-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], [-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463], [-463, -167, 7826, -10141, -12711, 21303, 4229, -10344, -332, 1496]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], [-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], [-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], [-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], [-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463], [-463, -167, 7826, -10141, -12711, 21303, 4229, -10344, -332, 1496], [-1496, -463, 25265, -34062, -38565, 69569, 9335, -31675, 128, 4156]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], [-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], [-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], [-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], [-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463], [-463, -167, 7826, -10141, -12711, 21303, 4229, -10344, -332, 1496], [-1496, -463, 25265, -34062, -38565, 69569, 9335, -31675, 128, 4156], [-4156, -1496, 70189, -91103, -113026, 190015, 36321, -90409, -2583, 12596]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -28, -19, 55, -8, -24, 7, 3], [-3, -1, 51, -67, -85, 146, 31, -80, -3, 16], [-16, -3, 271, -397, -371, 795, 18, -353, 32, 45], [-45, -16, 762, -989, -1252, 2104, 435, -1062, -38, 167], [-167, -45, 2823, -3914, -4162, 7933, 768, -3573, 107, 463], [-463, -167, 7826, -10141, -12711, 21303, 4229, -10344, -332, 1496], [-1496, -463, 25265, -34062, -38565, 69569, 9335, -31675, 128, 4156], [-4156, -1496, 70189, -91103, -113026, 190015, 36321, -90409, -2583, 12596], [-12596, -4156, 212636, -282499, -330427, 579754, 89247, -265983, -2237, 35205]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1483066889 : Fact (Nat.Prime 1483066889) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 3, 1]
  b' := [4, 0, 1, 2, 1]
  k := [1]
  f := [3, 0, 5, -4, -2, 13, -1, -4, 2, 1]
  g := [4, 0, 1, 1, 1, 1]
  h := [4, 0, 1, 1, 1, 1]
  a := [1, 2, 4, 4, 4]
  b := [2, 1, 4, 1, 4, 1, 1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1483066889 : CertificateDedekindCriterionLists l 1483066889 where
  n := 2
  a' := [302765501, 1279192787, 1212433599, 1395337553, 386154782, 431620920, 1385417066, 623095019]
  b' := [1037705568, 938905575, 5592261, 509690383, 202583788, 1365653110, 412235485, 1472560840, 95552430]
  k := [149629943, 1248376564, 596542105, 790646408, 145835964, 1092436536, 811261699, 1236363658, 1]
  f := [105085963, 110906394, 11897021, 24240857, 63150508, 31221532, 118820194, 114985754, 113092050, 1]
  g := [1263457422, 1333436946, 143038879, 291449873, 759263897, 375379114, 1428585240, 1382483435, 1359715272, 1]
  h := [123351614, 1]
  a := [894226755, 872779043, 523068584, 62613718, 796549343, 1333462201, 605459930, 172488906, 1178028583]
  b := [105295084, 906352151, 763353021, 927026954, 302635033, 83229614, 1291420239, 3791206, 305038306]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1483066889]
  exp := ![1, 1]
  pdgood := [5, 1483066889]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1483066889.out
  a := [7415334445, -47477503288496, 25085525119515, 154568158593948, -84212069133242, -95981564382176, 48498085638343, 15731082176920, -7207960444300]
  b := [-1396397155544, -2715820489169, 18459948204450, -3283902562261, -32846886577798, 13111875095456, 14207472336607, -5970835356717, -1789347031021, 720796044430]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1483066889 T_ofList CD1483066889

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

end VoightMaximalOrderD10R355

end TraceEuclidean
