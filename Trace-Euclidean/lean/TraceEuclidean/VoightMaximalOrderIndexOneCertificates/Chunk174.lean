import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk170
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

namespace VoightMaximalOrderD10R74

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1807334539264, [-1, -6, 1, 28, 3, -44, -1, 26, -4, -4, 1], 1⟩
local notation "l" => [-1, -6, 1, 28, 3, -44, -1, 26, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -28, -3, 44, 1, -26, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -28, -3, 44, 1, -26, 4, 4], ![4, 25, 2, -113, -40, 173, 48, -103, -10, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -28, -3, 44, 1, -26, 4, 4], ![4, 25, 2, -113, -40, 173, 48, -103, -10, 20], ![20, 124, 5, -558, -173, 840, 193, -472, -23, 70]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -28, -3, 44, 1, -26, 4, 4], ![4, 25, 2, -113, -40, 173, 48, -103, -10, 20], ![20, 124, 5, -558, -173, 840, 193, -472, -23, 70], ![70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -28, -3, 44, 1, -26, 4, 4], ![4, 25, 2, -113, -40, 173, 48, -103, -10, 20], ![20, 124, 5, -558, -173, 840, 193, -472, -23, 70], ![70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], ![257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -28, -3, 44, 1, -26, 4, 4], ![4, 25, 2, -113, -40, 173, 48, -103, -10, 20], ![20, 124, 5, -558, -173, 840, 193, -472, -23, 70], ![70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], ![257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836], ![836, 5273, 776, -23225, -9650, 34058, 11376, -18572, -2428, 2745]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -28, -3, 44, 1, -26, 4, 4], ![4, 25, 2, -113, -40, 173, 48, -103, -10, 20], ![20, 124, 5, -558, -173, 840, 193, -472, -23, 70], ![70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], ![257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836], ![836, 5273, 776, -23225, -9650, 34058, 11376, -18572, -2428, 2745], ![2745, 17306, 2528, -76084, -31460, 111130, 36803, -59994, -7592, 8552]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -28, -3, 44, 1, -26, 4, 4], ![4, 25, 2, -113, -40, 173, 48, -103, -10, 20], ![20, 124, 5, -558, -173, 840, 193, -472, -23, 70], ![70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], ![257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836], ![836, 5273, 776, -23225, -9650, 34058, 11376, -18572, -2428, 2745], ![2745, 17306, 2528, -76084, -31460, 111130, 36803, -59994, -7592, 8552], ![8552, 54057, 8754, -236928, -101740, 344828, 119682, -185549, -25786, 26616]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -28, -3, 44, 1, -26, 4, 4], ![4, 25, 2, -113, -40, 173, 48, -103, -10, 20], ![20, 124, 5, -558, -173, 840, 193, -472, -23, 70], ![70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], ![257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836], ![836, 5273, 776, -23225, -9650, 34058, 11376, -18572, -2428, 2745], ![2745, 17306, 2528, -76084, -31460, 111130, 36803, -59994, -7592, 8552], ![8552, 54057, 8754, -236928, -101740, 344828, 119682, -185549, -25786, 26616], ![26616, 168248, 27441, -736494, -316776, 1069364, 371444, -572334, -79085, 80678]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-257, -70, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-257, -70, -20, -4, -1], [-836, -257, -70, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-257, -70, -20, -4, -1], [-836, -257, -70, -20, -4, -1], [-2745, -836, -257, -70, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-257, -70, -20, -4, -1], [-836, -257, -70, -20, -4, -1], [-2745, -836, -257, -70, -20, -4, -1], [-8552, -2745, -836, -257, -70, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-257, -70, -20, -4, -1], [-836, -257, -70, -20, -4, -1], [-2745, -836, -257, -70, -20, -4, -1], [-8552, -2745, -836, -257, -70, -20, -4, -1], [-26616, -8552, -2745, -836, -257, -70, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -28, -3, 44, 1, -26, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -28, -3, 44, 1, -26, 4, 4], [4, 25, 2, -113, -40, 173, 48, -103, -10, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -28, -3, 44, 1, -26, 4, 4], [4, 25, 2, -113, -40, 173, 48, -103, -10, 20], [20, 124, 5, -558, -173, 840, 193, -472, -23, 70]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -28, -3, 44, 1, -26, 4, 4], [4, 25, 2, -113, -40, 173, 48, -103, -10, 20], [20, 124, 5, -558, -173, 840, 193, -472, -23, 70], [70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -28, -3, 44, 1, -26, 4, 4], [4, 25, 2, -113, -40, 173, 48, -103, -10, 20], [20, 124, 5, -558, -173, 840, 193, -472, -23, 70], [70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], [257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -28, -3, 44, 1, -26, 4, 4], [4, 25, 2, -113, -40, 173, 48, -103, -10, 20], [20, 124, 5, -558, -173, 840, 193, -472, -23, 70], [70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], [257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836], [836, 5273, 776, -23225, -9650, 34058, 11376, -18572, -2428, 2745]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -28, -3, 44, 1, -26, 4, 4], [4, 25, 2, -113, -40, 173, 48, -103, -10, 20], [20, 124, 5, -558, -173, 840, 193, -472, -23, 70], [70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], [257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836], [836, 5273, 776, -23225, -9650, 34058, 11376, -18572, -2428, 2745], [2745, 17306, 2528, -76084, -31460, 111130, 36803, -59994, -7592, 8552]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -28, -3, 44, 1, -26, 4, 4], [4, 25, 2, -113, -40, 173, 48, -103, -10, 20], [20, 124, 5, -558, -173, 840, 193, -472, -23, 70], [70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], [257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836], [836, 5273, 776, -23225, -9650, 34058, 11376, -18572, -2428, 2745], [2745, 17306, 2528, -76084, -31460, 111130, 36803, -59994, -7592, 8552], [8552, 54057, 8754, -236928, -101740, 344828, 119682, -185549, -25786, 26616]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -28, -3, 44, 1, -26, 4, 4], [4, 25, 2, -113, -40, 173, 48, -103, -10, 20], [20, 124, 5, -558, -173, 840, 193, -472, -23, 70], [70, 440, 54, -1955, -768, 2907, 910, -1627, -192, 257], [257, 1612, 183, -7142, -2726, 10540, 3164, -5772, -599, 836], [836, 5273, 776, -23225, -9650, 34058, 11376, -18572, -2428, 2745], [2745, 17306, 2528, -76084, -31460, 111130, 36803, -59994, -7592, 8552], [8552, 54057, 8754, -236928, -101740, 344828, 119682, -185549, -25786, 26616], [26616, 168248, 27441, -736494, -316776, 1069364, 371444, -572334, -79085, 80678]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp55155473 : Fact (Nat.Prime 55155473) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 0, 1]
  k := [1]
  f := [1, 4, 1, -12, 0, 24, 2, -12, 3, 2]
  g := [1, 1, 1, 1, 0, 1]
  h := [1, 1, 1, 1, 0, 1]
  a := [1, 0, 0, 0, 1]
  b := [0, 0, 1, 1, 1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD55155473 : CertificateDedekindCriterionLists l 55155473 where
  n := 2
  a' := [26239695, 6957754, 48803400, 45666006, 19078392, 46105559, 14141926, 21340458]
  b' := [26401671, 4597726, 20475098, 52439024, 1381458, 7293400, 40909726, 36779594, 52784311]
  k := [10474444, 43455337, 47108295, 2551622, 22514550, 43206287, 12054323, 46847027, 1]
  f := [736607, 3630724, 1491478, 3719352, 2201419, 204274, 3701996, 2104564, 3841332, 1]
  g := [9779910, 48205016, 19802299, 49381725, 29228165, 2712133, 49151294, 27942224, 51001248, 1]
  h := [4154221, 1]
  a := [19906945, 22356498, 50882230, 3781810, 25072656, 27389159, 17726162, 15364253, 31596101]
  b := [27262669, 39681494, 31815044, 5860435, 37341274, 27971760, 46229029, 5627971, 23559372]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 55155473]
  exp := ![2, 1]
  pdgood := [2, 55155473]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp55155473.out
  a := [2233889716, -6230332218, -21787638472, 44536506368, 34619955148, -63452799804, 3562031544, 14790077786, -3639433460]
  b := [-409085268, -1331862769, 4062772241, 5641325494, -10800389970, -5046382809, 9238810140, -579833138, -1624585117, 363943346]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 55155473 T_ofList CD55155473

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

end VoightMaximalOrderD10R74

namespace VoightMaximalOrderD10R78

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1884917982208, [1, -10, -19, 44, 28, -56, -7, 26, -3, -4, 1], 1⟩
local notation "l" => [1, -10, -19, 44, 28, -56, -7, 26, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, 19, -44, -28, 56, 7, -26, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], ![-4, 39, 86, -157, -156, 196, 84, -97, -14, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], ![-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], ![-19, 186, 400, -750, -689, 908, 329, -410, -40, 62]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], ![-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], ![-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], ![-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], ![-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], ![-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], ![-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], ![-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], ![-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], ![-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], ![-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], ![-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608], ![-608, 5872, 13570, -22199, -24812, 25896, 13418, -11569, -2242, 1773]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], ![-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], ![-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], ![-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], ![-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608], ![-608, 5872, 13570, -22199, -24812, 25896, 13418, -11569, -2242, 1773], ![-1773, 17122, 39559, -64442, -71843, 74476, 38307, -32680, -6250, 4850]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], ![-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], ![-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], ![-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], ![-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608], ![-608, 5872, 13570, -22199, -24812, 25896, 13418, -11569, -2242, 1773], ![-1773, 17122, 39559, -64442, -71843, 74476, 38307, -32680, -6250, 4850], ![-4850, 46727, 109272, -173841, -200242, 199757, 108426, -87793, -18130, 13150]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], ![-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], ![-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], ![-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], ![-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608], ![-608, 5872, 13570, -22199, -24812, 25896, 13418, -11569, -2242, 1773], ![-1773, 17122, 39559, -64442, -71843, 74476, 38307, -32680, -6250, 4850], ![-4850, 46727, 109272, -173841, -200242, 199757, 108426, -87793, -18130, 13150], ![-13150, 126650, 296577, -469328, -542041, 536158, 291807, -233474, -48343, 34470]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1], [-1773, -608, -208, -62, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1], [-1773, -608, -208, -62, -19, -4, -1], [-4850, -1773, -608, -208, -62, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1], [-1773, -608, -208, -62, -19, -4, -1], [-4850, -1773, -608, -208, -62, -19, -4, -1], [-13150, -4850, -1773, -608, -208, -62, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, 19, -44, -28, 56, 7, -26, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], [-4, 39, 86, -157, -156, 196, 84, -97, -14, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], [-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], [-19, 186, 400, -750, -689, 908, 329, -410, -40, 62]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], [-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], [-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], [-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], [-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], [-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], [-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], [-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], [-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], [-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], [-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], [-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608], [-608, 5872, 13570, -22199, -24812, 25896, 13418, -11569, -2242, 1773]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], [-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], [-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], [-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], [-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608], [-608, 5872, 13570, -22199, -24812, 25896, 13418, -11569, -2242, 1773], [-1773, 17122, 39559, -64442, -71843, 74476, 38307, -32680, -6250, 4850]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], [-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], [-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], [-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], [-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608], [-608, 5872, 13570, -22199, -24812, 25896, 13418, -11569, -2242, 1773], [-1773, 17122, 39559, -64442, -71843, 74476, 38307, -32680, -6250, 4850], [-4850, 46727, 109272, -173841, -200242, 199757, 108426, -87793, -18130, 13150]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, 19, -44, -28, 56, 7, -26, 3, 4], [-4, 39, 86, -157, -156, 196, 84, -97, -14, 19], [-19, 186, 400, -750, -689, 908, 329, -410, -40, 62], [-62, 601, 1364, -2328, -2486, 2783, 1342, -1283, -224, 208], [-208, 2018, 4553, -7788, -8152, 9162, 4239, -4066, -659, 608], [-608, 5872, 13570, -22199, -24812, 25896, 13418, -11569, -2242, 1773], [-1773, 17122, 39559, -64442, -71843, 74476, 38307, -32680, -6250, 4850], [-4850, 46727, 109272, -173841, -200242, 199757, 108426, -87793, -18130, 13150], [-13150, 126650, 296577, -469328, -542041, 536158, 291807, -233474, -48343, 34470]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp1840740217 : Fact (Nat.Prime 1840740217) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1]
  k := [1]
  f := [0, 6, 10, -21, -12, 30, 5, -12, 3, 3]
  g := [1, 1, 0, 1, 1, 1]
  h := [1, 1, 0, 1, 1, 1]
  a := [0, 0, 0, 1]
  b := [1, 1, 1, 0, 0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1840740217 : CertificateDedekindCriterionLists l 1840740217 where
  n := 2
  a' := [1726440135, 1435366133, 676586045, 426666487, 1418244162, 1757331631, 776576216, 1687622011]
  b' := [1213957720, 1389335919, 947757527, 645129818, 753331031, 252185590, 1737158136, 764480922, 17013134]
  k := [1437944194, 1152145653, 1208261380, 119756412, 764698117, 895536661, 1035038936, 1795404500, 1]
  f := [476405677, 157491312, 466306971, 911844462, 856915441, 803393311, 772196731, 820931236, 459905909, 1]
  g := [929908574, 307411368, 910196648, 1779852810, 1672635431, 1568164200, 1507270788, 1602396930, 897702248, 1]
  h := [943037965, 1]
  a := [299656583, 89481247, 629975754, 553926913, 1417337663, 1744777390, 1104971504, 803923127, 741067821]
  b := [1459604336, 1512966482, 1837675696, 1423949484, 126320036, 1397892846, 553422366, 1195389882, 1099672396]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 1840740217]
  exp := ![1, 1]
  pdgood := [2, 1840740217]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp1840740217.out
  a := [-628037616, -13568416010, 12203323628, 48951153514, -25159132926, -38946544846, 16634568262, 8507598296, -3556266160]
  b := [-430951805, 908812874, 6839967096, -3113788612, -11747600347, 3987096774, 6116351453, -2048631191, -993010476, 355626616]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1840740217 T_ofList CD1840740217

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

end VoightMaximalOrderD10R78

namespace VoightMaximalOrderD10R80

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1931381815625, [-1, -2, 20, 16, -43, -25, 31, 13, -9, -2, 1], 1⟩
local notation "l" => [-1, -2, 20, 16, -43, -25, 31, 13, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, -16, 43, 25, -31, -13, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, -16, 43, 25, -31, -13, 9, 2], ![2, 5, -38, -52, 70, 93, -37, -57, 5, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, -16, 43, 25, -31, -13, 9, 2], ![2, 5, -38, -52, 70, 93, -37, -57, 5, 13], ![13, 28, -255, -246, 507, 395, -310, -206, 60, 31]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, -16, 43, 25, -31, -13, 9, 2], ![2, 5, -38, -52, 70, 93, -37, -57, 5, 13], ![13, 28, -255, -246, 507, 395, -310, -206, 60, 31], ![31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, -16, 43, 25, -31, -13, 9, 2], ![2, 5, -38, -52, 70, 93, -37, -57, 5, 13], ![13, 28, -255, -246, 507, 395, -310, -206, 60, 31], ![31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], ![122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, -16, 43, 25, -31, -13, 9, 2], ![2, 5, -38, -52, 70, 93, -37, -57, 5, 13], ![13, 28, -255, -246, 507, 395, -310, -206, 60, 31], ![31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], ![122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317], ![317, 756, -6065, -7437, 11087, 12420, -5690, -6621, 701, 1019]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, -16, 43, 25, -31, -13, 9, 2], ![2, 5, -38, -52, 70, 93, -37, -57, 5, 13], ![13, 28, -255, -246, 507, 395, -310, -206, 60, 31], ![31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], ![122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317], ![317, 756, -6065, -7437, 11087, 12420, -5690, -6621, 701, 1019], ![1019, 2355, -19624, -22369, 36380, 36562, -19169, -18937, 2550, 2739]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, -16, 43, 25, -31, -13, 9, 2], ![2, 5, -38, -52, 70, 93, -37, -57, 5, 13], ![13, 28, -255, -246, 507, 395, -310, -206, 60, 31], ![31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], ![122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317], ![317, 756, -6065, -7437, 11087, 12420, -5690, -6621, 701, 1019], ![1019, 2355, -19624, -22369, 36380, 36562, -19169, -18937, 2550, 2739], ![2739, 6497, -52425, -63448, 95408, 104855, -48347, -54776, 5714, 8028]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, -16, 43, 25, -31, -13, 9, 2], ![2, 5, -38, -52, 70, 93, -37, -57, 5, 13], ![13, 28, -255, -246, 507, 395, -310, -206, 60, 31], ![31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], ![122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317], ![317, 756, -6065, -7437, 11087, 12420, -5690, -6621, 701, 1019], ![1019, 2355, -19624, -22369, 36380, 36562, -19169, -18937, 2550, 2739], ![2739, 6497, -52425, -63448, 95408, 104855, -48347, -54776, 5714, 8028], ![8028, 18795, -154063, -180873, 281756, 296108, -144013, -152711, 17476, 21770]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-122, -31, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-122, -31, -13, -2, -1], [-317, -122, -31, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-122, -31, -13, -2, -1], [-317, -122, -31, -13, -2, -1], [-1019, -317, -122, -31, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-122, -31, -13, -2, -1], [-317, -122, -31, -13, -2, -1], [-1019, -317, -122, -31, -13, -2, -1], [-2739, -1019, -317, -122, -31, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-122, -31, -13, -2, -1], [-317, -122, -31, -13, -2, -1], [-1019, -317, -122, -31, -13, -2, -1], [-2739, -1019, -317, -122, -31, -13, -2, -1], [-8028, -2739, -1019, -317, -122, -31, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, -16, 43, 25, -31, -13, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, -16, 43, 25, -31, -13, 9, 2], [2, 5, -38, -52, 70, 93, -37, -57, 5, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, -16, 43, 25, -31, -13, 9, 2], [2, 5, -38, -52, 70, 93, -37, -57, 5, 13], [13, 28, -255, -246, 507, 395, -310, -206, 60, 31]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, -16, 43, 25, -31, -13, 9, 2], [2, 5, -38, -52, 70, 93, -37, -57, 5, 13], [13, 28, -255, -246, 507, 395, -310, -206, 60, 31], [31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, -16, 43, 25, -31, -13, 9, 2], [2, 5, -38, -52, 70, 93, -37, -57, 5, 13], [13, 28, -255, -246, 507, 395, -310, -206, 60, 31], [31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], [122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, -16, 43, 25, -31, -13, 9, 2], [2, 5, -38, -52, 70, 93, -37, -57, 5, 13], [13, 28, -255, -246, 507, 395, -310, -206, 60, 31], [31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], [122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317], [317, 756, -6065, -7437, 11087, 12420, -5690, -6621, 701, 1019]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, -16, 43, 25, -31, -13, 9, 2], [2, 5, -38, -52, 70, 93, -37, -57, 5, 13], [13, 28, -255, -246, 507, 395, -310, -206, 60, 31], [31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], [122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317], [317, 756, -6065, -7437, 11087, 12420, -5690, -6621, 701, 1019], [1019, 2355, -19624, -22369, 36380, 36562, -19169, -18937, 2550, 2739]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, -16, 43, 25, -31, -13, 9, 2], [2, 5, -38, -52, 70, 93, -37, -57, 5, 13], [13, 28, -255, -246, 507, 395, -310, -206, 60, 31], [31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], [122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317], [317, 756, -6065, -7437, 11087, 12420, -5690, -6621, 701, 1019], [1019, 2355, -19624, -22369, 36380, 36562, -19169, -18937, 2550, 2739], [2739, 6497, -52425, -63448, 95408, 104855, -48347, -54776, 5714, 8028]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, -16, 43, 25, -31, -13, 9, 2], [2, 5, -38, -52, 70, 93, -37, -57, 5, 13], [13, 28, -255, -246, 507, 395, -310, -206, 60, 31], [31, 75, -592, -751, 1087, 1282, -566, -713, 73, 122], [122, 275, -2365, -2544, 4495, 4137, -2500, -2152, 385, 317], [317, 756, -6065, -7437, 11087, 12420, -5690, -6621, 701, 1019], [1019, 2355, -19624, -22369, 36380, 36562, -19169, -18937, 2550, 2739], [2739, 6497, -52425, -63448, 95408, 104855, -48347, -54776, 5714, 8028], [8028, 18795, -154063, -180873, 281756, 296108, -144013, -152711, 17476, 21770]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp618042181 : Fact (Nat.Prime 618042181) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 4, 1]
  b' := [4, 1, 3, 2, 4]
  k := [1]
  f := [1, 2, 0, 0, 15, 9, 1, -1, 5, 2]
  g := [2, 2, 4, 0, 4, 1]
  h := [2, 2, 4, 0, 4, 1]
  a := [2, 4, 2, 4, 1]
  b := [2, 4, 2, 1, 4, 0, 2, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD618042181 : CertificateDedekindCriterionLists l 618042181 where
  n := 2
  a' := [33136470, 344400267, 501277309, 361517925, 25227048, 338902175, 533345646, 505924390]
  b' := [274910876, 617462213, 329659527, 248806217, 131370455, 185720857, 508270605, 252951817, 424485653]
  k := [230738618, 315832133, 608195818, 13332195, 460959274, 403759875, 358978940, 7022426, 1]
  f := [286309347, 343190946, 339941550, 168372370, 364427605, 536452241, 432525703, 526339633, 3491265, 1]
  g := [287945218, 345151818, 341883856, 169334390, 366509816, 539517340, 434997002, 529346952, 3511212, 1]
  h := [614530967, 1]
  a := [499908212, 413876799, 525603637, 488016168, 368827432, 300070244, 391918927, 30002832, 550169943]
  b := [134811284, 219885890, 406524856, 573147446, 380065072, 273170270, 55385760, 252884353, 67872238]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 618042181]
  exp := ![1, 1]
  pdgood := [5, 618042181]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp618042181.out
  a := [-416205179, -53392595096, -2982442020, 229314142432, -25956431958, -224724072226, 48818856692, 58775526968, -18504843260]
  b := [-1337002863, 372445467, 26082604944, -3357185282, -53981514281, 9817850014, 33501806564, -7703421274, -6247649562, 1850484326]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 618042181 T_ofList CD618042181

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

end VoightMaximalOrderD10R80

namespace VoightMaximalOrderD10R83

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1953336210512, [-1, 0, 14, 5, -34, -10, 28, 6, -9, -1, 1], 1⟩
local notation "l" => [-1, 0, 14, 5, -34, -10, 28, 6, -9, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -14, -5, 34, 10, -28, -6, 9, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -14, -5, 34, 10, -28, -6, 9, 1], ![1, 1, -14, -19, 29, 44, -18, -34, 3, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -14, -5, 34, 10, -28, -6, 9, 1], ![1, 1, -14, -19, 29, 44, -18, -34, 3, 10], ![10, 1, -139, -64, 321, 129, -236, -78, 56, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -14, -5, 34, 10, -28, -6, 9, 1], ![1, 1, -14, -19, 29, 44, -18, -34, 3, 10], ![10, 1, -139, -64, 321, 129, -236, -78, 56, 13], ![13, 10, -181, -204, 378, 451, -235, -314, 39, 69]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -14, -5, 34, 10, -28, -6, 9, 1], ![1, 1, -14, -19, 29, 44, -18, -34, 3, 10], ![10, 1, -139, -64, 321, 129, -236, -78, 56, 13], ![13, 10, -181, -204, 378, 451, -235, -314, 39, 69], ![69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -14, -5, 34, 10, -28, -6, 9, 1], ![1, 1, -14, -19, 29, 44, -18, -34, 3, 10], ![10, 1, -139, -64, 321, 129, -236, -78, 56, 13], ![13, 10, -181, -204, 378, 451, -235, -314, 39, 69], ![69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108], ![108, 69, -1499, -1496, 3146, 3222, -1956, -2129, 323, 415]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -14, -5, 34, 10, -28, -6, 9, 1], ![1, 1, -14, -19, 29, 44, -18, -34, 3, 10], ![10, 1, -139, -64, 321, 129, -236, -78, 56, 13], ![13, 10, -181, -204, 378, 451, -235, -314, 39, 69], ![69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108], ![108, 69, -1499, -1496, 3146, 3222, -1956, -2129, 323, 415], ![415, 108, -5741, -3574, 12614, 7296, -8398, -4446, 1606, 738]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -14, -5, 34, 10, -28, -6, 9, 1], ![1, 1, -14, -19, 29, 44, -18, -34, 3, 10], ![10, 1, -139, -64, 321, 129, -236, -78, 56, 13], ![13, 10, -181, -204, 378, 451, -235, -314, 39, 69], ![69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108], ![108, 69, -1499, -1496, 3146, 3222, -1956, -2129, 323, 415], ![415, 108, -5741, -3574, 12614, 7296, -8398, -4446, 1606, 738], ![738, 415, -10224, -9431, 21518, 19994, -13368, -12826, 2196, 2344]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -14, -5, 34, 10, -28, -6, 9, 1], ![1, 1, -14, -19, 29, 44, -18, -34, 3, 10], ![10, 1, -139, -64, 321, 129, -236, -78, 56, 13], ![13, 10, -181, -204, 378, 451, -235, -314, 39, 69], ![69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108], ![108, 69, -1499, -1496, 3146, 3222, -1956, -2129, 323, 415], ![415, 108, -5741, -3574, 12614, 7296, -8398, -4446, 1606, 738], ![738, 415, -10224, -9431, 21518, 19994, -13368, -12826, 2196, 2344], ![2344, 738, -32401, -21944, 70265, 44958, -45638, -27432, 8270, 4540]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-10, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-13, -10, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-13, -10, -1, -1], [-69, -13, -10, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-13, -10, -1, -1], [-69, -13, -10, -1, -1], [-108, -69, -13, -10, -1, -1]], ![[], [], [], [-1], [-1, -1], [-10, -1, -1], [-13, -10, -1, -1], [-69, -13, -10, -1, -1], [-108, -69, -13, -10, -1, -1], [-415, -108, -69, -13, -10, -1, -1]], ![[], [], [-1], [-1, -1], [-10, -1, -1], [-13, -10, -1, -1], [-69, -13, -10, -1, -1], [-108, -69, -13, -10, -1, -1], [-415, -108, -69, -13, -10, -1, -1], [-738, -415, -108, -69, -13, -10, -1, -1]], ![[], [-1], [-1, -1], [-10, -1, -1], [-13, -10, -1, -1], [-69, -13, -10, -1, -1], [-108, -69, -13, -10, -1, -1], [-415, -108, -69, -13, -10, -1, -1], [-738, -415, -108, -69, -13, -10, -1, -1], [-2344, -738, -415, -108, -69, -13, -10, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -14, -5, 34, 10, -28, -6, 9, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -14, -5, 34, 10, -28, -6, 9, 1], [1, 1, -14, -19, 29, 44, -18, -34, 3, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -14, -5, 34, 10, -28, -6, 9, 1], [1, 1, -14, -19, 29, 44, -18, -34, 3, 10], [10, 1, -139, -64, 321, 129, -236, -78, 56, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -14, -5, 34, 10, -28, -6, 9, 1], [1, 1, -14, -19, 29, 44, -18, -34, 3, 10], [10, 1, -139, -64, 321, 129, -236, -78, 56, 13], [13, 10, -181, -204, 378, 451, -235, -314, 39, 69]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -14, -5, 34, 10, -28, -6, 9, 1], [1, 1, -14, -19, 29, 44, -18, -34, 3, 10], [10, 1, -139, -64, 321, 129, -236, -78, 56, 13], [13, 10, -181, -204, 378, 451, -235, -314, 39, 69], [69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -14, -5, 34, 10, -28, -6, 9, 1], [1, 1, -14, -19, 29, 44, -18, -34, 3, 10], [10, 1, -139, -64, 321, 129, -236, -78, 56, 13], [13, 10, -181, -204, 378, 451, -235, -314, 39, 69], [69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108], [108, 69, -1499, -1496, 3146, 3222, -1956, -2129, 323, 415]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -14, -5, 34, 10, -28, -6, 9, 1], [1, 1, -14, -19, 29, 44, -18, -34, 3, 10], [10, 1, -139, -64, 321, 129, -236, -78, 56, 13], [13, 10, -181, -204, 378, 451, -235, -314, 39, 69], [69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108], [108, 69, -1499, -1496, 3146, 3222, -1956, -2129, 323, 415], [415, 108, -5741, -3574, 12614, 7296, -8398, -4446, 1606, 738]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -14, -5, 34, 10, -28, -6, 9, 1], [1, 1, -14, -19, 29, 44, -18, -34, 3, 10], [10, 1, -139, -64, 321, 129, -236, -78, 56, 13], [13, 10, -181, -204, 378, 451, -235, -314, 39, 69], [69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108], [108, 69, -1499, -1496, 3146, 3222, -1956, -2129, 323, 415], [415, 108, -5741, -3574, 12614, 7296, -8398, -4446, 1606, 738], [738, 415, -10224, -9431, 21518, 19994, -13368, -12826, 2196, 2344]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -14, -5, 34, 10, -28, -6, 9, 1], [1, 1, -14, -19, 29, 44, -18, -34, 3, 10], [10, 1, -139, -64, 321, 129, -236, -78, 56, 13], [13, 10, -181, -204, 378, 451, -235, -314, 39, 69], [69, 13, -956, -526, 2142, 1068, -1481, -649, 307, 108], [108, 69, -1499, -1496, 3146, 3222, -1956, -2129, 323, 415], [415, 108, -5741, -3574, 12614, 7296, -8398, -4446, 1606, 738], [738, 415, -10224, -9431, 21518, 19994, -13368, -12826, 2196, 2344], [2344, 738, -32401, -21944, 70265, 44958, -45638, -27432, 8270, 4540]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp439 : Fact (Nat.Prime 439) := fact_iff.2 (by norm_num)
instance hp9547 : Fact (Nat.Prime 9547) := fact_iff.2 (by norm_num)
instance hp29129 : Fact (Nat.Prime 29129) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := []
  b' := [1]
  k := [1, 0, 1, 1, 0, 1, 1]
  f := [1, 1, -6, -2, 17, 5, -14, -3, 5, 1]
  g := [1, 1, 0, 0, 0, 0, 0, 0, 1]
  h := [1, 1, 1]
  a := [1, 1, 0, 1, 1, 0, 1, 1]
  b := [0, 0, 1, 0, 1, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD439 : CertificateDedekindCriterionLists l 439 where
  n := 2
  a' := [414, 303, 414, 102, 60, 121, 84, 244]
  b' := [9, 44, 155, 12, 89, 252, 93, 337, 168]
  k := [306, 427, 158, 275, 337, 292, 433, 336, 1]
  f := [28, 16, 17, 16, 40, 36, 50, 2, 45, 1]
  g := [241, 133, 144, 135, 341, 303, 425, 9, 387, 1]
  h := [51, 1]
  a := [101, 418, 333, 209, 32, 0, 423, 365, 277]
  b := [185, 380, 384, 302, 51, 169, 63, 423, 162]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9547 : CertificateDedekindCriterionLists l 9547 where
  n := 2
  a' := [451, 1702, 972, 6626, 6418, 5707, 7932, 2539]
  b' := [3790, 5729, 4825, 8531, 7051, 9028, 3590, 9209, 3961]
  k := [1737, 6648, 3372, 2301, 4553, 5948, 116, 2809, 1]
  f := [3025, 6661, 3668, 5885, 1558, 1056, 4492, 5057, 1198, 1]
  g := [3547, 7810, 4300, 6900, 1826, 1238, 5267, 5929, 1404, 1]
  h := [8142, 1]
  a := [5325, 338, 4919, 8125, 6784, 5845, 4289, 8924, 2883]
  b := [3493, 3922, 864, 6329, 8815, 6652, 6334, 2607, 6664]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29129 : CertificateDedekindCriterionLists l 29129 where
  n := 2
  a' := [6153, 28576, 12326, 4103, 13781, 15664, 18172, 12558]
  b' := [16609, 20546, 11326, 23750, 18917, 10761, 28410, 10526, 18024]
  k := [11796, 10084, 20481, 27691, 4963, 127, 26260, 20409, 1]
  f := [7781, 11261, 1335, 9261, 4209, 12820, 2357, 16089, 6630, 1]
  g := [11977, 17333, 2054, 14255, 6478, 19733, 3627, 24765, 10204, 1]
  h := [18924, 1]
  a := [18199, 26584, 15129, 28170, 1450, 18030, 1419, 7559, 26258]
  b := [10209, 12682, 9695, 9492, 9050, 3826, 19800, 14024, 2871]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 439, 9547, 29129]
  exp := ![1, 1, 1, 1]
  pdgood := [2, 439, 9547, 29129]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp439.out
    exact hp9547.out
    exact hp29129.out
  a := [-244167026314, -1387316511784, 3588895819962, 4296376666634, -6286643795809, -3551401122759, 3363287162309, 757181630181, -550698524190]
  b := [-49547018278, 276801409376, 501758119169, -1080536165619, -880159606731, 1135575214138, 497681933651, -432838921001, -81225148260, 55069852419]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 439 T_ofList CD439
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9547 T_ofList CD9547
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29129 T_ofList CD29129

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

end VoightMaximalOrderD10R83

end TraceEuclidean
