import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk223
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

namespace VoightMaximalOrderD10R666

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6817719345677, [-1, -4, 7, 28, -21, -40, 29, 14, -11, -1, 1], 1⟩
local notation "l" => [-1, -4, 7, 28, -21, -40, 29, 14, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -28, 21, 40, -29, -14, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -28, 21, 40, -29, -14, 11, 1], ![1, 5, -3, -35, -7, 61, 11, -43, -3, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -28, 21, 40, -29, -14, 11, 1], ![1, 5, -3, -35, -7, 61, 11, -43, -3, 12], ![12, 49, -79, -339, 217, 473, -287, -157, 89, 9]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -28, 21, 40, -29, -14, 11, 1], ![1, 5, -3, -35, -7, 61, 11, -43, -3, 12], ![12, 49, -79, -339, 217, 473, -287, -157, 89, 9], ![9, 48, -14, -331, -150, 577, 212, -413, -58, 98]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -28, 21, 40, -29, -14, 11, 1], ![1, 5, -3, -35, -7, 61, 11, -43, -3, 12], ![12, 49, -79, -339, 217, 473, -287, -157, 89, 9], ![9, 48, -14, -331, -150, 577, 212, -413, -58, 98], ![98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -28, 21, 40, -29, -14, 11, 1], ![1, 5, -3, -35, -7, 61, 11, -43, -3, 12], ![12, 49, -79, -339, 217, 473, -287, -157, 89, 9], ![9, 48, -14, -331, -150, 577, 212, -413, -58, 98], ![98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40], ![40, 258, 121, -1758, -1918, 3327, 2610, -2825, -720, 705]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -28, 21, 40, -29, -14, 11, 1], ![1, 5, -3, -35, -7, 61, 11, -43, -3, 12], ![12, 49, -79, -339, 217, 473, -287, -157, 89, 9], ![9, 48, -14, -331, -150, 577, 212, -413, -58, 98], ![98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40], ![40, 258, 121, -1758, -1918, 3327, 2610, -2825, -720, 705], ![705, 2860, -4677, -19619, 13047, 26282, -17118, -7260, 4930, -15]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -28, 21, 40, -29, -14, 11, 1], ![1, 5, -3, -35, -7, 61, 11, -43, -3, 12], ![12, 49, -79, -339, 217, 473, -287, -157, 89, 9], ![9, 48, -14, -331, -150, 577, 212, -413, -58, 98], ![98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40], ![40, 258, 121, -1758, -1918, 3327, 2610, -2825, -720, 705], ![705, 2860, -4677, -19619, 13047, 26282, -17118, -7260, 4930, -15], ![-15, 645, 2965, -4257, -19934, 12447, 26717, -16908, -7425, 4915]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -28, 21, 40, -29, -14, 11, 1], ![1, 5, -3, -35, -7, 61, 11, -43, -3, 12], ![12, 49, -79, -339, 217, 473, -287, -157, 89, 9], ![9, 48, -14, -331, -150, 577, 212, -413, -58, 98], ![98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40], ![40, 258, 121, -1758, -1918, 3327, 2610, -2825, -720, 705], ![705, 2860, -4677, -19619, 13047, 26282, -17118, -7260, 4930, -15], ![-15, 645, 2965, -4257, -19934, 12447, 26717, -16908, -7425, 4915], ![4915, 19645, -33760, -134655, 98958, 176666, -130088, -42093, 37157, -2510]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-98, -9, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-98, -9, -12, -1, -1], [-40, -98, -9, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-98, -9, -12, -1, -1], [-40, -98, -9, -12, -1, -1], [-705, -40, -98, -9, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-98, -9, -12, -1, -1], [-40, -98, -9, -12, -1, -1], [-705, -40, -98, -9, -12, -1, -1], [15, -705, -40, -98, -9, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-98, -9, -12, -1, -1], [-40, -98, -9, -12, -1, -1], [-705, -40, -98, -9, -12, -1, -1], [15, -705, -40, -98, -9, -12, -1, -1], [-4915, 15, -705, -40, -98, -9, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -28, 21, 40, -29, -14, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -28, 21, 40, -29, -14, 11, 1], [1, 5, -3, -35, -7, 61, 11, -43, -3, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -28, 21, 40, -29, -14, 11, 1], [1, 5, -3, -35, -7, 61, 11, -43, -3, 12], [12, 49, -79, -339, 217, 473, -287, -157, 89, 9]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -28, 21, 40, -29, -14, 11, 1], [1, 5, -3, -35, -7, 61, 11, -43, -3, 12], [12, 49, -79, -339, 217, 473, -287, -157, 89, 9], [9, 48, -14, -331, -150, 577, 212, -413, -58, 98]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -28, 21, 40, -29, -14, 11, 1], [1, 5, -3, -35, -7, 61, 11, -43, -3, 12], [12, 49, -79, -339, 217, 473, -287, -157, 89, 9], [9, 48, -14, -331, -150, 577, 212, -413, -58, 98], [98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -28, 21, 40, -29, -14, 11, 1], [1, 5, -3, -35, -7, 61, 11, -43, -3, 12], [12, 49, -79, -339, 217, 473, -287, -157, 89, 9], [9, 48, -14, -331, -150, 577, 212, -413, -58, 98], [98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40], [40, 258, 121, -1758, -1918, 3327, 2610, -2825, -720, 705]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -28, 21, 40, -29, -14, 11, 1], [1, 5, -3, -35, -7, 61, 11, -43, -3, 12], [12, 49, -79, -339, 217, 473, -287, -157, 89, 9], [9, 48, -14, -331, -150, 577, 212, -413, -58, 98], [98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40], [40, 258, 121, -1758, -1918, 3327, 2610, -2825, -720, 705], [705, 2860, -4677, -19619, 13047, 26282, -17118, -7260, 4930, -15]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -28, 21, 40, -29, -14, 11, 1], [1, 5, -3, -35, -7, 61, 11, -43, -3, 12], [12, 49, -79, -339, 217, 473, -287, -157, 89, 9], [9, 48, -14, -331, -150, 577, 212, -413, -58, 98], [98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40], [40, 258, 121, -1758, -1918, 3327, 2610, -2825, -720, 705], [705, 2860, -4677, -19619, 13047, 26282, -17118, -7260, 4930, -15], [-15, 645, 2965, -4257, -19934, 12447, 26717, -16908, -7425, 4915]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -28, 21, 40, -29, -14, 11, 1], [1, 5, -3, -35, -7, 61, 11, -43, -3, 12], [12, 49, -79, -339, 217, 473, -287, -157, 89, 9], [9, 48, -14, -331, -150, 577, 212, -413, -58, 98], [98, 401, -638, -2758, 1727, 3770, -2265, -1160, 665, 40], [40, 258, 121, -1758, -1918, 3327, 2610, -2825, -720, 705], [705, 2860, -4677, -19619, 13047, 26282, -17118, -7260, 4930, -15], [-15, 645, 2965, -4257, -19934, 12447, 26717, -16908, -7425, 4915], [4915, 19645, -33760, -134655, 98958, 176666, -130088, -42093, 37157, -2510]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp463 : Fact (Nat.Prime 463) := fact_iff.2 (by norm_num)
instance hp40789739 : Fact (Nat.Prime 40789739) := fact_iff.2 (by norm_num)

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [2, 10, 9, 6, 18, 5, 16]
  b' := [9, 18, 6, 9, 3, 15, 9, 17]
  k := [15, 14, 0, 7, 2, 0, 1]
  f := [9, 13, 9, 7, 9, 9, 8, 10, 6, 1]
  g := [17, 9, 8, 8, 7, 6, 12, 9, 1]
  h := [10, 9, 1]
  a := [9, 1, 16, 0, 11, 3, 8, 18]
  b := [2, 15, 14, 5, 7, 10, 8, 8, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD463 : CertificateDedekindCriterionLists l 463 where
  n := 2
  a' := [457, 370, 11, 86, 121, 111, 57, 156]
  b' := [258, 214, 8, 158, 293, 228, 327, 171, 137]
  k := [23, 183, 5, 223, 353, 400, 298, 173, 1]
  f := [255, 250, 172, 41, 57, 226, 327, 52, 70, 1]
  g := [314, 307, 211, 50, 70, 278, 402, 63, 86, 1]
  h := [376, 1]
  a := [444, 335, 458, 132, 338, 81, 114, 263, 446]
  b := [272, 440, 77, 372, 380, 203, 445, 391, 17]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD40789739 : CertificateDedekindCriterionLists l 40789739 where
  n := 2
  a' := [3482299, 124136, 384156, 38181891, 13010033, 27917941, 10240281, 28738404]
  b' := [39013016, 19984203, 17631057, 39561702, 10030351, 2845558, 10236354, 36443065, 37596583]
  k := [22550167, 34576252, 11714301, 27670944, 16775849, 7099255, 28764559, 25964760, 1]
  f := [4058126, 4722101, 4730550, 5416884, 97904, 7007195, 725315, 7133075, 6065460, 1]
  g := [22331217, 25984962, 26031455, 29808241, 538746, 38559471, 3991287, 39252168, 33377249, 1]
  h := [7412489, 1]
  a := [27120656, 17268900, 34414266, 23609068, 19518257, 13368464, 12506665, 32030526, 18220226]
  b := [24374256, 39574145, 31731582, 28161588, 33378456, 5933323, 22639680, 33423154, 22569513]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![19, 463, 40789739]
  exp := ![1, 1, 1]
  pdgood := [19, 463, 40789739]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp19.out
    exact hp463.out
    exact hp40789739.out
  a := [5862549922633, -45340301036916, 28886298445093, 131157797545252, -129404966949840, -64869232520966, 75141723061250, 5175062534442, -9024422497980]
  b := [-1555344314154, 28820237057, 15816829022716, -11357068032641, -26850365788819, 23036983175490, 9559604595592, -9529014432818, -607750478424, 902442249798]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 463 T_ofList CD463
    exact satisfiesDedekindCriterion_of_certificate_lists T l 40789739 T_ofList CD40789739

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

end VoightMaximalOrderD10R666

namespace VoightMaximalOrderD10R669

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6826923203372, [-1, -1, 12, 8, -33, -15, 31, 7, -10, -1, 1], 1⟩
local notation "l" => [-1, -1, 12, 8, -33, -15, 31, 7, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -8, 33, 15, -31, -7, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -8, 33, 15, -31, -7, 10, 1], ![1, 2, -11, -20, 25, 48, -16, -38, 3, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -8, 33, 15, -31, -7, 10, 1], ![1, 2, -11, -20, 25, 48, -16, -38, 3, 11], ![11, 12, -130, -99, 343, 190, -293, -93, 72, 14]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -8, 33, 15, -31, -7, 10, 1], ![1, 2, -11, -20, 25, 48, -16, -38, 3, 11], ![11, 12, -130, -99, 343, 190, -293, -93, 72, 14], ![14, 25, -156, -242, 363, 553, -244, -391, 47, 86]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -8, 33, 15, -31, -7, 10, 1], ![1, 2, -11, -20, 25, 48, -16, -38, 3, 11], ![11, 12, -130, -99, 343, 190, -293, -93, 72, 14], ![14, 25, -156, -242, 363, 553, -244, -391, 47, 86], ![86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -8, 33, 15, -31, -7, 10, 1], ![1, 2, -11, -20, 25, 48, -16, -38, 3, 11], ![11, 12, -130, -99, 343, 190, -293, -93, 72, 14], ![14, 25, -156, -242, 363, 553, -244, -391, 47, 86], ![86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133], ![133, 219, -1496, -2071, 3545, 4591, -2470, -3044, 484, 602]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -8, 33, 15, -31, -7, 10, 1], ![1, 2, -11, -20, 25, 48, -16, -38, 3, 11], ![11, 12, -130, -99, 343, 190, -293, -93, 72, 14], ![14, 25, -156, -242, 363, 553, -244, -391, 47, 86], ![86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133], ![133, 219, -1496, -2071, 3545, 4591, -2470, -3044, 484, 602], ![602, 735, -7005, -6312, 17795, 12575, -14071, -6684, 2976, 1086]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -8, 33, 15, -31, -7, 10, 1], ![1, 2, -11, -20, 25, 48, -16, -38, 3, 11], ![11, 12, -130, -99, 343, 190, -293, -93, 72, 14], ![14, 25, -156, -242, 363, 553, -244, -391, 47, 86], ![86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133], ![133, 219, -1496, -2071, 3545, 4591, -2470, -3044, 484, 602], ![602, 735, -7005, -6312, 17795, 12575, -14071, -6684, 2976, 1086], ![1086, 1688, -12297, -15693, 29526, 34085, -21091, -21673, 4176, 4062]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -8, 33, 15, -31, -7, 10, 1], ![1, 2, -11, -20, 25, 48, -16, -38, 3, 11], ![11, 12, -130, -99, 343, 190, -293, -93, 72, 14], ![14, 25, -156, -242, 363, 553, -244, -391, 47, 86], ![86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133], ![133, 219, -1496, -2071, 3545, 4591, -2470, -3044, 484, 602], ![602, 735, -7005, -6312, 17795, 12575, -14071, -6684, 2976, 1086], ![1086, 1688, -12297, -15693, 29526, 34085, -21091, -21673, 4176, 4062], ![4062, 5148, -47056, -44793, 118353, 90456, -91837, -49525, 18947, 8238]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-86, -14, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-86, -14, -11, -1, -1], [-133, -86, -14, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-86, -14, -11, -1, -1], [-133, -86, -14, -11, -1, -1], [-602, -133, -86, -14, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-86, -14, -11, -1, -1], [-133, -86, -14, -11, -1, -1], [-602, -133, -86, -14, -11, -1, -1], [-1086, -602, -133, -86, -14, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-86, -14, -11, -1, -1], [-133, -86, -14, -11, -1, -1], [-602, -133, -86, -14, -11, -1, -1], [-1086, -602, -133, -86, -14, -11, -1, -1], [-4062, -1086, -602, -133, -86, -14, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -8, 33, 15, -31, -7, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -8, 33, 15, -31, -7, 10, 1], [1, 2, -11, -20, 25, 48, -16, -38, 3, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -8, 33, 15, -31, -7, 10, 1], [1, 2, -11, -20, 25, 48, -16, -38, 3, 11], [11, 12, -130, -99, 343, 190, -293, -93, 72, 14]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -8, 33, 15, -31, -7, 10, 1], [1, 2, -11, -20, 25, 48, -16, -38, 3, 11], [11, 12, -130, -99, 343, 190, -293, -93, 72, 14], [14, 25, -156, -242, 363, 553, -244, -391, 47, 86]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -8, 33, 15, -31, -7, 10, 1], [1, 2, -11, -20, 25, 48, -16, -38, 3, 11], [11, 12, -130, -99, 343, 190, -293, -93, 72, 14], [14, 25, -156, -242, 363, 553, -244, -391, 47, 86], [86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -8, 33, 15, -31, -7, 10, 1], [1, 2, -11, -20, 25, 48, -16, -38, 3, 11], [11, 12, -130, -99, 343, 190, -293, -93, 72, 14], [14, 25, -156, -242, 363, 553, -244, -391, 47, 86], [86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133], [133, 219, -1496, -2071, 3545, 4591, -2470, -3044, 484, 602]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -8, 33, 15, -31, -7, 10, 1], [1, 2, -11, -20, 25, 48, -16, -38, 3, 11], [11, 12, -130, -99, 343, 190, -293, -93, 72, 14], [14, 25, -156, -242, 363, 553, -244, -391, 47, 86], [86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133], [133, 219, -1496, -2071, 3545, 4591, -2470, -3044, 484, 602], [602, 735, -7005, -6312, 17795, 12575, -14071, -6684, 2976, 1086]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -8, 33, 15, -31, -7, 10, 1], [1, 2, -11, -20, 25, 48, -16, -38, 3, 11], [11, 12, -130, -99, 343, 190, -293, -93, 72, 14], [14, 25, -156, -242, 363, 553, -244, -391, 47, 86], [86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133], [133, 219, -1496, -2071, 3545, 4591, -2470, -3044, 484, 602], [602, 735, -7005, -6312, 17795, 12575, -14071, -6684, 2976, 1086], [1086, 1688, -12297, -15693, 29526, 34085, -21091, -21673, 4176, 4062]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -8, 33, 15, -31, -7, 10, 1], [1, 2, -11, -20, 25, 48, -16, -38, 3, 11], [11, 12, -130, -99, 343, 190, -293, -93, 72, 14], [14, 25, -156, -242, 363, 553, -244, -391, 47, 86], [86, 100, -1007, -844, 2596, 1653, -2113, -846, 469, 133], [133, 219, -1496, -2071, 3545, 4591, -2470, -3044, 484, 602], [602, 735, -7005, -6312, 17795, 12575, -14071, -6684, 2976, 1086], [1086, 1688, -12297, -15693, 29526, 34085, -21091, -21673, 4176, 4062], [4062, 5148, -47056, -44793, 118353, 90456, -91837, -49525, 18947, 8238]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp81299 : Fact (Nat.Prime 81299) := fact_iff.2 (by norm_num)
instance hp20993257 : Fact (Nat.Prime 20993257) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 0, 0, 1, 0, 1]
  b' := [1, 1, 0, 0, 1, 1, 0, 1]
  k := [1, 1, 1, 1, 0, 0, 1, 1, 1]
  f := [1, 1, -6, -4, 17, 8, -15, -3, 5, 1]
  g := [1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
  h := [1, 1]
  a := [0, 1, 1, 0, 1, 0, 0, 1, 1]
  b := [1, 1, 0, 1, 0, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD81299 : CertificateDedekindCriterionLists l 81299 where
  n := 2
  a' := [42278, 39490, 78283, 57386, 31222, 25956, 45265, 850]
  b' := [59951, 53724, 28156, 38834, 8835, 36532, 30861, 58414, 17972]
  k := [48267, 28046, 53532, 46703, 36981, 54640, 12259, 51227, 1]
  f := [2024, 24649, 33105, 24916, 20561, 34457, 20105, 34070, 17544, 1]
  g := [2955, 35987, 48332, 36376, 30018, 50306, 29352, 49741, 25613, 1]
  h := [55685, 1]
  a := [76162, 38513, 23205, 37524, 14724, 3208, 5346, 15728, 47710]
  b := [66907, 17726, 10783, 57789, 39711, 42585, 44441, 5497, 33589]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD20993257 : CertificateDedekindCriterionLists l 20993257 where
  n := 2
  a' := [14409203, 4894140, 9983937, 2797551, 17394023, 8505207, 12349608, 14170246]
  b' := [10344852, 7103564, 17045661, 20814311, 4816744, 1017402, 16275222, 11798504, 14753617]
  k := [10027362, 17743038, 11759026, 17018185, 14783954, 19963430, 23931, 13995683, 1]
  f := [2393268, 9703818, 4010289, 7536694, 13975413, 10769484, 11878336, 7780525, 4665198, 1]
  g := [3589925, 14555820, 6015471, 11305113, 20963253, 16154328, 17817617, 11670861, 6997841, 1]
  h := [13995415, 1]
  a := [7122909, 3473835, 17693505, 3193828, 132201, 14710860, 10390614, 11181897, 6368665]
  b := [19597667, 20085481, 139426, 2818962, 2982978, 1252174, 7013374, 16306676, 14624592]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 81299, 20993257]
  exp := ![1, 1, 1]
  pdgood := [2, 81299, 20993257]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp81299.out
    exact hp20993257.out
  a := [359385930664, -96444493487857, 101191659603106, 423700631014367, -381563873235596, -268231672977656, 213609155333520, 45098523792217, -30494364786130]
  b := [-3772847532350, 5536766780793, 41899527015351, -42864199648789, -82294319497205, 69464716243062, 36613127729600, -27283252535731, -4814796027083, 3049436478613]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 81299 T_ofList CD81299
    exact satisfiesDedekindCriterion_of_certificate_lists T l 20993257 T_ofList CD20993257

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

end VoightMaximalOrderD10R669

namespace VoightMaximalOrderD10R671

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6828638647616, [-1, -5, 3, 32, 9, -48, -10, 26, 0, -5, 1], 1⟩
local notation "l" => [-1, -5, 3, 32, 9, -48, -10, 26, 0, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -32, -9, 48, 10, -26, 0, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -32, -9, 48, 10, -26, 0, 5], ![5, 26, -10, -163, -77, 231, 98, -120, -26, 25]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -32, -9, 48, 10, -26, 0, 5], ![5, 26, -10, -163, -77, 231, 98, -120, -26, 25], ![25, 130, -49, -810, -388, 1123, 481, -552, -120, 99]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -32, -9, 48, 10, -26, 0, 5], ![5, 26, -10, -163, -77, 231, 98, -120, -26, 25], ![25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], ![99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -32, -9, 48, 10, -26, 0, 5], ![5, 26, -10, -163, -77, 231, 98, -120, -26, 25], ![25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], ![99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], ![375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -32, -9, 48, 10, -26, 0, 5], ![5, 26, -10, -163, -77, 231, 98, -120, -26, 25], ![25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], ![99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], ![375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323], ![1323, 6990, -1995, -42941, -24074, 56912, 29529, -26284, -7637, 4522]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -32, -9, 48, 10, -26, 0, 5], ![5, 26, -10, -163, -77, 231, 98, -120, -26, 25], ![25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], ![99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], ![375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323], ![1323, 6990, -1995, -42941, -24074, 56912, 29529, -26284, -7637, 4522], ![4522, 23933, -6576, -146699, -83639, 192982, 102132, -88043, -26284, 14973]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -32, -9, 48, 10, -26, 0, 5], ![5, 26, -10, -163, -77, 231, 98, -120, -26, 25], ![25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], ![99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], ![375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323], ![1323, 6990, -1995, -42941, -24074, 56912, 29529, -26284, -7637, 4522], ![4522, 23933, -6576, -146699, -83639, 192982, 102132, -88043, -26284, 14973], ![14973, 79387, -20986, -485712, -281456, 635065, 342712, -287166, -88043, 48581]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -32, -9, 48, 10, -26, 0, 5], ![5, 26, -10, -163, -77, 231, 98, -120, -26, 25], ![25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], ![99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], ![375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323], ![1323, 6990, -1995, -42941, -24074, 56912, 29529, -26284, -7637, 4522], ![4522, 23933, -6576, -146699, -83639, 192982, 102132, -88043, -26284, 14973], ![14973, 79387, -20986, -485712, -281456, 635065, 342712, -287166, -88043, 48581], ![48581, 257878, -66356, -1575578, -922941, 2050432, 1120875, -920394, -287166, 154862]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-99, -25, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-99, -25, -5, -1], [-375, -99, -25, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-99, -25, -5, -1], [-375, -99, -25, -5, -1], [-1323, -375, -99, -25, -5, -1]], ![[], [], [], [-1], [-5, -1], [-25, -5, -1], [-99, -25, -5, -1], [-375, -99, -25, -5, -1], [-1323, -375, -99, -25, -5, -1], [-4522, -1323, -375, -99, -25, -5, -1]], ![[], [], [-1], [-5, -1], [-25, -5, -1], [-99, -25, -5, -1], [-375, -99, -25, -5, -1], [-1323, -375, -99, -25, -5, -1], [-4522, -1323, -375, -99, -25, -5, -1], [-14973, -4522, -1323, -375, -99, -25, -5, -1]], ![[], [-1], [-5, -1], [-25, -5, -1], [-99, -25, -5, -1], [-375, -99, -25, -5, -1], [-1323, -375, -99, -25, -5, -1], [-4522, -1323, -375, -99, -25, -5, -1], [-14973, -4522, -1323, -375, -99, -25, -5, -1], [-48581, -14973, -4522, -1323, -375, -99, -25, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -32, -9, 48, 10, -26, 0, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -32, -9, 48, 10, -26, 0, 5], [5, 26, -10, -163, -77, 231, 98, -120, -26, 25]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -32, -9, 48, 10, -26, 0, 5], [5, 26, -10, -163, -77, 231, 98, -120, -26, 25], [25, 130, -49, -810, -388, 1123, 481, -552, -120, 99]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -32, -9, 48, 10, -26, 0, 5], [5, 26, -10, -163, -77, 231, 98, -120, -26, 25], [25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], [99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -32, -9, 48, 10, -26, 0, 5], [5, 26, -10, -163, -77, 231, 98, -120, -26, 25], [25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], [99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], [375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -32, -9, 48, 10, -26, 0, 5], [5, 26, -10, -163, -77, 231, 98, -120, -26, 25], [25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], [99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], [375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323], [1323, 6990, -1995, -42941, -24074, 56912, 29529, -26284, -7637, 4522]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -32, -9, 48, 10, -26, 0, 5], [5, 26, -10, -163, -77, 231, 98, -120, -26, 25], [25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], [99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], [375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323], [1323, 6990, -1995, -42941, -24074, 56912, 29529, -26284, -7637, 4522], [4522, 23933, -6576, -146699, -83639, 192982, 102132, -88043, -26284, 14973]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -32, -9, 48, 10, -26, 0, 5], [5, 26, -10, -163, -77, 231, 98, -120, -26, 25], [25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], [99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], [375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323], [1323, 6990, -1995, -42941, -24074, 56912, 29529, -26284, -7637, 4522], [4522, 23933, -6576, -146699, -83639, 192982, 102132, -88043, -26284, 14973], [14973, 79387, -20986, -485712, -281456, 635065, 342712, -287166, -88043, 48581]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -32, -9, 48, 10, -26, 0, 5], [5, 26, -10, -163, -77, 231, 98, -120, -26, 25], [25, 130, -49, -810, -388, 1123, 481, -552, -120, 99], [99, 520, -167, -3217, -1701, 4364, 2113, -2093, -552, 375], [375, 1974, -605, -12167, -6592, 16299, 8114, -7637, -2093, 1323], [1323, 6990, -1995, -42941, -24074, 56912, 29529, -26284, -7637, 4522], [4522, 23933, -6576, -146699, -83639, 192982, 102132, -88043, -26284, 14973], [14973, 79387, -20986, -485712, -281456, 635065, 342712, -287166, -88043, 48581], [48581, 257878, -66356, -1575578, -922941, 2050432, 1120875, -920394, -287166, 154862]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp106697478869 : Fact (Nat.Prime 106697478869) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 4
  a' := [1]
  b' := [0, 1]
  k := [1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1]
  f := [1, 3, -1, -15, -4, 25, 6, -12, 1, 3]
  g := [1, 0, 0, 1, 0, 1, 0, 1]
  h := [1, 1, 1, 1]
  a := [1, 1, 1, 0, 1, 0, 1]
  b := [0, 0, 1, 1, 1, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD106697478869 : CertificateDedekindCriterionLists l 106697478869 where
  n := 2
  a' := [22695278393, 60966198739, 87609925449, 54298545598, 64415053076, 105241934048, 8023108118, 56795919559]
  b' := [37880571028, 87073410007, 93979941546, 53756099181, 43822025525, 81188120377, 43752746732, 22057941383, 17399893131]
  k := [69756324750, 70961820000, 96222242289, 9288110252, 3950483352, 45312613024, 95504804061, 101933249777, 1]
  f := [30713995709, 5672737249, 21159998083, 30159951375, 21647165712, 28598305444, 8893009856, 9413467881, 26621186924, 1]
  g := [58802363040, 10860532712, 40511104481, 57741637617, 41443793540, 54751845216, 17025788471, 18022212448, 50966624886, 1]
  h := [55730853978, 1]
  a := [80976237392, 41811640640, 52754218084, 3817436706, 7142190551, 83587318795, 384809160, 12033052515, 13550153393]
  b := [30565516912, 18642641754, 59513275457, 78895697856, 75565931937, 74364640440, 2028975665, 100999319733, 93147325476]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 106697478869]
  exp := ![2, 1]
  pdgood := [2, 106697478869]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp106697478869.out
  a := [5714524665249, -22148731109010, -57545320710819, 90137739477186, 70563828336159, -88084859680962, -11791144533235, 25633292813790, -5173699862160]
  b := [-1228262916145, -2758693942821, 10193429328954, 13223190503907, -19567736963871, -10928289309519, 12783534406585, 1296696625027, -2822014274487, 517369986216]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 106697478869 T_ofList CD106697478869

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

end VoightMaximalOrderD10R671

namespace VoightMaximalOrderD10R677

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6865906065625, [-1, -1, 12, 11, -34, -22, 33, 14, -10, -2, 1], 1⟩
local notation "l" => [-1, -1, 12, 11, -34, -22, 33, 14, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -11, 34, 22, -33, -14, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -11, 34, 22, -33, -14, 10, 2], ![2, 3, -23, -34, 57, 78, -44, -61, 6, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -11, 34, 22, -33, -14, 10, 2], ![2, 3, -23, -34, 57, 78, -44, -61, 6, 14], ![14, 16, -165, -177, 442, 365, -384, -240, 79, 34]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -11, 34, 22, -33, -14, 10, 2], ![2, 3, -23, -34, 57, 78, -44, -61, 6, 14], ![14, 16, -165, -177, 442, 365, -384, -240, 79, 34], ![34, 48, -392, -539, 979, 1190, -757, -860, 100, 147]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -11, 34, 22, -33, -14, 10, 2], ![2, 3, -23, -34, 57, 78, -44, -61, 6, 14], ![14, 16, -165, -177, 442, 365, -384, -240, 79, 34], ![34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], ![147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -11, 34, 22, -33, -14, 10, 2], ![2, 3, -23, -34, 57, 78, -44, -61, 6, 14], ![14, 16, -165, -177, 442, 365, -384, -240, 79, 34], ![34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], ![147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394], ![394, 541, -4547, -6050, 11387, 13127, -8789, -9177, 1125, 1398]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -11, 34, 22, -33, -14, 10, 2], ![2, 3, -23, -34, 57, 78, -44, -61, 6, 14], ![14, 16, -165, -177, 442, 365, -384, -240, 79, 34], ![34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], ![147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394], ![394, 541, -4547, -6050, 11387, 13127, -8789, -9177, 1125, 1398], ![1398, 1792, -16235, -19925, 41482, 42143, -33007, -28361, 4803, 3921]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -11, 34, 22, -33, -14, 10, 2], ![2, 3, -23, -34, 57, 78, -44, -61, 6, 14], ![14, 16, -165, -177, 442, 365, -384, -240, 79, 34], ![34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], ![147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394], ![394, 541, -4547, -6050, 11387, 13127, -8789, -9177, 1125, 1398], ![1398, 1792, -16235, -19925, 41482, 42143, -33007, -28361, 4803, 3921], ![3921, 5319, -45260, -59366, 113389, 127744, -87250, -87901, 10849, 12645]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -12, -11, 34, 22, -33, -14, 10, 2], ![2, 3, -23, -34, 57, 78, -44, -61, 6, 14], ![14, 16, -165, -177, 442, 365, -384, -240, 79, 34], ![34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], ![147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394], ![394, 541, -4547, -6050, 11387, 13127, -8789, -9177, 1125, 1398], ![1398, 1792, -16235, -19925, 41482, 42143, -33007, -28361, 4803, 3921], ![3921, 5319, -45260, -59366, 113389, 127744, -87250, -87901, 10849, 12645], ![12645, 16566, -146421, -184355, 370564, 391579, -289541, -264280, 38549, 36139]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-147, -34, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-147, -34, -14, -2, -1], [-394, -147, -34, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-147, -34, -14, -2, -1], [-394, -147, -34, -14, -2, -1], [-1398, -394, -147, -34, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-147, -34, -14, -2, -1], [-394, -147, -34, -14, -2, -1], [-1398, -394, -147, -34, -14, -2, -1], [-3921, -1398, -394, -147, -34, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-34, -14, -2, -1], [-147, -34, -14, -2, -1], [-394, -147, -34, -14, -2, -1], [-1398, -394, -147, -34, -14, -2, -1], [-3921, -1398, -394, -147, -34, -14, -2, -1], [-12645, -3921, -1398, -394, -147, -34, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -11, 34, 22, -33, -14, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -11, 34, 22, -33, -14, 10, 2], [2, 3, -23, -34, 57, 78, -44, -61, 6, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -11, 34, 22, -33, -14, 10, 2], [2, 3, -23, -34, 57, 78, -44, -61, 6, 14], [14, 16, -165, -177, 442, 365, -384, -240, 79, 34]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -11, 34, 22, -33, -14, 10, 2], [2, 3, -23, -34, 57, 78, -44, -61, 6, 14], [14, 16, -165, -177, 442, 365, -384, -240, 79, 34], [34, 48, -392, -539, 979, 1190, -757, -860, 100, 147]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -11, 34, 22, -33, -14, 10, 2], [2, 3, -23, -34, 57, 78, -44, -61, 6, 14], [14, 16, -165, -177, 442, 365, -384, -240, 79, 34], [34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], [147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -11, 34, 22, -33, -14, 10, 2], [2, 3, -23, -34, 57, 78, -44, -61, 6, 14], [14, 16, -165, -177, 442, 365, -384, -240, 79, 34], [34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], [147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394], [394, 541, -4547, -6050, 11387, 13127, -8789, -9177, 1125, 1398]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -11, 34, 22, -33, -14, 10, 2], [2, 3, -23, -34, 57, 78, -44, -61, 6, 14], [14, 16, -165, -177, 442, 365, -384, -240, 79, 34], [34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], [147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394], [394, 541, -4547, -6050, 11387, 13127, -8789, -9177, 1125, 1398], [1398, 1792, -16235, -19925, 41482, 42143, -33007, -28361, 4803, 3921]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -11, 34, 22, -33, -14, 10, 2], [2, 3, -23, -34, 57, 78, -44, -61, 6, 14], [14, 16, -165, -177, 442, 365, -384, -240, 79, 34], [34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], [147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394], [394, 541, -4547, -6050, 11387, 13127, -8789, -9177, 1125, 1398], [1398, 1792, -16235, -19925, 41482, 42143, -33007, -28361, 4803, 3921], [3921, 5319, -45260, -59366, 113389, 127744, -87250, -87901, 10849, 12645]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -12, -11, 34, 22, -33, -14, 10, 2], [2, 3, -23, -34, 57, 78, -44, -61, 6, 14], [14, 16, -165, -177, 442, 365, -384, -240, 79, 34], [34, 48, -392, -539, 979, 1190, -757, -860, 100, 147], [147, 181, -1716, -2009, 4459, 4213, -3661, -2815, 610, 394], [394, 541, -4547, -6050, 11387, 13127, -8789, -9177, 1125, 1398], [1398, 1792, -16235, -19925, 41482, 42143, -33007, -28361, 4803, 3921], [3921, 5319, -45260, -59366, 113389, 127744, -87250, -87901, 10849, 12645], [12645, 16566, -146421, -184355, 370564, 391579, -289541, -264280, 38549, 36139]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7159 : Fact (Nat.Prime 7159) := fact_iff.2 (by norm_num)
instance hp306899 : Fact (Nat.Prime 306899) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 3, 4]
  b' := [0, 1, 4, 0, 1]
  k := [1]
  f := [1, 1, 1, 1, 14, 10, 1, 2, 6, 2]
  g := [2, 1, 4, 2, 4, 1]
  h := [2, 1, 4, 2, 4, 1]
  a := [1, 2, 1, 4]
  b := [0, 1, 0, 4, 4, 4, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7159 : CertificateDedekindCriterionLists l 7159 where
  n := 2
  a' := [773, 2750, 3893, 674, 2935, 4818, 2347, 5800]
  b' := [482, 640, 2399, 1722, 3845, 5117, 3390, 3025, 151]
  k := [4423, 3212, 3680, 5011, 5429, 4270, 5342, 1816, 1]
  f := [2489, 4878, 1175, 1576, 2271, 3647, 1916, 1020, 792, 1]
  g := [2851, 5587, 1345, 1805, 2601, 4177, 2194, 1168, 907, 1]
  h := [6250, 1]
  a := [2092, 5741, 3361, 6826, 1660, 4471, 4102, 4167, 6361]
  b := [190, 5525, 6699, 4472, 4997, 2740, 3905, 4289, 798]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD306899 : CertificateDedekindCriterionLists l 306899 where
  n := 2
  a' := [190669, 160638, 177392, 73717, 133400, 249136, 66288, 163157]
  b' := [121842, 299556, 87397, 117414, 255887, 163928, 132475, 102967, 118271]
  k := [284050, 283759, 149091, 28564, 133071, 256291, 73725, 127923, 1]
  f := [52361, 59024, 49526, 27406, 48124, 82670, 80934, 54389, 63394, 1]
  g := [179574, 202423, 169849, 93988, 165042, 283518, 277563, 186526, 217410, 1]
  h := [89487, 1]
  a := [7117, 22131, 113659, 87640, 235394, 35355, 29413, 84269, 97398]
  b := [262549, 186963, 284005, 169924, 59240, 92665, 11623, 156777, 209501]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 7159, 306899]
  exp := ![1, 1, 1]
  pdgood := [5, 7159, 306899]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7159.out
    exact hp306899.out
  a := [-126925210855, 2609398581154, 8004613248014, -7631191056140, -24974131589592, -3194426369462, 10226146099582, 1175394067442, -1173479914740]
  b := [115939761150, 300080897301, -1109160706254, -2941811392994, 909370685990, 4255964443194, 607969068905, -1276047988488, -141009005039, 117347991474]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7159 T_ofList CD7159
    exact satisfiesDedekindCriterion_of_certificate_lists T l 306899 T_ofList CD306899

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

end VoightMaximalOrderD10R677

end TraceEuclidean
