import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk185
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

namespace VoightMaximalOrderD10R227

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3453020641017, [3, -9, -12, 38, 15, -49, -3, 24, -3, -4, 1], 1⟩
local notation "l" => [3, -9, -12, 38, 15, -49, -3, 24, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 9, 12, -38, -15, 49, 3, -24, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], ![-12, 33, 57, -140, -98, 181, 61, -93, -12, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], ![-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], ![-57, 159, 261, -665, -425, 833, 238, -395, -36, 64]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], ![-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], ![-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], ![-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], ![-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], ![-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], ![-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], ![-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], ![-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], ![-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], ![-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], ![-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677], ![-2031, 5433, 9912, -22567, -17588, 27702, 11186, -12877, -2224, 2070]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], ![-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], ![-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], ![-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], ![-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677], ![-2031, 5433, 9912, -22567, -17588, 27702, 11186, -12877, -2224, 2070], ![-6210, 16599, 30273, -68748, -53617, 83842, 33912, -38494, -6667, 6056]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], ![-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], ![-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], ![-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], ![-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677], ![-2031, 5433, 9912, -22567, -17588, 27702, 11186, -12877, -2224, 2070], ![-6210, 16599, 30273, -68748, -53617, 83842, 33912, -38494, -6667, 6056], ![-18168, 48294, 89271, -199855, -159588, 243127, 102010, -111432, -20326, 17557]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], ![-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], ![-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], ![-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], ![-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677], ![-2031, 5433, 9912, -22567, -17588, 27702, 11186, -12877, -2224, 2070], ![-6210, 16599, 30273, -68748, -53617, 83842, 33912, -38494, -6667, 6056], ![-18168, 48294, 89271, -199855, -159588, 243127, 102010, -111432, -20326, 17557], ![-52671, 139845, 258978, -577895, -463210, 700705, 295798, -319358, -58761, 49902]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1], [-677, -220, -64, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1], [-677, -220, -64, -19, -4, -1], [-2070, -677, -220, -64, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1], [-677, -220, -64, -19, -4, -1], [-2070, -677, -220, -64, -19, -4, -1], [-6056, -2070, -677, -220, -64, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-64, -19, -4, -1], [-220, -64, -19, -4, -1], [-677, -220, -64, -19, -4, -1], [-2070, -677, -220, -64, -19, -4, -1], [-6056, -2070, -677, -220, -64, -19, -4, -1], [-17557, -6056, -2070, -677, -220, -64, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 9, 12, -38, -15, 49, 3, -24, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], [-12, 33, 57, -140, -98, 181, 61, -93, -12, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], [-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], [-57, 159, 261, -665, -425, 833, 238, -395, -36, 64]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], [-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], [-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], [-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], [-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], [-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], [-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], [-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], [-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], [-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], [-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], [-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677], [-2031, 5433, 9912, -22567, -17588, 27702, 11186, -12877, -2224, 2070]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], [-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], [-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], [-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], [-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677], [-2031, 5433, 9912, -22567, -17588, 27702, 11186, -12877, -2224, 2070], [-6210, 16599, 30273, -68748, -53617, 83842, 33912, -38494, -6667, 6056]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], [-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], [-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], [-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], [-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677], [-2031, 5433, 9912, -22567, -17588, 27702, 11186, -12877, -2224, 2070], [-6210, 16599, 30273, -68748, -53617, 83842, 33912, -38494, -6667, 6056], [-18168, 48294, 89271, -199855, -159588, 243127, 102010, -111432, -20326, 17557]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 9, 12, -38, -15, 49, 3, -24, 3, 4], [-12, 33, 57, -140, -98, 181, 61, -93, -12, 19], [-57, 159, 261, -665, -425, 833, 238, -395, -36, 64], [-192, 519, 927, -2171, -1625, 2711, 1025, -1298, -203, 220], [-660, 1788, 3159, -7433, -5471, 9155, 3371, -4255, -638, 677], [-2031, 5433, 9912, -22567, -17588, 27702, 11186, -12877, -2224, 2070], [-6210, 16599, 30273, -68748, -53617, 83842, 33912, -38494, -6667, 6056], [-18168, 48294, 89271, -199855, -159588, 243127, 102010, -111432, -20326, 17557], [-52671, 139845, 258978, -577895, -463210, 700705, 295798, -319358, -58761, 49902]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp3041 : Fact (Nat.Prime 3041) := fact_iff.2 (by norm_num)
instance hp14018377 : Fact (Nat.Prime 14018377) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [1, 1, 2, 0, 1, 2]
  b' := [2, 2, 2, 0, 2, 0, 2]
  k := [1, 0, 2, 0, 1, 0, 2, 1, 2, 1, 0, 0, 1, 1, 1]
  f := [-1, 3, 4, -12, -5, 17, 1, -8, 1, 2]
  g := [0, 2, 0, 2, 0, 0, 0, 2, 1]
  h := [0, 0, 1]
  a := [2, 0, 1, 1, 1, 1, 1, 2]
  b := [0, 1, 2, 1, 2, 2, 2, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3041 : CertificateDedekindCriterionLists l 3041 where
  n := 2
  a' := [2926, 1123, 2095, 751, 1970, 1632, 254, 1004]
  b' := [704, 1680, 482, 1362, 878, 61, 1128, 794, 1240]
  k := [975, 2585, 2690, 2259, 2310, 280, 2076, 1095, 1]
  f := [311, 698, 753, 185, 323, 160, 937, 311, 660, 1]
  g := [974, 2185, 2356, 577, 1011, 500, 2934, 971, 2066, 1]
  h := [971, 1]
  a := [2353, 2889, 1010, 2774, 1033, 2893, 2722, 1123, 343]
  b := [1940, 86, 1240, 1562, 2025, 2832, 1413, 657, 2698]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD14018377 : CertificateDedekindCriterionLists l 14018377 where
  n := 2
  a' := [6980716, 434285, 3846031, 11788480, 12962554, 4772681, 1797402, 3168501]
  b' := [10223706, 13116245, 6609232, 5244709, 11704564, 9236143, 8922896, 2825994, 8993529]
  k := [46583, 9792629, 9199119, 4475383, 10293849, 3855370, 11176471, 1212579, 1]
  f := [5098200, 3892815, 3014311, 5741308, 1774133, 5703889, 252650, 3466685, 3478371, 1]
  g := [11161899, 8522851, 6599472, 12569906, 3884250, 12487982, 553145, 7589892, 7615476, 1]
  h := [6402897, 1]
  a := [898822, 13196002, 3432065, 473145, 1116176, 5296679, 8648215, 8238519, 4267310]
  b := [6994924, 12244098, 1541213, 11412402, 9428380, 1581670, 11067333, 5893295, 9751067]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 3041, 14018377]
  exp := ![2, 1, 1]
  pdgood := [3, 3041, 14018377]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp3041.out
    exact hp14018377.out
  a := [-655500239841, -4113854924910, 50084260806, 12537273980224, -746714386476, -9864660250062, 1844938886508, 2296884262452, -681354081320]
  b := [-261129964404, -19438163385, 1748738884876, 196092427914, -2708338308167, 81747712662, 1453606479429, -231614750742, -256942589498, 68135408132]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3041 T_ofList CD3041
    exact satisfiesDedekindCriterion_of_certificate_lists T l 14018377 T_ofList CD14018377

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

end VoightMaximalOrderD10R227

namespace VoightMaximalOrderD10R234

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3487343440625, [1, 8, 9, -26, -41, 21, 43, -3, -12, 0, 1], 1⟩
local notation "l" => [1, 8, 9, -26, -41, 21, 43, -3, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -9, 26, 41, -21, -43, 3, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], ![0, -1, -8, -9, 26, 41, -21, -43, 3, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], ![0, -1, -8, -9, 26, 41, -21, -43, 3, 12], ![-12, -96, -109, 304, 483, -226, -475, 15, 101, 3]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], ![0, -1, -8, -9, 26, 41, -21, -43, 3, 12], ![-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], ![-3, -36, -123, -31, 427, 420, -355, -466, 51, 101]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], ![0, -1, -8, -9, 26, 41, -21, -43, 3, 12], ![-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], ![-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], ![-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], ![0, -1, -8, -9, 26, 41, -21, -43, 3, 12], ![-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], ![-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], ![-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51], ![-51, -509, -1270, 381, 4594, 3039, -3887, -3770, 560, 746]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], ![0, -1, -8, -9, 26, 41, -21, -43, 3, 12], ![-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], ![-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], ![-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51], ![-51, -509, -1270, 381, 4594, 3039, -3887, -3770, 560, 746], ![-746, -6019, -7223, 18126, 30967, -11072, -29039, -1649, 5182, 560]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], ![0, -1, -8, -9, 26, 41, -21, -43, 3, 12], ![-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], ![-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], ![-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51], ![-51, -509, -1270, 381, 4594, 3039, -3887, -3770, 560, 746], ![-746, -6019, -7223, 18126, 30967, -11072, -29039, -1649, 5182, 560], ![-560, -5226, -11059, 7337, 41086, 19207, -35152, -27359, 5071, 5182]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], ![0, -1, -8, -9, 26, 41, -21, -43, 3, 12], ![-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], ![-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], ![-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51], ![-51, -509, -1270, 381, 4594, 3039, -3887, -3770, 560, 746], ![-746, -6019, -7223, 18126, 30967, -11072, -29039, -1649, 5182, 560], ![-560, -5226, -11059, 7337, 41086, 19207, -35152, -27359, 5071, 5182], ![-5182, -42016, -51864, 123673, 219799, -67736, -203619, -19606, 34825, 5071]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-3, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-3, -12, 0, -1], [-101, -3, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-3, -12, 0, -1], [-101, -3, -12, 0, -1], [-51, -101, -3, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-3, -12, 0, -1], [-101, -3, -12, 0, -1], [-51, -101, -3, -12, 0, -1], [-746, -51, -101, -3, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-3, -12, 0, -1], [-101, -3, -12, 0, -1], [-51, -101, -3, -12, 0, -1], [-746, -51, -101, -3, -12, 0, -1], [-560, -746, -51, -101, -3, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-3, -12, 0, -1], [-101, -3, -12, 0, -1], [-51, -101, -3, -12, 0, -1], [-746, -51, -101, -3, -12, 0, -1], [-560, -746, -51, -101, -3, -12, 0, -1], [-5182, -560, -746, -51, -101, -3, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -9, 26, 41, -21, -43, 3, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], [0, -1, -8, -9, 26, 41, -21, -43, 3, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], [0, -1, -8, -9, 26, 41, -21, -43, 3, 12], [-12, -96, -109, 304, 483, -226, -475, 15, 101, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], [0, -1, -8, -9, 26, 41, -21, -43, 3, 12], [-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], [-3, -36, -123, -31, 427, 420, -355, -466, 51, 101]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], [0, -1, -8, -9, 26, 41, -21, -43, 3, 12], [-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], [-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], [-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], [0, -1, -8, -9, 26, 41, -21, -43, 3, 12], [-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], [-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], [-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51], [-51, -509, -1270, 381, 4594, 3039, -3887, -3770, 560, 746]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], [0, -1, -8, -9, 26, 41, -21, -43, 3, 12], [-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], [-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], [-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51], [-51, -509, -1270, 381, 4594, 3039, -3887, -3770, 560, 746], [-746, -6019, -7223, 18126, 30967, -11072, -29039, -1649, 5182, 560]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], [0, -1, -8, -9, 26, 41, -21, -43, 3, 12], [-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], [-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], [-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51], [-51, -509, -1270, 381, 4594, 3039, -3887, -3770, 560, 746], [-746, -6019, -7223, 18126, 30967, -11072, -29039, -1649, 5182, 560], [-560, -5226, -11059, 7337, 41086, 19207, -35152, -27359, 5071, 5182]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -9, 26, 41, -21, -43, 3, 12, 0], [0, -1, -8, -9, 26, 41, -21, -43, 3, 12], [-12, -96, -109, 304, 483, -226, -475, 15, 101, 3], [-3, -36, -123, -31, 427, 420, -355, -466, 51, 101], [-101, -811, -945, 2503, 4110, -1694, -3923, -52, 746, 51], [-51, -509, -1270, 381, 4594, 3039, -3887, -3770, 560, 746], [-746, -6019, -7223, 18126, 30967, -11072, -29039, -1649, 5182, 560], [-560, -5226, -11059, 7337, 41086, 19207, -35152, -27359, 5071, 5182], [-5182, -42016, -51864, 123673, 219799, -67736, -203619, -19606, 34825, 5071]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp101449991 : Fact (Nat.Prime 101449991) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 1]
  b' := [1, 4, 4, 3, 2]
  k := [1]
  f := [3, 0, 0, 12, 10, -1, -5, 1, 4]
  g := [4, 1, 1, 4, 0, 1]
  h := [4, 1, 1, 4, 0, 1]
  a := [1, 0, 4, 4, 4]
  b := [2, 2, 1, 0, 1, 4, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [10, 2, 7, 0, 1, 3, 2, 1]
  b' := [7, 10, 8, 5, 8, 3, 8, 7, 6]
  k := [3, 10, 8, 5, 2, 2, 0, 7, 1]
  f := [1, 0, 0, 4, 6, 0, -3, 1, 3, 1]
  g := [6, 1, 4, 7, 9, 6, 2, 3, 9, 1]
  h := [2, 1]
  a := [7, 10, 0, 6, 6, 5, 6, 3, 9]
  b := [10, 4, 0, 2, 2, 10, 6, 7, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD101449991 : CertificateDedekindCriterionLists l 101449991 where
  n := 2
  a' := [52786089, 44531605, 18977857, 58207850, 7765022, 42023871, 29394479, 77063409]
  b' := [6210405, 68987245, 63710110, 57745286, 33040935, 42209459, 94523605, 77683740, 92887390]
  k := [46922670, 13172366, 57040985, 76542757, 87851222, 13829750, 95429803, 99401817, 1]
  f := [944999, 941810, 399342, 483858, 995403, 293205, 352949, 662468, 1013750, 1]
  g := [93615230, 93299224, 39560261, 47932793, 98608397, 29045917, 34964455, 65626590, 100425904, 1]
  h := [1024087, 1]
  a := [96289736, 45893199, 45959033, 6545219, 25281220, 84242305, 6371961, 59154365, 40237155]
  b := [21797375, 88436692, 68916835, 30768290, 12915860, 59005587, 51631128, 31387659, 61212836]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 101449991]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 101449991]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp101449991.out
  a := [-1288287903687, -890700136146, 13854768570339, 5090564564022, -24436708274241, -4202462761764, 9677145704612, 702363317610, -1057234114320]
  b := [161733456649, 1035725143245, -145302413472, -3935200736405, -572724676680, 4211973772353, 493662402114, -1221450757898, -70236331761, 105723411432]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 101449991 T_ofList CD101449991

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

end VoightMaximalOrderD10R234

namespace VoightMaximalOrderD10R236

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3519966715625, [1, 0, -14, 7, 48, -46, -17, 28, -3, -4, 1], 1⟩
local notation "l" => [1, 0, -14, 7, 48, -46, -17, 28, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 14, -7, -48, 46, 17, -28, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], ![-4, -1, 56, -14, -199, 136, 114, -95, -16, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], ![-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], ![-19, -4, 265, -77, -926, 675, 459, -418, -38, 60]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], ![-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], ![-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], ![-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], ![-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], ![-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], ![-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], ![-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], ![-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], ![-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], ![-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], ![-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570], ![-570, -202, 7920, -1181, -27938, 16369, 16025, -10692, -2251, 1665]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], ![-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], ![-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], ![-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], ![-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570], ![-570, -202, 7920, -1181, -27938, 16369, 16025, -10692, -2251, 1665], ![-1665, -570, 23108, -3735, -81101, 48652, 44674, -30595, -5697, 4409]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], ![-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], ![-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], ![-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], ![-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570], ![-570, -202, 7920, -1181, -27938, 16369, 16025, -10692, -2251, 1665], ![-1665, -570, 23108, -3735, -81101, 48652, 44674, -30595, -5697, 4409], ![-4409, -1665, 61156, -7755, -215367, 121713, 123605, -78778, -17368, 11939]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], ![-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], ![-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], ![-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], ![-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570], ![-570, -202, 7920, -1181, -27938, 16369, 16025, -10692, -2251, 1665], ![-1665, -570, 23108, -3735, -81101, 48652, 44674, -30595, -5697, 4409], ![-4409, -1665, 61156, -7755, -215367, 121713, 123605, -78778, -17368, 11939], ![-11939, -4409, 165481, -22417, -580827, 333827, 324676, -210687, -42961, 30388]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1], [-570, -202, -60, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1], [-570, -202, -60, -19, -4, -1], [-1665, -570, -202, -60, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1], [-570, -202, -60, -19, -4, -1], [-1665, -570, -202, -60, -19, -4, -1], [-4409, -1665, -570, -202, -60, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1], [-570, -202, -60, -19, -4, -1], [-1665, -570, -202, -60, -19, -4, -1], [-4409, -1665, -570, -202, -60, -19, -4, -1], [-11939, -4409, -1665, -570, -202, -60, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 14, -7, -48, 46, 17, -28, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], [-4, -1, 56, -14, -199, 136, 114, -95, -16, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], [-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], [-19, -4, 265, -77, -926, 675, 459, -418, -38, 60]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], [-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], [-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], [-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], [-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], [-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], [-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], [-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], [-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], [-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], [-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], [-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570], [-570, -202, 7920, -1181, -27938, 16369, 16025, -10692, -2251, 1665]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], [-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], [-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], [-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], [-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570], [-570, -202, 7920, -1181, -27938, 16369, 16025, -10692, -2251, 1665], [-1665, -570, 23108, -3735, -81101, 48652, 44674, -30595, -5697, 4409]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], [-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], [-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], [-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], [-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570], [-570, -202, 7920, -1181, -27938, 16369, 16025, -10692, -2251, 1665], [-1665, -570, 23108, -3735, -81101, 48652, 44674, -30595, -5697, 4409], [-4409, -1665, 61156, -7755, -215367, 121713, 123605, -78778, -17368, 11939]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 14, -7, -48, 46, 17, -28, 3, 4], [-4, -1, 56, -14, -199, 136, 114, -95, -16, 19], [-19, -4, 265, -77, -926, 675, 459, -418, -38, 60], [-60, -19, 836, -155, -2957, 1834, 1695, -1221, -238, 202], [-202, -60, 2809, -578, -9851, 6335, 5268, -3961, -615, 570], [-570, -202, 7920, -1181, -27938, 16369, 16025, -10692, -2251, 1665], [-1665, -570, 23108, -3735, -81101, 48652, 44674, -30595, -5697, 4409], [-4409, -1665, 61156, -7755, -215367, 121713, 123605, -78778, -17368, 11939], [-11939, -4409, 165481, -22417, -580827, 333827, 324676, -210687, -42961, 30388]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp269 : Fact (Nat.Prime 269) := fact_iff.2 (by norm_num)
instance hp14489 : Fact (Nat.Prime 14489) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2, 4]
  b' := [3, 0, 1, 0, 3]
  k := [1]
  f := [3, 0, 6, 5, -4, 14, 9, 0, 4, 2]
  g := [4, 0, 2, 4, 3, 1]
  h := [4, 0, 2, 4, 3, 1]
  a := [4, 0, 2, 0, 4]
  b := [1, 0, 2, 4, 0, 3, 4, 3, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [10, 0, 6, 2, 4, 9, 3]
  b' := [0, 7, 7, 16, 4, 5, 10, 6]
  k := [8, 12, 7, 5, 5, 11, 1]
  f := [7, 6, 5, 1, 4, 4, 7, 6, 2, 1]
  g := [12, 9, 5, 1, 11, 1, 9, 12, 1]
  h := [10, 1, 1]
  a := [9, 16, 15, 2, 7, 9, 0, 7]
  b := [9, 12, 5, 7, 6, 8, 5, 2, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD269 : CertificateDedekindCriterionLists l 269 where
  n := 2
  a' := [124, 27, 223, 17, 22, 96, 133, 36]
  b' := [248, 92, 47, 22, 126, 13, 206, 151, 265]
  k := [166, 72, 182, 117, 43, 94, 131, 65, 1]
  f := [71, 39, 93, 18, 42, 11, 5, 65, 62, 1]
  g := [191, 103, 249, 46, 113, 28, 13, 175, 165, 1]
  h := [100, 1]
  a := [208, 175, 155, 103, 124, 241, 179, 20, 187]
  b := [110, 143, 13, 156, 203, 232, 25, 142, 82]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD14489 : CertificateDedekindCriterionLists l 14489 where
  n := 2
  a' := [1388, 729, 11564, 1000, 6025, 6336, 4317, 5452]
  b' := [1194, 1886, 5268, 10324, 6967, 12440, 3230, 1161, 2614]
  k := [6535, 9019, 2381, 2239, 9420, 8774, 2066, 6057, 1]
  f := [2731, 2314, 488, 1509, 3708, 2074, 2039, 3239, 2988, 1]
  g := [9390, 7954, 1676, 5188, 12748, 7128, 7009, 11135, 10271, 1]
  h := [4214, 1]
  a := [3478, 5926, 511, 11747, 13090, 10437, 1441, 5040, 11067]
  b := [11399, 13958, 8246, 10376, 2168, 6532, 8375, 8103, 3422]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 17, 269, 14489]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 17, 269, 14489]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp17.out
    exact hp269.out
    exact hp14489.out
  a := [331290985, -4276000176, -20948772138, 38781108690, 8995698128, -32426659328, 6024312820, 5921371298, -1825110480]
  b := [-152714292, -1028351645, 1787414980, 5838034286, -8021815979, -1665208318, 4709119251, -737898968, -665141549, 182511048]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 269 T_ofList CD269
    exact satisfiesDedekindCriterion_of_certificate_lists T l 14489 T_ofList CD14489

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

end VoightMaximalOrderD10R236

namespace VoightMaximalOrderD10R238

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3530693065625, [1, 14, 27, -28, -57, 17, 40, -3, -11, 0, 1], 1⟩
local notation "l" => [1, 14, 27, -28, -57, 17, 40, -3, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -27, 28, 57, -17, -40, 3, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], ![0, -1, -14, -27, 28, 57, -17, -40, 3, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], ![0, -1, -14, -27, 28, 57, -17, -40, 3, 11], ![-11, -154, -298, 294, 600, -159, -383, 16, 81, 3]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], ![0, -1, -14, -27, 28, 57, -17, -40, 3, 11], ![-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], ![-3, -53, -235, -214, 465, 549, -279, -374, 49, 81]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], ![0, -1, -14, -27, 28, 57, -17, -40, 3, 11], ![-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], ![-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], ![-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], ![0, -1, -14, -27, 28, 57, -17, -40, 3, 11], ![-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], ![-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], ![-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49], ![-49, -767, -2460, -868, 4826, 3570, -2872, -2544, 503, 517]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], ![0, -1, -14, -27, 28, 57, -17, -40, 3, 11], ![-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], ![-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], ![-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49], ![-49, -767, -2460, -868, 4826, 3570, -2872, -2544, 503, 517], ![-517, -7287, -14726, 12016, 28601, -3963, -17110, -1321, 3143, 503]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], ![0, -1, -14, -27, 28, 57, -17, -40, 3, 11], ![-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], ![-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], ![-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49], ![-49, -767, -2460, -868, 4826, 3570, -2872, -2544, 503, 517], ![-517, -7287, -14726, 12016, 28601, -3963, -17110, -1321, 3143, 503], ![-503, -7559, -20868, -642, 40687, 20050, -24083, -15601, 4212, 3143]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], ![0, -1, -14, -27, 28, 57, -17, -40, 3, 11], ![-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], ![-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], ![-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49], ![-49, -767, -2460, -868, 4826, 3570, -2872, -2544, 503, 517], ![-517, -7287, -14726, 12016, 28601, -3963, -17110, -1321, 3143, 503], ![-503, -7559, -20868, -642, 40687, 20050, -24083, -15601, 4212, 3143], ![-3143, -44505, -92420, 67136, 178509, -12744, -105670, -14654, 18972, 4212]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1], [-49, -81, -3, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1], [-49, -81, -3, -11, 0, -1], [-517, -49, -81, -3, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1], [-49, -81, -3, -11, 0, -1], [-517, -49, -81, -3, -11, 0, -1], [-503, -517, -49, -81, -3, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1], [-49, -81, -3, -11, 0, -1], [-517, -49, -81, -3, -11, 0, -1], [-503, -517, -49, -81, -3, -11, 0, -1], [-3143, -503, -517, -49, -81, -3, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -27, 28, 57, -17, -40, 3, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], [0, -1, -14, -27, 28, 57, -17, -40, 3, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], [0, -1, -14, -27, 28, 57, -17, -40, 3, 11], [-11, -154, -298, 294, 600, -159, -383, 16, 81, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], [0, -1, -14, -27, 28, 57, -17, -40, 3, 11], [-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], [-3, -53, -235, -214, 465, 549, -279, -374, 49, 81]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], [0, -1, -14, -27, 28, 57, -17, -40, 3, 11], [-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], [-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], [-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], [0, -1, -14, -27, 28, 57, -17, -40, 3, 11], [-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], [-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], [-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49], [-49, -767, -2460, -868, 4826, 3570, -2872, -2544, 503, 517]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], [0, -1, -14, -27, 28, 57, -17, -40, 3, 11], [-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], [-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], [-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49], [-49, -767, -2460, -868, 4826, 3570, -2872, -2544, 503, 517], [-517, -7287, -14726, 12016, 28601, -3963, -17110, -1321, 3143, 503]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], [0, -1, -14, -27, 28, 57, -17, -40, 3, 11], [-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], [-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], [-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49], [-49, -767, -2460, -868, 4826, 3570, -2872, -2544, 503, 517], [-517, -7287, -14726, 12016, 28601, -3963, -17110, -1321, 3143, 503], [-503, -7559, -20868, -642, 40687, 20050, -24083, -15601, 4212, 3143]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -27, 28, 57, -17, -40, 3, 11, 0], [0, -1, -14, -27, 28, 57, -17, -40, 3, 11], [-11, -154, -298, 294, 600, -159, -383, 16, 81, 3], [-3, -53, -235, -214, 465, 549, -279, -374, 49, 81], [-81, -1137, -2240, 2033, 4403, -912, -2691, -36, 517, 49], [-49, -767, -2460, -868, 4826, 3570, -2872, -2544, 503, 517], [-517, -7287, -14726, 12016, 28601, -3963, -17110, -1321, 3143, 503], [-503, -7559, -20868, -642, 40687, 20050, -24083, -15601, 4212, 3143], [-3143, -44505, -92420, 67136, 178509, -12744, -105670, -14654, 18972, 4212]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp102711071 : Fact (Nat.Prime 102711071) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 2]
  b' := [3, 4, 0, 1, 3]
  k := [1]
  f := [3, 2, -2, 10, 14, -1, -6, 1, 3]
  g := [4, 3, 1, 2, 0, 1]
  h := [4, 3, 1, 2, 0, 1]
  a := [2, 3, 3, 0, 3]
  b := [0, 3, 0, 3, 1, 2, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [3, 5, 6, 0, 3, 6, 9, 3]
  b' := [3, 7, 2, 2, 9, 9, 3, 9, 7]
  k := [4, 7, 9, 0, 0, 2, 9, 10, 1]
  f := [1, 0, 1, 8, 6, -1, -3, 2, 4, 1]
  g := [2, 2, 6, 9, 0, 1, 1, 3, 5, 1]
  h := [6, 1]
  a := [7, 2, 5, 8, 8, 5, 2, 3, 10]
  b := [8, 2, 1, 1, 1, 8, 5, 7, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD102711071 : CertificateDedekindCriterionLists l 102711071 where
  n := 2
  a' := [87894948, 46010182, 95054126, 82568249, 32037056, 94099225, 47125367, 39965428]
  b' := [42666282, 43624921, 65827399, 52243706, 58754427, 15623182, 86025860, 18221527, 52621103]
  k := [80513278, 5394679, 15426692, 26589433, 45489240, 78025799, 90861031, 77832182, 1]
  f := [46685069, 29428461, 47535486, 31936749, 23428889, 32479527, 6763955, 18811592, 24171214, 1]
  g := [75163805, 47380353, 76532991, 51418742, 37720934, 52292625, 10890089, 30287003, 38916091, 1]
  h := [63794980, 1]
  a := [11890229, 49038806, 75053228, 102403482, 89389053, 25241165, 30836369, 41139764, 42582773]
  b := [39967078, 40182803, 68502183, 17870079, 39941541, 11043748, 23971883, 1909749, 60128298]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 102711071]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 102711071]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp102711071.out
  a := [-82206962125, -214009766618, 656142152027, 680683271620, -1053296652175, -461364202562, 501450649184, 85100765550, -69696261180]
  b := [6275433645, 73288129967, 80654283283, -225609582129, -124001325591, 199889933181, 58585925171, -65478242378, -8510076555, 6969626118]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 102711071 T_ofList CD102711071

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

end VoightMaximalOrderD10R238

end TraceEuclidean
