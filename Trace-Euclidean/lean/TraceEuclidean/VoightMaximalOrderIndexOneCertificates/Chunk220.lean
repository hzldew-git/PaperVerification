import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk216
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

namespace VoightMaximalOrderD10R571

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6224132763557, [-1, 19, -108, 177, -28, -121, 50, 27, -13, -2, 1], 1⟩
local notation "l" => [-1, 19, -108, 177, -28, -121, 50, 27, -13, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -19, 108, -177, 28, 121, -50, -27, 13, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -19, 108, -177, 28, 121, -50, -27, 13, 2], ![2, -37, 197, -246, -121, 270, 21, -104, -1, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -19, 108, -177, 28, 121, -50, -27, 13, 2], ![2, -37, 197, -246, -121, 270, 21, -104, -1, 17], ![17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -19, 108, -177, 28, 121, -50, -27, 13, 2], ![2, -37, 197, -246, -121, 270, 21, -104, -1, 17], ![17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], ![33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -19, 108, -177, 28, 121, -50, -27, 13, 2], ![2, -37, 197, -246, -121, 270, 21, -104, -1, 17], ![17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], ![33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], ![183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -19, 108, -177, 28, 121, -50, -27, 13, 2], ![2, -37, 197, -246, -121, 270, 21, -104, -1, 17], ![17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], ![33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], ![183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357], ![357, -6600, 35112, -44035, -19152, 44279, 2405, -14566, -14, 1622]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -19, 108, -177, 28, 121, -50, -27, 13, 2], ![2, -37, 197, -246, -121, 270, 21, -104, -1, 17], ![17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], ![33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], ![183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357], ![357, -6600, 35112, -44035, -19152, 44279, 2405, -14566, -14, 1622], ![1622, -30461, 168576, -251982, 1381, 177110, -36821, -41389, 6520, 3230]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -19, 108, -177, 28, 121, -50, -27, 13, 2], ![2, -37, 197, -246, -121, 270, 21, -104, -1, 17], ![17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], ![33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], ![183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357], ![357, -6600, 35112, -44035, -19152, 44279, 2405, -14566, -14, 1622], ![1622, -30461, 168576, -251982, 1381, 177110, -36821, -41389, 6520, 3230], ![3230, -59748, 318379, -403134, -161542, 392211, 15610, -124031, 601, 12980]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -19, 108, -177, 28, 121, -50, -27, 13, 2], ![2, -37, 197, -246, -121, 270, 21, -104, -1, 17], ![17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], ![33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], ![183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357], ![357, -6600, 35112, -44035, -19152, 44279, 2405, -14566, -14, 1622], ![1622, -30461, 168576, -251982, 1381, 177110, -36821, -41389, 6520, 3230], ![3230, -59748, 318379, -403134, -161542, 392211, 15610, -124031, 601, 12980], ![12980, -243390, 1342092, -1979081, -39694, 1409038, -256789, -334850, 44709, 26561]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-17, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-17, -2, -1], [-33, -17, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-17, -2, -1], [-33, -17, -2, -1], [-183, -33, -17, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-17, -2, -1], [-33, -17, -2, -1], [-183, -33, -17, -2, -1], [-357, -183, -33, -17, -2, -1]], ![[], [], [], [-1], [-2, -1], [-17, -2, -1], [-33, -17, -2, -1], [-183, -33, -17, -2, -1], [-357, -183, -33, -17, -2, -1], [-1622, -357, -183, -33, -17, -2, -1]], ![[], [], [-1], [-2, -1], [-17, -2, -1], [-33, -17, -2, -1], [-183, -33, -17, -2, -1], [-357, -183, -33, -17, -2, -1], [-1622, -357, -183, -33, -17, -2, -1], [-3230, -1622, -357, -183, -33, -17, -2, -1]], ![[], [-1], [-2, -1], [-17, -2, -1], [-33, -17, -2, -1], [-183, -33, -17, -2, -1], [-357, -183, -33, -17, -2, -1], [-1622, -357, -183, -33, -17, -2, -1], [-3230, -1622, -357, -183, -33, -17, -2, -1], [-12980, -3230, -1622, -357, -183, -33, -17, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -19, 108, -177, 28, 121, -50, -27, 13, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -19, 108, -177, 28, 121, -50, -27, 13, 2], [2, -37, 197, -246, -121, 270, 21, -104, -1, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -19, 108, -177, 28, 121, -50, -27, 13, 2], [2, -37, 197, -246, -121, 270, 21, -104, -1, 17], [17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -19, 108, -177, 28, 121, -50, -27, 13, 2], [2, -37, 197, -246, -121, 270, 21, -104, -1, 17], [17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], [33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -19, 108, -177, 28, 121, -50, -27, 13, 2], [2, -37, 197, -246, -121, 270, 21, -104, -1, 17], [17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], [33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], [183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -19, 108, -177, 28, 121, -50, -27, 13, 2], [2, -37, 197, -246, -121, 270, 21, -104, -1, 17], [17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], [33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], [183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357], [357, -6600, 35112, -44035, -19152, 44279, 2405, -14566, -14, 1622]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -19, 108, -177, 28, 121, -50, -27, 13, 2], [2, -37, 197, -246, -121, 270, 21, -104, -1, 17], [17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], [33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], [183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357], [357, -6600, 35112, -44035, -19152, 44279, 2405, -14566, -14, 1622], [1622, -30461, 168576, -251982, 1381, 177110, -36821, -41389, 6520, 3230]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -19, 108, -177, 28, 121, -50, -27, 13, 2], [2, -37, 197, -246, -121, 270, 21, -104, -1, 17], [17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], [33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], [183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357], [357, -6600, 35112, -44035, -19152, 44279, 2405, -14566, -14, 1622], [1622, -30461, 168576, -251982, 1381, 177110, -36821, -41389, 6520, 3230], [3230, -59748, 318379, -403134, -161542, 392211, 15610, -124031, 601, 12980]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -19, 108, -177, 28, 121, -50, -27, 13, 2], [2, -37, 197, -246, -121, 270, 21, -104, -1, 17], [17, -321, 1799, -2812, 230, 1936, -580, -438, 117, 33], [33, -610, 3243, -4042, -1888, 4223, 286, -1471, -9, 183], [183, -3444, 19154, -29148, 1082, 20255, -4927, -4655, 908, 357], [357, -6600, 35112, -44035, -19152, 44279, 2405, -14566, -14, 1622], [1622, -30461, 168576, -251982, 1381, 177110, -36821, -41389, 6520, 3230], [3230, -59748, 318379, -403134, -161542, 392211, 15610, -124031, 601, 12980], [12980, -243390, 1342092, -1979081, -39694, 1409038, -256789, -334850, 44709, 26561]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp10613 : Fact (Nat.Prime 10613) := fact_iff.2 (by norm_num)

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [36, 43, 37, 52, 44, 10, 39]
  b' := [53, 24, 43, 53, 0, 16, 39, 18]
  k := [41, 37, 48, 9, 28, 31, 1]
  f := [4, 23, 24, 20, 16, 14, 4, 20, 11, 1]
  g := [9, 48, 25, 37, 15, 18, 1, 45, 1]
  h := [27, 14, 1]
  a := [41, 35, 24, 32, 24, 45, 44, 51]
  b := [9, 35, 33, 33, 39, 37, 44, 43, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [228, 14, 35, 5, 249, 386, 119]
  b' := [182, 373, 353, 179, 46, 213, 347, 134]
  k := [171, 219, 182, 336, 28, 144, 1]
  f := [93, 169, 174, 243, 346, 431, 318, 151, 59, 1]
  g := [130, 88, 142, 178, 280, 282, 122, 71, 1]
  h := [284, 324, 1]
  a := [272, 360, 273, 234, 219, 149, 67, 169]
  b := [65, 90, 218, 220, 269, 93, 244, 373, 228]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD10613 : CertificateDedekindCriterionLists l 10613 where
  n := 2
  a' := [4333, 1393, 620, 288, 9138, 4274, 1851, 8322]
  b' := [2670, 8922, 8870, 6395, 234, 317, 10242, 3688, 2613]
  k := [8156, 6175, 716, 4271, 4895, 6218, 8148, 2941, 1]
  f := [632, 385, 1181, 1497, 795, 1270, 3298, 1903, 2449, 1]
  g := [1749, 1065, 3268, 4142, 2199, 3514, 9126, 5264, 6776, 1]
  h := [3835, 1]
  a := [7200, 438, 9918, 4454, 5310, 5536, 6193, 940, 9202]
  b := [4686, 6781, 2821, 3281, 13, 1478, 4275, 6751, 1411]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![61, 397, 10613]
  exp := ![1, 1, 1]
  pdgood := [61, 397, 10613]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp61.out
    exact hp397.out
    exact hp10613.out
  a := [18584047965, -62989431208, 22300883259, 72627092948, -40328943323, -24090580656, 13883984558, 2469356642, -1381228240]
  b := [991634894, -10625958181, 21284850559, -4860532961, -14977085386, 6694496199, 3513248317, -1747854882, -274560229, 138122824]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 10613 T_ofList CD10613

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

end VoightMaximalOrderD10R571

namespace VoightMaximalOrderD10R572

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6226893453125, [-1, 11, -36, 28, 52, -81, 6, 30, -8, -3, 1], 1⟩
local notation "l" => [-1, 11, -36, 28, 52, -81, 6, 30, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, 36, -28, -52, 81, -6, -30, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, 36, -28, -52, 81, -6, -30, 8, 3], ![3, -32, 97, -48, -184, 191, 63, -96, -6, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, 36, -28, -52, 81, -6, -30, 8, 3], ![3, -32, 97, -48, -184, 191, 63, -96, -6, 17], ![17, -184, 580, -379, -932, 1193, 89, -447, 40, 45]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, 36, -28, -52, 81, -6, -30, 8, 3], ![3, -32, 97, -48, -184, 191, 63, -96, -6, 17], ![17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], ![45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, 36, -28, -52, 81, -6, -30, 8, 3], ![3, -32, 97, -48, -184, 191, 63, -96, -6, 17], ![17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], ![45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], ![175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, 36, -28, -52, 81, -6, -30, 8, 3], ![3, -32, 97, -48, -184, 191, 63, -96, -6, 17], ![17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], ![45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], ![175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438], ![438, -4643, 13888, -6442, -26240, 25698, 8828, -11477, -823, 1453]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, 36, -28, -52, 81, -6, -30, 8, 3], ![3, -32, 97, -48, -184, 191, 63, -96, -6, 17], ![17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], ![45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], ![175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438], ![438, -4643, 13888, -6442, -26240, 25698, 8828, -11477, -823, 1453], ![1453, -15545, 47665, -26796, -81998, 91453, 16980, -34762, 147, 3536]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, 36, -28, -52, 81, -6, -30, 8, 3], ![3, -32, 97, -48, -184, 191, 63, -96, -6, 17], ![17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], ![45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], ![175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438], ![438, -4643, 13888, -6442, -26240, 25698, 8828, -11477, -823, 1453], ![1453, -15545, 47665, -26796, -81998, 91453, 16980, -34762, 147, 3536], ![3536, -37443, 111751, -51343, -210668, 204418, 70237, -89100, -6474, 10755]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, 36, -28, -52, 81, -6, -30, 8, 3], ![3, -32, 97, -48, -184, 191, 63, -96, -6, 17], ![17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], ![45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], ![175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438], ![438, -4643, 13888, -6442, -26240, 25698, 8828, -11477, -823, 1453], ![1453, -15545, 47665, -26796, -81998, 91453, 16980, -34762, 147, 3536], ![3536, -37443, 111751, -51343, -210668, 204418, 70237, -89100, -6474, 10755], ![10755, -114769, 349737, -189389, -610603, 660487, 139888, -252413, -3060, 25791]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1], [-438, -175, -45, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1], [-438, -175, -45, -17, -3, -1], [-1453, -438, -175, -45, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1], [-438, -175, -45, -17, -3, -1], [-1453, -438, -175, -45, -17, -3, -1], [-3536, -1453, -438, -175, -45, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1], [-438, -175, -45, -17, -3, -1], [-1453, -438, -175, -45, -17, -3, -1], [-3536, -1453, -438, -175, -45, -17, -3, -1], [-10755, -3536, -1453, -438, -175, -45, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, 36, -28, -52, 81, -6, -30, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, 36, -28, -52, 81, -6, -30, 8, 3], [3, -32, 97, -48, -184, 191, 63, -96, -6, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, 36, -28, -52, 81, -6, -30, 8, 3], [3, -32, 97, -48, -184, 191, 63, -96, -6, 17], [17, -184, 580, -379, -932, 1193, 89, -447, 40, 45]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, 36, -28, -52, 81, -6, -30, 8, 3], [3, -32, 97, -48, -184, 191, 63, -96, -6, 17], [17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], [45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, 36, -28, -52, 81, -6, -30, 8, 3], [3, -32, 97, -48, -184, 191, 63, -96, -6, 17], [17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], [45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], [175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, 36, -28, -52, 81, -6, -30, 8, 3], [3, -32, 97, -48, -184, 191, 63, -96, -6, 17], [17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], [45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], [175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438], [438, -4643, 13888, -6442, -26240, 25698, 8828, -11477, -823, 1453]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, 36, -28, -52, 81, -6, -30, 8, 3], [3, -32, 97, -48, -184, 191, 63, -96, -6, 17], [17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], [45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], [175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438], [438, -4643, 13888, -6442, -26240, 25698, 8828, -11477, -823, 1453], [1453, -15545, 47665, -26796, -81998, 91453, 16980, -34762, 147, 3536]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, 36, -28, -52, 81, -6, -30, 8, 3], [3, -32, 97, -48, -184, 191, 63, -96, -6, 17], [17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], [45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], [175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438], [438, -4643, 13888, -6442, -26240, 25698, 8828, -11477, -823, 1453], [1453, -15545, 47665, -26796, -81998, 91453, 16980, -34762, 147, 3536], [3536, -37443, 111751, -51343, -210668, 204418, 70237, -89100, -6474, 10755]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, 36, -28, -52, 81, -6, -30, 8, 3], [3, -32, 97, -48, -184, 191, 63, -96, -6, 17], [17, -184, 580, -379, -932, 1193, 89, -447, 40, 45], [45, -478, 1436, -680, -2719, 2713, 923, -1261, -87, 175], [175, -1880, 5822, -3464, -9780, 11456, 1663, -4327, 139, 438], [438, -4643, 13888, -6442, -26240, 25698, 8828, -11477, -823, 1453], [1453, -15545, 47665, -26796, -81998, 91453, 16980, -34762, 147, 3536], [3536, -37443, 111751, -51343, -210668, 204418, 70237, -89100, -6474, 10755], [10755, -114769, 349737, -189389, -610603, 660487, 139888, -252413, -3060, 25791]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp199 : Fact (Nat.Prime 199) := fact_iff.2 (by norm_num)
instance hp105401 : Fact (Nat.Prime 105401) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [4, 2, 1]
  b' := [4, 3, 4, 1]
  k := [4, 4, 1, 1, 3, 0, 1]
  f := [1, 1, 8, -1, -7, 21, 1, -2, 5, 2]
  g := [4, 0, 4, 3, 1]
  h := [1, 4, 0, 1, 1, 4, 1]
  a := [3, 3, 3, 1]
  b := [2, 1, 3, 0, 3, 2, 4, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [6, 11, 8, 8, 16, 6, 17, 6]
  b' := [8, 15, 2, 9, 15, 4, 16, 15, 12]
  k := [2, 11, 1, 11, 13, 9, 1, 3, 1]
  f := [11, 6, 9, 4, 6, 9, 5, 8, 1, 1]
  g := [13, 7, 8, 6, 10, 5, 6, 11, 0, 1]
  h := [16, 1]
  a := [10, 18, 14, 3, 14, 11, 6, 8, 9]
  b := [15, 13, 2, 15, 0, 1, 13, 2, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD199 : CertificateDedekindCriterionLists l 199 where
  n := 2
  a' := [122, 108, 79, 9, 44, 47, 131, 192]
  b' := [53, 17, 56, 101, 145, 151, 31, 73, 45]
  k := [96, 18, 13, 168, 26, 91, 65, 153, 1]
  f := [45, 52, 121, 27, 79, 57, 119, 44, 46, 1]
  g := [74, 85, 198, 43, 130, 92, 195, 71, 75, 1]
  h := [121, 1]
  a := [194, 30, 47, 24, 86, 162, 56, 99, 193]
  b := [116, 8, 123, 186, 189, 49, 181, 125, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD105401 : CertificateDedekindCriterionLists l 105401 where
  n := 2
  a' := [52810, 72908, 83769, 7538, 33715, 52853, 54735, 97156]
  b' := [42609, 68389, 55699, 57031, 25323, 87475, 86749, 51459, 47761]
  k := [73859, 94097, 11813, 27117, 27695, 9970, 53437, 78564, 1]
  f := [11635, 10201, 8404, 12953, 9218, 5260, 4659, 3975, 11709, 1]
  g := [91402, 80130, 66014, 101751, 72407, 41316, 36597, 31224, 91981, 1]
  h := [13417, 1]
  a := [103780, 43802, 83829, 9742, 51488, 91850, 21679, 9596, 66949]
  b := [16911, 56369, 7373, 58179, 91259, 31480, 37856, 39745, 38452]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 19, 199, 105401]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 19, 199, 105401]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp199.out
    exact hp105401.out
  a := [1346861361259, -5601743339850, -2812297294482, 18657918718896, -5950835729747, -9335990482540, 3878664160961, 1189078161630, -525236195800]
  b := [122623087924, -1053486907561, 1922044701744, 1053893370986, -3854766032929, 909718216425, 1366622844055, -478775994435, -134664902037, 52523619580]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 199 T_ofList CD199
    exact satisfiesDedekindCriterion_of_certificate_lists T l 105401 T_ofList CD105401

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

end VoightMaximalOrderD10R572

namespace VoightMaximalOrderD10R575

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6240267015625, [5, -5, -35, 50, 34, -69, 2, 28, -7, -3, 1], 1⟩
local notation "l" => [5, -5, -35, 50, 34, -69, 2, 28, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 35, -50, -34, 69, -2, -28, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], ![-15, 10, 110, -115, -152, 173, 63, -86, -7, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], ![-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], ![-80, 65, 570, -690, -659, 952, 141, -385, 26, 41]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], ![-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], ![-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], ![-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], ![-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], ![-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], ![-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], ![-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], ![-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], ![-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], ![-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], ![-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349], ![-1745, 1000, 12755, -12110, -17816, 17535, 7499, -7900, -859, 1083]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], ![-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], ![-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], ![-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], ![-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349], ![-1745, 1000, 12755, -12110, -17816, 17535, 7499, -7900, -859, 1083], ![-5415, 3670, 38905, -41395, -48932, 56911, 15369, -22825, -319, 2390]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], ![-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], ![-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], ![-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], ![-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349], ![-1745, 1000, 12755, -12110, -17816, 17535, 7499, -7900, -859, 1083], ![-5415, 3670, 38905, -41395, -48932, 56911, 15369, -22825, -319, 2390], ![-11950, 6535, 87320, -80595, -122655, 115978, 52131, -51551, -6095, 6851]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], ![-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], ![-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], ![-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], ![-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349], ![-1745, 1000, 12755, -12110, -17816, 17535, 7499, -7900, -859, 1083], ![-5415, 3670, 38905, -41395, -48932, 56911, 15369, -22825, -319, 2390], ![-11950, 6535, 87320, -80595, -122655, 115978, 52131, -51551, -6095, 6851], ![-34255, 22305, 246320, -255230, -313529, 350064, 102276, -139697, -3594, 14458]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-41, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-41, -16, -3, -1], [-149, -41, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-41, -16, -3, -1], [-149, -41, -16, -3, -1], [-349, -149, -41, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-41, -16, -3, -1], [-149, -41, -16, -3, -1], [-349, -149, -41, -16, -3, -1], [-1083, -349, -149, -41, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-41, -16, -3, -1], [-149, -41, -16, -3, -1], [-349, -149, -41, -16, -3, -1], [-1083, -349, -149, -41, -16, -3, -1], [-2390, -1083, -349, -149, -41, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-41, -16, -3, -1], [-149, -41, -16, -3, -1], [-349, -149, -41, -16, -3, -1], [-1083, -349, -149, -41, -16, -3, -1], [-2390, -1083, -349, -149, -41, -16, -3, -1], [-6851, -2390, -1083, -349, -149, -41, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 35, -50, -34, 69, -2, -28, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], [-15, 10, 110, -115, -152, 173, 63, -86, -7, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], [-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], [-80, 65, 570, -690, -659, 952, 141, -385, 26, 41]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], [-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], [-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], [-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], [-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], [-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], [-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], [-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], [-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], [-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], [-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], [-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349], [-1745, 1000, 12755, -12110, -17816, 17535, 7499, -7900, -859, 1083]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], [-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], [-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], [-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], [-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349], [-1745, 1000, 12755, -12110, -17816, 17535, 7499, -7900, -859, 1083], [-5415, 3670, 38905, -41395, -48932, 56911, 15369, -22825, -319, 2390]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], [-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], [-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], [-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], [-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349], [-1745, 1000, 12755, -12110, -17816, 17535, 7499, -7900, -859, 1083], [-5415, 3670, 38905, -41395, -48932, 56911, 15369, -22825, -319, 2390], [-11950, 6535, 87320, -80595, -122655, 115978, 52131, -51551, -6095, 6851]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 35, -50, -34, 69, -2, -28, 7, 3], [-15, 10, 110, -115, -152, 173, 63, -86, -7, 16], [-80, 65, 570, -690, -659, 952, 141, -385, 26, 41], [-205, 125, 1500, -1480, -2084, 2170, 870, -1007, -98, 149], [-745, 540, 5340, -5950, -6546, 8197, 1872, -3302, 36, 349], [-1745, 1000, 12755, -12110, -17816, 17535, 7499, -7900, -859, 1083], [-5415, 3670, 38905, -41395, -48932, 56911, 15369, -22825, -319, 2390], [-11950, 6535, 87320, -80595, -122655, 115978, 52131, -51551, -6095, 6851], [-34255, 22305, 246320, -255230, -313529, 350064, 102276, -139697, -3594, 14458]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp359 : Fact (Nat.Prime 359) := fact_iff.2 (by norm_num)
instance hp1112471 : Fact (Nat.Prime 1112471) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [4, 1, 4]
  b' := [2, 3, 2, 4]
  k := [4, 1, 2, 3, 3, 2, 1]
  f := [-1, 1, 7, -10, -5, 15, 1, -4, 2, 1]
  g := [0, 3, 1, 1, 1]
  h := [0, 0, 0, 3, 1, 1, 1]
  a := [4, 1, 4, 4]
  b := [4, 2, 4, 1, 0, 2, 4, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD359 : CertificateDedekindCriterionLists l 359 where
  n := 2
  a' := [177, 332, 111, 147, 259, 246, 274, 113]
  b' := [252, 98, 91, 242, 212, 340, 196, 279, 147]
  k := [301, 22, 91, 212, 258, 8, 58, 163, 1]
  f := [113, 208, 7, 66, 260, 241, 170, 132, 62, 1]
  g := [147, 270, 8, 86, 338, 312, 220, 171, 80, 1]
  h := [276, 1]
  a := [36, 270, 285, 129, 233, 191, 151, 290, 266]
  b := [92, 144, 85, 318, 304, 26, 19, 190, 93]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1112471 : CertificateDedekindCriterionLists l 1112471 where
  n := 2
  a' := [829482, 377703, 167934, 637054, 77292, 275315, 418756, 241995]
  b' := [78619, 422315, 784188, 18550, 203318, 127955, 27528, 446457, 714759]
  k := [1072177, 6159, 400447, 365353, 738979, 933832, 102282, 839822, 1]
  f := [46913, 94348, 9571, 133667, 47567, 15290, 74922, 66324, 119618, 1]
  g := [382836, 769929, 78099, 1090796, 388165, 124772, 611404, 541236, 976145, 1]
  h := [136323, 1]
  a := [645698, 882167, 646842, 304550, 569003, 960926, 938198, 178455, 910063]
  b := [528362, 1055002, 233165, 251205, 586662, 467577, 807821, 497640, 202408]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 359, 1112471]
  exp := ![1, 1, 1]
  pdgood := [5, 359, 1112471]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp359.out
    exact hp1112471.out
  a := [-22010784431, -348085347062, 133267404771, 779205722874, -361685806800, -434669149834, 223902523440, 59174126570, -32101503100]
  b := [-22410161520, -12332301351, 135775616164, -17956156943, -168772937567, 56396692564, 65678715842, -27709460732, -6880457750, 3210150310]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 359 T_ofList CD359
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1112471 T_ofList CD1112471

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

end VoightMaximalOrderD10R575

namespace VoightMaximalOrderD10R576

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6243478862977, [4, -23, -26, 68, 29, -71, -4, 29, -4, -4, 1], 1⟩
local notation "l" => [4, -23, -26, 68, 29, -71, -4, 29, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-4, 23, 26, -68, -29, 71, 4, -29, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], ![-16, 88, 127, -246, -184, 255, 87, -112, -13, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], ![-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], ![-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], ![-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], ![-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], ![-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], ![-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], ![-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], ![-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], ![-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], ![-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], ![-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], ![-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], ![-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719], ![-2876, 15593, 23854, -41295, -34713, 40257, 16456, -15976, -2464, 2212]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], ![-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], ![-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], ![-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], ![-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719], ![-2876, 15593, 23854, -41295, -34713, 40257, 16456, -15976, -2464, 2212], ![-8848, 48000, 73105, -126562, -105443, 122339, 49105, -47692, -7128, 6384]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], ![-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], ![-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], ![-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], ![-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719], ![-2876, 15593, 23854, -41295, -34713, 40257, 16456, -15976, -2464, 2212], ![-8848, 48000, 73105, -126562, -105443, 122339, 49105, -47692, -7128, 6384], ![-25536, 137984, 213984, -361007, -311698, 347821, 147875, -136031, -22156, 18408]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], ![-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], ![-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], ![-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], ![-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719], ![-2876, 15593, 23854, -41295, -34713, 40257, 16456, -15976, -2464, 2212], ![-8848, 48000, 73105, -126562, -105443, 122339, 49105, -47692, -7128, 6384], ![-25536, 137984, 213984, -361007, -311698, 347821, 147875, -136031, -22156, 18408], ![-73632, 397848, 616592, -1037760, -894839, 995270, 421453, -385957, -62399, 51476]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-236, -67, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-236, -67, -20, -4, -1], [-719, -236, -67, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-236, -67, -20, -4, -1], [-719, -236, -67, -20, -4, -1], [-2212, -719, -236, -67, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-236, -67, -20, -4, -1], [-719, -236, -67, -20, -4, -1], [-2212, -719, -236, -67, -20, -4, -1], [-6384, -2212, -719, -236, -67, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-236, -67, -20, -4, -1], [-719, -236, -67, -20, -4, -1], [-2212, -719, -236, -67, -20, -4, -1], [-6384, -2212, -719, -236, -67, -20, -4, -1], [-18408, -6384, -2212, -719, -236, -67, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-4, 23, 26, -68, -29, 71, 4, -29, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], [-16, 88, 127, -246, -184, 255, 87, -112, -13, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], [-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], [-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], [-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], [-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], [-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], [-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], [-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], [-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], [-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], [-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], [-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], [-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], [-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719], [-2876, 15593, 23854, -41295, -34713, 40257, 16456, -15976, -2464, 2212]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], [-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], [-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], [-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], [-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719], [-2876, 15593, 23854, -41295, -34713, 40257, 16456, -15976, -2464, 2212], [-8848, 48000, 73105, -126562, -105443, 122339, 49105, -47692, -7128, 6384]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], [-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], [-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], [-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], [-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719], [-2876, 15593, 23854, -41295, -34713, 40257, 16456, -15976, -2464, 2212], [-8848, 48000, 73105, -126562, -105443, 122339, 49105, -47692, -7128, 6384], [-25536, 137984, 213984, -361007, -311698, 347821, 147875, -136031, -22156, 18408]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-4, 23, 26, -68, -29, 71, 4, -29, 4, 4], [-16, 88, 127, -246, -184, 255, 87, -112, -13, 20], [-80, 444, 608, -1233, -826, 1236, 335, -493, -32, 67], [-268, 1461, 2186, -3948, -3176, 3931, 1504, -1608, -225, 236], [-944, 5160, 7597, -13862, -10792, 13580, 4875, -5340, -664, 719], [-2876, 15593, 23854, -41295, -34713, 40257, 16456, -15976, -2464, 2212], [-8848, 48000, 73105, -126562, -105443, 122339, 49105, -47692, -7128, 6384], [-25536, 137984, 213984, -361007, -311698, 347821, 147875, -136031, -22156, 18408], [-73632, 397848, 616592, -1037760, -894839, 995270, 421453, -385957, -62399, 51476]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp4729 : Fact (Nat.Prime 4729) := fact_iff.2 (by norm_num)
instance hp72307 : Fact (Nat.Prime 72307) := fact_iff.2 (by norm_num)

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [12, 13, 7, 7, 12, 11, 4, 5]
  b' := [11, 14, 10, 0, 18, 17, 6, 1, 10]
  k := [6, 2, 18, 9, 0, 13, 5, 18, 1]
  f := [4, 3, 7, 3, 3, 8, 7, 6, 4, 1]
  g := [10, 3, 13, 14, 9, 9, 15, 16, 7, 1]
  h := [8, 1]
  a := [2, 10, 13, 9, 2, 17, 13, 8, 16]
  b := [5, 11, 11, 4, 13, 13, 6, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [27, 21, 14, 28, 9, 10]
  b' := [19, 7, 9, 24, 28, 22, 22]
  k := [8, 29, 12, 16, 15, 18, 1]
  f := [0, 5, 21, 12, 17, 18, 12, 5, 5, 1]
  g := [1, 28, 16, 23, 20, 16, 7, 7, 1]
  h := [4, 20, 1]
  a := [4, 29, 9, 28, 28, 13, 28, 7]
  b := [1, 14, 14, 23, 29, 25, 21, 17, 24]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4729 : CertificateDedekindCriterionLists l 4729 where
  n := 2
  a' := [1326, 804, 3432, 3358, 4478, 1322, 2382, 4005]
  b' := [1129, 1747, 2430, 866, 672, 4052, 2472, 3729, 4284]
  k := [3502, 3468, 1804, 1323, 450, 2737, 4376, 3445, 1]
  f := [604, 54, 562, 276, 116, 325, 516, 100, 553, 1]
  g := [4463, 392, 4152, 2033, 854, 2400, 3809, 733, 4085, 1]
  h := [640, 1]
  a := [1782, 1389, 2790, 395, 3376, 959, 4261, 2703, 3937]
  b := [3673, 3524, 1439, 1755, 2155, 159, 3649, 4250, 792]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD72307 : CertificateDedekindCriterionLists l 72307 where
  n := 2
  a' := [1772, 32924, 28409, 7269, 65744, 60647, 16599, 57790]
  b' := [28320, 24424, 58150, 15321, 51054, 57262, 30827, 21319, 1613]
  k := [27582, 55030, 48049, 45980, 38637, 54104, 58296, 21197, 1]
  f := [9371, 19417, 2107, 20690, 20308, 17073, 8121, 18907, 16522, 1]
  g := [26517, 54943, 5960, 58546, 57463, 48309, 22978, 53500, 46750, 1]
  h := [25553, 1]
  a := [68870, 22983, 30883, 66320, 23464, 61902, 38027, 21087, 56279]
  b := [28311, 65291, 28464, 10466, 26223, 1863, 3931, 13736, 16028]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![19, 31, 4729, 72307]
  exp := ![1, 1, 1, 1]
  pdgood := [19, 31, 4729, 72307]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp19.out
    exact hp31.out
    exact hp4729.out
    exact hp72307.out
  a := [-1589401952253, -4740935365812, 11226167418718, 15613662951690, -15629461705759, -11437694051632, 7678098591964, 2321965511462, -1218766083420]
  b := [-285174363173, 1409633492329, 2773657485162, -3056843260314, -4019667327964, 2613332301063, 1892525087637, -947934841424, -280947194483, 121876608342]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4729 T_ofList CD4729
    exact satisfiesDedekindCriterion_of_certificate_lists T l 72307 T_ofList CD72307

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

end VoightMaximalOrderD10R576

end TraceEuclidean
