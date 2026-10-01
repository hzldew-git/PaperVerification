import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk161
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

namespace VoightMaximalOrderD9R3

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨16240385609, [1, 7, -1, -25, -2, 26, 4, -9, -1, 1], 1⟩
local notation "l" => [1, 7, -1, -25, -2, 26, 4, -9, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsNine := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsNine_irreducible row row_mem
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
def basisNumerator : Fin 9 → Fin 9 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 9 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, 2, -26, -4, 9, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, 2, -26, -4, 9, 1], ![-1, -8, -6, 26, 27, -24, -30, 5, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, 2, -26, -4, 9, 1], ![-1, -8, -6, 26, 27, -24, -30, 5, 10], ![-10, -71, 2, 244, 46, -233, -64, 60, 15]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, 2, -26, -4, 9, 1], ![-1, -8, -6, 26, 27, -24, -30, 5, 10], ![-10, -71, 2, 244, 46, -233, -64, 60, 15], ![-15, -115, -56, 377, 274, -344, -293, 71, 75]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, 2, -26, -4, 9, 1], ![-1, -8, -6, 26, 27, -24, -30, 5, 10], ![-10, -71, 2, 244, 46, -233, -64, 60, 15], ![-15, -115, -56, 377, 274, -344, -293, 71, 75], ![-75, -540, -40, 1819, 527, -1676, -644, 382, 146]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, 2, -26, -4, 9, 1], ![-1, -8, -6, 26, 27, -24, -30, 5, 10], ![-10, -71, 2, 244, 46, -233, -64, 60, 15], ![-15, -115, -56, 377, 274, -344, -293, 71, 75], ![-75, -540, -40, 1819, 527, -1676, -644, 382, 146], ![-146, -1097, -394, 3610, 2111, -3269, -2260, 670, 528]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, 2, -26, -4, 9, 1], ![-1, -8, -6, 26, 27, -24, -30, 5, 10], ![-10, -71, 2, 244, 46, -233, -64, 60, 15], ![-15, -115, -56, 377, 274, -344, -293, 71, 75], ![-75, -540, -40, 1819, 527, -1676, -644, 382, 146], ![-146, -1097, -394, 3610, 2111, -3269, -2260, 670, 528], ![-528, -3842, -569, 12806, 4666, -11617, -5381, 2492, 1198]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, 2, -26, -4, 9, 1], ![-1, -8, -6, 26, 27, -24, -30, 5, 10], ![-10, -71, 2, 244, 46, -233, -64, 60, 15], ![-15, -115, -56, 377, 274, -344, -293, 71, 75], ![-75, -540, -40, 1819, 527, -1676, -644, 382, 146], ![-146, -1097, -394, 3610, 2111, -3269, -2260, 670, 528], ![-528, -3842, -569, 12806, 4666, -11617, -5381, 2492, 1198], ![-1198, -8914, -2644, 29381, 15202, -26482, -16409, 5401, 3690]]]
  s := ![![[], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-10, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-15, -10, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-15, -10, -1, -1], [-75, -15, -10, -1, -1]], ![[], [], [], [-1], [-1, -1], [-10, -1, -1], [-15, -10, -1, -1], [-75, -15, -10, -1, -1], [-146, -75, -15, -10, -1, -1]], ![[], [], [-1], [-1, -1], [-10, -1, -1], [-15, -10, -1, -1], [-75, -15, -10, -1, -1], [-146, -75, -15, -10, -1, -1], [-528, -146, -75, -15, -10, -1, -1]], ![[], [-1], [-1, -1], [-10, -1, -1], [-15, -10, -1, -1], [-75, -15, -10, -1, -1], [-146, -75, -15, -10, -1, -1], [-528, -146, -75, -15, -10, -1, -1], [-1198, -528, -146, -75, -15, -10, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 9 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 9) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 9) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 9) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 9 → Fin 9 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, 2, -26, -4, 9, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, 2, -26, -4, 9, 1], [-1, -8, -6, 26, 27, -24, -30, 5, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, 2, -26, -4, 9, 1], [-1, -8, -6, 26, 27, -24, -30, 5, 10], [-10, -71, 2, 244, 46, -233, -64, 60, 15]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, 2, -26, -4, 9, 1], [-1, -8, -6, 26, 27, -24, -30, 5, 10], [-10, -71, 2, 244, 46, -233, -64, 60, 15], [-15, -115, -56, 377, 274, -344, -293, 71, 75]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, 2, -26, -4, 9, 1], [-1, -8, -6, 26, 27, -24, -30, 5, 10], [-10, -71, 2, 244, 46, -233, -64, 60, 15], [-15, -115, -56, 377, 274, -344, -293, 71, 75], [-75, -540, -40, 1819, 527, -1676, -644, 382, 146]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, 2, -26, -4, 9, 1], [-1, -8, -6, 26, 27, -24, -30, 5, 10], [-10, -71, 2, 244, 46, -233, -64, 60, 15], [-15, -115, -56, 377, 274, -344, -293, 71, 75], [-75, -540, -40, 1819, 527, -1676, -644, 382, 146], [-146, -1097, -394, 3610, 2111, -3269, -2260, 670, 528]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, 2, -26, -4, 9, 1], [-1, -8, -6, 26, 27, -24, -30, 5, 10], [-10, -71, 2, 244, 46, -233, -64, 60, 15], [-15, -115, -56, 377, 274, -344, -293, 71, 75], [-75, -540, -40, 1819, 527, -1676, -644, 382, 146], [-146, -1097, -394, 3610, 2111, -3269, -2260, 670, 528], [-528, -3842, -569, 12806, 4666, -11617, -5381, 2492, 1198]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, 2, -26, -4, 9, 1], [-1, -8, -6, 26, 27, -24, -30, 5, 10], [-10, -71, 2, 244, 46, -233, -64, 60, 15], [-15, -115, -56, 377, 274, -344, -293, 71, 75], [-75, -540, -40, 1819, 527, -1676, -644, 382, 146], [-146, -1097, -394, 3610, 2111, -3269, -2260, 670, 528], [-528, -3842, -569, 12806, 4666, -11617, -5381, 2492, 1198], [-1198, -8914, -2644, 29381, 15202, -26482, -16409, 5401, 3690]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp138041 : Fact (Nat.Prime 138041) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 3
  a' := [1, 1]
  b' := [5, 1, 2]
  k := [1]
  f := [0, -1, 1, 4, 2, -2, 1, 3, 1]
  g := [1, 0, 2, 1]
  h := [1, 0, 4, 2, 4, 4, 1]
  a := [5, 0, 2]
  b := [1, 5, 0, 6, 4, 4, 5, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD138041 : CertificateDedekindCriterionLists l 138041 where
  n := 2
  a' := [126761, 83005, 128860, 118633, 117997, 94444, 130692]
  b' := [55748, 27445, 100645, 72772, 81947, 13335, 21416, 52684]
  k := [28853, 72308, 78848, 69091, 55361, 78484, 56198, 1]
  f := [8579, 10579, 12149, 39705, 31341, 11034, 39078, 28791, 1]
  g := [28940, 35686, 40982, 133938, 105721, 37219, 131823, 97119, 1]
  h := [40921, 1]
  a := [110653, 6112, 137817, 63537, 72999, 62783, 113284, 18347]
  b := [112327, 23652, 37203, 52199, 95308, 129172, 88252, 119694]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![7, 138041]
  exp := ![1, 1]
  pdgood := [7, 138041]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp138041.out
  a := [478842, 6737666, -9167662, -41862448, -7594272, 27159966, 4290113, -4550724]
  b := [69635, -1421470, -5019639, 1236050, 9491135, 1517164, -4026021, -532861, 505636]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 138041 T_ofList CD138041

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

noncomputable def bOm : Basis (Fin 9) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 9 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 9
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 9 := T_degree

noncomputable def bQ : Basis (Fin 9) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 9) :
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
          (∑ x : Fin 9,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 9,
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
        (List.ofFn fun i : Fin 9 =>
          (List.ofFn fun j : Fin 9 =>
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
      (voightPolynomialDiscriminantInput 9 row row_mem)
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

end VoightMaximalOrderD9R3

namespace VoightMaximalOrderD9R4

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨16440305941, [1, -2, -9, 11, 28, -18, -34, 8, 13, 1], 1⟩
local notation "l" => [1, -2, -9, 11, 28, -18, -34, 8, 13, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsNine := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsNine_irreducible row row_mem
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
def basisNumerator : Fin 9 → Fin 9 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 9 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 9, -11, -28, 18, 34, -8, -13]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 9, -11, -28, 18, 34, -8, -13], ![13, -27, -115, 152, 353, -262, -424, 138, 161]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 9, -11, -28, 18, 34, -8, -13], ![13, -27, -115, 152, 353, -262, -424, 138, 161], ![-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 9, -11, -28, 18, 34, -8, -13], ![13, -27, -115, 152, 353, -262, -424, 138, 161], ![-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], ![1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 9, -11, -28, 18, 34, -8, -13], ![13, -27, -115, 152, 353, -262, -424, 138, 161], ![-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], ![1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703], ![-23703, 49361, 209256, -277993, -640757, 479508, 766356, -252843, -287287]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 9, -11, -28, 18, 34, -8, -13], ![13, -27, -115, 152, 353, -262, -424, 138, 161], ![-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], ![1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703], ![-23703, 49361, 209256, -277993, -640757, 479508, 766356, -252843, -287287], ![287287, -598277, -2536222, 3369413, 7766043, -5811923, -9288250, 3064652, 3481888]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 9, -11, -28, 18, 34, -8, -13], ![13, -27, -115, 152, 353, -262, -424, 138, 161], ![-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], ![1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703], ![-23703, 49361, 209256, -277993, -640757, 479508, 766356, -252843, -287287], ![287287, -598277, -2536222, 3369413, 7766043, -5811923, -9288250, 3064652, 3481888], ![-3481888, 7251063, 30738715, -40836990, -94123451, 70440027, 112572269, -37143354, -42199892]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 9, -11, -28, 18, 34, -8, -13], ![13, -27, -115, 152, 353, -262, -424, 138, 161], ![-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], ![1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703], ![-23703, 49361, 209256, -277993, -640757, 479508, 766356, -252843, -287287], ![287287, -598277, -2536222, 3369413, 7766043, -5811923, -9288250, 3064652, 3481888], ![-3481888, 7251063, 30738715, -40836990, -94123451, 70440027, 112572269, -37143354, -42199892], ![42199892, -87881672, -372547965, 494937527, 1140759986, -853721507, -1364356301, 450171405, 511455242]]]
  s := ![![[], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [-1], [13, -1]], ![[], [], [], [], [], [], [-1], [13, -1], [-161, 13, -1]], ![[], [], [], [], [], [-1], [13, -1], [-161, 13, -1], [1955, -161, 13, -1]], ![[], [], [], [], [-1], [13, -1], [-161, 13, -1], [1955, -161, 13, -1], [-23703, 1955, -161, 13, -1]], ![[], [], [], [-1], [13, -1], [-161, 13, -1], [1955, -161, 13, -1], [-23703, 1955, -161, 13, -1], [287287, -23703, 1955, -161, 13, -1]], ![[], [], [-1], [13, -1], [-161, 13, -1], [1955, -161, 13, -1], [-23703, 1955, -161, 13, -1], [287287, -23703, 1955, -161, 13, -1], [-3481888, 287287, -23703, 1955, -161, 13, -1]], ![[], [-1], [13, -1], [-161, 13, -1], [1955, -161, 13, -1], [-23703, 1955, -161, 13, -1], [287287, -23703, 1955, -161, 13, -1], [-3481888, 287287, -23703, 1955, -161, 13, -1], [42199892, -3481888, 287287, -23703, 1955, -161, 13, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 9 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 9) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 9) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 9) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 9 → Fin 9 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 9, -11, -28, 18, 34, -8, -13]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 9, -11, -28, 18, 34, -8, -13], [13, -27, -115, 152, 353, -262, -424, 138, 161]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 9, -11, -28, 18, 34, -8, -13], [13, -27, -115, 152, 353, -262, -424, 138, 161], [-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 9, -11, -28, 18, 34, -8, -13], [13, -27, -115, 152, 353, -262, -424, 138, 161], [-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], [1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 9, -11, -28, 18, 34, -8, -13], [13, -27, -115, 152, 353, -262, -424, 138, 161], [-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], [1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703], [-23703, 49361, 209256, -277993, -640757, 479508, 766356, -252843, -287287]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 9, -11, -28, 18, 34, -8, -13], [13, -27, -115, 152, 353, -262, -424, 138, 161], [-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], [1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703], [-23703, 49361, 209256, -277993, -640757, 479508, 766356, -252843, -287287], [287287, -598277, -2536222, 3369413, 7766043, -5811923, -9288250, 3064652, 3481888]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 9, -11, -28, 18, 34, -8, -13], [13, -27, -115, 152, 353, -262, -424, 138, 161], [-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], [1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703], [-23703, 49361, 209256, -277993, -640757, 479508, 766356, -252843, -287287], [287287, -598277, -2536222, 3369413, 7766043, -5811923, -9288250, 3064652, 3481888], [-3481888, 7251063, 30738715, -40836990, -94123451, 70440027, 112572269, -37143354, -42199892]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 9, -11, -28, 18, 34, -8, -13], [13, -27, -115, 152, 353, -262, -424, 138, 161], [-161, 335, 1422, -1886, -4356, 3251, 5212, -1712, -1955], [1955, -4071, -17260, 22927, 52854, -39546, -63219, 20852, 23703], [-23703, 49361, 209256, -277993, -640757, 479508, 766356, -252843, -287287], [287287, -598277, -2536222, 3369413, 7766043, -5811923, -9288250, 3064652, 3481888], [-3481888, 7251063, 30738715, -40836990, -94123451, 70440027, 112572269, -37143354, -42199892], [42199892, -87881672, -372547965, 494937527, 1140759986, -853721507, -1364356301, 450171405, 511455242]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp37 : Fact (Nat.Prime 37) := fact_iff.2 (by norm_num)
instance hp229 : Fact (Nat.Prime 229) := fact_iff.2 (by norm_num)

def CD37 : CertificateDedekindCriterionLists l 37 where
  n := 3
  a' := [18, 14, 1, 20, 15, 20]
  b' := [27, 14, 36, 24, 26, 29, 13]
  k := [26, 12, 27, 35, 0, 36, 16, 5, 7, 16, 34, 6, 1]
  f := [3, 13, 19, 20, 14, 5, 9, 16, 1]
  g := [16, 25, 29, 25, 6, 4, 31, 1]
  h := [7, 19, 1]
  a := [33, 33, 5, 35, 5, 26, 36]
  b := [17, 26, 5, 24, 23, 4, 33, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD229 : CertificateDedekindCriterionLists l 229 where
  n := 2
  a' := [149, 70, 35, 97, 152]
  b' := [120, 116, 220, 29, 106, 51]
  k := [129, 28, 128, 1]
  f := [39, 128, 173, 122, 70, 107, 121, 47, 1]
  g := [154, 200, 135, 15, 111, 185, 1]
  h := [58, 115, 57, 1]
  a := [16, 10, 68, 57, 69, 215]
  b := [48, 17, 160, 109, 40, 167, 60, 14]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![37, 229]
  exp := ![1, 1]
  pdgood := [37, 229]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp37.out
    exact hp229.out
  a := [67164259, 499527310, -1888548468, -814461898, 4296584194, 148974444, -2115438642, -193809672]
  b := [33577893, -119601641, -115590706, 550099334, 82084196, -733200526, 1807006, 266153994, 21534408]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 37 T_ofList CD37
    exact satisfiesDedekindCriterion_of_certificate_lists T l 229 T_ofList CD229

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

noncomputable def bOm : Basis (Fin 9) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 9 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 9
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 9 := T_degree

noncomputable def bQ : Basis (Fin 9) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 9) :
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
          (∑ x : Fin 9,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 9,
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
        (List.ofFn fun i : Fin 9 =>
          (List.ofFn fun j : Fin 9 =>
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
      (voightPolynomialDiscriminantInput 9 row row_mem)
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

end VoightMaximalOrderD9R4

namespace VoightMaximalOrderD9R6

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨16983563041, [-1, 1, 8, -7, -21, 15, 20, -10, -5, 1], 1⟩
local notation "l" => [-1, 1, 8, -7, -21, 15, 20, -10, -5, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsNine := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsNine_irreducible row row_mem
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
def basisNumerator : Fin 9 → Fin 9 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 9 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -8, 7, 21, -15, -20, 10, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -8, 7, 21, -15, -20, 10, 5], ![5, -4, -41, 27, 112, -54, -115, 30, 35]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -8, 7, 21, -15, -20, 10, 5], ![5, -4, -41, 27, 112, -54, -115, 30, 35], ![35, -30, -284, 204, 762, -413, -754, 235, 205]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -8, 7, 21, -15, -20, 10, 5], ![5, -4, -41, 27, 112, -54, -115, 30, 35], ![35, -30, -284, 204, 762, -413, -754, 235, 205], ![205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -8, 7, 21, -15, -20, 10, 5], ![5, -4, -41, 27, 112, -54, -115, 30, 35], ![35, -30, -284, 204, 762, -413, -754, 235, 205], ![205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260], ![1260, -1055, -10250, 7150, 27611, -14391, -27513, 8087, 7596]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -8, 7, 21, -15, -20, 10, 5], ![5, -4, -41, 27, 112, -54, -115, 30, 35], ![35, -30, -284, 204, 762, -413, -754, 235, 205], ![205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260], ![1260, -1055, -10250, 7150, 27611, -14391, -27513, 8087, 7596], ![7596, -6336, -61823, 42922, 166666, -86329, -166311, 48447, 46067]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -8, 7, 21, -15, -20, 10, 5], ![5, -4, -41, 27, 112, -54, -115, 30, 35], ![35, -30, -284, 204, 762, -413, -754, 235, 205], ![205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260], ![1260, -1055, -10250, 7150, 27611, -14391, -27513, 8087, 7596], ![7596, -6336, -61823, 42922, 166666, -86329, -166311, 48447, 46067], ![46067, -38471, -374872, 260646, 1010329, -524339, -1007669, 294359, 278782]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -8, 7, 21, -15, -20, 10, 5], ![5, -4, -41, 27, 112, -54, -115, 30, 35], ![35, -30, -284, 204, 762, -413, -754, 235, 205], ![205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260], ![1260, -1055, -10250, 7150, 27611, -14391, -27513, 8087, 7596], ![7596, -6336, -61823, 42922, 166666, -86329, -166311, 48447, 46067], ![46067, -38471, -374872, 260646, 1010329, -524339, -1007669, 294359, 278782], ![278782, -232715, -2268727, 1576602, 6115068, -3171401, -6099979, 1780151, 1688269]]]
  s := ![![[], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-35, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-35, -5, -1], [-205, -35, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-35, -5, -1], [-205, -35, -5, -1], [-1260, -205, -35, -5, -1]], ![[], [], [], [-1], [-5, -1], [-35, -5, -1], [-205, -35, -5, -1], [-1260, -205, -35, -5, -1], [-7596, -1260, -205, -35, -5, -1]], ![[], [], [-1], [-5, -1], [-35, -5, -1], [-205, -35, -5, -1], [-1260, -205, -35, -5, -1], [-7596, -1260, -205, -35, -5, -1], [-46067, -7596, -1260, -205, -35, -5, -1]], ![[], [-1], [-5, -1], [-35, -5, -1], [-205, -35, -5, -1], [-1260, -205, -35, -5, -1], [-7596, -1260, -205, -35, -5, -1], [-46067, -7596, -1260, -205, -35, -5, -1], [-278782, -46067, -7596, -1260, -205, -35, -5, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 9 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 9) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 9) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 9) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 9 → Fin 9 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -8, 7, 21, -15, -20, 10, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -8, 7, 21, -15, -20, 10, 5], [5, -4, -41, 27, 112, -54, -115, 30, 35]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -8, 7, 21, -15, -20, 10, 5], [5, -4, -41, 27, 112, -54, -115, 30, 35], [35, -30, -284, 204, 762, -413, -754, 235, 205]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -8, 7, 21, -15, -20, 10, 5], [5, -4, -41, 27, 112, -54, -115, 30, 35], [35, -30, -284, 204, 762, -413, -754, 235, 205], [205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -8, 7, 21, -15, -20, 10, 5], [5, -4, -41, 27, 112, -54, -115, 30, 35], [35, -30, -284, 204, 762, -413, -754, 235, 205], [205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260], [1260, -1055, -10250, 7150, 27611, -14391, -27513, 8087, 7596]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -8, 7, 21, -15, -20, 10, 5], [5, -4, -41, 27, 112, -54, -115, 30, 35], [35, -30, -284, 204, 762, -413, -754, 235, 205], [205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260], [1260, -1055, -10250, 7150, 27611, -14391, -27513, 8087, 7596], [7596, -6336, -61823, 42922, 166666, -86329, -166311, 48447, 46067]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -8, 7, 21, -15, -20, 10, 5], [5, -4, -41, 27, 112, -54, -115, 30, 35], [35, -30, -284, 204, 762, -413, -754, 235, 205], [205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260], [1260, -1055, -10250, 7150, 27611, -14391, -27513, 8087, 7596], [7596, -6336, -61823, 42922, 166666, -86329, -166311, 48447, 46067], [46067, -38471, -374872, 260646, 1010329, -524339, -1007669, 294359, 278782]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -8, 7, 21, -15, -20, 10, 5], [5, -4, -41, 27, 112, -54, -115, 30, 35], [35, -30, -284, 204, 762, -413, -754, 235, 205], [205, -170, -1670, 1151, 4509, -2313, -4513, 1296, 1260], [1260, -1055, -10250, 7150, 27611, -14391, -27513, 8087, 7596], [7596, -6336, -61823, 42922, 166666, -86329, -166311, 48447, 46067], [46067, -38471, -374872, 260646, 1010329, -524339, -1007669, 294359, 278782], [278782, -232715, -2268727, 1576602, 6115068, -3171401, -6099979, 1780151, 1688269]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 9
  a' := []
  b' := [1]
  k := [1]
  f := [9, 4, 2, 9, 3, 3, 3, 3, 1]
  g := [10, 1]
  h := [17, 6, 4, 16, 2, 7, 7, 4, 1]
  a := [18]
  b := [1, 6, 11, 15, 14, 16, 12, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 1
  p := ![19]
  exp := ![1]
  pdgood := [19]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp19.out
  a := [1411, 25722, 20439, -92826, -63558, 74844, 30459, -7722]
  b := [1430, 1431, -9437, -8001, 18234, 11682, -10461, -3861, 858]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19

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

noncomputable def bOm : Basis (Fin 9) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 9 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 9
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 9 := T_degree

noncomputable def bQ : Basis (Fin 9) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 9) :
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
          (∑ x : Fin 9,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 9,
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
        (List.ofFn fun i : Fin 9 =>
          (List.ofFn fun j : Fin 9 =>
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
      (voightPolynomialDiscriminantInput 9 row row_mem)
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

end VoightMaximalOrderD9R6

namespace VoightMaximalOrderD9R7

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨17515230173, [1, -5, -2, 34, -24, -26, 29, -3, -4, 1], 1⟩
local notation "l" => [1, -5, -2, 34, -24, -26, 29, -3, -4, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsNine := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsNine_irreducible row row_mem
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
def basisNumerator : Fin 9 → Fin 9 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 9 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -34, 24, 26, -29, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -34, 24, 26, -29, 3, 4], ![-4, 19, 13, -134, 62, 128, -90, -17, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -34, 24, 26, -29, 3, 4], ![-4, 19, 13, -134, 62, 128, -90, -17, 19], ![-19, 91, 57, -633, 322, 556, -423, -33, 59]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -34, 24, 26, -29, 3, 4], ![-4, 19, 13, -134, 62, 128, -90, -17, 19], ![-19, 91, 57, -633, 322, 556, -423, -33, 59], ![-59, 276, 209, -1949, 783, 1856, -1155, -246, 203]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -34, 24, 26, -29, 3, 4], ![-4, 19, 13, -134, 62, 128, -90, -17, 19], ![-19, 91, 57, -633, 322, 556, -423, -33, 59], ![-59, 276, 209, -1949, 783, 1856, -1155, -246, 203], ![-203, 956, 682, -6693, 2923, 6061, -4031, -546, 566]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -34, 24, 26, -29, 3, 4], ![-4, 19, 13, -134, 62, 128, -90, -17, 19], ![-19, 91, 57, -633, 322, 556, -423, -33, 59], ![-59, 276, 209, -1949, 783, 1856, -1155, -246, 203], ![-203, 956, 682, -6693, 2923, 6061, -4031, -546, 566], ![-566, 2627, 2088, -18562, 6891, 17639, -10353, -2333, 1718]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -34, 24, 26, -29, 3, 4], ![-4, 19, 13, -134, 62, 128, -90, -17, 19], ![-19, 91, 57, -633, 322, 556, -423, -33, 59], ![-59, 276, 209, -1949, 783, 1856, -1155, -246, 203], ![-203, 956, 682, -6693, 2923, 6061, -4031, -546, 566], ![-566, 2627, 2088, -18562, 6891, 17639, -10353, -2333, 1718], ![-1718, 8024, 6063, -56324, 22670, 51559, -32183, -5199, 4539]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 2, -34, 24, 26, -29, 3, 4], ![-4, 19, 13, -134, 62, 128, -90, -17, 19], ![-19, 91, 57, -633, 322, 556, -423, -33, 59], ![-59, 276, 209, -1949, 783, 1856, -1155, -246, 203], ![-203, 956, 682, -6693, 2923, 6061, -4031, -546, 566], ![-566, 2627, 2088, -18562, 6891, 17639, -10353, -2333, 1718], ![-1718, 8024, 6063, -56324, 22670, 51559, -32183, -5199, 4539], ![-4539, 20977, 17102, -148263, 52612, 140684, -80072, -18566, 12957]]]
  s := ![![[], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-59, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-59, -19, -4, -1], [-203, -59, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-59, -19, -4, -1], [-203, -59, -19, -4, -1], [-566, -203, -59, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-59, -19, -4, -1], [-203, -59, -19, -4, -1], [-566, -203, -59, -19, -4, -1], [-1718, -566, -203, -59, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-59, -19, -4, -1], [-203, -59, -19, -4, -1], [-566, -203, -59, -19, -4, -1], [-1718, -566, -203, -59, -19, -4, -1], [-4539, -1718, -566, -203, -59, -19, -4, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 9 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 9) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 9) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 9) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 9 → Fin 9 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -34, 24, 26, -29, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -34, 24, 26, -29, 3, 4], [-4, 19, 13, -134, 62, 128, -90, -17, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -34, 24, 26, -29, 3, 4], [-4, 19, 13, -134, 62, 128, -90, -17, 19], [-19, 91, 57, -633, 322, 556, -423, -33, 59]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -34, 24, 26, -29, 3, 4], [-4, 19, 13, -134, 62, 128, -90, -17, 19], [-19, 91, 57, -633, 322, 556, -423, -33, 59], [-59, 276, 209, -1949, 783, 1856, -1155, -246, 203]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -34, 24, 26, -29, 3, 4], [-4, 19, 13, -134, 62, 128, -90, -17, 19], [-19, 91, 57, -633, 322, 556, -423, -33, 59], [-59, 276, 209, -1949, 783, 1856, -1155, -246, 203], [-203, 956, 682, -6693, 2923, 6061, -4031, -546, 566]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -34, 24, 26, -29, 3, 4], [-4, 19, 13, -134, 62, 128, -90, -17, 19], [-19, 91, 57, -633, 322, 556, -423, -33, 59], [-59, 276, 209, -1949, 783, 1856, -1155, -246, 203], [-203, 956, 682, -6693, 2923, 6061, -4031, -546, 566], [-566, 2627, 2088, -18562, 6891, 17639, -10353, -2333, 1718]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -34, 24, 26, -29, 3, 4], [-4, 19, 13, -134, 62, 128, -90, -17, 19], [-19, 91, 57, -633, 322, 556, -423, -33, 59], [-59, 276, 209, -1949, 783, 1856, -1155, -246, 203], [-203, 956, 682, -6693, 2923, 6061, -4031, -546, 566], [-566, 2627, 2088, -18562, 6891, 17639, -10353, -2333, 1718], [-1718, 8024, 6063, -56324, 22670, 51559, -32183, -5199, 4539]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 2, -34, 24, 26, -29, 3, 4], [-4, 19, 13, -134, 62, 128, -90, -17, 19], [-19, 91, 57, -633, 322, 556, -423, -33, 59], [-59, 276, 209, -1949, 783, 1856, -1155, -246, 203], [-203, 956, 682, -6693, 2923, 6061, -4031, -546, 566], [-566, 2627, 2088, -18562, 6891, 17639, -10353, -2333, 1718], [-1718, 8024, 6063, -56324, 22670, 51559, -32183, -5199, 4539], [-4539, 20977, 17102, -148263, 52612, 140684, -80072, -18566, 12957]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp53 : Fact (Nat.Prime 53) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 3
  a' := [3]
  b' := [2, 6]
  k := [1]
  f := [1, 5, 7, 2, 10, 9, -1, 2, 1]
  g := [4, 5, 1, 1]
  h := [2, 5, 5, 4, 4, 2, 1]
  a := [4, 0, 6]
  b := [1, 6, 3, 6, 3, 3, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD53 : CertificateDedekindCriterionLists l 53 where
  n := 2
  a' := [12, 24, 9, 42, 25]
  b' := [7, 2, 6, 37, 7, 40]
  k := [11, 12, 40, 1]
  f := [3, 21, 29, 42, 20, 22, 8, 11, 1]
  g := [8, 47, 15, 24, 1, 18, 1]
  h := [20, 21, 31, 1]
  a := [47, 45, 25, 40, 51, 43]
  b := [9, 52, 29, 3, 4, 4, 38, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![7, 53]
  exp := ![1, 1]
  pdgood := [7, 53]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp53.out
  a := [-315019, -1264882, 2366588, 1543442, -3234225, 592708, 573647, -176994]
  b := [-63078, 112505, 487412, -577806, -340647, 544441, -81716, -72479, 19666]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 53 T_ofList CD53

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

noncomputable def bOm : Basis (Fin 9) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 9 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 9
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 9 := T_degree

noncomputable def bQ : Basis (Fin 9) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 9) :
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
          (∑ x : Fin 9,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 9,
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
        (List.ofFn fun i : Fin 9 =>
          (List.ofFn fun j : Fin 9 =>
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
      (voightPolynomialDiscriminantInput 9 row row_mem)
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

end VoightMaximalOrderD9R7

end TraceEuclidean
