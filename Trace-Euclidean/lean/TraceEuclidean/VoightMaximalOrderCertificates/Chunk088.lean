import TraceEuclidean.VoightMaximalOrderCertificates.Chunk084
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

namespace VoightMaximalOrderD7R49

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨83266101, [-4, -10, 5, 18, -1, -8, 0, 1], 2⟩
local notation "l" => [-4, -10, 5, 18, -1, -8, 0, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![2, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 2, 0], ![0, 1, 0, 1, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, 0, 2], ![2, 5, -2, -9, 1, 4, 0]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, 0, 2], ![4, 10, -5, -18, 1, 8, 0], ![0, -2, 5, -6, -9, 1, 8]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, 0, 2], ![4, 10, -5, -18, 1, 8, 0], ![0, -4, 10, -13, -18, 1, 16], ![16, 39, -18, -68, 2, 23, 2]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, 0, 2], ![4, 10, -5, -18, 1, 8, 0], ![0, -4, 10, -13, -18, 1, 16], ![32, 79, -36, -135, 3, 46, 2], ![4, 3, 35, -59, -66, 10, 46]], ![![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, 0, 2], ![4, 10, -5, -18, 1, 8, 0], ![0, -4, 10, -13, -18, 1, 16], ![32, 79, -36, -135, 3, 46, 2], ![4, -4, 75, -100, -133, 11, 92], ![92, 224, -89, -389, -13, 118, 20]], ![![0, 0, 0, 0, 0, 0, 1], ![2, 5, -2, -9, 1, 4, 0], ![0, -2, 5, -6, -9, 1, 8], ![16, 39, -18, -68, 2, 23, 2], ![4, 3, 35, -59, -66, 10, 46], ![92, 224, -89, -389, -13, 118, 20], ![29, 59, 82, -232, -183, 47, 119]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-2]], ![[], [], [], [], [], [-4], [0, -2]], ![[], [], [], [], [-4], [0, -4], [-16, 0, -2]], ![[], [], [], [-4], [0, -4], [-32, 0, -4], [-4, -16, 0, -2]], ![[], [], [-4], [0, -4], [-32, 0, -4], [-4, -32, 0, -4], [-92, -4, -16, 0, -2]], ![[], [-2], [0, -2], [-16, 0, -2], [-4, -16, 0, -2], [-92, -4, -16, 0, -2], [-29, -46, -3, -8, 0, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, 0, 2], [2, 5, -2, -9, 1, 4, 0]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, 0, 2], [4, 10, -5, -18, 1, 8, 0], [0, -2, 5, -6, -9, 1, 8]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, 0, 2], [4, 10, -5, -18, 1, 8, 0], [0, -4, 10, -13, -18, 1, 16], [16, 39, -18, -68, 2, 23, 2]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, 0, 2], [4, 10, -5, -18, 1, 8, 0], [0, -4, 10, -13, -18, 1, 16], [32, 79, -36, -135, 3, 46, 2], [4, 3, 35, -59, -66, 10, 46]], ![[0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, 0, 2], [4, 10, -5, -18, 1, 8, 0], [0, -4, 10, -13, -18, 1, 16], [32, 79, -36, -135, 3, 46, 2], [4, -4, 75, -100, -133, 11, 92], [92, 224, -89, -389, -13, 118, 20]], ![[0, 0, 0, 0, 0, 0, 1], [2, 5, -2, -9, 1, 4, 0], [0, -2, 5, -6, -9, 1, 8], [16, 39, -18, -68, 2, 23, 2], [4, 3, 35, -59, -66, 10, 46], [92, 224, -89, -389, -13, 118, 20], [29, 59, 82, -232, -183, 47, 119]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp359 : Fact (Nat.Prime 359) := fact_iff.2 (by norm_num)
instance hp25771 : Fact (Nat.Prime 25771) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [2, 0, 0, 1]
  b' := [1, 0, 2, 1, 1]
  k := [2, 0, 1, 1]
  f := [2, 5, 0, -5, 2, 4, 1]
  g := [1, 2, 1, 0, 2, 1]
  h := [2, 1, 1]
  a := [0, 0, 0, 2, 1]
  b := [1, 1, 0, 1, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD359 : CertificateDedekindCriterionLists l 359 where
  n := 2
  a' := [169, 145, 161, 112, 10]
  b' := [174, 131, 130, 82, 297, 118]
  k := [189, 254, 339, 123, 312, 1]
  f := [177, 32, 81, 101, 156, 89, 1]
  g := [313, 55, 143, 178, 275, 156, 1]
  h := [203, 1]
  a := [75, 269, 341, 16, 28, 46]
  b := [351, 227, 356, 63, 182, 313]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD25771 : CertificateDedekindCriterionLists l 25771 where
  n := 2
  a' := [25099, 15179, 5575, 9631, 16514]
  b' := [11619, 4071, 20897, 15648, 9514, 5838]
  k := [13908, 16077, 16692, 10376, 1974, 1]
  f := [8412, 20047, 8408, 6412, 19844, 950, 1]
  g := [8747, 20845, 8742, 6667, 20634, 987, 1]
  h := [24784, 1]
  a := [8477, 3747, 22382, 11957, 24084, 8046]
  b := [23467, 16344, 15310, 2908, 15908, 17725]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 3, 359, 25771]
  exp := ![1, 1, 1, 1]
  pdgood := [3, 359, 25771]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp359.out
    exact hp25771.out
  a := [86098074, -248441930, -120194958, 239874436, 28712453, -47077373]
  b := [-39990303, -26711605, 96909709, 23663915, -49639980, -4101779, 6725339]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 359 T_ofList CD359
    exact satisfiesDedekindCriterion_of_certificate_lists T l 25771 T_ofList CD25771

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 7
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 0, 1, 0]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]], ![[0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0], [0, 0, 1, 1, 1, 0, 0]], ![[0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0], [1, 1, 0, 0, 1, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 1, 0], ![0, 1, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0], ![0, 0, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R49

namespace VoightMaximalOrderD7R72

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨100069857, [-1, -5, 2, 17, 4, -8, -1, 1], 3⟩
local notation "l" => [-1, -5, 2, 17, 4, -8, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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

def basisDenominator : ℤ := 3
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![3, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 0], ![0, 0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 3, 0], ![1, 0, 1, 2, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![-1, 0, -1, -2, -1, 0, 3], ![0, 2, -1, -6, -1, 3, 1]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![-1, 0, -1, -2, -1, 0, 3], ![0, 5, -3, -19, -5, 8, 3], ![-3, 2, -2, -13, -10, 2, 10]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![-1, 0, -1, -2, -1, 0, 3], ![0, 5, -3, -19, -5, 8, 3], ![-8, 6, -6, -37, -30, 4, 27], ![-2, 17, -10, -66, -25, 20, 16]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![-1, 0, -1, -2, -1, 0, 3], ![0, 5, -3, -19, -5, 8, 3], ![-8, 6, -6, -37, -30, 4, 27], ![-4, 46, -25, -176, -68, 51, 39], ![-20, 30, -19, -146, -102, 23, 76]], ![![0, 0, 0, 0, 0, 1, 0], ![-1, 0, -1, -2, -1, 0, 3], ![0, 5, -3, -19, -5, 8, 3], ![-8, 6, -6, -37, -30, 4, 27], ![-4, 46, -25, -176, -68, 51, 39], ![-51, 74, -44, -361, -266, 49, 192], ![-23, 132, -69, -521, -245, 126, 145]], ![![0, 0, 0, 0, 0, 0, 1], ![0, 2, -1, -6, -1, 3, 1], ![-3, 2, -2, -13, -10, 2, 10], ![-2, 17, -10, -66, -25, 20, 16], ![-20, 30, -19, -146, -102, 23, 76], ![-23, 132, -69, -521, -245, 126, 145], ![-51, 111, -60, -494, -318, 85, 214]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-3]], ![[], [], [], [], [], [-9], [-3, -3]], ![[], [], [], [], [-9], [-9, -9], [-30, -3, -3]], ![[], [], [], [-9], [-9, -9], [-81, -9, -9], [-48, -30, -3, -3]], ![[], [], [-9], [-9, -9], [-81, -9, -9], [-117, -81, -9, -9], [-228, -48, -30, -3, -3]], ![[], [-3], [-3, -3], [-30, -3, -3], [-48, -30, -3, -3], [-228, -48, -30, -3, -3], [-182, -89, -19, -11, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, 0, -1, -2, -1, 0, 3], [0, 2, -1, -6, -1, 3, 1]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, 0, -1, -2, -1, 0, 3], [0, 5, -3, -19, -5, 8, 3], [-3, 2, -2, -13, -10, 2, 10]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, 0, -1, -2, -1, 0, 3], [0, 5, -3, -19, -5, 8, 3], [-8, 6, -6, -37, -30, 4, 27], [-2, 17, -10, -66, -25, 20, 16]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, 0, -1, -2, -1, 0, 3], [0, 5, -3, -19, -5, 8, 3], [-8, 6, -6, -37, -30, 4, 27], [-4, 46, -25, -176, -68, 51, 39], [-20, 30, -19, -146, -102, 23, 76]], ![[0, 0, 0, 0, 0, 1, 0], [-1, 0, -1, -2, -1, 0, 3], [0, 5, -3, -19, -5, 8, 3], [-8, 6, -6, -37, -30, 4, 27], [-4, 46, -25, -176, -68, 51, 39], [-51, 74, -44, -361, -266, 49, 192], [-23, 132, -69, -521, -245, 126, 145]], ![[0, 0, 0, 0, 0, 0, 1], [0, 2, -1, -6, -1, 3, 1], [-3, 2, -2, -13, -10, 2, 10], [-2, 17, -10, -66, -25, 20, 16], [-20, 30, -19, -146, -102, 23, 76], [-23, 132, -69, -521, -245, 126, 145], [-51, 111, -60, -494, -318, 85, 214]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp383 : Fact (Nat.Prime 383) := fact_iff.2 (by norm_num)
instance hp9677 : Fact (Nat.Prime 9677) := fact_iff.2 (by norm_num)

def CD383 : CertificateDedekindCriterionLists l 383 where
  n := 2
  a' := [12, 244, 74, 301, 370]
  b' := [35, 105, 66, 305, 241, 66]
  k := [95, 307, 237, 208, 170, 1]
  f := [31, 23, 42, 20, 63, 77, 1]
  g := [112, 82, 151, 71, 227, 276, 1]
  h := [106, 1]
  a := [366, 44, 98, 274, 328, 222]
  b := [333, 216, 283, 354, 188, 161]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9677 : CertificateDedekindCriterionLists l 9677 where
  n := 2
  a' := [6148, 776, 6083, 829, 7034]
  b' := [5120, 5050, 9588, 8694, 7624, 5279]
  k := [9586, 5428, 4754, 7280, 6748, 1]
  f := [341, 255, 1138, 1256, 929, 1243, 1]
  g := [2254, 1684, 7521, 8297, 6135, 8212, 1]
  h := [1464, 1]
  a := [961, 5019, 5918, 7579, 8897, 893]
  b := [5848, 1280, 7665, 1959, 1786, 8784]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![3, 383, 9677]
  exp := ![3, 1, 1]
  pdgood := [383, 9677]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp383.out
    exact hp9677.out
  a := [127846213, -572393176, -507286834, 588988680, 151865081, -117421906]
  b := [-45583214, -49834149, 220172926, 117172688, -121437827, -24091377, 16774558]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 383 T_ofList CD383
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9677 T_ofList CD9677

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 2
  n := 5
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [2, 0, 2, 1, 2, 0, 0], [0, 2, 2, 0, 2, 0, 1]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [2, 0, 2, 1, 2, 0, 0], [0, 2, 0, 2, 1, 2, 0], [0, 2, 1, 2, 2, 2, 1]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [2, 0, 2, 1, 2, 0, 0], [0, 2, 0, 2, 1, 2, 0], [1, 0, 0, 2, 0, 1, 0], [1, 2, 2, 0, 2, 2, 1]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [2, 0, 2, 1, 2, 0, 0], [0, 2, 0, 2, 1, 2, 0], [1, 0, 0, 2, 0, 1, 0], [2, 1, 2, 1, 1, 0, 0], [1, 0, 2, 1, 0, 2, 1]], ![[0, 0, 0, 0, 0, 1, 0], [2, 0, 2, 1, 2, 0, 0], [0, 2, 0, 2, 1, 2, 0], [1, 0, 0, 2, 0, 1, 0], [2, 1, 2, 1, 1, 0, 0], [0, 2, 1, 2, 1, 1, 0], [1, 0, 0, 1, 1, 0, 1]], ![[0, 0, 0, 0, 0, 0, 1], [0, 2, 2, 0, 2, 0, 1], [0, 2, 1, 2, 2, 2, 1], [1, 2, 2, 0, 2, 2, 1], [1, 0, 2, 1, 0, 2, 1], [1, 0, 0, 1, 1, 0, 1], [0, 0, 0, 1, 0, 1, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![2, 2, 1, 2, 1, 1, 0], ![0, 2, 1, 1, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 2, 0, 0, 0], ![1, 0, 0, 2, 0, 0, 0], ![2, 1, 1, 1, 2, 0, 0], ![0, 1, 1, 2, 1, 0, 0]]
  v := ![![2, 2, 1, 2, 1, 1, 0], ![0, 2, 1, 1, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 2, 0, 0, 0], ![1, 0, 0, 2, 0, 0, 0], ![2, 1, 1, 1, 2, 0, 0], ![0, 1, 1, 2, 1, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 2, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0]]
  v_ind := ![5, 6]
  w_ind := ![0, 1, 2, 3, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![2, 0, 0, 2, 4, 0, 0], ![4, 2, 0, 2, 0, 2, 4], ![2, 4, 2, 0, 0, 4, 0], ![0, 2, 0, 0, 4, 0, 0], ![0, 0, 0, 4, 2, 0, 0], ![4, 4, 0, 2, 4, 4, 0], ![2, 2, 4, 2, 4, 4, 0]]
  a := ![![![320, 372], ![174, 368]], ![![1056, 1734], ![776, 1374]], ![![498, 1200], ![570, 750]], ![![294, 306], ![138, 330]], ![![198, 294], ![150, 240]], ![![798, 1560], ![738, 1098]], ![![834, 1578], ![744, 1134]]]
  c := ![![![-3, -82, -101, -66, -140], ![99, -84, -77, -84, -50]], ![![429, -346, -473, -390, -406], ![435, -270, -387, -332, -272]], ![![395, -262, -257, -284, -134], ![147, -138, -245, -164, -244]], ![![-6, -66, -96, -56, -128], ![113, -78, -69, -82, -26]], ![![0, -68, -58, -48, -88], ![33, -54, -55, -48, -58]], ![![393, -338, -353, -346, -272], ![243, -216, -321, -244, -294]], ![![393, -348, -363, -354, -276], ![246, -226, -320, -250, -296]]]
  d := ![![![0, 0], ![222, 144], ![192, 108], ![306, 774], ![306, 486]], ![![6, 12], ![678, 942], ![534, 756], ![1662, 2892], ![1278, 2076]], ![![12, 0], ![204, 756], ![120, 648], ![1422, 1368], ![828, 1206]], ![![0, 0], ![216, 108], ![192, 72], ![216, 720], ![258, 432]], ![![0, 0], ![120, 126], ![96, 108], ![306, 468], ![234, 324]], ![![12, 0], ![414, 900], ![300, 756], ![1722, 2106], ![1122, 1674]], ![![12, 0], ![438, 900], ![324, 756], ![1722, 2178], ![1140, 1710]]]
  e := ![![![-9, 0, 3, 4, -4], ![-93, -48, -35, -14, -90], ![-79, -32, -35, -8, -88], ![82, -194, -88, -132, -110], ![-10, -128, -74, -80, -116]], ![![-3, -4, 3, 0, -2], ![-18, -212, -202, -150, -304], ![-1, -160, -163, -120, -258], ![684, -628, -708, -646, -576], ![352, -452, -498, -430, -490]], ![![6, -2, -4, -4, 4], ![141, -190, -73, -138, -50], ![170, -158, -56, -128, -16], ![7, -274, -491, -266, -624], ![110, -264, -292, -228, -346]], ![![-15, 2, 3, 6, -8], ![-51, -44, -49, -24, -64], ![-73, -22, -43, -6, -84], ![120, -178, -72, -130, -66], ![28, -116, -72, -82, -82]], ![![-7, 0, 3, 2, -2], ![-90, -40, -4, 2, -66], ![-71, -28, -5, 2, -62], ![-19, -124, -71, -76, -118], ![-59, -88, -43, -40, -104]], ![![-15, 0, 3, 4, -8], ![53, -234, -109, -150, -142], ![77, -184, -85, -128, -116], ![90, -454, -580, -394, -738], ![114, -384, -370, -308, -458]], ![![12, -6, -6, -6, 12], ![30, -240, -102, -150, -150], ![120, -198, -102, -150, -84], ![90, -480, -576, -402, -732], ![84, -396, -360, -306, -474]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inr 1, Sum.inr 0), (Sum.inl 1, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [3]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R72

namespace VoightMaximalOrderD7R142

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨142394852, [4, -16, -8, 23, 5, -9, -1, 1], 2⟩
local notation "l" => [4, -16, -8, 23, 5, -9, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![2, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 2, 0], ![0, 0, 1, 1, 1, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, -1, -1, -1, -1, 2], ![-2, 8, 3, -12, -3, 4, 2]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, -1, -1, -1, -1, 2], ![-4, 16, 7, -24, -6, 8, 2], ![-4, 14, 10, -25, -22, 1, 12]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, -1, -1, -1, -1, 2], ![-4, 16, 7, -24, -6, 8, 2], ![-4, 12, 14, -25, -38, -6, 20], ![-24, 92, 49, -135, -62, 25, 26]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, -1, -1, -1, -1, 2], ![-4, 16, 7, -24, -6, 8, 2], ![-4, 12, 14, -25, -38, -6, 20], ![-40, 156, 78, -220, -79, 48, 28], ![-52, 184, 145, -288, -238, 17, 102]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, -1, -1, -1, -1, 2], ![-4, 16, 7, -24, -6, 8, 2], ![-4, 12, 14, -25, -38, -6, 20], ![-40, 156, 78, -220, -79, 48, 28], ![-56, 184, 192, -306, -352, -15, 152], ![-204, 764, 473, -1096, -611, 153, 238]], ![![0, 0, 0, 0, 0, 0, 1], ![-2, 8, 3, -12, -3, 4, 2], ![-4, 14, 10, -25, -22, 1, 12], ![-24, 92, 49, -135, -62, 25, 26], ![-52, 184, 145, -288, -238, 17, 102], ![-204, 764, 473, -1096, -611, 153, 238], ![-380, 1377, 1001, -2040, -1448, 192, 580]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-2]], ![[], [], [], [], [], [-4], [-4, -2]], ![[], [], [], [], [-4], [-4, -4], [-24, -4, -2]], ![[], [], [], [-4], [-4, -4], [-40, -4, -4], [-52, -24, -4, -2]], ![[], [], [-4], [-4, -4], [-40, -4, -4], [-56, -40, -4, -4], [-204, -52, -24, -4, -2]], ![[], [-2], [-4, -2], [-24, -4, -2], [-52, -24, -4, -2], [-204, -52, -24, -4, -2], [-380, -143, -41, -15, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, -1, -1, -1, -1, 2], [-2, 8, 3, -12, -3, 4, 2]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, -1, -1, -1, -1, 2], [-4, 16, 7, -24, -6, 8, 2], [-4, 14, 10, -25, -22, 1, 12]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, -1, -1, -1, -1, 2], [-4, 16, 7, -24, -6, 8, 2], [-4, 12, 14, -25, -38, -6, 20], [-24, 92, 49, -135, -62, 25, 26]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, -1, -1, -1, -1, 2], [-4, 16, 7, -24, -6, 8, 2], [-4, 12, 14, -25, -38, -6, 20], [-40, 156, 78, -220, -79, 48, 28], [-52, 184, 145, -288, -238, 17, 102]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, -1, -1, -1, -1, 2], [-4, 16, 7, -24, -6, 8, 2], [-4, 12, 14, -25, -38, -6, 20], [-40, 156, 78, -220, -79, 48, 28], [-56, 184, 192, -306, -352, -15, 152], [-204, 764, 473, -1096, -611, 153, 238]], ![[0, 0, 0, 0, 0, 0, 1], [-2, 8, 3, -12, -3, 4, 2], [-4, 14, 10, -25, -22, 1, 12], [-24, 92, 49, -135, -62, 25, 26], [-52, 184, 145, -288, -238, 17, 102], [-204, 764, 473, -1096, -611, 153, 238], [-380, 1377, 1001, -2040, -1448, 192, 580]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp35598713 : Fact (Nat.Prime 35598713) := fact_iff.2 (by norm_num)

def CD35598713 : CertificateDedekindCriterionLists l 35598713 where
  n := 2
  a' := [479963, 24356710, 21722812, 17885770, 4890894]
  b' := [5607737, 32478374, 7890809, 2944846, 15920518, 34783564]
  k := [10404896, 30410693, 14528189, 12546215, 20350298, 1]
  f := [4047925, 4452496, 4540770, 549874, 1439971, 5991324, 1]
  g := [18900447, 20789455, 21201621, 2567452, 6723468, 27974505, 1]
  h := [7624207, 1]
  a := [5805779, 34442718, 28931859, 371341, 31729308, 29285038]
  b := [23518991, 6337000, 25778167, 19647624, 26526114, 6313675]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 35598713]
  exp := ![2, 1]
  pdgood := [35598713]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp35598713.out
  a := [137330537, -14530392, -668956617, 271952334, 311914415, -129237052]
  b := [25432956, -166396091, 54701683, 201128913, -82220275, -47196693, 18462436]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 35598713 T_ofList CD35598713

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 5
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 1, 1, 0], [0, 0, 1, 0, 1, 0, 0]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 1, 1, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 1, 1, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 1, 1, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 0]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 1, 1, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 1, 0]], ![[0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 1, 1, 1, 0], ![0, 1, 0, 1, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0]]
  v := ![![0, 1, 1, 1, 1, 1, 0], ![0, 1, 0, 1, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0]]
  v_ind := ![5, 6]
  w_ind := ![0, 2, 3, 4, 5]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 1, 0, 1, 1, 0], ![0, 1, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 0], ![0, 0, 1, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 1, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 1, 1, 0]]
  a := ![![![93, 260], ![174, 377]], ![![292, 642], ![399, 986]], ![![94, 286], ![202, 406]], ![![58, 56], ![28, 116]], ![![94, 284], ![198, 404]], ![![8, 4], ![2, 12]], ![![92, 260], ![174, 376]]]
  c := ![![![-78, -500, -43, -762, 151], ![-134, -782, -17, -1241, 237]], ![![-221, -1308, -43, -2071, 391], ![-338, -2068, -108, -3174, 653]], ![![-82, -532, -52, -810, 160], ![-147, -840, -8, -1356, 249]], ![![-26, -117, 20, -227, 23], ![-30, -214, -32, -307, 67]], ![![-82, -532, -51, -809, 160], ![-146, -837, -9, -1347, 249]], ![![-2, -6, 3, -17, -1], ![-2, -16, -4, -23, 4]], ![![-78, -500, -43, -762, 151], ![-134, -782, -17, -1241, 237]]]
  d := ![![![2, 0], ![82, 100], ![0, 4], ![6, 44], ![102, 156]], ![![2, 2], ![118, 304], ![8, 8], ![56, 96], ![198, 440]], ![![2, 0], ![100, 104], ![0, 4], ![4, 48], ![120, 164]], ![![0, 0], ![-14, 44], ![2, 0], ![18, 4], ![4, 52]], ![![2, 0], ![98, 104], ![0, 4], ![4, 48], ![118, 164]], ![![0, 0], ![-2, 4], ![0, 0], ![2, 0], ![0, 4]], ![![2, 0], ![82, 100], ![0, 4], ![6, 44], ![102, 156]]]
  e := ![![![1, 0, -1, -1, 0], ![-44, -208, 27, -387, 50], ![0, 0, 0, -1, -1], ![-8, -65, -15, -91, 18], ![-56, -286, 17, -515, 67]], ![![0, 0, -1, -2, 0], ![-96, -592, -36, -922, 177], ![-2, -7, 1, -19, -1], ![-32, -175, 2, -302, 42], ![-138, -818, -35, -1324, 226]], ![![0, 0, 0, 0, 0], ![-48, -222, 34, -420, 48], ![0, 0, -2, -2, 0], ![-8, -64, -16, -94, 18], ![-60, -298, 22, -550, 64]], ![![0, 0, -1, -1, 1], ![-4, -52, -23, -61, 20], ![0, 0, 0, 1, -1], ![-4, -13, 7, -33, -2], ![-8, -64, -17, -95, 17]], ![![0, 0, -1, 0, 0], ![-48, -222, 34, -420, 49], ![0, 1, -1, -1, -1], ![-8, -65, -16, -94, 18], ![-60, -298, 23, -550, 64]], ![![0, -1, -1, -1, 1], ![0, 0, -1, -2, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, -1], ![0, 1, -1, -1, -1]], ![![0, 0, -1, -1, 0], ![-44, -209, 27, -387, 50], ![0, 0, -1, -1, -1], ![-8, -65, -15, -92, 18], ![-56, -286, 17, -515, 66]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inl 1, Sum.inr 1), (Sum.inr 0, Sum.inr 1), (Sum.inr 1, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R142

namespace VoightMaximalOrderD7R144

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨143148924, [4, -8, -11, 16, 10, -7, -2, 1], 2⟩
local notation "l" => [4, -8, -11, 16, 10, -7, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![2, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 2, 0], ![0, 1, 0, 0, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, 0, -1, 0, 2], ![-2, 3, 6, -8, -6, 4, 2]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, 0, -1, 0, 2], ![-4, 6, 11, -16, -12, 7, 4], ![-4, 0, 15, -10, -24, 2, 12]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, 0, -1, 0, 2], ![-4, 6, 11, -16, -12, 7, 4], ![-8, 1, 30, -21, -47, 4, 22], ![-24, 30, 72, -81, -84, 24, 28]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, 0, -1, 0, 2], ![-4, 6, 11, -16, -12, 7, 4], ![-8, 1, 30, -21, -47, 4, 22], ![-44, 54, 133, -146, -157, 41, 52], ![-56, 36, 198, -152, -273, 28, 104]], ![![0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, 0, -1, 0, 2], ![-4, 6, 11, -16, -12, 7, 4], ![-8, 1, 30, -21, -47, 4, 22], ![-44, 54, 133, -146, -157, 41, 52], ![-104, 71, 366, -283, -499, 51, 186], ![-208, 228, 660, -634, -804, 143, 264]], ![![0, 0, 0, 0, 0, 0, 1], ![-2, 3, 6, -8, -6, 4, 2], ![-4, 0, 15, -10, -24, 2, 12], ![-24, 30, 72, -81, -84, 24, 28], ![-56, 36, 198, -152, -273, 28, 104], ![-208, 228, 660, -634, -804, 143, 264], ![-293, 240, 1008, -806, -1320, 142, 460]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-2]], ![[], [], [], [], [], [-4], [-4, -2]], ![[], [], [], [], [-4], [-8, -4], [-24, -4, -2]], ![[], [], [], [-4], [-8, -4], [-44, -8, -4], [-56, -24, -4, -2]], ![[], [], [-4], [-8, -4], [-44, -8, -4], [-104, -44, -8, -4], [-208, -56, -24, -4, -2]], ![[], [-2], [-4, -2], [-24, -4, -2], [-56, -24, -4, -2], [-208, -56, -24, -4, -2], [-293, -116, -30, -13, -2, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, 0, 0, -1, 0, 2], [-2, 3, 6, -8, -6, 4, 2]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, 0, 0, -1, 0, 2], [-4, 6, 11, -16, -12, 7, 4], [-4, 0, 15, -10, -24, 2, 12]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, 0, 0, -1, 0, 2], [-4, 6, 11, -16, -12, 7, 4], [-8, 1, 30, -21, -47, 4, 22], [-24, 30, 72, -81, -84, 24, 28]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, 0, 0, -1, 0, 2], [-4, 6, 11, -16, -12, 7, 4], [-8, 1, 30, -21, -47, 4, 22], [-44, 54, 133, -146, -157, 41, 52], [-56, 36, 198, -152, -273, 28, 104]], ![[0, 0, 0, 0, 0, 1, 0], [0, -1, 0, 0, -1, 0, 2], [-4, 6, 11, -16, -12, 7, 4], [-8, 1, 30, -21, -47, 4, 22], [-44, 54, 133, -146, -157, 41, 52], [-104, 71, 366, -283, -499, 51, 186], [-208, 228, 660, -634, -804, 143, 264]], ![[0, 0, 0, 0, 0, 0, 1], [-2, 3, 6, -8, -6, 4, 2], [-4, 0, 15, -10, -24, 2, 12], [-24, 30, 72, -81, -84, 24, 28], [-56, 36, 198, -152, -273, 28, 104], [-208, 228, 660, -634, -804, 143, 264], [-293, 240, 1008, -806, -1320, 142, 460]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp227 : Fact (Nat.Prime 227) := fact_iff.2 (by norm_num)
instance hp5839 : Fact (Nat.Prime 5839) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [1, 0, 0, 2]
  b' := [0, 1, 2, 0, 2]
  k := [1, 2, 0, 0, 0, 2, 2, 2, 1]
  f := [-1, 3, 4, -5, -3, 3, 1]
  g := [1, 0, 0, 1, 0, 1]
  h := [1, 1, 1]
  a := [1, 0, 2, 0, 2]
  b := [2, 0, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD227 : CertificateDedekindCriterionLists l 227 where
  n := 2
  a' := [69, 25, 124, 124, 195]
  b' := [197, 151, 50, 23, 220, 81]
  k := [167, 69, 16, 173, 203, 1]
  f := [1, 1, 1, 5, 7, 11, 1]
  g := [21, 18, 18, 103, 136, 214, 1]
  h := [11, 1]
  a := [137, 206, 165, 78, 117, 131]
  b := [80, 34, 224, 154, 144, 96]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5839 : CertificateDedekindCriterionLists l 5839 where
  n := 2
  a' := [533, 3473, 5039, 1446, 1817]
  b' := [5676, 2807, 4849, 5833, 712, 4563]
  k := [188, 5234, 3093, 1287, 2519, 1]
  f := [689, 228, 1148, 328, 1541, 1188, 1]
  g := [2425, 801, 4040, 1152, 5423, 4178, 1]
  h := [1659, 1]
  a := [5603, 966, 4623, 2177, 3574, 1174]
  b := [4353, 4982, 816, 4332, 3286, 4665]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 3, 227, 5839]
  exp := ![3, 1, 1, 1]
  pdgood := [3, 227, 5839]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp227.out
    exact hp5839.out
  a := [-5966890, -65179044, -55941652, 57474135, 23787160, -13740391]
  b := [-6959804, -7483171, 24232588, 16028462, -12126939, -3958998, 1962913]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 227 T_ofList CD227
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5839 T_ofList CD5839

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0], [0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1, 0]], ![[0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 0, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0], ![0, 1, 1, 0, 1, 1, 0]]
  v := ![![1, 0, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0], ![0, 1, 1, 0, 1, 1, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0]]
  v_ind := ![6]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 1, 1, 1, 1, 1, 0], ![1, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 0, 0]]
  a := ![![![411]], ![![462]], ![![118]], ![![104]], ![![410]], ![![146]], ![![134]]]
  c := ![![![-352, -744, -817, 865, -490, 101]], ![![-377, -780, -836, 885, -452, 71]], ![![-90, -171, -178, 181, -88, 17]], ![![-80, -154, -161, 165, -80, 14]], ![![-352, -744, -817, 865, -490, 101]], ![![-116, -228, -242, 248, -131, 29]], ![![-108, -216, -230, 237, -127, 28]]]
  d := ![![![0], ![160], ![220], ![232], ![68], ![708]], ![![2], ![208], ![268], ![292], ![80], ![764]], ![![0], ![48], ![56], ![60], ![12], ![168]], ![![0], ![44], ![52], ![56], ![12], ![152]], ![![0], ![160], ![220], ![232], ![68], ![708]], ![![0], ![56], ![68], ![72], ![16], ![220]], ![![0], ![52], ![64], ![68], ![16], ![208]]]
  e := ![![![1, 0, 1, -1, 1, 1], ![-136, -276, -304, 311, -190, 53], ![-178, -341, -368, 368, -218, 66], ![-188, -358, -387, 384, -230, 74], ![-50, -82, -84, 75, -42, 20], ![-574, -1140, -1224, 1254, -693, 166]], ![![0, 0, 0, 0, 0, 0], ![-160, -308, -322, 330, -160, 28], ![-216, -432, -460, 474, -254, 56], ![-232, -456, -484, 496, -262, 58], ![-68, -138, -152, 156, -94, 26], ![-652, -1374, -1506, 1596, -894, 178]], ![![0, 0, -1, 2, -1, 0], ![-32, -48, -46, 41, -16, 5], ![-40, -65, -64, 56, -28, 14], ![-42, -64, -63, 54, -26, 14], ![-10, -16, -18, 15, -12, 8], ![-140, -276, -302, 306, -185, 54]], ![![0, 1, 0, 0, 0, 0], ![-30, -48, -47, 44, -18, 4], ![-38, -66, -66, 61, -32, 12], ![-40, -66, -66, 60, -31, 12], ![-10, -18, -20, 18, -14, 7], ![-128, -259, -284, 292, -175, 46]], ![![0, 0, 1, -1, 1, 1], ![-136, -277, -304, 311, -190, 53], ![-178, -341, -369, 368, -218, 66], ![-188, -358, -387, 383, -230, 74], ![-50, -82, -84, 75, -43, 20], ![-574, -1140, -1224, 1254, -693, 165]], ![![0, 0, 0, 1, 0, 0], ![-40, -66, -66, 60, -31, 12], ![-50, -82, -84, 74, -42, 21], ![-52, -81, -82, 70, -39, 22], ![-12, -16, -17, 12, -10, 9], ![-178, -341, -368, 367, -217, 66]], ![![0, 0, 1, 0, 0, 0], ![-38, -66, -66, 61, -32, 12], ![-48, -82, -86, 78, -45, 20], ![-50, -82, -84, 74, -42, 21], ![-12, -17, -18, 14, -11, 8], ![-168, -324, -349, 350, -204, 59]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inr 0, Sum.inr 1), (Sum.inr 1, Sum.inr 1), (Sum.inr 3, Sum.inr 1), (Sum.inr 4, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R144

end TraceEuclidean
