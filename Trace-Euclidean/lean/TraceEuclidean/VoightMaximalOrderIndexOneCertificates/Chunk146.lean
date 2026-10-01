import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk142
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

namespace VoightMaximalOrderD8R12

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨661518125, [1, 2, -10, -7, 15, 5, -7, -1, 1], 1⟩
local notation "l" => [1, 2, -10, -7, 15, 5, -7, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 10, 7, -15, -5, 7, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 10, 7, -15, -5, 7, 1], ![-1, -3, 8, 17, -8, -20, 2, 8]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 10, 7, -15, -5, 7, 1], ![-1, -3, 8, 17, -8, -20, 2, 8], ![-8, -17, 77, 64, -103, -48, 36, 10]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 10, 7, -15, -5, 7, 1], ![-1, -3, 8, 17, -8, -20, 2, 8], ![-8, -17, 77, 64, -103, -48, 36, 10], ![-10, -28, 83, 147, -86, -153, 22, 46]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 10, 7, -15, -5, 7, 1], ![-1, -3, 8, 17, -8, -20, 2, 8], ![-8, -17, 77, 64, -103, -48, 36, 10], ![-10, -28, 83, 147, -86, -153, 22, 46], ![-46, -102, 432, 405, -543, -316, 169, 68]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 10, 7, -15, -5, 7, 1], ![-1, -3, 8, 17, -8, -20, 2, 8], ![-8, -17, 77, 64, -103, -48, 36, 10], ![-10, -28, 83, 147, -86, -153, 22, 46], ![-46, -102, 432, 405, -543, -316, 169, 68], ![-68, -182, 578, 908, -615, -883, 160, 237]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 10, 7, -15, -5, 7, 1], ![-1, -3, 8, 17, -8, -20, 2, 8], ![-8, -17, 77, 64, -103, -48, 36, 10], ![-10, -28, 83, 147, -86, -153, 22, 46], ![-46, -102, 432, 405, -543, -316, 169, 68], ![-68, -182, 578, 908, -615, -883, 160, 237], ![-237, -542, 2188, 2237, -2647, -1800, 776, 397]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-8, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-8, -1, -1], [-10, -8, -1, -1]], ![[], [], [], [-1], [-1, -1], [-8, -1, -1], [-10, -8, -1, -1], [-46, -10, -8, -1, -1]], ![[], [], [-1], [-1, -1], [-8, -1, -1], [-10, -8, -1, -1], [-46, -10, -8, -1, -1], [-68, -46, -10, -8, -1, -1]], ![[], [-1], [-1, -1], [-8, -1, -1], [-10, -8, -1, -1], [-46, -10, -8, -1, -1], [-68, -46, -10, -8, -1, -1], [-237, -68, -46, -10, -8, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 10, 7, -15, -5, 7, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 10, 7, -15, -5, 7, 1], [-1, -3, 8, 17, -8, -20, 2, 8]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 10, 7, -15, -5, 7, 1], [-1, -3, 8, 17, -8, -20, 2, 8], [-8, -17, 77, 64, -103, -48, 36, 10]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 10, 7, -15, -5, 7, 1], [-1, -3, 8, 17, -8, -20, 2, 8], [-8, -17, 77, 64, -103, -48, 36, 10], [-10, -28, 83, 147, -86, -153, 22, 46]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 10, 7, -15, -5, 7, 1], [-1, -3, 8, 17, -8, -20, 2, 8], [-8, -17, 77, 64, -103, -48, 36, 10], [-10, -28, 83, 147, -86, -153, 22, 46], [-46, -102, 432, 405, -543, -316, 169, 68]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 10, 7, -15, -5, 7, 1], [-1, -3, 8, 17, -8, -20, 2, 8], [-8, -17, 77, 64, -103, -48, 36, 10], [-10, -28, 83, 147, -86, -153, 22, 46], [-46, -102, 432, 405, -543, -316, 169, 68], [-68, -182, 578, 908, -615, -883, 160, 237]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 10, 7, -15, -5, 7, 1], [-1, -3, 8, 17, -8, -20, 2, 8], [-8, -17, 77, 64, -103, -48, 36, 10], [-10, -28, 83, 147, -86, -153, 22, 46], [-46, -102, 432, 405, -543, -316, 169, 68], [-68, -182, 578, 908, -615, -883, 160, 237], [-237, -542, 2188, 2237, -2647, -1800, 776, 397]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp439 : Fact (Nat.Prime 439) := fact_iff.2 (by norm_num)
instance hp2411 : Fact (Nat.Prime 2411) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 1, 1]
  b' := [0, 3, 4, 1]
  k := [1]
  f := [0, 0, 3, 3, -1, 1, 3, 1]
  g := [1, 1, 2, 2, 1]
  h := [1, 1, 2, 2, 1]
  a := [0, 3]
  b := [1, 4, 4, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD439 : CertificateDedekindCriterionLists l 439 where
  n := 2
  a' := [81, 418, 400, 431, 328, 388]
  b' := [199, 167, 409, 392, 18, 22, 70]
  k := [360, 86, 246, 80, 353, 228, 1]
  f := [11, 41, 4, 73, 65, 36, 80, 1]
  g := [46, 171, 15, 305, 269, 148, 333, 1]
  h := [105, 1]
  a := [77, 109, 188, 283, 177, 360, 188]
  b := [287, 394, 278, 357, 322, 231, 251]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2411 : CertificateDedekindCriterionLists l 2411 where
  n := 2
  a' := [1923, 825, 1735, 1219, 946, 1773]
  b' := [1926, 1404, 183, 507, 925, 1875, 780]
  k := [218, 1789, 849, 1680, 1875, 340, 1]
  f := [604, 80, 210, 566, 623, 760, 591, 1]
  g := [1407, 185, 489, 1318, 1450, 1769, 1375, 1]
  h := [1035, 1]
  a := [505, 1151, 1683, 750, 889, 1830, 1664]
  b := [1675, 501, 826, 596, 1850, 806, 747]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 439, 2411]
  exp := ![1, 1, 1]
  pdgood := [5, 439, 2411]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp439.out
    exact hp2411.out
  a := [4284357, 8641320, -28565002, -13903842, 26134130, 4811588, -5687136]
  b := [503894, -3566077, -3306917, 8088974, 2974456, -4513400, -690310, 710892]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 439 T_ofList CD439
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2411 T_ofList CD2411

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

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R12

namespace VoightMaximalOrderD8R14

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨733968125, [1, 2, -7, -11, 11, 10, -6, -2, 1], 1⟩
local notation "l" => [1, 2, -7, -11, 11, 10, -6, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 7, 11, -11, -10, 6, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 7, 11, -11, -10, 6, 2], ![-2, -5, 12, 29, -11, -31, 2, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 7, 11, -11, -10, 6, 2], ![-2, -5, 12, 29, -11, -31, 2, 10], ![-10, -22, 65, 122, -81, -111, 29, 22]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 7, 11, -11, -10, 6, 2], ![-2, -5, 12, 29, -11, -31, 2, 10], ![-10, -22, 65, 122, -81, -111, 29, 22], ![-22, -54, 132, 307, -120, -301, 21, 73]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 7, 11, -11, -10, 6, 2], ![-2, -5, 12, 29, -11, -31, 2, 10], ![-10, -22, 65, 122, -81, -111, 29, 22], ![-22, -54, 132, 307, -120, -301, 21, 73], ![-73, -168, 457, 935, -496, -850, 137, 167]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 7, 11, -11, -10, 6, 2], ![-2, -5, 12, 29, -11, -31, 2, 10], ![-10, -22, 65, 122, -81, -111, 29, 22], ![-22, -54, 132, 307, -120, -301, 21, 73], ![-73, -168, 457, 935, -496, -850, 137, 167], ![-167, -407, 1001, 2294, -902, -2166, 152, 471]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 7, 11, -11, -10, 6, 2], ![-2, -5, 12, 29, -11, -31, 2, 10], ![-10, -22, 65, 122, -81, -111, 29, 22], ![-22, -54, 132, 307, -120, -301, 21, 73], ![-73, -168, 457, 935, -496, -850, 137, 167], ![-167, -407, 1001, 2294, -902, -2166, 152, 471], ![-471, -1109, 2890, 6182, -2887, -5612, 660, 1094]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-10, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-10, -2, -1], [-22, -10, -2, -1]], ![[], [], [], [-1], [-2, -1], [-10, -2, -1], [-22, -10, -2, -1], [-73, -22, -10, -2, -1]], ![[], [], [-1], [-2, -1], [-10, -2, -1], [-22, -10, -2, -1], [-73, -22, -10, -2, -1], [-167, -73, -22, -10, -2, -1]], ![[], [-1], [-2, -1], [-10, -2, -1], [-22, -10, -2, -1], [-73, -22, -10, -2, -1], [-167, -73, -22, -10, -2, -1], [-471, -167, -73, -22, -10, -2, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 7, 11, -11, -10, 6, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 7, 11, -11, -10, 6, 2], [-2, -5, 12, 29, -11, -31, 2, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 7, 11, -11, -10, 6, 2], [-2, -5, 12, 29, -11, -31, 2, 10], [-10, -22, 65, 122, -81, -111, 29, 22]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 7, 11, -11, -10, 6, 2], [-2, -5, 12, 29, -11, -31, 2, 10], [-10, -22, 65, 122, -81, -111, 29, 22], [-22, -54, 132, 307, -120, -301, 21, 73]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 7, 11, -11, -10, 6, 2], [-2, -5, 12, 29, -11, -31, 2, 10], [-10, -22, 65, 122, -81, -111, 29, 22], [-22, -54, 132, 307, -120, -301, 21, 73], [-73, -168, 457, 935, -496, -850, 137, 167]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 7, 11, -11, -10, 6, 2], [-2, -5, 12, 29, -11, -31, 2, 10], [-10, -22, 65, 122, -81, -111, 29, 22], [-22, -54, 132, 307, -120, -301, 21, 73], [-73, -168, 457, 935, -496, -850, 137, 167], [-167, -407, 1001, 2294, -902, -2166, 152, 471]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 7, 11, -11, -10, 6, 2], [-2, -5, 12, 29, -11, -31, 2, 10], [-10, -22, 65, 122, -81, -111, 29, 22], [-22, -54, 132, 307, -120, -301, 21, 73], [-73, -168, 457, 935, -496, -850, 137, 167], [-167, -407, 1001, 2294, -902, -2166, 152, 471], [-471, -1109, 2890, 6182, -2887, -5612, 660, 1094]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp106759 : Fact (Nat.Prime 106759) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2, 2]
  b' := [0, 4, 4, 2]
  k := [1]
  f := [3, 6, 11, 15, 9, 6, 6, 2]
  g := [4, 4, 4, 4, 1]
  h := [4, 4, 4, 4, 1]
  a := [2, 1, 1, 2]
  b := [0, 0, 1, 2, 3, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [8, 8, 10, 6, 1, 10]
  b' := [0, 9, 1, 4, 7, 1, 8]
  k := [5, 6, 10, 6, 9, 4, 1]
  f := [5, 7, 8, 4, 0, 5, 2, 1]
  g := [7, 9, 9, 3, 1, 8, 1, 1]
  h := [8, 1]
  a := [0, 10, 8, 3, 8, 8, 7]
  b := [8, 3, 0, 1, 1, 7, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD106759 : CertificateDedekindCriterionLists l 106759 where
  n := 2
  a' := [69290, 12630, 7955, 100293, 103478, 56527]
  b' := [92103, 95046, 7499, 42132, 52950, 96367, 7176]
  k := [20771, 12877, 74757, 88562, 74078, 19589, 1]
  f := [30089, 8115, 17981, 36465, 40187, 36470, 25791, 1]
  g := [73703, 19876, 44044, 89320, 98436, 89331, 63173, 1]
  h := [43584, 1]
  a := [2917, 74715, 61931, 87866, 50082, 14355, 65412]
  b := [32665, 64305, 7746, 82174, 68693, 8893, 41347]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 106759]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 106759]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp106759.out
  a := [-10367297, 144991722, -68964186, -237379580, 112430946, 67664852, -31545552]
  b := [8119521, -5291917, -49866491, 23093340, 46554488, -19579280, -9443905, 3943194]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 106759 T_ofList CD106759

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

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R14

namespace VoightMaximalOrderD8R17

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨852038125, [1, 0, -10, 5, 17, -5, -10, 0, 1], 1⟩
local notation "l" => [1, 0, -10, 5, 17, -5, -10, 0, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 10, -5, -17, 5, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 10, -5, -17, 5, 10, 0], ![0, -1, 0, 10, -5, -17, 5, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 10, -5, -17, 5, 10, 0], ![0, -1, 0, 10, -5, -17, 5, 10], ![-10, 0, 99, -50, -160, 45, 83, 5]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 10, -5, -17, 5, 10, 0], ![0, -1, 0, 10, -5, -17, 5, 10], ![-10, 0, 99, -50, -160, 45, 83, 5], ![-5, -10, 50, 74, -135, -135, 95, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 10, -5, -17, 5, 10, 0], ![0, -1, 0, 10, -5, -17, 5, 10], ![-10, 0, 99, -50, -160, 45, 83, 5], ![-5, -10, 50, 74, -135, -135, 95, 83], ![-83, -5, 820, -365, -1337, 280, 695, 95]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 10, -5, -17, 5, 10, 0], ![0, -1, 0, 10, -5, -17, 5, 10], ![-10, 0, 99, -50, -160, 45, 83, 5], ![-5, -10, 50, 74, -135, -135, 95, 83], ![-83, -5, 820, -365, -1337, 280, 695, 95], ![-95, -83, 945, 345, -1980, -862, 1230, 695]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 10, -5, -17, 5, 10, 0], ![0, -1, 0, 10, -5, -17, 5, 10], ![-10, 0, 99, -50, -160, 45, 83, 5], ![-5, -10, 50, 74, -135, -135, 95, 83], ![-83, -5, 820, -365, -1337, 280, 695, 95], ![-95, -83, 945, 345, -1980, -862, 1230, 695], ![-695, -95, 6867, -2530, -11470, 1495, 6088, 1230]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [-5, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [-5, -10, 0, -1], [-83, -5, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [-5, -10, 0, -1], [-83, -5, -10, 0, -1], [-95, -83, -5, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [-5, -10, 0, -1], [-83, -5, -10, 0, -1], [-95, -83, -5, -10, 0, -1], [-695, -95, -83, -5, -10, 0, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 10, -5, -17, 5, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 10, -5, -17, 5, 10, 0], [0, -1, 0, 10, -5, -17, 5, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 10, -5, -17, 5, 10, 0], [0, -1, 0, 10, -5, -17, 5, 10], [-10, 0, 99, -50, -160, 45, 83, 5]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 10, -5, -17, 5, 10, 0], [0, -1, 0, 10, -5, -17, 5, 10], [-10, 0, 99, -50, -160, 45, 83, 5], [-5, -10, 50, 74, -135, -135, 95, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 10, -5, -17, 5, 10, 0], [0, -1, 0, 10, -5, -17, 5, 10], [-10, 0, 99, -50, -160, 45, 83, 5], [-5, -10, 50, 74, -135, -135, 95, 83], [-83, -5, 820, -365, -1337, 280, 695, 95]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 10, -5, -17, 5, 10, 0], [0, -1, 0, 10, -5, -17, 5, 10], [-10, 0, 99, -50, -160, 45, 83, 5], [-5, -10, 50, 74, -135, -135, 95, 83], [-83, -5, 820, -365, -1337, 280, 695, 95], [-95, -83, 945, 345, -1980, -862, 1230, 695]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 10, -5, -17, 5, 10, 0], [0, -1, 0, 10, -5, -17, 5, 10], [-10, 0, 99, -50, -160, 45, 83, 5], [-5, -10, 50, 74, -135, -135, 95, 83], [-83, -5, 820, -365, -1337, 280, 695, 95], [-95, -83, 945, 345, -1980, -862, 1230, 695], [-695, -95, 6867, -2530, -11470, 1495, 6088, 1230]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp1621 : Fact (Nat.Prime 1621) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [0, 1]
  k := [1]
  f := [0, 0, 2, -1, -3, 1, 2]
  g := [1, 0, 0, 0, 1]
  h := [1, 0, 0, 0, 1]
  a := [3, 1, 0, 1]
  b := [1, 0, 4, 1, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [10, 27, 19, 23, 26]
  b' := [2, 13, 2, 15, 22, 15]
  k := [1, 18, 3, 11, 1]
  f := [27, 28, 22, 10, 15, 24, 8, 1]
  g := [28, 20, 15, 5, 14, 20, 1]
  h := [28, 9, 1]
  a := [18, 3, 15, 7, 24, 4]
  b := [21, 19, 14, 17, 6, 24, 25]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1621 : CertificateDedekindCriterionLists l 1621 where
  n := 2
  a' := [950, 1410, 769, 1510, 1116, 1086]
  b' := [1159, 272, 951, 125, 234, 429, 308]
  k := [1620, 332, 13, 874, 1608, 332, 1]
  f := [149, 1, 1271, 736, 1267, 1446, 150, 1]
  g := [166, 1, 1416, 819, 1411, 1610, 166, 1]
  h := [1455, 1]
  a := [1099, 714, 424, 847, 1049, 1472, 378]
  b := [1572, 134, 1080, 704, 1255, 1334, 1243]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 29, 1621]
  exp := ![1, 1, 1]
  pdgood := [5, 29, 1621]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp29.out
    exact hp1621.out
  a := [235045, -9813840, -8160150, 23799406, 22175512, -1961936, -3213040]
  b := [-490692, -893549, 3817137, 3373330, -4341087, -3776014, 245242, 401630]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1621 T_ofList CD1621

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

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R17

namespace VoightMaximalOrderD8R18

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨877268125, [1, 7, -1, -25, 5, 20, -6, -3, 1], 1⟩
local notation "l" => [1, 7, -1, -25, 5, 20, -6, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, -5, -20, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, -5, -20, 6, 3], ![-3, -22, -4, 76, 10, -65, -2, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, -5, -20, 6, 3], ![-3, -22, -4, 76, 10, -65, -2, 15], ![-15, -108, -7, 371, 1, -290, 25, 43]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, -5, -20, 6, 3], ![-3, -22, -4, 76, 10, -65, -2, 15], ![-15, -108, -7, 371, 1, -290, 25, 43], ![-43, -316, -65, 1068, 156, -859, -32, 154]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, -5, -20, 6, 3], ![-3, -22, -4, 76, 10, -65, -2, 15], ![-15, -108, -7, 371, 1, -290, 25, 43], ![-43, -316, -65, 1068, 156, -859, -32, 154], ![-154, -1121, -162, 3785, 298, -2924, 65, 430]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, -5, -20, 6, 3], ![-3, -22, -4, 76, 10, -65, -2, 15], ![-15, -108, -7, 371, 1, -290, 25, 43], ![-43, -316, -65, 1068, 156, -859, -32, 154], ![-154, -1121, -162, 3785, 298, -2924, 65, 430], ![-430, -3164, -691, 10588, 1635, -8302, -344, 1355]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, 1, 25, -5, -20, 6, 3], ![-3, -22, -4, 76, 10, -65, -2, 15], ![-15, -108, -7, 371, 1, -290, 25, 43], ![-43, -316, -65, 1068, 156, -859, -32, 154], ![-154, -1121, -162, 3785, 298, -2924, 65, 430], ![-430, -3164, -691, 10588, 1635, -8302, -344, 1355], ![-1355, -9915, -1809, 33184, 3813, -25465, -172, 3721]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-154, -43, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-154, -43, -15, -3, -1], [-430, -154, -43, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-154, -43, -15, -3, -1], [-430, -154, -43, -15, -3, -1], [-1355, -430, -154, -43, -15, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, -5, -20, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, -5, -20, 6, 3], [-3, -22, -4, 76, 10, -65, -2, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, -5, -20, 6, 3], [-3, -22, -4, 76, 10, -65, -2, 15], [-15, -108, -7, 371, 1, -290, 25, 43]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, -5, -20, 6, 3], [-3, -22, -4, 76, 10, -65, -2, 15], [-15, -108, -7, 371, 1, -290, 25, 43], [-43, -316, -65, 1068, 156, -859, -32, 154]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, -5, -20, 6, 3], [-3, -22, -4, 76, 10, -65, -2, 15], [-15, -108, -7, 371, 1, -290, 25, 43], [-43, -316, -65, 1068, 156, -859, -32, 154], [-154, -1121, -162, 3785, 298, -2924, 65, 430]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, -5, -20, 6, 3], [-3, -22, -4, 76, 10, -65, -2, 15], [-15, -108, -7, 371, 1, -290, 25, 43], [-43, -316, -65, 1068, 156, -859, -32, 154], [-154, -1121, -162, 3785, 298, -2924, 65, 430], [-430, -3164, -691, 10588, 1635, -8302, -344, 1355]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, 1, 25, -5, -20, 6, 3], [-3, -22, -4, 76, 10, -65, -2, 15], [-15, -108, -7, 371, 1, -290, 25, 43], [-43, -316, -65, 1068, 156, -859, -32, 154], [-154, -1121, -162, 3785, 298, -2924, 65, 430], [-430, -3164, -691, 10588, 1635, -8302, -344, 1355], [-1355, -9915, -1809, 33184, 3813, -25465, -172, 3721]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp1669 : Fact (Nat.Prime 1669) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 1, 2]
  b' := [0, 3, 4, 2]
  k := [1]
  f := [0, -1, 2, 7, 3, -2, 3, 1]
  g := [1, 1, 4, 1, 1]
  h := [1, 1, 4, 1, 1]
  a := [1, 0, 2]
  b := [1, 0, 4, 0, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [24, 2, 8, 22, 15]
  b' := [26, 11, 21, 2, 7, 12]
  k := [20, 1, 9, 4, 1]
  f := [3, 11, 10, 5, 4, 12, 7, 1]
  g := [22, 21, 9, 0, 28, 15, 1]
  h := [4, 11, 1]
  a := [1, 20, 7, 3, 16, 24]
  b := [21, 11, 13, 16, 7, 2, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1669 : CertificateDedekindCriterionLists l 1669 where
  n := 2
  a' := [1582, 1574, 1600, 940, 1263, 274]
  b' := [431, 737, 731, 13, 574, 212, 1153]
  k := [134, 799, 1022, 1144, 315, 1422, 1]
  f := [97, 60, 23, 29, 87, 17, 113, 1]
  g := [1327, 810, 308, 394, 1187, 223, 1544, 1]
  h := [122, 1]
  a := [1001, 626, 982, 305, 657, 874, 1613]
  b := [850, 629, 305, 897, 441, 771, 56]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 29, 1669]
  exp := ![1, 1, 1]
  pdgood := [5, 29, 1669]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp29.out
    exact hp1669.out
  a := [-8161, 1039002, -1790662, -2083574, 2745614, 465980, -592352]
  b := [35738, -130057, -438611, 586704, 481360, -505312, -86014, 74044]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1669 T_ofList CD1669

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

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R18

end TraceEuclidean
