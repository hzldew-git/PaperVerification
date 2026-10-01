import TraceEuclidean.VoightMaximalOrderCertificates.Chunk068
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

namespace VoightMaximalOrderD6R661

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14350777, [-71, 3, 65, 5, -15, -1, 1], 27⟩
local notation "l" => [-71, 3, 65, 5, -15, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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

def basisDenominator : ℤ := 9
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![9, 0, 0, 0, 0, 0], ![0, 9, 0, 0, 0, 0], ![0, 0, 9, 0, 0, 0], ![0, 0, 0, 9, 0, 0], ![3, 3, 6, 0, 3, 0], ![4, 5, 6, 5, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, -1, -2, 0, 3, 0], ![-1, -1, -1, -1, -1, 3], ![5, -3, -12, -1, 6, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, -1, -2, 0, 3, 0], ![-3, -4, -4, -5, -3, 9], ![17, -8, -34, -3, 16, 3], ![5, -6, -31, -20, 3, 22]], ![![0, 0, 0, 1, 0, 0], ![-1, -1, -2, 0, 3, 0], ![-3, -4, -4, -5, -3, 9], ![53, -22, -99, -10, 42, 9], ![2, -5, -54, -53, -7, 54], ![127, -44, -233, -56, 69, 53]], ![![0, 0, 0, 0, 1, 0], ![-1, -1, -1, -1, -1, 3], ![17, -8, -34, -3, 16, 3], ![2, -5, -54, -53, -7, 54], ![121, -39, -203, -36, 68, 32], ![89, -20, -237, -132, 31, 120]], ![![0, 0, 0, 0, 0, 1], ![5, -3, -12, -1, 6, 2], ![5, -6, -31, -20, 3, 22], ![127, -44, -233, -56, 69, 53], ![89, -20, -237, -132, 31, 120], ![309, -81, -580, -199, 134, 177]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-9]], ![[], [], [], [], [-27], [-18, -9]], ![[], [], [], [-81], [-27, -27], [-198, -18, -9]], ![[], [], [-27], [-27, -27], [-180, -9, -9], [-174, -72, -6, -3]], ![[], [-9], [-18, -9], [-198, -18, -9], [-174, -72, -6, -3], [-493, -91, -29, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, -1, -2, 0, 3, 0], [-1, -1, -1, -1, -1, 3], [5, -3, -12, -1, 6, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, -1, -2, 0, 3, 0], [-3, -4, -4, -5, -3, 9], [17, -8, -34, -3, 16, 3], [5, -6, -31, -20, 3, 22]], ![[0, 0, 0, 1, 0, 0], [-1, -1, -2, 0, 3, 0], [-3, -4, -4, -5, -3, 9], [53, -22, -99, -10, 42, 9], [2, -5, -54, -53, -7, 54], [127, -44, -233, -56, 69, 53]], ![[0, 0, 0, 0, 1, 0], [-1, -1, -1, -1, -1, 3], [17, -8, -34, -3, 16, 3], [2, -5, -54, -53, -7, 54], [121, -39, -203, -36, 68, 32], [89, -20, -237, -132, 31, 120]], ![[0, 0, 0, 0, 0, 1], [5, -3, -12, -1, 6, 2], [5, -6, -31, -20, 3, 22], [127, -44, -233, -56, 69, 53], [89, -20, -237, -132, 31, 120], [309, -81, -580, -199, 134, 177]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp43 : Fact (Nat.Prime 43) := fact_iff.2 (by norm_num)
instance hp139 : Fact (Nat.Prime 139) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 3
  a' := [2]
  b' := [6, 6]
  k := [1]
  f := [13, 5, -7, 3, 4, 1]
  g := [5, 2, 1]
  h := [4, 6, 0, 4, 1]
  a := [4, 4]
  b := [1, 2, 2, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD43 : CertificateDedekindCriterionLists l 43 where
  n := 2
  a' := [36, 30, 34, 7]
  b' := [32, 24, 28, 40, 33]
  k := [1, 19, 6, 23, 1]
  f := [24, 23, 23, 23, 9, 1]
  g := [31, 31, 33, 31, 11, 1]
  h := [31, 1]
  a := [6, 37, 31, 38, 28]
  b := [37, 27, 40, 18, 15]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD139 : CertificateDedekindCriterionLists l 139 where
  n := 2
  a' := [40, 36, 97, 138]
  b' := [91, 59, 28, 84, 28]
  k := [19, 118, 135, 28, 1]
  f := [29, 46, 15, 3, 33, 1]
  g := [72, 115, 37, 7, 83, 1]
  h := [55, 1]
  a := [136, 121, 71, 76, 17]
  b := [63, 7, 106, 79, 122]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 4
  p := ![3, 7, 43, 139]
  exp := ![4, 1, 1, 1]
  pdgood := [7, 43, 139]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp7.out
    exact hp43.out
    exact hp139.out
  a := [-202983, -6641270, 2958650, 1506520, -573240]
  b := [-3674278, 2244973, 2149845, -942230, -267010, 95540]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 43 T_ofList CD43
    exact satisfiesDedekindCriterion_of_certificate_lists T l 139 T_ofList CD139

noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
  n := 6
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [2, 2, 1, 0, 0, 0], [2, 2, 2, 2, 2, 0], [2, 0, 0, 2, 0, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [2, 2, 1, 0, 0, 0], [0, 2, 2, 1, 0, 0], [2, 1, 2, 0, 1, 0], [2, 0, 2, 1, 0, 1]], ![[0, 0, 0, 1, 0, 0], [2, 2, 1, 0, 0, 0], [0, 2, 2, 1, 0, 0], [2, 2, 0, 2, 0, 0], [2, 1, 0, 1, 2, 0], [1, 1, 1, 1, 0, 2]], ![[0, 0, 0, 0, 1, 0], [2, 2, 2, 2, 2, 0], [2, 1, 2, 0, 1, 0], [2, 1, 0, 1, 2, 0], [1, 0, 1, 0, 2, 2], [2, 1, 0, 0, 1, 0]], ![[0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 2], [2, 0, 2, 1, 0, 1], [1, 1, 1, 1, 0, 2], [2, 1, 0, 0, 1, 0], [0, 0, 2, 2, 2, 0]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![2, 2, 0, 2, 0, 0], ![2, 2, 2, 0, 0, 0], ![2, 0, 1, 0, 2, 1], ![1, 1, 0, 1, 2, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [3]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R661

namespace VoightMaximalOrderD6R663

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14389193, [-56, -56, 70, 15, -16, -1, 1], 104⟩
local notation "l" => [-56, -56, 70, 15, -16, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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

def basisDenominator : ℤ := 52
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![52, 0, 0, 0, 0, 0], ![0, 52, 0, 0, 0, 0], ![0, 0, 52, 0, 0, 0], ![0, 0, 0, 52, 0, 0], ![0, 26, 0, 26, 26, 0], ![12, 48, 51, 30, 21, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, -1, 0, -1, 2, 0], ![-6, -14, -25, -5, -20, 26], ![-4, -11, -22, -4, -16, 22]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, -1, 0, -1, 2, 0], ![-12, -27, -51, -9, -42, 52], ![16, -7, -86, -24, -26, 52], ![8, -18, -95, -26, -40, 68]], ![![0, 0, 0, 1, 0, 0], ![0, -1, 0, -1, 2, 0], ![-12, -27, -51, -9, -42, 52], ![44, 13, -121, -40, -10, 52], ![-52, -168, -501, -140, -360, 468], ![-32, -154, -514, -141, -340, 456]], ![![0, 0, 0, 0, 1, 0], ![-6, -14, -25, -5, -20, 26], ![16, -7, -86, -24, -26, 52], ![-52, -168, -501, -140, -360, 468], ![115, -101, -995, -289, -474, 715], ![90, -156, -1111, -321, -567, 835]], ![![0, 0, 0, 0, 0, 1], ![-4, -11, -22, -4, -16, 22], ![8, -18, -95, -26, -40, 68], ![-32, -154, -514, -141, -340, 456], ![90, -156, -1111, -321, -567, 835], ![71, -205, -1224, -351, -651, 947]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-52]], ![[], [], [], [], [-1352], [-1144, -52]], ![[], [], [], [-2704], [-2704, -1352], [-3536, -1144, -52]], ![[], [], [-1352], [-2704, -1352], [-13520, -2028, -676], [-13650, -2340, -598, -26]], ![[], [-52], [-1144, -52], [-3536, -1144, -52], [-13650, -2340, -598, -26], [-13978, -2595, -560, -43, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, -1, 0, -1, 2, 0], [-6, -14, -25, -5, -20, 26], [-4, -11, -22, -4, -16, 22]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, -1, 0, -1, 2, 0], [-12, -27, -51, -9, -42, 52], [16, -7, -86, -24, -26, 52], [8, -18, -95, -26, -40, 68]], ![[0, 0, 0, 1, 0, 0], [0, -1, 0, -1, 2, 0], [-12, -27, -51, -9, -42, 52], [44, 13, -121, -40, -10, 52], [-52, -168, -501, -140, -360, 468], [-32, -154, -514, -141, -340, 456]], ![[0, 0, 0, 0, 1, 0], [-6, -14, -25, -5, -20, 26], [16, -7, -86, -24, -26, 52], [-52, -168, -501, -140, -360, 468], [115, -101, -995, -289, -474, 715], [90, -156, -1111, -321, -567, 835]], ![[0, 0, 0, 0, 0, 1], [-4, -11, -22, -4, -16, 22], [8, -18, -95, -26, -40, 68], [-32, -154, -514, -141, -340, 456], [90, -156, -1111, -321, -567, 835], [71, -205, -1224, -351, -651, 947]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp461 : Fact (Nat.Prime 461) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 3
  a' := [6]
  b' := [4, 4]
  k := [1]
  f := [8, 8, -10, -1, 4, 1]
  g := [0, 2, 1]
  h := [0, 0, 4, 4, 1]
  a := [1, 1]
  b := [6, 5, 3, 4, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD461 : CertificateDedekindCriterionLists l 461 where
  n := 2
  a' := [368, 242, 275, 55]
  b' := [387, 168, 339, 148, 450]
  k := [412, 234, 158, 26, 1]
  f := [203, 10, 191, 127, 115, 1]
  g := [431, 19, 406, 268, 243, 1]
  h := [217, 1]
  a := [244, 446, 286, 259, 413]
  b := [99, 104, 95, 51, 48]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 13] where
  n := 4
  p := ![2, 7, 13, 461]
  exp := ![3, 1, 2, 1]
  pdgood := [7, 461]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp7.out
    exact hp13.out
    exact hp461.out
  a := [-199891, 240531, 320151, -32457, -46782]
  b := [121982, 264315, -51737, -96927, 4110, 7797]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 461 T_ofList CD461

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 1, 1, 1, 0, 1], [0, 0, 1, 1, 1, 1]], ![[0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 1, 1], [1, 1, 0, 1, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

noncomputable def M13 : MaximalOrderCertificateLists 13 O Om hm where
  m := 1
  n := 5
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 12, 0, 12, 2, 0], [7, 12, 1, 8, 6, 0], [9, 2, 4, 9, 10, 9]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 12, 0, 12, 2, 0], [1, 12, 1, 4, 10, 0], [3, 6, 5, 2, 0, 0], [8, 8, 9, 0, 12, 3]], ![[0, 0, 0, 1, 0, 0], [0, 12, 0, 12, 2, 0], [1, 12, 1, 4, 10, 0], [5, 0, 9, 12, 3, 0], [0, 1, 6, 3, 4, 0], [7, 2, 6, 2, 11, 1]], ![[0, 0, 0, 0, 1, 0], [7, 12, 1, 8, 6, 0], [3, 6, 5, 2, 0, 0], [0, 1, 6, 3, 4, 0], [11, 3, 6, 10, 7, 0], [12, 0, 7, 4, 5, 3]], ![[0, 0, 0, 0, 0, 1], [9, 2, 4, 9, 10, 9], [8, 8, 9, 0, 12, 3], [7, 2, 6, 2, 11, 1], [12, 0, 7, 4, 5, 3], [6, 3, 11, 0, 12, 11]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![8, 10, 7, 8, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 5, 11, 9, 0, 10], ![0, 2, 0, 11, 0, 11], ![0, 11, 1, 3, 0, 12], ![5, 8, 10, 0, 0, 5]]
  v := ![![8, 10, 7, 8, 1, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 5, 11, 9, 0, 10], ![0, 2, 0, 11, 0, 11], ![0, 11, 1, 3, 0, 12], ![5, 8, 10, 0, 0, 5]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 10], ![0, 0, 1, 0, 0, 11], ![0, 0, 0, 1, 0, 12], ![0, 0, 0, 0, 1, 5]]
  v_ind := ![4]
  w_ind := ![0, 1, 2, 3, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![3344, 2128, 2432, 1520, 2736, 3040], ![1520, 912, 1824, 1520, 3648, 0], ![912, 1824, 1520, 2432, 1216, 912], ![2736, 3344, 304, 608, 0, 304], ![3040, 3648, 608, 1824, 3344, 2432], ![608, 2128, 2432, 2432, 608, 3040]]
  a := ![![![-23466672]], ![![-15321904]], ![![-10204064]], ![![-1683552]], ![![-23055968]], ![![-16187392]]]
  c := ![![![-437329438, -77353695, 76208804, -42827815, 90338870]], ![![-285592484, -50512610, 49765080, -27968002, 58993204]], ![![-189334366, -33505599, 33006900, -18541623, 39122150]], ![![-31010304, -5490984, 5409120, -3037032, 6410240]], ![![-429574262, -75985659, 74859380, -42067635, 88739438]], ![![-300804166, -53222715, 52432484, -29458163, 62148750]]]
  d := ![![![35568], ![-835120832], ![-904956624], ![-752595168], ![-314579200]], ![![47424], ![-538357248], ![-584690496], ![-483693184], ![-200919680]], ![![15808], ![-409514144], ![-434518448], ![-382711680], ![-168201072]], ![![0], ![-80193984], ![-83865392], ![-78874016], ![-35769552]], ![![43472], ![-829303488], ![-896309648], ![-751014368], ![-315994016]], ![![7904], ![-624692640], ![-667358432], ![-576652128], ![-249616224]]]
  e := ![![![775996, 136054, -133832, 75766, -158908], ![-15566070676, -2755129546, 2713667160, -1524158170, 3216564772], ![-16892428930, -2989461617, 2944514012, -1654007561, 3490343194], ![-14036385792, -2484869920, 2447270336, -1374299200, 2900748768], ![-5846250778, -1035347077, 1019639916, -572421229, 1208449314]], ![![987506, 173641, -170924, 96577, -203034], ![-10037839630, -1776669791, 1749909460, -982847463, 2074214454], ![-10917825880, -1932108724, 1903044208, -1068998372, 2255839352], ![-9023827670, -1597521939, 1573326404, -883511291, 1864867550], ![-3734615144, -661435476, 651382160, -365660308, 771988984]], ![![291634, 51393, -50508, 28585, -60090], ![-7625759830, -1349625467, 1329382292, -746712627, 1575733310], ![-8097846666, -1433151461, 1411624156, -792915853, 1673258834], ![-7136062206, -1262957007, 1243973220, -698734407, 1474531622], ![-3131011620, -554155162, 545851960, -306595130, 646983764]], ![![-59644, -10790, 10456, -5766, 12476], ![-1489112906, -263507517, 259592572, -145831221, 307687138], ![-1556612070, -275482475, 271375444, -152435939, 321653854], ![-1468352158, -259784023, 255924244, -143791935, 303361222], ![-666776036, -117942746, 116201400, -65299898, 137739860]], ![![894998, 156995, -154628, 87675, -183742], ![-15462758558, -2736815527, 2695613364, -1514029295, 3195191718], ![-16733674342, -2961359067, 2916813204, -1638448691, 3457536910], ![-14012951186, -2480614513, 2443089868, -1372000809, 2895833482], ![-5877934030, -1040884607, 1025102628, -575521207, 1214941430]], ![![161954, 28609, -27964, 15897, -33242], ![-11633397204, -2058960658, 2028058152, -1139132082, 2403875012], ![-12441382096, -2201847680, 2168774000, -1218219200, 2570742256], ![-10750169672, -1902772508, 1874118496, -1052598924, 2221430888], ![-4642369740, -821795670, 809441704, -454579910, 959384668]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inr 1, Sum.inr 0), (Sum.inr 2, Sum.inr 0), (Sum.inr 3, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2, 13]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
    exact @pMaximal_of_MaximalOrderCertificateLists K 13 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M13
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 13] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R663

namespace VoightMaximalOrderD6R665

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14414517, [3, 18, 15, -31, -12, 3, 1], 127⟩
local notation "l" => [3, 18, 15, -31, -12, 3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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

def basisDenominator : ℤ := 127
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![127, 0, 0, 0, 0, 0], ![0, 127, 0, 0, 0, 0], ![0, 0, 127, 0, 0, 0], ![0, 0, 0, 127, 0, 0], ![0, 0, 0, 0, 127, 0], ![63, 71, 94, 42, 9, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-63, -71, -94, -42, -9, 127], ![-3, -3, -4, -1, 0, 6]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-63, -71, -94, -42, -9, 127], ![186, 195, 267, 157, 39, -381], ![-18, -21, -27, -10, -1, 36]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-63, -71, -94, -42, -9, 127], ![186, 195, 267, 157, 39, -381], ![-1314, -1440, -1947, -990, -194, 2667], ![-45, -55, -71, -21, -1, 89]], ![![0, 0, 0, 0, 1, 0], ![-63, -71, -94, -42, -9, 127], ![186, 195, 267, 157, 39, -381], ![-1314, -1440, -1947, -990, -194, 2667], ![4221, 4459, 6128, 3534, 756, -8636], ![-204, -241, -317, -118, -12, 407]], ![![0, 0, 0, 0, 0, 1], ![-3, -3, -4, -1, 0, 6], ![-18, -21, -27, -10, -1, 36], ![-45, -55, -71, -21, -1, 89], ![-204, -241, -317, -118, -12, 407], ![-48, -57, -74, -25, -2, 96]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-127]], ![[], [], [], [], [-16129], [-762, -127]], ![[], [], [], [-16129], [48387, -16129], [-4572, -762, -127]], ![[], [], [-16129], [48387, -16129], [-338709, 48387, -16129], [-11303, -4572, -762, -127]], ![[], [-127], [-762, -127], [-4572, -762, -127], [-11303, -4572, -762, -127], [-3355, -759, -132, -15, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-63, -71, -94, -42, -9, 127], [-3, -3, -4, -1, 0, 6]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-63, -71, -94, -42, -9, 127], [186, 195, 267, 157, 39, -381], [-18, -21, -27, -10, -1, 36]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-63, -71, -94, -42, -9, 127], [186, 195, 267, 157, 39, -381], [-1314, -1440, -1947, -990, -194, 2667], [-45, -55, -71, -21, -1, 89]], ![[0, 0, 0, 0, 1, 0], [-63, -71, -94, -42, -9, 127], [186, 195, 267, 157, 39, -381], [-1314, -1440, -1947, -990, -194, 2667], [4221, 4459, 6128, 3534, 756, -8636], [-204, -241, -317, -118, -12, 407]], ![[0, 0, 0, 0, 0, 1], [-3, -3, -4, -1, 0, 6], [-18, -21, -27, -10, -1, 36], [-45, -55, -71, -21, -1, 89], [-204, -241, -317, -118, -12, 407], [-48, -57, -74, -25, -2, 96]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp127 : Fact (Nat.Prime 127) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [2]
  b' := [2, 2]
  k := [1]
  f := [-1, -6, -5, 11, 5]
  g := [0, 2, 1]
  h := [0, 0, 1, 1, 1]
  a := [2, 2]
  b := [1, 0, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD13 : CertificateDedekindCriterionLists l 13 where
  n := 2
  a' := [0, 8]
  b' := [1, 3, 6]
  k := [1]
  f := [6, 0, 10, 5, 6, 1]
  g := [9, 1, 8, 1]
  h := [9, 1, 8, 1]
  a := [2, 9, 9]
  b := [6, 2, 5, 9, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [127] where
  n := 3
  p := ![3, 13, 127]
  exp := ![2, 1, 2]
  pdgood := [3, 13]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp13.out
    exact hp127.out
  a := [-4016031, 5800890, 3947802, -995940, -455856]
  b := [774177, 1758921, -2043785, -973846, 203978, 75976]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13

noncomputable def M127 : MaximalOrderCertificateOfUnramifiedLists 127 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [64, 56, 33, 85, 118, 0], [124, 124, 123, 126, 0, 6]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [64, 56, 33, 85, 118, 0], [59, 68, 13, 30, 39, 0], [109, 106, 100, 117, 126, 36]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [64, 56, 33, 85, 118, 0], [59, 68, 13, 30, 39, 0], [83, 84, 85, 26, 60, 0], [82, 72, 56, 106, 126, 89]], ![[0, 0, 0, 0, 1, 0], [64, 56, 33, 85, 118, 0], [59, 68, 13, 30, 39, 0], [83, 84, 85, 26, 60, 0], [30, 14, 32, 105, 121, 0], [50, 13, 64, 9, 115, 26]], ![[0, 0, 0, 0, 0, 1], [124, 124, 123, 126, 0, 6], [109, 106, 100, 117, 126, 36], [82, 72, 56, 106, 126, 89], [50, 13, 64, 9, 115, 26], [79, 70, 53, 102, 125, 96]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [127]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 127 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M127
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [127] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R665

namespace VoightMaximalOrderD6R673

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14513972, [-4, -8, 10, 9, -8, -1, 1], 2⟩
local notation "l" => [-4, -8, 10, 9, -8, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 1, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, -1, 0, -1, 2], ![2, 4, -6, -4, 3, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, -1, 0, -1, 2], ![4, 8, -11, -9, 7, 2], ![4, 10, -11, -14, -1, 10]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, -1, 0, -1, 2], ![4, 8, -11, -9, 7, 2], ![4, 12, -11, -19, -10, 18], ![20, 44, -49, -51, 17, 18]], ![![0, 0, 0, 0, 1, 0], ![0, 0, -1, 0, -1, 2], ![4, 8, -11, -9, 7, 2], ![4, 12, -11, -19, -10, 18], ![36, 76, -86, -83, 45, 16], ![36, 92, -81, -121, -14, 70]], ![![0, 0, 0, 0, 0, 1], ![2, 4, -6, -4, 3, 2], ![4, 10, -11, -14, -1, 10], ![20, 44, -49, -51, 17, 18], ![36, 92, -81, -121, -14, 70], ![90, 209, -203, -248, 44, 96]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-4, -2]], ![[], [], [], [-4], [-4, -4], [-20, -4, -2]], ![[], [], [-4], [-4, -4], [-36, -4, -4], [-36, -20, -4, -2]], ![[], [-2], [-4, -2], [-20, -4, -2], [-36, -20, -4, -2], [-90, -29, -12, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, -1, 0, -1, 2], [2, 4, -6, -4, 3, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, -1, 0, -1, 2], [4, 8, -11, -9, 7, 2], [4, 10, -11, -14, -1, 10]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, -1, 0, -1, 2], [4, 8, -11, -9, 7, 2], [4, 12, -11, -19, -10, 18], [20, 44, -49, -51, 17, 18]], ![[0, 0, 0, 0, 1, 0], [0, 0, -1, 0, -1, 2], [4, 8, -11, -9, 7, 2], [4, 12, -11, -19, -10, 18], [36, 76, -86, -83, 45, 16], [36, 92, -81, -121, -14, 70]], ![[0, 0, 0, 0, 0, 1], [2, 4, -6, -4, 3, 2], [4, 10, -11, -14, -1, 10], [20, 44, -49, -51, 17, 18], [36, 92, -81, -121, -14, 70], [90, 209, -203, -248, 44, 96]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp329863 : Fact (Nat.Prime 329863) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [5, 1, 4, 8]
  b' := [8, 9, 9, 10, 5]
  k := [2, 9, 2, 5, 1]
  f := [4, 7, 2, 6, 3, 1]
  g := [5, 8, 3, 9, 2, 1]
  h := [8, 1]
  a := [4, 3, 2, 3, 9]
  b := [8, 10, 7, 10, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD329863 : CertificateDedekindCriterionLists l 329863 where
  n := 2
  a' := [92334, 1794, 150191, 224967]
  b' := [142542, 283997, 172859, 58559, 218897]
  k := [15679, 155712, 147181, 143352, 1]
  f := [54373, 11059, 70762, 22657, 66891, 1]
  g := [192329, 39116, 250300, 80140, 236607, 1]
  h := [93255, 1]
  a := [70630, 24355, 57636, 42560, 229211]
  b := [306213, 292834, 306399, 317789, 100652]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 11, 329863]
  exp := ![2, 1, 1]
  pdgood := [11, 329863]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp11.out
    exact hp329863.out
  a := [-5702889, -53990, 30812355, -983148, -6700356]
  b := [1037198, 8322879, 1826942, -8295739, -22263, 1116726]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 329863 T_ofList CD329863

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 4
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0], [0, 0, 1, 1, 1, 0], [0, 0, 1, 0, 1, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0], [0, 0, 1, 1, 1, 0], [0, 0, 1, 1, 0, 0], [0, 0, 1, 1, 1, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0], [0, 0, 1, 1, 1, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0], [0, 0, 1, 1, 1, 0], [0, 0, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 0, 1, 1, 0], ![0, 0, 0, 1, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 0]]
  v := ![![0, 1, 0, 1, 1, 0], ![0, 0, 0, 1, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0]]
  v_ind := ![4, 5]
  w_ind := ![0, 2, 3, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 1, 0]]
  a := ![![![1, 0], ![0, 1]], ![![6, 92], ![65, 116]], ![![32, 58], ![4, 110]], ![![34, 36], ![-24, 88]], ![![38, 60], ![-2, 120]], ![![32, 56], ![0, 108]]]
  c := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![29, -68, -204, 67], ![56, -129, -338, 96]], ![![24, -60, -148, 38], ![33, -79, -237, 78]], ![![20, -49, -113, 27], ![20, -46, -166, 64]], ![![26, -66, -157, 39], ![34, -82, -250, 84]], ![![24, -60, -147, 38], ![32, -76, -232, 78]]]
  d := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![0, 2], ![-2, 20], ![36, 36], ![42, 40]], ![![2, 0], ![12, 8], ![-4, 40], ![-4, 44]], ![![2, 0], ![14, 4], ![-20, 36], ![-22, 40]], ![![2, 0], ![14, 8], ![-8, 44], ![-8, 48]], ![![2, 0], ![12, 8], ![-6, 40], ![-6, 44]]]
  e := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 0, -2, 1], ![4, -11, -33, 11], ![20, -49, -113, 26], ![22, -54, -123, 27]], ![![0, 0, 0, 0], ![4, -12, -20, 2], ![8, -22, -68, 22], ![8, -22, -70, 22]], ![![0, 0, 0, -1], ![4, -11, -19, 1], ![4, -11, -49, 22], ![4, -12, -51, 23]], ![![0, 1, 1, -1], ![4, -12, -21, 1], ![8, -23, -70, 24], ![8, -24, -71, 24]], ![![0, 0, 1, -1], ![4, -12, -21, 2], ![8, -22, -68, 23], ![8, -23, -70, 23]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inr 0, Sum.inr 1), (Sum.inr 3, Sum.inr 1)]
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

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R673

end TraceEuclidean
