import TraceEuclidean.VoightMaximalOrderCertificates.Chunk034
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

namespace VoightMaximalOrderD6R226

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6782000, [4, -24, 18, 10, -9, -1, 1], 4⟩
local notation "l" => [4, -24, 18, 10, -9, -1, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, -1, 2, 0], ![0, 0, 0, 0, 0, 1], ![-2, 12, -13, -10, 8, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, -1, 2, 0], ![0, 0, 1, 0, -2, 2], ![-2, 12, -13, -10, 8, 2], ![-4, 22, -4, -23, -4, 12]], ![![0, 0, 0, 1, 0, 0], ![0, 0, -1, -1, 2, 0], ![0, 0, 1, 0, -2, 2], ![-4, 24, -26, -19, 16, 2], ![-4, 22, -4, -23, -4, 12], ![-24, 140, -111, -101, 50, 20]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![-2, 12, -13, -10, 8, 2], ![-4, 22, -4, -23, -4, 12], ![-15, 87, -64, -67, 27, 17], ![-34, 189, -67, -167, 2, 61]], ![![0, 0, 0, 0, 0, 1], ![-2, 12, -13, -10, 8, 2], ![-4, 22, -4, -23, -4, 12], ![-24, 140, -111, -101, 50, 20], ![-34, 189, -67, -167, 2, 61], ![-122, 698, -437, -510, 154, 124]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [-4, -2]], ![[], [], [], [-4], [-4, -2], [-24, -4, -2]], ![[], [], [-2], [-4, -2], [-15, -3, -1], [-34, -15, -3, -1]], ![[], [-2], [-4, -2], [-24, -4, -2], [-34, -15, -3, -1], [-122, -34, -15, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 2, 0], [0, 0, 0, 0, 0, 1], [-2, 12, -13, -10, 8, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 2, 0], [0, 0, 1, 0, -2, 2], [-2, 12, -13, -10, 8, 2], [-4, 22, -4, -23, -4, 12]], ![[0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 2, 0], [0, 0, 1, 0, -2, 2], [-4, 24, -26, -19, 16, 2], [-4, 22, -4, -23, -4, 12], [-24, 140, -111, -101, 50, 20]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-2, 12, -13, -10, 8, 2], [-4, 22, -4, -23, -4, 12], [-15, 87, -64, -67, 27, 17], [-34, 189, -67, -167, 2, 61]], ![[0, 0, 0, 0, 0, 1], [-2, 12, -13, -10, 8, 2], [-4, 22, -4, -23, -4, 12], [-24, 140, -111, -101, 50, 20], [-34, 189, -67, -167, 2, 61], [-122, 698, -437, -510, 154, 124]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp3391 : Fact (Nat.Prime 3391) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 1]
  b' := [2, 1, 3]
  k := [1]
  f := [1, 6, -1, 0, 3, 1]
  g := [3, 1, 2, 1]
  h := [3, 1, 2, 1]
  a := [3, 3]
  b := [1, 1, 4, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3391 : CertificateDedekindCriterionLists l 3391 where
  n := 2
  a' := [503, 932, 2969, 3257]
  b' := [1552, 40, 3356, 1063, 705]
  k := [2510, 2400, 2895, 1429, 1]
  f := [2036, 1860, 778, 1461, 564, 1]
  g := [2580, 2356, 985, 1851, 714, 1]
  h := [2676, 1]
  a := [1190, 1348, 3036, 2108, 1430]
  b := [1754, 1040, 892, 2150, 1961]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 5, 3391]
  exp := ![2, 1, 1]
  pdgood := [5, 3391]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp3391.out
  a := [-83431, 36501, 127746, -9809, -24258]
  b := [-16731, 64418, -2070, -34254, 961, 4043]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3391 T_ofList CD3391

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 4
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 1, 1], [0, 1, 1, 1, 0, 1]], ![[0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 1, 1, 1, 0, 1], [0, 0, 1, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0]]
  v := ![![0, 1, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  v_ind := ![3, 5]
  w_ind := ![0, 1, 2, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 1, 0, 1], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0]]
  a := ![![![1, 0], ![0, 1]], ![![-186, 55], ![-821, 223]], ![![-134, 34], ![-530, 128]], ![![-154, 40], ![-644, 158]], ![![-20, 4], ![-102, 20]], ![![-20, 6], ![-124, 32]]]
  c := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![-58, 38, 174, -30], ![-204, 110, 748, -22]], ![![-43, 28, 134, -25], ![-148, 85, 528, -51]], ![![-52, 35, 156, -35], ![-181, 105, 640, -66]], ![![-10, 8, 23, -11], ![-38, 26, 116, -31]], ![![-10, 8, 22, -11], ![-38, 24, 123, -20]]]
  d := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![2, 2], ![-618, 226], ![-20, 6], ![-86, 38]], ![![0, 2], ![-398, 154], ![-20, 4], ![-64, 28]], ![![2, 2], ![-466, 184], ![-20, 4], ![-68, 32]], ![![2, 0], ![-46, 28], ![-2, 0], ![-2, 4]], ![![2, 0], ![-66, 32], ![0, 0], ![-2, 4]]]
  e := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 1, -1, -1], ![-111, 49, 421, 84], ![-12, 10, 23, -13], ![-22, 14, 57, 0]], ![![0, 0, 0, 0], ![-46, 6, 230, 110], ![-10, 8, 22, -10], ![-10, 4, 36, 12]], ![![0, 0, -2, 0], ![-58, 12, 266, 120], ![-12, 10, 24, -14], ![-12, 6, 36, 10]], ![![0, 0, 0, -1], ![0, -4, 12, 23], ![-2, 2, 1, -2], ![0, 0, -2, 1]], ![![0, 0, -1, 0], ![-12, 6, 35, 10], ![-2, 2, 1, -3], ![-2, 2, -1, -2]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 0, Sum.inr 2), (Sum.inl 1, Sum.inr 2)]
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

end VoightMaximalOrderD6R226

namespace VoightMaximalOrderD6R237

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7056125, [-1, -2, 16, 8, -10, -1, 1], 25⟩
local notation "l" => [-1, -2, 16, 8, -10, -1, 1]
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

def basisDenominator : ℤ := 5
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![5, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 5, 0, 0], ![4, 2, 4, 0, 1, 0], ![0, 4, 2, 4, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-4, -2, -4, 0, 5, 0], ![0, 0, 0, 0, 0, 1], ![-11, -6, -14, -2, 14, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-4, -2, -4, 0, 5, 0], ![0, -4, -2, -4, 0, 5], ![-11, -6, -14, -2, 14, 1], ![-3, -13, -12, -16, 4, 15]], ![![0, 0, 0, 1, 0, 0], ![-4, -2, -4, 0, 5, 0], ![0, -4, -2, -4, 0, 5], ![-39, -22, -58, -12, 50, 5], ![-3, -13, -12, -16, 4, 15], ![-101, -61, -159, -42, 130, 19]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![-11, -6, -14, -2, 14, 1], ![-3, -13, -12, -16, 4, 15], ![-29, -17, -43, -10, 38, 5], ![-15, -39, -47, -53, 20, 43]], ![![0, 0, 0, 0, 0, 1], ![-11, -6, -14, -2, 14, 1], ![-3, -13, -12, -16, 4, 15], ![-101, -61, -159, -42, 130, 19], ![-15, -39, -47, -53, 20, 43], ![-261, -167, -429, -133, 337, 63]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-5]], ![[], [], [], [], [-5], [-5, -5]], ![[], [], [], [-25], [-5, -5], [-75, -5, -5]], ![[], [], [-5], [-5, -5], [-19, -1, -1], [-25, -19, -1, -1]], ![[], [-5], [-5, -5], [-75, -5, -5], [-25, -19, -1, -1], [-215, -25, -19, -1, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-4, -2, -4, 0, 5, 0], [0, 0, 0, 0, 0, 1], [-11, -6, -14, -2, 14, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-4, -2, -4, 0, 5, 0], [0, -4, -2, -4, 0, 5], [-11, -6, -14, -2, 14, 1], [-3, -13, -12, -16, 4, 15]], ![[0, 0, 0, 1, 0, 0], [-4, -2, -4, 0, 5, 0], [0, -4, -2, -4, 0, 5], [-39, -22, -58, -12, 50, 5], [-3, -13, -12, -16, 4, 15], [-101, -61, -159, -42, 130, 19]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-11, -6, -14, -2, 14, 1], [-3, -13, -12, -16, 4, 15], [-29, -17, -43, -10, 38, 5], [-15, -39, -47, -53, 20, 43]], ![[0, 0, 0, 0, 0, 1], [-11, -6, -14, -2, 14, 1], [-3, -13, -12, -16, 4, 15], [-101, -61, -159, -42, 130, 19], [-15, -39, -47, -53, 20, 43], [-261, -167, -429, -133, 337, 63]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp2971 : Fact (Nat.Prime 2971) := fact_iff.2 (by norm_num)

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [12, 13, 14, 3]
  b' := [10, 18, 1, 3, 7]
  k := [2, 9, 4, 12, 1]
  f := [1, 2, 0, 0, 3, 1]
  g := [6, 10, 2, 2, 15, 1]
  h := [3, 1]
  a := [12, 3, 14, 4, 14]
  b := [14, 7, 12, 12, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2971 : CertificateDedekindCriterionLists l 2971 where
  n := 2
  a' := [1034, 1179, 1120, 2369]
  b' := [1038, 2662, 1172, 2936, 1903]
  k := [1996, 2495, 1007, 984, 1]
  f := [124, 574, 408, 221, 661, 1]
  g := [371, 1717, 1219, 660, 1977, 1]
  h := [993, 1]
  a := [1106, 992, 2287, 1574, 457]
  b := [1272, 2553, 2552, 2667, 2514]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [5] where
  n := 3
  p := ![5, 19, 2971]
  exp := ![3, 1, 1]
  pdgood := [19, 2971]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp2971.out
  a := [-6326569, -5985168, 9461862, 1258676, -1463136]
  b := [-364778, 3482705, 1987629, -2388736, -250422, 243856]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2971 T_ofList CD2971

noncomputable def M5 : MaximalOrderCertificateLists 5 O Om hm where
  m := 3
  n := 3
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 3, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1], [4, 4, 1, 3, 4, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 3, 1, 0, 0, 0], [0, 1, 3, 1, 0, 0], [4, 4, 1, 3, 4, 1], [2, 2, 3, 4, 4, 0]], ![[0, 0, 0, 1, 0, 0], [1, 3, 1, 0, 0, 0], [0, 1, 3, 1, 0, 0], [1, 3, 2, 3, 0, 0], [2, 2, 3, 4, 4, 0], [4, 4, 1, 3, 0, 4]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [4, 4, 1, 3, 4, 1], [2, 2, 3, 4, 4, 0], [1, 3, 2, 0, 3, 0], [0, 1, 3, 2, 0, 3]], ![[0, 0, 0, 0, 0, 1], [4, 4, 1, 3, 4, 1], [2, 2, 3, 4, 4, 0], [4, 4, 1, 3, 0, 4], [0, 1, 3, 2, 0, 3], [4, 3, 1, 2, 2, 3]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![3, 3, 2, 1, 0, 0], ![4, 2, 3, 0, 1, 0], ![1, 0, 1, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![4, 0, 1, 0, 0, 0], ![1, 1, 0, 0, 0, 0]]
  v := ![![3, 3, 2, 1, 0, 0], ![4, 2, 3, 0, 1, 0], ![1, 0, 1, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![4, 0, 1, 0, 0, 0], ![1, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 2, 0, 0], ![0, 0, 1, 3, 0, 0]]
  v_ind := ![3, 4, 5]
  w_ind := ![0, 1, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![1, 1, 2, 3, 0, 3], ![4, 1, 3, 4, 2, 0], ![2, 3, 2, 3, 2, 0], ![4, 0, 0, 2, 2, 0], ![3, 0, 3, 0, 0, 3]]
  a := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-290, 760, 220], ![-384, 281, 375], ![-615, 1445, 341]], ![![-105, 365, 115], ![-125, 315, 144], ![-339, 631, 234]], ![![-85, 300, 95], ![-95, 270, 115], ![-280, 520, 195]], ![![-70, 200, 70], ![-80, 200, 80], ![-200, 330, 140]], ![![-240, 570, 180], ![-315, 270, 285], ![-495, 1050, 285]]]
  c := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![1885, -566, -217], ![565, -180, 43], ![3520, -1059, -363]], ![![930, -278, -124], ![775, -233, -93], ![1500, -454, -129]], ![![761, -228, -102], ![675, -203, -84], ![1235, -374, -106]], ![![500, -150, -60], ![486, -146, -56], ![770, -234, -56]], ![![1395, -420, -150], ![540, -171, 21], ![2526, -762, -240]]]
  d := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![15, 0, 15], ![-235, 110, 360], ![-5, 285, 30]], ![![20, 10, 0], ![-15, 255, 110], ![35, 110, 10]], ![![15, 10, 0], ![-5, 230, 85], ![25, 85, 10]], ![![10, 10, 0], ![-20, 180, 60], ![10, 60, 10]], ![![0, 0, 15], ![-240, 135, 285], ![-15, 210, 30]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![25, -7, -8], ![262, -85, 46], ![762, -226, -133]], ![![43, -11, -15], ![692, -201, -123], ![321, -94, -68]], ![![35, -10, -10], ![625, -185, -105], ![235, -70, -50]], ![![40, -10, -10], ![490, -140, -80], ![170, -50, -30]], ![![0, 0, 0], ![225, -75, 45], ![555, -165, -90]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 2, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [5]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 5 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M5
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [5] D q hq hbad)
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

end VoightMaximalOrderD6R237

namespace VoightMaximalOrderD6R246

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7310125, [-1, -6, 13, 7, -8, -1, 1], 5⟩
local notation "l" => [-1, -6, 13, 7, -8, -1, 1]
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

def basisDenominator : ℤ := 5
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![5, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 5, 0, 0], ![0, 0, 0, 0, 5, 0], ![2, 1, 1, 3, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -1, -1, -3, -2, 5], ![-1, 1, -3, -3, 1, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -1, -1, -3, -2, 5], ![-1, 5, -14, -10, 6, 5], ![-5, 1, -9, -15, -2, 14]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -1, -1, -3, -2, 5], ![-1, 5, -14, -10, 6, 5], ![-17, -2, -16, -47, -17, 45], ![-10, 11, -39, -45, 3, 32]], ![![0, 0, 0, 0, 1, 0], ![-2, -1, -1, -3, -2, 5], ![-1, 5, -14, -10, 6, 5], ![-17, -2, -16, -47, -17, 45], ![-11, 45, -120, -100, 32, 50], ![-38, 19, -88, -144, -19, 111]], ![![0, 0, 0, 0, 0, 1], ![-1, 1, -3, -3, 1, 3], ![-5, 1, -9, -15, -2, 14], ![-10, 11, -39, -45, 3, 32], ![-38, 19, -88, -144, -19, 111], ![-37, 33, -120, -161, -5, 115]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-5]], ![[], [], [], [], [-25], [-15, -5]], ![[], [], [], [-25], [-25, -25], [-70, -15, -5]], ![[], [], [-25], [-25, -25], [-225, -25, -25], [-160, -70, -15, -5]], ![[], [-5], [-15, -5], [-70, -15, -5], [-160, -70, -15, -5], [-221, -70, -23, -5, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -1, -1, -3, -2, 5], [-1, 1, -3, -3, 1, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -1, -1, -3, -2, 5], [-1, 5, -14, -10, 6, 5], [-5, 1, -9, -15, -2, 14]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -1, -1, -3, -2, 5], [-1, 5, -14, -10, 6, 5], [-17, -2, -16, -47, -17, 45], [-10, 11, -39, -45, 3, 32]], ![[0, 0, 0, 0, 1, 0], [-2, -1, -1, -3, -2, 5], [-1, 5, -14, -10, 6, 5], [-17, -2, -16, -47, -17, 45], [-11, 45, -120, -100, 32, 50], [-38, 19, -88, -144, -19, 111]], ![[0, 0, 0, 0, 0, 1], [-1, 1, -3, -3, 1, 3], [-5, 1, -9, -15, -2, 14], [-10, 11, -39, -45, 3, 32], [-38, 19, -88, -144, -19, 111], [-37, 33, -120, -161, -5, 115]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp58481 : Fact (Nat.Prime 58481) := fact_iff.2 (by norm_num)

def CD58481 : CertificateDedekindCriterionLists l 58481 where
  n := 2
  a' := [43263, 27090, 3885, 27664]
  b' := [51650, 5113, 25026, 47595, 41252]
  k := [54218, 54401, 52230, 22457, 1]
  f := [25669, 15703, 9049, 42540, 9073, 1]
  g := [31769, 19434, 11199, 52649, 11228, 1]
  h := [47252, 1]
  a := [28497, 56908, 47227, 54013, 1247]
  b := [14660, 16453, 32709, 1627, 57234]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [5] where
  n := 2
  p := ![5, 58481]
  exp := ![3, 1]
  pdgood := [58481]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp58481.out
  a := [-4236391, -2455086, 6508544, 552596, -1345848]
  b := [-512289, 2425653, 909633, -1698716, -129484, 224308]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 58481 T_ofList CD58481

noncomputable def M5 : MaximalOrderCertificateLists 5 O Om hm where
  m := 3
  n := 3
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [3, 4, 4, 2, 3, 0], [4, 1, 2, 2, 1, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [3, 4, 4, 2, 3, 0], [4, 0, 1, 0, 1, 0], [0, 1, 1, 0, 3, 4]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [3, 4, 4, 2, 3, 0], [4, 0, 1, 0, 1, 0], [3, 3, 4, 3, 3, 0], [0, 1, 1, 0, 3, 2]], ![[0, 0, 0, 0, 1, 0], [3, 4, 4, 2, 3, 0], [4, 0, 1, 0, 1, 0], [3, 3, 4, 3, 3, 0], [4, 0, 0, 0, 2, 0], [2, 4, 2, 1, 1, 1]], ![[0, 0, 0, 0, 0, 1], [4, 1, 2, 2, 1, 3], [0, 1, 1, 0, 3, 4], [0, 1, 1, 0, 3, 2], [2, 4, 2, 1, 1, 1], [3, 3, 0, 4, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![3, 4, 2, 1, 0, 0], ![4, 0, 0, 0, 1, 0], ![1, 2, 2, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![1, 4, 4, 0, 0, 0], ![2, 0, 1, 0, 0, 0]]
  v := ![![3, 4, 2, 1, 0, 0], ![4, 0, 0, 0, 1, 0], ![1, 2, 2, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![1, 4, 4, 0, 0, 0], ![2, 0, 1, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 3, 0, 0], ![0, 0, 1, 0, 2, 0]]
  v_ind := ![3, 4, 5]
  w_ind := ![0, 1, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![16, 12, 8, 4, 8, 12], ![16, 16, 0, 4, 4, 0], ![12, 0, 4, 8, 16, 4], ![4, 4, 12, 16, 4, 0], ![8, 8, 0, 4, 0, 16]]
  a := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-1680, -8, 1600], ![-2816, 32, 2060], ![-4040, -148, 3180]], ![![-320, 0, 360], ![-620, 60, 460], ![-896, -20, 756]], ![![-1700, -100, 1640], ![-2560, 400, 1640], ![-3960, -180, 3100]], ![![-500, 60, 600], ![-1220, -60, 1000], ![-1640, -20, 1380]], ![![-1420, 80, 1260], ![-2500, -380, 2060], ![-3360, -100, 2600]]]
  c := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![2355, 193, -976], ![4130, 390, -1692], ![5860, 528, -2344]], ![![445, 35, -188], ![935, 89, -404], ![1290, 114, -524]], ![![2374, 186, -948], ![3760, 388, -1672], ![5740, 516, -2280]], ![![640, 44, -296], ![1769, 155, -704], ![2340, 204, -956]], ![![2005, 175, -860], ![3670, 310, -1360], ![4899, 445, -1968]]]
  d := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![20, 40, 60], ![-6220, 520, 6140], ![-1260, 200, 1260]], ![![20, 20, 0], ![-940, 260, 1200], ![-140, 120, 200]], ![![40, 80, 20], ![-5960, 1200, 5380], ![-1140, 540, 920]], ![![80, 20, 0], ![-1600, 260, 2400], ![-260, 60, 500]], ![![20, 0, 80], ![-5820, -400, 5920], ![-1180, -200, 1380]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-41, -7, 4], ![8435, 701, -3724], ![1692, 144, -768]], ![![4, 0, -8], ![1216, 100, -632], ![244, 20, -148]], ![![-110, -10, 20], ![8110, 730, -3820], ![1445, 155, -780]], ![![-125, -15, 40], ![1855, 85, -920], ![295, 5, -160]], ![![-10, -10, 0], ![8010, 610, -3200], ![1695, 105, -640]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 2, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [5]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 5 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M5
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [5] D q hq hbad)
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

end VoightMaximalOrderD6R246

namespace VoightMaximalOrderD6R249

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7328637, [-3, -18, 12, 16, -6, -3, 1], 3⟩
local notation "l" => [-3, -18, 12, 16, -6, -3, 1]
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

def basisDenominator : ℤ := 3
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 3, 0], ![0, 0, 0, 1, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, -1, -2, 3], ![1, 6, -4, -7, -1, 5]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, -1, -2, 3], ![3, 18, -12, -19, 0, 9], ![5, 31, -14, -38, -10, 22]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, -1, -2, 3], ![3, 18, -12, -19, 0, 9], ![9, 57, -18, -75, -28, 45], ![22, 137, -57, -158, -40, 80]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, -1, -2, 3], ![3, 18, -12, -19, 0, 9], ![9, 57, -18, -75, -28, 45], ![45, 279, -123, -305, -64, 141], ![80, 502, -183, -577, -158, 280]], ![![0, 0, 0, 0, 0, 1], ![1, 6, -4, -7, -1, 5], ![5, 31, -14, -38, -10, 22], ![22, 137, -57, -158, -40, 80], ![80, 502, -183, -577, -158, 280], ![154, 967, -347, -1099, -299, 522]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-3]], ![[], [], [], [], [-9], [-15, -3]], ![[], [], [], [-9], [-27, -9], [-66, -15, -3]], ![[], [], [-9], [-27, -9], [-135, -27, -9], [-240, -66, -15, -3]], ![[], [-3], [-15, -3], [-66, -15, -3], [-240, -66, -15, -3], [-462, -129, -33, -7, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, -1, -2, 3], [1, 6, -4, -7, -1, 5]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, -1, -2, 3], [3, 18, -12, -19, 0, 9], [5, 31, -14, -38, -10, 22]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, -1, -2, 3], [3, 18, -12, -19, 0, 9], [9, 57, -18, -75, -28, 45], [22, 137, -57, -158, -40, 80]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, -1, -2, 3], [3, 18, -12, -19, 0, 9], [9, 57, -18, -75, -28, 45], [45, 279, -123, -305, -64, 141], [80, 502, -183, -577, -158, 280]], ![[0, 0, 0, 0, 0, 1], [1, 6, -4, -7, -1, 5], [5, 31, -14, -38, -10, 22], [22, 137, -57, -158, -40, 80], [80, 502, -183, -577, -158, 280], [154, 967, -347, -1099, -299, 522]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp1117 : Fact (Nat.Prime 1117) := fact_iff.2 (by norm_num)

def CD1117 : CertificateDedekindCriterionLists l 1117 where
  n := 2
  a' := [1064, 146, 1077, 695]
  b' := [893, 981, 276, 429, 978]
  k := [444, 251, 1074, 37, 1]
  f := [55, 991, 1092, 329, 17, 1]
  g := [56, 1009, 1111, 334, 17, 1]
  h := [1097, 1]
  a := [882, 357, 57, 801, 732]
  b := [909, 16, 252, 316, 385]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 2
  p := ![3, 1117]
  exp := ![3, 1]
  pdgood := [1117]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp1117.out
  a := [12663, -35184, -18102, 36420, -9408]
  b := [-3786, -11847, 20751, 956, -6854, 1568]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1117 T_ofList CD1117

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 4
  n := 2
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 1, 0], [1, 0, 2, 2, 2, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 1, 0], [0, 0, 0, 2, 0, 0], [2, 1, 1, 1, 2, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 1, 0], [0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0], [1, 2, 0, 1, 2, 2]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 1, 0], [0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0], [0, 0, 0, 1, 2, 0], [2, 1, 0, 2, 1, 1]], ![[0, 0, 0, 0, 0, 1], [1, 0, 2, 2, 2, 2], [2, 1, 1, 1, 2, 1], [1, 2, 0, 1, 2, 2], [2, 1, 0, 2, 1, 1], [1, 1, 1, 2, 1, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![2, 2, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![0, 1, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![2, 2, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 1], ![0, 0, 1, 0, 0, 0], ![1, 2, 0, 0, 1, 2], ![0, 0, 1, 0, 2, 0], ![0, 0, 0, 2, 2, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-18, -45, -11, 30], ![-77, -190, -42, 102], ![-217, -677, -186, 339], ![-424, -1305, -349, 636]], ![![0, 1, 1, 0], ![0, 1, -2, 3], ![-12, -18, 0, 9], ![-12, -36, -10, 22]], ![![-45, -108, -24, 66], ![-144, -420, -114, 231], ![-495, -1476, -387, 720], ![-897, -2819, -764, 1365]], ![![-24, -39, -3, 24], ![-36, -153, -66, 105], ![-258, -630, -132, 297], ![-378, -1194, -330, 594]], ![![-24, -42, -6, 30], ![-60, -192, -60, 120], ![-282, -762, -186, 378], ![-480, -1470, -396, 732]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-18, 32], ![-59, 154], ![-195, 554], ![-363, 1086]], ![![0, -1], ![-2, -2], ![-5, 16], ![-13, 27]], ![![-39, 82], ![-135, 331], ![-411, 1230], ![-778, 2349]], ![![-14, 31], ![-64, 104], ![-167, 544], ![-341, 981]], ![![-18, 30], ![-72, 138], ![-216, 636], ![-420, 1210]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![3, 3, 0, 3], ![-12, -18, 0, 15]], ![![3, 0, 0, 0], ![0, 3, 0, 0]], ![![0, 0, 3, 6], ![-18, -45, -12, 39]], ![![3, 0, 6, 0], ![0, -3, -12, 18]], ![![0, 6, 6, 0], ![0, -6, -6, 18]]]
  e := ![![![1, 0], ![0, 1]], ![![-2, -5], ![-9, 12]], ![![0, -1], ![0, -2]], ![![-3, -3], ![-24, 27]], ![![0, -3], ![-12, -6]], ![![0, -6], ![-12, -6]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 3, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 3, Sum.inr 1)]
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

end VoightMaximalOrderD6R249

end TraceEuclidean
