module

public import ComparisonSelectedUnitEndpointCoordinates
public import ComparisonCapSideTraceWall
public import ComparisonCapSideTraceTerminal
public import ComparisonContactCover
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2400000

def nativeDyadicMass (U : ℝ) (j : ℕ) : ℝ := U*(2:ℝ)^j

theorem nativeDyadicMass_pos {U : ℝ} (hU : 0 < U) (j : ℕ) :
    0 < nativeDyadicMass U j := by unfold nativeDyadicMass;positivity

theorem nativeDyadicMass_add (U : ℝ) (j k : ℕ) :
    nativeDyadicMass U (j+k)=nativeDyadicMass U j*(2:ℝ)^k := by
  simp only [nativeDyadicMass,pow_add];ring

theorem nativeDyadicMass_monotone {U : ℝ} (hU : 0 ≤ U) : Monotone (nativeDyadicMass U) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij) hU

theorem nativeDyadicMass_ge_base {U : ℝ} (hU : 0 ≤ U) (j : ℕ) :
    U ≤ nativeDyadicMass U j := by
  simpa only [nativeDyadicMass,pow_zero,mul_one] using
    nativeDyadicMass_monotone hU (Nat.zero_le j)

theorem nativeDyadicMass_exists_near {U s : ℝ} (hU : 0 < U) (hUs : U ≤ s) :
    ∃k : ℕ,nativeDyadicMass U k ≤ s ∧ s < nativeDyadicMass U (k+1) := by
  obtain ⟨k,hk,hk1⟩ := exists_nat_pow_near
    ((le_div_iff₀ hU).mpr (by simpa using hUs)) (by norm_num : (1:ℝ) < 2)
  exact ⟨k,by simpa only [nativeDyadicMass,mul_comm] using
    ((le_div_iff₀ hU).mp hk),by simpa only [nativeDyadicMass,mul_comm] using
    ((div_lt_iff₀ hU).mp hk1)⟩

theorem native_cap_broad_comparable_or_near_zero {U A B : ℝ}
    (hU : 0 < U) (_hA : 0 ≤ A) (_hAB : A < B) :
    B ≤ 8*U ∨
    (U ≤ A ∧ (B+U) ≤ 9*(A+U)) ∨
    8*max A U < B := by
  by_cases hb : 8*max A U < B
  · exact Or.inr (Or.inr hb)
  · have hb' : B ≤ 8*max A U := le_of_not_gt hb
    by_cases ha : A < U
    · exact Or.inl (by simpa only [max_eq_right ha.le] using hb')
    · have hUA : U ≤ A := le_of_not_gt ha
      exact Or.inr (Or.inl ⟨hUA,by rw [max_eq_left hUA] at hb';linarith⟩)

theorem native_comparable_cap_dyadic_enlargement {U A B : ℝ} {k : ℕ}
    (hU : 0 < U) (_hUA : U ≤ A) (hB : B ≤ 8*A)
    (hk : nativeDyadicMass U k ≤ A) (hk1 : A < nativeDyadicMass U (k+1)) :
    let v := nativeDyadicMass U k
    U ≤ v ∧ v ≤ A ∧ B ≤ 16*v ∧ (16*v+U) ≤ 32*(v/2+U) := by
  dsimp only
  have hp := nativeDyadicMass_pos hU k
  have he : nativeDyadicMass U (k+1)=2*nativeDyadicMass U k := by
    rw [nativeDyadicMass_add];norm_num;ring
  rw [he] at hk1
  exact ⟨nativeDyadicMass_ge_base hU.le k,hk,by linarith,by linarith⟩

def nativeBroadSliceCount (k m : ℕ) : ℕ := m-k-1

def nativeBroadSliceNode (U s B : ℝ) (k m i : ℕ) : ℝ :=
  if i=0 then s else if i<nativeBroadSliceCount k m then nativeDyadicMass U (k+1+i) else B

def nativeBroadSliceScale (U : ℝ) (k m : ℕ) (i : Fin (nativeBroadSliceCount k m)) : ℝ :=
  if i.val=0 then nativeDyadicMass U (k+1) else nativeDyadicMass U (k+1+i.val)

theorem native_broad_dyadic_index_gap {U s B : ℝ} {k m : ℕ}
    (hU : 0 < U) (hs : nativeDyadicMass U k ≤ s)
    (hB : B < nativeDyadicMass U (m+1)) (hbroad : 8*s < B) :
    k+3 ≤ m := by
  have hgap : nativeDyadicMass U (k+3) < B := by
    rw [nativeDyadicMass_add]
    norm_num
    linarith
  by_contra hno
  have hidx : m+1 ≤ k+3 := by omega
  exact (hgap.trans hB).not_ge (nativeDyadicMass_monotone hU.le hidx)

theorem nativeBroadSliceNode_endpoints (U s B : ℝ) {k m : ℕ} (hgap : k+3 ≤ m) :
    nativeBroadSliceNode U s B k m 0=s ∧
      nativeBroadSliceNode U s B k m (nativeBroadSliceCount k m)=B := by
  have hcount : 2 ≤ nativeBroadSliceCount k m := by unfold nativeBroadSliceCount;omega
  simp [nativeBroadSliceNode,show nativeBroadSliceCount k m ≠ 0 by omega]

theorem nativeBroadSlice_geometry {U s B : ℝ} {k m : ℕ}
    (hU : 0 < U) (hs : nativeDyadicMass U k ≤ s)
    (hs1 : s < nativeDyadicMass U (k+1))
    (hBm : nativeDyadicMass U m ≤ B) (hBm1 : B < nativeDyadicMass U (m+1))
    (hgap : k+3 ≤ m) (i : Fin (nativeBroadSliceCount k m)) :
    let v := nativeBroadSliceScale U k m i
    let l := nativeBroadSliceNode U s B k m i.val
    let r := nativeBroadSliceNode U s B k m (i.val+1)
    U ≤ v ∧ v ≤ r-l ∧ v/2 ≤ l ∧ r ≤ 4*v ∧ s ≤ l ∧ r ≤ B ∧ l < r := by
  dsimp only
  have hcount : 2 ≤ nativeBroadSliceCount k m := by unfold nativeBroadSliceCount;omega
  have hmono := nativeDyadicMass_monotone hU.le
  have hpow1 j : nativeDyadicMass U (j+1)=2*nativeDyadicMass U j := by
    rw [nativeDyadicMass_add];norm_num;ring
  by_cases hi : i.val=0
  · have hnode0 : nativeBroadSliceNode U s B k m i.val=s := by
      simp only [nativeBroadSliceNode,hi,ite_true]
    have hnode1 : nativeBroadSliceNode U s B k m (i.val+1)=nativeDyadicMass U (k+2) := by
      simp only [hi,nativeBroadSliceNode,Nat.zero_add,show (1:ℕ)≠0 by omega,
        ite_false,show (1:ℕ)<nativeBroadSliceCount k m by omega,ite_true]
    rw [nativeBroadSliceScale,ite_eq_left hi,hnode0,hnode1]
    have hpow2 : nativeDyadicMass U (k+2)=2*nativeDyadicMass U (k+1) := by
      simpa only [Nat.add_assoc] using hpow1 (k+1)
    have hbase := nativeDyadicMass_ge_base hU.le (k+1)
    have hbound := (hmono (show k+2 ≤ m by omega)).trans hBm
    have hv0 := nativeDyadicMass_pos hU (k+1)
    rw [hpow1 k] at hs1
    rw [hpow2]
    refine ⟨hbase,?_,?_,?_,le_rfl,?_,?_⟩ <;> nlinarith [hpow1 k]
  · have hil : i.val < nativeBroadSliceCount k m := i.isLt
    have hnode : nativeBroadSliceNode U s B k m i.val=nativeDyadicMass U (k+1+i.val) := by
      simp only [nativeBroadSliceNode,hi,ite_false,hil,ite_true]
    rw [nativeBroadSliceScale,ite_eq_right hi,hnode]
    have hbase := nativeDyadicMass_ge_base hU.le (k+1+i.val)
    have hv0 := nativeDyadicMass_pos hU (k+1+i.val)
    have hsle : s ≤ nativeDyadicMass U (k+1+i.val) := hs1.le.trans
      (hmono (by omega))
    by_cases hi1 : i.val+1 < nativeBroadSliceCount k m
    · have hnode1 : nativeBroadSliceNode U s B k m (i.val+1)=
          2*nativeDyadicMass U (k+1+i.val) := by
        simp only [nativeBroadSliceNode,show i.val+1≠0 by omega,ite_false,hi1,ite_true]
        simpa only [Nat.add_assoc] using hpow1 (k+1+i.val)
      rw [hnode1]
      have hb := (hmono (show k+1+i.val+1 ≤ m by
        unfold nativeBroadSliceCount at hi1;omega)).trans hBm
      rw [hpow1] at hb
      refine ⟨hbase,?_,?_,?_,hsle,hb,?_⟩ <;> nlinarith
    · have heq : k+1+i.val+1=m := by unfold nativeBroadSliceCount at hil hi1;omega
      have hBm' : 2*nativeDyadicMass U (k+1+i.val) ≤ B := by
        simpa only [←heq,hpow1] using hBm
      have hBm1' : B < 4*nativeDyadicMass U (k+1+i.val) := by
        rw [←heq,hpow1,hpow1] at hBm1
        nlinarith
      rw [nativeBroadSliceNode,ite_eq_right (by omega : i.val+1≠0),ite_eq_right hi1]
      exact ⟨hbase,by linarith,by linarith,by linarith,hsle,le_rfl,by linarith⟩

theorem native_broad_cap_exists_dyadic_geometry {U A B : ℝ}
    (hU : 0 < U) (hbroad : 8*max A U < B) :
    ∃k m : ℕ,k+3 ≤ m ∧
      (∀i : Fin (nativeBroadSliceCount k m),
        let v := nativeBroadSliceScale U k m i
        let l := nativeBroadSliceNode U (max A U) B k m i.val
        let r := nativeBroadSliceNode U (max A U) B k m (i.val+1)
        U ≤ v ∧ v ≤ r-l ∧ v/2 ≤ l ∧ r ≤ 4*v ∧ max A U ≤ l ∧ r ≤ B ∧ l < r) := by
  obtain ⟨k,hk,hk1⟩ := nativeDyadicMass_exists_near hU (le_max_right A U)
  have hUB : U ≤ B := (le_max_right A U).trans (by
    have hp : 0 < max A U := hU.trans_le (le_max_right A U)
    linarith)
  obtain ⟨m,hm,hm1⟩ := nativeDyadicMass_exists_near hU hUB
  have hgap := native_broad_dyadic_index_gap hU hk hm1 hbroad
  exact ⟨k,m,hgap,fun i=>nativeBroadSlice_geometry hU hk hk1 hm hm1 hgap i⟩

theorem nativeBroadSlice_cover (U s B : ℝ) {k m : ℕ} (hgap : k+3 ≤ m)
    {t : ℝ} (ht : t∈Ioc s B) :
    ∃i : Fin (nativeBroadSliceCount k m),t∈Ioc
      (nativeBroadSliceNode U s B k m i.val)
      (nativeBroadSliceNode U s B k m (i.val+1)) := by
  have he := nativeBroadSliceNode_endpoints U s B hgap
  have hc := contactMeetingCells_cover (fun _ : ℝ=>0) id
    (nativeBroadSliceNode U s B k m) (nativeBroadSliceCount k m)
    (by simpa only [id_eq,he.1] using ht.1) (by simpa only [id_eq,he.2] using ht.2) rfl
  obtain ⟨i,hi,_,hr⟩ := hc
  exact ⟨⟨i,hi⟩,hr⟩

theorem nativeBroadSlice_mass_sum (U s B : ℝ) {k m : ℕ} (hgap : k+3 ≤ m) :
    (∑i : Fin (nativeBroadSliceCount k m),
      (nativeBroadSliceNode U s B k m (i.val+1)-nativeBroadSliceNode U s B k m i.val))=B-s := by
  let nodes := nativeBroadSliceNode U s B k m
  have he := nativeBroadSliceNode_endpoints U s B hgap
  have hh := WholeUnitSideKernel.finite_unit_coordinate_eq_cumulative (fun j=>nodes j-s)
    (fun i : Fin (nativeBroadSliceCount k m)=>nodes (i.val+1)-nodes i.val)
    (by change nativeBroadSliceNode U s B k m 0-s=0;rw [he.1];ring)
    (fun _=>by ring) (nativeBroadSliceCount k m) le_rfl
  simpa only [nodes,Fin.is_lt,ite_true,he.2] using hh.symm

theorem nativeBroadSlice_pairwise_disjoint {U s B : ℝ} {k m : ℕ}
    (hU : 0 < U) (hs : nativeDyadicMass U k ≤ s)
    (hs1 : s < nativeDyadicMass U (k+1))
    (hBm : nativeDyadicMass U m ≤ B) (hBm1 : B < nativeDyadicMass U (m+1))
    (hgap : k+3 ≤ m) :
    Pairwise (fun i j : Fin (nativeBroadSliceCount k m)=>Disjoint
      (Ioc (nativeBroadSliceNode U s B k m i.val) (nativeBroadSliceNode U s B k m (i.val+1)))
      (Ioc (nativeBroadSliceNode U s B k m j.val) (nativeBroadSliceNode U s B k m (j.val+1)))) := by
  let nodes := nativeBroadSliceNode U s B k m
  have hstep : ∀i<nativeBroadSliceCount k m,nodes i < nodes (i+1) := by
    intro i hi
    exact (nativeBroadSlice_geometry hU hs hs1 hBm hBm1 hgap ⟨i,hi⟩).2.2.2.2.2.2
  have hm := WholeUnitSideKernel.unitPoints_monotoneOn nodes (fun i hi=>(hstep i hi).le)
  intro i j hne
  apply Set.disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hne with hij|hji
  · have hh := hm ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
      (show i.val+1 ≤ j.val by exact Nat.succ_le_of_lt hij)
    linarith [hi.2,hj.1]
  · have hh := hm ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
      (show j.val+1 ≤ i.val by exact Nat.succ_le_of_lt hji)
    linarith [hj.2,hi.1]

theorem nativeBroadSlice_scale_inside_original {U A s B : ℝ} {k m : ℕ}
    (hU : 0 < U) (hAs : A ≤ s) (hs : nativeDyadicMass U k ≤ s)
    (hs1 : s < nativeDyadicMass U (k+1))
    (hBm : nativeDyadicMass U m ≤ B) (hBm1 : B < nativeDyadicMass U (m+1))
    (hgap : k+3 ≤ m) (i : Fin (nativeBroadSliceCount k m)) :
    nativeBroadSliceScale U k m i∈Ioo A B := by
  have hg := nativeBroadSlice_geometry hU hs hs1 hBm hBm1 hgap i
  have hv0 := hU.trans_le hg.1
  constructor
  · unfold nativeBroadSliceScale
    split_ifs
    · exact hAs.trans_lt hs1
    · exact (hAs.trans_lt hs1).trans_le
        (nativeDyadicMass_monotone hU.le (by omega))
  · linarith [hg.2.1,hg.2.2.1,hg.2.2.2.2.2.1]

theorem native_crossing_components_card_le_one {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (A B : ι→ℝ)
    (hdisjoint : Pairwise (fun i j=>Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j))))
    (v : ℝ) : (F.filter (fun i=>v∈Ioo (A i) (B i))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  exact Set.disjoint_left.mp (hdisjoint hne)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def nativeBroadMassSlice (α : inverseIntegralConstraints 0 0 k M) (l r : ℝ) : Set ℝ :=
  Ioo (comparisonSweepQuantile hc hk hkc hm hM α l)
    (comparisonSweepQuantile hc hk hkc hm hM α r)

theorem nativeBroadMassSlice_mass (α : inverseIntegralConstraints 0 0 k M)
    {l r : ℝ} (hl : l∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1) (hlr : l<r) :
    (∫t in nativeBroadMassSlice hc hk hkc hm hM α l r,deriv α.val.val t)=r-l := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  have hR : Monotone R := comparisonSweepQuantile_monotone hc hk hkc hm hM α
  have hstrict : R l < R r := lt_of_le_of_ne (hR hlr.le) (by
    intro he
    have hh := congrArg α.val.val he
    rw [comparisonSweepQuantile_spec hc hk hkc hm hM α hl,
      comparisonSweepQuantile_spec hc hk hkc hm hM α hr] at hh
    exact hlr.ne hh)
  have hsub : Icc (R l) (R r)⊆Icc (0:ℝ) 1 :=
    Icc_subset_Icc (comparisonSweepQuantile_bounds hc hk hkc hm hM α l).1
      (comparisonSweepQuantile_bounds hc hk hkc hm hM α r).2
  have hac : AbsolutelyContinuousOnInterval α.val.val (R l) (R r) := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hstrict.le] using
      (inverseIntegralConstraints_lipschitz hm hM α.property).mono hsub
  rw [nativeBroadMassSlice,←integral_Ioc_eq_integral_Ioo,
    ←intervalIntegral.integral_of_le hstrict.le,hac.integral_deriv_eq_sub,
    comparisonSweepQuantile_spec hc hk hkc hm hM α hl,
    comparisonSweepQuantile_spec hc hk hkc hm hM α hr]

theorem nativeBroadMassSlice_mass_ceiling (α : inverseIntegralConstraints 0 0 k M)
    {l r t : ℝ} (hr : r∈Icc (0:ℝ) 1)
    (ht : t∈nativeBroadMassSlice hc hk hkc hm hM α l r) : α.val.val t ≤ r := by
  have hh := α.val.property.2 ht.2.le
  rw [comparisonSweepQuantile_spec hc hk hkc hm hM α hr] at hh
  exact hh

theorem nativeBroadMassSlice_subset_cap (α : inverseIntegralConstraints 0 0 k M)
    {a z l r : ℝ} (ha : a∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1)
    (hl : α.val.val a ≤ l) (hr : r ≤ α.val.val z) :
    nativeBroadMassSlice hc hk hkc hm hM α l r⊆Ioo a z := by
  intro t ht
  have hR := comparisonSweepQuantile_monotone hc hk hkc hm hM α
  have hlo := hR hl
  have hhi := hR hr
  rw [comparisonSweepQuantile_at_profile hc hk hkc hm hM α ha] at hlo
  rw [comparisonSweepQuantile_at_profile hc hk hkc hm hM α hz] at hhi
  exact ⟨hlo.trans_lt ht.1,ht.2.trans_le hhi⟩

theorem nativeBroadMassSlice_broad_contracts (α : inverseIntegralConstraints 0 0 k M)
    {U s B : ℝ} {k m : ℕ}
    (hU : 0 < U) (hs : nativeDyadicMass U k ≤ s)
    (hs1 : s < nativeDyadicMass U (k+1))
    (hBm : nativeDyadicMass U m ≤ B) (hBm1 : B < nativeDyadicMass U (m+1))
    (hgap : k+3 ≤ m) (hB1 : B ≤ 1) (i : Fin (nativeBroadSliceCount k m)) :
    let v := nativeBroadSliceScale U k m i
    let l := nativeBroadSliceNode U s B k m i.val
    let V := nativeBroadSliceNode U s B k m (i.val+1)
    U ≤ v ∧ V∈Icc (0:ℝ) 1 ∧ V ≤ 4*v ∧
      (∀t∈nativeBroadMassSlice hc hk hkc hm hM α l V,α.val.val t ≤ V) ∧
      v ≤ ∫t in nativeBroadMassSlice hc hk hkc hm hM α l V,deriv α.val.val t := by
  dsimp only
  have hg := nativeBroadSlice_geometry hU hs hs1 hBm hBm1 hgap i
  have hv0 : 0 < nativeBroadSliceScale U k m i := hU.trans_le hg.1
  have hl0 : 0 ≤ nativeBroadSliceNode U s B k m i.val := by linarith [hg.2.2.1]
  have hV : nativeBroadSliceNode U s B k m (i.val+1)∈Icc (0:ℝ) 1 :=
    ⟨by linarith [hg.2.1],hg.2.2.2.2.2.1.trans hB1⟩
  have hl : nativeBroadSliceNode U s B k m i.val∈Icc (0:ℝ) 1 :=
    ⟨hl0,hg.2.2.2.2.2.2.le.trans hV.2⟩
  exact ⟨hg.1,hV,hg.2.2.2.1,
    fun t ht=>nativeBroadMassSlice_mass_ceiling hc hk hkc hm hM α hV ht,
    by rw [nativeBroadMassSlice_mass hc hk hkc hm hM α hl hV hg.2.2.2.2.2.2];exact hg.2.1⟩

theorem comparison_native_broad_cap_exists_physical_sampler
    (α : inverseIntegralConstraints 0 0 k M) {U a z : ℝ}
    (hU : 0 < U) (ha : a∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1)
    (hbroad : 8*max (α.val.val a) U < α.val.val z) :
    ∃k m : ℕ,k+3 ≤ m ∧
      (∑i : Fin (nativeBroadSliceCount k m),
        ∫t in nativeBroadMassSlice hc hk hkc hm hM α
          (nativeBroadSliceNode U (max (α.val.val a) U) (α.val.val z) k m i.val)
          (nativeBroadSliceNode U (max (α.val.val a) U) (α.val.val z) k m (i.val+1)),
          deriv α.val.val t)=α.val.val z-max (α.val.val a) U ∧
      (∀i : Fin (nativeBroadSliceCount k m),
        let v := nativeBroadSliceScale U k m i
        let l := nativeBroadSliceNode U (max (α.val.val a) U) (α.val.val z) k m i.val
        let V := nativeBroadSliceNode U (max (α.val.val a) U) (α.val.val z) k m (i.val+1)
        U ≤ v ∧ V∈Icc (0:ℝ) 1 ∧ V ≤ 4*v ∧
          nativeBroadMassSlice hc hk hkc hm hM α l V⊆Ioo a z ∧
          (∀t∈nativeBroadMassSlice hc hk hkc hm hM α l V,α.val.val t ≤ V) ∧
          v ≤ ∫t in nativeBroadMassSlice hc hk hkc hm hM α l V,deriv α.val.val t) := by
  let s := max (α.val.val a) U
  let B := α.val.val z
  obtain ⟨kk,hnear,hnear1⟩ := nativeDyadicMass_exists_near hU (le_max_right (α.val.val a) U)
  have hUB : U ≤ B := (le_max_right (α.val.val a) U).trans (by
    have hp : 0 < s := hU.trans_le (le_max_right _ _)
    linarith)
  obtain ⟨mm,hmm,hmm1⟩ := nativeDyadicMass_exists_near hU hUB
  have hgap := native_broad_dyadic_index_gap hU hnear hmm1 hbroad
  have hB1 : B ≤ 1 := (α.val.property.1 z).2
  have hgeom i := nativeBroadSlice_geometry hU hnear hnear1 hmm hmm1 hgap i
  have htrueMass (i : Fin (nativeBroadSliceCount kk mm)) : (∫t in nativeBroadMassSlice hc hk hkc hm hM α
      (nativeBroadSliceNode U s B kk mm i.val) (nativeBroadSliceNode U s B kk mm (i.val+1)),
      deriv α.val.val t)=
      nativeBroadSliceNode U s B kk mm (i.val+1)-nativeBroadSliceNode U s B kk mm i.val := by
    have hg := hgeom i
    have hv0 := hU.trans_le hg.1
    have hV : nativeBroadSliceNode U s B kk mm (i.val+1)∈Icc (0:ℝ) 1 :=
      ⟨by linarith [hg.2.1,hg.2.2.1],hg.2.2.2.2.2.1.trans hB1⟩
    have hl : nativeBroadSliceNode U s B kk mm i.val∈Icc (0:ℝ) 1 :=
      ⟨by linarith [hg.2.2.1],hg.2.2.2.2.2.2.le.trans hV.2⟩
    exact nativeBroadMassSlice_mass hc hk hkc hm hM α hl hV hg.2.2.2.2.2.2
  refine ⟨kk,mm,hgap,?_,?_⟩
  · change (∑i : Fin (nativeBroadSliceCount kk mm),
      ∫t in nativeBroadMassSlice hc hk hkc hm hM α
        (nativeBroadSliceNode U s B kk mm i.val) (nativeBroadSliceNode U s B kk mm (i.val+1)),
        deriv α.val.val t)=B-s
    simp_rw [htrueMass]
    exact nativeBroadSlice_mass_sum U s B hgap
  · intro i
    have hg := hgeom i
    have hcontracts := nativeBroadMassSlice_broad_contracts hc hk hkc hm hM α
      hU hnear hnear1 hmm hmm1 hgap hB1 i
    exact ⟨hcontracts.1,hcontracts.2.1,hcontracts.2.2.1,
      nativeBroadMassSlice_subset_cap hc hk hkc hm hM α ha hz
        ((le_max_left _ _).trans hg.2.2.2.2.1) hg.2.2.2.2.2.1,
      hcontracts.2.2.2.1,hcontracts.2.2.2.2⟩

theorem native_broad_near_zero_discard_mass (α : inverseIntegralConstraints 0 0 k M)
    {U : ℝ} (hU : 0 < U) :
    (∫t in nativeBroadMassSlice hc hk hkc hm hM α 0 (min (8*U) 1),deriv α.val.val t) ≤ 8*U := by
  have hu : 0 < min (8*U) 1 := lt_min (by positivity) zero_lt_one
  rw [nativeBroadMassSlice_mass hc hk hkc hm hM α (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)
    ⟨hu.le,min_le_right _ _⟩ hu,sub_zero]
  exact min_le_left _ _

theorem actual_variableEndpoint_comparison_initial_cap_increment
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS n
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB n
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {z p q : ℝ} (hz : z ≤ 1) (hp : p∈Ioo (0:ℝ) z) (hq : q∈Ioo (0:ℝ) z)
    (hzH : H z=0) (hneg : ∀r∈Ioo (0:ℝ) z,H r<0) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS n bf hf (α.val.val r)
    S q-S p ≤ z ∧ S q ≤ z := by
  dsimp only
  have hright := actual_variableEndpoint_comparison_cap_right_bound hc hk hkc hm hM
    hN hlog hd hnd hlam hld n hn b h hb hlb hh hh0 α H J hH hJ hD
    (show (0:ℝ)≤0 from le_rfl) hz hq hzH (hneg q hq)
  have hmom := comparisonVariableEndpoint_radius_moments hc hk hkc hm hM n hn
    b h hd.ne' hlam.le hlb hb hh hh0 α
  have hp01 : p∈Icc (0:ℝ) 1 := ⟨hp.1.le,hp.2.le.trans hz⟩
  have hpS := (hmom.2.2 p hp01).1.1
  dsimp only at hright hpS
  exact ⟨by linarith,hright⟩

theorem actual_variableEndpoint_comparison_cap_increment_endpoint_cases
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS n
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB n
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {a z p q : ℝ} (ha : 0 ≤ a) (hz : z ≤ 1)
    (hp : p∈Ioo a z) (hq : q∈Ioo a z) (hpq : p ≤ q)
    (hboundary : (H a=0 ∧ H z=0) ∨ (a=0 ∧ H z=0) ∨ (H a=0 ∧ z=1))
    (hneg : ∀r∈Ioo a z,H r<0) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS n bf hf (α.val.val r)
    S q-S p ≤ (9*Real.log N)*(z-a) := by
  dsimp only
  rcases hboundary with ho|hi|ht
  · exact (actual_variableEndpoint_comparison_cap_interior_geometry hc hk hkc hm hM
      hN hlog hd hnd hlam hld n hn b h hb hlb hh hh0 α H J hH hJ hD
      ha hz hp hq hpq ho.1 ho.2 (hneg p hp) (hneg q hq)).1
  · have hh := (actual_variableEndpoint_comparison_initial_cap_increment hc hk hkc hm hM
      hN hlog hd hnd hlam hld n hn b h hb hlb hh hh0 α H J hH hJ hD hz
      (by simpa only [hi.1] using hp) (by simpa only [hi.1] using hq) hi.2
      (by simpa only [hi.1] using hneg)).1
    have hz0 : 0 ≤ z := (ha.trans_lt hp.1).le.trans hp.2.le
    have hs := mul_le_mul_of_nonneg_right (show (1:ℝ)≤9*Real.log N by linarith) hz0
    dsimp only at hh
    rw [hi.1,sub_zero]
    linarith
  · have hh := actual_variableEndpoint_comparison_terminal_cap_increment hc hk hkc hm hM
      hN hlog hd hnd hlam hld n hn b h hb hlb hh hh0 α H J hH hJ hD ha
      (by simpa only [ht.2] using hp) (by simpa only [ht.2] using hq) hpq ht.1
      (hneg p hp) (hneg q hq)
    simpa only [ht.2] using hh

end

end OAI.SKFluctuations.LaplaceWindowFormalization
