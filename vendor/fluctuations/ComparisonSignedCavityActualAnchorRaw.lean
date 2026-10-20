module

public import ComparisonSignedCavityActualAnchorMarginal
public import ComparisonSignedCavityForestObservedHighGeometry

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_original_rest_deleted_fourth_le_raw (n : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ → ℝ)
    (hb : Monotone b) (hh : Monotone h) (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j)
    (j : ℕ) (hj : j ≤ as.length) :
    (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
      (fun l => Sum.elim (fun _ => b l) (fun _ => h l))
      (fun σ => |deletedOverlap n (joinSpin ((ClockTree.pairSpin as j σ).1,false))
        (joinSpin ((ClockTree.pairSpin as j σ).2,false))|^4) 0 ≤
      finitePhysicalDeletedRawBudget n 2 as b h j := by
  let : Nonempty (RestCoordinate n) := ⟨Sum.inr ⟨0,hn⟩⟩
  let T := ClockTree.pairClock (S:=Spin n × Bool) as j
  let s := ClockTree.pairLeftSlot (S:=Spin n × Bool) as j
  let t := ClockTree.pairRightSlot (S:=Spin n × Bool) as j
  let Q := fun σ τ : Spin n => |deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))|^4
  let P := fun σ : T.cavityLeft.Assignment =>
    Q (T.cavityLeft.atSlot σ (T.cavityLeftSlot s)) (T.cavityLeft.atSlot σ (T.cavityLeftSlot t))
  have hst : T.cavityLeftSlot s ≠ T.cavityLeftSlot t :=
    fun H => ClockTree.pairSlots_distinct as j (T.cavityLeftSlot.injective H)
  have hsplit : T.cavityLeft.splitIndex (T.cavityLeftSlot s) (T.cavityLeftSlot t)=j := by
    rw [ClockTree.cavityLeft_splitIndex]
    exact (ClockTree.pairSlots_splitIndex as j).trans (Nat.min_eq_left hj)
  have HD := native_decoupled_rest_expect n
    (fun l => Sum.elim (fun _ => b l) (fun _ => h l)) 0 b h
    (finitePhysicalMixedClock (n+1) as b h) T ho P
  dsimp only [P] at HD
  rw [T.cavityLeft.disorderExpect_pairAtSlot_actual (restWeight_pos n) (restFeature n)
    ho 0 _ 0 _ _ hst Q,hsplit] at HD
  have Hraw := finitePhysicalDeleted_moment_le_raw n 2 0 ho
    (show (0:ℝ)∈Icc 0 1 by norm_num) b h hb hh hb0 hh0 j hj
  rw [←HD]
  convert Hraw using 1
  congr 1
  funext σ
  dsimp only [P,Q]
  rw [ClockTree.atSlot_cavityLeft,ClockTree.atSlot_cavityLeft]
  simp only [T,s,t,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot]
  simp [deletedOverlap,joinSpin]

theorem ordered_overlap_fourth_le_sixteen_deleted (n : ℕ) (hn : 0 < n)
    (σ τ : Spin n) :
    |orderedOverlap n σ τ|^4 ≤
      16*|deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))|^4 := by
  let k : ℝ := (n:ℝ)/(n+1:ℕ)
  have hk : (1:ℝ)/2 ≤ k := by
    dsimp [k]
    have hn1 : (0:ℝ) < (n+1:ℕ) := Nat.cast_pos.mpr (by omega)
    apply (le_div_iff₀ hn1).mpr
    have H : (1:ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith
  have hk0 : 0 ≤ k := by positivity
  have H := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hk 4
  norm_num at H
  rw [deleted_overlap_join_eq_scaled,abs_mul,abs_of_nonneg hk0,mul_pow]
  change |orderedOverlap n σ τ|^4 ≤ 16*(k^4*|orderedOverlap n σ τ|^4)
  nlinarith [pow_nonneg (abs_nonneg (orderedOverlap n σ τ)) 4]

theorem native_original_rest_fourth_le_sixteen_raw (n : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (b h : ℕ → ℝ)
    (hb : Monotone b) (hh : Monotone h) (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j)
    (j : ℕ) (hj : j ≤ as.length) :
    (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
      (fun l => Sum.elim (fun _ => b l) (fun _ => h l))
      (fun σ => |orderedOverlap n (ClockTree.pairSpin as j σ).1
        (ClockTree.pairSpin as j σ).2|^4) 0 ≤
      16*finitePhysicalDeletedRawBudget n 2 as b h j := by
  have hw := (ClockTree.pairClock (S:=Spin n) as j).disorderWeight_probability
    (restWeight_pos n) (restFeature n) ho 0
    (fun l => Sum.elim (fun _ => b l) (fun _ => h l)) 0
  have H := Finset.sum_le_sum (fun σ (_ : σ∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (ordered_overlap_fourth_le_sixteen_deleted n hn
      (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) (hw.1 σ))
  have H' : (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
      (fun l => Sum.elim (fun _ => b l) (fun _ => h l))
      (fun σ => |orderedOverlap n (ClockTree.pairSpin as j σ).1
        (ClockTree.pairSpin as j σ).2|^4) 0 ≤
      16*(ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
        (fun l => Sum.elim (fun _ => b l) (fun _ => h l))
        (fun σ => |deletedOverlap n (joinSpin ((ClockTree.pairSpin as j σ).1,false))
          (joinSpin ((ClockTree.pairSpin as j σ).2,false))|^4) 0 := by
    unfold ClockTree.disorderExpect
    rw [Finset.mul_sum]
    convert H using 1
    apply Finset.sum_congr rfl
    intro σ _
    ring
  exact H'.trans (mul_le_mul_of_nonneg_left
    (native_original_rest_deleted_fourth_le_raw n hn ho b h hb hh hb0 hh0 j hj) (by norm_num))

theorem eventually_actual_minimum_bare_rest_fourth_bound
    (Bclock Temp : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀j ≤ as.length,
          (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
            (fun l => Sum.elim (fun _ => b l) (fun _ => h l))
            (fun σ => |orderedOverlap n (ClockTree.pairSpin as j σ).1
              (ClockTree.pairSpin as j σ).2|^4) 0 ≤
            (C*(M.xs+partitionPoint 0 as j))^4 := by
  let Cf:=NativeOverlapMinimum.bareSourceClockConstant cl Az D
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) 2 (by norm_num) Bclock (4*Cf+2*Temp) Temp hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨2*Cd,by positivity,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hbconst hhzero hxs L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro j hj
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HC:=M.bare_sampled_full_square_clock_budget hcl hAz Temp hbconst hhzero hxs as ho
  have HB:=(M.bare_source_clock_bounds hcl hAz Temp hbconst hhzero
    (partitionPoint_mem as ho as.length)).2.1
  have HRj:=hk j hj HC HB
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  have H:=native_original_rest_fourth_le_sixteen_raw n hn0 ho b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) j hj
  apply H.trans
  have HH:=mul_le_mul_of_nonneg_left HRj (by norm_num : (0:ℝ) ≤ 16)
  convert HH using 1
  ring

end OAI.SKFluctuations.Cavity
