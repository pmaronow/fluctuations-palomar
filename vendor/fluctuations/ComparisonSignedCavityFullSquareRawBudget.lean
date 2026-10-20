module

public import ComparisonSignedCavityNaturalScaleCalibrationProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 5000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def finitePhysicalCavitySquareVariance (n U : ℕ) (as : List PositiveMass)
    (b h : ℕ→ℝ) (l t : ℝ) : ℕ→FullCoordinate n→ℝ :=
  cavityPath n U l t (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h
    (finitePhysicalMixedClock (n+1) as b h)

theorem finitePhysicalCavitySquareVariance_at_zero (n U : ℕ) (as : List PositiveMass)
    (b h : ℕ→ℝ) (t : ℝ) :
    finitePhysicalCavitySquareVariance n U as b h 0 t=
      finitePhysicalCavityVariance n U as b h t := rfl

theorem finitePhysicalSquareDeleted_moment_le_raw (n p U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) (j : ℕ) (hj : j ≤ as.length) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)|^(2*p)) 0 ≤
      finitePhysicalDeletedRawBudget n p as b h j := by
  have H:=cavityPath_pairDeleted_moment_le_physicalStar n p U ho hl ht hb hh
    (finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0) hb0 hh0
    (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0) j hj 0
  dsimp only at H
  rw [physicalStarPairMoment_zero_eq_raw (n+1) p as ho _ j hj] at H
  simpa only [sub_zero,finitePhysicalCavitySquareVariance,finitePhysicalDeletedRawBudget] using H

theorem actual_full_square_mixed_pair_moment_le (n p U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j)
    (j : ℕ) (hj : j ≤ as.length) (α β : ℝ) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|fullBoundaryAffineFactor n α β (ClockTree.pairSpin as j σ).2
        (ClockTree.pairSpin as j σ).1|^(2*p)) 0 ≤
      nativeMixedBoundaryRawBudget n p as b h j α β := by
  have H:=actual_low_row_moment_le n (2*p) (ClockTree.pairClock as j) ho 0
    (finitePhysicalCavitySquareVariance n U as b h l t) 0
    (ClockTree.pairRightSlot as j) (ClockTree.pairLeftSlot as j) β α 0 1
  simp_rw [low_row_covariance_centered n β α 0 1] at H
  simp only [ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot,
    abs_mul,abs_spinValue,mul_zero,add_zero,sub_zero,
    one_mul,fullBoundaryAffineFactor] at H ⊢
  apply H.trans
  have Hd:=finitePhysicalSquareDeleted_moment_le_raw n p U ho hl ht b h hb hh hb0 hh0 j hj
  have hsym (σ τ : Spin (n+1)) : deletedOverlap n σ τ=deletedOverlap n τ σ := by
    unfold deletedOverlap
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    ring
  simp_rw [hsym (joinSpin (ClockTree.pairSpin as j _).2)
    (joinSpin (ClockTree.pairSpin as j _).1)]
  unfold nativeMixedBoundaryRawBudget
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left Hd (by positivity))) (by positivity)

theorem actual_full_square_boundary_forest_product_square_le (n U a : ℕ) (ha : 0 < a)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (G : ActualMixedBoundaryForest n a T b h) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>G.product σ^2) 0 ≤ (∏e,G.rho e)^2 := by
  let q:=finitePhysicalCavitySquareVariance n U as b h l t
  let f:=fun e σ=>fullBoundaryAffineFactor n (G.α e) (G.β e)
    (T.atSlot σ (G.j e)) (T.atSlot σ (G.i e))
  apply finite_weighted_product_square_scales ha
    (fun σ=>T.disorderWeight (fullWeight n) (fullFeature n) 0 q σ 0) f
    (T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0 q 0).1
    G.rho G.rhoPos
  intro e
  change T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>|f e σ|^(2*a)) 0 ≤ _
  rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 q 0
    (G.i e) (G.j e) (G.distinctLeft e)
    (fun d c=>|fullBoundaryAffineFactor n (G.α e) (G.β e) c d|^(2*a))]
  exact (actual_full_square_mixed_pair_moment_le n a U ho hl ht b h hb hh hb0 hh0 _
    (G.lowInGrid e) (G.α e) (G.β e)).trans (G.raw e)

theorem eventually_actual_minimum_full_square_deleted_moment_bound
    (p : ℕ) (hp : 0 < p) (Bclock Btotal Bbond : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cd : ℝ,0 < Cd ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
          ∀(U : ℕ) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          ∀j,j ≤ as.length →
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length ≤ Btotal →
            b as.length ≤ Bbond →
            (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
              (finitePhysicalCavitySquareVariance n U as b h l t)
              (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
                (joinSpin (ClockTree.pairSpin as j σ).2)|^(2*p)) 0 ≤
              (Cd*(M.xs+partitionPoint 0 as j))^(2*p) := by
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) p hp Bclock Btotal Bbond hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cd,hCd,?_⟩
  filter_upwards [HR] with n hn
  intro M L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U l t hl ht j hj hclock hbond
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  exact (finitePhysicalSquareDeleted_moment_le_raw n p U ho hl ht b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) j hj).trans
    (hk j hj hclock hbond)

end OAI.SKFluctuations.Cavity
