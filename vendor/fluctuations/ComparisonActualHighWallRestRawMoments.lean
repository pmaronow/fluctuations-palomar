module

public import ComparisonActualHighWallSourceMoments
public import ComparisonSignedCavityInheritedRestRawMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_high_wall_rest_even_bound
    (l : ℕ) (hl : 0< l) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) :
    ∃C : ℝ,0< C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(L : ℕ) (us : List PositiveMass),(∀u∈us,u.val≤1) →
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤ M.xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀j≤ as.length,(ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
          (fun r=>Sum.elim (fun _=>b r) (fun _=>h r))
          (fun σ=>|orderedOverlap n (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*l)) 0≤
          (C*(M.xs+partitionPoint 0 as j))^(2*l) := by
  let B:=max Bclock 0
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_high_wall_deleted_raw_on_retained_net
    (D:=D) l hl Bclock (2*B) B hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*Cd,by positivity,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro j hj
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HC:=M.data.full_square_clock_budget M.alpha as ho
  have HCB : finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length≤2*B:=
    HC.trans (by dsimp only [B];nlinarith only [M.hT,le_max_left Bclock (0:ℝ)])
  have HT:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho as.length)
  have HB : b as.length≤ B:=by
    have HP:=(M.hf (partitionPoint 0 as as.length)).coe_nonneg
    dsimp only [b,B];linarith only [HT,HP,M.hT,le_max_left Bclock (0:ℝ)]
  have HRj:=hk j hj HCB HB
  have hb : Monotone b:=comp_partitionPoint_monotone
    (fun x hx y hy hxy=>show (M.bf x:ℝ)≤ (M.bf y:ℝ) from M.data.bf_monotone M.alpha hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (fun x hx y hy hxy=>show (M.hf x:ℝ)≤ (M.hf y:ℝ) from M.data.hf_monotone M.alpha hx hy hxy) as ho
  have H:=native_original_rest_even_le_raw n l hn0 ho b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) j hj
  have HH:=mul_le_mul_of_nonneg_left HRj (by positivity : (0:ℝ)≤ (2:ℝ)^(2*l))
  apply H.trans
  convert HH using 1
  simp only [mul_pow];ring

end OAI.SKFluctuations.Cavity
