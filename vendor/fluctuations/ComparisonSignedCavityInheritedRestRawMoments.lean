module

public import ComparisonSignedCavityActualRestRawMoments
public import ComparisonSignedCavityInheritedCanonicalSourceMoments

@[expose] public section
noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_rest_even_bound
    (l : ℕ) (hl : 0 < l) (Bclock Temp Cf : ℝ) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
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
              (ClockTree.pairSpin as j σ).2|^(2*l)) 0 ≤
            (C*(M.xs+partitionPoint 0 as j))^(2*l) := by
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) l hl Bclock (4*Cf+2*Temp) Temp hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨2*Cd,by positivity,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro j hj
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HC:=native_small_source_clock_full_square_budget M Temp Cf hCf hsource hxs as ho
  have HB:=(hsource _ (partitionPoint_mem as ho as.length)).1
  have HRj:=hk j hj HC HB
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  have H:=native_original_rest_even_le_raw n l hn0 ho b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) j hj
  apply H.trans
  have HH:=mul_le_mul_of_nonneg_left HRj (by positivity : (0:ℝ) ≤ (2:ℝ)^(2*l))
  convert HH using 1
  simp only [mul_pow]
  ring

end OAI.SKFluctuations.Cavity
