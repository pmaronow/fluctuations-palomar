module

public import ComparisonActualHighWallSecondLowSoleRootTargetLocalThermalAlong
public import ComparisonActualHighWallJointLowCubicPrice

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_second_low_sole_root_target_B0_uniform_local_thermal_budget_along
    (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ),U≤as.length → i<U → partitionPoint 0 as U≤Ccut*M.data.d →
        let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) i
        let di:=nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as i+1/(dim n+1:ℕ)
        |nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2|≤
          C*M.data.d^2*di+C*M.data.d*
            (∫u in 0..min (Ccut*M.data.d) 1,Real.sqrt (orderedPathB (dim n+1) M.bf M.hf u-
              (orderedPathS (dim n+1) M.bf M.hf u)^2)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_second_low_sole_root_target_B0_local_thermal_budget_along
    (D:=D) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  have hCB : 0 ≤ CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  let Cuniform:=C*(CB+1)
  have hUniform : 0 < Cuniform:=by dsimp only [Cuniform];positivity
  refine ⟨Cuniform,hUniform,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i U hU hi hcut
  have HB:=hk i U hU hi hcut
  let as:=finiteCutMasses us k
  let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
  let di:=nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf as i+1/(dim n+1:ℕ)
  let I:=(∫u in 0..min (Ccut*M.data.d) 1,Real.sqrt (orderedPathB (dim n+1) M.bf M.hf u-
    (orderedPathS (dim n+1) M.bf M.hf u)^2))
  have hDi : 0 ≤ di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hI : 0 ≤ I:=by
    apply intervalIntegral.integral_nonneg (le_min (mul_nonneg hCcut M.data.hd.le) zero_le_one)
    intro u _
    exact Real.sqrt_nonneg _
  have Hclock : Cerr ≤ CB:=actual_wall_low_error_comparison_constant_le (M.data.hepsilon.1.trans M.data.hepsilon.2).le
    (M.hT.trans (le_max_left _ _))
  have Hfactor : C*Cerr ≤ Cuniform:=by
    have HH:=mul_le_mul_of_nonneg_left Hclock hC.le
    dsimp only [Cuniform]
    nlinarith only [HH,hC]
  have H1:=mul_le_mul_of_nonneg_right Hfactor (mul_nonneg (sq_nonneg M.data.d) hDi)
  have H2:=mul_le_mul_of_nonneg_right Hfactor (mul_nonneg M.data.hd.le hI)
  apply HB.trans
  convert add_le_add H1 H2 using 1 <;> ring

end OAI.SKFluctuations.Cavity
