module

public import ComparisonSignedCavitySecondLowActualSoleRootTargetB0Budget
public import ComparisonSignedCavitySecondLowSoleRootTargetDensityIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_second_low_sole_root_target_B0_integral_budget
    (Bclock Temp Cf Couter : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ),U≤as.length → i<U → M.xs≤x → x≤M.canonicalDirectTestBandScale →
          partitionPoint 0 as U≤Couter*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        |nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2|≤
          C*x^2*Cerr*di+C*x*Cerr*
            (∫u in 0..min (Couter*x) 1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
              (orderedPathS (n+1) M.bf M.hf u)^2)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_sole_root_target_B0_budget
    (D:=D) Bclock Temp Cf Couter hTemp hCf hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C*(2+Couter),mul_pos hC (by linarith),?_⟩
  filter_upwards [H] with n hn
  intro M HS hxs L us hus hret hmesh
  filter_upwards [hn M HS hxs L us hus hret hmesh,
    actual_second_low_literal_moving_density_target_integral_on_every_final_net M Couter hCouter us hus] with k hk hD
  dsimp only at hk hD ⊢
  intro i U x hU hi hxsx hxW houter
  have HB:=hk i U x hU hi hxsx hxW houter
  have HD:=hD i U x hU hxsx houter
  let as:=finiteCutMasses us k
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let I:=(∫u in 0..min (Couter*x) 1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2))
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hCerr : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hR : 0≤nativeOriginalCutLowErrorRadius n M.bf M.hf as i:=Real.sqrt_nonneg _
  have hdi : 0≤di:=add_nonneg hR (by positivity)
  have hsite : (1/(n+1:ℕ):ℝ)≤di:=le_add_of_nonneg_left hR
  have hI : 0≤I:=by
    apply intervalIntegral.integral_nonneg (le_min (mul_nonneg hCouter hx.le) zero_le_one)
    intro u _
    exact Real.sqrt_nonneg _
  apply HB.trans
  have HM:=mul_le_mul_of_nonneg_left HD (show 0≤C*x*Cerr by positivity)
  apply (add_le_add le_rfl HM).trans
  have HsiteCost:=mul_le_mul_of_nonneg_left hsite (show 0≤C*(1+Couter)*x^2*Cerr by positivity)
  have HIcost:=mul_le_mul_of_nonneg_right (show C≤C*(2+Couter) by nlinarith) (show 0≤x*Cerr*I by positivity)
  dsimp only [di,I,Cerr,as] at HsiteCost HIcost ⊢
  simp only [div_eq_mul_inv] at HsiteCost HIcost ⊢
  nlinarith

end OAI.SKFluctuations.Cavity
