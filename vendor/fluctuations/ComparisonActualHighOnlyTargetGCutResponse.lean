module

public import ComparisonSignedCavityActualTargetGCutResponse
public import ComparisonActualHighOnlyPullbackFourProducers
public import ComparisonActualHighOnlyTargetGCutEnvelope
public import ComparisonActualHighOnlyTargetGCutDensity
public import ComparisonActualHighOnlyInheritedTargetScalarCutClock
public import ComparisonSignedCavityActualTargetGCutDensity
public import ComparisonSignedCavityInheritedTargetScalarCutExchange
public import ComparisonNativeActualUniformBandL1Density

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_target_G_cut_thermal_comparison_high_only
    (Bclock Temp Cf Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C R : ℝ,0 < C ∧ 0 < R ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs → ActualHighOnlySmallSourceClocks M Temp Cf→M.xs≤1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U V : ℕ),i < U→U≤V→V≤as.length→
        ∀x W : ℝ,M.xs≤x→partitionPoint 0 as i≤Ccut*x→
          M.xs≤W→partitionPoint 0 as V≤Couter*W→
          let band:=(∫u in partitionPoint 0 as U..partitionPoint 0 as V,
            Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))+3/(n+1:ℕ)
          let tail:=(∫u in partitionPoint 0 as V..1,
            Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))+3/(n+1:ℕ)
          abs (nativeActualTargetLongitudinalResponse_high_only M as i U-nativeActualTargetLongitudinalResponse_high_only M as i V)≤
              C*x*(band+R*W*tail) ∧
          abs (nativeActualTargetConditionalResponse_high_only M as i U-nativeActualTargetConditionalResponse_high_only M as i V)≤
              C*x*(band+R*W*tail) := by
  obtain ⟨Cr,hCr,Hr⟩:=eventually_actual_minimum_inherited_original_fresh_target_rms_high_only
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Rk,hRk,Hk⟩:=eventually_actual_minimum_inherited_continuum_cut_clock_upper_high_only
    (D:=D) Bclock Temp Cf Couter hTemp hCf hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let F:=forkVariation 2 3
  let Cmp:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let Ck:=(3/2:ℝ)*(errorJetVariation 5 0 0*(6:ℝ))
  let R:=Ck*Rk+1
  have hF : 0≤F:=forkVariation_nonneg 2 3
  have hCmp : 0≤Cmp:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hCk : 0≤Ck:=mul_nonneg (by norm_num)
    (mul_nonneg (errorJetVariation_nonneg 5 0 0) (by norm_num))
  have hR : 0 < R:=by dsimp only [R];positivity
  refine ⟨Cr*F*Cmp+1,R,by positivity,hR,?_⟩
  filter_upwards [Hr,Hk] with n hn hk
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh,
    actual_original_high_l1_density_on_all_final_nets_high_only M,
    original_band_l1_density_on_all_final_nets n M.bf M.hf M.bf_monotone M.hf_monotone] with jGrid hj ht hb
  dsimp only at hj ⊢
  intro i U V hi hUV hV x W hscale hmass hxW hVmass
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hx : 0≤x:=M.hxs.le.trans hscale
  have hW : 0≤W:=M.hxs.le.trans hxW
  have HR:=hj U 1 1 (by norm_num) (by norm_num)
    (single (S:=Spin n×Bool) (finiteCutMasses us jGrid))
    (singleSlot (finiteCutMasses us jGrid)) i ((hi.le.trans hUV).trans hV) x hscale hmass
  have HP:=(Real.sqrt_le_iff.mp HR).2
  have HL:=actual_minimum_inherited_target_G_cut_density_high_only M Temp Cf hTemp hCf hsource hxs
    (finiteCutMasses us jGrid) ho i U V hi hUV hV (Cr*x) (mul_nonneg hCr.le hx) HP
  have HB:=hb us hus U V hUV hV
  have HT:=ht us hus V hV
  let elo:=edgeBudget 0 (finiteCutMasses us jGrid) (fun j=>if j < U then 0 else if j < V then
    nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us jGrid) j+1/(n+1:ℕ) else 0)
  let ehi:=edgeBudget 0 (finiteCutMasses us jGrid) (fun j=>if j < V then 0 else
    nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us jGrid) j+1/(n+1:ℕ))
  have hlo : 0≤elo:=edgeBudget_nonneg ho (by
    intro j
    split_ifs
    · exact le_rfl
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · exact le_rfl)
  have hhi : 0≤ehi:=edgeBudget_nonneg ho (by
    intro j
    split_ifs
    · exact le_rfl
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hclock:=hk M hs0 hsxs hsource (finiteCutMasses us jGrid) ho W hW hxW V hVmass
  have Hcoef : nativeActualTargetCutCoefficient_high_only M (finiteCutMasses us jGrid) V≤R*W:=by
    change Ck*nativeContinuumMixedClock n M.bf M.hf (finiteCutMasses us jGrid) (V-1)≤_
    apply (mul_le_mul_of_nonneg_left Hclock hCk).trans
    have HE : Ck*(Rk*W)=(Ck*Rk)*W:=by ring
    rw [HE]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hW
  have hc : 0≤nativeActualTargetCutCoefficient_high_only M (finiteCutMasses us jGrid) V:=
    mul_nonneg hCk (native_continuum_mixed_clock_nonneg n M.bf M.hf
      M.inherited_bf_monotone M.inherited_hf_monotone (finiteCutMasses us jGrid) ho _)
  have HH:=add_le_add HB (mul_le_mul Hcoef HT hhi (mul_nonneg hR.le hW))
  have Hrhs0 : (0:ℝ)≤_ := (add_nonneg hlo (mul_nonneg hc hhi)).trans HH
  have Hbound:=HL.trans (mul_le_mul_of_nonneg_left HH
    (mul_nonneg (mul_nonneg (mul_nonneg hCr.le hx) hF) hCmp))
  change abs (nativeActualTargetLongitudinalResponse_high_only M (finiteCutMasses us jGrid) i U-
    nativeActualTargetLongitudinalResponse_high_only M (finiteCutMasses us jGrid) i V)≤(Cr*x)*F*Cmp*_ at Hbound
  have Hcoef' : (Cr*x)*F*Cmp=(Cr*F*Cmp)*x:=by ring
  rw [Hcoef'] at Hbound
  have Hfinal:=Hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hx) Hrhs0)
  refine ⟨Hfinal,?_⟩
  rwa [←native_actual_target_longitudinal_eq_conditional_high_only M _ ho i U hi (hUV.trans hV),
    ←native_actual_target_longitudinal_eq_conditional_high_only M _ ho i V (hi.trans_le hUV) hV]

end OAI.SKFluctuations.Cavity
