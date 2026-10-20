module

public import ComparisonSignedCavityActualCenteredResourceJointLowRestorationFromMinimum
public import ComparisonSignedCavityActualFreshResourceJointLowRestorationReadout
public import ComparisonSignedCavitySharpOriginalLowRadiusAlong
public import ComparisonSignedCavityTransientForkCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem actual_inherited_constant_resource_fresh_joint_LOW_restoration_rate_along
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 < Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠ n : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠ n : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star ∈ us →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀U : ℕ,star < U → U ≤ as.length → partitionPoint 0 as U ≤ min (Ccut*W n) 1 →
        ∀(i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U [] k T P → i ≤ star →
          T.leaves ≤ rBound → k ≤ degree →
          partitionPoint 0 as i ≤ Cmass*(M n).xs → partitionPoint 0 as star ≤ Cmass*W n →
          |((W n)⁻¹)^k*nativeActualOriginalFreshResourceJointLowRestoration (M n) U P| ≤
              |P.coefficient| *err n*(W n*(M n).xs^2) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_centered_resource_joint_LOW_restoration_from_minimum
    (D:=D) degree (rBound+1) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>C*((dim n+1:ℕ):ℝ)^(-eta/32)
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along hm hdelta hC0 Cerr
    (actualLowErrorComparisonConstant_nonneg _ hTemp) dim hdim M W hcanonical hWlim w hw
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < eta/32 from div_pos
    (actualMassSavingExponent_pos hm hdelta) (by norm_num))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,Function.comp_def,mul_zero,neg_div] using Hpow.const_mul C
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hdim.eventually HC,HR,Hsource,HW1] with n hnC hnR hsource hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx1:=hxW.trans hW1
  intro L us hus hret hmesh hstar
  filter_upwards [hnC (M n) hsource hx1 L us hus hret hmesh,hnR us hus hstar] with jGrid hgridC hgridR
  dsimp only at hgridC hgridR ⊢
  intro U hs hU hcut i k T P hP hi hT hdepth hmi hms
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have Hsplit : g.tree.splitIndex (g.embed P.live.test.target) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,
      min_eq_left (hs.le.trans hU)]
  have H:=hgridC i star U k [] g.tree (P.retarget 0) hP.retarget hi hs hU hg (by simpa using hdepth)
    (W n) hxW hW1 hmi hms (hcut.trans (min_le_left _ _)) (g.embed P.live.test.target) g.mark
    (by rw [Hsplit];exact hs)
  rw [Hsplit] at H
  simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one,NativeResourceTerm.retarget] at H
  rw [native_actual_original_fresh_resource_joint_LOW_restoration_eq_centered_retarget (M n) U P ho]
  have HD:=mul_le_mul_of_nonneg_left hgridR
    (show 0 ≤ |P.coefficient| *C*(W n)^2 by positivity)
  have hW : W n≠0:=((M n).hxs.trans_le hxW).ne'
  apply H.trans
  convert HD using 1 <;> (try dsimp only [err,eta,Cerr,star,as]) <;> field_simp [hW]

end OAI.SKFluctuations.Cavity
