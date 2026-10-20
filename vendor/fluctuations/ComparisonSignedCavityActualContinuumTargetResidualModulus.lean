module

public import ComparisonSignedCavityActualContinuumTargetMeanReductionAlong
public import ComparisonSignedCavityActualHistoryInitialResidualAlong
public import ComparisonSignedCavityActualHistoryTargetOriginalTaylorModulusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

private theorem target_gap_residual_triangle
    {S G a L R T C D x e t r A : ℝ} (_hx : 0 ≤ x) (_hr : 0 ≤ r)
    (Hm : |S-G-a*L-T| ≤ e*x^3) (HT : |T| ≤ C*x^2*D+t*x^3)
    (HR : |L-R| ≤ r*x^3) (Ha : |a| ≤ A) :
    |S-G-a*R| ≤ C*x^2*D+(e+t+A*r)*x^3 := by
  have Hprod : |a*(L-R)| ≤ A*(r*x^3) := by
    rw [abs_mul]
    exact mul_le_mul Ha HR (abs_nonneg _) (le_trans (abs_nonneg _) Ha)
  rw [show S-G-a*R=(S-G-a*L-T)+T+a*(L-R) by ring]
  have H:=((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add Hm HT) Hprod)
  exact H.trans_eq (by ring)

def ActualContinuumTargetResidualModulusAlong
    {m delta cl cu Az C0 Ct D Bclock Temp : ℝ} {dim : ℕ→ℕ}
    (hTemp : 0 < Temp) (depth : ℕ) (Ccut Couter c C : ℝ) (eta : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W x : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp,
    ∀(Lnet : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us → (∀u∈uniformMasses Lnet,u∈us) →
      ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀u∈us,let i:=retainedMassPrefixIndex u.val as
      ∀(U V : ℕ) (hi : i ≤ star) (_hiU : i < U) (_hUV : U ≤ V)
        (hs : star < V) (hV : V ≤ as.length),
      2*c*x n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*x n →
      partitionPoint 0 as V ≤ Couter*W n →
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hV))
      |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
        scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)-
        2*((M n).bf u.val:ℝ)*chi*
          nativeActualMinimumFourResidualSum (M n) hs hV (W n) depth [st]| ≤
        C*(x n)^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+
          1/(dim n+1:ℕ))+eta n*(x n)^3

theorem actual_selected_bad_history_continuum_target_residual_modulus_of_initial_approx
    {m delta cl cu Az C0 Ct D Bclock Temp Cs c0 c saving : ℝ}
    (Ccut Couter : ℝ) (hTemp : 0 < Temp) (hCcut : 0 ≤ Ccut) (hCouter : 0 < Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hsaving : 0 < saving) (depth : ℕ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W x : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (hxsx : ∀n,(M n).xs ≤ x n)
    (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (Hresidual : ActualTargetInitialResidualApproxAlong depth saving Ccut M W w) :
    ∃(C : ℝ) (eta : ℕ→ℝ),0 < C ∧ (∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ActualContinuumTargetResidualModulusAlong hTemp depth Ccut Couter c C eta M W x w := by
  have hxlim : Tendsto x atTop (𝓝 0):=squeeze_zero'
    (Filter.Eventually.of_forall (fun n=>(M n).hxs.le.trans (hxsx n))) hxW hWlim
  have HWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    simpa only [←hcanonical] using hWlim
  have HxW : ∀ᶠn in atTop,x n ≤ (M n).canonicalDirectTestBandScale:=by
    simpa only [hcanonical] using hxW
  have HW1:=HWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp.le hb hh Hhistory
  obtain ⟨em,hem,Hem,HM⟩:=actual_selected_bad_history_continuum_target_mean_reduction_along
    Bclock Temp Ccut Couter hTemp hCcut hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs hc0 hmargin hcapmargin dim hdim root M epsilon shell hepsilon hb hh Hhistory
    x hxsx hxlim hsmall HWlim
  obtain ⟨C,et,hC,het,Het,HT⟩:=actual_selected_bad_history_target_original_Taylor_modulus_along
    Ccut hTemp.le hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter hc0
    hmargin hcapmargin dim hdim root M epsilon shell hepsilon hb hh Hhistory
    x hxsx hxlim HxW hsmall HW1
  let rate n:=((dim n+1:ℕ):ℝ)^(-saving)
  have Hrate : Tendsto rate atTop (𝓝 0):=by
    have H:=(tendsto_rpow_neg_atTop hsaving).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)
    simpa only [rate,Function.comp_def] using H
  let eta n:=em n+et n+6*Temp*rate n
  have Heta : Tendsto eta atTop (𝓝 0):=by
    simpa only [add_zero,mul_zero] using (Hem.add Het).add (Hrate.const_mul (6*Temp))
  refine ⟨C,eta,hC,?_,Heta,?_⟩
  · intro n
    have hr : 0 ≤ rate n:=Real.rpow_nonneg (by positivity) _
    have hm0:=hem n
    have ht0:=het n
    dsimp only [eta]
    positivity
  · filter_upwards [HM,HT,Hresidual,Hsource,hxW] with n hmN htN hrN hsource hxw
    obtain ⟨htotal,hmN⟩:=hmN
    refine ⟨htotal,?_⟩
    intro Lnet us hus hstar hret hmesh
    filter_upwards [hmN Lnet us hus hret hmesh,htN Lnet us hus hret hmesh,
      hrN Lnet us hus hstar hret hmesh] with jGrid hmj htj hrj
    dsimp only at hmj htj hrj ⊢
    intro u hu U V hi hiU hUV hs hV hcutlo hcut hVmass
    let as:=finiteCutMasses us jGrid
    let i:=retainedMassPrefixIndex u.val as
    let star:=retainedMassPrefixIndex (w n).star.val as
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hU:=hUV.trans hV
    have Hret : partitionPoint 0 as i=u.val:=nativeRetainedCut_partitionPoint as ho u
      (finiteCutMasses_nodes us jGrid hu)
    have himass : partitionPoint 0 as i ≤ Ccut*x n:=(partitionPoint_mono as ho hiU.le).trans hcut
    have hmass : u.val ≤ Ccut*x n:=by rw [←Hret];exact himass
    have HM:=hmj u hu U V hiU hUV hV hmass (by simpa only [←hcanonical n] using hVmass)
    have HT:=htj i U hiU hU hcutlo hcut
    have HR:=hrj V i hi hs hV (x n) (hxsx n) hxw himass
    have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid (M n) as ho U
      (Nat.zero_le i |>.trans_lt hiU) hU
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    have Hb:=hsource u.val ⟨u.property.le,hus u hu⟩
    have Ha : |2*((M n).bf u.val:ℝ)*chi| ≤ 2*Temp:=by
      have Hmul:=mul_le_mul Hb.1 Hchi.2 Hchi.1 hTemp.le
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1)]
      nlinarith only [Hmul]
    have H:=target_gap_residual_triangle ((M n).hxs.le.trans (hxsx n))
      (show 0 ≤ 3*rate n by dsimp only [rate];positivity) HM HT HR Ha
    exact H.trans_eq (by dsimp only [eta,rate];ring)

end OAI.SKFluctuations.Cavity
