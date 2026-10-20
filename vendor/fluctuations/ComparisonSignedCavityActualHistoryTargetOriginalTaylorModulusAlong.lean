module

public import ComparisonSignedCavityActualTargetOriginalTaylorBudget
public import ComparisonSignedCavitySecondLowActualHistoryTargetB0ModulusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_original_Taylor_modulus_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cs c0 c : ℝ}
    (Ccut : ℝ) (hTemp : 0≤Temp) (hCcut : 0≤Ccut)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0≤epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (x : ℕ→ℝ) (hxsx : ∀n,(M n).xs≤x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hxW : ∀ᶠn in atTop,x n≤(M n).canonicalDirectTestBandScale)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤Cs*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hW1 : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale≤1) :
    ∃(C : ℝ) (err : ℕ→ℝ),0<C ∧ (∀n,0≤err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U : ℕ),i<U → U≤as.length →
          2*c*x n≤partitionPoint 0 as U → partitionPoint 0 as U≤Ccut*x n →
          |nativeActualTargetOriginalTaylorPart (M n) as i U|≤
            C*(x n)^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+
              1/(dim n+1:ℕ))+err n*(x n)^3 := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1:=by
    filter_upwards [Hps] with n hn
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha Temp epsilon shell ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
      (M n).b (M n).h hn.2.1 hn.2.2 le_rfl zero_le_one le_rfl
  obtain ⟨C,hC,HC⟩:=eventually_actual_regular_target_original_Taylor_integral_budget
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let I:=fun n=>(∫u in 0..(Ccut+1)*x n,Real.sqrt
    (orderedPathB (dim n+1) (M n).bf (M n).hf u-(orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))
  let save:=fun n=>((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
  let err:=fun n=>C*(I n/(x n)^2+save n)
  have HI:=actual_second_low_actual_history_initial_mass_error_ratio_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim root M epsilon shell hb hh Hhistory
    x hxsx hxlim Ccut hCcut
  have HP : Tendsto save atTop (𝓝 0):=by
    have HH:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
      (by norm_num : (0:ℝ)<256))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
    simpa only [save,Function.comp_def] using HH
  have Herr : Tendsto err atTop (𝓝 0):=by
    have HH:=(HI.add HP).const_mul C
    simpa only [err,I,add_zero,mul_zero] using HH
  have Hupper:=((hxlim.const_mul (Ccut+1)).eventually
    (eventually_le_nhds (show (Ccut+1)*(0:ℝ)<1 by simp)))
  refine ⟨C,err,hC,?_,Herr,?_⟩
  · intro n
    have hx : 0<x n:=(M n).hxs.trans_le (hxsx n)
    have hI : 0≤I n:=intervalIntegral.integral_nonneg (by positivity) (fun _ _=>Real.sqrt_nonneg _)
    dsimp only [err,save]
    positivity
  · filter_upwards [hdim.eventually HC,Hsource,Hclock,hsmall,hW1,hxW,Hupper]
      with n hn hs hcN hsm hw hxw hupper
    have hx : 0<x n:=(M n).hxs.trans_le (hxsx n)
    have hcut1 : Ccut*x n≤1:=(by nlinarith : Ccut*x n≤(Ccut+1)*x n).trans hupper
    intro L us hus hret hmesh
    filter_upwards [hn (M n) hcN hs hsm hw L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro i U hi hU hcutlo hcut
    have H:=hj i U (x n) hi hU (hxsx n) hxw hcut1 hcutlo hcut
    have HIbig:=native_intervalIntegrable_sqrt_of_intervalIntegrable
      ((native_comparison_thermal_intervalIntegrable (M n)).mono_set (by
        rw [uIcc_of_le (by positivity : 0≤(Ccut+1)*x n),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hupper))
    have HImono : (∫u in 0..Ccut*x n,Real.sqrt
        (orderedPathB (dim n+1) (M n).bf (M n).hf u-(orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))≤I n:=
      intervalIntegral.integral_mono_interval le_rfl (mul_nonneg hCcut hx.le)
        (by nlinarith : Ccut*x n≤(Ccut+1)*x n) (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) HIbig
    apply H.trans
    have Hcost:=mul_le_mul_of_nonneg_left HImono (show 0≤C*x n by positivity)
    have HE : C*x n*I n+C*save n*(x n)^3=err n*(x n)^3:=by
      dsimp only [err]
      field_simp
    dsimp only [NativeOverlapContext.N] at Hcost ⊢
    dsimp only [save] at HE
    rw [←HE]
    nlinarith only [Hcost]

end OAI.SKFluctuations.Cavity
