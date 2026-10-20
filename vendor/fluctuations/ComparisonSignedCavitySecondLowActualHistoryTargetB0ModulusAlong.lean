module

public import ComparisonSignedCavitySecondLowActualSoleRootTargetIntegralBudget
public import ComparisonNativeActualRegularInitialMassErrorAlong
public import ComparisonNativeActualSelectedBadHistorySourceClocks
public import ComparisonNativeActualSelectedBadHistoryReadout
public import ComparisonNativeActualShellHistoryThermalBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def ActualSecondLowOriginalSoleRootTargetB0ModulusOnEveryFinalNetAlong
    {dim : ℕ → ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (Couter Temp Cf C : ℝ) (eps : ℕ → ℝ)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ),U ≤ as.length → i < U → partitionPoint 0 as U ≤ Couter*x n →
          let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) i
          let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
          let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)
          |nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun _=>1)
            [g.embed (singleSlot as),g.mark]/2| ≤ C*(x n)^2*Cerr*di+eps n*(x n)^3

theorem actual_second_low_actual_history_initial_mass_error_ratio_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (x : ℕ → ℝ) (hxsx : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (Couter : ℝ) (hCouter : 0 ≤ Couter) :
    Tendsto (fun n=>
      (∫u in 0..(Couter+1)*x n,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(x n)^2) atTop (𝓝 0) := by
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
    filter_upwards [Hps] with n hn
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha Temp epsilon shell ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
      (M n).b (M n).h hn.2.1 hn.2.2 le_rfl zero_le_one le_rfl
  exact regular_minimum_initial_mass_error_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M x hxsx hxlim Hclock (Couter+1) (by linarith)

theorem actual_second_low_actual_history_sole_root_target_B0_modulus_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (Couter : ℝ) (hTemp : 0 ≤ Temp) (hCouter : 0 ≤ Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (x : ℕ → ℝ) (hxsx : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hxW : ∀ᶠn in atTop,x n ≤ (M n).canonicalDirectTestBandScale) :
    ∃(Cf C : ℝ) (eps : ℕ → ℝ),0 ≤ Cf ∧ 0 < C ∧ (∀n,0 ≤ eps n) ∧
      Tendsto eps atTop (𝓝 0) ∧
      ActualSecondLowOriginalSoleRootTargetB0ModulusOnEveryFinalNetAlong Couter Temp Cf C eps M x := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨C,hC,HB⟩:=eventually_actual_minimum_inherited_second_low_sole_root_target_B0_integral_budget
    (D:=D) Bclock Temp Cf Couter hTemp hCf hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let I:=fun n=>(∫u in 0..(Couter+1)*x n,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
    (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))
  let eps:=fun n=>C*Cerr*(I n/(x n)^2)
  have HCerr : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have Hratio:=actual_second_low_actual_history_initial_mass_error_ratio_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim root M epsilon shell hb hh Hhistory
    x hxsx hxlim Couter hCouter
  have Heps : Tendsto eps atTop (𝓝 0) := by
    have HH:=Hratio.const_mul (C*Cerr)
    simpa only [mul_zero] using HH
  have Hupper:=((hxlim.const_mul (Couter+1)).eventually
    (eventually_le_nhds (show (Couter+1)*(0:ℝ) < 1 by simp)))
  refine ⟨Cf,C,eps,hCf,hC,?_,Heps,?_⟩
  · intro n
    have hx : 0 < x n:=(M n).hxs.trans_le (hxsx n)
    have hI : 0 ≤ I n:=intervalIntegral.integral_nonneg (by positivity) (fun _ _=>Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hC.le HCerr) (div_nonneg hI (sq_nonneg _))
  · filter_upwards [hdim.eventually HB,Hsource,hxW,Hupper] with n hn HS hband hupper
    have hx : 0 < x n:=(M n).hxs.trans_le (hxsx n)
    have hxs : (M n).xs ≤ 1:=by
      have hsmall : x n ≤ (Couter+1)*x n:=by nlinarith
      exact (hxsx n).trans (hsmall.trans hupper)
    intro L us hus hret hmesh
    filter_upwards [hn (M n) HS hxs L us hus hret hmesh] with k hk
    dsimp only at hk ⊢
    intro i U hU hi houter
    have HT:=hk i U (x n) hU hi (hxsx n) hband houter
    have hsmallBig : Couter*x n ≤ (Couter+1)*x n:=by nlinarith
    have hsmall : Couter*x n ≤ 1:=hsmallBig.trans hupper
    rw [min_eq_left hsmall] at HT
    have hiBig:=native_intervalIntegrable_sqrt_of_intervalIntegrable
      ((native_comparison_thermal_intervalIntegrable (M n)).mono_set (by
        rw [uIcc_of_le (by positivity : 0 ≤ (Couter+1)*x n),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hupper))
    have Hmono : (∫u in 0..Couter*x n,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)) ≤ I n := by
      apply intervalIntegral.integral_mono_interval le_rfl (mul_nonneg hCouter hx.le) hsmallBig
        (ae_of_all _ (fun u=>Real.sqrt_nonneg _)) hiBig
    have Hcost:=mul_le_mul_of_nonneg_left Hmono (show 0 ≤ C*x n*Cerr by positivity)
    apply HT.trans
    apply (add_le_add le_rfl Hcost).trans
    have Heq : C*x n*Cerr*I n=eps n*(x n)^3:=by
      dsimp only [eps]
      field_simp
    exact le_of_eq (by rw [Heq])

end OAI.SKFluctuations.Cavity
