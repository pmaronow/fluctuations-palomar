module

public import ComparisonNativeActualGeneralBareHistory
public import ComparisonSignedCavityInheritedCanonicalSourceMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T Cbase : ℝ} {dim : ℕ→ℕ}

theorem actual_general_history_compensated_field_le_regular_caps
    {n : ℕ} (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock))
    (b0 h0 : ℝ→ℝ) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hT : 0 ≤ T)
    (hb0 : b0 0 ≤ T)
    (hb : ∀u,M.b u=b0 u-historyMatrixReduction (ps.map (fun P=>P.toHistoryTerm)) u)
    (hh : ∀u,M.h u=h0 u+historyFieldAddition (ps.map (fun P=>P.toHistoryTerm)) u)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (M.hf u:ℝ) ≤ h0 u+actualHistoryRegularCapSum ps+
      (T/cl+bareSourceClockConstant cl Az D)*(M.xs+u) := by
  have Hsum : actualHistoryStrengthSum ps ≤ T := by
    have H:=hb 0
    rw [actual_history_matrix_reduction_zero] at H
    linarith [M.hlb,M.hlam]
  have Hfield : M.h u ≤ h0 u+actualHistoryRegularCapSum ps+(T/cl)*u := by
    rw [hh u]
    have H:=actual_history_field_le_regular_caps ps hcl hu
    have Hup:=mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right Hsum hcl.le) hu.1
    linarith
  have hdD : M.context.d^2 ≤ D^2:=pow_le_pow_left₀ M.context.hd.le M.hdD 2
  have Hstrength:=(laplaceComparisonStrength_le M.context.d M.hlam.le (M.R u)).trans
    (M.hld.trans hdD)
  have hr:=(comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u).1
  have Hcomp:=mul_le_mul_of_nonneg_right Hstrength hr
  have Hrad:=mul_le_mul_of_nonneg_left (M.inverse_radius_le_source_mass hcl hAz hu) (sq_nonneg D)
  have Hextra:=mul_nonneg (div_nonneg hT hcl.le) M.hxs.le
  rw [(M.inherited_clock_coe hu).2]
  dsimp only [bareSourceClockConstant] at *
  nlinarith only [Hfield,Hcomp,Hrad,Hextra]

theorem actual_weak_general_bare_history_small_source_clocks
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hT : 0 ≤ T) (hCbase : 0 ≤ Cbase)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (Hroot : ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(root n).h u+(root n).b u ≤ T) ∧
      (root n).h 0=0)
    (Hfield : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,
      (root n).h u ≤ Cbase*(comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d+u)) :
    ∃Cf : ℝ,0 ≤ Cf ∧ ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf := by
  obtain ⟨ps,Hps⟩:=H.literal_readout_general_bare
  let Ccap:=(Az*max 1 (D^2/c0))*(ps.length:ℝ)
  let Cf:=Cbase+Ccap+T/cl+bareSourceClockConstant cl Az D
  have hCcap : 0 ≤ Ccap:=by dsimp only [Ccap];positivity
  have hCf : 0 ≤ Cf:=by
    have Hb:=bare_source_clock_constant_nonneg (D:=D) hcl hAz
    dsimp only [Cf]
    positivity
  have Hcaps:=eventually_actual_history_regular_caps_le_working_scale (cl:=cl) (cu:=cu)
    (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hAz hC0 hc0 hmargin hcapmargin ps.length
  have Hcut:=H.cutoff_inherits_root hm hdelta hAz hC0 hc0 hmargin hcapmargin hdim
  have Htotal:=H.total_root_general_bare Hroot
  refine ⟨Cf,hCf,?_⟩
  filter_upwards [Hps,Hroot,Hfield,Hcut,Htotal,hdim.eventually Hcaps] with
    n hnps hnroot hnfield hncut hntotal hncaps
  intro u hu
  have Hcap:=hncaps (ps.map (fun P=>P n)) (M n) hnps.1 (by simp)
  have hb0 : (root n).b 0 ≤ T:=by
    have H:=hnroot.1 0 (by norm_num)
    rw [hnroot.2,zero_add] at H
    exact H
  have HB:=actual_general_history_compensated_field_le_regular_caps (M n)
    (ps.map (fun P=>P n)) (root n).b (root n).h hcl hAz hT hb0 hnps.2.1 hnps.2.2 hu
  have Hbase : (root n).h u ≤ Cbase*((M n).xs+u):=(hnfield u hu).trans
    (mul_le_mul_of_nonneg_left (add_le_add (hncut.trans (M n).hscale) (le_refl u)) hCbase)
  have Hextra:=mul_nonneg hCcap hu.1
  have HM:=(M n).inherited_total_clock_le hntotal.1 u hu
  constructor
  · linarith [(M n).hf u |>.coe_nonneg]
  · dsimp only [Cf,Ccap] at *
    nlinarith only [HB,Hbase,Hcap,Hextra]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
