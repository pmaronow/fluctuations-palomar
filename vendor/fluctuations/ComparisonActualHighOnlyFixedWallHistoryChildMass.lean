module

public import ComparisonActualHighOnlyFixedWallHistory
public import ComparisonNativeActualChildParameterGrowth

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 24000000
namespace ActualHighOnlyOverlapMinimum

theorem ActualFixedWallHighOnlyHistory.eventually_mass_below_child_cutoff
    {m cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hAz : 0≤Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hdim : Tendsto dim atTop atTop)
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock}
    (G : ActualFixedWallHighOnlyHistory M T c0)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).context.N
      (m/10000) (M n).context.E (M n).lam≤(M n).xs)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0)) :
    ∀ᶠn in atTop,(M n).data.s≤actualChildCutoff (dim n+1) (m/10000)
      c0 (M n).context.d (M n).lam (M n).xs := by
  obtain ⟨HwallMass, HfirstCut, _⟩ := G.root_cutoff_gates hm hmsmall hC0 hc0 hdim
  have hdelta : 0 < m/10000 := by positivity
  have hmargin : (m/10000)/4 < 3*m-99*(m/10000) := by linarith
  have hcapmargin : 100*(m/10000) < (1:ℝ)/3+m := by linarith
  have Hdim : Tendsto (fun n=>dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  have Hparam := Hdim.eventually
    (eventually_actual_child_parameters_from_target hm hdelta
      (one_div_pos.mpr hC0) hc0 hmargin)
  have HrootMass := HwallMass.eventually
    (eventually_le_nhds zero_lt_one)
  have Hcut := G.history.cutoff_inherits_root hm hdelta hAz hC0 hc0
    hmargin hcapmargin hdim
  have Hweak := hweak.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [G.history.same_omission,G.same_mass,HrootMass,HfirstCut,Hcut,Hparam,Hweak,htarget]
    with n hnS hnSame hnMass hnFirstCut hnCut hnParam hnWeak hnTarget
  have hwallCut : 0 < actualChildCutoff (dim n+1) (m/10000) c0
      (G.wall n).data.d ((G.wall n).data.d^2) (G.wall n).xs :=
    (actual_child_cutoff_pos_le_radius (G.wall n).data.hN hc0
      (sq_pos_of_pos (G.wall n).data.hd) (G.wall n).hxs).1
  have hsRoot : (G.root n).data.s≤comparisonLowerScale
      (G.root n).context.N (G.root n).context.E (G.root n).context.d := by
    rw [hnSame]
    exact ((div_le_one₀ hwallCut).mp hnMass).trans hnFirstCut
  have hweakPoint : laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs≤(M n).xs^2 :=
    (div_le_one₀ (sq_pos_of_pos (M n).hxs)).mp hnWeak.le
  have hlo : (1/C0)*((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*
      (M n).context.d≤(M n).context.E := by
    have H := (div_le_iff₀ hC0).mpr
      (by simpa only [mul_comm] using (M n).hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul]
      using H
  have hup : (M n).context.E≤(M n).context.d^2/
      Real.sqrt ((dim n+1:ℕ):ℝ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr (M n).context.hN)).mpr
      (by simpa only [mul_comm] using (M n).hupper)
  have hp := hnParam (M n).context.d (M n).lam (M n).context.E
    (M n).xs (M n).context.hd (M n).hlam (M n).hld
    (M n).context.hE (M n).hxs hlo hup hnTarget hweakPoint
  rw [hnS]
  exact hsRoot.trans (hnCut.trans hp.2.2.2.1)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
