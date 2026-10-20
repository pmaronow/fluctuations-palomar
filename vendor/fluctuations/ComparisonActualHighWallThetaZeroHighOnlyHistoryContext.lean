module

public import ComparisonActualHighWallThetaZeroHighOnlySourceField
public import ComparisonActualHighWallThetaZeroChildComparableClocks
public import ComparisonActualHighOnlyWallHistoryContext

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}

theorem ActualWeakHighOnlyHistoryChain.exists_theta_zero_wall_comparable_context
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hTpos : 0 < T)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (hsame : ∀ᶠn in atTop,(root n).data.s=(P n).data.s)
    (hunit : ∀ᶠn in atTop,(P n).xs≤1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (P n).data.N delta
      (P n).data.E (P n).lam≤(P n).xs)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).data.d (P n).lam
      (P n).xs/(P n).xs^2) atTop (𝓝 0))
    (hs : Tendsto (fun n=>(P n).data.s/
      actualChildCutoff (dim n+1) delta c0 (P n).data.d (P n).lam (P n).xs)
      atTop (𝓝 0))
    (hcut : ∀ᶠn in atTop,actualChildCutoff (dim n+1) delta c0 (P n).data.d
      (P n).lam (P n).xs≤comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=(P n).changedBare u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=(P n).changedField u)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    Nonempty (HighOnlyActualComparableBandContext M T) := by
  have Hroot : ∀ᶠn in atTop,
      (∀u∈Icc (0:ℝ) 1,(root n).h u+(root n).b u≤T) ∧
      (root n).h 0=0 := by
    filter_upwards [hT,hb,hh] with n hnT hnb hnh
    constructor
    · intro u hu
      rw [hnb,hnh,←hnT]
      exact (P n).changed_total_clock_le_temperature hu
    · rw [hnh]
      exact (P n).changed_root_field_zero
  have Hfield : ∃C:ℝ,0≤C ∧ ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,
      (root n).h u ≤ C*(comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d+u) := by
    have Hweak := hweak.eventually (gt_mem_nhds (pow_pos hc0 3))
    have Hstrength : ∀ᶠn in atTop,(P n).lam≤
        (actualChildCutoff (dim n+1) delta c0 (P n).data.d (P n).lam (P n).xs)^2 := by
      filter_upwards [hdim.eventually (eventually_theta_zero_strength_le_child_cutoff_sq
        hdelta hC0 hc0 hc01 (show (0:ℝ)<1 by norm_num)
        (show (1:ℝ)≤1 by norm_num) hgapmargin),hunit,htarget,Hweak]
        with n hn hnunit hntarget hnweak
      have Hnumeric : laplaceComparisonStrength (P n).data.d (P n).lam (P n).xs≤
          ((1:ℝ)*c0)^3*(P n).xs^2 := by
        simpa only [one_mul] using
          (div_le_iff₀ (sq_pos_of_pos (P n).hxs)).mp hnweak.le
      simpa only [one_pow,one_mul] using hn (P n) hnunit hntarget Hnumeric
    refine ⟨1,zero_le_one,?_⟩
    filter_upwards [hh,hcut,hunit,Hstrength] with n hnh hncut hnunit hnstrength u hu
    have Hcut := actual_child_cutoff_pos_le_radius (delta:=delta)
      (d:=(P n).data.d) (P n).data.hN hc0
      (P n).hlam (P n).hxs
    have Hcut1 : actualChildCutoff (dim n+1) delta c0 (P n).data.d
        (P n).lam (P n).xs≤1 :=
      Hcut.2.trans ((mul_le_mul_of_nonneg_left hnunit hc0.le).trans
        (by simpa only [mul_one] using hc01))
    have HcutSq : (actualChildCutoff (dim n+1) delta c0 (P n).data.d
        (P n).lam (P n).xs)^2≤
        actualChildCutoff (dim n+1) delta c0 (P n).data.d (P n).lam (P n).xs := by
      have Hprod := mul_nonneg Hcut.1.le (sub_nonneg.mpr Hcut1)
      nlinarith only [Hprod]
    rw [hnh,one_mul]
    exact ((P n).changed_field_le_selected_strength hu).trans
      (by linarith only [hnstrength,HcutSq,hncut,hu.1])
  have Hbare : ∀ᶠn in atTop,
      ∀Q:ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      Q.data.s=(root n).data.s →
        NativePullbackClockRegularity Q.alpha.val.val (root n).b (root n).h 0 1 := by
    filter_upwards [hsame,hb,hh] with n hns hnb hnh Q hQ
    have HB:(root n).b=(P n).changedBare := funext hnb
    have HH:(root n).h=(P n).changedField := funext hnh
    rw [HB,HH]
    exact (P n).changed_pullback_on_high_only_child_profile Q (hQ.trans hns)
  have Htotal := H.total_root Hroot
  obtain ⟨Cf,hCf,Hsource⟩ := H.bare_field_budget hm hdelta hcl hAz hC0 hc0
    hmargin hcapmargin hdim Hfield
  have Hphysical : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,
      ((M n).bf u:ℝ)≤T ∧
      ((M n).hf u:ℝ)≤(Cf+D^2*(Az+1/cl))*((M n).xs+u) := by
    filter_upwards [Htotal,Hsource] with n hn hnS
    exact (M n).small_source_clocks_of_bare_field hcl hAz hCf hn.1 hnS
  have Hinherit := H.cutoff_inherits_root hm hdelta hAz hC0 hc0 hmargin hcapmargin hdim
  have Homit : Tendsto (fun n=>(M n).data.s/comparisonLowerScale
      (M n).context.N (M n).context.E (M n).context.d) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n=>div_nonneg (M n).data.hs.1
      (div_pos (mul_pos (Real.sqrt_pos.mpr (M n).data.hN) (M n).data.hE)
        (M n).data.hd).le)) _ hs
    filter_upwards [H.same_omission,hsame,Hinherit,hcut] with n hnS hnroot hnI hnC
    rw [hnS,hnroot]
    exact div_le_div_of_nonneg_left (P n).data.hs.1.le
      (actual_child_cutoff_pos_le_radius (P n).data.hN hc0
        (P n).hlam (P n).hxs).1 (hnC.trans hnI)
  have Hpositive := theta_zero_first_child_comparable_bare_clocks hdelta hcl hAz hC0
    hc0 hc01 hgapmargin dim hdim P hT hunit htarget hweak hs
  have Hseed := SequentialComparableBareClocks.toHighOnly Hpositive root hcut hb hh
  exact ⟨⟨hTpos,hxs,Homit,H.pullback Hbare,Htotal,Cf+D^2*(Az+1/cl),
    by positivity,Hphysical,H.comparable_clocks hm hdelta hcl hAz hC0 hc0 hc01
      hmargin hcapmargin hgapmargin hdim Hseed⟩⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
