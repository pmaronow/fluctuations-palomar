module

public import ComparisonActualHighWallThetaZeroChildPositiveBand
public import ComparisonActualHighWallComparableBandClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 16000000

theorem theta_zero_first_child_comparable_bare_clocks
    {m delta cl cu Az C0 Ct D Bclock c0 T:ℝ}
    (hdelta:0<delta) (hcl:0<cl) (hAz:0≤Az) (hC0:0<C0)
    (hc0:0<c0) (hc01:c0≤1) (hmargin:0<9*m-298*delta)
    (dim:ℕ→ℕ) (hdim:Tendsto dim atTop atTop)
    (M:(n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT:∀ᶠn in atTop,(M n).data.T=T)
    (hunit:∀ᶠn in atTop,(M n).xs≤1)
    (htarget:∀ᶠn in atTop,comparisonConditionalScale (M n).data.N delta
      (M n).data.E (M n).lam≤(M n).xs)
    (hweak:Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam
      (M n).xs/(M n).xs^2) atTop (𝓝 0))
    (hs:Tendsto (fun n=>(M n).data.s/
      actualChildCutoff (dim n+1) delta c0 (M n).data.d (M n).lam (M n).xs)
      atTop (𝓝 0)):
    SequentialComparableBareClocks
      (fun n=>actualChildCutoff (dim n+1) delta c0 (M n).data.d
        (M n).lam (M n).xs)
      (fun n=>(M n).changedBare) (fun n=>(M n).changedField) T:=by
  intro y hy hay c Cmass epsilon hc hCmass heps
  let C:=max 1 (Az+Cmass/cl)
  let eta:=min 1 (epsilon/(C+1))
  have hC:1≤C:=le_max_left _ _
  have hC0':0≤C:=zero_le_one.trans hC
  have heta:0<eta:=lt_min zero_lt_one (div_pos heps (by positivity))
  have heta1:eta≤1:=min_le_left _ _
  have Het:eta*(C+1)≤epsilon:=
    (le_div_iff₀ (by positivity:0<C+1)).mp (min_le_right _ _)
  have Het2:eta^2≤eta:=by nlinarith
  have hsave:eta^2≤epsilon ∧ C*eta^2≤epsilon:=by
    have H:=mul_le_mul_of_nonneg_left Het2 hC0'
    constructor <;> nlinarith only [Het,Het2,H,heta.le,hC,mul_nonneg heta.le hC0']
  have Hweak:=hweak.eventually (gt_mem_nhds (pow_pos (mul_pos heta hc0) 3))
  have Hs:=hs.eventually (eventually_le_nhds hc)
  filter_upwards [hdim.eventually (eventually_theta_zero_child_positive_band_increments
    hdelta hcl hAz hC0 hc0 hc01 heta heta1 hCmass hmargin),
    Hweak,Hs,hunit,htarget,hay,hT]
    with n hn hnweak hnS hnunit hntarget hny hnT
  intro u hu
  have ha:0<actualChildCutoff (dim n+1) delta c0 (M n).data.d
      (M n).lam (M n).xs:=
    (actual_child_cutoff_pos_le_radius (M n).data.hN hc0 (M n).hlam (M n).hxs).1
  have hypos:0<y n:=ha.trans_le hny
  have hsy:(M n).data.s≤c*y n:=
    ((div_le_iff₀ ha).mp hnS).trans
      (mul_le_mul_of_nonneg_left hny hc.le)
  have Hweak':laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs≤
      (eta*c0)^3*(M n).xs^2:=
    (div_le_iff₀ (sq_pos_of_pos (M n).hxs)).mp hnweak.le
  have H:=hn (M n) hnunit hntarget Hweak' (M n).hzxs
    (y n) hny u ⟨hsy.trans hu.1,hu.2⟩
  rw [hnT] at H
  exact ⟨H.1.trans (mul_le_mul_of_nonneg_right hsave.1 (sq_nonneg (y n))),
    H.2.trans (mul_le_mul_of_nonneg_right hsave.2 (pow_nonneg hypos.le 3))⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
