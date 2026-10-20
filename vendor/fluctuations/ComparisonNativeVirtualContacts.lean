module

public import ComparisonCalibrationWeightedMass
public import ComparisonNativeMinimumPotential
public import ComparisonGlobalProfileRigidity
public import ComparisonVirtualMovingContactExtension

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000

structure NativeVirtualContactData (delta : ℝ) where
  N : ℝ
  U : ℝ
  L : ℝ
  E : ℝ
  d : ℝ
  origin : ℝ
  u0 : ℝ
  hN : 0 < N
  hU : 0 < U
  hL : 0 < L
  hE : 0 < E
  hd : 0 < d
  hLU : L ≤ U
  horigin : 0 ≤ origin
  hwork : origin ≤ 1
  alpha : inverseIntegralConstraints origin u0 (comparisonFloor N delta U) (comparisonCap N delta U L E d)
  H : ℝ → ℝ
  hH : AbsolutelyContinuousOnInterval H origin 1
  hfloor : ∀ᵐ r,r∈Icc origin 1  →  0 < H r  →  deriv alpha.val.val r=comparisonFloor N delta U r
  hcap : ∀ᵐ r,r∈Icc origin 1  →  H r < 0  →  deriv alpha.val.val r=comparisonCap N delta U L E d (alpha.val.val r)

namespace NativeVirtualContactData
variable {delta : ℝ}
abbrev k (D : NativeVirtualContactData delta) := comparisonFloor D.N delta D.U
abbrev M (D : NativeVirtualContactData delta) := comparisonCap D.N delta D.U D.L D.E D.d
abbrev c (D : NativeVirtualContactData delta) := D.k 1

theorem hc (D : NativeVirtualContactData delta) : 0 < D.c := comparisonFloor_pos D.hN D.hU (by norm_num)
theorem hk (D : NativeVirtualContactData delta) : ContinuousOn D.k (Icc D.origin 1) :=
  comparisonFloor_continuousOn D.hN D.hU D.horigin
theorem hkc (D : NativeVirtualContactData delta) : ∀r∈Icc D.origin 1,D.c ≤ D.k r :=
  fun _r hr=>comparisonFloor_lower_on D.hN D.hU D.horigin hr
theorem hm (D : NativeVirtualContactData delta) : MonotoneOn D.M (Icc (0:ℝ) 1) :=
  comparisonCap_monotoneOn D.hN D.hU.le D.hL D.hE D.hd.le
theorem hM (D : NativeVirtualContactData delta) : 0 ≤ D.M 1 :=
  comparisonCap_nonneg D.hN D.hU.le D.hL D.hE D.hd.le zero_le_one

def radius (D : NativeVirtualContactData delta) : ℝ → ℝ :=
  comparisonCalibrationConstrainedRadius D.hwork D.hc D.hk D.hkc D.hm D.hM D.alpha

def travel (D : NativeVirtualContactData delta) : ℝ :=
  (D.L/D.N^delta)*Real.log ((1+D.U)/D.U)

def floorMass (D : NativeVirtualContactData delta) : ℝ := D.N^(-delta)*D.U

theorem travel_pos (D : NativeVirtualContactData delta) : 0 < D.travel :=
  mul_pos (div_pos D.hL (Real.rpow_pos_of_pos D.hN _))
    (Real.log_pos ((one_lt_div D.hU).mpr (by linarith)))

theorem travel_bound (D : NativeVirtualContactData delta) {a b : ℝ}
    (ha : D.origin ≤ a) (hb : b ≤ 1) (hab : a ≤ b) (hn : ∀r∈Ioo a b,D.H r < 0) :
    b-a ≤ D.travel := by
  rcases eq_or_lt_of_le hab with he|hlt
  · rw [←he,sub_self];exact D.travel_pos.le
  · exact comparison_calibration_shifted_cap_travel D.hN D.hU D.hL D.hE D.hd D.hc D.hk D.hkc
      D.alpha D.H D.hcap ha hb hlt hn

theorem negative_point_near_contact (D : NativeVirtualContactData delta) {r : ℝ}
    (hr : D.origin ≤ r) (hend : r+2*D.travel ≤ 1) (hn : D.H r < 0) :
    ∃z∈Icc r (r+2*D.travel),D.H z=0 := by
  have hHc : ContinuousOn D.H (Icc D.origin 1) := by
    simpa only [uIcc_of_le D.hwork] using D.hH.continuousOn
  by_contra hfalse
  have hzero : ∀z∈Icc r (r+2*D.travel),D.H z≠0 := by simpa only [not_exists,not_and] using hfalse
  have hnegative : ∀t∈Ioo r (r+2*D.travel),D.H t < 0 := by
    intro t ht
    by_contra hh
    have hHt : 0 ≤ D.H t := not_lt.mp hh
    have hsub : Icc r t ⊆ Icc D.origin 1 := Icc_subset_Icc hr (ht.2.le.trans hend)
    obtain ⟨z,hz,hHz⟩ := intermediate_value_Icc ht.1.le (hHc.mono hsub) ⟨hn.le,hHt⟩
    exact hzero z ⟨hz.1,hz.2.trans ht.2.le⟩ hHz
  have hh := D.travel_bound hr hend (by linarith [D.travel_pos]) hnegative
  linarith [D.travel_pos]

theorem contact_above_mass_threshold (D : NativeVirtualContactData delta)
    {lo hi v : ℝ} (hv : v∈Icc D.u0 1)
    (hend : hi+2*D.travel ≤ 1)
    (hroom : D.floorMass < D.alpha.val.val hi-max (D.alpha.val.val lo) v) :
    ∃z,lo < z ∧ z ≤ hi+2*D.travel ∧ D.H z=0 ∧ v ≤ D.alpha.val.val z := by
  let a := max lo (D.radius v)
  have hvR : D.alpha.val.val (D.radius v)=v ∧ D.radius v∈Icc D.origin 1 := comparison_calibration_constrained_radius_mass_spec D.hwork D.hc D.hk D.hkc D.hm D.hM D.alpha hv
  have hae : D.alpha.val.val a=max (D.alpha.val.val lo) v := by
    dsimp only [a]
    rw [D.alpha.val.property.2.map_max,hvR.1]
  have hmass0 : 0 ≤ D.floorMass := mul_nonneg (Real.rpow_pos_of_pos D.hN _).le D.hU.le
  have hab : a < hi := by
    by_contra hn
    have hh := D.alpha.val.property.2 (not_lt.mp hn)
    rw [hae] at hh
    linarith
  have ha : D.origin ≤ a := hvR.2.1.trans (le_max_right _ _)
  have hb : hi ≤ 1 := by linarith [D.travel_pos]
  have hsub : Icc a hi ⊆ Icc D.origin 1 := Icc_subset_Icc ha hb
  have hfloorLocal : ∀ᵐ r,r∈Icc a hi  →  0 < D.H r  →  deriv D.alpha.val.val r=D.k r := by
    filter_upwards [D.hfloor] with r hr hri
    exact hr (hsub hri)
  have hkAll : IntervalIntegrable D.k volume 0 1 :=
    (comparisonFloor_continuousOn D.hN D.hU (show (0:ℝ) ≤ 0 from le_rfl)).intervalIntegrable_of_Icc zero_le_one
  have hkBound : (∫r in a..hi,D.k r) ≤ D.floorMass :=
    (intervalIntegral.integral_mono_interval (D.horigin.trans ha) hab.le hb
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr;exact (comparisonFloor_pos D.hN D.hU hr.1.le).le)
      hkAll).trans (comparisonFloor_total_mass D.hN D.hU)
  have hroom' : (∫r in a..hi,D.k r) < D.alpha.val.val hi-D.alpha.val.val a := by rw [hae];exact hkBound.trans_lt hroom
  obtain ⟨r,hr,hHr⟩ := virtual_positive_mass_has_nonpositive_anchor hab
    ((inverseIntegralConstraints_lipschitz D.hm D.hM D.alpha.property).mono hsub) hfloorLocal hroom'
  have hAlpha : v ≤ D.alpha.val.val r := by
    have hh := D.alpha.val.property.2 hr.1.le
    rw [hae] at hh
    exact (le_max_right _ _).trans hh
  by_cases he : D.H r=0
  · exact ⟨r,(le_max_left lo (D.radius v)).trans_lt hr.1,by linarith [hr.2,D.travel_pos],he,hAlpha⟩
  · obtain ⟨z,hz,hHz⟩ := D.negative_point_near_contact (ha.trans hr.1.le)
      (by linarith [hr.2]) (lt_of_le_of_ne hHr he)
    exact ⟨z,((le_max_left lo (D.radius v)).trans_lt hr.1).trans_le hz.1,
      by linarith [hz.2,hr.2],hHz,hAlpha.trans (D.alpha.val.property.2 hz.1)⟩

end NativeVirtualContactData

def NativeOverlapMinimum.Potential.toVirtualContactData
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {minimum : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : minimum.Potential) : NativeVirtualContactData delta where
  N := minimum.context.N
  U := minimum.context.U
  L := minimum.context.L
  E := minimum.context.E
  d := minimum.context.d
  origin := 0
  u0 := 0
  hN := minimum.context.hN
  hU := minimum.context.hU
  hL := minimum.context.hL
  hE := minimum.context.hE
  hd := minimum.context.hd
  hLU := min_le_left _ _
  horigin := le_rfl
  hwork := zero_le_one
  alpha := minimum.alpha
  H := p.H
  hH := p.hH
  hfloor := p.hfloor
  hcap := p.hbang

theorem comparison_native_virtual_geometric_rates
    {delta CU : ℝ} (hdelta : 0 < delta) (hCU : 0 ≤ CU)
    (D : ℕ → NativeVirtualContactData delta) (x : ℕ → ℝ)
    (hx : ∀n,0 < x n) (hN : Tendsto (fun n=>(D n).N) atTop atTop)
    (hE : ∀n,(D n).U=comparisonSmallMass (D n).N (D n).E)
    (hE1 : ∀n,(D n).E ≤ 1) (hN2 : ∀n,2 ≤ (D n).N)
    (hU : ∀n,(D n).U/x n ≤ CU) :
    Tendsto (fun n=>(D n).floorMass/x n) atTop (𝓝 0) ∧
    Tendsto (fun n=>(D n).travel/x n) atTop (𝓝 0) := by
  have hfloorUpper n : (D n).floorMass/x n ≤ CU*(D n).N^(-delta) := by
    unfold NativeVirtualContactData.floorMass
    have hh := mul_le_mul_of_nonneg_left (hU n) (Real.rpow_pos_of_pos (D n).hN (-delta)).le
    simpa only [mul_div_assoc,mul_comm CU] using hh
  have hfloor0 := (tendsto_rpow_neg_atTop hdelta).comp hN |>.const_mul CU
  have hFloorNonneg n : 0 ≤ (D n).floorMass/x n := div_nonneg
    (mul_nonneg (Real.rpow_pos_of_pos (D n).hN _).le (D n).hU.le) (hx n).le
  have htravelUpper n : (D n).travel/x n ≤ CU*(2*Real.log (D n).N/(D n).N^delta) := by
    have hL := div_le_div_of_nonneg_right (D n).hLU (hx n).le
    have hlog := comparison_native_cap_log_le (hN2 n) (D n).hE (hE1 n)
    rw [←hE n] at hlog
    have hlog0 : 0 ≤ Real.log ((1+(D n).U)/(D n).U) :=
      Real.log_nonneg ((le_div_iff₀ (D n).hU).mpr (by linarith [(D n).hU]))
    have hden : 0 < (D n).N^delta := Real.rpow_pos_of_pos (D n).hN _
    have h1 := mul_le_mul_of_nonneg_right (hL.trans (hU n)) (div_nonneg hlog0 hden.le)
    have h2 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hden.le) hCU
    have he : (D n).travel/x n=((D n).L/x n)*(Real.log ((1+(D n).U)/(D n).U)/(D n).N^delta) := by
      unfold NativeVirtualContactData.travel
      field_simp
    rw [he]
    exact h1.trans h2
  have htravel0 := (comparison_weighted_cap_log_rate_tendsto (fun n=>(D n).N) hdelta hN).const_mul CU
  exact ⟨squeeze_zero hFloorNonneg hfloorUpper (by simpa only [Function.comp_def,mul_zero] using hfloor0),
    squeeze_zero (fun n=>div_nonneg (D n).travel_pos.le (hx n).le) htravelUpper (by simpa only [mul_zero] using htravel0)⟩

theorem comparison_native_virtual_contact_eventually
    {delta t c eta : ℝ} (D : ℕ → NativeVirtualContactData delta) (x : ℕ → ℝ)
    (V : ℝ → ℝ) (_hV : Monotone V) (hsupport : t∈comparisonIncrementSupport V)
    (_ht : 0 ≤ t) (hc : 0 < c) (heta : 0 < eta) (hRight : ∀eps,0 < eps  →  eps ≤ eta  →  c < V (t+eps))
    (hx : ∀n,0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hu0 : Tendsto (fun n=>(D n).u0/x n) atTop (𝓝 0))
    (hCDF : ∀s,Tendsto (fun n=>(D n).alpha.val.val (x n*s)/x n) atTop (𝓝 (V s)))
    (hfloor : Tendsto (fun n=>(D n).floorMass/x n) atTop (𝓝 0))
    (htravel : Tendsto (fun n=>(D n).travel/x n) atTop (𝓝 0)) :
    ∀eps>0,∀ᶠ n in atTop,∃z,|(z/x n)-t| < eps ∧ (D n).H z=0 ∧ c*x n ≤ (D n).alpha.val.val z := by
  intro eps heps
  let e := min (eps/4) (eta/2)
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have heEta : e ≤ eta := (min_le_right _ _).trans (by linarith)
  have heEps : e ≤ eps/4 := min_le_left _ _
  have hplus := hRight e he heEta
  have hminus := hsupport e he
  have hgap : 0 < V (t+e)-max (V (t-e)) c := sub_pos.mpr (max_lt hminus hplus)
  have hdiff := (hCDF (t+e)).sub ((hCDF (t-e)).max (tendsto_const_nhds (x:=c)))
  have hcost := hdiff.sub hfloor
  have hcostpos := (hcost.eventually (lt_mem_nhds (by simpa only [sub_zero] using hgap)))
  have hvLow := hu0.eventually (gt_mem_nhds hc)
  have hvHigh : ∀ᶠ n in atTop,c*x n<1 := (hx0.const_mul c).eventually (gt_mem_nhds (by norm_num))
  have hT0 : Tendsto (fun n=>(D n).travel) atTop (𝓝 0) := by
    have hh := hx0.mul htravel
    simpa only [mul_zero,mul_div_cancel₀ _ (hx _).ne'] using hh
  have hEnd : ∀ᶠ n in atTop,x n*(t+e)+2*(D n).travel<1 :=
    ((hx0.mul_const (t+e)).add (hT0.const_mul 2)).eventually (gt_mem_nhds (by norm_num))
  have hTsmall := htravel.eventually (gt_mem_nhds he)
  filter_upwards [hcostpos,hvLow,hvHigh,hEnd,hTsmall] with n hcostn hLow hHigh hEndn hTn
  have hv : c*x n∈Icc (D n).u0 1 := ⟨by
    have hh := (div_lt_iff₀ (hx n)).mp hLow
    nlinarith,by nlinarith [hHigh]⟩
  have heMax : max ((D n).alpha.val.val (x n*(t-e))/x n) c=
      max ((D n).alpha.val.val (x n*(t-e))) (c*x n)/x n := by
    rw [←max_div_div_right (hx n).le,mul_div_cancel_right₀ c (hx n).ne']
  have hroom : (D n).floorMass < (D n).alpha.val.val (x n*(t+e))-
      max ((D n).alpha.val.val (x n*(t-e))) (c*x n) := by
    rw [heMax] at hcostn
    have hh : 0 < ((D n).alpha.val.val (x n*(t+e))-
      max ((D n).alpha.val.val (x n*(t-e))) (c*x n)-(D n).floorMass)/x n := by
      simpa only [sub_div] using hcostn
    have hh' := (div_pos_iff_of_pos_right (hx n)).mp hh
    linarith
  obtain ⟨z,hzLow,hzHigh,hHz,hMass⟩ := (D n).contact_above_mass_threshold hv hEndn.le hroom
  have hz0 : t-e < z/x n := (lt_div_iff₀ (hx n)).mpr (by nlinarith [hzLow])
  have hz1 : z/x n ≤ t+e+2*((D n).travel/x n) := by
    apply (div_le_iff₀ (hx n)).mpr
    have hh : (t+e+2*((D n).travel/x n))*x n=x n*(t+e)+2*(D n).travel := by field_simp [(hx n).ne']
    rw [hh]
    exact hzHigh
  refine ⟨z,abs_lt.mpr ⟨by linarith,by linarith⟩,hHz,hMass⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
