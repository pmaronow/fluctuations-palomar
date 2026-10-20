module

public import ActualOuterCalibrationSelection
public import ComparisonScalarPrimitives

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 4000000

def comparisonCalibrationFloor (H R : ℝ→ℝ) : Set ℝ := {u | 0 < H (R u)}

def comparisonCalibrationCost (D rho bare weighted : ℝ→ℝ) (floor : Set ℝ)
    (T x delta B u : ℝ) : ℝ :=
  (floorᶜ.indicator (fun u=>|D u|) u)/(delta*x)+
    (floorᶜ.indicator (fun u=>|rho u|) u)/(B*x^3)+
    (floorᶜ.indicator (fun u=>|bare u|) u)/(T*B*x^3)+
    (floorᶜ.indicator (fun u=>|weighted u|) u)/(T*B*x^3)+floor.indicator (fun _=>1) u

theorem comparison_calibration_cost_nonnegative
    (D rho bare weighted : ℝ→ℝ) (floor : Set ℝ) {T x delta B u : ℝ}
    (hT : 0<T) (hx : 0<x) (hd : 0<delta) (hB : 0<B) :
    0 ≤ comparisonCalibrationCost D rho bare weighted floor T x delta B u := by
  unfold comparisonCalibrationCost
  exact add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (div_nonneg (Set.indicator_nonneg (fun _ _=>abs_nonneg _) _) (mul_pos hd hx).le)
      (div_nonneg (Set.indicator_nonneg (fun _ _=>abs_nonneg _) _) (mul_pos hB (pow_pos hx 3)).le))
    (div_nonneg (Set.indicator_nonneg (fun _ _=>abs_nonneg _) _) (by positivity)))
    (div_nonneg (Set.indicator_nonneg (fun _ _=>abs_nonneg _) _) (by positivity))) (Set.indicator_nonneg (fun _ _=>by norm_num) _)

theorem comparison_calibration_cost_budget
    (D rho bare weighted : ℝ→ℝ) (floor : Set ℝ) {T x delta B a z : ℝ}
    (hT : 0<T) (hx : 0<x) (hd : 0<delta) (hB : 0<B) (haz : a<z)
    (hD : IntervalIntegrable (floorᶜ.indicator (fun u=>|D u|)) volume a z)
    (hR : IntervalIntegrable (floorᶜ.indicator (fun u=>|rho u|)) volume a z)
    (hBare : IntervalIntegrable (floorᶜ.indicator (fun u=>|bare u|)) volume a z)
    (hW : IntervalIntegrable (floorᶜ.indicator (fun u=>|weighted u|)) volume a z)
    (hF : IntervalIntegrable (floor.indicator (fun _ : ℝ=>(1 : ℝ))) volume a z)
    (hDb : (∫u in a..z,floorᶜ.indicator (fun u=>|D u|) u) ≤ (delta*x)*(z-a)/8)
    (hRb : (∫u in a..z,floorᶜ.indicator (fun u=>|rho u|) u) ≤ (B*x^3)*(z-a)/8)
    (hBb : (∫u in a..z,floorᶜ.indicator (fun u=>|bare u|) u) ≤ (T*B*x^3)*(z-a)/8)
    (hWb : (∫u in a..z,floorᶜ.indicator (fun u=>|weighted u|) u) ≤ (T*B*x^3)*(z-a)/8)
    (hFb : (∫u in a..z,floor.indicator (fun _ : ℝ=>(1 : ℝ)) u) ≤ (z-a)/8) :
    IntervalIntegrable (comparisonCalibrationCost D rho bare weighted floor T x delta B)
      volume a z ∧
    (∫u in a..z,comparisonCalibrationCost D rho bare weighted floor T x delta B u)<z-a := by
  have hp : 0<delta*x := mul_pos hd hx
  have hq : 0<B*x^3 := mul_pos hB (pow_pos hx 3)
  have hr : 0<T*B*x^3 := by positivity
  refine ⟨((((hD.div_const _).add (hR.div_const _)).add
    (hBare.div_const _)).add (hW.div_const _)).add hF,?_⟩
  unfold comparisonCalibrationCost
  rw [intervalIntegral.integral_add ((((hD.div_const _).add (hR.div_const _)).add
    (hBare.div_const _)).add (hW.div_const _)) hF,
    intervalIntegral.integral_add (((hD.div_const _).add (hR.div_const _)).add
      (hBare.div_const _)) (hW.div_const _),
    intervalIntegral.integral_add ((hD.div_const _).add (hR.div_const _))
      (hBare.div_const _),intervalIntegral.integral_add (hD.div_const _) (hR.div_const _),
    intervalIntegral.integral_div,intervalIntegral.integral_div,
    intervalIntegral.integral_div,intervalIntegral.integral_div]
  have h1 : (∫u in a..z,floorᶜ.indicator (fun u=>|D u|) u)/(delta*x)≤(z-a)/8 :=
    (div_le_iff₀ hp).mpr (by nlinarith)
  have h2 : (∫u in a..z,floorᶜ.indicator (fun u=>|rho u|) u)/(B*x^3)≤(z-a)/8 :=
    (div_le_iff₀ hq).mpr (by nlinarith)
  have h3 : (∫u in a..z,floorᶜ.indicator (fun u=>|bare u|) u)/(T*B*x^3)≤(z-a)/8 :=
    (div_le_iff₀ hr).mpr (by nlinarith)
  have h4 : (∫u in a..z,floorᶜ.indicator (fun u=>|weighted u|) u)/(T*B*x^3)≤(z-a)/8 :=
    (div_le_iff₀ hr).mpr (by nlinarith)
  linarith

theorem comparison_calibration_cost_point
    (D rho bare weighted : ℝ→ℝ) (floor : Set ℝ) {T x delta B u : ℝ}
    (hT : 0<T) (hx : 0<x) (hd : 0<delta) (hB : 0<B)
    (hsmall : comparisonCalibrationCost D rho bare weighted floor T x delta B u<1) :
    u∉floor ∧ |D u|<delta*x ∧
      |rho u|+(|bare u|+|weighted u|)/T<B*x^3 := by
  have h1 : 0≤|D u|/(delta*x) := div_nonneg (abs_nonneg _) (by positivity)
  have h2 : 0≤|rho u|/(B*x^3) := div_nonneg (abs_nonneg _) (by positivity)
  have h3 : 0≤|bare u|/(T*B*x^3) := div_nonneg (abs_nonneg _) (by positivity)
  have h4 : 0≤|weighted u|/(T*B*x^3) := div_nonneg (abs_nonneg _) (by positivity)
  have hn : u∉floor := by
    intro hu
    simp only [comparisonCalibrationCost,Set.indicator_of_mem hu,
      Set.indicator_of_notMem (show u∉floorᶜ from fun h=>h hu),zero_div,zero_add] at hsmall
    linarith
  have hsum : |D u|/(delta*x)+|rho u|/(B*x^3)+
      |bare u|/(T*B*x^3)+|weighted u|/(T*B*x^3)<1 := by
    simpa only [comparisonCalibrationCost,Set.indicator_of_notMem hn,
      Set.indicator_of_mem (show u∈floorᶜ from hn),add_zero] using hsmall
  refine ⟨hn,(div_lt_one₀ (mul_pos hd hx)).mp (by linarith),?_⟩
  have hh : |rho u|/(B*x^3)+|bare u|/(T*B*x^3)+|weighted u|/(T*B*x^3)<1 := by linarith
  have he : |rho u|/(B*x^3)+|bare u|/(T*B*x^3)+|weighted u|/(T*B*x^3)=
      (|rho u|+(|bare u|+|weighted u|)/T)/(B*x^3) := by
    field_simp
    ring
  rw [he] at hh
  exact (div_lt_one₀ (mul_pos hB (pow_pos hx 3))).mp hh

theorem comparison_actual_clock_mean_difference
    {T : ℝ} (hT : T≠0) (n : ℕ) (b h : ℝ → ℝ≥0)
    (h0 b0 e R : ℝ→ℝ) {u : ℝ}
    (hb : (b u : ℝ)=b0 u-e u) (hh : (h u : ℝ)=h0 u+e u*R u) :
    orderedPathS n b h u-actualMixedClock n b h u/T =
      (e u*(orderedPathS n b h u-R u)-
        (h0 u+(b0 u-T)*orderedPathS n b h u))/T := by
  unfold actualMixedClock
  rw [hb,hh]
  field_simp
  ring

theorem comparison_actual_positive_scalar_calibration
    {T x delta B A c0 R0 c2 a1 z1 a2 z2 : ℝ}
    (hT : 0<T) (hx : 0<x) (hd : 0<delta) (hB : 0<B)
    (hBx : B*x^2≤delta) (hsep : R0+4*delta<c2)
    (ha1 : 0≤a1) (ha2 : 0≤a2) (hz1 : z1≤1) (hz2 : z2≤1)
    (hab1 : a1<z1) (hab2 : a2<z2) (hmass : z2≤A*x)
    (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (htotal : ∀u∈Icc (0:ℝ) 1,(h u : ℝ)+(b u : ℝ)≤T)
    (h0 b0 e R H : ℝ→ℝ)
    (hwallb : ∀u∈Ioo a1 z1∪Ioo a2 z2,(b u : ℝ)=b0 u-e u)
    (hwallh : ∀u∈Ioo a1 z1∪Ioo a2 z2,(h u : ℝ)=h0 u+e u*R u)
    (hr1 : ∀u∈Ioo a1 z1,c0*x≤R u ∧ R u≤R0*x)
    (hr2 : ∀u∈Ioo a2 z2,c2*x≤R u)
    (hi : ∀a z, (a=a1 ∧ z=z1)∨(a=a2 ∧ z=z2) →
      IntervalIntegrable (comparisonCalibrationCost
        (fun u=>orderedPathS n b h u-R u) (actualCavityResidual hT n hn b h hb hh htotal)
        (fun u=>h0 u+(b0 u-T)*orderedPathS n b h u)
        (fun u=>e u*(orderedPathS n b h u-R u)) (comparisonCalibrationFloor H R)
        T x delta B) volume a z)
    (hbudget : ∀a z, (a=a1 ∧ z=z1)∨(a=a2 ∧ z=z2) →
      (∫u in a..z,comparisonCalibrationCost
        (fun u=>orderedPathS n b h u-R u) (actualCavityResidual hT n hn b h hb hh htotal)
        (fun u=>h0 u+(b0 u-T)*orderedPathS n b h u)
        (fun u=>e u*(orderedPathS n b h u-R u)) (comparisonCalibrationFloor H R)
        T x delta B u)<z-a) :
    let alpha := actualMixedMassProfile hT n hn b h hb hh htotal
    ∃u1∈Ioo a1 z1,∃u2∈Ioo a2 z2,
      H (R u1)≤0 ∧ H (R u2)≤0 ∧
      (c0-2*delta)*x≤actualMixedClock n b h u1/T ∧
      actualMixedClock n b h u1/T≤(R0+2*delta)*x ∧
      (R0+2*delta)*x<actualMixedClock n b h u2/T ∧
      alpha.val ((R0+2*delta)*x)≤A*x ∧
      |scalarPlantedEnergy hT alpha (actualMixedClock n b h u1/T)-
        actualMixedClock n b h u1/T|≤B*x^3 := by
  dsimp only
  let alpha := actualMixedMassProfile hT n hn b h hb hh htotal
  let D := fun u=>orderedPathS n b h u-R u
  let rho := actualCavityResidual hT n hn b h hb hh htotal
  let bare := fun u=>h0 u+(b0 u-T)*orderedPathS n b h u
  let weighted := fun u=>e u*(orderedPathS n b h u-R u)
  let cost := comparisonCalibrationCost D rho bare weighted (comparisonCalibrationFloor H R) T x delta B
  obtain ⟨u1,hu1,hgood1⟩ := exists_outer_good_point hab1 (hi a1 z1 (Or.inl ⟨rfl,rfl⟩))
    (hbudget a1 z1 (Or.inl ⟨rfl,rfl⟩))
  obtain ⟨u2,hu2,hgood2⟩ := exists_outer_good_point hab2 (hi a2 z2 (Or.inr ⟨rfl,rfl⟩))
    (hbudget a2 z2 (Or.inr ⟨rfl,rfl⟩))
  have hg1 := comparison_calibration_cost_point D rho bare weighted (comparisonCalibrationFloor H R)
    hT hx hd hB hgood1
  have hg2 := comparison_calibration_cost_point D rho bare weighted (comparisonCalibrationFloor H R)
    hT hx hd hB hgood2
  have hpoint u (hu : u∈Ioo a1 z1∪Ioo a2 z2)
      (hg : |D u|<delta*x ∧ |rho u|+(|bare u|+|weighted u|)/T<B*x^3) :
      |actualMixedClock n b h u/T-R u|<2*delta*x ∧
      |scalarPlantedEnergy hT alpha (actualMixedClock n b h u/T)-
        actualMixedClock n b h u/T|<B*x^3 := by
    have he := comparison_actual_clock_mean_difference hT.ne' n b h h0 b0 e R
      (hwallb u hu) (hwallh u hu)
    have hmean : |orderedPathS n b h u-actualMixedClock n b h u/T|≤
        (|bare u|+|weighted u|)/T := by
      rw [he,abs_div,abs_of_pos hT]
      exact div_le_div_of_nonneg_right (by simpa only [sub_zero,zero_sub,abs_neg,add_comm] using (abs_sub_le (weighted u) 0 (bare u))) hT.le
    have hsmallmean : |orderedPathS n b h u-actualMixedClock n b h u/T|<B*x^3 := by
      have hh0 := abs_nonneg (rho u)
      exact hmean.trans_lt (by linarith [hg.2])
    have hscale : B*x^3≤delta*x := by nlinarith [mul_le_mul_of_nonneg_right hBx hx.le]
    have hradius := abs_sub_le (actualMixedClock n b h u/T) (orderedPathS n b h u) (R u)
    rw [abs_sub_comm (actualMixedClock n b h u/T) (orderedPathS n b h u)] at hradius
    have hcavity : |scalarPlantedEnergy hT alpha (actualMixedClock n b h u/T)-orderedPathS n b h u|=|rho u| := by
      change |scalarPlantedEnergy hT alpha (actualMixedClock n b h u/T)-orderedPathS n b h u|=
        |orderedPathS n b h u-scalarPlantedEnergy hT alpha (actualMixedClock n b h u/T)|
      exact abs_sub_comm _ _
    have hcal := abs_sub_le (scalarPlantedEnergy hT alpha (actualMixedClock n b h u/T))
      (orderedPathS n b h u) (actualMixedClock n b h u/T)
    rw [hcavity] at hcal
    exact ⟨by dsimp [D] at hg;linarith [hradius],
      hcal.trans_lt ((add_le_add_right hmean _).trans_lt hg.2)⟩
  have hp1 := hpoint u1 (Or.inl hu1) hg1.2
  have hp2 := hpoint u2 (Or.inr hu2) hg2.2
  have hlow : (c0-2*delta)*x≤actualMixedClock n b h u1/T := by
    have hh1 := (abs_lt.mp hp1.1).1
    have hh2 := (hr1 u1 hu1).1
    nlinarith
  have hhigh : actualMixedClock n b h u1/T≤(R0+2*delta)*x := by
    have hh1 := (abs_lt.mp hp1.1).2
    have hh2 := (hr1 u1 hu1).2
    nlinarith
  have horder : (R0+2*delta)*x<actualMixedClock n b h u2/T := by
    have hh1 := (abs_lt.mp hp2.1).1
    have hh2 := hr2 u2 hu2
    nlinarith [mul_lt_mul_of_pos_right hsep hx]
  have hcdf := actualMixedMassProfile_cdf_cap hT n hn b h hb hh htotal
    (show u2∈Ioc (0:ℝ) 1 from ⟨ha2.trans_lt hu2.1,hu2.2.le.trans hz2⟩) horder
  refine ⟨u1,hu1,u2,hu2,?_,?_,hlow,hhigh,horder,hcdf.trans (hu2.2.le.trans hmass),hp1.2.le⟩
  · exact not_lt.mp hg1.1
  · exact not_lt.mp hg2.1

end OAI.SKFluctuations.LaplaceWindowFormalization
