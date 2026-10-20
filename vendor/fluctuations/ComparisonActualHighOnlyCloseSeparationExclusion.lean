module

public import ComparisonActualHighOnlyCloseChildBarrier
public import ComparisonNativeChildRampRoom
public import ComparisonNativeChildGainSaving

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem eventually_actual_high_only_child_excludes_close_upward
    {delta gamma Dbound m c0 cScale cMove rho qRamp qBand:ℝ}
    (hdelta:0 < delta) (hgamma:0 < gamma) (hm:0 < m) (hc0:0 < c0)
    (hcScale:0 < cScale) (hcScale1:cScale ≤ 1)
    (hcMove:0 < cMove) (hcMove1:cMove ≤ 1) (hrho:0 < rho) (hrho1:rho ≤ 1) (hqRamp:0 < qRamp) (hqBand:0 < qBand) :
    ∀ᶠ n:ℕ in atTop,∀a:ActualHighOnlyChildBarrierCall n delta,∀x y start stop finish:ℝ,
      a.context.d ≤ Dbound → Real.sqrt (n:ℝ)*a.context.E ≤ a.context.d^2 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*a.context.d ≤ a.context.E →
      x∈Ioc (0:ℝ) 1 → y∈Ioc (0:ℝ) 1 → comparisonLowerScale n a.context.E a.context.d ≤ x →
      cScale*x ≤ y → a.e x ≤ x^2 →
      a.childRadius=c0*x → a.childLam=(c0*x)^2 →
      a.err ≤ (n:ℝ)^(20*delta)*actualChildErrorBudget n delta c0 a.context.d a.lam x →
      a.context.s ≤ start → start < stop → stop ≤ finish → finish ≤ 1 →
      qRamp*y ≤ stop-start → qBand*y ≤ finish-stop →
      y ≤ a.Z start → ((∀u∈Icc start 1,cMove*y ≤ a.R u) ∨ a.e 0 ≤ a.D y) →
      (∀u∈Icc stop finish,a.R u ≤ (1-rho)*y) → False := by
  have hroom:=eventually_comparison_native_upward_ramp_room (gamma:=gamma) (D:=Dbound)
    (m:=m) (delta:=delta) (cScale:=cScale) (q:=qRamp) hgamma hm hdelta hcScale hqRamp
  have hforceRoom:=eventually_comparison_native_upward_ramp_room (gamma:=gamma) (D:=Dbound)
    (m:=m) (delta:=delta) (cScale:=rho*cScale) (q:=1) hgamma hm hdelta (by positivity) zero_lt_one
  have hsmall:=eventually_actual_child_error_below_separated_gain (delta:=delta) (c0:=c0)
    (cScale:=cScale) (A:=cMove*rho^3*qBand/200) hdelta hc0 hcScale hcScale1 (by positivity)
  filter_upwards [hroom,hforceRoom,hsmall] with n hnroom hnforce hnsmall
  intro a x y start stop finish hdD hupper hlower hx hy hax hscale hweak hdc hlc herr
    ha hab hbf hf hwidthRamp hwidthBand hZlarge hroute hRupper
  have hscaleA:cScale*comparisonLowerScale n a.context.E a.context.d ≤ y:=
    (mul_le_mul_of_nonneg_left hax hcScale.le).trans hscale
  obtain ⟨_hforceOld,hspeedOld⟩:=hnroom a.context.E a.context.d y start stop a.context.hE a.context.hd
    hdD hupper hlower hscaleA hwidthRamp
  obtain ⟨hforce,_⟩:=hnforce a.context.E a.context.d (rho*y) 0 (rho*y) a.context.hE a.context.hd
    hdD hupper hlower (by nlinarith [mul_le_mul_of_nonneg_left hscaleA hrho.le]) (by simp)
  have hspeed:(a.context.M 0)⁻¹+(1-rho/2)*y/(stop-start) ≤
      ((n:ℝ)^(2*delta)*a.context.U)^2/((n:ℝ)^delta*a.context.U^2):=by
    apply le_trans _ hspeedOld
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr hab).le
    nlinarith [hy.1]
  have hgain:=comparison_actual_high_only_upward_close_child_error_lower a hcMove hcMove1 hrho hrho1 hy.1 ha hab hbf hf
    hqBand.le hwidthBand hforce hspeed hZlarge hroute hRupper
  have herror:=hnsmall a.context.d a.lam x y a.context.hd.ne' a.hlam hx hy hscale hweak
  rw [←hlc,←hdc] at herror
  have hh:=mul_le_mul_of_nonneg_left herr (by norm_num : (0:ℝ) ≤ 4)
  linarith

theorem eventually_actual_high_only_child_excludes_close_downward
    {delta gamma Dbound m c0 cScale C rho qTravel qBand:ℝ}
    (hdelta:0 < delta) (hgamma:0 < gamma) (hm:0 < m) (hc0:0 < c0)
    (hcScale:0 < cScale) (hcScale1:cScale ≤ 1)
    (hC:1 ≤ C) (hrho:0 < rho) (hrho1:rho ≤ 1) (hqTravel:0 < qTravel) (hqBand:0 < qBand) :
    ∀ᶠ n:ℕ in atTop,∀a:ActualHighOnlyChildBarrierCall n delta,∀x y start stop departure finish:ℝ,
      a.context.d ≤ Dbound → Real.sqrt (n:ℝ)*a.context.E ≤ a.context.d^2 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*a.context.d ≤ a.context.E →
      x∈Ioc (0:ℝ) 1 → y∈Ioc (0:ℝ) 1 → comparisonLowerScale n a.context.E a.context.d ≤ x →
      cScale*x ≤ y → a.e x ≤ x^2 →
      a.childRadius=c0*x → a.childLam=(c0*x)^2 →
      a.err ≤ (n:ℝ)^(20*delta)*actualChildErrorBudget n delta c0 a.context.d a.lam x →
      a.context.s ≤ start → start ≤ stop → stop ≤ departure → departure ≤ finish → finish ≤ 1 →
      qTravel*y ≤ finish-departure → qBand*y ≤ stop-start → a.Z finish ≤ (1-rho)*y →
      (∀u∈Icc (0:ℝ) finish,a.R u ≤ C*y) →
      (∀u∈Icc start stop,y ≤ a.R u) → False := by
  have hroom:=eventually_comparison_native_upward_ramp_room (gamma:=gamma) (D:=Dbound)
    (m:=m) (delta:=delta) (cScale:=rho*cScale) (q:=1) hgamma hm hdelta (by positivity) zero_lt_one
  have htravel:=eventually_comparison_native_downward_ramp_room (gamma:=gamma) (m:=m)
    (delta:=delta) (cScale:=cScale) (q:=qTravel) hgamma hm hdelta hcScale hqTravel
  have hC0:0 < C:=zero_lt_one.trans_le hC
  have hsmall:=eventually_actual_child_error_below_separated_gain (delta:=delta) (c0:=c0)
    (cScale:=cScale) (A:=qBand*rho^2/(400*C^2)) hdelta hc0 hcScale hcScale1 (by positivity)
  filter_upwards [hroom,htravel,hsmall] with n hnroom hntravel hnsmall
  intro a x y start stop departure finish hdD hupper hlower hx hy hax hscale hweak hdc hlc herr
    ha hab hstop hb hf hwidthTravel hwidthBand hZsmall hRupper hRlarge
  have hscaleA:cScale*comparisonLowerScale n a.context.E a.context.d ≤ y:=
    (mul_le_mul_of_nonneg_left hax hcScale.le).trans hscale
  obtain ⟨hforce,hspeed⟩:=hnroom a.context.E a.context.d (rho*y) 0 (rho*y) a.context.hE a.context.hd
    hdD hupper hlower (by nlinarith [mul_le_mul_of_nonneg_left hscaleA hrho.le]) (by simp)
  have hspeed':(a.context.M 0)⁻¹ ≤
      ((n:ℝ)^(2*delta)*a.context.U)^2/((n:ℝ)^delta*a.context.U^2):=by
    have hp:0 ≤ 2*(rho*y)/(rho*y-0):=div_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg hrho.le hy.1.le))
      (by simpa using mul_nonneg hrho.le hy.1.le)
    exact (le_add_of_nonneg_right hp).trans hspeed
  have ht:=hntravel a.context.E a.context.d y a.context.hE a.context.hd hupper hlower hscaleA
  have htravel':departure+reciprocalFloorTime ((n:ℝ)^delta*a.context.U^2)
      ((n:ℝ)^(2*delta)*a.context.U) 1 ≤ finish:=by
    have hh:=add_le_add_left ht departure
    linarith
  have hgain:=comparison_actual_high_only_downward_close_child_error_lower a hC hrho hrho1 hy.1 hy.2 ha hab hstop hb hf
    hqBand.le hwidthBand hforce hspeed' htravel' hZsmall hRupper hRlarge
  have herror:=hnsmall a.context.d a.lam x y a.context.hd.ne' a.hlam hx hy hscale hweak
  rw [←hlc,←hdc] at herror
  have hh:=mul_le_mul_of_nonneg_left herr (by norm_num : (0:ℝ) ≤ 4)
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
