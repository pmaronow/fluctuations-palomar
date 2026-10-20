module

public import ComparisonActualHighWallPotential
public import ComparisonVirtualShiftedControlFactor

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_controlFactor_pos
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) : 0 < M.controlFactor r := inverseControlFactor_pos _ _ _

def actualVirtualScaledFactor
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ref t : ℝ) : ℝ :=
  M.controlFactor (M.xs*t)/M.controlFactor ref

def actualVirtualMovingFactor
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ref t : ℝ) : ℝ :=
  M.actualVirtualScaledFactor ref (max (ref/M.xs) t)

def actualVirtualScaledGradient
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (t : ℝ) : ℝ :=
  radiusComparisonGradient M.data.g M.alpha.val.val
    (orderedPathS n M.bf M.hf) (orderedPathB n M.bf M.hf) (M.xs*t)/M.xs^3

def Potential.actualVirtualScaledPotential
    {M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (ref t : ℝ) : ℝ :=
  p.H (M.xs*t)/(M.xs^4*M.controlFactor ref)

theorem actual_virtual_moving_factor_eq_one
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ref : ℝ) {t : ℝ} (ht : t ≤ ref/M.xs) :
    M.actualVirtualMovingFactor ref t=1 := by
  have he : M.xs*(ref/M.xs)=ref := by field_simp [M.hxs.ne']
  simp only [actualVirtualMovingFactor,max_eq_left ht,actualVirtualScaledFactor,he,
    div_self (M.actual_controlFactor_pos ref).ne']

theorem actual_virtual_moving_factor_eq_scaled
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ref : ℝ) {t : ℝ} (ht : ref/M.xs ≤ t) :
    M.actualVirtualMovingFactor ref t=M.actualVirtualScaledFactor ref t := by
  simp only [actualVirtualMovingFactor,max_eq_right ht]

theorem Potential.actual_virtual_scaled_derivative
    {M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (ref : ℝ) {a b : ℝ}
    (ha : M.data.rmin ≤ M.xs*a) (hb : M.xs*b ≤ 1) :
    ∀ᵐ t,t∈Icc a b→HasDerivAt (p.actualVirtualScaledPotential ref)
      (M.actualVirtualScaledFactor ref t*M.actualVirtualScaledGradient t) t := by
  apply comparison_virtual_scaled_potential_derivative M.hxs (M.actual_controlFactor_pos ref)
    p.H M.controlFactor
    (radiusComparisonGradient M.data.g M.alpha.val.val
      (orderedPathS n M.bf M.hf) (orderedPathB n M.bf M.hf))
  filter_upwards [p.hD] with r hr hri
  exact hr ⟨ha.trans hri.1,hri.2.trans hb⟩

theorem Potential.actual_virtual_scaled_primitive
    {M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (ref : ℝ) {s t : ℝ}
    (hs : M.data.rmin ≤ M.xs*s) (hst : s ≤ t) (ht : M.xs*t ≤ 1) :
    p.actualVirtualScaledPotential ref t-p.actualVirtualScaledPotential ref s =
      ∫r in s..t,M.actualVirtualScaledFactor ref r*M.actualVirtualScaledGradient r := by
  let G := radiusComparisonGradient M.data.g M.alpha.val.val
    (orderedPathS n M.bf M.hf) (orderedPathB n M.bf M.hf)
  have hstx : M.xs*s ≤ M.xs*t := mul_le_mul_of_nonneg_left hst M.hxs.le
  have hsub : Icc (M.xs*s) (M.xs*t) ⊆ Icc M.data.rmin 1 :=
    Icc_subset_Icc hs ht
  have hAC : AbsolutelyContinuousOnInterval p.H (M.xs*s) (M.xs*t) :=
    p.hH.mono (by simpa only [uIcc_of_le hstx,uIcc_of_le M.data.hr] using hsub)
  have hd : ∀ᵐ r,r∈Icc (M.xs*s) (M.xs*t)→
      HasDerivAt p.H (M.controlFactor r*G r) r := by
    filter_upwards [p.hD] with r hr hri
    exact hr (hsub hri)
  have hp := potential_integral_eq_sub hstx hAC hd
  have he : (∫r in s..t,M.actualVirtualScaledFactor ref r*M.actualVirtualScaledGradient r)=
      (∫r in s..t,M.controlFactor (M.xs*r)*G (M.xs*r))/
        (M.controlFactor ref*M.xs^3) := by
    rw [←intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [actualVirtualScaledFactor,actualVirtualScaledGradient,G]
    ring
  rw [he,intervalIntegral.integral_comp_mul_left (fun r=>M.controlFactor r*G r)
    M.hxs.ne',smul_eq_mul,hp]
  dsimp only [Potential.actualVirtualScaledPotential]
  field_simp

theorem Potential.actual_virtual_moving_primitive
    {M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (ref : ℝ) {s t : ℝ}
    (hs : M.data.rmin ≤ M.xs*s) (href : ref/M.xs ≤ s)
    (hst : s ≤ t) (ht : M.xs*t ≤ 1) :
    p.actualVirtualScaledPotential ref t-p.actualVirtualScaledPotential ref s =
      ∫r in s..t,M.actualVirtualMovingFactor ref r*M.actualVirtualScaledGradient r := by
  rw [p.actual_virtual_scaled_primitive ref hs hst ht]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hst] at hr
  dsimp only
  rw [M.actual_virtual_moving_factor_eq_scaled ref (href.trans hr.1)]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
