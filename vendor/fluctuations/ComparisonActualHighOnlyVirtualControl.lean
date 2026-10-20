module

public import ComparisonActualHighOnlyAllCapMismatch
public import ComparisonActualHighOnlyClocks
public import ComparisonVirtualShiftedControlFactor

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_control_factor_pos
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (r : ℝ) :
    0<M.controlFactor r:=inverseControlFactor_pos _ _ _

def actualVirtualScaledFactor
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (ref t : ℝ) : ℝ :=
  M.controlFactor (M.xs*t)/M.controlFactor ref

def actualVirtualMovingFactor
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (ref t : ℝ) : ℝ :=
  M.actualVirtualScaledFactor ref (max (ref/M.xs) t)

def actualVirtualScaledGradient
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (t : ℝ) : ℝ :=
  radiusComparisonGradient (laplaceComparisonStrength M.context.d M.lam)
    M.alpha.val.val (orderedPathS n M.bf M.hf) (orderedPathB n M.bf M.hf) (M.xs*t)/M.xs^3

def Potential.actualVirtualScaledPotential
    {M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (ref t : ℝ) : ℝ :=
  p.H (M.xs*t)/(M.xs^4*M.controlFactor ref)

theorem actual_controlFactor_continuous
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : Continuous M.controlFactor := by
  let A := comparisonVirtualControlDensity M.context.N delta M.context.U M.context.L
    M.context.E M.context.d M.alpha.val.val M.context.k
  have hAm : Measurable A :=
    (inverseControlWeight_measurable M.alpha.val.property.2.measurable
      (comparisonFloor_measurable M.context.N delta M.context.U)
      (comparisonCap_continuous M.context.N delta M.context.U M.context.L M.context.E M.context.d).measurable).mul
      ((comparisonCapSlope_continuous M.context.N delta M.context.U M.context.L
        M.context.E M.context.d).measurable.comp M.alpha.val.property.2.measurable)
  have hAbound r : |A r| ≤ comparisonCapSlope M.context.N delta M.context.U M.context.L
      M.context.E M.context.d 1 := by
    have hw := inverseControlWeight_mem M.alpha.val.val M.context.k M.context.M r
    have hb := comparisonCapSlope_bound (δ:=delta) M.context.hN M.context.hU.le
      M.context.hL M.context.hE M.context.hd.le (M.alpha.val.property.1 r)
    dsimp only [A,comparisonVirtualControlDensity]
    rw [abs_mul,abs_of_nonneg hw.1]
    exact (mul_le_mul_of_nonneg_right hw.2 (abs_nonneg _)).trans (by simpa only [one_mul] using hb)
  have hi : ∀a b,IntervalIntegrable A volume a b := by
    intro a b
    rcases le_total a b with hab|hba
    · exact bounded_measurable_intervalIntegrable hab hAm (Eventually.of_forall (fun r _=>hAbound r))
    · exact (bounded_measurable_intervalIntegrable hba hAm
        (Eventually.of_forall (fun r _=>hAbound r))).symm
  exact Real.continuous_exp.comp (intervalIntegral.continuous_primitive hi 0)

theorem actual_virtual_scaled_factor_data
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {a b ref c C : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : M.xs*b ≤ 1)
    (href : ref∈Icc (M.xs*a) (M.xs*b)) (hc : 0 < c) (hcC : c ≤ C)
    (hlower : c*M.xs ≤ M.alpha.val.val (M.xs*a))
    (hupper : M.alpha.val.val (M.xs*b) ≤ C*M.xs) :
    Continuous (M.actualVirtualScaledFactor ref) ∧
    MonotoneOn (M.actualVirtualScaledFactor ref) (Icc a b) ∧
    ∀t∈Icc a b,M.actualVirtualScaledFactor ref t∈Icc (1/(C/c)^2) ((C/c)^2) := by
  have hK : 1 ≤ C/c := (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hcC)
  have hK0 : 0 ≤ C/c := zero_le_one.trans hK
  have hband : M.alpha.val.val (M.xs*b)+M.context.U ≤
      (C/c)*(M.alpha.val.val (M.xs*a)+M.context.U) := by
    calc
      _ ≤ C*M.xs+M.context.U := add_le_add hupper le_rfl
      _ = (C/c)*(c*M.xs)+M.context.U := by field_simp
      _ ≤ (C/c)*M.alpha.val.val (M.xs*a)+(C/c)*M.context.U :=
        add_le_add (mul_le_mul_of_nonneg_left hlower hK0)
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK M.context.hU.le)
      _ = _ := by ring
  obtain ⟨_hi,hmono,hbound⟩ := comparison_virtual_shifted_native_factor_data
    M.context.hN M.context.hU M.context.hL M.context.hE M.context.hd.le
    zero_le_one M.context.hc M.context.hk M.context.hkc
    (comparisonFloor_measurable M.context.N delta M.context.U) M.alpha
    (mul_nonneg M.hxs.le ha) hb (mul_le_mul_of_nonneg_left hab M.hxs.le) href hK hband
  refine ⟨(M.actual_controlFactor_continuous.comp (continuous_const.mul continuous_id)).div_const _,?_,?_⟩
  · intro s hs t ht hst
    apply div_le_div_of_nonneg_right _ (M.actual_control_factor_pos ref).le
    exact hmono ⟨mul_nonneg M.hxs.le (ha.trans hs.1),
      (mul_le_mul_of_nonneg_left hs.2 M.hxs.le).trans hb⟩
      ⟨mul_nonneg M.hxs.le (ha.trans ht.1),
      (mul_le_mul_of_nonneg_left ht.2 M.hxs.le).trans hb⟩
      (mul_le_mul_of_nonneg_left hst M.hxs.le)
  · intro t ht
    exact hbound (M.xs*t) ⟨mul_le_mul_of_nonneg_left ht.1 M.hxs.le,
      mul_le_mul_of_nonneg_left ht.2 M.hxs.le⟩

theorem actual_virtual_moving_factor_eq_one
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ref : ℝ) {t : ℝ} (ht : t ≤ ref/M.xs) : M.actualVirtualMovingFactor ref t=1 := by
  have he : M.xs*(ref/M.xs)=ref := by field_simp [M.hxs.ne']
  simp only [actualVirtualMovingFactor,max_eq_left ht,actualVirtualScaledFactor,he,
    div_self (M.actual_control_factor_pos ref).ne']

theorem actual_virtual_moving_factor_eq_scaled
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ref : ℝ) {t : ℝ} (ht : ref/M.xs ≤ t) :
    M.actualVirtualMovingFactor ref t=M.actualVirtualScaledFactor ref t := by
  simp only [actualVirtualMovingFactor,max_eq_right ht]

theorem actual_virtual_moving_factor_data
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 ≤ cu) (hAz : 0 ≤ Az) {B ref c : ℝ} (hB : 0 ≤ B)
    (hc : 0 < c) (href : ref∈Icc (0:ℝ) (M.xs*B)) (hphysical : M.xs*B ≤ 1)
    (hmass : c*M.xs ≤ M.alpha.val.val ref) :
    let K := (c+cu*(B+Az)+1)/c
    1 ≤ K ∧ Continuous (M.actualVirtualMovingFactor ref) ∧
      MonotoneOn (M.actualVirtualMovingFactor ref) (Iic B) ∧
      ∀t≤B,M.actualVirtualMovingFactor ref t∈Icc (1/K^2) (K^2) := by
  let C := c+cu*(B+Az)+1
  have hcC : c ≤ C := by dsimp only [C];linarith [mul_nonneg hcu (add_nonneg hB hAz)]
  have ha : 0 ≤ ref/M.xs := div_nonneg href.1 M.hxs.le
  have haB : ref/M.xs ≤ B := (div_le_iff₀ M.hxs).mpr (by simpa only [mul_comm] using href.2)
  have he : M.xs*(ref/M.xs)=ref := by field_simp [M.hxs.ne']
  have hupper : M.alpha.val.val (M.xs*B) ≤ C*M.xs := by
    let z := max (M.xs*B) M.z
    have hz : z∈Icc M.z 1 := ⟨le_max_right _ _,max_le hphysical M.hz.2⟩
    have hsize : z ≤ (B+Az)*M.xs := by
      apply max_le
      · nlinarith only [mul_nonneg hAz M.hxs.le]
      · nlinarith only [M.hzxs,mul_nonneg hB M.hxs.le]
    have H := (M.alpha.val.property.2 (le_max_left (M.xs*B) M.z)).trans (M.regular z hz).2
    have H' := mul_le_mul_of_nonneg_left hsize hcu
    have HC : cu*(B+Az) ≤ C := by dsimp only [C];linarith
    exact H.trans (H'.trans (by nlinarith only [mul_le_mul_of_nonneg_right HC M.hxs.le]))
  have Hdata := M.actual_virtual_scaled_factor_data ha haB hphysical
    (by simpa only [he] using (show ref∈Icc ref (M.xs*B) from ⟨le_rfl,href.2⟩))
    hc hcC (by simpa only [he] using hmass) hupper
  have hmax t (ht : t ≤ B) : max (ref/M.xs) t∈Icc (ref/M.xs) B :=
    ⟨le_max_left _ _,max_le haB ht⟩
  refine ⟨(le_div_iff₀ hc).mpr (by simpa only [one_mul] using hcC),
    Hdata.1.comp (continuous_const.max continuous_id),?_,?_⟩
  · intro s hs t ht hst
    exact Hdata.2.1 (hmax s hs) (hmax t ht) (max_le_max_left _ hst)
  · intro t ht
    exact Hdata.2.2 _ (hmax t ht)

theorem Potential.actual_virtual_scaled_derivative
    {M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (ref : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : M.xs*b ≤ 1) :
    ∀ᵐ t,t∈Icc a b→HasDerivAt (p.actualVirtualScaledPotential ref)
      (M.actualVirtualScaledFactor ref t*M.actualVirtualScaledGradient t) t := by
  apply comparison_virtual_scaled_potential_derivative M.hxs (M.actual_control_factor_pos ref)
    p.H M.controlFactor
    (radiusComparisonGradient (laplaceComparisonStrength M.context.d M.lam)
      M.alpha.val.val (orderedPathS n M.bf M.hf) (orderedPathB n M.bf M.hf))
  filter_upwards [p.hD] with r hr hri
  exact hr ⟨(mul_nonneg M.hxs.le ha).trans hri.1,hri.2.trans hb⟩

theorem Potential.actual_virtual_scaled_primitive
    {M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (ref : ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : M.xs*t ≤ 1) :
    p.actualVirtualScaledPotential ref t-p.actualVirtualScaledPotential ref s =
      ∫r in s..t,M.actualVirtualScaledFactor ref r*M.actualVirtualScaledGradient r := by
  let G := radiusComparisonGradient (laplaceComparisonStrength M.context.d M.lam)
    M.alpha.val.val (orderedPathS n M.bf M.hf) (orderedPathB n M.bf M.hf)
  have hstx : M.xs*s ≤ M.xs*t := mul_le_mul_of_nonneg_left hst M.hxs.le
  have hsub : Icc (M.xs*s) (M.xs*t) ⊆ Icc (0:ℝ) 1 :=
    Icc_subset_Icc (mul_nonneg M.hxs.le hs) ht
  have hAC : AbsolutelyContinuousOnInterval p.H (M.xs*s) (M.xs*t) :=
    p.hH.mono (by simpa only [uIcc_of_le hstx,uIcc_of_le zero_le_one] using hsub)
  have hd : ∀ᵐ r,r∈Icc (M.xs*s) (M.xs*t)→HasDerivAt p.H (M.controlFactor r*G r) r := by
    filter_upwards [p.hD] with r hr hri
    exact hr (hsub hri)
  have hp := potential_integral_eq_sub hstx hAC hd
  have he : (∫r in s..t,M.actualVirtualScaledFactor ref r*M.actualVirtualScaledGradient r)=
      (∫r in s..t,M.controlFactor (M.xs*r)*G (M.xs*r))/(M.controlFactor ref*M.xs^3) := by
    rw [←intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [actualVirtualScaledFactor,actualVirtualScaledGradient,G]
    ring
  rw [he,intervalIntegral.integral_comp_mul_left (fun r=>M.controlFactor r*G r) M.hxs.ne',smul_eq_mul,hp]
  dsimp only [Potential.actualVirtualScaledPotential]
  field_simp

theorem Potential.actual_virtual_moving_primitive
    {M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (ref : ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (href : ref/M.xs ≤ s) (hst : s ≤ t) (ht : M.xs*t ≤ 1) :
    p.actualVirtualScaledPotential ref t-p.actualVirtualScaledPotential ref s =
      ∫r in s..t,M.actualVirtualMovingFactor ref r*M.actualVirtualScaledGradient r := by
  rw [p.actual_virtual_scaled_primitive ref hs hst ht]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hst] at hr
  dsimp only
  rw [M.actual_virtual_moving_factor_eq_scaled ref (href.trans hr.1)]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
