module

public import SKProof.OriginalQAllMassTwoScale
public import ComparisonActualHighWallSuccessfulChildOuterRadiusBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem inverse_radius_outer_band_upper_bound_theta_zero_original_q
    {n : ℕ}
    (Q : ActualThetaZeroOverlapMinimum (n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hcu : 0 < cu) (_hAz : 0 ≤ Az)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (hfar : cu*Az*Q.xs ≤ u) :
    Q.sweepRadius u ≤ u/cl := by
  have Hmass : Q.alpha.val.val Q.z ≤ u := by
    have H0 := (Q.regular Q.z ⟨le_rfl,Q.hz.2⟩).2
    have H1 := mul_le_mul_of_nonneg_left Q.hzxs hcu.le
    nlinarith only [H0,H1,hfar]
  have HzR := Q.data.wallRadius_monotone Q.alpha Hmass
  rw [Q.data.wallRadius_inverse Q.alpha Q.hz] at HzR
  have Hreg := (Q.regular _
    ⟨HzR,(Q.data.wallRadius_bounds Q.alpha u).2⟩).1
  have Hs : Q.data.s ≤ u := by
    have H := Q.alpha.val.property.2 Q.hz.1
    rw [Q.alpha.property.1] at H
    exact H.trans Hmass
  rw [Q.data.wallRadius_spec Q.alpha ⟨Hs,hu.2⟩] at Hreg
  change cl*Q.sweepRadius u ≤ u at Hreg
  exact (le_div_iff₀ hcl).mpr (by simpa only [mul_comm] using Hreg)

theorem theta_zero_successful_all_mass_child_outer_radius_bounds_original_q
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl)
    (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    {c0 : ℝ} (hc0 : 0 < c0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (Q : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (a : (n:ℕ) → ActualShiftedAllMassParentChildCall
      (dim n+1) delta)
    (hxlim : Tendsto (fun n => (Q n).xs) atTop (𝓝 0))
    (hcontext : ∀n, (a n).context =
      (Q n).data.thetaZeroShiftedParentData
        (Q n).lam (Q n).hlam (Q n).hld)
    (hR : ∀n, (a n).R = (Q n).data.wallRadius (Q n).alpha)
    (hchild : ∀ᶠn in atTop,
      (a n).childRadius = c0*(Q n).xs ∧
      (a n).childLam = (c0*(Q n).xs)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (Q n).data.d (Q n).lam (Q n).xs)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (Q n).data.d (Q n).lam (Q n).xs/(Q n).xs^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n => (Q n).data.s/(Q n).xs)
      atTop (𝓝 0))
    (hr : Tendsto (fun n => (Q n).data.rmin/(Q n).xs)
      atTop (𝓝 0)) :
    ∃C:ℝ, 1 ≤ C ∧ ∀ᶠn in atTop,
      ∀u∈Icc (C*(Q n).xs) 1,
        u/(4*cu) ≤ (a n).Z u ∧ (a n).Z u ≤ 4*u/cl := by
  let C := max 1 (2*cu*Az)
  have hC : 1 ≤ C := le_max_left _ _
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hClower : 2*cu*Az ≤ C := le_max_right _ _
  have hx n : 0 < (Q n).xs := (Q n).hxs
  have hcl1 : cl ≤ 1 := by
    have H := ((Q 0).regular 1 ⟨(Q 0).hz.2,le_rfl⟩).1
    simpa only [mul_one,(Q 0).alpha.property.2.1] using H
  have Hagree := theta_zero_successful_all_mass_child_two_scale_agreement_original_q
    hm hdelta hcl hcu hAz hC0 hc0 dim hdim Q a
    (fun n => (Q n).xs) (fun _ => le_rfl) hxlim
    hcontext hR hchild hweak hs hr
  have Hlower := Hagree C (1/2) 1 (1/(4*cu)) (1/4)
    hCp (by norm_num) (by norm_num) (by positivity) (by norm_num)
  have Hupper := Hagree C 1 2 (1/cl) (1/2)
    hCp zero_lt_one (by norm_num) (by positivity) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [Hlower,Hupper] with n hnlo hnup
  intro u hu
  have hup : 0 < u := (mul_pos hCp (hx n)).trans_le hu.1
  have houter : cu*Az*(Q n).xs ≤ (1/2)*u := by
    have H := (mul_le_mul_of_nonneg_right hClower (hx n).le).trans hu.1
    nlinarith only [H]
  have HL := hnlo u hu.1 (by simpa only [mul_one] using hu.2)
  have hsizeL : ENNReal.ofReal ((1/4)*u) ≤
      volume (Icc (u*(1/2)) (u*1)) := by
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [hup]
  obtain ⟨v,hv,Hv⟩ := exists_pointwise_agreement_of_disagreement_measure_lt
    ((Q n).data.wallRadius (Q n).alpha) (a n).Z
    (HL.trans_le hsizeL)
  have hvI : v∈Icc (0:ℝ) 1 :=
    ⟨(by positivity : 0 ≤ u*(1/2)).trans hv.1,
      by simpa only [mul_one] using hv.2.trans (by simpa only [mul_one] using hu.2)⟩
  have Hrad := (Q n).inverse_radius_outer_band_lower_bound_of_parent_scale_theta_zero
    hcu hAz hvI le_rfl
    (by simpa only [mul_comm] using hv.1) houter
  change (1/2)*u/cu ≤ (Q n).data.wallRadius (Q n).alpha v at Hrad
  have HvZu : (a n).Z v ≤ (a n).Z u :=
    (a n).child_radius_monotone
      (by simpa only [mul_one] using hv.2)
  have HchildLower : u/(4*cu) ≤ (a n).Z u := by
    have Herr := (abs_le.mp Hv).1
    calc
      u/(4*cu) = (1/2)*u/cu-(1/(4*cu))*u := by field_simp; ring
      _ ≤ (a n).Z v := by linarith only [Hrad,Herr]
      _ ≤ (a n).Z u := HvZu
  refine ⟨HchildLower,?_⟩
  by_cases huHalf : u ≤ 1/2
  · have Hsize : u*2 ≤ 1 := by linarith
    have HU := hnup u hu.1 Hsize
    have hsizeU : ENNReal.ofReal ((1/2)*u) ≤
        volume (Icc (u*1) (u*2)) := by
      rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      nlinarith only [hup]
    obtain ⟨w,hw,Hw⟩ := exists_pointwise_agreement_of_disagreement_measure_lt
      ((Q n).data.wallRadius (Q n).alpha) (a n).Z
      (HU.trans_le hsizeU)
    have hwI : w∈Icc (0:ℝ) 1 :=
      ⟨by
         have Huw : u ≤ w := by simpa only [mul_one] using hw.1
         exact hup.le.trans Huw,
        hw.2.trans Hsize⟩
    have HZu : (a n).Z u ≤ (a n).Z w :=
      (a n).child_radius_monotone
        (by simpa only [mul_one] using hw.1)
    have Hfar : cu*Az*(Q n).xs ≤ w := by
      exact houter.trans ((by linarith only [hup] : (1/2)*u ≤ u).trans
        (by simpa only [mul_one] using hw.1))
    have Hrad := (Q n).inverse_radius_outer_band_upper_bound_theta_zero_original_q
      hcl hcu hAz hwI Hfar
    change (Q n).data.wallRadius (Q n).alpha w ≤ w/cl at Hrad
    have Hdiv : w/cl ≤ (u*2)/cl :=
      div_le_div_of_nonneg_right hw.2 hcl.le
    have Herr := (abs_le.mp Hw).2
    have heq : (u*2)/cl+(1/cl)*u ≤ 4*u/cl := by
      calc
        (u*2)/cl+(1/cl)*u = 3*(u/cl) := by ring
        _ ≤ 4*(u/cl) := mul_le_mul_of_nonneg_right (by norm_num) (div_pos hup hcl).le
        _ = 4*u/cl := by ring
    linarith only [HZu,Hrad,Hdiv,Herr,heq]
  · have HZ := ((a n).child_radius_bounds u).2
    apply HZ.trans
    apply (le_div_iff₀ hcl).mpr
    nlinarith only [hcl1,not_le.mp huHalf]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
