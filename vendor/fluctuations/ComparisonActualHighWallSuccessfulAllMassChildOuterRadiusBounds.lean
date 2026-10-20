module

public import ComparisonActualHighWallTwoScaleAllMassChildAgreement
public import ComparisonActualHighWallSuccessfulChildOuterRadiusBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 20000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem successful_all_mass_child_outer_radius_bounds
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→ActualShiftedAllMassParentChildCall (dim n+1) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀n,(a n).context=(M n).data.shiftedParentData)
    (hR : ∀n,(a n).R=(M n).data.wallRadius (M n).alpha)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).data.d ((M n).data.d^2) (x n))
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d ((M n).data.d^2) (x n)/(x n)^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n=>(M n).data.rmin/x n) atTop (𝓝 0)) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn in atTop,∀u∈Icc (C*x n) 1,
      u/(4*cu) ≤ (a n).Z u ∧ (a n).Z u ≤ 4*u/cl := by
  let C := max 1 (max (2*cu*Az) (cl*Az))
  have hC : 1 ≤ C := le_max_left _ _
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hClower : 2*cu*Az ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCupper : cl*Az ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have hcl1 : cl ≤ 1 := by
    have H := ((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).1
    simpa only [mul_one,(M 0).alpha.property.2.1] using H
  have Hagree := successful_all_mass_child_two_scale_agreement hm hdelta hcl hcu hAz hC0
    hc0 dim hdim M a x hxs hxlim hcontext hR hchild hweak hs hr
  have Hlower := Hagree C (1/2) 1 (1/(4*cu)) (1/4) hCp
    (by norm_num) (by norm_num) (by positivity) (by norm_num)
  have Hupper := Hagree C 1 2 (1/cl) (1/2) hCp zero_lt_one
    (by norm_num) (by positivity) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [Hlower,Hupper] with n hnlo hnup
  intro u hu
  have hup : 0 < u := (mul_pos hCp (hx n)).trans_le hu.1
  have huI : u∈Icc (0:ℝ) 1 := ⟨hup.le,hu.2⟩
  have houter : cu*Az*x n ≤ (1/2)*u := by
    have H := (mul_le_mul_of_nonneg_right hClower (hx n).le).trans hu.1
    nlinarith only [H]
  have HL := hnlo u hu.1 (by simpa only [mul_one] using hu.2)
  have hsizeL : ENNReal.ofReal ((1/4)*u) ≤ volume (Icc (u*(1/2)) (u*1)) := by
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [hup]
  obtain ⟨v,hv,Hv⟩ := exists_pointwise_agreement_of_disagreement_measure_lt
    ((M n).data.wallRadius (M n).alpha) (a n).Z (HL.trans_le hsizeL)
  have hvI : v∈Icc (0:ℝ) 1 :=
    ⟨(by positivity : 0 ≤ u*(1/2)).trans hv.1,by simpa only [mul_one] using hv.2.trans (by simpa only [mul_one] using hu.2)⟩
  have Hrad := (M n).inverse_radius_outer_band_lower_bound_of_parent_scale_high_wall hcu hAz hvI (hxs n)
    (by simpa only [mul_comm] using hv.1) houter
  have HvZu : (a n).Z v ≤ (a n).Z u := (a n).child_radius_monotone (by simpa only [mul_one] using hv.2)
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
    have hsizeU : ENNReal.ofReal ((1/2)*u) ≤ volume (Icc (u*1) (u*2)) := by
      rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      nlinarith only [hup]
    obtain ⟨v,hv,Hv⟩ := exists_pointwise_agreement_of_disagreement_measure_lt
      ((M n).data.wallRadius (M n).alpha) (a n).Z (HU.trans_le hsizeU)
    have hvI : v∈Icc (0:ℝ) 1 :=
      ⟨by have Hv0 : 0 ≤ u*1 := by simpa only [mul_one] using hup.le
          exact Hv0.trans hv.1, hv.2.trans Hsize⟩
    have HZu : (a n).Z u ≤ (a n).Z v := (a n).child_radius_monotone (by simpa only [mul_one] using hv.1)
    have Hr := (M n).inverse_radius_le_source_threshold_add_mass_high_wall hcl hAz hvI
    have Hx : Az*(M n).xs ≤ u/cl := by
      have H := (mul_le_mul_of_nonneg_right hCupper (hx n).le).trans hu.1
      apply (le_div_iff₀ hcl).mpr
      have Hxs := mul_le_mul_of_nonneg_left (hxs n) (mul_nonneg hcl.le hAz)
      nlinarith only [H,Hxs]
    have Hdiv : v/cl ≤ (u*2)/cl := div_le_div_of_nonneg_right hv.2 hcl.le
    have Herr := (abs_le.mp Hv).2
    have heq : u/cl+(u*2)/cl+(1/cl)*u=4*u/cl := by ring
    linarith only [HZu,Hr,Hx,Hdiv,Herr,heq]
  · have HZ := ((a n).child_radius_bounds u).2
    apply HZ.trans
    apply (le_div_iff₀ hcl).mpr
    nlinarith only [hcl1,not_le.mp huHalf]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
