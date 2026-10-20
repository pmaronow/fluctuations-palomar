module

public import ComparisonActualShiftedAllMassMacroscopicChildAgreement
public import ComparisonActualHighWallShiftedParentData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 6000000

private theorem macro_good_point_of_small_disagreement
    (R Z : ℝ→ℝ) {left right eps : ℝ}
    (H : volume (physicalPropagationDisagreementMassSet R Z left right eps)<volume (Icc left right)) :
    ∃u∈Icc left right,|Z u-R u|≤eps := by
  classical
  by_contra Hnone
  push Not at Hnone
  have Hsub : Icc left right ⊆ physicalPropagationDisagreementMassSet R Z left right eps :=
    fun u hu=>⟨hu,Hnone u hu⟩
  exact not_lt_of_ge (measure_mono Hsub) H

namespace ActualHighWallOverlapMinimum

theorem macro_inverse_profile_strict_band_of_fixed_allmass_child_agreement_high_wall
    {m delta cl cu Az C0 Ct D Bclock cR CR x : ℝ}
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n) m delta cl cu Az C0 Ct D Bclock)
    (a : (n:ℕ)→ActualShiftedAllMassParentChildCall (dim n) delta)
    (hcR : 0 < cR) (hCR : 1 ≤ CR) (r : ℝ→ℝ)
    (hZ : ∀u∈Ioo (0:ℝ) 1,Tendsto (fun n=>(a n).Z u) atTop (𝓝 (r u)))
    (hband : ∀u∈Ioo (0:ℝ) 1,cR*u ≤ r u ∧ r u ≤ CR*u)
    (hx : x∈Ioc (0:ℝ) 1) (hxs : ∀n,(M n).xs≤1)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 x))
    (hxsorigin : ∀ᶠn in atTop,(M n).data.rmin ≤ (M n).xs)
    (hs : Tendsto (fun n=>(M n).data.s) atTop (𝓝 0))
    (hagree : ∀left right eps theta : ℝ,0 < left → left < right → right≤1 →
      0 < eps → 0 < theta → ∀ᶠn in atTop,
      volume (physicalPropagationDisagreementMassSet ((M n).data.wallRadius (M n).alpha) (a n).Z left right eps)<ENNReal.ofReal theta) :
    ∀ᶠn in atTop,(1/(16*CR))*(M n).xs < (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs < (16/cR)*(M n).xs := by
  have hxpos : 0 < x := hx.1
  have hxone : x≤1 := hx.2
  have hCRp : 0 < CR := zero_lt_one.trans_le hCR
  let v := x/(8*CR)
  have hv : 0 < v := div_pos hxpos (by positivity)
  have hv2 : 2*v∈Ioo (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    have heq : 2*v=x/(4*CR) := by dsimp [v];field_simp;norm_num
    rw [heq]
    apply (div_lt_one (by positivity : 0 < 4*CR)).mpr
    linarith
  have hrv : r (2*v) < x/3 := by
    have h := (hband (2*v) hv2).2
    have heq : CR*(2*v)=x/4 := by dsimp [v];field_simp;norm_num
    rw [heq] at h
    linarith
  have HZv := (hZ (2*v) hv2).eventually (gt_mem_nhds hrv)
  have Hagreev := hagree v (2*v) (x/16) (v/2) hv (by linarith) hv2.2.le (by positivity) (by positivity)
  have Hxl := hxlim.eventually (lt_mem_nhds (by linarith : x/2 < x))
  have Hxu := hxlim.eventually (gt_mem_nhds (by linarith : x < 2*x))
  have Hlower : ∀ᶠn in atTop,(1/(16*CR))*(M n).xs < (M n).alpha.val.val (M n).xs := by
    filter_upwards [HZv,Hagreev,Hxl,Hxu,hxsorigin,hs.eventually (gt_mem_nhds hv)] with n hZn hAn hln hun horigin hsn
    have hmass : volume (physicalPropagationDisagreementMassSet ((M n).data.wallRadius (M n).alpha) (a n).Z v (2*v) (x/16))<volume (Icc v (2*v)) := by
      rw [Real.volume_Icc,show 2*v-v=v by ring]
      exact hAn.trans ((ENNReal.ofReal_lt_ofReal_iff hv).mpr (by linarith))
    obtain ⟨u,hu,hgood⟩ := macro_good_point_of_small_disagreement ((M n).data.wallRadius (M n).alpha) (a n).Z hmass
    have hRp := (M n).data.wallRadius_monotone (M n).alpha hu.1
    have hZp := (a n).child_radius_monotone hu.2
    have hRbelow : ((M n).data.wallRadius (M n).alpha) v < (M n).xs := by
      have habs := (abs_le.mp hgood).1
      linarith
    have hv1 : v≤1 := (show v≤2*v by linarith).trans hv2.2.le
    have hm : v ≤ (M n).alpha.val.val (M n).xs := by
      have H := (inverseConstraint_strictMonoOn (M n).data.hc (M n).data.hk (M n).data.hkc
        (M n).alpha.property).monotoneOn
        (omittedSweepQuantile_bounds (M n).data.hr ⟨(M n).data.hs.1.le,(M n).data.hs1⟩
          (M n).data.hc (M n).data.hk (M n).data.hkc (M n).data.hm (M n).data.hM (M n).alpha v)
        ⟨horigin,hxs n⟩ hRbelow.le
      rw [omittedSweepQuantile_spec (M n).data.hr ⟨(M n).data.hs.1.le,(M n).data.hs1⟩
        (M n).data.hc (M n).data.hk (M n).data.hkc (M n).data.hm (M n).data.hM (M n).alpha ⟨hsn.le,hv1⟩] at H
      exact H
    have hstrict : (1/(16*CR))*(M n).xs < v := by
      rw [div_mul_eq_mul_div,one_mul]
      apply (div_lt_iff₀ (by positivity : 0 < 16*CR)).mpr
      have heq : v*(16*CR)=2*x := by dsimp [v];field_simp;norm_num
      rw [heq]
      exact hun
    exact hstrict.trans_le hm
  by_cases hxlarge : cR/8≤x
  · filter_upwards [Hlower,Hxl] with n hn hln
    refine ⟨hn,?_⟩
    have hunit := ((M n).alpha.val.property.1 (M n).xs).2
    have hgt : (1:ℝ)<(16/cR)*(M n).xs := by
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hcR).mpr
      nlinarith
    exact hunit.trans_lt hgt
  · let w := 8*x/cR
    have hw : w∈Ioo (0:ℝ) 1 := by
      refine ⟨div_pos (by positivity) hcR,?_⟩
      apply (div_lt_one hcR).mpr
      have hh := lt_of_not_ge hxlarge
      linarith
    have hw2 : w/2∈Ioo (0:ℝ) 1 := ⟨half_pos hw.1,by linarith [hw.2]⟩
    have hrw : 3*x < r (w/2) := by
      have h := (hband (w/2) hw2).1
      have heq : cR*(w/2)=4*x := by dsimp [w];field_simp;norm_num
      rw [heq] at h
      linarith
    have HZw := (hZ (w/2) hw2).eventually (lt_mem_nhds hrw)
    have Hagreew := hagree (w/2) w (x/4) (w/4) hw2.1 (by linarith [hw.1]) hw.2.le
      (by positivity) (by positivity)
    filter_upwards [Hlower,HZw,Hagreew,Hxl,Hxu,hxsorigin,hs.eventually (gt_mem_nhds hw.1)] with n hn hZn hAn hln hun horigin hsn
    refine ⟨hn,?_⟩
    have hmass : volume (physicalPropagationDisagreementMassSet ((M n).data.wallRadius (M n).alpha) (a n).Z (w/2) w (x/4))<volume (Icc (w/2) w) := by
      rw [Real.volume_Icc,show w-w/2=w/2 by ring]
      exact hAn.trans ((ENNReal.ofReal_lt_ofReal_iff hw2.1).mpr (by linarith [hw.1]))
    obtain ⟨u,hu,hgood⟩ := macro_good_point_of_small_disagreement ((M n).data.wallRadius (M n).alpha) (a n).Z hmass
    have hRp := (M n).data.wallRadius_monotone (M n).alpha hu.2
    have hZp := (a n).child_radius_monotone hu.1
    have hRabove : (M n).xs < ((M n).data.wallRadius (M n).alpha) w := by
      have habs := (abs_le.mp hgood).2
      linarith
    have hm : (M n).alpha.val.val (M n).xs ≤ w := by
      have H := (inverseConstraint_strictMonoOn (M n).data.hc (M n).data.hk (M n).data.hkc
        (M n).alpha.property).monotoneOn ⟨horigin,hxs n⟩
        (omittedSweepQuantile_bounds (M n).data.hr ⟨(M n).data.hs.1.le,(M n).data.hs1⟩
          (M n).data.hc (M n).data.hk (M n).data.hkc (M n).data.hm (M n).data.hM (M n).alpha w)
        hRabove.le
      rw [omittedSweepQuantile_spec (M n).data.hr ⟨(M n).data.hs.1.le,(M n).data.hs1⟩
        (M n).data.hc (M n).data.hk (M n).data.hkc (M n).data.hm (M n).data.hM (M n).alpha ⟨hsn.le,hw.2.le⟩] at H
      exact H
    have hwstrict : w<(16/cR)*(M n).xs := by
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hcR).mpr
      have heq : w*cR=8*x := by dsimp [w];field_simp
      rw [heq]
      nlinarith
    exact hm.trans_lt hwstrict

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
