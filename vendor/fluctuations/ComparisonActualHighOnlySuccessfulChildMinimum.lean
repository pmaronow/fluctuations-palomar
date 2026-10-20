module

public import ComparisonActualHighOnlyOverlapMinimum
public import ComparisonActualShiftedParentChildCall
public import ComparisonNativeActualChildDirectCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false

namespace ActualHighOnlyComparisonData
variable {n : ℕ} {delta : ℝ}

theorem inverse_outer_regular_of_quantile_bounds
    (a : ActualHighOnlyComparisonData n delta) (alpha : a.Profile)
    {lo up cutoff : ℝ} (hlo : 0 < lo) (hlo1 : lo ≤ 1)
    (hloup : lo ≤ up) (hcutoff : a.s ≤ cutoff)
    (hq : ∀u∈Icc cutoff 1,u/up ≤ a.R alpha u ∧ a.R alpha u ≤ u/lo) :
    ∀r∈Icc (cutoff/lo) 1,lo*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ up*r := by
  have hup : 0 < up := hlo.trans_le hloup
  have hcut0 : 0 ≤ cutoff := a.hs.1.trans hcutoff
  intro r hr
  have hr0 : 0 ≤ r := (div_nonneg hcut0 hlo.le).trans hr.1
  have hlowcut : cutoff ≤ lo*r := by
    have H := (div_le_iff₀ hlo).mp hr.1
    simpa only [mul_comm] using H
  have hlow1 : lo*r ≤ 1 :=
    (mul_le_mul_of_nonneg_right hlo1 hr0).trans (by simpa using hr.2)
  have hlowspec := omittedSweepQuantile_spec zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha
    (show lo*r∈Icc a.s 1 from ⟨hcutoff.trans hlowcut,hlow1⟩)
  have hlowrad : a.R alpha (lo*r) ≤ r := by
    simpa only [mul_div_cancel_left₀ _ hlo.ne'] using (hq (lo*r) ⟨hlowcut,hlow1⟩).2
  have hlow := alpha.val.property.2 hlowrad
  rw [hlowspec] at hlow
  refine ⟨hlow,?_⟩
  by_cases hhigh1 : up*r ≤ 1
  · have hhighcut : cutoff ≤ up*r :=
      hlowcut.trans (mul_le_mul_of_nonneg_right hloup hr0)
    have hhighspec := omittedSweepQuantile_spec zero_le_one ⟨a.hs.1,a.hs1⟩
      a.hc a.hk a.hkc a.hm a.hM alpha
      (show up*r∈Icc a.s 1 from ⟨hcutoff.trans hhighcut,hhigh1⟩)
    have hhighrad : r ≤ a.R alpha (up*r) := by
      simpa only [mul_div_cancel_left₀ _ hup.ne'] using (hq (up*r) ⟨hhighcut,hhigh1⟩).1
    have hhigh := alpha.val.property.2 hhighrad
    rw [hhighspec] at hhigh
    exact hhigh
  · exact (alpha.val.property.1 r).2.trans (le_of_not_ge hhigh1)

def successfulChildMinimum
    (a : ActualHighOnlyComparisonData n delta)
    {m cl cu C0 c0 x C T Dchild : ℝ}
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hx : 0 < x)
    (hcl : 0 < cl) (hcu : 0 < cu) (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu) (hC : 1 ≤ C)
    (Q : ActualHighOnlyComparisonMinimum a (a.d^2)) (hd : a.d=c0*x)
    (hdD : a.d ≤ Dchild) (hupper : Real.sqrt (n:ℝ)*a.E ≤ a.d^2)
    (hlower : (n:ℝ)^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E)
    (htotal : ∀u∈Icc (0:ℝ) 1,a.h u+a.b u ≤ T)
    (hquantile : ∀u∈Icc (C*x) 1,u/(4*cu) ≤ a.R Q.alpha u ∧ a.R Q.alpha u ≤ 4*u/cl) :
    ActualHighOnlyOverlapMinimum n m delta (cl/4) (4*cu) (4*C/cl) C0 1 Dchild T := by
  have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr a.hN
  have Hroot : Real.sqrt (n:ℝ)*a.E ≤ (c0*x)^2 := by simpa only [hd] using hupper
  have Hstrength := actual_child_full_strength_at_parent_test_lower hc0 hc01 hx
  have hscale : comparisonLowerScale n a.E a.d ≤ x := by
    unfold comparisonLowerScale
    apply (div_le_iff₀ a.hd).mpr
    rw [hd]
    have Hc := mul_le_mul_of_nonneg_left hc01 (sq_nonneg x)
    nlinarith only [Hroot,Hc,hc0]
  have htest : (n:ℝ)*a.E^2 ≤ laplaceComparisonStrength a.d (a.d^2) x*x^2 := by
    have Hsq := pow_le_pow_left₀ (mul_nonneg hs.le a.hE.le) Hroot 2
    rw [mul_pow,Real.sq_sqrt a.hN.le] at Hsq
    have Hc : c0^4 ≤ c0^3 := by
      have H := mul_le_mul_of_nonneg_left hc01 (pow_nonneg hc0.le 3)
      nlinarith only [H]
    have Hs := mul_le_mul_of_nonneg_right Hstrength (sq_nonneg x)
    have Hc' := mul_le_mul_of_nonneg_right Hc (pow_nonneg hx.le 4)
    rw [hd]
    nlinarith only [Hsq,Hs,Hc']
  refine {
    data:=a,lam:=a.d^2,hlam:=sq_pos_of_pos a.hd,hld:=le_rfl,
    optimizer:=Q,xs:=x,z:=min ((4*C/cl)*x) 1,hxs:=hx,hscale:=hscale,
    hz:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩,
    hzxs:=min_le_left _ _,hdD:=hdD,hupper:=hupper,hlower:=hlower,
    htest:=by simpa only [one_mul] using htest,regular:=?_,clockBudget:=?_ }
  · intro r hr
    by_cases hz1 : (4*C/cl)*x ≤ 1
    · rw [min_eq_left hz1] at hr
      have hmasscut : C*x ≤ 1 := by
        have HE : (4*C/cl)*x=(4*C*x)/cl := by ring
        have Hdiv : (4*C*x)/cl ≤ (1:ℝ) := by
          rw [←HE]
          exact hz1
        have H : 4*C*x ≤ cl := by
          have HH := (div_le_iff₀ hcl).mp Hdiv
          linarith only [HH]
        linarith
      have hsCut : a.s ≤ C*x := by
        by_contra H
        have Hmono := omittedSweepQuantile_monotone zero_le_one ⟨a.hs.1,a.hs1⟩
          a.hc a.hk a.hkc a.hm a.hM Q.alpha (not_le.mp H).le
        have Hleft := omittedSweepQuantile_left zero_le_one ⟨a.hs.1,a.hs1⟩
          a.hc a.hk a.hkc a.hm a.hM Q.alpha
        have Hlow := (hquantile (C*x) ⟨le_rfl,hmasscut⟩).1
        have Hpos : 0 < C*x/(4*cu) := by positivity
        change a.R Q.alpha (C*x) ≤ a.R Q.alpha a.s at Hmono
        change a.R Q.alpha a.s=0 at Hleft
        linarith
      have H := a.inverse_outer_regular_of_quantile_bounds Q.alpha
        (show 0 < cl/4 by positivity) (show cl/4 ≤ 1 by linarith)
        (show cl/4 ≤ 4*cu by linarith) hsCut (fun u hu=>by
          have he : u/(cl/4)=4*u/cl := by field_simp
          simpa only [he] using hquantile u hu)
      have he : (C*x)/(cl/4)=(4*C/cl)*x := by field_simp
      rw [he] at H
      exact H r hr
    · rw [min_eq_right (le_of_not_ge hz1)] at hr
      have hr1 : r=1 := le_antisymm hr.2 hr.1
      subst r
      simpa only [Q.alpha.property.2,mul_one] using
        And.intro (show cl/4 ≤ 1 by linarith) (show 1 ≤ 4*cu by linarith)
  · have H := a.total_clock_le Q.alpha ⟨sq_nonneg a.d,le_rfl⟩ htotal (u:=1) (by norm_num)
    exact (sub_le_self _ (NNReal.coe_nonneg _)).trans (by
      linarith only [H,NNReal.coe_nonneg (a.bf Q.alpha (a.d^2) 1)])

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
