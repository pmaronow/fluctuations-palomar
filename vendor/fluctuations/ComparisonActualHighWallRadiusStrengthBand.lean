module

public import ComparisonRadiusSizeRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology

theorem wall_radius_strength_antitone_nonnegative {d lam : ℝ}
    (hd : 0 < d) (hlam : 0 < lam) :
    AntitoneOn (laplaceComparisonStrength d lam) (Ici (0:ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0:ℝ))
    (laplaceComparisonStrength_contDiff d lam).continuous.continuousOn
  · intro r _
    exact ((laplaceComparisonStrength_contDiff d lam).differentiable (by norm_num) r).differentiableWithinAt
  · intro r hr
    have hrpos : 0 < r := by simpa only [interior_Ici,mem_Ioi] using hr
    have hg := laplaceComparisonStrength_pos d hlam r
    have hp := (laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1
    have hprod := mul_nonneg hp hg.le
    have heq : comparisonLogSlope (laplaceComparisonStrength d lam) r*
        laplaceComparisonStrength d lam r= -r*deriv (laplaceComparisonStrength d lam) r := by
      unfold comparisonLogSlope
      exact div_mul_cancel₀ _ hg.ne'
    rw [heq] at hprod
    nlinarith

theorem wall_radius_strength_band_scale {d lam xs W z C : ℝ}
    (hd : 0 < d) (hlam : 0 < lam) (hxs : 0 < xs)
    (hz : 0 < z) (hz1 : z≤1) (hxsW : xs≤W) (hC : 1≤C) (hzW : z≤C*W) :
    laplaceComparisonStrength d lam xs*xs^2≤C*laplaceComparisonStrength d lam z*W^2 := by
  have hg := (laplaceComparisonStrength_pos d hlam z).le
  by_cases hzs : z≤xs
  · have He := wall_radius_strength_antitone_nonnegative hd hlam hz.le hxs.le hzs
    have Hsq := (sq_le_sq₀ hxs.le (hxs.le.trans hxsW)).mpr hxsW
    have H := mul_le_mul He Hsq (sq_nonneg xs) hg
    have HC := mul_le_mul_of_nonneg_right hC (mul_nonneg hg (sq_nonneg W))
    exact H.trans (by simpa only [one_mul,mul_assoc] using HC)
  · have hsz : xs≤z := (lt_of_not_ge hzs).le
    have hmono := laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl
    have H := hmono.2 ⟨hxs.le,hsz.trans hz1⟩ ⟨hz.le,hz1⟩ hsz
    have H1 := mul_le_mul_of_nonneg_right H hxs.le
    have H2 := mul_le_mul_of_nonneg_left hzW hg
    have H3 := mul_le_mul H2 hxsW hxs.le (mul_nonneg hg (hz.le.trans hzW))
    calc
      _ = (laplaceComparisonStrength d lam xs*xs)*xs := by ring
      _ ≤ (laplaceComparisonStrength d lam z*z)*xs := H1
      _ ≤ (laplaceComparisonStrength d lam z*(C*W))*W := H3
      _ = _ := by ring

end OAI.SKFluctuations.LaplaceWindowFormalization
