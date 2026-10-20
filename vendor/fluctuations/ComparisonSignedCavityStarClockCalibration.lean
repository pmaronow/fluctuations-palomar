module

public import ComparisonSignedCavitySusceptibilityBounds
public import ComparisonNativeCavityRadiusGoodPoint
public import ComparisonContactLinearMismatch
public import ActualMixedClockCDF

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 2500000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def starMean (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) : ℝ := orderedPathS n M.bf M.hf (M.alpha.val.val r)

theorem star_mixed_clock_compensation
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) (T : ℝ) :
    actualMixedClock n M.bf M.hf (M.alpha.val.val r)-T*M.starMean r =
      (M.b (M.alpha.val.val r)-T)*M.starMean r+
        M.h (M.alpha.val.val r)+
        laplaceComparisonStrength M.context.d M.lam r*(r-M.starMean r) := by
  have huri := M.alpha.val.property.1 r
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hb0 : 0 ≤ M.b (M.alpha.val.val r)-
      laplaceComparisonStrength M.context.d M.lam (M.R (M.alpha.val.val r)) :=
    had.2.2.1.trans (had.1 (by norm_num) huri huri.1)
  have hh0 : 0 ≤ M.h (M.alpha.val.val r)+
      laplaceComparisonStrength M.context.d M.lam (M.R (M.alpha.val.val r))*
        M.R (M.alpha.val.val r) :=
    had.2.2.2.trans (had.2.1 (by norm_num) huri huri.1)
  have hinv := comparisonSweepQuantile_inverse M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.alpha hr
  change M.R (M.alpha.val.val r)=r at hinv
  have hbc : (M.bf (M.alpha.val.val r):ℝ)=
      M.b (M.alpha.val.val r)-laplaceComparisonStrength M.context.d M.lam r := by
    change ((M.b (M.alpha.val.val r)-laplaceComparisonStrength M.context.d M.lam
      (M.R (M.alpha.val.val r))).toNNReal:ℝ)=_
    rw [Real.coe_toNNReal _ hb0,hinv]
  have hfc : (M.hf (M.alpha.val.val r):ℝ)=
      M.h (M.alpha.val.val r)+laplaceComparisonStrength M.context.d M.lam r*r := by
    change ((M.h (M.alpha.val.val r)+laplaceComparisonStrength M.context.d M.lam
      (M.R (M.alpha.val.val r))*M.R (M.alpha.val.val r)).toNNReal:ℝ)=_
    rw [Real.coe_toNNReal _ hh0,hinv]
  rw [actualMixedClock,hbc,hfc]
  dsimp only [starMean]
  ring

theorem star_mean_bounds_of_contact
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r W : ℝ} (hW : 0 < W) (hr : r ∈ Icc (0:ℝ) 1)
    (hband : W/2 ≤ r ∧ r ≤ W)
    (hcontact : radiusComparisonGradient (laplaceComparisonStrength M.context.d M.lam)
      M.alpha.val.val (orderedPathS (n+1) M.bf M.hf)
      (orderedPathB (n+1) M.bf M.hf) r = 0)
    (hdefect : M.cavityRadiusPointDefect r ≤ W^2/16) :
    W/4 ≤ M.starMean r ∧ M.starMean r ≤ W := by
  have hmom := comparisonVariableEndpoint_radius_moments M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM (n+1) (by omega)
    M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hp : 0 < r := by linarith [hband.1]
  have hmis := comparison_laplace_contact_linear_mismatch M.context.hd.ne' M.hlam
    hp (hmom.2.2 r hr).1.1 (hmom.2.2 r hr).2.1 hcontact
  have hSr := (comparison_gradient_nonneg_geometry hp
    (laplaceComparisonStrength_pos M.context.d M.hlam r)
    (by
      have H := laplaceComparisonStrength_logSlope_mem M.context.hd.ne' M.hlam.ne' r
      exact ⟨H.1,H.2.le⟩)
    (hmom.2.2 r hr).1.1 (hmom.2.2 r hr).2.1 hcontact.ge).1
  have hprod := (le_div_iff₀ hp).mp hmis
  change |M.starMean r-r| *r ≤ M.cavityRadiusPointDefect r at hprod
  have hleft : r-M.starMean r ≤ |M.starMean r-r| := by
    simpa only [neg_sub] using neg_le_abs (M.starMean r-r)
  have hmult := mul_le_mul_of_nonneg_right hleft hp.le
  constructor
  · by_contra H
    have hs : M.starMean r < W/4 := lt_of_not_ge H
    have hgap : W/4 < r-M.starMean r := by linarith [hband.1]
    have hlow := mul_le_mul_of_nonneg_left hband.1 (by linarith : 0 ≤ r-M.starMean r)
    nlinarith [hprod,hdefect]
  · exact hSr.trans hband.2

theorem star_mean_lower_of_squared_mismatch
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r W : ℝ} (hW : 0 < W) (hband : W/2 ≤ r)
    (hmis : (M.starMean r-r)^2 ≤ W^2/16) : W/4 ≤ M.starMean r := by
  by_contra H
  have hs : M.starMean r < W/4 := lt_of_not_ge H
  have hgap : M.starMean r-r < -(W/4) := by linarith
  nlinarith [sq_nonneg (M.starMean r-r+W/4)]

theorem star_mean_norm_bounds_of_squared_mismatch
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r W : ℝ} (hW : 0<W) (hband : W/2≤r ∧ r≤W)
    (hmis : (M.starMean r-r)^2≤W^2/16) :
    |M.starMean r|≤2*W ∧ |r-M.starMean r|≤W/4 := by
  have hbound : |M.starMean r-r|≤W/4 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤W/4)).mp
    rw [sq_abs]
    nlinarith [hmis]
  have hlow := M.star_mean_lower_of_squared_mismatch hW hband.1 hmis
  refine ⟨?_,by simpa only [abs_sub_comm] using hbound⟩
  rw [abs_of_nonneg (by linarith : 0≤M.starMean r)]
  linarith [(abs_le.mp hbound).2,hband.2]

theorem star_strength_le_two_sq
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r W : ℝ} (hW : 0 < W) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hband : W/2 ≤ r ∧ r ≤ W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2) :
    laplaceComparisonStrength M.context.d M.lam r ≤ 2*W^2 := by
  have hp : 0 < r := by linarith [hband.1]
  have hmono := laplaceComparisonStrength_monotonicities M.context.hd.ne' M.hlam
    (r₀:=0) le_rfl
  by_cases hxsr : M.xs ≤ r
  · have H := hmono.1 ⟨M.hxs.le,hxs.trans hW1⟩
      ⟨hp.le,hband.2.trans hW1⟩ hxsr
    linarith [hscale,sq_nonneg W]
  · have H := hmono.2 ⟨hp.le,hband.2.trans hW1⟩
      ⟨M.hxs.le,hxs.trans hW1⟩ (le_of_not_ge hxsr)
    have H2 := mul_le_mul hscale hxs M.hxs.le (sq_nonneg W)
    have he := (laplaceComparisonStrength_pos M.context.d M.hlam r).le
    have H3 := mul_le_mul_of_nonneg_left hband.1 he
    nlinarith

theorem star_bare_matrix_clock_lower
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r W T : ℝ} (hW : 0 < W) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hband : W/2 ≤ r ∧ r ≤ W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmall : 2*W^2 ≤ T/2) (hb : M.b (M.alpha.val.val r)=T) :
    T/2 ≤ (M.bf (M.alpha.val.val r) : ℝ) := by
  have hs := M.star_strength_le_two_sq hW hW1 hxs hband hscale
  have hr : r ∈ Icc (0:ℝ) 1 := ⟨by linarith [hband.1],hband.2.trans hW1⟩
  have hi := comparisonSweepQuantile_inverse M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hr
  change M.R (M.alpha.val.val r)=r at hi
  change T/2 ≤ ((M.b (M.alpha.val.val r)-
    laplaceComparisonStrength M.context.d M.lam (M.R (M.alpha.val.val r))).toNNReal:ℝ)
  rw [hi,hb]
  exact (by linarith : T/2 ≤ T-laplaceComparisonStrength M.context.d M.lam r).trans
    (Real.le_coe_toNNReal _)

theorem star_near_bare_matrix_clock_lower
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r W T Cb : ℝ} (hW : 0<W) (hW1 : W≤1)
    (hxs : M.xs≤W) (hband : W/2≤r ∧ r≤W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs≤W^2)
    (hsmall : (Cb+2)*W^2≤T/2)
    (hb : |M.b (M.alpha.val.val r)-T|≤Cb*W^2) :
    T/2≤(M.bf (M.alpha.val.val r):ℝ) := by
  have hs := M.star_strength_le_two_sq hW hW1 hxs hband hscale
  have hr : r∈Icc (0:ℝ) 1 := ⟨by linarith [hband.1],hband.2.trans hW1⟩
  have hi := comparisonSweepQuantile_inverse M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hr
  change M.R (M.alpha.val.val r)=r at hi
  change T/2≤((M.b (M.alpha.val.val r)-
    laplaceComparisonStrength M.context.d M.lam (M.R (M.alpha.val.val r))).toNNReal:ℝ)
  rw [hi]
  exact (by nlinarith [(abs_le.mp hb).1] :
    T/2≤M.b (M.alpha.val.val r)-laplaceComparisonStrength M.context.d M.lam r).trans
    (Real.le_coe_toNNReal _)

theorem star_near_bare_mixed_clock_lower
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r W T Cb : ℝ} (hW : 0<W) (hW1 : W≤1)
    (hxs : M.xs≤W) (hband : W/2≤r ∧ r≤W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs≤W^2)
    (hsmall : (Cb+2)*W^2≤T/2)
    (hb : |M.b (M.alpha.val.val r)-T|≤Cb*W^2)
    (hmis : (M.starMean r-r)^2≤W^2/16) :
    (T/8)*W≤actualMixedClock n M.bf M.hf (M.alpha.val.val r) := by
  have hm := M.star_mean_lower_of_squared_mismatch hW hband.1 hmis
  have hb' := M.star_near_bare_matrix_clock_lower hW hW1 hxs hband hscale hsmall hb
  have hh := (M.hf (M.alpha.val.val r)).coe_nonneg
  have H := mul_le_mul hb' hm (by positivity : 0≤W/4)
    (M.bf (M.alpha.val.val r)).coe_nonneg
  dsimp only [actualMixedClock,starMean] at *
  nlinarith

theorem star_near_bare_mixed_clock_cubic_error
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r W T Cb Ch : ℝ} (hW : 0<W) (hW1 : W≤1)
    (hCb : 0≤Cb) (_hCh : 0≤Ch) (hxs : M.xs≤W) (hband : W/2≤r ∧ r≤W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs≤W^2)
    (hb : |M.b (M.alpha.val.val r)-T|≤Cb*W^2)
    (hh : |M.h (M.alpha.val.val r)|≤Ch*W^3)
    (hmis : (M.starMean r-r)^2≤W^2/16) :
    |actualMixedClock n M.bf M.hf (M.alpha.val.val r)-T*M.starMean r|≤
      (2*Cb+Ch+1/2)*W^3 := by
  have hr : r∈Icc (0:ℝ) 1 := ⟨by linarith [hband.1],hband.2.trans hW1⟩
  rw [M.star_mixed_clock_compensation hr T]
  have hm := M.star_mean_norm_bounds_of_squared_mismatch hW hband hmis
  have hs := M.star_strength_le_two_sq hW hW1 hxs hband hscale
  have h1 : |(M.b (M.alpha.val.val r)-T)*M.starMean r|≤2*Cb*W^3 := by
    rw [abs_mul]
    have H := mul_le_mul hb hm.1 (abs_nonneg _) (by positivity : 0≤Cb*W^2)
    nlinarith only [H]
  have h2 : |laplaceComparisonStrength M.context.d M.lam r*(r-M.starMean r)|≤W^3/2 := by
    rw [abs_mul,abs_of_pos (laplaceComparisonStrength_pos M.context.d M.hlam r)]
    have H := mul_le_mul hs hm.2 (abs_nonneg _) (by positivity : 0≤2*W^2)
    nlinarith only [H]
  have H := (abs_add_le
    ((M.b (M.alpha.val.val r)-T)*M.starMean r+M.h (M.alpha.val.val r))
    (laplaceComparisonStrength M.context.d M.lam r*(r-M.starMean r))).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add h1 hh)) h2)
  nlinarith only [H]

theorem star_bare_mixed_clock_lower
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r W T : ℝ} (hW : 0 < W) (_hT : 0 < T) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hband : W/2 ≤ r ∧ r ≤ W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmall : 2*W^2 ≤ T/2) (hb : M.b (M.alpha.val.val r)=T)
    (hmis : (M.starMean r-r)^2 ≤ W^2/16) :
    (T/8)*W ≤ actualMixedClock n M.bf M.hf (M.alpha.val.val r) := by
  have hm := M.star_mean_lower_of_squared_mismatch hW hband.1 hmis
  have hb' := M.star_bare_matrix_clock_lower hW hW1 hxs hband hscale hsmall hb
  have hh := (M.hf (M.alpha.val.val r)).coe_nonneg
  have H := mul_le_mul hb' hm (by positivity : 0 ≤ W/4)
    (M.bf (M.alpha.val.val r)).coe_nonneg
  dsimp only [actualMixedClock,starMean] at *
  nlinarith

theorem star_bare_contact_clock_calibration
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r W T : ℝ} (hW : 0 < W) (hT : 0 < T) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hband : W/2 ≤ r ∧ r ≤ W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hb : M.b (M.alpha.val.val r)=T) (hh : M.h (M.alpha.val.val r)=0)
    (hcontact : radiusComparisonGradient (laplaceComparisonStrength M.context.d M.lam)
      M.alpha.val.val (orderedPathS (n+1) M.bf M.hf)
      (orderedPathB (n+1) M.bf M.hf) r = 0)
    (hdefect : M.cavityRadiusPointDefect r ≤ W^2/16) :
    W/4 ≤ M.starMean r ∧ M.starMean r ≤ W ∧
      (T/4)*W ≤ actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r) ∧
      |actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)-T*M.starMean r| ≤ W^3/4 := by
  have hr : r ∈ Icc (0:ℝ) 1 := ⟨by linarith [hband.1],hband.2.trans hW1⟩
  have hmean := M.star_mean_bounds_of_contact hW hr hband hcontact hdefect
  have hid := M.star_mixed_clock_compensation hr T
  simp only [hb,hh,sub_self,zero_mul,zero_add,add_zero] at hid
  have hp : 0 < r := by linarith [hband.1]
  have hmom := comparisonVariableEndpoint_radius_moments M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM (n+1) (by omega)
    M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hmis := comparison_laplace_contact_linear_mismatch M.context.hd.ne' M.hlam
    hp (hmom.2.2 r hr).1.1 (hmom.2.2 r hr).2.1 hcontact
  have hSr := (comparison_gradient_nonneg_geometry hp
    (laplaceComparisonStrength_pos M.context.d M.hlam r)
    (by
      have H := laplaceComparisonStrength_logSlope_mem M.context.hd.ne' M.hlam.ne' r
      exact ⟨H.1,H.2.le⟩)
    (hmom.2.2 r hr).1.1 (hmom.2.2 r hr).2.1 hcontact.ge).1
  change M.starMean r ≤ r at hSr
  have he := (laplaceComparisonStrength_pos M.context.d M.hlam r).le
  have hs := M.star_strength_le_two_sq hW hW1 hxs hband hscale
  have hdiff : 0 ≤ r-M.starMean r := sub_nonneg.mpr hSr
  have hKdiff : 0 ≤ actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)-T*M.starMean r := by
    rw [hid]
    exact mul_nonneg he hdiff
  refine ⟨hmean.1,hmean.2,?_,?_⟩
  · have H := mul_le_mul_of_nonneg_left hmean.1 hT.le
    nlinarith [hKdiff]
  · rw [abs_of_nonneg hKdiff,hid]
    have hpbound := (le_div_iff₀ hp).mp hmis
    change |M.starMean r-r| *r ≤ M.cavityRadiusPointDefect r at hpbound
    rw [abs_of_nonpos (sub_nonpos.mpr hSr)] at hpbound
    have h1 := mul_le_mul_of_nonneg_left hband.1 hdiff
    have h2 : r-M.starMean r ≤ W/8 := by
      apply (mul_le_mul_iff_right₀ hW).mp
      nlinarith [hpbound,hdefect]
    have H := mul_le_mul hs h2 hdiff (by positivity : 0 ≤ 2*W^2)
    nlinarith only [H]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
