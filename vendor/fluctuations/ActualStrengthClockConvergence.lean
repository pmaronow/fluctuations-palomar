module

public import ConcreteComparisonStrength
public import BoundedMassProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal

theorem laplaceComparisonStrength_joint_tendsto
    {dseq lamseq rseq : ℕ → ℝ} {d lam r : ℝ}
    (hd : Tendsto dseq atTop (𝓝 d)) (hlam : Tendsto lamseq atTop (𝓝 lam))
    (hr : Tendsto rseq atTop (𝓝 r)) (hd0 : d ≠ 0) :
    Tendsto (fun n => laplaceComparisonStrength (dseq n) (lamseq n) (rseq n))
      atTop (𝓝 (laplaceComparisonStrength d lam r)) := by
  have harg := (hlam.mul hr).div (hd.pow 3) (pow_ne_zero 3 hd0)
  have hshape := laplaceComparisonShape_contDiff.continuous.tendsto (lam*r/d^3) |>.comp harg
  exact hlam.mul hshape

theorem bounded_unit_interval_l1_tendsto {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {C : ℝ}
    (hf : ∀ n, Measurable (f n)) (hF : Measurable F)
    (hbound : ∀ᶠ n in atTop, ∀ u : ℝ, |f n u-F u| ≤ C)
    (ht : ∀ u : ℝ, Tendsto (fun n => f n u) atTop (𝓝 (F u))) :
    Tendsto (fun n => ∫u in (0:ℝ)..1, |f n u-F u|) atTop (𝓝 0) := by
  have hh := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun n u => |f n u-F u|) (f := fun _ => (0:ℝ))
    (μ := volume) (a := (0:ℝ)) (b := 1) (fun _ => C)
    (Eventually.of_forall fun n => ((hf n).sub hF).abs.aestronglyMeasurable)
    (hbound.mono fun n hn => Eventually.of_forall fun u _ => by
      simpa only [Real.norm_eq_abs,abs_abs] using hn u)
    intervalIntegrable_const (Eventually.of_forall fun u _ => by
      simpa only [sub_self,abs_zero] using ((ht u).sub_const (F u)).abs)
  simpa only [intervalIntegral.integral_zero] using hh

theorem actual_strength_clock_convergences
    {dseq lamseq : ℕ → ℝ} {d lam : ℝ} (hd0 : d ≠ 0)
    (hd : Tendsto dseq atTop (𝓝 d)) (hlam : Tendsto lamseq atTop (𝓝 lam))
    (hlamn : ∀ n, 0 ≤ lamseq n) (hlam0 : 0 ≤ lam)
    {rseq : ℕ → boundedMassProfiles} {r : boundedMassProfiles}
    (hr : Tendsto rseq atTop (𝓝 r)) :
    let eseq := fun n u => laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u)
    let e := fun u => laplaceComparisonStrength d lam (r.val u)
    Tendsto (fun n => ∫u in (0:ℝ)..1, |eseq n u-e u|) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫u in (0:ℝ)..1, |eseq n u*(rseq n).val u-e u*r.val u|)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫u in (0:ℝ)..1, eseq n u*((rseq n).val u)^2) atTop
        (𝓝 (∫u in (0:ℝ)..1, e u*(r.val u)^2)) := by
  dsimp only
  let eseq := fun n u => laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u)
  let e := fun u => laplaceComparisonStrength d lam (r.val u)
  let C := |lam|+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hlC : lam ≤ C := by dsimp [C]; linarith [le_abs_self lam]
  have hlamC : ∀ᶠ n in atTop, lamseq n ≤ C :=
    (hlam.eventually (gt_mem_nhds (by dsimp [C]; linarith [le_abs_self lam]))).mono
      fun _ hn => hn.le
  have hrt (u : ℝ) : Tendsto (fun n => (rseq n).val u) atTop (𝓝 (r.val u)) :=
    tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hr) u
  have het (u : ℝ) : Tendsto (fun n => eseq n u) atTop (𝓝 (e u)) :=
    laplaceComparisonStrength_joint_tendsto hd hlam (hrt u) hd0
  have hem (n : ℕ) : Measurable (eseq n) :=
    (laplaceComparisonStrength_contDiff (dseq n) (lamseq n)).continuous.measurable.comp
      (rseq n).property.2.measurable
  have hEm : Measurable e :=
    (laplaceComparisonStrength_contDiff d lam).continuous.measurable.comp r.property.2.measurable
  have he0 (n : ℕ) (u : ℝ) : 0 ≤ eseq n u :=
    mul_nonneg (hlamn n) (laplaceComparisonShape_pos _).le
  have hel (n : ℕ) (u : ℝ) : eseq n u ≤ lamseq n :=
    laplaceComparisonStrength_le (dseq n) (hlamn n) _
  have hE0 (u : ℝ) : 0 ≤ e u := mul_nonneg hlam0 (laplaceComparisonShape_pos _).le
  have hEC (u : ℝ) : e u ≤ C := (laplaceComparisonStrength_le d hlam0 _).trans hlC
  have hraw : ∀ᶠ n in atTop, ∀ u : ℝ, |eseq n u-e u| ≤ 2*C := by
    filter_upwards [hlamC] with n hn u
    exact abs_le.mpr ⟨by linarith [he0 n u,hEC u], by linarith [hel n u,hE0 u]⟩
  have hfield : ∀ᶠ n in atTop, ∀ u : ℝ,
      |eseq n u*(rseq n).val u-e u*r.val u| ≤ 2*C := by
    filter_upwards [hlamC] with n hn u
    have hn0 := mul_nonneg (he0 n u) ((rseq n).property.1 u).1
    have hN := (mul_le_of_le_one_right (he0 n u) ((rseq n).property.1 u).2).trans
      ((hel n u).trans hn)
    have h00 := mul_nonneg (hE0 u) (r.property.1 u).1
    have hM := (mul_le_of_le_one_right (hE0 u) (r.property.1 u).2).trans (hEC u)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hpen : ∀ᶠ n in atTop, ∀ u : ℝ, ‖eseq n u*((rseq n).val u)^2‖ ≤ C := by
    filter_upwards [hlamC] with n hn u
    have hs : ((rseq n).val u)^2 ≤ 1 := by
      nlinarith [(rseq n).property.1 u |>.1,(rseq n).property.1 u |>.2]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (he0 n u) (sq_nonneg _))]
    exact (mul_le_of_le_one_right (he0 n u) hs).trans ((hel n u).trans hn)
  refine ⟨bounded_unit_interval_l1_tendsto hem hEm hraw het,
    bounded_unit_interval_l1_tendsto (fun n =>
      ((hem n).mul (rseq n).property.2.measurable)) (hEm.mul r.property.2.measurable) hfield
      (fun u => (het u).mul (hrt u)), ?_⟩
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun n u => eseq n u*((rseq n).val u)^2) (f := fun u => e u*(r.val u)^2)
    (μ := volume) (a := (0:ℝ)) (b := 1) (fun _ => C)
    (Eventually.of_forall fun n =>
      ((hem n).mul ((rseq n).property.2.measurable.pow_const 2)).aestronglyMeasurable)
    (hpen.mono fun n hn => Eventually.of_forall fun u _ => hn u)
    intervalIntegrable_const (Eventually.of_forall fun u _ => (het u).mul ((hrt u).pow 2))

end OAI.SKFluctuations.LaplaceWindowFormalization
