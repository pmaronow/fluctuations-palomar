module

public import GeneralClockCongruence
public import BoundedMassProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal

theorem macroBoundedProfiles_l1_tendsto {a : ℕ → boundedMassProfiles} {b : boundedMassProfiles}
    (ha : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun n => ∫u in (0:ℝ)..1, |(a n).val u-b.val u|) atTop (𝓝 0) := by
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun n u => |(a n).val u-b.val u|) (f := fun _ => (0:ℝ))
    (μ := volume) (a := (0:ℝ)) (b := 1) (fun _ => (1:ℝ))
    (Eventually.of_forall fun n =>
      ((a n).property.2.measurable.sub b.property.2.measurable).abs.aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun u _ => by
      rw [Real.norm_eq_abs,abs_abs]
      exact abs_le.mpr ⟨by linarith [(a n).property.1 u |>.1,b.property.1 u |>.2],
        by linarith [(a n).property.1 u |>.2,b.property.1 u |>.1]⟩)
    intervalIntegrable_const (Eventually.of_forall fun u _ => by
      have hu := tendsto_pi_nhds.mp (tendsto_subtype_rng.mp ha) u
      simpa only [sub_self,abs_zero] using (hu.sub_const (b.val u)).abs)
  simpa only [intervalIntegral.integral_zero] using ht

theorem macroScalarQuantileValue_l1 {b h q z : ℝ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W) (hh0 : 0 ≤ h 0)
    (hq : q ∈ unitMassQuantiles) (hz : z ∈ unitMassQuantiles) :
    |generalScalarQuantileValue b h q-generalScalarQuantileValue b h z| ≤
      W*(∫u in (0:ℝ)..1, |q u-z u|) :=
  mass_strength_objective_l1_comparison 1 (by norm_num) (fun _ => 0) h b q z hW
    (fun _ _ _ _ _ => le_rfl) hh hb hq.1 hz.1 hbb hq.2 hz.2 le_rfl hh0

theorem macroScalarQuantileValue_eq_of_eqOn {b h q z : ℝ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W) (hh0 : 0 ≤ h 0)
    (hq : q ∈ unitMassQuantiles) (hz : z ∈ unitMassQuantiles)
    (he : EqOn q z (Icc (0:ℝ) 1)) :
    generalScalarQuantileValue b h q=generalScalarQuantileValue b h z := by
  have hi : (∫u in (0:ℝ)..1, |q u-z u|)=0 := by
    calc
      _ = ∫u in (0:ℝ)..1, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        simp only [he (by simpa using hu),sub_self,abs_zero]
      _ = 0 := intervalIntegral.integral_zero
  have h := macroScalarQuantileValue_l1 hW hb hh hbb hh0 hq hz
  rw [hi,mul_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

theorem macroScalarQuantileValue_profile_tendsto {b h : ℝ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W) (hh0 : 0 ≤ h 0)
    {a : ℕ → boundedMassProfiles} {z : boundedMassProfiles}
    (ha : Tendsto a atTop (𝓝 z)) :
    Tendsto (fun n => generalScalarQuantileValue b h (a n).val) atTop
      (𝓝 (generalScalarQuantileValue b h z.val)) := by
  have hi : Tendsto (fun n => W*(∫u in (0:ℝ)..1, |(a n).val u-z.val u|)) atTop (𝓝 0) :=
    by simpa only [mul_zero] using (macroBoundedProfiles_l1_tendsto ha).const_mul W
  rw [← tendsto_sub_nhds_zero_iff]
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n =>
    macroScalarQuantileValue_l1 hW hb hh hbb hh0
      ⟨(a n).property.2.monotoneOn _,fun u _ => (a n).property.1 u⟩
      ⟨z.property.2.monotoneOn _,fun u _ => z.property.1 u⟩) hi

theorem macroScalarMinimum_attained (b h : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W) (hh0 : 0 ≤ h 0) :
    ∃ z : ℝ → ℝ, z ∈ unitMassQuantiles ∧
      generalScalarQuantileValue b h z=generalScalarMinimum b h := by
  classical
  let e : ℕ → ℝ := fun n => 1/(n+1:ℕ)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have het : Tendsto e atTop (𝓝 0) := SKCavity.tendsto_succ_reciprocal
  have hbelow := generalScalarQuantileValues_bddBelow b h hW hb hh hbb hh0
  have hnear (n : ℕ) : ∃ q ∈ unitMassQuantiles,
      generalScalarQuantileValue b h q < generalScalarMinimum b h+e n := by
    obtain ⟨v,hv,hvlt⟩ := (csInf_lt_iff hbelow (generalScalarQuantileValues_nonempty b h)).mp
      (show generalScalarMinimum b h < generalScalarMinimum b h+e n by linarith [he n])
    obtain ⟨q,hq,rfl⟩ := hv
    exact ⟨q,hq,hvlt⟩
  choose q hq hv using hnear
  let a : ℕ → boundedMassProfiles := fun n =>
    ⟨unitClockExtension (q n),
      ⟨fun u => hq n |>.2 _ (projIcc 0 1 (by norm_num) u).property,
        unitClockExtension_monotone _ (hq n).1⟩⟩
  have heq (n : ℕ) : generalScalarQuantileValue b h (a n).val=
      generalScalarQuantileValue b h (q n) :=
    macroScalarQuantileValue_eq_of_eqOn hW hb hh hbb hh0
      ⟨(a n).property.2.monotoneOn _,fun u _ => (a n).property.1 u⟩ (hq n)
      (unitClockExtension_eq_on _)
  have hav : Tendsto (fun n => generalScalarQuantileValue b h (a n).val) atTop
      (𝓝 (generalScalarMinimum b h)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    apply squeeze_zero (fun n => by
      rw [heq]
      exact sub_nonneg.mpr (generalScalarMinimum_le b h _ hW hb hh hbb hh0 (hq n)))
      (fun n => by rw [heq]; linarith [hv n]) het
  obtain ⟨z,φ,hφ,haz⟩ := boundedMassProfiles_tendsto_subseq a
  refine ⟨z.val,⟨z.property.2.monotoneOn _,fun u _ => z.property.1 u⟩,?_⟩
  exact tendsto_nhds_unique
    (macroScalarQuantileValue_profile_tendsto hW hb hh hbb hh0 haz)
    (hav.comp hφ.tendsto_atTop)

end OAI.SKFluctuations.LaplaceWindowFormalization
