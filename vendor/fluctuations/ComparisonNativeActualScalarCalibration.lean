module

public import ComparisonNativeActualScalarProfile
public import ComparisonSignedCavityActualSlowWindowSequence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

def bareScalarCavityResidual {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0) (u : ℝ) : ℝ :=
  orderedPathS (n+1) M.bf M.hf u-
    scalarCovarianceResponse hT (M.bareScalarMassProfile hT hb hh)
      (actualMixedClock (n+1) M.bf M.hf u)

theorem bare_scalar_calibration_of_cavity_and_clock {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0)
    {u x c Cs Ck Cr : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hCk : 0 ≤ Ck)
    (hS : orderedPathS (n+1) M.bf M.hf u ≤ Cs*x)
    (hK : T*c*x ≤ actualMixedClock (n+1) M.bf M.hf u)
    (hclock : |actualMixedClock (n+1) M.bf M.hf u-
      T*orderedPathS (n+1) M.bf M.hf u| ≤ Ck*x^3)
    (hres : |M.bareScalarCavityResidual hT hb hh u| ≤ Cr*x^3) :
    let q := actualMixedClock (n+1) M.bf M.hf u/T
    c*x ≤ q ∧ q ≤ (Cs+Ck/T)*x ∧
      |scalarPlantedEnergy hT (M.bareScalarMassProfile hT hb hh) q-q| ≤
        (Cr+Ck/T)*x^3 := by
  dsimp only
  let S := orderedPathS (n+1) M.bf M.hf u
  let K := actualMixedClock (n+1) M.bf M.hf u
  have hcomp : |K/T-S| ≤ (Ck/T)*x^3 := by
    have he : K/T-S=(K-T*S)/T := by field_simp
    rw [he,abs_div,abs_of_pos hT]
    exact (div_le_div_of_nonneg_right hclock hT.le).trans_eq (by ring)
  have hx2 : x^2 ≤ 1 := by nlinarith only [hx, hx1, sq_nonneg (x-1)]
  have hx3 : x^3 ≤ x := by
    have H := mul_le_mul_of_nonneg_right hx2 hx.le
    nlinarith only [H]
  have hupper : K/T ≤ (Cs+Ck/T)*x := by
    have H := le_abs_self (K/T-S)
    have Hsmall := mul_le_mul_of_nonneg_left hx3 (div_nonneg hCk hT.le)
    change S ≤ Cs*x at hS
    linarith only [hS,H,Hsmall,hcomp]
  refine ⟨(le_div_iff₀ hT).mpr (by convert hK using 1; ring),hupper,?_⟩
  have H := abs_sub_le
    (scalarPlantedEnergy hT (M.bareScalarMassProfile hT hb hh) (K/T)) S (K/T)
  have hres' : |scalarPlantedEnergy hT (M.bareScalarMassProfile hT hb hh) (K/T)-S| ≤ Cr*x^3 := by
    change |S-scalarPlantedEnergy hT (M.bareScalarMassProfile hT hb hh) (K/T)| ≤ Cr*x^3 at hres
    rw [abs_sub_comm]
    exact hres
  have hcomp' : |S-K/T| ≤ (Ck/T)*x^3 := by
    rw [abs_sub_comm]
    exact hcomp
  exact (H.trans (add_le_add hres' hcomp')).trans_eq (by ring)

theorem bare_scalar_calibration_at_slow_star {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0)
    {W L Cs Cr : ℝ} (w : ActualSlowWindowChoice)
    (hW : 0 < W) (hW1 : W ≤ 1)
    (hw : IsActualCalibratedSlowWindow M W T L Cs w)
    (hres : |M.bareScalarCavityResidual hT hb hh w.star.val| ≤ Cr*W^3) :
    let c := starMassBandConstant cu Az/cu
    let q := actualMixedClock (n+1) M.bf M.hf w.star.val/T
    (3*c/8)*W ≤ q ∧ q ≤ (Cs+((c+1)/4)/T)*W ∧
      |scalarPlantedEnergy hT (M.bareScalarMassProfile hT hb hh) q-q| ≤
        (Cr+((c+1)/4)/T)*W^3 := by
  obtain ⟨p,_,_,_,_,_,_,_,_,_,_,hS,_,_,_,_,hK,hclock,_⟩ := hw
  have hc : 0 < starMassBandConstant cu Az/cu :=
    div_pos (star_mass_band_constant_pos hcu hAz) hcu
  apply M.bare_scalar_calibration_of_cavity_and_clock hT hb hh hW hW1
    (by positivity) hS _ hclock hres
  convert hK using 1
  ring

theorem actual_bare_scalar_hcal_of_slow_window_residual
    (hT : 0 < T) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {L Cs Cr : ℝ} (hCs : 0 < Cs) (hCr : 0 ≤ Cr)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hW0 : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n))
    (hres : ∀ᶠn in atTop,
      |(M n).bareScalarCavityResidual hT (hb n) (hh n) (w n).star.val| ≤ Cr*(W n)^3) :
    ∃c R0 B : ℝ,0 < c ∧ 0 < R0 ∧ 0 ≤ B ∧ ∀ᶠn in atTop,
      ∃q : ℝ,c*W n ≤ q ∧ q ≤ R0*W n ∧
        |scalarPlantedEnergy hT ((M n).bareScalarMassProfile hT (hb n) (hh n)) q-q| ≤ B*(W n)^3 := by
  let c := starMassBandConstant cu Az/cu
  have hc : 0 < c := div_pos (star_mass_band_constant_pos hcu hAz) hcu
  refine ⟨3*c/8,Cs+((c+1)/4)/T,Cr+((c+1)/4)/T,by positivity,by positivity,by positivity,?_⟩
  have HW1 := hW0.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hw,hres,HW1] with n hn hr hn1
  refine ⟨actualMixedClock (n+1) (M n).bf (M n).hf (w n).star.val/T,?_⟩
  exact (M n).bare_scalar_calibration_at_slow_star hT hcu hAz (hb n) (hh n) (w n)
    ((M n).hxs.trans_le (hxs n)) hn1 hn hr

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
