module

public import ComparisonActualHighWallPairedFarGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallOverlapMinimum
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

 theorem field_clock_cubic_of_low_source_mass
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Cmass : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hCm : 0 ≤ Cmass)
    (hwork : M.xs=M.data.d) {u : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (hmass : u ≤ Cmass*M.data.d) :
    (M.hf u:ℝ) ≤ (1/16+(Az+1/cl)*(1+Cmass))*M.data.d^3 := by
  let Clow:=(Az+1/cl)*(1+Cmass)
  have hClow : 0 ≤ Clow:=by dsimp only [Clow];positivity
  by_cases hlow : u < M.data.s
  · have H:=M.data.low_field_cubic M.alpha hu hlow
    have HH:=mul_nonneg hClow (pow_nonneg M.data.hd.le 3)
    dsimp only [Clow] at *
    nlinarith only [H,HH]
  · have HR:=M.inverse_radius_le_source_mass hcl hAz hu
    have Hmass : M.xs+u ≤ (1+Cmass)*M.data.d:=by rw [hwork];nlinarith only [hmass]
    have HRd : M.data.wallRadius M.alpha u ≤ Clow*M.data.d:=by
      exact HR.trans ((mul_le_mul_of_nonneg_left Hmass (by positivity : 0 ≤ Az+1/cl)).trans_eq (by dsimp only [Clow];ring))
    rw [M.data.high_field_clock M.alpha ⟨le_of_not_gt hlow,hu.2⟩]
    have Hg : M.data.g (M.data.wallRadius M.alpha u) ≤ M.data.d^2:=
      laplaceComparisonStrength_le M.data.d (sq_nonneg M.data.d) _
    have Hg0 : 0 ≤ M.data.g (M.data.wallRadius M.alpha u):=
      (laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) _).le
    have HR0 : 0 ≤ M.data.wallRadius M.alpha u:=
      M.data.hrbounds.1.le.trans (M.data.wallRadius_bounds M.alpha u).1
    have H:=mul_le_mul Hg HRd HR0 (sq_nonneg M.data.d)
    dsimp only [Clow] at H
    nlinarith only [H,pow_pos M.data.hd 3]

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallOverlapMinimum
