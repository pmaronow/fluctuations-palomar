module

public import ComparisonActualGeneralDefectBootstrap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter LaplaceWindowFormalization
open scoped Topology
set_option maxHeartbeats 12000000

 theorem scalar_defect_quadratic_of_original_joint_feedback
    {defect d c A q B Cfb J : ℝ}
    (hdefect : 0 ≤ defect) (hd : 0 < d) (hc : 0 < c) (hsmall : 2*A*q ≤ c)
    (Hfeedback : defect*(c*d) ≤ |J|+Cfb*d^3)
    (Hsource : |J| ≤ defect*A*q*d+B*d^3) :
    defect ≤ (2*(B+Cfb)/c)*d^2 := by
  have Hcombined : defect*(c*d) ≤ defect*A*q*d+(B+Cfb)*d^3:=by
    nlinarith only [Hfeedback,Hsource]
  exact scalar_defect_quadratic_of_cubic_feedback hdefect hd hc le_rfl hsmall Hcombined

 theorem eventually_scalar_defect_quadratic_of_original_joint_feedback_along
    {saving c : ℝ} (hsaving : 0 < saving) (hc : 0 < c) (A B Cfb : ℝ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∀ᶠn : ℕ in atTop,∀defect d J : ℝ,0 ≤ defect → 0 < d →
      defect*(c*d) ≤ |J|+Cfb*d^3 →
      |J| ≤ defect*A*((dim n+1:ℕ):ℝ)^(-saving)*d+B*d^3 →
      defect ≤ (2*(B+Cfb)/c)*d^2 := by
  have Hsmall:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=2*A) (d:=c) (q:=-saving) (r:=0) hc (by linarith))
  filter_upwards [Hsmall] with n hn
  intro defect d J hdefect hd Hfeedback Hsource
  exact scalar_defect_quadratic_of_original_joint_feedback hdefect hd hc
    (by simpa only [Function.comp_apply,Real.rpow_zero,mul_one,mul_assoc] using hn) Hfeedback Hsource

end OAI.SKFluctuations.Cavity
