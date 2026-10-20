module

public import ComparisonSignedCavityActualDyadicCutCountAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter LaplaceWindowFormalization
open scoped Topology
set_option maxHeartbeats 12000000

theorem scalar_defect_quadratic_of_cubic_feedback
    {D K d cK A q B : ℝ} (hD : 0≤D) (hd : 0<d) (hcK : 0<cK)
    (hK : cK*d≤K) (hsmall : 2*A*q≤cK)
    (Hsource : D*K≤D*A*q*d+B*d^3) :
    D≤(2*B/cK)*d^2 := by
  have Hlow:=mul_le_mul_of_nonneg_left hK hD
  have Hsave:=mul_le_mul_of_nonneg_right hsmall (mul_nonneg hD hd.le)
  have HH : (cK/2*d)*D≤B*d^3:=by nlinarith only [Hsource,Hlow,Hsave]
  have Hpos : 0<cK/2*d:=by positivity
  have Hdiv : D≤B*d^3/(cK/2*d):=(le_div_iff₀ Hpos).mpr (by nlinarith only [HH])
  convert Hdiv using 1
  field_simp

theorem eventually_scalar_defect_quadratic_of_cubic_feedback
    {saving cK : ℝ} (hsaving : 0<saving) (hcK : 0<cK) (A B : ℝ) :
    ∀ᶠn : ℕ in atTop,∀D K d : ℝ,0≤D → 0<d → cK*d≤K →
      D*K≤D*A*(n:ℝ)^(-saving)*d+B*d^3 → D≤(2*B/cK)*d^2 := by
  have H:=eventually_coefficient_rpow_le (c:=2*A) (d:=cK) (q:=-saving) (r:=0)
    hcK (by linarith)
  filter_upwards [H] with n hn
  intro D K d hD hd hK Hsource
  apply scalar_defect_quadratic_of_cubic_feedback hD hd hcK hK _ Hsource
  simpa only [Real.rpow_zero,mul_one,mul_assoc] using hn

theorem eventually_scalar_defect_quadratic_of_cubic_feedback_along
    {saving cK : ℝ} (hsaving : 0<saving) (hcK : 0<cK) (A B : ℝ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∀ᶠn : ℕ in atTop,∀D K d : ℝ,0≤D → 0<d → cK*d≤K →
      D*K≤D*A*(dim n:ℝ)^(-saving)*d+B*d^3 → D≤(2*B/cK)*d^2 :=
  hdim.eventually (eventually_scalar_defect_quadratic_of_cubic_feedback hsaving hcK A B)

end OAI.SKFluctuations.Cavity
