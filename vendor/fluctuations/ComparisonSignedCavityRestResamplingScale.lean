module

public import ComparisonSignedCavityOriginalRestProductResampling
public import ComparisonSignedCavityRestAllHighResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 5000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem savedExteriorScale_antitone_mass {x W v w : ℝ}
    (hx : 0 ≤ x) (hW : 0 < W) (hv : 0 < v) (hvw : v ≤ w) :
    savedExteriorScale x W w ≤ savedExteriorScale x W v := by
  unfold savedExteriorScale
  apply div_le_div_of_nonneg_left (pow_nonneg hx 3)
    (Real.sqrt_pos.mpr (mul_pos (pow_pos hW 3) hv))
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvw (pow_nonneg hW.le 3))

theorem savedExteriorScale_pos {x W v : ℝ} (hx : 0 < x) (hW : 0 < W) (hv : 0 < v) :
    0 < savedExteriorScale x W v := by
  unfold savedExteriorScale
  exact div_pos (pow_pos hx 3) (Real.sqrt_pos.mpr (mul_pos (pow_pos hW 3) hv))

theorem rest_resampling_relative_factor {x scale C Cb r : ℝ}
    (hx : 0 < x) (hscale : x ≤ scale) (hC : 1 ≤ C) (hCb : 0 < Cb) (hr : 0 ≤ r) :
    r ≤ (Cb*r/x)*(C*scale)/Cb := by
  have hs : 0 ≤ scale:=hx.le.trans hscale
  have hxs : x ≤ C*scale:=hscale.trans (by nlinarith)
  have H:=mul_le_mul_of_nonneg_left hxs hr
  have H' : r ≤ r*(C*scale)/x := (le_div_iff₀ hx).mpr (by nlinarith)
  convert H' using 1
  field_simp

theorem rest_resampling_product_scale {a : ℕ} (C Cb r x W : ℝ) (initial : Finset (Fin a)) :
    (a:ℝ)*(Cb*r/x)*(∏e,C*sourceFactorScale x W initial e)=
      (a:ℝ)*Cb*r/x*(C^a*sourceMonomialScale x W initial) := by
  rw [Finset.prod_mul_distrib,source_factor_scale_product]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

end OAI.SKFluctuations.Cavity
