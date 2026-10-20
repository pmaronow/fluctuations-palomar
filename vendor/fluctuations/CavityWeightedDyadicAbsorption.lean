module

public import CavityWeightedExteriorClock

@[expose] public section

noncomputable section
open scoped BigOperators
namespace OAI.SKFluctuations

theorem weighted_projected_dyadic_product_sq {x W v s : ℝ}
    (hW : 0 < W) (hv : 0 < v) (hs : 0 < s) :
    (v^2*savedProjectedScale x W v*savedWeightedExteriorScale x W v s/s)^2=
      x^12/(W^5*s) := by
  rw [div_pow,mul_pow,mul_pow,
    savedProjectedScale_sq,savedWeightedExteriorScale_sq hW hs.le]
  field_simp
  <;> ring

theorem weighted_projected_dyadic_product_le {x W v s : ℝ}
    (hx : 0 ≤ x) (hW : 0 < W) (hv : 0 < v) (hs : 0 < s)
    (hxW : x ≤ W) (hxs : x ≤ s) :
    v^2*savedProjectedScale x W v*savedWeightedExteriorScale x W v s/s ≤ W*x^2 := by
  have hp : x^8 ≤ W^7*s := by
    calc
      x^8=x^7*x := by ring
      _ ≤ W^7*s := mul_le_mul (pow_le_pow_left₀ hx hxW 7) hxs hx
        (pow_nonneg hW.le _)
  have hsq : (v^2*savedProjectedScale x W v*savedWeightedExteriorScale x W v s/s)^2 ≤
      (W*x^2)^2 := by
    rw [weighted_projected_dyadic_product_sq hW hv hs]
    apply (div_le_iff₀ (by positivity : 0 < W^5*s)).2
    calc
      x^12=x^4*x^8 := by ring
      _ ≤ x^4*(W^7*s) := mul_le_mul_of_nonneg_left hp (by positivity)
      _=(W*x^2)^2*(W^5*s) := by ring
  exact (sq_le_sq₀ (by
    unfold savedProjectedScale savedWeightedExteriorScale
    positivity) (by positivity)).mp hsq

theorem weighted_projected_initial_dyadic_product_le {x W v : ℝ}
    (hx : 0 < x) (hW : 0 < W) (hv : 0 < v) (hxW : x ≤ W) :
    v^2*savedProjectedScale x W v*savedWeightedExteriorScale x W v x/x ≤ W*x^2 :=
  weighted_projected_dyadic_product_le hx.le hW hv hx hxW le_rfl

theorem weighted_projected_positive_dyadic_product_le {x W v : ℝ}
    (hx : 0 ≤ x) (hW : 0 < W) (hv : 0 < v) (hxW : x ≤ W) :
    v^2*savedProjectedScale x W v*savedWeightedExteriorScale x W v W/W ≤ W*x^2 :=
  weighted_projected_dyadic_product_le hx hW hv hW hxW hxW

end OAI.SKFluctuations
