module

public import WallClockGeometry
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem wallPsi_band_gap {s v x y : ℝ} {n : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hn : 1 ≤ n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hx : 0 ≤ x) (hxy : x ≤ y) (hys : y < s)
    (hleft : s-v ≤ x) (hright : y ≤ s-(n : ℝ)^(-(10 : ℝ))) :
    (y-x)/(22*v*Real.log (n : ℝ)) ≤
      wallPsi s ((n : ℝ)^(-(10 : ℝ))) y-wallPsi s ((n : ℝ)^(-(10 : ℝ))) x := by
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one (Nat.one_le_cast.mpr hn)
  have hτ : 0 < (n : ℝ)^(-(10 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hv : 0 < v := by linarith
  have hlog : 0 < Real.log (n : ℝ) := by linarith
  have hcont : ContinuousOn (wallPsi s ((n : ℝ)^(-(10 : ℝ)))) (Icc x y) :=
    (wallPsi_continuousOn hs hτ).mono (Icc_subset_Icc hx hys.le)
  have hdiff : DifferentiableOn ℝ (wallPsi s ((n : ℝ)^(-(10 : ℝ)))) (interior (Icc x y)) := by
    intro z hz
    have hz' : z ∈ Icc x y := interior_subset hz
    exact (wallPsi_hasDerivAt hs hτ (hz'.2.trans hys.le)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ z ∈ interior (Icc x y), 1/(22*v*Real.log (n : ℝ)) ≤
      deriv (wallPsi s ((n : ℝ)^(-(10 : ℝ)))) z := by
    intro z hz
    have hz' : z ∈ Icc x y := interior_subset hz
    have hgap : (n : ℝ)^(-(10 : ℝ)) ≤ s-z := by linarith [hz'.2]
    have hgap0 : 0 < s-z := hτ.trans_le hgap
    have hupper : s-z ≤ v := by linarith [hz'.1]
    apply le_trans _ (wallPsi_deriv_lower_nat hs hs1 hn hlogn hgap)
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hupper hlog.le]
  have hh := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv hcont hdiff hderiv
    x ⟨le_rfl, hxy⟩ y ⟨hxy, le_rfl⟩ hxy
  convert hh using 1
  ring

theorem wallPsi_dyadic_band_gap {s v x y : ℝ} {n : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hn : 1 ≤ n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hvτ : 4*(n : ℝ)^(-(10 : ℝ)) ≤ v) (hvs : v ≤ s)
    (hx : x ∈ Icc (s-v) (s-v/4)) (hy : y ∈ Icc (s-v) (s-v/4)) (hxy : x ≤ y) :
    (y-x)/(22*v*Real.log (n : ℝ)) ≤
      wallPsi s ((n : ℝ)^(-(10 : ℝ))) y-wallPsi s ((n : ℝ)^(-(10 : ℝ))) x := by
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one (Nat.one_le_cast.mpr hn)
  have hτ : 0 < (n : ℝ)^(-(10 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hv : 0 < v := by linarith
  exact wallPsi_band_gap hs hs1 hn hlogn (by linarith [hx.1]) hxy
    (by linarith [hy.2]) hx.1 (by linarith [hy.2])

theorem wallPsi_dyadic_minus_gap {s v : ℝ} {n : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hn : 1 ≤ n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hvτ : 4*(n : ℝ)^(-(10 : ℝ)) ≤ v) (hvs : v ≤ s) :
    1/(44*Real.log (n : ℝ)) ≤
      wallPsi s ((n : ℝ)^(-(10 : ℝ))) (s-v/2)-wallPsi s ((n : ℝ)^(-(10 : ℝ))) (s-v) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one (Nat.one_le_cast.mpr hn)
  have hτ : 0 < (n : ℝ)^(-(10 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hv : 0 < v := by linarith
  have hh := wallPsi_dyadic_band_gap hs hs1 hn hlogn hvτ hvs
    (x := s-v) (y := s-v/2) ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  convert hh using 1
  field_simp [hv.ne']
  ring

theorem wallPsi_dyadic_plus_gap {s v : ℝ} {n : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hn : 1 ≤ n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hvτ : 4*(n : ℝ)^(-(10 : ℝ)) ≤ v) (hvs : v ≤ s) :
    1/(88*Real.log (n : ℝ)) ≤
      wallPsi s ((n : ℝ)^(-(10 : ℝ))) (s-v/4)-wallPsi s ((n : ℝ)^(-(10 : ℝ))) (s-v/2) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one (Nat.one_le_cast.mpr hn)
  have hτ : 0 < (n : ℝ)^(-(10 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hv : 0 < v := by linarith
  have hh := wallPsi_dyadic_band_gap hs hs1 hn hlogn hvτ hvs
    (x := s-v/2) (y := s-v/4) ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  convert hh using 1
  field_simp [hv.ne']
  ring

section
variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin ≤ 1) (hs1 : s ≤ 1) (hc : 0 < c)
variable (hk : ContinuousOn k (Icc rmin 1))
variable (hkc : ∀ t ∈ Icc rmin 1, c ≤ k t)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

theorem wallChangedField_band_gap {T ε θ d v x y : ℝ} {n : ℕ}
    (hs : 0 < s) (hn : 1 ≤ n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc (0 : ℝ) 1) (hrmin : 0 ≤ rmin)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hys : y < s)
    (hleft : s-v ≤ x) (hright : y ≤ s-(n : ℝ)^(-(10 : ℝ)))
    (α : inverseIntegralConstraints rmin s k M) :
    θ*wallLowStrength T ε*wallLowRadius d rmin ε*(y-x)/(22*v*Real.log (n : ℝ)) ≤
      wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α y-
      wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α x := by
  have hh := wallPsi_band_gap hs hs1 hn hlogn hx hxy hys hleft hright
  have hamp := (wall_low_amplitude_bound (d := d) hε hθ hrmin).1
  have hh' := mul_le_mul_of_nonneg_left hh hamp
  rw [wallChangedField_below hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α hys,
    wallChangedField_below hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α (hxy.trans_lt hys)]
  convert hh' using 1 <;> ring

theorem wallChangedField_dyadic_band_gap {T ε θ d v x y : ℝ} {n : ℕ}
    (hs : 0 < s) (hn : 1 ≤ n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc (0 : ℝ) 1) (hrmin : 0 ≤ rmin)
    (hvτ : 4*(n : ℝ)^(-(10 : ℝ)) ≤ v) (hvs : v ≤ s)
    (hx : x ∈ Icc (s-v) (s-v/4)) (hy : y ∈ Icc (s-v) (s-v/4)) (hxy : x ≤ y)
    (α : inverseIntegralConstraints rmin s k M) :
    θ*wallLowStrength T ε*wallLowRadius d rmin ε*(y-x)/(22*v*Real.log (n : ℝ)) ≤
      wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α y-
      wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α x := by
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one (Nat.one_le_cast.mpr hn)
  have hτ : 0 < (n : ℝ)^(-(10 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hv : 0 < v := by linarith
  exact wallChangedField_band_gap hr hs1 hc hk hkc hm hM g hg hs hn hlogn hε hθ hrmin
    (by linarith [hx.1]) hxy (by linarith [hy.2]) hx.1 (by linarith [hy.2]) α

theorem wallChangedField_dyadic_toNNReal_gap {T ε θ d v x y : ℝ} {n : ℕ}
    (hs : 0 < s) (hn : 1 ≤ n) (hlogn : 1 ≤ Real.log (n : ℝ))
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc (0 : ℝ) 1) (hrmin : 0 ≤ rmin)
    (hvτ : 4*(n : ℝ)^(-(10 : ℝ)) ≤ v) (hvs : v ≤ s)
    (hx : x ∈ Icc (s-v) (s-v/4)) (hy : y ∈ Icc (s-v) (s-v/4)) (hxy : x ≤ y)
    (α : inverseIntegralConstraints rmin s k M) :
    θ*wallLowStrength T ε*wallLowRadius d rmin ε*(y-x)/(22*v*Real.log (n : ℝ)) ≤
      ((wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α y).toNNReal : ℝ)-
      ((wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α x).toNNReal : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one (Nat.one_le_cast.mpr hn)
  have hτ : 0 < (n : ℝ)^(-(10 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hv : 0 < v := by linarith
  have hamp := (wall_low_amplitude_bound (d := d) hε hθ hrmin).1
  have hx0s : x ∈ Icc (0 : ℝ) s := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hy0s : y ∈ Icc (0 : ℝ) s := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hnonneg (z : ℝ) (hz : z ∈ Icc (0 : ℝ) s) (hzs : z < s) :
      0 ≤ wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α z := by
    rw [wallChangedField_below hr hs1 hc hk hkc hm hM g hg T ε θ ((n : ℝ)^(-(10 : ℝ))) d α hzs]
    exact mul_nonneg hamp (wallPsi_mem hs hτ hz).1
  rw [Real.coe_toNNReal _ (hnonneg y hy0s (by linarith [hy.2])),
      Real.coe_toNNReal _ (hnonneg x hx0s (by linarith [hx.2]))]
  exact wallChangedField_dyadic_band_gap hr hs1 hc hk hkc hm hM g hg hs hn hlogn hε hθ hrmin
    hvτ hvs hx hy hxy α

end
end OAI.SKFluctuations.LaplaceWindowFormalization
