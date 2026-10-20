module

public import SKConstants.GaussianProposalScalarMeshCallbacks
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem scalarPinnedBridge_norm_difference_le (h : ℝ≥0) (hh : 0<h)
    (f g : ScalarContinuousPath h) :
    ‖scalarPinnedBridge h f-scalarPinnedBridge h g‖≤3*‖f-g‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hhR : 0<(h : ℝ) := hh
  have hcoef : 0≤(t : ℝ)/(h : ℝ) ∧ (t : ℝ)/(h : ℝ)≤1 :=
    ⟨div_nonneg t.property.1 h.coe_nonneg,(div_le_one hhR).mpr t.property.2⟩
  let a := f t-g t
  let b := (1-(t : ℝ)/(h : ℝ))*(f ⟨0,le_rfl,h.coe_nonneg⟩-g ⟨0,le_rfl,h.coe_nonneg⟩)
  let c := ((t : ℝ)/(h : ℝ))*(f ⟨h,h.coe_nonneg,le_rfl⟩-g ⟨h,h.coe_nonneg,le_rfl⟩)
  have ha : |a|≤‖f-g‖ := (f-g).norm_coe_le_norm t
  have hb : |b|≤‖f-g‖ := by
    dsimp [b]
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hcoef.2)]
    have hb0 : |f ⟨0,le_rfl,h.coe_nonneg⟩-g ⟨0,le_rfl,h.coe_nonneg⟩|≤‖f-g‖ :=
      (f-g).norm_coe_le_norm _
    nlinarith [abs_nonneg (f ⟨0,le_rfl,h.coe_nonneg⟩-g ⟨0,le_rfl,h.coe_nonneg⟩)]
  have hc : |c|≤‖f-g‖ := by
    dsimp [c]
    rw [abs_mul,abs_of_nonneg hcoef.1]
    have hc0 : |f ⟨h,h.coe_nonneg,le_rfl⟩-g ⟨h,h.coe_nonneg,le_rfl⟩|≤‖f-g‖ :=
      (f-g).norm_coe_le_norm _
    nlinarith [abs_nonneg (f ⟨h,h.coe_nonneg,le_rfl⟩-g ⟨h,h.coe_nonneg,le_rfl⟩)]
  have h1 := norm_sub_le a b
  have h2 := norm_sub_le (a-b) c
  simp only [Real.norm_eq_abs] at h1 h2
  have he : (scalarPinnedBridge h f-scalarPinnedBridge h g) t = a-b-c := by
    dsimp [scalarPinnedBridge,a,b,c]
    ring
  rw [he,Real.norm_eq_abs]
  linarith

theorem scalarQueryBridgeComplete_norm_difference_le (h : ℝ≥0) (hh : 0<h)
    (z w : ℝ) (f g : ScalarContinuousPath h) :
    ‖scalarQueryBridgeComplete h (z,f)-scalarQueryBridgeComplete h (w,g)‖≤
      Real.sqrt h*|z-w|+3*‖f-g‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hhR : 0<(h : ℝ) := hh
  have hcoef : 0≤(t : ℝ)/(h : ℝ) ∧ (t : ℝ)/(h : ℝ)≤1 :=
    ⟨div_nonneg t.property.1 h.coe_nonneg,(div_le_one hhR).mpr t.property.2⟩
  have hp : |scalarPinnedBridge h f t-scalarPinnedBridge h g t|≤3*‖f-g‖ :=
    ((scalarPinnedBridge h f-scalarPinnedBridge h g).norm_coe_le_norm t).trans
      (scalarPinnedBridge_norm_difference_le h hh f g)
  have he : (scalarQueryBridgeComplete h (z,f)-scalarQueryBridgeComplete h (w,g)) t =
      (scalarPinnedBridge h f t-scalarPinnedBridge h g t)+
        ((t : ℝ)/(h : ℝ))*Real.sqrt h*(z-w) := by
    dsimp [scalarQueryBridgeComplete,scalarBrownianBridgeComplete]
    ring
  have hn : |((t : ℝ)/(h : ℝ))*Real.sqrt h*(z-w)|≤Real.sqrt h*|z-w| := by
    rw [abs_mul,abs_mul,abs_of_nonneg hcoef.1,abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef.2 (Real.sqrt_nonneg (h : ℝ))) (abs_nonneg (z-w))
  rw [he,Real.norm_eq_abs]
  have hsum := abs_add_le (scalarPinnedBridge h f t-scalarPinnedBridge h g t)
    (((t : ℝ)/(h : ℝ))*Real.sqrt h*(z-w))
  linarith

theorem scalarAppendQueryInterval_norm_difference_le (H h : ℝ≥0) (hh : 0<h)
    (a : ℝ) (B C : ScalarContinuousPath H) (z w : ℝ) (f g : ScalarContinuousPath h) :
    ‖scalarAppendQueryInterval H h a (B,(z,f))-
        scalarAppendQueryInterval H h a (C,(w,g))‖≤
      ‖B-C‖+Real.sqrt h*|z-w|+3*‖f-g‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  let u := projIcc 0 (H : ℝ) H.coe_nonneg (min (t : ℝ) a)
  let v := projIcc 0 (h : ℝ) h.coe_nonneg ((t : ℝ)-a)
  have hB : |B u-C u|≤‖B-C‖ := (B-C).norm_coe_le_norm u
  have hq : |scalarQueryBridgeComplete h (z,f) v-scalarQueryBridgeComplete h (w,g) v|≤
      Real.sqrt h*|z-w|+3*‖f-g‖ :=
    ((scalarQueryBridgeComplete h (z,f)-scalarQueryBridgeComplete h (w,g)).norm_coe_le_norm v).trans
      (scalarQueryBridgeComplete_norm_difference_le h hh z w f g)
  have he : (scalarAppendQueryInterval H h a (B,(z,f))-
      scalarAppendQueryInterval H h a (C,(w,g))) t =
      (B u-C u)+(scalarQueryBridgeComplete h (z,f) v-scalarQueryBridgeComplete h (w,g) v) := by
    dsimp [scalarAppendQueryInterval,u,v]
    ring
  rw [he,Real.norm_eq_abs]
  have hh := abs_add_le (B u-C u)
    (scalarQueryBridgeComplete h (z,f) v-scalarQueryBridgeComplete h (w,g) v)
  linarith

end SKConstants
