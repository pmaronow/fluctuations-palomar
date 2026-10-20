module

public import FinitePhysicalPropagationBarrierSelectionMeasure
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set
open scoped Topology
set_option maxHeartbeats 3000000

def physicalPropagationDisagreementMassSet (R Z : ℝ → ℝ) (a b eps : ℝ) : Set ℝ :=
  {u | u ∈ Icc a b ∧ eps < |Z u-R u|}

theorem physical_propagation_good_point_of_small_disagreement_mass
    (R Z : ℝ → ℝ) {a b left right eps : ℝ}
    (hsubset : Icc left right ⊆ Icc a b)
    (hbad : volume (physicalPropagationDisagreementMassSet R Z a b eps) <
      ENNReal.ofReal (right-left)) :
    ∃ u ∈ Icc left right,|Z u-R u| ≤ eps := by
  classical
  by_contra hnot
  have hcover : Icc left right ⊆ physicalPropagationDisagreementMassSet R Z a b eps := by
    intro u hu
    refine ⟨hsubset hu,?_⟩
    by_contra hlarge
    exact hnot ⟨u,hu,le_of_not_gt hlarge⟩
  have hmeasure := measure_mono (μ := volume) hcover
  rw [Real.volume_Icc] at hmeasure
  exact not_lt_of_ge hmeasure hbad

theorem physical_propagation_actual_monotone_bracket
    {R Z : ℝ → ℝ} (hR : Monotone R) (hZ : Monotone Z)
    {a b u h eps : ℝ} (hh : 0 ≤ h) (hleft : a ≤ u-h) (hright : u+h ≤ b)
    (hbad : volume (physicalPropagationDisagreementMassSet R Z a b eps) < ENNReal.ofReal h) :
    Z (u-h)-eps ≤ R u ∧ R u ≤ Z (u+h)+eps := by
  have hsubsetL : Icc (u-h) u ⊆ Icc a b :=
    Icc_subset_Icc hleft (by linarith)
  have hsubsetR : Icc u (u+h) ⊆ Icc a b :=
    Icc_subset_Icc (by linarith) hright
  have hlengthL : u-(u-h)=h := by ring
  have hlengthR : (u+h)-u=h := by ring
  obtain ⟨left,hleftmem,hleftgood⟩ := physical_propagation_good_point_of_small_disagreement_mass
    R Z hsubsetL (by simpa only [hlengthL] using hbad)
  obtain ⟨right,hrightmem,hrightgood⟩ := physical_propagation_good_point_of_small_disagreement_mass
    R Z hsubsetR (by simpa only [hlengthR] using hbad)
  have hleftabs := (abs_le.mp hleftgood).2
  have hrightabs := (abs_le.mp hrightgood).1
  have hRleft := hR hleftmem.2
  have hRright := hR hrightmem.1
  have hZleft := hZ hleftmem.1
  have hZright := hZ hrightmem.2
  constructor <;> linarith

theorem physical_propagation_transfer_actual_child_linear_profile
    (R Z : ℕ → ℝ → ℝ) (x : ℕ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hx : ∀ᶠ n in atTop,0 < x n)
    (hR : ∀ n,Monotone (R n)) (hZ : ∀ n,Monotone (Z n))
    (hchild : ∀ v : ℝ,0 < v → Tendsto (fun n => Z n (x n*v)/x n)
      atTop (𝓝 (kappa*v)))
    (hagreement : ∀ a b eps theta : ℝ,0 < a → a < b → 0 < eps → 0 < theta →
      ∀ᶠ n in atTop,volume (physicalPropagationDisagreementMassSet (R n) (Z n)
        (x n*a) (x n*b) (eps*x n)) < ENNReal.ofReal (theta*x n)) :
    ∀ v : ℝ,0 < v → Tendsto (fun n => R n (x n*v)/x n) atTop (𝓝 (kappa*v)) := by
  intro v hv
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let h := min (v/2) (eps/(8*kappa))
  have hh : 0 < h := lt_min (half_pos hv) (div_pos heps (by positivity))
  have hhv : h ≤ v/2 := min_le_left _ _
  have hheps : h ≤ eps/(8*kappa) := min_le_right _ _
  have hlo : 0 < v-h := by linarith
  have hhi : 0 < v+h := by linarith
  have hab : v-h < v+h := by linarith
  have heps8 : 0 < eps/8 := by positivity
  have hklimit := (le_div_iff₀ (by positivity : 0 < 8*kappa)).mp hheps
  have hchildL : ∀ᶠ n in atTop,|Z n (x n*(v-h))/x n-kappa*(v-h)| < eps/8 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hchild (v-h) hlo) (eps/8) heps8)
  have hchildR : ∀ᶠ n in atTop,|Z n (x n*(v+h))/x n-kappa*(v+h)| < eps/8 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hchild (v+h) hhi) (eps/8) heps8)
  filter_upwards [hx,hagreement (v-h) (v+h) (eps/8) h hlo hab heps8 hh,
      hchildL,hchildR] with n hxn hnagree hnchildL hnchildR
  have hmass : 0 ≤ h*x n := mul_nonneg hh.le hxn.le
  have hleft : x n*(v-h) ≤ x n*v-h*x n := by nlinarith
  have hright : x n*v+h*x n ≤ x n*(v+h) := by nlinarith
  have hbracket := physical_propagation_actual_monotone_bracket (hR n) (hZ n) hmass
    hleft hright hnagree
  have hlow := div_le_div_of_nonneg_right hbracket.1 hxn.le
  have hupp := div_le_div_of_nonneg_right hbracket.2 hxn.le
  have hidL : (Z n (x n*v-h*x n)-(eps/8)*x n)/x n=
      Z n (x n*(v-h))/x n-eps/8 := by
    rw [show x n*v-h*x n=x n*(v-h) by ring]
    field_simp [hxn.ne'] <;> ring
  have hidR : (Z n (x n*v+h*x n)+(eps/8)*x n)/x n=
      Z n (x n*(v+h))/x n+eps/8 := by
    rw [show x n*v+h*x n=x n*(v+h) by ring]
    field_simp [hxn.ne'] <;> ring
  rw [hidL] at hlow
  rw [hidR] at hupp
  have hL := abs_lt.mp hnchildL
  have hR' := abs_lt.mp hnchildR
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
