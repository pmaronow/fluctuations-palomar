module

public import ComparisonCanonicalPhysicalStrength
public import ComparisonNativeActualChildBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem comparison_conditional_scale_ge_lower
    {N delta E d lam : ℝ} (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hE : 0 < E) (hd : 0 < d) (hlam : 0 < lam) (hld : lam ≤ d^2) :
    comparisonLowerScale N E d ≤ comparisonConditionalScale N delta E lam := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hslo : Real.sqrt lam ≤ d := by
    nlinarith [Real.sq_sqrt hlam.le, Real.sqrt_nonneg lam]
  have hpow : 1 ≤ N^delta := Real.one_le_rpow hN hdelta
  unfold comparisonLowerScale comparisonConditionalScale
  have hdiv := div_le_div_of_nonneg_left
    (mul_pos (Real.sqrt_pos.mpr hNp) hE).le hs hslo
  have hmul := mul_le_mul_of_nonneg_left hpow
    (div_nonneg (mul_pos (Real.sqrt_pos.mpr hNp) hE).le hs.le)
  calc
    _ ≤ Real.sqrt N*E/Real.sqrt lam := hdiv
    _ ≤ (Real.sqrt N*E/Real.sqrt lam)*N^delta := by simpa only [mul_one] using hmul
    _ = _ := by ring

theorem comparison_conditional_scale_direct_test
    {N delta E d lam : ℝ} (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hE : 0 < E) (hd : 0 < d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hupper : Real.sqrt N*E ≤ d^2) :
    N*E^2 ≤ laplaceComparisonStrength d lam (comparisonConditionalScale N delta E lam)*
      (comparisonConditionalScale N delta E lam)^2 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let A := comparisonConditionalScale N delta E lam
  have hA : 0 < A := comparison_conditional_scale_pos hNp hE hlam
  have hs := comparison_canonical_inner_strength hN hdelta hE hd hlam hld hupper
    (K:=1) le_rfl hA (by dsimp [A]; simp)
  simp only [one_mul] at hs
  have hs' : N^(-delta)*lam ≤ laplaceComparisonStrength d lam A :=
    le_of_mul_le_mul_left hs hNp
  have ht := mul_le_mul_of_nonneg_right hs' (sq_nonneg A)
  have he : (N^(-delta)*lam)*A^2=N^delta*(N*E^2) := by
    calc
      _ = N^(-delta)*(lam*A^2) := by ring
      _ = N^(-delta)*(N^(2*delta)*N*E^2) := by
        rw [comparison_conditional_scale_square hNp hlam]
      _ = (N^(-delta)*N^(2*delta))*(N*E^2) := by ring
      _ = _ := by rw [←Real.rpow_add hNp, show -delta+2*delta=delta by ring]
  rw [he] at ht
  have hp := mul_le_mul_of_nonneg_right (Real.one_le_rpow hN hdelta)
    (mul_nonneg hNp.le (sq_nonneg E))
  have hp' : N*E^2 ≤ N^delta*(N*E^2) := by simpa only [one_mul] using hp
  exact hp'.trans ht

namespace NativeOverlapContext
variable {n : ℕ} {margin delta cl cu C0 D T lam : ℝ}

def conditionalMinimum (c : NativeOverlapContext n delta)
    (alpha : c.Profile) (b h : ℝ → ℝ)
    (hlam : 0 < lam) (hld : lam ≤ c.d^2) (hdelta : 0 ≤ delta)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hminimum : ∀beta : c.Profile,
      comparisonVariableEndpointObjective c.hc c.hk c.hkc c.hm c.hM n b h c.d lam alpha ≤
      comparisonVariableEndpointObjective c.hc c.hk c.hkc c.hm c.hM n b h c.d lam beta)
    (hdD : c.d ≤ D) (hupper : Real.sqrt c.N*c.E ≤ c.d^2)
    (hlower : c.N^(-(2:ℝ)/3+margin)*c.d ≤ C0*c.E)
    (htotal : ∀u∈Icc (0:ℝ) 1,h u+b u ≤ T)
    (hregular : ∀r∈Icc (min (comparisonConditionalScale c.N delta c.E lam) 1) 1,
      cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) :
    NativeOverlapMinimum n margin delta cl cu 1 C0 1 D T where
  context := c
  lam := lam
  hlam := hlam
  hld := hld
  alpha := alpha
  b := b
  h := h
  hb := hb
  hlb := hlb
  hh := hh
  hh0 := hh0
  minimum := hminimum
  xs := comparisonConditionalScale c.N delta c.E lam
  z := min (comparisonConditionalScale c.N delta c.E lam) 1
  hxs := comparison_conditional_scale_pos c.hN c.hE hlam
  hscale := comparison_conditional_scale_ge_lower (by exact_mod_cast c.hn)
    hdelta c.hE c.hd hlam hld
  hz := ⟨le_min (comparison_conditional_scale_pos c.hN c.hE hlam).le zero_le_one,
    min_le_right _ _⟩
  hzxs := by
    simpa only [one_mul] using min_le_left (comparisonConditionalScale c.N delta c.E lam) 1
  hdD := hdD
  hupper := hupper
  hlower := hlower
  htest := by
    simpa only [one_mul] using comparison_conditional_scale_direct_test
      (by exact_mod_cast c.hn) hdelta c.hE c.hd hlam hld hupper
  regular := hregular
  clockBudget := by
    have hr := comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM alpha 1
    have hg := (laplaceComparisonStrength_pos c.d hlam (c.R alpha 1)).le
    have hgb := (laplaceComparisonStrength_le c.d hlam.le (c.R alpha 1)).trans
      (hlb.trans (hb (by norm_num) (by norm_num) zero_le_one))
    have hh1 := hh0.trans (hh (by norm_num) (by norm_num) zero_le_one)
    have he := mul_le_mul_of_nonneg_left hr.2 hg
    have hbound : h 1+laplaceComparisonStrength c.d lam (c.R alpha 1)*c.R alpha 1 ≤ T := by
      linarith [htotal 1 (by norm_num)]
    rw [Real.coe_toNNReal _ (add_nonneg hh1 (mul_nonneg hg hr.1))]
    exact sub_le_self _ (NNReal.coe_nonneg _)|>.trans hbound

theorem conditional_terminal_regularity (c : NativeOverlapContext n delta)
    (alpha : c.Profile) (hcl : cl ≤ 1) (hcu : 1 ≤ cu)
    (hA : 1 ≤ comparisonConditionalScale c.N delta c.E lam) :
    ∀r∈Icc (min (comparisonConditionalScale c.N delta c.E lam) 1) 1,
      cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r := by
  rw [min_eq_right hA]
  intro r hr
  have hr1 : r=1 := le_antisymm hr.2 hr.1
  subst r
  simpa only [alpha.property.2, mul_one] using And.intro hcl hcu

theorem minimum_of_sweep_attained (c : NativeOverlapContext n delta)
    (alpha : c.Profile) (b h : ℝ → ℝ)
    (hlam : 0 ≤ lam) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hattained : variableEndpointComparisonSweepObjective c.hc c.hk c.hkc c.hm c.hM
      n b h c.d lam alpha =
      variableEndpointComparisonSweepMinimum c.hc c.hk c.hkc c.hm c.hM n b h c.d lam) :
    ∀beta : c.Profile,
      comparisonVariableEndpointObjective c.hc c.hk c.hkc c.hm c.hM n b h c.d lam alpha ≤
      comparisonVariableEndpointObjective c.hc c.hk c.hkc c.hm c.hM n b h c.d lam beta := by
  obtain ⟨_,_,hmin⟩ := variableEndpointComparisonSweepMinimum_attained c.hc c.hk c.hkc c.hm c.hM
    n c.hn b h c.hd.ne' hlam hlb hb hh hh0
    (comparisonCap_continuous _ _ _ _ _ _) ⟨alpha, alpha.property⟩
  intro beta
  change variableEndpointComparisonSweepObjective c.hc c.hk c.hkc c.hm c.hM
    n b h c.d lam alpha ≤ _
  rw [hattained]
  exact hmin beta

end NativeOverlapContext
end OAI.SKFluctuations.LaplaceWindowFormalization
