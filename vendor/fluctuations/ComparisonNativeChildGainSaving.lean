module

public import ComparisonActualChildData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem actual_child_separated_strength_gain {d lam c0 cScale x y:ℝ}
    (hd:d≠0) (hlam:0 < lam) (hc0:0 < c0)
    (hcScale:0 < cScale) (hcScale1:cScale ≤ 1)
    (hx:x∈Ioc (0:ℝ) 1) (hy:y∈Ioc (0:ℝ) 1) (hscale:cScale*x ≤ y)
    (hweak:laplaceComparisonStrength d lam x ≤ x^2) :
    let K:=min (cScale^3) (min (c0^2*cScale^3) (c0^3*cScale^2))
    K*(laplaceComparisonStrength d lam x*x^3) ≤
      min (laplaceComparisonStrength d lam y)
        (laplaceComparisonStrength (c0*x) ((c0*x)^2) y)*y^3 := by
  let ex:=laplaceComparisonStrength d lam x
  let ey:=laplaceComparisonStrength d lam y
  let Dy:=laplaceComparisonStrength (c0*x) ((c0*x)^2) y
  let Kchild:=min (c0^2*cScale^3) (c0^3*cScale^2)
  have hex:0 < ex:=laplaceComparisonStrength_pos d hlam x
  have hey:0 < ey:=laplaceComparisonStrength_pos d hlam y
  have hy2:(cScale*x)^2 ≤ y^2:=pow_le_pow_left₀ (mul_nonneg hcScale.le hx.1.le) hscale 2
  have hy3:(cScale*x)^3 ≤ y^3:=pow_le_pow_left₀ (mul_nonneg hcScale.le hx.1.le) hscale 3
  have heparent:cScale^3*(ex*x^3) ≤ ey*y^3:=by
    by_cases hxy:x ≤ y
    · have hf:ex*x ≤ ey*y:=(laplaceComparisonStrength_monotonicities hd hlam (r₀:=0) le_rfl).2
        ⟨hx.1.le,hx.2⟩ ⟨hy.1.le,hy.2⟩ hxy
      have hs:x^2 ≤ y^2:=pow_le_pow_left₀ hx.1.le hxy 2
      have hh:=mul_le_mul hf hs (sq_nonneg x) (mul_nonneg hey.le hy.1.le)
      have hc:cScale^3 ≤ 1:=by simpa using pow_le_pow_left₀ hcScale.le hcScale1 3
      have hj:=mul_le_mul_of_nonneg_right hc (mul_nonneg hex.le (pow_nonneg hx.1.le 3))
      nlinarith
    · have hea:ex ≤ ey:=(laplaceComparisonStrength_monotonicities hd hlam (r₀:=0) le_rfl).1
        ⟨hy.1.le,hy.2⟩ ⟨hx.1.le,hx.2⟩ (le_of_not_ge hxy)
      have hh:=mul_le_mul hea hy3 (pow_nonneg (mul_nonneg hcScale.le hx.1.le) 3) hey.le
      simp only [mul_pow] at hh
      nlinarith
  have hchild:=laplaceComparisonStrength_lower (mul_pos hc0 hx.1)
    (sq_pos_of_pos (mul_pos hc0 hx.1)) hy.1
  have hm1:(c0^2*cScale^3)*x^5 ≤ (c0*x)^2*y^3:=by
    have hh:=mul_le_mul_of_nonneg_left hy3 (sq_nonneg (c0*x))
    simp only [mul_pow] at hh
    nlinarith
  have hm2:(c0^3*cScale^2)*x^5 ≤ ((c0*x)^3/y)*y^3:=by
    have hh:=mul_le_mul_of_nonneg_left hy2 (pow_nonneg (mul_nonneg hc0.le hx.1.le) 3)
    have he:((c0*x)^3/y)*y^3=(c0*x)^3*y^2:=by field_simp
    rw [he]
    simp only [mul_pow] at hh
    nlinarith
  have hm:Kchild*x^5 ≤ Dy*y^3:=by
    have hh:=min_le_min hm1 hm2
    rw [←min_mul_of_nonneg _ _ (pow_nonneg hx.1.le 5),←min_mul_of_nonneg _ _ (pow_nonneg hy.1.le 3)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hchild (pow_nonneg hy.1.le 3))
  have hKchild:0 ≤ Kchild:=by dsimp [Kchild];positivity
  have hscaleEx:ex*x^3 ≤ x^5:=by
    have hh:=mul_le_mul_of_nonneg_right hweak (pow_nonneg hx.1.le 3)
    nlinarith
  have hm':Kchild*(ex*x^3) ≤ Dy*y^3:=
    (mul_le_mul_of_nonneg_left hscaleEx hKchild).trans hm
  change min (cScale^3) Kchild*(ex*x^3) ≤ min ey Dy*y^3
  rw [min_mul_of_nonneg _ _ (mul_nonneg hex.le (pow_nonneg hx.1.le 3)),
    min_mul_of_nonneg _ _ (pow_nonneg hy.1.le 3)]
  exact min_le_min heparent hm'

theorem eventually_actual_child_error_below_separated_gain
    {delta c0 cScale A:ℝ} (hdelta:0 < delta) (hc0:0 < c0)
    (hcScale:0 < cScale) (hcScale1:cScale ≤ 1) (hA:0 < A) :
    ∀ᶠ n:ℕ in atTop,∀ d lam x y:ℝ,
      d≠0 → 0 < lam → x∈Ioc (0:ℝ) 1 → y∈Ioc (0:ℝ) 1 →
      cScale*x ≤ y → laplaceComparisonStrength d lam x ≤ x^2 →
      4*((n:ℝ)^(20*delta)*actualChildErrorBudget n delta c0 d lam x) <
        A*min (laplaceComparisonStrength d lam y)
          (laplaceComparisonStrength (c0*x) ((c0*x)^2) y)*y^3 := by
  let K:=min (cScale^3) (min (c0^2*cScale^3) (c0^3*cScale^2))
  have hK:0 < K:=by dsimp [K];positivity
  have ht:Tendsto (fun n:ℕ=>4*(n:ℝ)^(-80*delta)) atTop (𝓝 0):=by
    simpa using ((tendsto_rpow_neg_atTop (show 0 < 80*delta by positivity)).comp
      tendsto_natCast_atTop_atTop).const_mul 4
  filter_upwards [ht.eventually (gt_mem_nhds (mul_pos hA hK)),
    eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro d lam x y hd hlam hx hy hscale hweak
  have hN:0 < (n:ℝ):=by exact_mod_cast hn0
  have hex:0 < laplaceComparisonStrength d lam x*x^3:=
    mul_pos (laplaceComparisonStrength_pos d hlam x) (pow_pos hx.1 3)
  have hbudget:actualChildErrorBudget n delta c0 d lam x ≤
      (n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3:=min_le_right _ _
  have hfirst:4*((n:ℝ)^(20*delta)*actualChildErrorBudget n delta c0 d lam x) ≤
      (4*(n:ℝ)^(-80*delta))*(laplaceComparisonStrength d lam x*x^3):=by
    have hh:=mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 4*(n:ℝ)^(20*delta) by positivity)
    have he:(n:ℝ)^(20*delta)*(n:ℝ)^(-100*delta)=(n:ℝ)^(-80*delta):=by
      rw [←Real.rpow_add hN]
      congr 1
      ring
    convert hh using 1
    · ring
    · rw [show 4*(n:ℝ)^(20*delta)*((n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3)=
        4*((n:ℝ)^(20*delta)*(n:ℝ)^(-100*delta))*(laplaceComparisonStrength d lam x*x^3) by ring,he]
  have hstrict:(4*(n:ℝ)^(-80*delta))*(laplaceComparisonStrength d lam x*x^3) <
      A*(K*(laplaceComparisonStrength d lam x*x^3)):=by
    have hh:=mul_lt_mul_of_pos_right hn hex
    nlinarith
  have hstrength:=actual_child_separated_strength_gain hd hlam hc0 hcScale hcScale1 hx hy hscale hweak
  have hlast:A*(K*(laplaceComparisonStrength d lam x*x^3)) ≤
      A*(min (laplaceComparisonStrength d lam y)
        (laplaceComparisonStrength (c0*x) ((c0*x)^2) y)*y^3):=
    mul_le_mul_of_nonneg_left hstrength hA.le
  exact (hfirst.trans_lt hstrict).trans_le (by convert hlast using 1 <;> ring)

end OAI.SKFluctuations.LaplaceWindowFormalization
